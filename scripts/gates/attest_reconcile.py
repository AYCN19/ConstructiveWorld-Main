#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""attest_reconcile.py -- CI reconciliation step before coqchk (cw.attest/v1 hit -> skip list).

ATT-RECON 20261029 wiring, landed. Reconciliation caliber shared with the sandbox reconciler coqchk_delta_check.py:
  * archive key = module name (keeping the '.v' suffix and 'Local/'-style relative paths); vo file = key minus '.v' plus '.vo'.
  * per-file check = archive {vo_sha256, size} vs the live tree's byte-stream sha256 / byte count; mtime and any
    other stat metadata never enter the verdict -- the only deviation-must-check criterion is the content itself.
  * four verdicts unchanged / changed / added / removed, mutually exclusive and exhaustive.

CI duty (exactly one): hit files (unchanged) -> write the skip list (line shape = the parallel_chk.sh mods.txt
line shape: the stem with '.v' stripped); coqchk skips them this round, certification inherits by hash; misses are
not listed and go to coqchk as usual (deviation must be checked).

Skip surface v1, narrowed as declared (prefer stronger over weaker):
  * top-level modules only (keys without '/'); Local/ files keep the dependency-closure verification status quo;
  * '_'-prefixed files never were on the certification surface (CI#46 lesson) and never enter the list.

Red only grows (fail-direction law):
  * archive missing / corrupt archive / contract mismatch / tree_sha256 self-consistency broken -> empty list +
    exit 3 (full coqchk this round, certified branch off) -- archive trouble may only slow down, never weaken;
  * live-tree vo unreadable -> exit 2 fail-loud (unreadable although the build face is green = a real anomaly, red).

Usage (the coq.yml reconciliation step):
  python attest_reconcile.py --tree ConstructiveWorld_vo \\
      --attest scripts/gates/cw_attest.json \\
      --skip-out ConstructiveWorld_vo/_attest_skip.txt --json attest_reconcile.json

Exit codes: 0 = list written (may be empty); 3 = archive side unusable (list emptied, FULL mode);
2 = structural failure (tree unreadable, fail-loud red).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

SCHEMA = "cw.attest/v1"
GENERATED_BY = "coqchk green run"
RECON_SCHEMA = "cw.recon/v1"

EXIT_OK = 0
EXIT_ERROR = 2
EXIT_NO_ARCHIVE = 3


class ReconError(Exception):
    """Archive side unusable (the EXIT_NO_ARCHIVE path)."""


class FatalReconError(Exception):
    """Live-tree structural failure (the EXIT_ERROR path, fail-loud red)."""


# ------------------------------------------------------------------ hashing --
def sha256_file(path: Path) -> tuple[str, int]:
    """Byte-stream sha256 and byte count of a file. Reads no stat metadata."""
    h = hashlib.sha256()
    size = 0
    with open(path, "rb") as fh:
        while True:
            chunk = fh.read(1 << 20)
            if not chunk:
                break
            h.update(chunk)
            size += len(chunk)
    return h.hexdigest(), size


# ------------------------------------------------------------------ archive --
def load_attest(path: Path) -> dict:
    """Contract-shape check + tree_sha256 self-consistency (same caliber as the sandbox reconciler's load_attest).

    Any mismatch -> ReconError (the caller takes EXIT_NO_ARCHIVE: list emptied, FULL mode).
    """
    try:
        raw = path.read_bytes()
        archive = json.loads(raw.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ReconError(f"档案不可读/非合法 JSON: {path}: {exc}") from exc
    if not isinstance(archive, dict):
        raise ReconError("档案顶层非 JSON 对象")
    if archive.get("schema") != SCHEMA:
        raise ReconError(f"schema 不符契约: {archive.get('schema')!r} != {SCHEMA!r}")
    if archive.get("generated_by") != GENERATED_BY:
        raise ReconError(
            f"generated_by 不符契约（非 coqchk 全绿运行铸造）: {archive.get('generated_by')!r}"
        )
    modules = archive.get("modules")
    if not isinstance(modules, dict) or not modules:
        raise ReconError("modules 缺失或非非空对象")
    for key, entry in modules.items():
        if not isinstance(entry, dict) or set(entry) != {"vo_sha256", "size"}:
            raise ReconError(f"模块条目字段不符契约: {key!r}")
        sha = entry["vo_sha256"]
        size = entry["size"]
        if not isinstance(sha, str) or len(sha) != 64:
            raise ReconError(f"vo_sha256 非 64 位 hex: {key!r}")
        if not isinstance(size, int) or isinstance(size, bool) or size < 0:
            raise ReconError(f"size 非非负整数: {key!r}")
        if not key.endswith(".v"):
            raise ReconError(f"模块键不以 .v 结尾: {key!r}")
    tree_sha = archive.get("tree_sha256")
    if not isinstance(tree_sha, str) or len(tree_sha) != 64:
        raise ReconError("tree_sha256 非 64 位 hex 字符串")
    canonical = json.dumps(
        modules, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    recomputed = hashlib.sha256(canonical).hexdigest()
    if recomputed != tree_sha:
        raise ReconError(
            f"档案 tree_sha256 自洽性破: 档案 {tree_sha} != 按 modules 重算 {recomputed}"
        )
    return archive


# --------------------------------------------------------------------- tree --
def scan_surface(tree: Path) -> dict[str, Path]:
    """Certification surface = .vo files of the tree root (non-recursive) + Local/ (non-recursive); '_'-prefixed files excluded.

    Line shape aligned with parallel_chk.sh mods.txt: stem = relative path minus '.vo' ('X.vo' -> 'X',
    'Local/Y.vo' -> 'Local/Y')."""
    surface: dict[str, Path] = {}
    for p in sorted(tree.glob("*.vo")):
        if p.name.startswith("_"):
            continue
        surface[p.name[:-3]] = p
    local = tree / "Local"
    if local.is_dir():
        for p in sorted(local.glob("*.vo")):
            if p.name.startswith("_"):
                continue
            surface["Local/" + p.name[:-3]] = p
    return surface


def reconcile(tree: Path, archive: dict) -> dict:
    """Four-way reconciliation (union of archive keys and the certification surface, per stem). Read-only on tree and archive."""
    modules = archive["modules"]
    surface = scan_surface(tree)
    arch_stem = {k[:-2]: v for k, v in modules.items()}  # 'X.v' → 'X'
    counts = {"unchanged": 0, "changed": 0, "added": 0, "removed": 0}
    skipped: list[str] = []
    changed_or_removed: list[str] = []
    for stem in sorted(set(arch_stem) | set(surface)):
        ent = arch_stem.get(stem)
        if ent is None:
            counts["added"] += 1
            continue
        path = surface.get(stem)
        if path is None:
            counts["removed"] += 1
            changed_or_removed.append(stem)
            continue
        try:
            digest, size = sha256_file(path)
        except OSError as exc:
            raise FatalReconError(f"现树 vo 不可读: {path}: {exc}")
        if digest == ent["vo_sha256"] and size == ent["size"]:
            counts["unchanged"] += 1
            if "/" not in stem:  # skip surface v1 = top-level only (Local/ keeps closure verification as-is)
                skipped.append(stem)
        else:
            counts["changed"] += 1
            changed_or_removed.append(stem)
    return {
        "archive_tree_sha256": archive["tree_sha256"],
        "surface": sorted(surface),
        "skipped": sorted(skipped),
        "sent_to_chk": sorted(set(surface) - set(skipped)),
        "changed_or_removed": sorted(changed_or_removed),
        "counts": counts,
    }


# ---------------------------------------------------------------------- main --
def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="cw.attest/v1 命中→跳过清单（只读树与档案）")
    ap.add_argument("--tree", type=Path, required=True, help="现 vo 树根（只读）")
    ap.add_argument("--attest", type=Path, required=True, help="认证档案（只读）")
    ap.add_argument("--skip-out", type=Path, required=True, help="跳过清单输出")
    ap.add_argument("--json", dest="jsonout", type=Path, required=True, help="对账报告输出")
    args = ap.parse_args(argv)

    def write_skip(stems: list[str]) -> None:
        args.skip_out.parent.mkdir(parents=True, exist_ok=True)
        tmp = args.skip_out.with_suffix(args.skip_out.suffix + ".tmp")
        tmp.write_text("".join(s + "\n" for s in stems), encoding="utf-8", newline="\n")
        tmp.replace(args.skip_out)

    def write_json(doc: dict) -> None:
        args.jsonout.parent.mkdir(parents=True, exist_ok=True)
        args.jsonout.write_text(
            json.dumps(doc, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
            newline="\n",
        )

    if not args.tree.is_dir():
        print(f"[error] 现树不存在: {args.tree}")
        write_skip([])
        write_json(
            {
                "schema": RECON_SCHEMA,
                "mode": "FULL",
                "archive_valid": False,
                "reason": f"tree missing: {args.tree}",
                "surface": [],
                "skipped": [],
                "sent_to_chk": [],
                "changed_or_removed": [],
                "counts": {"unchanged": 0, "changed": 0, "added": 0, "removed": 0},
            }
        )
        return EXIT_ERROR

    try:
        archive = load_attest(args.attest)
        rep = reconcile(args.tree, archive)
    except FatalReconError as exc:
        print(f"[error] {exc}")
        write_skip([])
        write_json(
            {
                "schema": RECON_SCHEMA,
                "mode": "FULL",
                "archive_valid": False,
                "reason": f"fatal: {exc}",
                "surface": [],
                "skipped": [],
                "sent_to_chk": [],
                "changed_or_removed": [],
                "counts": {"unchanged": 0, "changed": 0, "added": 0, "removed": 0},
            }
        )
        return EXIT_ERROR
    except ReconError as exc:
        print(f"[no-archive] {exc}")
        write_skip([])
        write_json(
            {
                "schema": RECON_SCHEMA,
                "mode": "FULL",
                "archive_valid": False,
                "archive_tree_sha256": None,
                "reason": str(exc),
                "surface": [],
                "skipped": [],
                "sent_to_chk": [],
                "changed_or_removed": [],
                "counts": {"unchanged": 0, "changed": 0, "added": 0, "removed": 0},
            }
        )
        return EXIT_NO_ARCHIVE

    write_skip(rep["skipped"])
    doc = {
        "schema": RECON_SCHEMA,
        "mode": "ATTESTED" if rep["skipped"] else "FULL",
        "archive": str(args.attest),
        "archive_tree_sha256": rep["archive_tree_sha256"],
        "archive_valid": True,
        "reason": None,
        "cert_surface": rep["surface"],
        "skipped": rep["skipped"],
        "sent_to_chk": rep["sent_to_chk"],
        "changed_or_removed": rep["changed_or_removed"],
        "counts": rep["counts"],
    }
    write_json(doc)
    c = rep["counts"]
    print(
        f"[recon] surface={len(rep['surface'])} skipped(顶层命中)={len(rep['skipped'])} "
        f"sent_to_chk={len(rep['sent_to_chk'])} | unchanged={c['unchanged']} "
        f"changed={c['changed']} added={c['added']} removed={c['removed']} "
        f"| archive_tree_sha256={rep['archive_tree_sha256'][:12]}…"
    )
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
