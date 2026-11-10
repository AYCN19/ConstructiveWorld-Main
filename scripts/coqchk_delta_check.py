#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""coqchk_delta_check.py - ConstructiveWorld vo tree vs certification archive,
a four-way delta reconciliation.

Reconciliation object (contract cw.attest/v1, same source as coqchk_attest.py):
    * module name = an archive modules key (the '.v' suffix and relative paths
      such as 'Local/' are preserved).
    * the corresponding vo file = the module name with the trailing '.v'
      replaced by '.vo', resolved under the vo tree root.
    * per-file hash pair = the archive's {vo_sha256, size} vs the sha256 / byte
      count of the live file's byte stream (mtime and any other stat metadata
      never enter the reconciliation).

Four verdicts (mutually exclusive and exhaustive, judged per file over the full
union of archive keys and vo files addressed in the live tree):
    unchanged - present in the archive and in the tree, sha256 and size both
      match;
    changed   - present in the archive and in the tree, sha256 or size
      mismatch (tamper detection included);
    removed   - present in the archive, absent from the tree (the vo file is
      missing);
    added     - absent from the archive, present in the tree (an uncertified
      vo file mixed in).

Scan scope (where added files can be discovered):
    the vo tree root (non-recursive) + every subdirectory addressed by archive
    keys (e.g. Local/, non-recursive).
    Directories not addressed by archive keys (e.g. _pchk_tmp_* build
    leftovers) are outside the reconciliation scope - they are not
    certification objects of this archive; this scope definition is stated
    explicitly in the report's scan_domains.

Exit codes: 0 = all unchanged (zero delta); 1 = some changed/added/removed;
2 = structural failure (archive missing/bad JSON/contract mismatch/archive
tree_sha256 self-consistency broken/vo tree missing).

Discipline (read-only law):
    * the real vo tree and the certification archive are read-only (opened
      'rb' / 'r' only).
    * every write (fixture trees, tampering, self-test leftovers) lands only in
      the sandbox = the directory holding this script;
      --json escaping the sandbox is refused.

Three-state closed-loop selftest (fixtures live in the sandbox; the real vo
tree is untouched):
    (1)  copy several certified .vo files from the real tree into a fixture
       tree and reconcile against the matching slice of the real archive
       (original hashes kept intact) -> all must be judged unchanged;
    (2)  flip 1 byte of 1 file inside the fixture -> the reconciliation must
       flag it changed (tamper detection), the rest stay unchanged, and
       removed/added are zero;
    (3)  delete 1 file inside the fixture -> the reconciliation must flag it
       removed, with changed back to zero.
    One extra state (4), added beyond the three as acceptance: place 1 vo file
    outside the archive inside the fixture -> judged added. Each state is
    reverted as soon as it is verified; states never pollute one another. All
    of states (1)(2)(3) must pass for delivery. Fixtures are deleted after
    use.

Usage:
    python coqchk_delta_check.py                       # real tree vs sandbox archive, four-way reconciliation
    python coqchk_delta_check.py --tree T --attest A   # explicit vo tree root and archive
    python coqchk_delta_check.py --json OUT            # also write a per-file JSON report (must stay in the sandbox)
    python coqchk_delta_check.py --selftest            # sandbox fixture three-state closed loop (extra state (4) included)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
import time
from pathlib import Path, PurePosixPath

SCHEMA = "cw.attest/v1"
GENERATED_BY = "coqchk green run"
DELTA_SCHEMA = "cw.delta/v1"
DEFAULT_TREE = Path(r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo")
SANDBOX = Path(__file__).resolve().parent
DEFAULT_ATTEST = SANDBOX / "cw_attest.json"

# Certified modules picked for the selftest (cross-category sample; includes 1 Local/ subdirectory file to exercise subdirectory resolution)
SELFTEST_PICKS = [
    "AttnSqrt.v",
    "G02_Debt.v",
    "UpCS.v",
    "S15_TailFEPUp.v",
    "Local/LW0LeibSeparation.v",
]
TAMPER_TARGET = "AttnSqrt.v"   # state (2): the file with 1 byte flipped
REMOVE_TARGET = "G02_Debt.v"   # state (3): the file deleted
ADDED_TARGET = "ZZ_UnattestedExtra.v"  # extra state (4): the file mixed in from outside the archive

EXIT_CLEAN = 0
EXIT_DELTA = 1
EXIT_ERROR = 2

VERDICTS = ("unchanged", "changed", "added", "removed")


class DeltaError(Exception):
    """Structural failure (exit code 2)."""


# ------------------------------------------------------------------ helpers --
def sha256_file(path: Path) -> tuple[str, int]:
    """sha256 and byte count of a file's byte stream. Reads no stat metadata."""
    h = hashlib.sha256()
    size = 0
    try:
        with open(path, "rb") as fh:
            while True:
                chunk = fh.read(1 << 20)
                if not chunk:
                    break
                h.update(chunk)
                size += len(chunk)
    except OSError as exc:
        raise DeltaError(f"vo 不可读: {path}: {exc}") from exc
    return h.hexdigest(), size


def vo_rel(key: str) -> str:
    """Module name -> relative vo path ('X.v' -> 'X.vo'). A non-.v ending is an error."""
    if not key.endswith(".v"):
        raise DeltaError(f"模块键不以 .v 结尾，无法解析 vo: {key!r}")
    return key[:-2] + ".vo"


def canonical_modules_bytes(modules: dict) -> bytes:
    return json.dumps(
        modules, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def tree_sha256_of(modules: dict) -> str:
    return hashlib.sha256(canonical_modules_bytes(modules)).hexdigest()


# ------------------------------------------------------------ archive loading --
def load_attest(archive_path: Path) -> dict:
    """Load the certification archive; validate the contract structure + tree_sha256 self-consistency; a bad archive -> DeltaError."""
    try:
        raw = archive_path.read_bytes()
    except OSError as exc:
        raise DeltaError(f"档案不可读: {archive_path}: {exc}") from exc
    try:
        archive = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise DeltaError(f"档案非合法 JSON/UTF-8: {exc}") from exc
    if not isinstance(archive, dict):
        raise DeltaError("档案顶层非 JSON 对象")
    if archive.get("schema") != SCHEMA:
        raise DeltaError(f"schema 不符契约: {archive.get('schema')!r} ≠ {SCHEMA!r}")
    if archive.get("generated_by") != GENERATED_BY:
        raise DeltaError(
            f"generated_by 不符契约: {archive.get('generated_by')!r} ≠ {GENERATED_BY!r}"
        )
    modules = archive.get("modules")
    if not isinstance(modules, dict) or not modules:
        raise DeltaError("modules 缺失或非非空对象")
    for key, entry in modules.items():
        if not isinstance(entry, dict):
            raise DeltaError(f"模块条目非对象: {key!r}")
        if set(entry) != {"vo_sha256", "size"}:
            raise DeltaError(f"模块条目字段不符契约 {key!r}: {sorted(entry)}")
        if not isinstance(entry["vo_sha256"], str) or len(entry["vo_sha256"]) != 64:
            raise DeltaError(f"vo_sha256 非 64 位 hex 字符串: {key!r}")
        if (
            not isinstance(entry["size"], int)
            or isinstance(entry["size"], bool)
            or entry["size"] < 0
        ):
            raise DeltaError(f"size 非非负整数: {key!r}")
    if not isinstance(archive.get("tree_sha256"), str) or len(archive["tree_sha256"]) != 64:
        raise DeltaError("tree_sha256 非 64 位 hex 字符串")
    recomputed = tree_sha256_of(modules)
    if recomputed != archive["tree_sha256"]:
        raise DeltaError(
            f"档案 tree_sha256 自洽性破: 档案 {archive['tree_sha256']} "
            f"≠ 按 modules 重算 {recomputed}"
        )
    return archive


# ------------------------------------------------------------- reconciliation --
def scan_domains_of(modules: dict) -> list[str]:
    """Subdirectories addressed by archive keys (root '.' included). The discovery scope for added is exactly the root plus these directories."""
    dirs = {"."}
    for key in modules:
        parent = PurePosixPath(vo_rel(key)).parent
        if str(parent) not in (".", ""):
            dirs.add(str(parent))
    return sorted(dirs)


def discover_tree_vos(tree: Path, modules: dict) -> dict[str, Path]:
    """Discover vo files in the scan scope (root + archive-key subdirectories, each non-recursive) -> {module name: path}."""
    found: dict[str, Path] = {}
    for domain in scan_domains_of(modules):
        base = tree if domain == "." else tree.joinpath(*PurePosixPath(domain).parts)
        if not base.is_dir():
            continue
        for p in sorted(base.glob("*.vo")):
            rel = p.name if domain == "." else f"{domain}/{p.name}"
            found[rel[:-3] + ".v"] = p
    return found


def reconcile(tree: Path, archive: dict) -> dict:
    """Four-way delta reconciliation. Per-file hash pairs go into entries. The tree and the archive are read-only."""
    modules = archive["modules"]
    tree_vos = discover_tree_vos(tree, modules)
    entries: list[dict] = []
    counts = {v: 0 for v in VERDICTS}
    for key in sorted(set(modules) | set(tree_vos)):
        ent = modules.get(key)
        if ent is None:
            digest, size = sha256_file(tree_vos[key])
            counts["added"] += 1
            entries.append(
                {
                    "module": key,
                    "verdict": "added",
                    "attest_sha256": None,
                    "attest_size": None,
                    "tree_sha256": digest,
                    "tree_size": size,
                    "match": False,
                }
            )
            continue
        path = tree.joinpath(*PurePosixPath(vo_rel(key)).parts)
        if key not in tree_vos or not path.is_file():
            counts["removed"] += 1
            entries.append(
                {
                    "module": key,
                    "verdict": "removed",
                    "attest_sha256": ent["vo_sha256"],
                    "attest_size": ent["size"],
                    "tree_sha256": None,
                    "tree_size": None,
                    "match": False,
                }
            )
            continue
        digest, size = sha256_file(path)
        ok = digest == ent["vo_sha256"] and size == ent["size"]
        verdict = "unchanged" if ok else "changed"
        counts[verdict] += 1
        entries.append(
            {
                "module": key,
                "verdict": verdict,
                "attest_sha256": ent["vo_sha256"],
                "attest_size": ent["size"],
                "tree_sha256": digest,
                "tree_size": size,
                "match": ok,
            }
        )
    return {
        "tree": str(tree),
        "attest": None,  # filled in by the caller
        "scan_domains": scan_domains_of(modules),
        "counts": counts,
        "entries": entries,
    }


def short(hexstr: str | None) -> str:
    return "—" if hexstr is None else f"{hexstr[:8]}…{hexstr[-8:]}"


def print_report(rep: dict) -> None:
    c = rep["counts"]
    print(f"对账域（scan_domains）: {', '.join(rep['scan_domains'])}")
    print(
        f"四类判定: unchanged={c['unchanged']}  changed={c['changed']}  "
        f"added={c['added']}  removed={c['removed']}"
    )
    print("逐件哈希对（档案 vs 现树）:")
    for e in rep["entries"]:
        print(
            f"  {e['verdict']:9s} {e['module']:42s} "
            f"档案 {short(e['attest_sha256'])} ({e['attest_size']} B)  "
            f"树 {short(e['tree_sha256'])} ({e['tree_size']} B)  "
            f"{'==' if e['match'] else '!!'}"
        )
    clean = c["changed"] == c["added"] == c["removed"] == 0
    print(f"判定: {'CLEAN（全 unchanged，零增量）' if clean else 'DELTA（存在增量，见上）'}")


def _ensure_in_sandbox(path: Path) -> Path:
    resolved = path.resolve()
    try:
        resolved.relative_to(SANDBOX)
    except ValueError as exc:
        raise DeltaError(f"写入路径越出沙箱（只读律: 真实 vo 树只读）: {resolved}") from exc
    return resolved


# ----------------------------------------------------------------- selftest --
def _copy_real_vo(tree: Path, key: str, dest: Path) -> None:
    """Copy 1 vo file from the real tree into the fixture, read-only. The source is opened 'rb' only."""
    src = tree.joinpath(*PurePosixPath(vo_rel(key)).parts)
    try:
        blob = src.read_bytes()
    except OSError as exc:
        raise DeltaError(f"真实 vo 不可读: {src}: {exc}") from exc
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(blob)


def _subset_archive(archive: dict, keys: list[str]) -> dict:
    """A key slice of the real archive: original vo_sha256/size kept intact
    (tamper detection anchors on the certified hashes); tree_sha256 recomputed
    with the same canonical form, so the slice itself is a valid cw.attest/v1
    archive."""
    sub_modules = {k: dict(archive["modules"][k]) for k in keys}
    return {
        "modules": sub_modules,
        "tree_sha256": tree_sha256_of(sub_modules),
        "generated_by": GENERATED_BY,
        "schema": SCHEMA,
    }


def _counts_of(rep: dict) -> dict:
    return dict(rep["counts"])


def run_selftest() -> int:
    """Sandbox fixture three-state closed loop ((1) all unchanged, (2) 1 changed, (3) 1 removed, plus the extra state (4) added)."""
    results: list[tuple[str, bool, str]] = []
    work = Path(tempfile.mkdtemp(prefix="delta_fixture_", dir=SANDBOX))
    try:
        archive = load_attest(DEFAULT_ATTEST)
        real_tree = DEFAULT_TREE.resolve()
        ftree = work / "fix_tree"
        ftree.mkdir()

        # Copy several real .vo files (the Local/ subdirectory file included) into the fixture tree
        for key in SELFTEST_PICKS:
            _copy_real_vo(real_tree, key, ftree.joinpath(*PurePosixPath(vo_rel(key)).parts))
        # Fixture reconciliation archive = the matching slice of the real archive (original hashes as the anchor)
        sub = _subset_archive(archive, SELFTEST_PICKS)

        def once() -> dict:
            return reconcile(ftree, sub)

        def ok_counts(rep: dict, want: dict) -> bool:
            return rep["counts"] == want

        # state (1): all unchanged
        rep1 = once()
        want1 = {"unchanged": len(SELFTEST_PICKS), "changed": 0, "added": 0, "removed": 0}
        results.append(
            (
                "① 复制真实 .vo 数件 → 全 unchanged",
                ok_counts(rep1, want1),
                f"counts={_counts_of(rep1)}（期望 {want1}）",
            )
        )

        # state (2): flip 1 byte of 1 fixture file -> must be flagged changed (tamper detection)
        tamper_path = ftree.joinpath(*PurePosixPath(vo_rel(TAMPER_TARGET)).parts)
        blob = tamper_path.read_bytes()
        tamper_path.write_bytes(blob[:0] + bytes([blob[0] ^ 0xFF]) + blob[1:])
        rep2 = once()
        changed2 = {e["module"] for e in rep2["entries"] if e["verdict"] == "changed"}
        cond2 = (
            rep2["counts"]["changed"] == 1
            and changed2 == {TAMPER_TARGET}
            and rep2["counts"]["unchanged"] == len(SELFTEST_PICKS) - 1
            and rep2["counts"]["removed"] == 0
            and rep2["counts"]["added"] == 0
        )
        tam_e = next(e for e in rep2["entries"] if e["module"] == TAMPER_TARGET)
        detail2 = (
            f"changed={sorted(changed2)} 篡改件哈希对 档案{short(tam_e['attest_sha256'])}"
            f" vs 树{short(tam_e['tree_sha256'])} counts={_counts_of(rep2)}"
        )
        results.append(("② 改 1 件 1 字节 → 标入 changed", cond2, detail2))
        # Restore (re-copy the real file; states never pollute one another)
        _copy_real_vo(real_tree, TAMPER_TARGET, tamper_path)

        # state (3): delete 1 file in the fixture -> flagged removed
        remove_path = ftree.joinpath(*PurePosixPath(vo_rel(REMOVE_TARGET)).parts)
        remove_path.unlink()
        rep3 = once()
        removed3 = {e["module"] for e in rep3["entries"] if e["verdict"] == "removed"}
        cond3 = (
            rep3["counts"]["removed"] == 1
            and removed3 == {REMOVE_TARGET}
            and rep3["counts"]["unchanged"] == len(SELFTEST_PICKS) - 1
            and rep3["counts"]["changed"] == 0
            and rep3["counts"]["added"] == 0
        )
        results.append(
            (
                "③ 删 1 件 → 标入 removed",
                cond3,
                f"removed={sorted(removed3)} counts={_counts_of(rep3)}",
            )
        )
        # Restore
        _copy_real_vo(real_tree, REMOVE_TARGET, remove_path)

        # Extra state (4) (added beyond the three states): mix in 1 vo file outside the archive -> flagged added
        (ftree / vo_rel(ADDED_TARGET)).write_bytes(b"fixture unattested extra bytes")
        rep4 = once()
        added4 = {e["module"] for e in rep4["entries"] if e["verdict"] == "added"}
        cond4 = (
            rep4["counts"]["added"] == 1
            and added4 == {ADDED_TARGET}
            and rep4["counts"]["unchanged"] == len(SELFTEST_PICKS)
            and rep4["counts"]["changed"] == 0
            and rep4["counts"]["removed"] == 0
        )
        results.append(
            (
                "④（附加）混入档案外 vo → 标入 added",
                cond4,
                f"added={sorted(added4)} counts={_counts_of(rep4)}",
            )
        )
    except DeltaError as exc:
        print(f"[error] selftest 结构性失败: {exc}")
        shutil.rmtree(work, ignore_errors=True)
        return EXIT_ERROR
    finally:
        shutil.rmtree(work, ignore_errors=True)

    print("三态闭环（沙箱 fixture，真实树零改动，fixture 用毕已删）:")
    all_ok = True
    for name, ok, detail in results:
        all_ok = all_ok and ok
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}")
        print(f"         {detail}")
    verdict = "PASS（①②③全过，附加④亦过）" if all_ok else "FAIL"
    print("selftest:", verdict)
    return EXIT_CLEAN if all_ok else EXIT_DELTA


# ----------------------------------------------------------------------- main --
def main(argv: list[str] | None = None) -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="cw.attest/v1 vo 树四类增量对账（只读真实树）")
    ap.add_argument("--tree", type=Path, default=DEFAULT_TREE, help="vo 树根（只读）")
    ap.add_argument("--attest", type=Path, default=DEFAULT_ATTEST, help="认证档案（只读）")
    ap.add_argument("--json", type=Path, default=None, help="逐件 JSON 报告输出路径（须在沙箱内）")
    ap.add_argument("--selftest", action="store_true", help="沙箱 fixture 三态闭环自验")
    args = ap.parse_args(argv)

    t0 = time.time()
    if args.selftest:
        rc = run_selftest()
        print(f"耗时 {time.time() - t0:.1f}s，退出码 {rc}")
        return rc

    tree = args.tree.resolve()
    try:
        archive = load_attest(args.attest.resolve())
        if not tree.is_dir():
            raise DeltaError(f"vo 树不存在: {tree}")
        rep = reconcile(tree, archive)
        if args.json is not None:
            out = _ensure_in_sandbox(args.json)
            report = dict(rep)
            report["attest"] = str(args.attest.resolve())
            report["schema"] = DELTA_SCHEMA
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(
                json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
            )
            print(f"JSON 报告已落: {out}")
    except DeltaError as exc:
        print(f"[error] {exc}")
        return EXIT_ERROR

    print(f"对账: 树 {tree}  vs  档案 {args.attest.resolve()}")
    rep["attest"] = str(args.attest.resolve())
    print_report(rep)
    c = rep["counts"]
    rc = EXIT_CLEAN if (c["changed"] == c["added"] == c["removed"] == 0) else EXIT_DELTA
    print(f"耗时 {time.time() - t0:.1f}s，退出码 {rc}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
