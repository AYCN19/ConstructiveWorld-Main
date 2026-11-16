#!/usr/bin/env python3
"""attest_cast.py — cast cw.attest/v1 archive (cw_attest.json) from a
coqchk-green certified vo tree.

Archive contract (identical to attest_reconcile.py's load_attest):
  modules: {"<Stem>.v" | "Local/<Stem>.v": {"vo_sha256": <64-hex>, "size": <int>}}
  tree_sha256: sha256 over the canonical serialization of modules
               (json.dumps sort_keys=True, separators=(",",":"), ensure_ascii=False)
  generated_by: provenance string (default "coqchk green run" — the archive
                is only cast from a tree whose .vo set passed a green run)
  schema: "cw.attest/v1"

Surface: vo-tree root *.vo (non-recursive) + Local/*.vo (non-recursive),
"-"-prefixed files excluded — byte-identical to attest_reconcile.scan_surface.

Usage:
  python -I tools/../attest_cast.py --tree <vo_dir> --out <cw_attest.json>
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path


def sha256_file(path: Path) -> tuple[str, int]:
    h = hashlib.sha256()
    n = 0
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
            n += len(chunk)
    return h.hexdigest(), n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", required=True, help="certified vo tree directory")
    ap.add_argument("--out", required=True, help="archive json output path")
    ap.add_argument("--generated-by", default="coqchk green run")
    args = ap.parse_args()

    tree = Path(args.tree)
    if not tree.is_dir():
        print(f"CAST-FAIL: tree missing {tree}")
        return 2

    modules: dict[str, dict] = {}
    for p in sorted(tree.glob("*.vo")):
        if p.name.startswith("_"):
            continue
        sha, size = sha256_file(p)
        modules[p.name[:-3] + ".v"] = {"vo_sha256": sha, "size": size}
    local = tree / "Local"
    if local.is_dir():
        for p in sorted(local.glob("*.vo")):
            if p.name.startswith("_"):
                continue
            sha, size = sha256_file(p)
            modules["Local/" + p.name[:-3] + ".v"] = {"vo_sha256": sha, "size": size}

    canonical = json.dumps(modules, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    archive = {
        "modules": modules,
        "tree_sha256": hashlib.sha256(canonical).hexdigest(),
        "generated_by": args.generated_by,
        "schema": "cw.attest/v1",
    }
    Path(args.out).write_text(
        json.dumps(archive, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
    )
    print(f"CAST-OK: modules={len(modules)} tree_sha256={archive['tree_sha256'][:16]} out={args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
