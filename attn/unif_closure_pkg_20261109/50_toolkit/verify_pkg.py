#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""verify_pkg.py — 数据包完整性校验：按包根 MANIFEST.json 逐件核 md5 与字节数。
用法（在包根目录下）：python 50_toolkit/verify_pkg.py
退出码：0 全部一致；1 有失配或缺失。"""

import hashlib
import json
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    man = json.loads((PKG / "MANIFEST.json").read_text(encoding="utf-8"))
    bad, miss = [], []
    for rel, ent in man["files"].items():
        f = PKG / rel
        if not f.is_file():
            miss.append(rel)
            continue
        b = f.read_bytes()
        if len(b) != ent["size"] or hashlib.md5(b).hexdigest() != ent["md5"]:
            bad.append(rel)
    n = len(man["files"])
    print(f"[pkg] {man.get('package')}·清单 {n} 件：一致 {n - len(bad) - len(miss)}·失配 {len(bad)}·缺失 {len(miss)}")
    for x in (bad + miss)[:20]:
        print(f"  - {x}")
    return 0 if not bad and not miss else 1


if __name__ == "__main__":
    sys.exit(main())
