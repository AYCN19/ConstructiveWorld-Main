#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""env_check.py — 外派机环境自检（开工前必跑·任一失败即停）。

检查：Python ≥3.9；coqc / coqchk 版本含 expect_version（默认 9.3.0）；main_vo_dir 的 L0 .vo
（附卷A 解压目录或 Main 仓 ConstructiveWorld_vo）逐件 md5 对 10_data/L0_vo_md5_925d454.txt；
.vo 魔数＝90300；温控脚本（若启用）在盘；work_dir 可写。
用法：python 50_toolkit/env_check.py --config 50_toolkit/config.json
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_deposit as bd  # noqa: E402


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", required=True)
    a = ap.parse_args()
    fails: list[str] = []
    if sys.version_info < (3, 9):
        fails.append(f"Python 版本 {sys.version.split()[0]} < 3.9")
    try:
        cfg = bd.load_config(a.config)
    except bd.BuildError as e:
        print(f"[FAIL] {e}")
        return 1
    want = cfg.get("expect_version", "9.3.0")
    for tool in ("coqc", "coqchk"):
        try:
            p = subprocess.run([cfg[tool], "--version"], capture_output=True, timeout=120)
            out = (p.stdout + p.stderr).decode("utf-8", errors="replace")
            ok = want in out
            print(f"[{'ok' if ok else 'FAIL'}] {tool}: {out.strip().splitlines()[0] if out.strip() else '(无输出)'}")
            if not ok:
                fails.append(f"{tool} 版本不含 {want}（.vo 跨版本不可混用）")
        except Exception as e:  # noqa: BLE001
            fails.append(f"{tool} 无法执行: {e}")
    vo_dir = Path(cfg["main_vo_dir"])
    ref = Path(cfg.get("l0_md5_list", bd.PKG / "10_data" / "L0_vo_md5_925d454.txt"))
    if not vo_dir.is_dir():
        fails.append(f"main_vo_dir 不存在: {vo_dir}")
    elif not ref.is_file():
        fails.append(f"L0 md5 参照表缺失: {ref}")
    else:
        bad, miss, n = [], [], 0
        for line in ref.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            md5, rel = line.split(" *", 1)
            f = vo_dir / rel
            n += 1
            if not f.is_file():
                miss.append(rel)
                continue
            if hashlib.md5(f.read_bytes()).hexdigest() != md5:
                bad.append(rel)
        print(f"[{'ok' if not bad and not miss else 'FAIL'}] L0 .vo 对表 {n} 件：漂移 {len(bad)}·缺失 {len(miss)}")
        if bad or miss:
            fails.append(f"L0 .vo 与 925d454 参照不符：漂移 {bad[:5]} 缺失 {miss[:5]}")
        sample = sorted(vo_dir.glob("*.vo"))[:1]
        if sample:
            magic = sample[0].read_bytes()[4:8]
            mv = int.from_bytes(magic, "big")
            print(f"[{'ok' if mv == 90300 else 'FAIL'}] .vo 魔数 {mv}（期望 90300＝Rocq 9.3）")
            if mv != 90300:
                fails.append(f".vo 魔数 {mv} ≠ 90300")
    g = cfg.get("guard") or {}
    if g.get("enabled"):
        if not Path(g.get("ps1", "")).is_file():
            fails.append(f"温控脚本不在盘: {g.get('ps1')}")
        else:
            print(f"[ok] 温控包裹启用：{g['ps1']} {' '.join(g.get('extra', []))}")
    else:
        print("[warn] 温控包裹未启用——须用本机自有温控或串行低并发编译（见工单 §5 温控条）")
    work = Path(cfg["work_dir"])
    try:
        probe = work / "logs" / "_write_probe.txt"
        probe.write_text("ok", encoding="utf-8")
        probe.unlink()
        print(f"[ok] work_dir 可写：{work}")
    except Exception as e:  # noqa: BLE001
        fails.append(f"work_dir 不可写: {e}")
    if fails:
        print("[env] 自检未过：")
        for x in fails:
            print(f"  - {x}")
        return 1
    print("[env] 自检全过")
    return 0


if __name__ == "__main__":
    sys.exit(main())
