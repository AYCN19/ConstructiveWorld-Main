#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""build_deposit.py — y 系列存档波依赖链构建（扁平单根 + 拓扑序 + 可选温控包裹 + coqchk -norec 复核）。

用法：
  python 50_toolkit/build_deposit.py --config 50_toolkit/config.json [--dry-run] [--chk] [--targets M1 M2 ...]
    --dry-run   只打印拓扑序与命令，不编译
    --chk       编译后对本轮目标闭包内的 γ 模块逐个跑 coqchk -o -bytecode-compiler yes -norec
    --targets   只构建这些模块及其依赖闭包（默认＝全部存档件＋work_dir/nodes 下全部新件）

设计要点：
  * 单根：四个存档目录与 work_dir/nodes 的 .v 一律复制到 work_dir/build/ 扁平目录，
    同名文件必须逐字节一致（CxRealPair 两件在三段各有一份·已核一致），否则停机——
    避免同名模块多根导致的 coqchk 错靶（ambiguous=0 律）。
  * L0（Main 仓 1020 模块）只读引用：-Q <main_vo_dir> ""，不复制不重编。
  * 依赖图取自 Require 语句（剥注释后按句切分）；L0 与标准库名不入图。
  * 增量：build/_stamp.json 记录每件 .v 的 md5；源未变、依赖未重编且 .vo 在盘则跳过。
退出码：0 成功；1 编译或复核失败；2 结构性失败（重名不一致 / 依赖成环 / 配置错）。
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

TOOLKIT = Path(__file__).resolve().parent
PKG = TOOLKIT.parent
STDLIB_PREFIXES = {"Stdlib", "Coq", "Corelib", "Ltac2"}


class BuildError(Exception):
    pass


# ------------------------------------------------------------------ config --
def load_config(path: str | Path) -> dict:
    p = Path(path)
    if not p.is_absolute():
        p = (Path.cwd() / p).resolve()
    if not p.is_file():
        raise BuildError(f"配置文件不存在: {p}（先把 config.example.json 复制为 config.json 并填写）")
    raw = p.read_text(encoding="utf-8")
    raw = raw.replace("{PKG}", PKG.as_posix())
    cfg = json.loads(raw)
    for key in ("coqc", "coqchk", "main_vo_dir", "deposit_dir", "work_dir"):
        if not cfg.get(key):
            raise BuildError(f"配置缺字段: {key}")
    cfg.setdefault("coqc_flags", ["-q"])
    cfg.setdefault("deposit_segments", ["seg_C1", "seg_C2", "seg_C3", "seg_C3_cast"])
    cfg.setdefault("exclude", ["GaC2_03_d_probe.v"])
    cfg.setdefault("guard", {"enabled": False})
    cfg.setdefault("inter_compile_sleep_sec", 0)
    work = Path(cfg["work_dir"])
    for sub in ("nodes", "build", "logs", "accept", "audit", "ledger", "lit_evidence"):
        (work / sub).mkdir(parents=True, exist_ok=True)
    return cfg


def md5_bytes(b: bytes) -> str:
    return hashlib.md5(b).hexdigest()


# ------------------------------------------------------------ coq parsing --
def strip_comments(text: str) -> str:
    """剥除 Coq 嵌套注释 (* ... *)，保留字符串字面量；注释换成等长空白以保住行号。"""
    out = []
    i, n, depth, in_str = 0, len(text), 0, False
    while i < n:
        c = text[i]
        if in_str:
            out.append(c)
            if c == '"':
                if i + 1 < n and text[i + 1] == '"':
                    out.append('"')
                    i += 2
                    continue
                in_str = False
            i += 1
            continue
        if depth == 0 and c == '"':
            in_str = True
            out.append(c)
            i += 1
            continue
        if text.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        out.append(c if depth == 0 or c == "\n" else (" " if c != "\t" else "\t"))
        i += 1
    return "".join(out)


SENT_SPLIT = re.compile(r"\.(?=\s|$)")


def parse_requires(text: str) -> list[str]:
    """返回 Require 语句引用的模块名（带 From 前缀者拼接为 Prefix.Name；标准库前缀丢弃）。"""
    names: list[str] = []
    code = strip_comments(text)
    for sent in SENT_SPLIT.split(code):
        s = " ".join(sent.split())
        if not s:
            continue
        prefix = None
        m = re.match(r"^From\s+(\S+)\s+(.*)$", s)
        if m:
            prefix, s = m.group(1), m.group(2)
        m = re.match(r"^Require(?:\s+(?:Import|Export))?\s+(.*)$", s)
        if not m:
            continue
        if prefix and prefix.split(".")[0] in STDLIB_PREFIXES:
            continue
        for tok in m.group(1).split():
            tok = tok.strip("()")
            if not tok or not re.match(r"^[A-Za-z_][\w'.]*$", tok):
                continue
            names.append(f"{prefix}.{tok}" if prefix else tok)
    return names


# ---------------------------------------------------------------- sources --
def l0_stems(main_vo_dir: Path) -> set[str]:
    stems = {p.stem for p in main_vo_dir.glob("*.vo")}
    local = main_vo_dir / "Local"
    if local.is_dir():
        stems |= {"Local." + p.stem for p in local.glob("*.vo")}
    return stems


def collect_sources(cfg: dict) -> dict[str, Path]:
    dep = Path(cfg["deposit_dir"])
    excl = set(cfg.get("exclude", []))
    found: dict[str, Path] = {}
    dirs = [dep / s for s in cfg["deposit_segments"]] + [Path(cfg["work_dir"]) / "nodes"]
    for d in dirs:
        if not d.is_dir():
            if d.name != "nodes":
                raise BuildError(f"存档目录缺失: {d}")
            continue
        for f in sorted(d.glob("*.v")):
            if f.name in excl:
                continue
            stem = f.stem
            if stem in found:
                if found[stem].read_bytes() != f.read_bytes():
                    raise BuildError(f"同名模块内容不一致（单根律）: {found[stem]} vs {f}")
                continue
            found[stem] = f
    return found


def build_graph(srcs: dict[str, Path], l0: set[str]) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    deps: dict[str, list[str]] = {}
    unresolved: dict[str, list[str]] = {}
    for stem, path in srcs.items():
        req = parse_requires(path.read_text(encoding="utf-8", errors="replace"))
        deps[stem] = sorted({r for r in req if r in srcs and r != stem})
        unk = sorted({r for r in req if r not in srcs and r not in l0})
        if unk:
            unresolved[stem] = unk
    return deps, unresolved


def closure(targets: list[str], deps: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(targets)
    while stack:
        t = stack.pop()
        if t in seen:
            continue
        if t not in deps:
            raise BuildError(f"目标模块不在源集合中: {t}")
        seen.add(t)
        stack.extend(deps[t])
    return seen


def topo_order(nodes: set[str], deps: dict[str, list[str]]) -> list[str]:
    indeg = {n: 0 for n in nodes}
    for n in nodes:
        for d in deps[n]:
            if d in nodes:
                indeg[n] += 1
    ready = sorted(n for n, k in indeg.items() if k == 0)
    order: list[str] = []
    rev: dict[str, list[str]] = {n: [] for n in nodes}
    for n in nodes:
        for d in deps[n]:
            if d in nodes:
                rev[d].append(n)
    while ready:
        n = ready.pop(0)
        order.append(n)
        for m in sorted(rev[n]):
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
        ready.sort()
    if len(order) != len(nodes):
        cyc = sorted(n for n in nodes if n not in order)
        raise BuildError(f"依赖成环（LINT-1）: {cyc[:12]}")
    return order


# --------------------------------------------------------------- commands --
def cmd_quote(a: str) -> str:
    if a == "":
        return '""'
    if any(ch in a for ch in ' \t&()^|<>"'):
        return '"' + a.replace('"', '\\"') + '"'
    return a


def wrap(cfg: dict, argv: list[str]) -> list[str]:
    g = cfg.get("guard") or {}
    if not g.get("enabled"):
        return argv
    line = " ".join(cmd_quote(a) for a in argv)
    return (["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", g["ps1"], "-Command", line]
            + list(g.get("extra", [])))


def qflags(cfg: dict) -> list[str]:
    return ["-Q", str(Path(cfg["main_vo_dir"])), "", "-Q", str(Path(cfg["work_dir"]) / "build"), ""]


def run_logged(argv: list[str], log: Path, cwd: Path, timeout: int | None = None) -> tuple[int, str]:
    t0 = time.time()
    p = subprocess.run(argv, cwd=str(cwd), capture_output=True, timeout=timeout)
    out = p.stdout.decode("utf-8", errors="replace") + p.stderr.decode("utf-8", errors="replace")
    log.write_text(f"# argv: {argv}\n# rc={p.returncode} wall={time.time() - t0:.1f}s\n{out}",
                   encoding="utf-8", newline="\n")
    return p.returncode, out


CHK_SECTIONS = [
    "Axioms:",
    "Constants/Inductives relying on type-in-type:",
    "Constants/Inductives relying on unsafe (co)fixpoints:",
    "Inductives whose positivity is assumed:",
]


def chk_sections(out: str) -> dict[str, list[str]]:
    """解析 coqchk -o 输出的四个假设段，返回 段名 → 条目列表（<none> 为空表）。"""
    res: dict[str, list[str]] = {s: [] for s in CHK_SECTIONS}
    cur = None
    for ln in out.splitlines():
        st = ln.strip()
        if st.startswith("* "):
            cur = next((s for s in CHK_SECTIONS if st[2:].startswith(s)), None)
            if cur and st.endswith("<none>"):
                cur = None
            continue
        if cur and st and not st.startswith("*"):
            res[cur].append(st)
    return res


def chk_verdict(out: str, module: str) -> tuple[bool, dict]:
    """-norec 模式的 coqchk 判据。

    -norec 只检查目标模块本身，依赖（标准库、L0、上游 γ 件）按「未检查·采信」载入，
    于是 -o 的 Axioms 段会列出被采信依赖里的模块类型参数——这些不是本模块引入的。
    判定：'Modules were successfully checked' 出现，且四个假设段里没有以本模块名打头的条目。
    依赖带入的条目只计数记录；依赖链的公理面由验收阶段 Print Assumptions 全闭包把关。
    """
    checked = "Modules were successfully checked" in out
    secs = chk_sections(out)
    own = {s: [x for x in v if x == module or x.startswith(module + ".")] for s, v in secs.items()}
    dep = {s: len(v) - len(own[s]) for s, v in secs.items()}
    own_n = sum(len(v) for v in own.values())
    return checked and own_n == 0, {"checked": checked, "own": {s: v for s, v in own.items() if v}, "dep_counts": dep}


# ------------------------------------------------------------------ build --
def build(cfg: dict, targets: list[str] | None = None, dry: bool = False, chk: bool = False) -> int:
    main_vo = Path(cfg["main_vo_dir"])
    if not main_vo.is_dir():
        raise BuildError(f"main_vo_dir 不存在: {main_vo}（解压附卷A 或指向 Main 仓 ConstructiveWorld_vo）")
    work = Path(cfg["work_dir"])
    bdir, logs = work / "build", work / "logs"
    srcs = collect_sources(cfg)
    l0 = l0_stems(main_vo)
    deps, unresolved = build_graph(srcs, l0)
    tgt = targets or sorted(srcs)
    nodes = closure(tgt, deps)
    order = topo_order(nodes, deps)
    if unresolved:
        print("[info] 以下 Require 名不在存档/新件/L0 中，按标准库对待（coqc 将最终判定）：")
        for k in sorted(unresolved):
            if k in nodes:
                print(f"   {k}: {unresolved[k]}")
    print(f"[plan] 目标闭包 {len(order)} 件：{' → '.join(order)}")
    stamp_path = bdir / "_stamp.json"
    stamp = json.loads(stamp_path.read_text(encoding="utf-8")) if stamp_path.is_file() else {}
    rebuilt: set[str] = set()
    for stem in order:
        src = srcs[stem]
        data = src.read_bytes()
        h = md5_bytes(data)
        dst = bdir / f"{stem}.v"
        vo = bdir / f"{stem}.vo"
        fresh = (stamp.get(stem) == h and vo.is_file() and not (set(deps[stem]) & rebuilt)
                 and dst.is_file() and dst.read_bytes() == data)
        argv = wrap(cfg, [cfg["coqc"], *cfg["coqc_flags"], *qflags(cfg), str(dst)])
        if dry:
            print(f"[dry] {'跳过' if fresh else '编译'} {stem}: {' '.join(cmd_quote(a) for a in argv)}")
            continue
        if fresh:
            continue
        if not dst.is_file() or dst.read_bytes() != data:
            shutil.copyfile(src, dst)
        print(f"[coqc] {stem} …", flush=True)
        rc, out = run_logged(argv, logs / f"{stem}.compile.log", bdir)
        if rc != 0 or not vo.is_file():
            print(f"[FAIL] coqc {stem} rc={rc}（日志 {logs / (stem + '.compile.log')}）\n{out[-3000:]}")
            stamp_path.write_text(json.dumps(stamp, indent=1), encoding="utf-8")
            return 1
        stamp[stem] = h
        rebuilt.add(stem)
        stamp_path.write_text(json.dumps(stamp, indent=1), encoding="utf-8")
        if cfg.get("inter_compile_sleep_sec", 0):
            time.sleep(int(cfg["inter_compile_sleep_sec"]))
    if dry:
        return 0
    print(f"[build] 完成：本轮重编 {len(rebuilt)} 件，跳过 {len(order) - len(rebuilt)} 件")
    if chk:
        summary = {}
        bad = []
        for stem in order:
            argv = wrap(cfg, [cfg["coqchk"], "-o", "-bytecode-compiler", "yes", *qflags(cfg), "-norec", stem])
            print(f"[coqchk] {stem} …", flush=True)
            rc, out = run_logged(argv, logs / f"{stem}.chk.log", bdir)
            ok, info = chk_verdict(out, stem)
            ok = ok and rc == 0
            summary[stem] = {"rc": rc, "pass": ok, **info}
            if not ok:
                bad.append(stem)
        (work / "chk_summary.json").write_text(json.dumps(summary, indent=1, ensure_ascii=False), encoding="utf-8")
        if bad:
            print(f"[FAIL] coqchk 未过 {len(bad)} 件: {bad}（日志 {logs}）")
            return 1
        print(f"[coqchk] {len(order)} 件全部 'Modules were successfully checked'，且无本模块自带假设（依赖带入条目已记入 chk_summary.json）")
    return 0


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="y 存档波依赖链构建")
    ap.add_argument("--config", required=True)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--chk", action="store_true")
    ap.add_argument("--targets", nargs="*", default=None)
    a = ap.parse_args()
    try:
        cfg = load_config(a.config)
        return build(cfg, a.targets or None, a.dry_run, a.chk)
    except BuildError as e:
        print(f"[error] {e}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
