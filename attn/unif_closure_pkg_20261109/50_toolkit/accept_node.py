#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""accept_node.py — 新节点六道链验收（dossier 同款口径＋项目红线 lint）。

用法：
  python 50_toolkit/accept_node.py --config 50_toolkit/config.json --node C3-P08 \
      --files GaC3_P08_PerronCutoff.v [GaC3_P08_PerronCutoff_cert.v ...] [--theorems name1 name2 ...] [--static]
  --files     节点文件；裸文件名按 work_dir/nodes/ 解析，也可给绝对路径（会复制进 nodes/）
  --theorems  Print Assumptions 审计名单；缺省则自动抽取文件内全部 Theorem/Lemma/Corollary/Proposition/Fact/Remark
  --static    只跑静态 lint 与 gate4（预检用，不编译不复核）

六道链（任一 HARD 即不过）：
  ① 依赖链编译 rc=0（build_deposit.build，温控按 config）
  ② coqchk -o -bytecode-compiler yes -norec <模块>：'Modules were successfully checked' + 'Axioms: <none>'
  ③ Print Assumptions：每个审计名都是 'Closed under the global context'（coqc 编审计件·禁 coqtop 交互）
  ④ 注释规范卡：两段式头注、五字段（Mission./Dependencies./References./Constructivity./Build.）、CJK=0、零自承字面
  ⑤ gate4 v2.1 EXT：FAIL=0、UNREADABLE=0（头注超长等 REVIEW 只记录）
  ⑥ md5 账：通过后写 work_dir/ledger/<节点>.md5 并追加 md5_ledger.txt（md5sum -c 兼容形）
另加项目红线 lint：≤400 行（born 基座豁免）、R2 证书分离（非 _cert 文件禁 vm_compute 等）、
  禁 Axiom/Parameter/Conjecture、Section 外禁 Variable/Hypothesis、γ 非 Iface 文件禁 Require Export、
  跨段只许经 Iface 且只许向低段依赖；承载位疑似 Prop 存在/析取＝REVIEW（交复审员判）。
退出码：0＝通过；1＝有 HARD；2＝结构性失败。结果 JSON 写 work_dir/accept/<节点>.json。
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build_deposit as bd  # noqa: E402

FIELDS = ["Mission.", "Dependencies.", "References.", "Constructivity.", "Build."]
CJK = re.compile(r"[\u3000-\u303f\u3400-\u4dbf\u4e00-\u9fff\uff00-\uffef]")
CONFESS = re.compile(r"\b(Admitted|admit|Abort|sorry|TODO|FIXME|XXX)\b")
AXIOM_DECL = re.compile(r"^\s*(Axiom|Axioms|Parameter|Parameters|Conjecture)\b", re.M)
SECTION_VAR = re.compile(r"^\s*(Variable|Variables|Hypothesis|Hypotheses|Context)\b")
R2_WORDS = re.compile(r"\b(vm_compute|native_compute|vm_cast_no_check|Compute)\b")
THM = re.compile(r"^\s*(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark)\s+([A-Za-z_][\w']*)", re.M)
STMT_START = re.compile(r"^\s*(Theorem|Lemma|Corollary|Proposition|Fact|Remark|Definition)\b")
GA_SEG = re.compile(r"^GaC(\d)_")


def lint_file(path: Path, born: set[str]) -> tuple[list[str], list[str]]:
    hard: list[str] = []
    review: list[str] = []
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    stem = path.stem
    code = bd.strip_comments(text)
    # LINT-6 行数谱
    if len(lines) > 400 and stem not in born:
        hard.append(f"LINT-6 行数 {len(lines)} > 400（拆 _a/_b 或下沉件；born 基座以外无豁免）")
    # CJK
    for i, ln in enumerate(lines, 1):
        if CJK.search(ln):
            hard.append(f"CJK 字符 :{i}（注释与代码全英文）")
            break
    # 两段式头注＋五字段
    head = "\n".join(lines[:160])
    if not lines or not lines[0].lstrip().startswith("(* ConstructiveWorld"):
        review.append("首行非一行横幅 '(* ConstructiveWorld-Main - ... *)'（两段式头注第一段）")
    miss = [f for f in FIELDS if f not in head]
    if miss:
        hard.append(f"头注五字段缺: {miss}")
    # 零自承字面（代码与注释全文）
    for i, ln in enumerate(lines, 1):
        m = CONFESS.search(ln)
        if m:
            hard.append(f"自承字面 '{m.group(1)}' :{i}")
    # 全局假设
    for m in AXIOM_DECL.finditer(code):
        ln = code.count("\n", 0, m.start()) + 1
        hard.append(f"全局假设声明 '{m.group(1)}' :{ln}（GAPASUME 只许 Section 内 Hypothesis 并在 End 出节）")
    # Section 外 Variable/Hypothesis
    depth = 0
    for i, ln in enumerate(code.splitlines(), 1):
        s = ln.strip()
        if re.match(r"^Section\s+\w+\s*\.", s):
            depth += 1
        elif re.match(r"^End\s+\w+\s*\.", s) and depth > 0:
            depth -= 1
        elif depth == 0 and SECTION_VAR.match(ln):
            hard.append(f"Section 外的 {s.split()[0]} :{i}（顶层会变成公理）")
    # R2 证书分离
    if not stem.endswith("_cert"):
        for i, ln in enumerate(code.splitlines(), 1):
            m = R2_WORDS.search(ln)
            if m:
                hard.append(f"LINT-5 证明面出现 '{m.group(1)}' :{i}（数值事实落 {stem}_cert.v）")
    # Require Export 伞面禁令与跨段 Iface 律
    is_iface = "_Iface_" in stem
    seg_m = GA_SEG.match(stem)
    for i, ln in enumerate(code.splitlines(), 1):
        if re.search(r"\bRequire\s+Export\b", ln) and not is_iface:
            hard.append(f"LINT-3 非 Iface 文件 Require Export :{i}")
    if seg_m:
        myseg = int(seg_m.group(1))
        for name in bd.parse_requires(text):
            dm = GA_SEG.match(name)
            if not dm:
                continue
            dseg = int(dm.group(1))
            if dseg > myseg:
                hard.append(f"LINT-2 上行依赖 {name}（只许向低段）")
            elif dseg < myseg and "_Iface_" not in name:
                hard.append(f"跨段直依他段节点 {name}（跨段只许经 GaC{dseg}_Iface_*）")
    # 承载位 Prop 疑点（REVIEW）
    cap = False
    for i, ln in enumerate(code.splitlines(), 1):
        if STMT_START.match(ln):
            cap = True
        if cap and (re.search(r"\bexists\b", ln) or "\\/" in ln):
            review.append(f"承载位疑似 Prop 存在/析取 :{i}（数据承载须 Set 形 sig/sigT/sumbool·gate7 born-clean）")
        if cap and ("Proof." in ln or ":=" in ln):
            cap = False
    return hard, review


def run_gate4(cfg: dict, files: list[Path]) -> tuple[list[str], list[str], str]:
    g4 = Path(cfg.get("gate4", bd.TOOLKIT / "gate4_comment_guard.py"))
    argv = [sys.executable, str(g4)]
    for f in files:
        argv += ["--file", str(f)]
    p = subprocess.run(argv, capture_output=True)
    out = p.stdout.decode("utf-8", errors="replace") + p.stderr.decode("utf-8", errors="replace")
    hard, review = [], []
    m_fail = re.search(r"FAIL=(\d+)", out)
    m_unr = re.search(r"UNREADABLE=(\d+)", out)
    m_rev = re.search(r"REVIEW\(人工复核\)=(\d+)", out)
    if not m_fail:
        hard.append("gate4 输出无法判读（未见 FAIL= 计数）")
    else:
        if int(m_fail.group(1)) > 0:
            hard.append(f"gate4 FAIL={m_fail.group(1)}")
        if m_unr and int(m_unr.group(1)) > 0:
            hard.append(f"gate4 UNREADABLE={m_unr.group(1)}")
        if m_rev and int(m_rev.group(1)) > 0:
            review.append(f"gate4 REVIEW={m_rev.group(1)}（头注超长等复核级·记录不阻断）")
    return hard, review, out[-4000:]


def audit_assumptions(cfg: dict, node: str, stems: list[str], theorems: list[str]) -> tuple[list[str], str]:
    work = Path(cfg["work_dir"])
    safe = re.sub(r"[^A-Za-z0-9]", "_", node)
    af = work / "audit" / f"Audit_{safe}.v"
    body = ["Require Import " + " ".join(stems) + "."]
    body += [f"Print Assumptions {t}." for t in theorems]
    af.write_text("\n".join(body) + "\n", encoding="utf-8", newline="\n")
    argv = bd.wrap(cfg, [cfg["coqc"], *cfg["coqc_flags"], *bd.qflags(cfg), str(af)])
    rc, out = bd.run_logged(argv, work / "logs" / f"Audit_{safe}.log", work / "audit")
    hard = []
    if rc != 0:
        hard.append(f"Print Assumptions 审计件编译失败 rc={rc}（名字不存在或 Module 内需限定名）")
        return hard, out[-3000:]
    closed = out.count("Closed under the global context")
    if closed != len(theorems):
        hard.append(f"Print Assumptions：{closed}/{len(theorems)} 为 Closed under the global context")
    if re.search(r"^\s*Axioms:", out, re.M):
        hard.append("Print Assumptions 输出含 Axioms 块")
    return hard, out[-3000:]


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass
    ap = argparse.ArgumentParser(description="新节点六道链验收")
    ap.add_argument("--config", required=True)
    ap.add_argument("--node", required=True)
    ap.add_argument("--files", nargs="+", required=True)
    ap.add_argument("--theorems", nargs="*", default=None)
    ap.add_argument("--static", action="store_true")
    a = ap.parse_args()
    try:
        cfg = bd.load_config(a.config)
    except bd.BuildError as e:
        print(f"[error] {e}")
        return 2
    work = Path(cfg["work_dir"])
    nodes_dir = work / "nodes"
    born = set(cfg.get("born_whitelist", ["CxRealPairCore", "CxRealPairExpLog"]))
    paths: list[Path] = []
    for f in a.files:
        p = Path(f)
        if not p.is_absolute():
            p = nodes_dir / p.name
        if not p.is_file():
            print(f"[error] 节点文件不存在: {p}")
            return 2
        if p.parent.resolve() != nodes_dir.resolve():
            shutil.copyfile(p, nodes_dir / p.name)
            p = nodes_dir / p.name
        paths.append(p)
    stems = [p.stem for p in paths]

    report: dict = {"node": a.node, "files": [p.name for p in paths], "time": datetime.datetime.now().isoformat(timespec="seconds"),
                    "hard": [], "review": [], "chain": {}}
    for p in paths:
        h, r = lint_file(p, born)
        report["hard"] += [f"{p.name}: {x}" for x in h]
        report["review"] += [f"{p.name}: {x}" for x in r]
    report["chain"]["lint"] = "pass" if not report["hard"] else "fail"
    g4h, g4r, g4out = run_gate4(cfg, paths)
    report["hard"] += g4h
    report["review"] += g4r
    report["chain"]["gate4"] = "pass" if not g4h else "fail"
    report["gate4_tail"] = g4out

    if not a.static:
        try:
            rc = bd.build(cfg, targets=stems, chk=False)
        except bd.BuildError as e:
            report["hard"].append(f"构建结构性失败: {e}")
            rc = 2
        report["chain"]["compile"] = "pass" if rc == 0 else "fail"
        if rc != 0:
            report["hard"].append("① 依赖链编译未过（见 work_dir/logs/*.compile.log）")
        else:
            chk_bad = []
            for s in stems:
                argv = bd.wrap(cfg, [cfg["coqchk"], "-o", "-bytecode-compiler", "yes", *bd.qflags(cfg), "-norec", s])
                crc, cout = bd.run_logged(argv, work / "logs" / f"{s}.chk.log", work / "build")
                cok, cinfo = bd.chk_verdict(cout, s)
                report.setdefault("coqchk_detail", {})[s] = cinfo
                if crc != 0 or not cok:
                    chk_bad.append(s)
            report["chain"]["coqchk"] = "pass" if not chk_bad else "fail"
            if chk_bad:
                report["hard"].append(f"② coqchk 未过: {chk_bad}（见 logs/<模块>.chk.log）")
            thms = a.theorems if a.theorems else []
            if not thms:
                for p in paths:
                    thms += THM.findall(bd.strip_comments(p.read_text(encoding="utf-8", errors="replace")))
            thms = list(dict.fromkeys(thms))
            report["theorems"] = thms
            if not thms:
                report["review"].append("③ 无可审计的命名定理（Iface 件属正常）")
                report["chain"]["print_assumptions"] = "n/a"
            else:
                ah, aout = audit_assumptions(cfg, a.node, stems, thms)
                report["hard"] += ah
                report["chain"]["print_assumptions"] = "pass" if not ah else "fail"
                report["audit_tail"] = aout
    passed = not report["hard"]
    if passed and not a.static:
        safe = re.sub(r"[^A-Za-z0-9.\-]", "_", a.node)
        lines = [f"{hashlib.md5(p.read_bytes()).hexdigest()} *{p.name}" for p in paths]
        (work / "ledger" / f"{safe}.md5").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
        with open(work / "ledger" / "md5_ledger.txt", "a", encoding="utf-8", newline="\n") as fh:
            fh.write("\n".join(lines) + "\n")
        report["chain"]["md5_ledger"] = "written"
        report["md5"] = lines
    report["verdict"] = ("PASS" if passed else "FAIL") + ("(static)" if a.static else "")
    safe = re.sub(r"[^A-Za-z0-9.\-]", "_", a.node)
    (work / "accept" / f"{safe}.json").write_text(json.dumps(report, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"[accept] {a.node} → {report['verdict']}  chain={report['chain']}")
    for x in report["hard"]:
        print(f"  HARD   {x}")
    for x in report["review"]:
        print(f"  REVIEW {x}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
