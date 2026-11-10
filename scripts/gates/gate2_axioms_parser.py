#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gate 2 CI "Axioms section = 0" sentinel: block state-machine parser for the
coqchk log (AX-GUARD 20260925)
==========================================================================
Parses the coqchk (-o) log with a **block state machine** and outputs the actual
axiom list; naive grep is forbidden.

Why not naive grep (observed on this machine):
- The local _chk_all.log has 88 `checking cst:` lines whose names contain the
  substring error
  (Corelib.Init.Specif.error / Stdlib.Lists.List.hd_error / nth_error /
  PadeErrorIntegral family...) - bare-word grep (-i error / -i axiom) matches
  every one of them falsely.
- Lesson E422: the 2212 bare-word hits for "axiom" were all stdlib
  NZAxioms/ZAxioms module type names.
- This parser's scope discipline: **only a line inside the `Axioms:` section
  can possibly be judged an axiom**; every line outside a section (checking
  cst / intern / module names) never enters the list - a false match is
  structurally impossible.

State machine:
  S0 scan lines -> on the `[*] Axioms:` header ->
      header line inline `<none>` -> record an empty section (CLEAN evidence)
      -> back to S0
      header line inline names   -> record the single entry
      header line inline empty  -> S1 collect the section
  S1 collect section -> a line that is an indented entry (starts with >= 2
            spaces and is non-empty) -> record the axiom;
            an empty line / the next section header (starts with `*`) / a non
            indented line -> back to S0

Verdict (the three E943-discipline readings):
  exit 0 = CLEAN (every Axioms section is empty and the log is complete with
  "Modules were successfully checked")
  exit 1 = DIRTY (some Axioms section is non-empty; the three target axioms
  are listed separately)
  exit 2 = NO_AXIOMS_SECTION (the log has no Axioms section - usually coqchk
  ran without -o; undecidable, fail-loud)
  exit 3 = LOG_INCOMPLETE (no "Modules were successfully checked" tail line -
  the log is truncated or still being written)

Target axioms (the three-piece set adjudicated by AX-RECIPE/AX-MATRIX,
anchored by full names):
  Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep
  Stdlib.Reals.ClassicalDedekindReals.sig_not_dec
  Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec

Usage:
  python gate2_axioms_parser.py LOG [LOG...] [--json OUT]
  python gate2_axioms_parser.py --naive-demo LOG   # demo contrasting naive grep false matches with this parser
"""
import os, re, sys, json, argparse, datetime

TARGET_AXIOMS = [
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
    "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec",
    "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec",
]
# Whitelist classes of naive-grep false matches (legal constant/module
# families whose names contain the substring error); used only for the
# --naive-demo contrast. Under this parser's state-machine scope discipline
# such lines never enter the list.
NAIVE_FALSE_CLASSES = [
    r"checking cst:\S*error", r"checking cst:\S*Error",
]
AXIOM_HEADER_RE = re.compile(r"^\*?\s*Axioms:\s*(.*)$")
ENTRY_RE = re.compile(r"^\s{2,}(\S.*?)\s*$")
SECTION_NEXT_RE = re.compile(r"^\*\s?|\s=+$")
COMPLETE_MARK = "Modules were successfully checked"

def parse_log(path):
    """Block state-machine parse. Returns a dict: sections / axioms / complete / stats."""
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = f.read().splitlines()
    sections = []          # [{line_no, entries:[...], inline:none|str}]
    axioms = []            # all axioms (with the line number of their owning section)
    in_axioms = False
    cur = None
    complete = False
    naive_error_lines = 0
    for lineno, line in enumerate(lines, 1):
        if COMPLETE_MARK in line:
            complete = True
        if re.search(r"checking cst:\S*(error|Error)", line):
            naive_error_lines += 1
        if in_axioms:
            if line.strip() == "" or SECTION_NEXT_RE.match(line):
                in_axioms = False
                cur = None
                continue
            m = ENTRY_RE.match(line)
            if m:
                entry = m.group(1).strip()
                axioms.append(entry)
                cur["entries"].append(entry)
                continue
            in_axioms = False
            cur = None
            continue
        m = AXIOM_HEADER_RE.match(line)
        if m:
            rest = m.group(1).strip()
            cur = {"line_no": lineno, "entries": [], "inline": None}
            sections.append(cur)
            if rest == "<none>":
                cur["inline"] = "<none>"
            elif rest:
                cur["inline"] = rest
                axioms.append(rest)
            else:
                in_axioms = True
    return {
        "log": path,
        "log_mtime": datetime.datetime.fromtimestamp(os.path.getmtime(path)).isoformat(timespec="seconds"),
        "complete": complete,
        "sections": sections,
        "axioms": axioms,
        "naive_error_lines": naive_error_lines,
    }

def verdict(res):
    targets = sorted(set(res["axioms"]) & set(TARGET_AXIOMS))
    others = sorted(set(res["axioms"]) - set(TARGET_AXIOMS))
    if not res["sections"]:
        return 2, "NO_AXIOMS_SECTION", targets, others
    if not res["complete"]:
        return 3, "LOG_INCOMPLETE", targets, others
    if res["axioms"]:
        return 1, "DIRTY", targets, others
    return 0, "CLEAN", targets, others

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("logs", nargs="*")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--naive-demo", action="store_true",
                    help="附印朴素 grep 假匹配对照（教育用）")
    args = ap.parse_args()
    if not args.logs:
        ap.error("至少一个日志路径")

    final = 0
    out = []
    for path in args.logs:
        if not os.path.isfile(path):
            print(f"[gate2] FATAL: 日志不存在: {path}", file=sys.stderr)
            return 2
        res = parse_log(path)
        code, v, targets, others = verdict(res)
        final = max(final, code)
        print(f"[gate2] 日志={res['log']}  mtime={res['log_mtime']}")
        print(f"  判定={v}(exit {code})  Axioms段数={len(res['sections'])}  公理总数={len(res['axioms'])}"
              f"  日志完整={res['complete']}")
        if targets:
            print(f"  靶公理命中 {len(targets)}/3:")
            for t in targets:
                print(f"    TARGET {t}")
        for o in others:
            print(f"    OTHER  {o}")
        if v == "NO_AXIOMS_SECTION":
            print("  !! 日志无 Axioms 段——通常系 coqchk 未带 -o（无 CONTEXT SUMMARY）。"
                  "本日志不可作公理判读依据（fail-loud，不静默当 CLEAN）。")
        if v == "LOG_INCOMPLETE":
            print("  !! 日志缺「Modules were successfully checked」尾行——被截断或在写。不可判。")
        if args.naive_demo:
            n_err = res["naive_error_lines"]
            n_axiom_word = 0
            with open(path, encoding="utf-8", errors="replace") as f:
                for ln in f:
                    if re.search(r"[Aa]xiom", ln):
                        n_axiom_word += 1
            print(f"  [naive对照] 裸 grep -i error 假匹配行={n_err}（白名单假匹配类："
                  f"Corelib.Init.Specif.error/hd_error/nth_error/PadeErrorIntegral 族）；"
                  f"裸 grep -i axiom 命中={n_axiom_word}（NZAxioms/ZAxioms 模块名假匹配族，E422 教训）；"
                  f"本解析器实际公理={len(res['axioms'])}。")
        out.append(res)
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(out, f, ensure_ascii=False, indent=1)
    return final

if __name__ == "__main__":
    sys.exit(main())
