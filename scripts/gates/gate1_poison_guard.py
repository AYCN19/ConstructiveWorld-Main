#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gate 1: poison-token grep guard (AX-GUARD 20260925) + shell-name anti-resurrection token, plan-B zero-whitelist (R130 EX-PROBE 20260926)
================================================================================
[This file = sandbox draft, not landed. Full diff: the sibling file gate1_shell_token_ablation_zero_whitelist.patch;
 for the difference vs the R7 plan-A form (ratchet-ledger form, _tr130feas_guard_ws sandbox), see section 3 of:
 _tr130exprobe_探针预制报告-20260926.md §三。】

Plan-B form semantics (after the shell ablation, case I, has landed):
  after the shell CW_ConstructiveWorld_219 ablation lands, surviving shell Requires = 0, so the [zero-whitelist
  form] holds -- once the shell-name token is in POISON_TOKENS, any hit (= any newly written or surviving shell
  Require live line) exits 1 directly; no ratchet ledger, no --regen-baseline, no exemption face (R8 vector 5:
  "no exemption-list mechanism needed"). --strict stays as a no-op compatibility flag: accepted, zero behavior
  difference (the only mode under zero-whitelist is strict; kept solely for R7 plan-A CLI/runbook compatibility
  so wiring changes do not turn red). Applies after the shell ablation lands + split retires in the same vote;
  earlier it would bite 1007 surviving shell Require lines (R7 measured), so use the R7 plan-A ratchet form then.

R130 plan-B extension diff (vs AX-GUARD v1.0, base 96272acb):
  [T1] POISON_TOKENS adds exactly 1 token: CW_ConstructiveWorld_219 (the shell aggregate export, full name).
       Full-name match + \\b word boundaries + strict case: the short form CW_219 does not match; the prefixed
       name af_CW_ConstructiveWorld_219 does not match (_ is a word char, no boundary); UpReqIndex comment
       literals are not Require lines, no match (comment stripping + Require-line anchoring, E422 caliber).
  [T2'] --strict kept as a no-op (CLI compatibility flag, see above).
  [T3] Everything else unchanged: comment stripping (nesting-aware), Require-line anchoring, exit codes 0/1/2, --tree/--live-x/--json/--text.

Design points (all from field-surveyed lessons; sources in the _taxguard_ report):
1. Full-name match, strict case -- no short-form traps: the token table uses full names only, project short forms
   banned (CW_219 != the full name). Plus \\b word boundaries + case sensitivity: RealSetoid does not match Reals (AX-MATRIX 1.3 grep -i lesson).
2. Match after comment stripping -- (* Require ... *) comment lines do not false-positive (E422 lesson; whitepaper
   word-list caliber: only live Require lines count). Stripping is (* *) nesting-aware and keeps line numbers unchanged.
3. Only lines containing the Require keyword (incl. From Stdlib Require Import/Export forms, unanchored -- the
   E-ARCH lesson: a ^Require Import anchor misses the From Stdlib forms).
4. fail-loud: hit exit 1; no hit exit 0; missing tree exit 2. No silent downgrade (the zero-whitelist form has no
   ledger-absent path; its fail-loud face is narrower and harder than the plan-A form).

Usage:
  python gate1_poison_guard.py [--tree DIR]... [--json OUT] [--text] [--strict]
  Default tree: the Main Live tree (ConstructiveWorld_Live). Repeat --tree to scan more trees.
  --live-x additionally scans Live_X (850-file surface incl. probe scaffolding; its hits are accounted apart from the main tree).
  Same wiring as CI (coq.yml gate1 pre-build fail-fast step): two trees
  --tree ConstructiveWorld_Live --tree ConstructiveWorld_vo; under bash -e any nonzero exit turns the step red.

R130 landed-version addition (single-file explicit exemption):
  the only exemption face = EXEMPT_FILES={"_t24_probe3.v"} -- user-protected file (content and existence protected
  by explicit user order; no deletion/edit); its shell Require line is the tree's sole remaining place, pending the
  user's final retirement ruling. Exempted hits are still logged one by one (exempted_hits, in text and JSON), never
  silent; outside this file zero-whitelist semantics are unchanged: any other shell-name live Require hit exits 1.

Exit codes: 0 = clean (guard PASS, incl. the form where only the exempt file hits); 1 = poison token hit (guard bites,
incl. shell-name resurrection, outside the exempt file); 2 = invalid tree path.
"""
import os, re, sys, json, argparse, datetime

POISON_TOKENS = [
    "Lra", "Psatz", "Reals", "ClassicalDedekindReals", "FunctionalExtensionality",
    "Micromega", "ClassicalDescription", "Logic.Classical",
    # R130 plan-B [T1]: shell-name anti-resurrection token (full name; zero-whitelist form -- any hit is red, no ledger exemption)
    "CW_ConstructiveWorld_219",
]
TOKEN_RE = re.compile(
    r"\b(" + "|".join(re.escape(t) for t in POISON_TOKENS) + r")\b"
)  # re.escape keeps \. a literal dot; \b sides are judged by word chars -- Logic.Classical matches correctly
REQUIRE_RE = re.compile(r"\bRequire\b")

# Single-file explicit exemption (user-protected file): _t24_probe3.v content and existence are user-protected; its shell
# Require line is the tree's sole remaining place, pending the user's ruling. Exempted hits logged one by one, never silent.
EXEMPT_FILES = {"_t24_probe3.v"}

def strip_comments(text):
    """(* *) nesting-aware comment stripping; non-comment characters kept verbatim (newlines kept -> line numbers unchanged)."""
    out = []
    depth = 0
    i, n = 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1; i += 2
            out.append("  "); continue
        if text.startswith("*)", i) and depth > 0:
            depth -= 1; i += 2
            out.append("  "); continue
        if depth > 0:
            out.append(text[i] if text[i] == "\n" else " ")
            i += 1; continue
        out.append(text[i]); i += 1
    return "".join(out)

def scan_tree(tree):
    hits = []
    exempted = []
    nfiles = 0
    for name in sorted(os.listdir(tree)):
        if not name.endswith(".v"):
            continue
        path = os.path.join(tree, name)
        if not os.path.isfile(path):
            continue
        nfiles += 1
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                raw = f.read()
        except OSError as e:
            hits.append({"file": path, "line": 0, "token": "<IO-ERROR>",
                         "text": str(e), "mtime": None})
            continue
        stripped = strip_comments(raw)
        mtime = datetime.datetime.fromtimestamp(os.path.getmtime(path)).isoformat(timespec="seconds")
        for lineno, (raw_line, st_line) in enumerate(
                zip(raw.splitlines(), stripped.splitlines()), 1):
            if REQUIRE_RE.search(st_line):
                m = TOKEN_RE.search(st_line)
                if m:
                    rec = {"file": path, "line": lineno, "token": m.group(1),
                           "text": raw_line.strip(), "mtime": mtime}
                    if os.path.basename(path) in EXEMPT_FILES:
                        rec["exempted"] = True
                        exempted.append(rec)
                    else:
                        hits.append(rec)
    return nfiles, hits, exempted

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", action="append", default=None,
                    help="树根目录（可多次）")
    ap.add_argument("--live-x", action="store_true",
                    help="附扫 Live_X 树（默认关）")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--text", action="store_true", help="只输出人类可读摘要")
    ap.add_argument("--strict", action="store_true",
                    help="[乙案态 T2'] 兼容 no-op：零白名单形下唯一模式即任何命中即红，"
                         "本旗标零行为差异，仅为 R7 甲案态命令行兼容保留")
    args = ap.parse_args()

    trees = args.tree or [r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live"]
    if args.live_x:
        trees.append(r"D:\ComplexAnalysis\新算法实践\Live_X")

    now = datetime.datetime.now().isoformat(timespec="seconds")
    report = {"scan_time": now, "tokens": POISON_TOKENS, "trees": {}, "total_hits": 0,
              "total_exempted_hits": 0,
              "exempt_files": sorted(EXEMPT_FILES),
              "form": "ablation-zero-whitelist + single-file exemption (R130 乙案态；"
                      "唯一豁免件 _t24_probe3.v=用户禁碰件，豁免命中逐笔留账)"}
    exit_code = 0
    for tree in trees:
        if not os.path.isdir(tree):
            print(f"[gate1] FATAL: 树不存在: {tree}", file=sys.stderr)
            return 2
        nfiles, hits, exempted = scan_tree(tree)
        report["trees"][tree] = {"v_files": nfiles, "hits": hits, "exempted_hits": exempted}
        report["total_hits"] += len(hits)
        report["total_exempted_hits"] += len(exempted)
        status = "FAIL(守卫咬合:命中毒token)" if hits else "PASS(洁净)"
        print(f"[gate1] 树={tree}  .v数={nfiles}  命中={len(hits)}  "
              f"豁免件命中={len(exempted)}  判定={status}  扫描时点={now}")
        for h in hits:
            print(f"  HIT {h['file']}:{h['line']}  token={h['token']}  mtime={h['mtime']}")
            print(f"      {h['text']}")
        for h in exempted:
            print(f"  EXEMPTED(用户禁碰件豁免留账) {h['file']}:{h['line']}  token={h['token']}")
            print(f"      {h['text']}")
    if report["total_hits"]:
        exit_code = 1
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=1)
    return exit_code

if __name__ == "__main__":
    sys.exit(main())
