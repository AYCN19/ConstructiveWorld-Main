#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gate 3: cross-tree poison-token diff + shell-module-set membership check extension (AX-GUARD 20260925 + R130 plan-B draft 20260926)
================================================================================
[Sandbox draft, not landed (do not modify repository gate scripts). Full diff: the sibling file gate3_module_membership_ablation.patch;
 semantic basis = R18 section 2 ruling (E4): the gate3 extension must be a [module-set membership check], not diff-shaped --
 the current diff logic is blind to "symmetric resurrection in both trees" (symmetry = no diff), exactly this extension's
 independent value. R2 section 10.2 same; gate1 tokens (plan-B zero-whitelist form) cover the Require-line face, this
 extension the file/module face; the union is a superset of the S3 gate6 Require-prefix grep.]

Current-gate semantics (AX-GUARD 20260925, E957 lesson embedded, kept unchanged):
  per-module comparison of both trees' comment-stripped Require line sets (whitespace normalized), two levels:
  [SINGLE-TREE-POISON] one tree's Require lines carry poison tokens, the other's same module does not -> exit 1 (main biting face)
  [REQUIRE-DRIFT]      Require lines differ but neither is poisonous -> exit 0, recorded only (hygiene information)

R130 plan-B extension ([M1], runs before the current poison-face comparison):
  each of --tree-a/--tree-b gets an independent [membership check] (not a cross-tree comparison, so symmetric resurrection bites per tree):
  [RESURRECT-MODULE]   the tree module set (top-level .v base names) contains CW_ConstructiveWorld_219 -> exit 1
                       (shell file/module-face resurrection: renamed bytes, git checkout, generator re-run)
  [RESURRECT-REQUIRE]  any live Require line (comment-stripped) of any .v contains CW_ConstructiveWorld_219 -> exit 1
                       (shell dependency-line face; same semantics as gate1's plan-B token, each tree independent)

R130 landed-version addition (single-file explicit exemption): the only exemption face = EXEMPT_FILES={"_t24_probe3.v"} --
  user-protected file (content and existence protected by explicit user order); its shell Require line is the tree's sole
  remaining place, pending the user's final retirement ruling; exempts only the [RESURRECT-REQUIRE] line face, each hit
  logged (exempted_hits); the module-face membership check is not exempt; outside this file the semantics are unchanged.
  Loud-stop discipline (R13 card 1 wording, merged per E4): on a hit, first run the digest trio (md5 + size + mtime against
  the deletion/snapshot ledger) to classify "residue vs resurrection"; no verdict before proof (R13 B-GO 63/63 residue case).

Scan-domain note: --tree-a/b each get a top-level flat scan (same domain as gate1 --tree); CW219_split is not in the default
domain -- if split is not retired in the same vote as the shell ablation (runbook cut 5), add it via --tree-a/--tree-b or wire a
third tree; once retired it leaves the domain naturally (R7 section 2: zero consumption holds; the coq.yml third --tree todo is void).

Usage:
  python gate3_cross_tree_diff.py [--tree-a DIR] [--tree-b DIR] [--json OUT]
  Default A = Main Live tree, B = vo mirror tree (both trees' .v files on disk).
Exit codes: 0 = no single-tree poison divergence and no shell-resurrection membership hit; 1 = a single-tree poison
        divergence or a shell-resurrection membership hit (hard red); 2 = invalid tree path.
"""
import os, re, sys, json, argparse, datetime

POISON_TOKEN_RE = re.compile(
    r"\b(Lra|Psatz|Reals|ClassicalDedekindReals|FunctionalExtensionality|"
    r"Micromega|ClassicalDescription|Logic\.Classical)\b")
REQUIRE_LINE_RE = re.compile(r"\bRequire\b")

# [M1] R130 plan-B extension: shell-module forbidden set (module-set membership check, not diff-shaped -- symmetric resurrection also bites)
SHELL_MODULE = "CW_ConstructiveWorld_219"
SHELL_NAME_RE = re.compile(r"\bCW_ConstructiveWorld_219\b")

# Single-file explicit exemption (user-protected file): _t24_probe3.v content and existence are user-protected;
# its shell Require line is the tree's sole remaining place, pending the user's retirement ruling. Exempts only
# [RESURRECT-REQUIRE] line-face hits (each logged in exempted_hits); the module-face membership check is not exempt.
EXEMPT_FILES = {"_t24_probe3.v"}

def strip_comments(text):
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

def require_face(path):
    """Return this .v file's Require lines (comments stripped, whitespace normalized)."""
    with open(path, encoding="utf-8", errors="replace") as f:
        raw = f.read()
    st = strip_comments(raw)
    reqs = []
    for raw_line, st_line in zip(raw.splitlines(), st.splitlines()):
        if REQUIRE_LINE_RE.search(st_line):
            reqs.append(re.sub(r"\s+", " ", st_line.strip()))
    return reqs

def load_tree(tree):
    mods = {}
    for name in os.listdir(tree):
        if name.endswith(".v") and os.path.isfile(os.path.join(tree, name)):
            mods[name[:-2]] = os.path.join(tree, name)
    return mods

def membership_check(tree_tag, tree, mods):
    """[M1] module-set membership check: module face + Require-line face, each tree independent (symmetric resurrection also bites)."""
    hits = []
    exempted = []
    # face 1: module-set membership -- tree module set intersect the forbidden set (no exemption: the shell file existing is red)
    if SHELL_MODULE in mods:
        hits.append({"tree": tree_tag, "kind": "RESURRECT-MODULE",
                     "module": SHELL_MODULE, "file": mods[SHELL_MODULE],
                     "line": None, "text": "<壳文件/模块存在于树模块集>"})
    # face 2: Require-line membership -- any live .v Require line containing the shell name (exempt-file hits logged
    # per line, no bite; m is the .v-stripped module base name -- the suffix is re-added to match the exemption table)
    for m in sorted(mods):
        if (m + ".v") in EXEMPT_FILES:
            try:
                for lineno, r in enumerate(require_face(mods[m]), 1):
                    if SHELL_NAME_RE.search(r):
                        exempted.append({"tree": tree_tag, "kind": "RESURRECT-REQUIRE",
                                         "module": m, "file": mods[m], "line": lineno,
                                         "text": r, "exempted": True})
            except OSError:
                pass
            continue
        try:
            for lineno, r in enumerate(require_face(mods[m]), 1):
                if SHELL_NAME_RE.search(r):
                    hits.append({"tree": tree_tag, "kind": "RESURRECT-REQUIRE",
                                 "module": m, "file": mods[m], "line": lineno,
                                 "text": r})
        except OSError:
            hits.append({"tree": tree_tag, "kind": "RESURRECT-REQUIRE",
                         "module": m, "file": mods[m], "line": 0,
                         "text": "<IO-ERROR>"})
    return hits, exempted

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree-a", default=r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_Live")
    ap.add_argument("--tree-b", default=r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo")
    ap.add_argument("--json", dest="jsonout", default=None)
    args = ap.parse_args()
    for t in (args.tree_a, args.tree_b):
        if not os.path.isdir(t):
            print(f"[gate3] FATAL: 树不存在: {t}", file=sys.stderr)
            return 2
    A, B = load_tree(args.tree_a), load_tree(args.tree_b)
    now = datetime.datetime.now().isoformat(timespec="seconds")
    # [M1] membership before diff: a membership hit = a concrete shell-resurrection candidate, exit 1 hard red
    rA, eA = membership_check("A", args.tree_a, A)
    rB, eB = membership_check("B", args.tree_b, B)
    resurrect = rA + rB
    exempted_hits = eA + eB
    common = sorted(set(A) & set(B))
    only_a, only_b = sorted(set(A) - set(B)), sorted(set(B) - set(A))
    poison_div, drift = [], []
    for m in common:
        ra, rb = require_face(A[m]), require_face(B[m])
        pa = [r for r in ra if POISON_TOKEN_RE.search(r)]
        pb = [r for r in rb if POISON_TOKEN_RE.search(r)]
        if pa != pb:  # poison face asymmetric across the two trees
            poison_div.append({"module": m, "a_lines": pa, "b_lines": pb})
        elif ra != rb:
            drift.append({"module": m, "a_lines": ra, "b_lines": rb})
    print(f"[gate3] 时点={now}  形态=diff＋壳模块集隶属检查扩条（R18 E4/R2 §十.2）")
    print(f"  树A={args.tree_a}  .v={len(A)}")
    print(f"  树B={args.tree_b}  .v={len(B)}")
    print(f"  共同模块={len(common)}  仅A={len(only_a)}  仅B={len(only_b)}")
    print(f"  [豁免留账] 用户禁碰件豁免命中={len(exempted_hits)} 笔（_t24_probe3.v 壳 Require 行，候用户终裁退役与否）")
    for h in exempted_hits:
        print(f"    EXEMPTED 树{h['tree']} {h['module']}.v:{h['line']}  {h['text']}")
    if resurrect:
        print(f"  判定=FAIL（壳模块集隶属命中 {len(resurrect)} 笔——CW_ConstructiveWorld_219 复活实锤候选）")
        for h in resurrect:
            print(f"    {h['kind']} 树{h['tree']} {h['module']}.v:{h['line'] or '-'}  {h['file']}")
            print(f"      {h['text']}")
        print("  [响停纪律] 先跑 digest 三件套（md5+size+mtime 对删除/快照台账）定性"
              "「残留 vs 复活」再处置，禁未证先判（R13 B-GO 63/63 残留判例）。")
    else:
        print("  [M1] 壳模块集隶属检查=PASS（两树模块集与 Require 行面均无 CW_ConstructiveWorld_219）")
    for m in only_a:
        print(f"    ONLY-A {m}.v")
    for m in only_b:
        print(f"    ONLY-B {m}.v")
    if poison_div:
        print(f"  判定=FAIL（单树毒分歧 {len(poison_div)} 件——E957 暗雷族/世系倒灌嫌疑）")
        for d in poison_div:
            print(f"    SINGLE-TREE-POISON {d['module']}.v")
            print(f"      A({os.path.basename(args.tree_a)}): {d['a_lines'] or '（无毒行）'}")
            print(f"      B({os.path.basename(args.tree_b)}): {d['b_lines'] or '（无毒行）'}")
    elif not resurrect:
        print("  判定=PASS（共同模块毒面两树全对称＋壳零隶属）")
    if drift:
        print(f"  [登记] 无毒 Require 漂移 {len(drift)} 件（卫生信息）:")
        for d in drift[:20]:
            print(f"    REQUIRE-DRIFT {d['module']}.v")
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump({"time": now, "form": "diff+module-membership (R130 乙案扩条＋单条文件级豁免)",
                       "shell_module": SHELL_MODULE,
                       "exempt_files": sorted(EXEMPT_FILES),
                       "resurrection_hits": resurrect,
                       "exempted_hits": exempted_hits,
                       "poison_divergence": poison_div,
                       "require_drift": drift, "only_a": only_a, "only_b": only_b},
                      f, ensure_ascii=False, indent=1)
    return 1 if (resurrect or poison_div) else 0

if __name__ == "__main__":
    sys.exit(main())
