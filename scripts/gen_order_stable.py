# -*- coding: utf-8 -*-
"""gen_order_stable.py - generator of the order.txt stable-anchor column
(an A4 patch package deliverable; zero apply)

Mission: cure the problem that order.txt line numbers shift with every
registration wave, so papers citing bare line numbers inevitably rot.
Per-line format: <file>#<registration round>-<first 6 of the commit>
(e.g. UpAblLogSelOracle.v#R113-1719a2);
untraceable registration rounds uniformly get #R0-d66910 (the first 6 hex
digits of the R113 baseline md5 d6691094).
Everything after '#' is a metadata column: every consumer must strip the
'#' column first (see consumer_tolerance.patch).

Modes:
  --backfill            one-off ID backfill for the stock lines (reads each
                        tree's order.txt and rewrites the same file; running
                        this same script over the three trees yields one
                        identical value across the three trees)
  --append FILE.v --round R1xx --commit <hash>   append one line at the tail of
                        a registration wave (reordering forbidden; E1 duplicate
                        check / E3 ghost check)
  --verify              hygiene gate: identical values across the three trees +
                        zero duplicates (E1) + zero ghosts (E3) + a valid ID
                        column format
fail-loud: any failed gate exits non-zero; silence is forbidden.
"""
import argparse, hashlib, os, re, sys
from pathlib import Path

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREES = [os.path.join(REPO, "ConstructiveWorld_Live"),
         os.path.join(REPO, "ConstructiveWorld_vo"),
         os.path.join(REPO, "scripts")]
MAP_FILE = os.path.join(REPO, "scripts", "order_stable_map.tsv")
BASELINE6 = "d66910"  # first 6 hex digits of the R113 baseline order.txt md5=d6691094...
ID_RE = re.compile(r"^(?P<fn>[A-Za-z0-9_]+\.v)#(?P<rnd>R\d+)-(?P<h6>[0-9a-f]{6})$")


def read_order(tree):
    p = os.path.join(tree, "order.txt")
    with open(p, encoding="utf-8") as f:
        return p, [l.rstrip("\r\n") for l in f]


def strip_id(line):
    return line.split("#", 1)[0].strip()


def load_map():
    m = {}
    if os.path.exists(MAP_FILE):
        with open(MAP_FILE, encoding="utf-8") as f:
            for ln in f:
                parts = ln.rstrip("\n").split("\t")
                if len(parts) >= 3 and parts[0] != "filename":
                    m[parts[0]] = (parts[1], parts[2])
    return m


def save_map(m):
    buf = ["filename\tround\tcommit6\n"]
    for fn in sorted(m):
        buf.append(f"{fn}\t{m[fn][0]}\t{m[fn][1]}\n")
    Path(MAP_FILE).resolve().write_bytes("".join(buf).encode("utf-8"))


def gates(orders_by_tree, live_tree):
    errs = []
    seqs = {t: [strip_id(l) for l in o] for t, o in orders_by_tree.items()}
    canon = seqs[TREES[0]]
    for t, s in seqs.items():                      # G1: three trees, one identical value (content level)
        if s != canon:
            errs.append(f"G1 三树不同值: {t}")
    seen = {}
    for i, fn in enumerate(canon):                 # E1: zero duplicates
        seen.setdefault(fn, []).append(i + 1)
    dups = {k: v for k, v in seen.items() if len(v) > 1}
    if dups:
        errs.append(f"E1 重复行: {dups}")
    for fn in canon:                               # E3: zero ghosts (must exist in both trees)
        for t in (TREES[0], TREES[1]):
            if not os.path.exists(os.path.join(t, fn)):
                errs.append(f"E3 幽灵行: {fn} 不在 {os.path.basename(t)}")
                break
    for t, o in orders_by_tree.items():            # ID column format validity
        for i, l in enumerate(o, 1):
            if l.strip() and not ID_RE.match(l.strip()):
                errs.append(f"ID格式: {os.path.basename(t)}:{i} [{l}]")
    return errs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--backfill", action="store_true")
    ap.add_argument("--append", metavar="FILE.v")
    ap.add_argument("--round", metavar="R1xx")
    ap.add_argument("--commit", metavar="HASH")
    ap.add_argument("--verify", action="store_true")
    a = ap.parse_args()

    orders = {t: read_order(t)[1] for t in TREES}
    if a.verify or a.backfill:
        pass  # gates run below for verify; backfill pre-checks E1/E3 first

    if a.verify:
        errs = gates(orders, TREES[0])
        for e in errs:
            print("[FAIL]", e)
        print("verify:", "PASS" if not errs else f"FAIL ({len(errs)})")
        sys.exit(1 if errs else 0)

    if a.append:
        if not (a.round and a.commit):
            sys.exit("FATAL: --append 需 --round 与 --commit")
        fn = os.path.basename(a.append)
        for t in (TREES[0], TREES[1]):             # E3 pre-check
            if not os.path.exists(os.path.join(t, fn)):
                sys.exit(f"FATAL E3: {fn} 不在 {os.path.basename(t)}，禁注册幽灵件")
        for t, o in orders.items():                # E1 pre-check
            if fn in [strip_id(l) for l in o]:
                sys.exit(f"FATAL E1: {fn} 已在 {os.path.basename(t)}/order.txt，禁重复注册")
        line = f"{fn}#{a.round}-{a.commit[:6]}"
        for t, o in orders.items():                # tail append (reordering forbidden)
            o.append(line)
            Path(os.path.join(t, "order.txt")).resolve().write_bytes(("\n".join(o) + "\n").encode("utf-8"))
        m = load_map(); m[fn] = (a.round, a.commit[:6]); save_map(m)
        print(f"appended: {line} -> 3 trees + map")
        return

    if a.backfill:
        m = load_map()
        errs = []
        for t, o in orders.items():
            names = [strip_id(l) for l in o]
            dups = {k for k in names if names.count(k) > 1}
            if dups:
                errs.append(f"E1 {os.path.basename(t)}: {sorted(dups)}")
            for fn in names:  # E3 checks only the Live/vo trees (the scripts tree holds no .v files; that is expected)
                for vt in (TREES[0], TREES[1]):
                    if not os.path.exists(os.path.join(vt, fn)):
                        errs.append(f"E3 {os.path.basename(t)}: 幽灵 {fn}")
                        break
        if errs:
            for e in errs:
                print("[FAIL]", e)
            sys.exit("backfill 预检失败，未写任何文件")
        for t, o in orders.items():
            out = []
            for l in o:
                fn = strip_id(l)
                rnd, c6 = m.get(fn, ("R0", BASELINE6))
                out.append(f"{fn}#{rnd}-{c6}")  # R0 also carries the uniform anchor #R0-d66910
            Path(os.path.join(t, "order.txt")).resolve().write_bytes(("\n".join(out) + "\n").encode("utf-8"))
        print(f"backfill done: {len(orders)} trees x {len(out)} lines")
        errs = gates({t: read_order(t)[1] for t in TREES}, TREES[0])
        for e in errs:
            print("[FAIL]", e)
        sys.exit(1 if errs else 0)

    ap.print_help()


if __name__ == "__main__":
    main()
