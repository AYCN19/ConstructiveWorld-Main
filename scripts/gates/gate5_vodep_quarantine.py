#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Gate 5: .vo/.vos/.vok binary dependency-layer quarantine (GATE-VOQ 20260926)
========================================================
Radius the source-level Gate 1 (gate1) cannot see: dormant poisoned binaries. Case E-STAGING-AXFORENSIC-1
(cw-ci-sop 6.B fourth kind): poisoned .vo files from the R109/R111 era lay dormant in sandbox worlds and
re-seeded the three classic axioms across batches by filename, not digest -- gate1 source-level green and
coqchk Axioms listings never intersect; the carrier hides in the .vo dependency-string table. This gate scans
all .vo/.vos/.vok binaries (token-string + poison-digest blacklists) before coqchk aggregates its closure.

Design points (all sourced from field-surveyed cases; see the _tgatevoq_ quarantine-radius report):
1. Decompression-aware scanning (VO-SCAN/AXFORENSIC cases): the .vo dependency-string table sits inside
   the gzip stream; a bare binary grep fakes zero hits -- scan the raw bytes plus every decompressed
   gzip (\\x1f\\x8b) and zlib (\\x78\\x9c) stream, blob by blob.
2. Platform control group built in (anti glob illusion, fail-loud): the scanner must SELF-HIT the
   platform's own ClassicalDedekindReals.vo; a missing control file or a failed self-hit = method
   unproven -- always exit 2, never green (zero hits are not credible without a control self-check).
3. All five token families scanned and reported, hard/soft split (main-tree 2477-file survey, 20260926):
   - Hard four families (hit = exit 1): Lra / Reals / ClassicalDedekindReals / FunctionalExtensionality --
     the certified clean main tree (Axioms=<none>) measured 0/0/0/0, while all five poison generations
     (43f866e8 etc.) carry Lra; \\b word boundaries + case sensitive (gate1 style): clean project
     names such as ConstructiveReals/Qreals do not mismatch.
   - Soft one family (recorded, not red; --strict-psatz promotes to hard): Psatz -- carried in the string
     tables of 172 clean main-tree files (micromega Q-domain supply of the Lia closure; AXFORENSIC 1.1
     verdict "not poison"); source-level Require Psatz is gate1's hard gate, binary strings are not evidence.
4. Poison-digest blacklist (md5): a same-name vo defeats the clean-by-name assumption (main tree a4b1c953
   clean vs P2 world 43f866e8 poisoned), so everything reconciles by digest; hits list the blacklist
   ledger name; a differing on-disk filename raises name_mismatch=true (rename-poison detection).
5. fail-loud: hits exit 1; no scannable surface / invalid tree / failed control / empty blacklist / scan
   errors (incomplete surface) all exit 2; exit 0 requires all three: full scan + control pass + zero hits.
6. Constructive-reals island context exemption (20261006 calibration, run #201 case): the stdlib
   constructive zero-axiom reals -- Stdlib.Reals.Cauchy.ConstructiveCauchyReals,
   Stdlib.Reals.Abstract.ConstructiveReals, same-subtree QExtra/ConstructiveExtra, etc. -- always embed the
   path segment Reals and clash with the hard token Reals (which targets the classical Stdlib.Reals.*
   poison face). Mechanical criteria (two mechanisms, calibrated on real born-vo bytes): (a) the maximal
   contiguous path run around the Reals hit ([A-Za-z0-9_./\\] chars only) contains an island name as a
   whole word; (b) under the leaf-first length-prefixed segment-list encoding, the segment left-adjacent
   to the hit (word1, gap<=4 structural bytes) is an island name or in {Cauchy,Abstract}. Either ->
   informational (exempted_island counted separately, verdict transparent); rightward gap crossing forbidden
   (neighbor digest barrier blocks serial exemption); all other Reals hits (ClassicalDedekindReals/Rbase/
   Raxioms/Lra segments, bare segments) stay hard; the digest layer takes no exemption (poison digests bite).

Usage:
  python gate5_vodep_quarantine.py [--tree DIR]... [--blacklist FILE]
      [--control PATH|off] [--strict-psatz] [--json OUT] [--text]
  Default tree: the main vo tree ConstructiveWorld_vo (repeat --tree to scan more trees/worlds; recursive).

Exit codes: 0 = clean (full scan + control pass + zero hits); 1 = hit (hard token or blacklist digest --
quarantine bites); 2 = no scannable surface / invalid tree / failed control / empty blacklist / scan error (red).
"""
import os, re, sys, io, zlib, gzip, json, hashlib, argparse, datetime

HARD_TOKENS = ["Lra", "Reals", "ClassicalDedekindReals", "FunctionalExtensionality"]
SOFT_TOKENS = ["Psatz"]  # informational tier; --strict-psatz promotes it to hard (section 3 calibration note)
ALL_TOKENS = HARD_TOKENS + SOFT_TOKENS
TOKEN_RES = {
    t: re.compile(rb"(?<![A-Za-z0-9_])" + t.encode() + rb"(?![A-Za-z0-9_])")
    for t in ALL_TOKENS
}
# Design point 6: constructive-reals island names + contiguous-path char class (island
# exemption applies only to the token Reals). Byte calibration (run #201 same-source born-vo
# survey, 20261006): the .vo dependency face stores two shapes -- (1) dot/slash contiguous strings
# (Stdlib.Reals.Cauchy.ConstructiveCauchyReals); (2) leaf-first length-prefixed segment lists
# (segments 1-2 structural bytes apart). Constructive subtree = Stdlib.Reals.{Cauchy,Abstract}.*
# (QExtra/ConstructiveExtra live in the Cauchy dir too); subtree segments judged by name; other hits hard.
CONSTRUCTIVE_ISLANDS = ["ConstructiveCauchyReals", "ConstructiveReals"]
CONSTRUCTIVE_SUBTREE_SEGS = ["Cauchy", "Abstract"]
ISLAND_RES = [
    (t, re.compile(rb"(?<![A-Za-z0-9_])" + t.encode() + rb"(?![A-Za-z0-9_])"))
    for t in CONSTRUCTIVE_ISLANDS
]
RUN_CHAR_RE = re.compile(rb"[A-Za-z0-9_./\\]")
WORD_RE = re.compile(rb"[A-Za-z0-9_]+")
MAX_SEG_GAP = 4  # cap on structural bytes between segments (measured 1-2; the 16-byte digest barrier always exceeds it)
SCAN_SUFFIXES = (".vo", ".vos", ".vok")
MAX_FILE_BYTES = 512 * 1024 * 1024  # per-file IO safety cap; over-cap counts as ERR (fail-loud)

CONTROL_NAME = "ClassicalDedekindReals.vo"
CONTROL_TOKEN = "ClassicalDedekindReals"
CONTROL_BASES = [
    "C:/Rocq-Platform~9.1~2026.01/lib/coq",  # pinned generation first (SW2: an inherited env value may be an old 9.0)
    os.environ.get("COQLIB"),
    os.environ.get("ROCQLIB"),
]


def blobs_of(path):
    """raw bytes + all gzip streams + zlib streams decompressed into blobs (VO-SCAN prototype lineage; case-verified)."""
    with open(path, "rb") as f:
        data = f.read()
    blobs = [data]
    i = 0
    while True:
        i = data.find(b"\x1f\x8b", i)
        if i < 0:
            break
        try:
            blobs.append(gzip.GzipFile(fileobj=io.BytesIO(data[i:])).read())
        except Exception:
            pass
        i += 1
    j = 0
    while True:
        j = data.find(b"\x78\x9c", j)
        if j < 0:
            break
        try:
            blobs.append(zlib.decompressobj().decompress(data[j : j + 2000000]))
        except Exception:
            pass
        j += 1
    return blobs


def reals_island_name(blob, start, end):
    """Island context verdict at a Reals hit: return the exemption reason (island name / subtree segment),
    else None (stays hard). Two mechanisms (byte calibration: design point 6): (a) contiguous path run --
    the maximal [A-Za-z0-9_./\\] run around the hit contains an island name whole-word (dot/slash shapes);
    (b) leftward segment neighborhood -- under the leaf-first segment-list encoding, walk left from the hit
    across <= MAX_SEG_GAP non-word bytes reading word1 only; word1 in island names or the constructive
    subtree segments (Cauchy/Abstract) -> exempt. No rightward gap reading: the neighbor entry's 16-byte
    digest is a barrier; reading across it risks serial exemption (defense-in-depth floor)."""
    lo = start
    while lo > 0 and RUN_CHAR_RE.match(blob[lo - 1 : lo]):
        lo -= 1
    hi = end
    n = len(blob)
    while hi < n and RUN_CHAR_RE.match(blob[hi : hi + 1]):
        hi += 1
    run = blob[lo:hi]
    for name, res in ISLAND_RES:
        if res.search(run):
            return name
    # (b) leftward segment neighborhood: word1 = the adjacent segment (this entry's leaf segment, leaf-first encoding as measured)
    pos = start
    gap = 0
    while pos > 0 and gap <= MAX_SEG_GAP and not WORD_RE.match(blob[pos - 1 : pos]):
        pos -= 1
        gap += 1
    if 0 < gap <= MAX_SEG_GAP and pos > 0:
        wend = pos
        while wend > 0 and WORD_RE.match(blob[wend - 1 : wend]):
            wend -= 1
        word1 = blob[wend:pos]
        if word1 in CONSTRUCTIVE_ISLANDS:
            return word1.decode("ascii")
        if word1 in [s.encode("ascii") for s in CONSTRUCTIVE_SUBTREE_SEGS]:
            return "Reals/" + word1.decode("ascii")
    return None


def scan_tokens(path):
    """Return (hard/soft hit token set, island exemption records, err or None).

    Token Reals is classified per occurrence: island-context occurrences become informational (recorded in
    exempted); any occurrence without island context makes the token hard in hits. Other tokens: unchanged."""
    try:
        hits = set()
        exempted = []
        for b in blobs_of(path):
            for t in ALL_TOKENS:
                if t in hits:
                    continue
                if t == "Reals":
                    for m in TOKEN_RES[t].finditer(b):
                        island = reals_island_name(b, m.start(), m.end())
                        if island is None:
                            hits.add(t)
                            break
                        rec = {"token": t, "island": island}
                        if rec not in exempted:
                            exempted.append(rec)
                elif TOKEN_RES[t].search(b):
                    hits.add(t)
        return hits, exempted, None
    except Exception as e:  # OSError/EOFError/MemoryError etc. -- fail-loud accounting
        return set(), [], str(e)[:80]


def md5_of(path):
    h = hashlib.md5()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def find_control():
    """Platform control group locator: find ClassicalDedekindReals.vo under COQLIB/ROCQLIB/the standard install."""
    cands = []
    for base in CONTROL_BASES:
        if not base or not os.path.isdir(base):
            continue
        for rel in (
            os.path.join("user-contrib", "Stdlib", "Reals", CONTROL_NAME),
            os.path.join("Stdlib", "Reals", CONTROL_NAME),
        ):
            p = os.path.join(base, rel)
            if os.path.isfile(p):
                return p
        for dp, dn, fn in os.walk(base):
            if CONTROL_NAME in fn:
                cands.append(os.path.join(dp, CONTROL_NAME))
                break
    return cands[0] if cands else None


def load_blacklist(path):
    """Poison-digest blacklist: first field per line = 32-char lowercase md5; text after # is a comment."""
    entries = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = line.split()
            digest = parts[0].lower()
            name = parts[1] if len(parts) > 1 else ""
            if not re.fullmatch(r"[0-9a-f]{32}", digest):
                raise ValueError(f"blacklist 格式非法: {digest!r} in {path}")
            entries[digest] = name
    return entries


def scan_tree(tree, blacklist, strict_psatz):
    files = errors = 0
    token_hits = []   # hard hits (Psatz included when --strict)
    soft_hits = []    # Psatz informational tier
    digest_hits = []
    island_exempt = []  # Reals hits whose context is a constructive-reals island -- informational (design point 6)
    for dp, dn, fn in os.walk(tree):
        for name in sorted(fn):
            if not name.endswith(SCAN_SUFFIXES):
                continue
            path = os.path.join(dp, name)
            rel = os.path.relpath(path, tree)
            try:
                if os.path.getsize(path) > MAX_FILE_BYTES:
                    raise OSError(f"file exceeds {MAX_FILE_BYTES} bytes cap")
            except OSError as e:
                errors += 1
                token_hits.append({"file": rel, "token": "<IO-ERROR>", "digest": None,
                                   "name_mismatch": None, "err": str(e)})
                continue
            files += 1
            hits, exempted, err = scan_tokens(path)
            if err:
                errors += 1
                token_hits.append({"file": rel, "token": "<SCAN-ERROR>", "digest": None,
                                   "name_mismatch": None, "err": err})
            digest = None
            if blacklist:
                try:
                    digest = md5_of(path)
                except OSError as e:
                    errors += 1
                    token_hits.append({"file": rel, "token": "<MD5-ERROR>", "digest": None,
                                       "name_mismatch": None, "err": str(e)[:80]})
                else:
                    if digest in blacklist:
                        digest_hits.append({
                            "file": rel, "digest": digest,
                            "blacklist_name": blacklist[digest],
                            "name_mismatch": os.path.basename(path) != blacklist[digest],
                        })
            for rec in exempted:
                if rec["token"] not in hits:  # a hard occurrence of the same token in the same file voids the exemption
                    island_exempt.append({"file": rel, "token": rec["token"],
                                          "island": rec["island"], "digest": digest})
            for t in sorted(hits):
                rec = {"file": rel, "token": t, "digest": digest,
                       "name_mismatch": None, "err": None}
                if t in HARD_TOKENS or (strict_psatz and t in SOFT_TOKENS):
                    token_hits.append(rec)
                else:
                    soft_hits.append(rec)
    return {"files": files, "errors": errors,
            "token_hits": token_hits, "soft_hits": soft_hits,
            "digest_hits": digest_hits, "island_exempt": island_exempt}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", action="append", default=None,
                    help="树/世界根目录（可多次，递归扫 .vo/.vos/.vok）")
    ap.add_argument("--blacklist", default=os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "poison_digest_blacklist_v2.txt"),
        help="毒 digest 黑名单（默认=同目录 vendored v2）")
    ap.add_argument("--control", default="auto",
                    help="platform 对照组 ClassicalDedekindReals.vo 路径；auto=自动定位；off=关闭（自担零命中不可信风险）")
    ap.add_argument("--strict-psatz", action="store_true",
                    help="Psatz 由信息档升为硬命中（默认关：净主树 172 件串表携带判例）")
    ap.add_argument("--json", dest="jsonout", default=None)
    ap.add_argument("--text", action="store_true", help="只输出人类可读摘要")
    args = ap.parse_args()

    now = datetime.datetime.now().isoformat(timespec="seconds")
    trees = args.tree or [
        r"D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo"]
    report = {
        "scan_time": now, "tool": "gate5_vodep_quarantine",
        "hard_tokens": HARD_TOKENS, "soft_tokens": SOFT_TOKENS,
        "constructive_islands": CONSTRUCTIVE_ISLANDS,
        "strict_psatz": args.strict_psatz, "trees": {}, "control": {},
        "blacklist": {}, "total_files": 0, "total_errors": 0,
        "total_token_hits": 0, "total_soft_hits": 0, "total_digest_hits": 0,
        "exempted_island": 0,
    }
    exit_code = 0
    fatal = None

    # Blacklist load: missing / empty / invalid file = method failure, exit 2 (fail-loud)
    try:
        blacklist = load_blacklist(args.blacklist)
        if not blacklist:
            raise ValueError("blacklist 为空")
    except Exception as e:
        print(f"[gate5] FATAL: 黑名单不可用: {args.blacklist} ({e})", file=sys.stderr)
        return 2
    report["blacklist"] = {"path": args.blacklist, "entries": len(blacklist)}

    # Control self-check: no SELF-HIT = scan method unproven, exit 2 (anti glob zero-hit illusion)
    if args.control != "off":
        cpath = args.control if args.control != "auto" else find_control()
        if not cpath or not os.path.isfile(cpath):
            print("[gate5] FATAL: 对照组 ClassicalDedekindReals.vo 未定位到——"
                  "无 SELF-HIT 校准的零命中不可信（glob 假象判例）", file=sys.stderr)
            report["control"] = {"path": cpath, "status": "CONTROL-ABSENT"}
            fatal = "control-absent"
        else:
            hits, _exempted, err = scan_tokens(cpath)
            ok = CONTROL_TOKEN in hits and err is None
            report["control"] = {"path": cpath, "status": "CONTROL-SELF-HIT-PASS" if ok
                                 else "CONTROL-SELF-HIT-FAIL", "tokens": sorted(hits),
                                 "err": err}
            if not ok:
                print(f"[gate5] FATAL: 对照组自命中失败: {cpath} hits={sorted(hits)} err={err}",
                      file=sys.stderr)
                fatal = "control-fail"
            else:
                print(f"[gate5] 对照组 SELF-HIT PASS: {cpath} tokens={sorted(hits)}")
        if fatal:
            if args.jsonout:
                with open(args.jsonout, "w", encoding="utf-8") as f:
                    json.dump(report, f, ensure_ascii=False, indent=1)
            print(f"[gate5] GATE5-VERDICT: {fatal.upper()} exit 2（不可判绿，fail-loud）")
            return 2

    for tree in trees:
        if not os.path.isdir(tree):
            print(f"[gate5] FATAL: 树不存在: {tree}", file=sys.stderr)
            report["trees"][tree] = {"error": "tree-missing"}
            fatal = "tree-missing"
            break
        res = scan_tree(tree, blacklist, args.strict_psatz)
        report["trees"][tree] = res
        for k, t in (("total_files", "files"), ("total_errors", "errors"),
                     ("total_token_hits", None), ("total_soft_hits", None),
                     ("total_digest_hits", None)):
            report[k] += res[t] if t is not None else len(res[k.replace("total_", "")])
        report["exempted_island"] += len(res["island_exempt"])
        status = ("HIT(检疫咬合)" if res["token_hits"] or res["digest_hits"]
                  else "PASS(洁净)" if res["errors"] == 0 else "INCOMPLETE(扫描出错,不可判绿)")
        print(f"[gate5] 树={tree}  可扫件={res['files']}  硬命中={len(res['token_hits'])}  "
              f"软命中(Psatz信息档)={len(res['soft_hits'])}  "
              f"岛豁免(构造性岛上下文信息档)={len(res['island_exempt'])}  "
              f"digest命中={len(res['digest_hits'])}  "
              f"出错={res['errors']}  判定={status}  扫描时点={now}")
        for h in res["token_hits"]:
            print(f"  HIT {tree}{os.sep}{h['file']}  token={h['token']}"
                  + (f"  err={h['err']}" if h["err"] else ""))
        for h in res["digest_hits"]:
            print(f"  DIGEST-HIT {tree}{os.sep}{h['file']}  md5={h['digest']}"
                  f"  册名={h['blacklist_name']}"
                  + ("  [改名投毒:name_mismatch]" if h["name_mismatch"] else ""))
        for h in res["island_exempt"]:
            print(f"  exempt-island {tree}{os.sep}{h['file']}  token={h['token']}"
                  f"  island={h['island']}（构造性岛上下文→信息档非硬命中）")
        for h in res["soft_hits"]:
            print(f"  soft {tree}{os.sep}{h['file']}  token={h['token']}（信息档非硬命中）")
        if res["token_hits"] or res["digest_hits"]:
            exit_code = max(exit_code, 1)
        if res["errors"]:
            fatal = fatal or "incomplete-surface"

    total_hit = report["total_token_hits"] + report["total_digest_hits"]
    if exit_code == 0 and report["total_files"] == 0:
        print("[gate5] FATAL: 无可扫面（0 件 .vo/.vos/.vok）——不可判绿", file=sys.stderr)
        fatal = fatal or "no-scannable-surface"
    if fatal:
        exit_code = 2 if exit_code == 0 else exit_code
    if args.jsonout:
        with open(args.jsonout, "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=1)
    if exit_code == 0:
        print(f"[gate5] GATE5-VERDICT: CLEAN exit 0（扫 {report['total_files']} 件＋"
              f"硬 token 0 命中＋digest 0 命中＋对照 SELF-HIT 过；"
              f"Psatz 信息档 {report['total_soft_hits']} 件＋构造性岛上下文豁免 "
              f"{report['exempted_island']} 件已记录）")
    elif exit_code == 1:
        print(f"[gate5] GATE5-VERDICT: HIT exit 1（硬命中 {total_hit} 处——检疫咬合，"
              "处置循 VO-RES-CLEAN 纪律：删毒代＋净源重编消费者闭包＋Axioms=<none> 复证）")
    else:
        print(f"[gate5] GATE5-VERDICT: {str(fatal).upper()} exit 2（不可判绿，fail-loud）")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
