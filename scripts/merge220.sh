#!/bin/bash
# ============================================================================
# merge220.sh — deterministic generator for releases/CW_ConstructiveWorld_220.v (2026-09-10)
# ============================================================================
# Incident background: CI #27 (af82fa6) reported `Error: positive_dist already exists` (L115662).
# The old merge track was flat hand-concatenation across rounds (base 219 + each new library verbatim); a new library redefining an existing base name blew up the build.
# Remedy (user ruling 20260910): source-level renaming -- the new-library side (attn Up*/CW220_Extensions.v)
# completed 150 source-level renames per scripts/rename-ledger-20260910.md; this generator flat-concatenates
# to regenerate the merge track deterministically, with a built-in [name-collision gate]: per-name comparison against names defined by preceding modules and the base;
# on collision it FAILs immediately, printing name and file -- turning this incident into a permanent gate.
#
# Inputs:
#   base    = ConstructiveWorld_vo/CW_ConstructiveWorld_219.v (registered canonical name in the repo, read-only)
#   modules = first 34 entries of scripts/order.txt (the established "220 merge zone: 34 modules" scope);
#           module sources currently come from the attn workspace (post-rename versions; after the
#           main-session bundle lands, if ConstructiveWorld_vo has synced the same-name versions, switch MOD_SRC=repo and rerun -- output unchanged).
#   exclude = CW214KL_scan.v / AttnHardLimit218.v (read-only shim files whose content the base already inlines;
#           the merge track does not inline them; the flat .vo library consumes them legitimately via Import shadowing).
# Transform: base verbatim on top; then each module has its non-Stdlib Require lines stripped (in-project
#       dependencies are already satisfied by the base/preceding blocks -- measured: external names are 100% supplied by the base); all other bytes verbatim.
# Idempotent: the header "generation time" takes the newest input mtime (deterministic); same input -> byte-identical output.
# Output: releases/CW_ConstructiveWorld_220.v (the previous file is auto-backed up as .bak before the first run)
# ============================================================================
set -u
REPO="D:/ComplexAnalysis/ConstructiveWorld-Main"
ATTN="D:/ComplexAnalysis/新算法实践/attn"
BASE="$REPO/ConstructiveWorld_vo/CW_ConstructiveWorld_219.v"
ORDER="$REPO/scripts/order.txt"
OUT="$REPO/releases/CW_ConstructiveWorld_220.v"
MOD_SRC="${MOD_SRC:-attn}"    # attn|repo
NMERGE=34                     # merge-zone module count (fixed 34 by v4)

[ -f "$BASE" ] || { echo "FAIL: missing base $BASE"; exit 2; }
[ -f "$ORDER" ] || { echo "FAIL: missing $ORDER"; exit 2; }

# Backup of the previous output file (first run only)
if [ -f "$OUT" ] && [ ! -f "$OUT.bak" ]; then
  cp -p "$OUT" "$OUT.bak" && echo "[bak] 旧合并轨已备份 -> CW_ConstructiveWorld_220.v.bak"
fi

python - "$BASE" "$ORDER" "$OUT" "$MOD_SRC" "$ATTN" "$REPO" "$NMERGE" <<'PYEOF'
import sys, os, re, hashlib
from collections import OrderedDict
from datetime import datetime

BASE, ORDER, OUT, MOD_SRC, ATTN, REPO, NMERGE = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6], int(sys.argv[7])
REPO_VO = os.path.join(REPO, "ConstructiveWorld_vo")

HEAD = re.compile(r"^(?:Program\s+)?(Definition|Theorem|Lemma|Corollary|Remark|Fact|Example|Proposition|Instance|Fixpoint|CoFixpoint|Function|Inductive|CoInductive|Class|Record|Structure|Scheme)\b\s*([^:={(*]*?)(?:\s*[:({:=]|$)")
CTOR = re.compile(r"^\|\s*([A-Za-z_][A-Za-z0-9_']*)\s*[:(]")
INLINE = re.compile(r":=\s*([A-Za-z_][A-Za-z0-9_']*)\s*[:({]")
FIELD = re.compile(r"^([A-Za-z_][A-Za-z0-9_']*)\s*:")
REQLINE = re.compile(r"^\s*(?:From\s+[A-Za-z0-9_.']+\s+)?Require\s+Import\s+([A-Za-z0-9_'.]+)")

def sha1(p):
    return hashlib.sha1(open(p, "rb").read()).hexdigest()

def strip_comments(lines):
    out, cdepth, instr = [], 0, False
    for raw in lines:
        line = raw.rstrip("\r\n")
        buf, i, n = [], 0, len(line)
        while i < n:
            c2 = line[i]; two = line[i:i+2]
            if cdepth > 0:
                if two == "(*": cdepth += 1; i += 2
                elif two == "*)": cdepth -= 1; i += 2
                else: i += 1
            elif instr:
                if two == '\\"': i += 2
                elif c2 == '"': instr = False; i += 1
                else: i += 1
            else:
                if two == "(*": cdepth += 1; i += 2
                elif c2 == '"': instr = True; buf.append(" "); i += 1
                else: buf.append(c2); i += 1
        out.append("".join(buf))
    return out

def scan(path, stripped=None):
    """根命名空间定义（Module 隔离 / Section 拍平 / 构造子字段随宿主）"""
    names = OrderedDict()
    pend = None
    stack = []
    if stripped is None:
        with open(path, encoding="utf-8", errors="replace", newline="") as fh:
            raw_lines = fh.readlines()
        stripped = strip_comments(raw_lines)
    in_mod = any(k == "M" for k, _ in stack)
    for ln, s in enumerate(stripped, 1):
        s = s.strip()
        if not s: continue
        ms = re.match(r"^(?:Declare\s+)?Module\s+([A-Za-z0-9_']+)", s)
        if ms:
            stack.append(("M", ms.group(1))); pend = None; continue
        me = re.match(r"^End\s+([A-Za-z0-9_']+)", s)
        if me and stack:
            if stack[-1][1] == me.group(1): stack.pop()
            pend = None; continue
        ss = re.match(r"^Section\s+([A-Za-z0-9_']+)", s)
        if ss:
            stack.append(("S", ss.group(1))); continue
        if any(k == "M" for k, _ in stack): continue
        m = HEAD.match(s)
        if m:
            tok = (m.group(2).strip().split() or [""])[0]
            kw = m.group(1)
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", tok):
                names.setdefault(tok, ln)
            pend = tok if kw in ("Inductive", "CoInductive", "Record", "Structure") else None
            if pend:
                ic = INLINE.search(s)
                if ic: names.setdefault(ic.group(1), ln)
            continue
        if s.startswith("|"):
            c = CTOR.match(s)
            if c and pend: names.setdefault(c.group(1), ln); continue
        if pend in ("Record", "Structure"):
            f2 = FIELD.match(s)
            if f2: names.setdefault(f2.group(1), ln)
        if "}" in s or "=>" in s or s == "." or s.startswith("End"):
            pend = None
    return names

def module_path(f):
    if MOD_SRC == "attn":
        p = os.path.join(ATTN, f)
        if os.path.exists(p): return p
    p2 = os.path.join(REPO_VO, f)
    if os.path.exists(p2): return p2
    return None

order = [l.split('#', 1)[0].strip() for l in open(ORDER, encoding="utf-8") if l.split('#', 1)[0].strip()]
mods = order[:NMERGE]
paths = []
for f in mods:
    p = module_path(f)
    if not p:
        print("GATE-FAIL: 模块缺失 %s（MOD_SRC=%s）" % (f, MOD_SRC)); sys.exit(1)
    paths.append((f, p))

# ---------- name-collision gate (the incident turned into a permanent gate) ----------
dup = OrderedDict()
def seen_before(n, label, ln):
    dup.setdefault(n, []).append((label, ln))
seen_map = OrderedDict()   # name -> first (label, line)
with open(BASE, encoding="utf-8", errors="replace", newline="") as fh:
    base_lines = fh.readlines()
base_stripped = strip_comments(base_lines)
for n, ln in scan(BASE, base_stripped).items():
    seen_map.setdefault(n, ("CW_ConstructiveWorld_219.v", ln))
gate = []
for f, p in paths:
    for n, ln in scan(p).items():
        if n in seen_map:
            gate.append((n, seen_map[n], (f, ln)))
        else:
            seen_map[n] = (f, ln)
if gate:
    print("GATE-FAIL: 撞名 %d 处——合并轨拒绝生成（名字 | 首定义 | 重定义）：" % len(gate))
    for n, first, second in gate:
        print("  %s | %s@L%d | %s@L%d" % (n, first[0], first[1], second[0], second[1]))
    sys.exit(1)
print("GATE-OK: 基座+%d 模块逐名比对零撞名" % NMERGE)

# ---------- concatenation ----------
def strip_local_requires(path):
    """剥除非 Stdlib Require 行（项目内依赖已就地满足）；其余字节原样"""
    with open(path, encoding="utf-8", errors="replace", newline="") as fh:
        lines = fh.readlines()
    kept, dropped = [], 0
    for raw in lines:
        rm = REQLINE.match(raw)
        if rm and re.match(r"^(CW[0-9]|CW_|Up[A-Z])", rm.group(1)):
            dropped += 1
            continue
        kept.append(raw)
    return kept, dropped

mt = max(os.path.getmtime(p) for p in [BASE] + [p for _, p in paths])
gen_time = datetime.fromtimestamp(mt).strftime("%Y-%m-%d %H:%M:%S %z")
hdr = []
hdr.append("(* ============================================================================\n")
hdr.append("    CW_ConstructiveWorld_220.v — 合并轨确定性产物 · merge220.sh 生成\n")
hdr.append("    生成时间·输入最新mtime: %s\n" % gen_time)
hdr.append("    基座: CW_ConstructiveWorld_219.v sha1=%s · %d 行 · 原样置顶\n"
           % (sha1(BASE), len(base_lines)))
hdr.append("    模块清单: order.txt 前 %d 项 · 源=%s · 已剥项目内 Require 行\n" % (NMERGE, MOD_SRC))
for f, p in paths:
    hdr.append("      %-24s sha1=%s\n" % (f, sha1(p)))
hdr.append("    撞名闸门: 基座+%d 模块逐名比对零撞名（本头部使正文行号整体下移）\n" % NMERGE)
hdr.append("    改名依据: scripts/rename-ledger-20260910.md · 源级改名方案 2026-09-10\n")
hdr.append("============================================================================ *)\n")
head_txt = "".join(hdr)
assert "(*" not in head_txt[2:] and "*)" not in head_txt[:-3], "header comment safety"
parts = [head_txt]
parts.extend(base_lines)
total_dropped = 0
for f, p in paths:
    kept, dropped = strip_local_requires(p)
    total_dropped += dropped
    parts.append("(* ==================== 合并模块 %s ==================== *)\n" % f)
    parts.extend(kept)
os.makedirs(os.path.dirname(OUT), exist_ok=True)
with open(OUT, "w", encoding="utf-8", newline="") as fh:
    fh.writelines(parts)
n_out = sum(1 for _ in open(OUT, encoding="utf-8", errors="replace"))
print("OUT=%s" % OUT)
print("OUT_LINES=%d" % n_out)
print("OUT_SHA1=%s" % sha1(OUT))
print("STRIPPED_REQUIRE_LINES=%d" % total_dropped)
PYEOF
rc=$?
[ $rc -ne 0 ] && { echo "merge220: FAILED (rc=$rc)"; exit $rc; }
echo "merge220: OK"
