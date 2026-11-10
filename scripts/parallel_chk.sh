#!/bin/bash
# 20261029: resolve the script dir ONCE at top (pre-cd) with a Windows-Python
# friendly mixed path (cygpath -m); line-52's cd $VO_DIR breaks any later
# relative $0 resolution (cost_table.json MISSING precedent -> count fallback).
SCRIPT_DIR="$(cd "$(dirname "$0")" 2>/dev/null && { command -v cygpath >/dev/null 2>&1 && cygpath -m "$PWD" || pwd; })"
# parallel_chk_v3.sh — cost-weighted packing + adaptive-K hook (sandbox copy;
# canonical scripts/parallel_chk.sh v2 stays untouched). v3 deltas over v2:
#   1) Cost weighting: packing reads module -> coqchk-seconds from cost_table.json
#      (env CHK_COST_TABLE, default: next to this script). Module missing from the
#      table = median default; table missing/unusable = fail-open weight 1, which
#      degrades CAP/LPT exactly back to the v2 count-based packing. Closure cost =
#      sum of member costs; CAP = ceil(total_cost/K*1.15); items sorted by closure
#      cost descending (LPT) and dropped onto the cost-lightest lane. The closure
#      same-lane invariant line  S = (clmemo[m] - assigned) | {m}  is verbatim v2.
#   2) Adaptive K: if env CHK_HEADROOM_FILE (RAM-guard drop file holding free-RAM
#      headroom in bytes) is set, K = clamp(4, tier, 8) with tier 8 at >=24 GiB,
#      6 at >=8 GiB, else 4; missing/unparseable file = fail-open K=4. Variable
#      unset = v2 behavior (CHK_JOBS, default 3). No workflow yml change needed.
#   3) PCHK-PACK lines now also print per-lane cost_s (the listed-count metric is
#      kept for old-caliber comparison); PCHK-PACK-SUM prints mode, K, total cost,
#      predicted makespan (max lane cost), median default and per-lane costs.
#   4) VO_DIR hook (env CHK_VO_DIR) so this sandbox copy can be pointed at the
#      real vo tree; the default resolves exactly like v2.
# All comments on changed lines are English; every untouched v2 line is byte-identical to the canonical
# v2 script (v2 Chinese comments englishized in place 2026-11-10; command/flag/variable bytes untouched).
# parallel_chk.sh — full-tree kernel certification, balanced-group parallel edition v2 (20261019 set1557 revision)
#
# v1->v2 revision reasons (run#267 Windows coqchk red root cause):
#   R1 Windows python /tmp path fix: same as parallel_build.sh R1 -- the v1 heredoc Python
#      open('/tmp/...') resolves under native Windows python as <drive>:\tmp\... -> FileNotFoundError
#      -> group output 0 bytes -> zero groups -> PCHK-NO-GROUPS exit 2 (run#267 evidence: the on-disk
#      /tmp/_pchk_groups.txt at 0 bytes + the CI log PCHK-NO-GROUPS, double proof). v2 routes all Python
#      data through cwd-relative paths (_pchk_tmp/).
#   R2 packing algorithm redesigned: v1 packed by dependency top-root closure -- "large-closure roots
#      exclusive, the rest orphaned into a single group". Replaying measured data (run#267 in-flight
#      _pchk_deps.txt, 841 modules / 406 roots) gave group shape 811/23/22: 96% of the tree in one group =
#      parallelism in name only, and 811 modules in a single argv hit the Windows CreateProcess 32K argument wall.
#      v2: all modules by closure size descending + budget-capped greedy (CAP=ceil(1.15*N/K)): measured shape 281/280/280, closure union 393/452/412, argv~5K.
#   R3 semantic red lines mechanized: union-coverage assertion (each module listed exactly once across groups,
#      union == full module set, violator exit 2); order.txt registration-surface coverage assertion (certification
#      surface superset of the registration surface, missing module exit 2); degenerate guard (NMOD>200 with <2 groups = degenerate single pass, exit 2).
#
# Certification semantics (red line): each module is listed by exactly one group's rocqchk call (exactly once);
# in-group kernels verify along the transitive closure of the whole chain; a shared base re-verified across groups =
# stronger guarantee, not a gap; the three group logs merge in group order into _chk_all.log (each lane keeps its own Chicken 9.1.0 banner, per-module Axioms sections preserved, zero-change compatible with the gate2 block state machine).
#
# fail-loud: any lane nonzero, or the merged log missing "Modules were successfully checked" -> exit 1.
# Thermal control: group count = parallelism (CHK_JOBS); the whole step is wrapped by cpu_guard at the yml layer (staggered when load exceeds threshold).
# Environment variables: COQCHK / CHK_JOBS (parallelism) / CHK_ROCQDEP / PYTHON / PCHK_PACK_ONLY=1
# (print the group shapes and exit -- packing-only debug flag).
set -u
# v3: VO_DIR hook — this sandbox copy lives outside ConstructiveWorld-Main/scripts,
# so the vo tree can be given explicitly; when unset the default path resolves
# exactly like v2 (script's parent dir + /ConstructiveWorld_vo).
VO_DIR="${CHK_VO_DIR:-$(dirname "$0")/../ConstructiveWorld_vo}"
cd "$VO_DIR" || { echo "PCHK-PWD-FAIL"; exit 2; }
K="${COQCHK:-C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe}"
JOBS="${CHK_JOBS:-3}"
# --- BEGIN pchk_pick_k (v3 adaptive-K hook; extracted verbatim by the dry-run self-test) ---
# CHK_HEADROOM_FILE: drop file of the RAM guard holding free-RAM headroom in bytes
# (first content must be a plain decimal integer; whitespace/CR/LF tolerated; the
# report-only RAM guard in coq.yml does not drop a file yet, so the parser defines
# the drop-file convention). Tier table chosen here (no repo convention exists):
#   headroom >= 24 GiB -> 8 | >= 8 GiB -> 6 | else 4, then clamp(4, K, 8).
# Missing/unparseable file -> fail-open K=4. Variable unset -> v2 behavior.
pchk_pick_k() {
  local f="$1" raw gib tier
  [ -n "$f" ] || { echo 4; return 0; }
  [ -f "$f" ] || { echo 4; return 0; }                 # missing file -> fail-open
  raw=$(tr -d ' \t\r\n' < "$f" | head -c 32)
  case "$raw" in ''|*[!0-9]*) echo 4; return 0 ;; esac # unparseable -> fail-open
  [ "${#raw}" -le 12 ] || { echo 4; return 0; }        # absurd magnitude -> fail-open
  gib=$(( raw / 1073741824 ))
  if [ "$gib" -ge 24 ]; then tier=8
  elif [ "$gib" -ge 8 ]; then tier=6
  else tier=4
  fi
  [ "$tier" -lt 4 ] && tier=4                          # clamp(4, tier, 8)
  [ "$tier" -gt 8 ] && tier=8
  echo "$tier"
  return 0
}
# --- END pchk_pick_k ---
if [ -n "${CHK_HEADROOM_FILE:-}" ]; then
  HK=$(pchk_pick_k "$CHK_HEADROOM_FILE")
  echo "PCHK-HEADROOM: file=${CHK_HEADROOM_FILE} -> K=${HK} (adaptive hook; CHK_JOBS/default was ${JOBS})" >&2
  JOBS="$HK"
fi
# v3: cost table (module -> coqchk seconds) consumed by the packing python below.
# Default sits next to this script; override with CHK_COST_TABLE. A missing or
# unusable table is not fatal: the packer falls back to weight 1 (= v2 count
# packing) with a loud PCHK-COST-TABLE-* line on stderr.
COST_TABLE="${CHK_COST_TABLE:-$SCRIPT_DIR/cost_table.json}"
export CHK_COST_TABLE="$COST_TABLE"
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || { PY=python; command -v "$PY" >/dev/null 2>&1 || PY=py; }
command -v "$PY" >/dev/null 2>&1 || { echo "PCHK-NO-PYTHON: python3/python/py 全缺席"; exit 2; }

# COQLIB/ROCQLIB same-source export (E-STAGING-SW2 doctrine: bin/lib must share one source)
case "$K" in
  */bin/coqchk.exe) COQLIB="${K%/coqchk.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqchk)     COQLIB="${K%/coqchk}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$K" in
  *coqchk.exe) ROCQDEP="${K%coqchk.exe}rocq.exe" ;;
  *coqchk)     ROCQDEP="${K%coqchk}rocq" ;;
esac
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

WORK="$PWD/_pchk_tmp_$$"   # per-instance unique + absolutized (once a lane cds into a copy, relative WORK mismatches -- att-chain evidence)
rm -rf "$WORK"; mkdir -p "$WORK"

echo "::group::PCHK 1/4 module list + coverage assertion"
# step 1: certification-surface list (`_`-prefixed probe/transient .vo are excluded from the closure -- CI#46 lesson)
# 20261108 admit-restoration companion (#11 PCHK-NO-LANES precedent): the certification surface absorbs the Local/ stem --
#   unified with attest_reconcile's cert_surface (tree root + Local/). In the full-tree era Local modules rode the
#   dependency closure unharmed; in the admit era the top level hit everything -> riders became orphans -> to-verify
#   set = 0 -> the zero-lane guard rejected the run (honest red). After absorption the admit furnace always gets one
#   real Local-closure lane check (1020 admit + 1 checked); full-tree furnace headline 1020->1021 (stronger semantics, not a downgrade: Local moves from closure-riding to explicitly listed).
: > "$WORK/mods.txt"
for f in *.vo; do
  [ -e "$f" ] || continue
  case "$f" in _*) continue ;; esac
  printf '%s\n' "${f%.vo}" >> "$WORK/mods.txt"
done
for f in Local/*.vo; do
  [ -e "$f" ] || continue
  case "$f" in Local/_*) continue ;; esac
  printf '%s\n' "${f%.vo}" >> "$WORK/mods.txt"
done
NMOD=$(wc -l < "$WORK/mods.txt")
[ "$NMOD" -gt 0 ] || { echo "PCHK-NO-MODS"; exit 2; }

# step 1b: certification-inheritance skip list (ATT-RECON 20261029; active when CHK_SKIP_FILE is a non-empty file):
#   the list = files matched by the reconcile step, which compares the cw.attest/v1 archive per-file sha256
#   against the current tree (unchanged, top level only). Semantics: the file's bytes equal what the last fully
#   green coqchk run verified -> certification inherited by hash; this round omits it (deviation-must-check is
#   guarded by the reconcile step: hash-mismatched files stay off the list and are sent as usual). Unknown-item guard:
#   a list naming modules outside mods.txt = config error, fail-loud exit 2 (no silent swallow). Default (unset CHK_SKIP_FILE or empty file) = v2 behavior byte-identical (everything sent).
SKIP_N=0
if [ -n "${CHK_SKIP_FILE:-}" ] && [ -s "$CHK_SKIP_FILE" ]; then
  comm -23 <(sort -u "$CHK_SKIP_FILE") <(sort -u "$WORK/mods.txt") > "$WORK/skip_unknown.txt"
  if [ -s "$WORK/skip_unknown.txt" ]; then
    echo "PCHK-SKIP-UNKNOWN: 跳过清单含认证面外模块: $(tr '\n' ' ' < "$WORK/skip_unknown.txt" | cut -c1-200)——fail-loud"
    exit 2
  fi
  grep -vxFf "$CHK_SKIP_FILE" "$WORK/mods.txt" > "$WORK/mods_kept.txt"
  SKIP_N=$(grep -c . "$CHK_SKIP_FILE")
  mv "$WORK/mods_kept.txt" "$WORK/mods.txt"
  echo "PCHK-ATTEST-SKIP: inherited=$SKIP_N sent_to_chk=$((NMOD-SKIP_N)) total=$NMOD"
  NMOD=$((NMOD-SKIP_N))
fi

# step 1a: registration-surface coverage assertion (no-missed-module gate: every .v registered in order.txt must have a .vo and enter the certification surface)
# Subdir registration lines (Local/*, order L478 R160 precedent): the build face self-builds and self-manages them
#   (build.sh walks each file); since 20261108 the Local/ stem is absorbed into the certification-surface list
#   (step 1 above, unified with reconcile cert_surface) -- the membership assertion still skips Local lines per the
#   top-level historical semantics (the */* continue below); coverage is guaranteed by mods.txt absorption + the unknown-item guard.
covfail=0
while IFS= read -r line; do
  f=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '\r' | tr -d ' ')
  case "$f" in *.v) ;; *) continue ;; esac
  case "$f" in */*) continue ;; esac
  m="${f%.v}"
  if [ ! -f "${m}.vo" ]; then echo "PCHK-COV-NO-VO: 注册面 $f 无 .vo（先修 build）"; covfail=1; continue; fi
  if [ -n "${CHK_SKIP_FILE:-}" ] && [ -f "$CHK_SKIP_FILE" ] && grep -qxF "$m" "$CHK_SKIP_FILE"; then continue; fi  # ATT-RECON: an inherited hit counts as covered (the on-disk .vo assertion on the line above still runs)
  grep -qxF "$m" "$WORK/mods.txt" || { echo "PCHK-COV-EXCLUDED: 注册面 $m 未入认证面"; covfail=1; }
done < order.txt
[ "$covfail" -eq 0 ] || { echo "PCHK-COVERAGE-FAIL: 注册面覆盖断言红——fail-loud"; exit 2; }

echo "::endgroup::"
echo "::group::PCHK 2/4 dependency graph + balanced packing"
# step 2: dependency graph -> balanced grouping
"$ROCQDEP" dep -Q . "" $(ls *.v 2>/dev/null | grep -v '^_'; ls Local/*.v 2>/dev/null | grep -v '/_') > "$WORK/deps.txt" 2>/dev/null || true
[ -s "$WORK/deps.txt" ] || echo "PCHK-WARN-EMPTYDEP: rocq dep 零输出（闭包退化=每组仅列模块——fail-loud 留痕）"
# 20261108 admit-scoping preparation (withdrawn): the scoped-admit mechanism was retired by the dry-run stand ruling --
#   real closure check at 152s/lane (50k checking lines on the bytecode machine), strongest semantics, no gain from admit inheritance (see note 3c-2).
CHK_JOBS="$JOBS" "$PY" - "$WORK/mods.txt" "$WORK/deps.txt" > "$WORK/groups.txt" <<'PYEOF'
import sys, os, math, json, statistics
from collections import defaultdict
mods_f, deps_f = sys.argv[1], sys.argv[2]
allm = [l.strip() for l in open(mods_f, encoding='utf-8', errors='replace') if l.strip()]
allset = set(allm)
deps = defaultdict(set)
for line in open(deps_f, encoding='utf-8', errors='replace'):
    if ':' not in line:
        continue
    left, right = line.split(':', 1)
    vt = [t for t in left.split() if t.endswith('.vo')]
    if not vt:
        continue
    src = vt[0].replace('\\', '/')
    if src.endswith('.vo'):
        src = src[:-3]
    if src not in allset:
        continue
    for t in right.split():
        if t.endswith('.vo') and not t.startswith('/'):
            d = t.replace('\\', '/').split('/')[-1][:-3]
            if d != src and d in allset:
                deps[src].add(d)
def closure(m):
    seen = set(); st = [m]
    while st:
        x = st.pop()
        if x in seen:
            continue
        seen.add(x)
        st.extend(deps.get(x, ()))
    return seen
clmemo = {m: closure(m) for m in allm}
N = len(allm)
K = max(1, int(os.environ.get('CHK_JOBS', '3')))
# v3: the adaptive-K hook (see pchk_pick_k in the bash side) tiers CHK_JOBS
# before this process starts, so the python K line stays verbatim v2.
if N > 200 and K < 2:
    sys.stderr.write('PCHK-DEGENERATE: NMOD=%d 但 CHK_JOBS=%d（退化单遍禁）\n' % (N, K))
    sys.exit(2)
# --- v3 cost weighting -----------------------------------------------
# Cost table: {"modules": {module: coqchk seconds}, ...} as produced by
# mine_cost_table.py. A module missing from the table defaults to the median
# (the table's own recorded median_all_valid_s when present, else the median of
# the table values). A missing/unusable TABLE is fail-open: every weight = 1,
# which degrades CAP/LPT exactly to the v2 count-based packing.
COST_TABLE_PATH = os.environ.get('CHK_COST_TABLE', '')
cost = {}
MED = 1
cost_mode = 'count-fallback(weight=1)'
if COST_TABLE_PATH and os.path.isfile(COST_TABLE_PATH):
    try:
        with open(COST_TABLE_PATH, encoding='utf-8') as fh:
            _doc = json.load(fh)
        _tbl = {m: int(s) for m, s in (_doc.get('modules') or {}).items()
                if isinstance(s, (int, float)) and s > 0}
        if _tbl:
            cost = _tbl
            _med = (_doc.get('sources') or {}).get('src2_mtime_diff', {}).get('median_all_valid_s')
            if isinstance(_med, (int, float)) and _med > 0:
                MED = int(round(_med))
            else:
                MED = int(round(statistics.median(_tbl.values())))
            cost_mode = 'cost-table(seconds)'
        else:
            sys.stderr.write('PCHK-COST-TABLE-EMPTY: no usable entries in %s -> count fallback (weight=1)\n'
                             % COST_TABLE_PATH)
    except Exception as exc:
        sys.stderr.write('PCHK-COST-TABLE-BROKEN: %s (%s) -> count fallback (weight=1)\n'
                         % (COST_TABLE_PATH, exc))
else:
    sys.stderr.write('PCHK-COST-TABLE-MISSING: %s -> count fallback (weight=1)\n' % COST_TABLE_PATH)
def mcost(m):
    return cost.get(m, MED)
TOTAL = sum(mcost(m) for m in allm)
# v3: capacity moves from module count to cost seconds (v2: CAP = ceil(N/K*1.15)).
CAP = math.ceil(TOTAL / K * 1.15)
# v3: LPT ordering moves from closure size to closure cost (ties break by module
# name, same tuple shape as v2).
ccost = {m: sum(mcost(x) for x in clmemo[m]) for m in allm}
items = sorted(((ccost[m], m) for m in allm), reverse=True)
loads = [0] * K
groups = [[] for _ in range(K)]
assigned = set()
PACK_MODE = os.environ.get('CHK_PACK_MODE', 'closure')
for sz, m in items:
    if m in assigned:
        continue
    if PACK_MODE == 'own':
        S = {m}
        scost = mcost(m)
    else:
        S = (clmemo[m] - assigned) | {m}
        scost = sum(mcost(x) for x in S)  # v3: closure cost = sum of member costs
    best = -1; bestload = None
    for i in range(K):
        nl = loads[i] + scost
        if nl <= CAP and (bestload is None or nl < bestload):
            best = i; bestload = nl
    if best < 0:
        best = min(range(K), key=lambda i: loads[i])
    groups[best].extend(sorted(S))
    loads[best] += scost
    assigned.update(S)
for m in sorted(allset - assigned):
    i = min(range(K), key=lambda i: loads[i])
    groups[i].append(m)
    loads[i] += mcost(m)  # v3: cost, not count
    assigned.add(m)
if assigned != allset:
    sys.stderr.write('PCHK-UNION-BROKEN: 并集覆盖断言红 assigned=%d allset=%d\n' % (len(assigned), len(allset)))
    sys.exit(2)
if sum(loads) != TOTAL:
    sys.stderr.write('PCHK-COST-SUM-BROKEN: lane costs %d != total %d\n' % (sum(loads), TOTAL))
    sys.exit(2)
for gi, g in enumerate(groups):
    uni = set()
    for m in g:
        uni |= clmemo[m]
    gcost = sum(mcost(m) for m in g)
    # v3: cost_s added (new caliber); listed = module count (old caliber, kept).
    sys.stderr.write('PCHK-PACK: group=%d listed=%d closure_union=%d cost_s=%d argv_chars=%d\n'
                     % (gi + 1, len(g), len(uni), gcost, sum(len(m) + 1 for m in g)))
# v3: summary line — makespan = max lane cost (predicted packing horizon).
sys.stderr.write('PCHK-PACK-SUM: mode=%s K=%d total_cost_s=%d makespan_cost_s=%d median_default_s=%d lane_costs=%s\n'
                 % (cost_mode, K, TOTAL, max(loads), MED, ','.join(str(x) for x in loads)))
sys.stdout.reconfigure(newline='\n')  # 20261019 CRLF verdict: forbid Windows text mode from writing group lines as \r\n (fixed at the producer side)
for g in groups:
    print('\x1f'.join(sorted(g)))
PYEOF
[ $? -eq 0 ] || { echo "PCHK-PACK-FAIL: 装箱断言红（见上方 stderr 诊断）——fail-loud"; exit 2; }
[ -s "$WORK/groups.txt" ] || { echo "PCHK-NO-GROUPS: 分组输出 0 字节（python 崩或空输入）——fail-loud"; exit 2; }

echo "::endgroup::"
echo "::group::PCHK 3/4 per-lane vo copies + scan-drain"
# step 3: K-lane parallelism (group count = parallelism)
# step 3a: Windows concurrent shared-load defect countermeasure (20261019 att1-3 triple evidence: 4 concurrent coqchk
#   on one tree all died -- two mmap shared-load race shapes: CI face Cannot find library (file on disk, magic correct,
#   single shot reproduces CLEAN) / local face silent rc1 mid-intern; sequential single-shot and whole-group single-shot
#   both CLEAN, mac POSIX same version unharmed). With CHK_TREE_COPY=1 each lane first copies a private vo copy then verifies (sharing broken, parallelism kept; copy dir _pchk_tmp/vo_gN inside the underscore-guarded zone).
LANE_ARR=()
if [ "${CHK_TREE_COPY:-0}" = "1" ]; then
  echo "PCHK: materializing per-lane vo copies (Windows concurrent-mmap defect countermeasure)"
  for c in $(seq 0 $((JOBS-1))); do
    rm -rf "$WORK/vo_g$c"; mkdir -p "$WORK/vo_g$c"
    cp ./*.vo "$WORK/vo_g$c"/ 2>/dev/null || true
    if [ -d Local ]; then mkdir -p "$WORK/vo_g$c/Local"; cp Local/*.vo "$WORK/vo_g$c/Local"/ 2>/dev/null || true; fi
    LANE_ARR+=("$WORK/vo_g$c")
  done
fi
# step 3c: scan-drain flow (20261019 unified verdict: all concurrent failures = coqchk opening a just-written .vo
#   colliding with the Defender exclusive scan window -- build-later 23 fresh / copies 1700 fresh, both sources same
#   disease; sequential single-shot always passed = the window had passed). Before launch, read-open every pending file until clean (Defender caches scan verdicts per file+version; reading them through drains the queue).
if [ "${CHK_TREE_COPY:-0}" = "1" ] && [ -n "${LANE_ARR[*]:-}" ]; then
  for pass in 1 2 3 4; do
    miss=0
    for d in "${LANE_ARR[@]}"; do
      while IFS= read -r f; do
        head -c 16 "$f" >/dev/null 2>&1 || { miss=$((miss+1)); sleep 1; }
      done < <(find "$d" -name '*.vo' 2>/dev/null)
    done
    echo "PCHK scan-drain pass=$pass pending=$miss"
    [ "$miss" -eq 0 ] && break
  done
fi
echo "::endgroup::"
echo "::group::PCHK 4/4 K-lane certification"
# step 3c-2 delta-furnace semantics (20261108 verdict; triple dry-run-stand precedent): the skip list is no longer
#   translated into -admit -- the to-verify set (reconcile sent_to_chk = changed files + Local guardian files) is really
#   checked over the full closure by the lanes (bytecode-machine symmetry: LW0 full closure measured 152s / 50k
#   checking lines). History: global -admit of 1020 in one lane = silent rc=129 death (Stdlib kernel mid-recalc after
#   intern all done; resource death, same signature as #329-331 -- the old "stale-account mismatch" diagnosis was
#   overturned by the dry-run stand); closure-scoped admit was still rejected after the fix (152s real check gives
#   admit no gain; dismantled). Empty skip list (20-furnace backstop sweep, run%20==0) = full re-verify (v2 behavior byte-identical).
#   Appendix verbatim (section 4b): ATTEST-SKIP = reconcile hit surface = the log-side master record of "not listed in this furnace" -- files really checked inside the closure are a superset strengthening, compatible with the appendix's minimal-guarantee semantics (stronger rather than weaker).
echo "PCHK-ADMIT: retired (delta lanes run real closure checks; skip list defines the check set only)"
# step 3c-3 vm_compute certificate bytecode-machine symmetry (20261103, E-COQCHK-BYTECODE-FLAG): default no = purely
#   structural reduction recomputing the bignum certificate = hours of grinding (K12_lo >= 5h); yes = the same path
#   coqc used to produce it (measured >=30x). The bytecode machine is part of the trusted kernel; symmetry does not lower verification strength; -o Axioms output unaffected.
PCHK_BC_ARGS="-bytecode-compiler yes"
i=0
LANE_PIDS=()
while IFS= read -r grp; do
  [ -n "$grp" ] || continue
  # 20261019 CRLF verdict: a trailing \r of a groups.txt line sticks to the last module name -> coqchk Cannot find library(name\r)
  #   (Windows Python text mode writes \n as \r\n; mac POSIX has no such translation, hence the same version unharmed; the
  #   CI att1-3 triple red always hitting each lane's last argument is the hard proof) -- here \037 and \r are both translated to spaces, consumer-side fallback.
  mods=$(printf '%s' "$grp" | tr '\037\r' '  ' | tr '/' '.')
  nm=$(printf '%s' "$mods" | wc -w | tr -d ' ')
  echo "PCHK group $((i+1)): $nm modules (real closure check)"
  if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then i=$((i+1)); continue; fi
  ldir="${LANE_ARR[$i]:-}"
  # 20261019 three-piece concurrent-failure countermeasure: staggered start (45s/lane -- channel-setup windows offset)
  #   + per-instance user isolation (USER/USERNAME into the lane env -- channel names may contain the user domain)
  #   + independent copies (CHK_TREE_COPY). Measured combination: four lanes coexist and progress throughout (the old die-in-seconds window no longer reproduces).
  if [ -n "$ldir" ] && [ -d "$ldir" ]; then
    ( sleep $((i*45)); export USER="lane$$-$i" USERNAME="lane$$-$i"; cd "$ldir" && "$K" -o $PCHK_BC_ARGS -Q . "" $mods > "$WORK/g$i.log" 2>&1; echo $? > "$WORK/g$i.rc" ) &
  else
    ( sleep $((i*45)); export USER="lane$$-$i" USERNAME="lane$$-$i"; "$K" -o $PCHK_BC_ARGS -Q . "" $mods > "$WORK/g$i.log" 2>&1; echo $? > "$WORK/g$i.rc" ) &
  fi
  # 20261019 deadlock fix: collect lane PIDs explicitly -- a bare wait would also wait forever on the monitor subshell (infinite loop) =
  #   the coqchk step hanging permanently (stub measurement: at t=338s the heartbeat kept going and wait never returned). Same for the step 3d retry section below.
  LANE_PIDS+=($!)
  i=$((i+1))
done < "$WORK/groups.txt"
echo "::endgroup::"
NGRP=$i
[ "$NGRP" -gt 0 ] || { echo "PCHK-NO-LANES: 零可用组——fail-loud"; exit 2; }
if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then echo "PCHK_PACK_ONLY: $NGRP groups packed — dry exit 0"; exit 0; fi

# step 3b: liveness dashboard (20261019 countermeasure to the diagnosed fake hang; user directive "make every stage explicit"):
#   during lane silence, print one heartbeat line to the console every PCHK_MON_SEC (default 30)s -- elapsed /
#   per-lane checking-line counts + last module / rc harvest count; lane completion announces a milestone immediately.
#   Console only, never into lane logs or the merged log (zero gate2 pollution). mac bash 3.2 compatible (pure POSIX). A hang/crash moment can be pinned to 30s from the heartbeat cutoff.
echo "[PCHK-MON] $NGRP lanes launched — heartbeat every ${PCHK_MON_SEC:-30}s (console only; lane logs = WORK/g*.log)"
MON_T0=$(date +%s); MON_PREV=0
(
  while :; do
    sleep "${PCHK_MON_SEC:-30}"
    el=$(( $(date +%s) - MON_T0 ))
    rcdone=0; line=""
    for k in $(seq 0 $((NGRP-1))); do
      if [ -f "$WORK/g$k.rc" ]; then
        rcdone=$((rcdone+1))
        line="$line g$k=DONE(rc=$(cat "$WORK/g$k.rc"))"
      else
        lc=$(grep -c 'checking' "$WORK/g$k.log" 2>/dev/null)
        lc=${lc:-0}
        lm=$(tail -n 1 "$WORK/g$k.log" 2>/dev/null | sed 's/.*checking cst://;s/^[[:space:]]*//' | cut -c1-42)
        line="$line g$k:${lc}L:${lm}"
      fi
    done
    echo "[PCHK-MON t=${el}s]${line} (done=${rcdone}/${NGRP})"
    if [ "$rcdone" -gt "$MON_PREV" ]; then
      echo "[PCHK-MON] milestone: ${rcdone}/${NGRP} lanes finished at t=${el}s"
      MON_PREV=$rcdone
    fi
  done
) &
MON_PID=$!
wait "${LANE_PIDS[@]}"
kill "$MON_PID" 2>/dev/null || true
wait "$MON_PID" 2>/dev/null || true

# step 3d: single lane retry (scan-window residue / transient self-heal -- real damage stays red, fail-loud unchanged)
retry_done=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
  if [ "$rc" -ne 0 ] && [ "$retry_done" -eq 0 ]; then
    retry_done=1
    echo "PCHK retry: group $((j+1)) rc=$rc — single retry after 60s settle"
    sleep 60
    ldir="${LANE_ARR[$j]:-}"
    mods=$(sed -n "$((j+1))p" "$WORK/groups.txt" | tr '\037\r' '  ' | tr '/' '.')
    if [ -n "$ldir" ] && [ -d "$ldir" ]; then
      ( export USER="lane$$-r$j" USERNAME="lane$$-r$j"; cd "$ldir" && "$K" -o $PCHK_BC_ARGS -Q . "" $mods > "$WORK/g$j.log" 2>&1; echo $? > "$WORK/g$j.rc" ) &
    else
      ( export USER="lane$$-r$j" USERNAME="lane$$-r$j"; "$K" -o $PCHK_BC_ARGS -Q . "" $mods > "$WORK/g$j.log" 2>&1; echo $? > "$WORK/g$j.rc" ) &
    fi
  fi
done
wait "${LANE_PIDS[@]}"

# step 4: merge logs in group order (gate2 compatible) + fail-loud final verdict
: > _chk_all.log
rc_total=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
  if [ "$rc" -eq 0 ]; then
    rc_total=$rc_total
  else
    rc_total=1
    # lane failure goes straight into the run summary note (20261019 fake-hang countermeasure: failures visible without opening logs)
    echo "::error::PCHK lane g$j FAILED (rc=$rc) — last module: $(tail -n 1 "$WORK/g$j.log" 2>/dev/null | sed 's/.*checking cst://;s/^[[:space:]]*//' | cut -c1-60)"
  fi
  cat "$WORK/g$j.log" >> _chk_all.log 2>/dev/null || rc_total=1
done
grep -q "Modules were successfully checked" _chk_all.log || rc_total=1

# step 4b: certification appendix (ATT-RECON 20261029): the skip list lands in the _chk_all.log appendix -- the
#   archive-coverage assertion of gate2's certified-state branch takes this appendix as the log-side master record
#   (reconciled item by item against attest_reconcile.json). Appendix line shapes (ATTEST-SKIP*/=== boundary lines) structurally never enter the Axioms section, by the gate2 block-state-machine scope discipline
#   (sandbox negative-control measurement: verdicts identical before/after appendix injection; real axioms still DIRTY -- the appendix cannot mask poison).
if [ "${SKIP_N:-0}" -gt 0 ] && [ -n "${CHK_SKIP_FILE:-}" ] && [ -f "$CHK_SKIP_FILE" ]; then
  {
    echo ""
    echo "=== ATTEST-SKIP APPENDIX BEGIN (cw.attest/v1) ==="
    echo "ATTEST-SKIP-COUNT $SKIP_N"
    echo "ATTEST-ARCHIVE ${CHK_ATTEST_SHA256:-none}"
    while IFS= read -r m; do [ -n "$m" ] && echo "ATTEST-SKIP $m"; done < "$CHK_SKIP_FILE"
    echo "=== ATTEST-SKIP APPENDIX END ==="
  } >> _chk_all.log
fi
tail -5 _chk_all.log
# step 4a: Step Summary final table (the run summary page reads each lane's status directly -- explicit-stage closure)
if [ -n "${GITHUB_STEP_SUMMARY:-}" ] && [ -w "$GITHUB_STEP_SUMMARY" ]; then
  {
    echo "### coqchk certification (parallel K=$NGRP, $NMOD modules listed)"
    echo ""
    echo "| lane | status | checking lines |"
    echo "|---|---|---|"
    for j in $(seq 0 $((NGRP-1))); do
      rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
      lc=$(grep -c 'checking' "$WORK/g$j.log" 2>/dev/null); lc=${lc:-0}
      if [ "$rc" -eq 0 ]; then st="PASS"; else st="FAIL(rc=$rc)"; fi
      echo "| g$j | $st | $lc |"
    done
  } >> "$GITHUB_STEP_SUMMARY"
fi
if [ "$rc_total" -eq 0 ]; then
  echo "COQCHK_ALL_PASS (parallel, $NGRP groups, $NMOD modules)"
  exit 0
fi
echo "COQCHK_FAIL (parallel; merged=_chk_all.log, per-group=$WORK/g*.log)"
exit 1
