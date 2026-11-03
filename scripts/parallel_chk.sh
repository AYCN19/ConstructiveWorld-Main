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
# All comments on changed lines are English; every untouched v2 line (including
# its Chinese comments) is byte-identical to the canonical script.
# parallel_chk.sh — 全树内核认证·均衡分组并行版 v2（20261019 set1557 修订）
#
# v1→v2 修订缘由（run#267 Windows coqchk 红根因）：
#   R1 Windows python /tmp 路径修复：同 parallel_build.sh R1——v1 heredoc Python
#      open('/tmp/...') 在 Windows 原生 python 下解析为 <盘>:\tmp\... → FileNotFoundError
#      → 分组输出 0 字节 → 零组 → PCHK-NO-GROUPS exit 2（run#267 实证，盘面
#      /tmp/_pchk_groups.txt 0 字节 + CI 日志 PCHK-NO-GROUPS 双证）。v2 全部 Python
#      数据面走 cwd 相对路径（_pchk_tmp/）。
#   R2 装箱算法重设计：v1 按依赖顶根闭包装箱，「大闭包根独占 + 其余成 orphans 倾入
#      单组」——实采数据重放（run#267 在飞 _pchk_deps.txt，841 模块 406 根）得组形
#      811/23/22：96% 全树挤单组=并行名存实亡 + 811 模块单 argv 逼 Windows CreateProcess
#      32K 参数墙。v2 全模块按闭包规模降序 + 预算封顶贪心（CAP=⌈1.15·N/K⌉）：
#      实测组形 281/280/280·闭包并集 393/452/412·argv≈5K。
#   R3 语义红线机械化：并集覆盖断言（每组模块列表恰一次列出·并集==全模块集·违者
#      exit 2）；order.txt 注册面覆盖断言（认证面 ⊇ 注册面·缺件 exit 2）；退化守卫
#      （NMOD>200 而组数<2 = 退化单遍，exit 2）。
#
# 认证语义（红线）：每模块恰被一组的 rocqchk 调用列出（恰一次）；组内核沿传递闭包
# 整链核验；跨组共享基座被重复核验=更强保障非缺口；三组日志按组序合并为 _chk_all.log
# （每路自带 Chicken 9.1.0 banner·Axioms 段逐模块保全·gate2 块状态机零改动兼容）。
#
# fail-loud：任一路非 0、或合并日志缺 "Modules were successfully checked" → exit 1。
# 温控：组数=并行度（CHK_JOBS）；整体由 yml 层 cpu_guard 包裹（负载>阈值错峰）。
# 环境变量：COQCHK / CHK_JOBS（并行度）/ CHK_ROCQDEP / PYTHON / PCHK_PACK_ONLY=1
# （仅装箱打印组形即退·调试旗标）。
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

# COQLIB/ROCQLIB 同源导出（E-STAGING-SW2 教义：bin/lib 必须同源）
case "$K" in
  */bin/coqchk.exe) COQLIB="${K%/coqchk.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqchk)     COQLIB="${K%/coqchk}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$K" in
  *coqchk.exe) ROCQDEP="${K%coqchk.exe}rocq.exe" ;;
  *coqchk)     ROCQDEP="${K%coqchk}rocq" ;;
esac
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

WORK="$PWD/_pchk_tmp_$$"   # 实例唯一＋绝对化（lane cd 进副本后相对 WORK 即失配——att 链实证）
rm -rf "$WORK"; mkdir -p "$WORK"

echo "::group::PCHK 1/4 module list + coverage assertion"
# ① 认证面清单（`_` 前缀探针/暂态 .vo 不入闭包——CI#46 教训）
: > "$WORK/mods.txt"
for f in *.vo; do
  [ -e "$f" ] || continue
  case "$f" in _*) continue ;; esac
  printf '%s\n' "${f%.vo}" >> "$WORK/mods.txt"
done
NMOD=$(wc -l < "$WORK/mods.txt")
[ "$NMOD" -gt 0 ] || { echo "PCHK-NO-MODS"; exit 2; }

# ①b 认证继承跳过清单（ATT-RECON 20261029·CHK_SKIP_FILE 非空文件时启用）：
# 清单=对账步按档案 cw.attest/v1 逐件 sha256 对照现树的命中件（unchanged，仅顶层）。
# 语义：该件字节与上次 coqchk 全绿运行所验内容全等 → 认证凭哈希继承，本轮免列
# （偏离必检由对账步把守：哈希不匹配者不在清单，照常送检）。
# 未知项守卫：清单含 mods.txt 之外模块 = 配置错，fail-loud exit 2（禁静默吞）。
# 清单缺省（未设 CHK_SKIP_FILE 或空文件）= v2 行为逐字节不变（全量送检）。
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

# ①a 注册面覆盖断言（禁漏件门：order.txt 全注册 .v 须有 .vo 且入认证面）
# 子目录注册行（Local/*，order L478 R160 判例）：build 面自编自管（build.sh 逐件走）·
# 认证面 membership 断言仅约束顶层（历史 coqchk_all 顶层 glob 语义）——Local 件经
# 依赖闭包随组核验，不单列。
covfail=0
while IFS= read -r line; do
  f=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '\r' | tr -d ' ')
  case "$f" in *.v) ;; *) continue ;; esac
  case "$f" in */*) continue ;; esac
  m="${f%.v}"
  if [ ! -f "${m}.vo" ]; then echo "PCHK-COV-NO-VO: 注册面 $f 无 .vo（先修 build）"; covfail=1; continue; fi
  if [ -n "${CHK_SKIP_FILE:-}" ] && [ -f "$CHK_SKIP_FILE" ] && grep -qxF "$m" "$CHK_SKIP_FILE"; then continue; fi  # ATT-RECON: 命中继承件视同已覆盖（.vo 在盘断言上行仍照跑）
  grep -qxF "$m" "$WORK/mods.txt" || { echo "PCHK-COV-EXCLUDED: 注册面 $m 未入认证面"; covfail=1; }
done < order.txt
[ "$covfail" -eq 0 ] || { echo "PCHK-COVERAGE-FAIL: 注册面覆盖断言红——fail-loud"; exit 2; }

echo "::endgroup::"
echo "::group::PCHK 2/4 dependency graph + balanced packing"
# ② 依赖图 → 均衡分组
"$ROCQDEP" dep -Q . "" $(ls *.v 2>/dev/null | grep -v '^_') > "$WORK/deps.txt" 2>/dev/null || true
[ -s "$WORK/deps.txt" ] || echo "PCHK-WARN-EMPTYDEP: rocq dep 零输出（闭包退化=每组仅列模块——fail-loud 留痕）"
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
    src = vt[0].replace('\\', '/').split('/')[-1][:-3]
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
sys.stdout.reconfigure(newline='\n')  # 20261019 CRLF 定谳：禁 Windows 文本模式把组行写成 \r\n（源侧根治）
for g in groups:
    print('\x1f'.join(sorted(g)))
PYEOF
[ $? -eq 0 ] || { echo "PCHK-PACK-FAIL: 装箱断言红（见上方 stderr 诊断）——fail-loud"; exit 2; }
[ -s "$WORK/groups.txt" ] || { echo "PCHK-NO-GROUPS: 分组输出 0 字节（python 崩或空输入）——fail-loud"; exit 2; }

echo "::endgroup::"
echo "::group::PCHK 3/4 per-lane vo copies + scan-drain"
# ③ K 路并行（组数=并行度）
# ③a Windows 并发共载缺陷对策（20261019 att1-3 三连实证：同树 4 并发 coqchk 全灭——
# mmap 共载竞态两型：CI 面 Cannot find library（文件在盘魔数正·单发复现 CLEAN）/本地面
# intern 中静默 rc1；顺序单发/全组单发皆 CLEAN·mac POSIX 侧同版无恙）——CHK_TREE_COPY=1
# 时每 lane 先复制独立 vo 副本再验（断共享·保并行度；副本目录 _pchk_tmp/vo_gN 下划线守卫域）。
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
# ③c 扫描疏引流（20261019 万相归一定谳：全部并发失败=coqchk 开「刚写完的 .vo」撞
# Defender 排他扫描窗——build 后 23 fresh/copies 1700 fresh 两源同病·顺序单发恒过=窗已过）。
# lane 发射前对全部待开文件做读开放直至洁净（Defender 按文件+版本缓存扫描结果·读尽即排空）。
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
# ③c-2 认证继承 admit 接线（20261103·三捷径③收口）：CHK_SKIP_FILE=attest_reconcile
# digest 命中件（该件字节=上次 coqchk 全绿所验内容·cw_attest/v1 建档律）→ -admit 载入不查。
# 跳过清单空（20 炉 backstop 收缴·run%20==0）=零 admit=全量闭包重验（v2 行为逐字节不变）。
# 声明：admit 件正当性=digest 断言非本炉内核重验；档案仅在绿炉后随 commit 前进（先绿后录）。
PCHK_ADMIT_ARGS=""
if [ -n "${CHK_SKIP_FILE:-}" ] && [ -s "$CHK_SKIP_FILE" ]; then
  while IFS= read -r _am; do [ -n "$_am" ] && PCHK_ADMIT_ARGS="$PCHK_ADMIT_ARGS -admit $_am"; done < "$CHK_SKIP_FILE"
  echo "PCHK-ADMIT: $(grep -c . "$CHK_SKIP_FILE") modules admitted (digest=attested, loaded-not-checked)"
else
  echo "PCHK-ADMIT: none (skip list absent/empty — full-closure mode)"
fi
i=0
LANE_PIDS=()
while IFS= read -r grp; do
  [ -n "$grp" ] || continue
  # 20261019 CRLF 定谳：groups.txt 行尾 \r 黏在末位件名上→coqchk Cannot find library(名\r)
  # （Windows Python 文本模式写 \n→\r\n·mac POSIX 无此翻译故同版无恙·CI att1-3 三连红恒为各
  #  lane 末位参即铁证）——此处连同 \037 一并翻译为空格，消费侧兜底。
  mods=$(printf '%s' "$grp" | tr '\037\r' '  ')
  nm=$(printf '%s' "$mods" | wc -w | tr -d ' ')
  echo "PCHK group $((i+1)): $nm modules"
  if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then i=$((i+1)); continue; fi
  ldir="${LANE_ARR[$i]:-}"
  # 20261019 并发失效对策三件：错峰启动（45s/lane——通道建立窗错开）＋实例域用户隔离
  # （USER/USERNAME 进 lane 环境——通道名可能含用户域）＋独立副本（CHK_TREE_COPY）。
  # 实测组合：四 lane 共存全程推进（旧配置秒死窗不复现）。
  if [ -n "$ldir" ] && [ -d "$ldir" ]; then
    ( sleep $((i*45)); export USER="lane$$-$i" USERNAME="lane$$-$i"; cd "$ldir" && "$K" -o -Q . "" $PCHK_ADMIT_ARGS $mods > "$WORK/g$i.log" 2>&1; echo $? > "$WORK/g$i.rc" ) &
  else
    ( sleep $((i*45)); export USER="lane$$-$i" USERNAME="lane$$-$i"; "$K" -o -Q . "" $PCHK_ADMIT_ARGS $mods > "$WORK/g$i.log" 2>&1; echo $? > "$WORK/g$i.rc" ) &
  fi
  # 20261019 死锁修：定向收 lane PID——裸 wait 会把监视器子壳（永循环）一并等死＝
  # coqchk 步永久假死（桩件实测 t=338s 心跳不歇·wait 不归）。下同 ③d 重试段。
  LANE_PIDS+=($!)
  i=$((i+1))
done < "$WORK/groups.txt"
echo "::endgroup::"
NGRP=$i
[ "$NGRP" -gt 0 ] || { echo "PCHK-NO-LANES: 零可用组——fail-loud"; exit 2; }
if [ "${PCHK_PACK_ONLY:-0}" = "1" ]; then echo "PCHK_PACK_ONLY: $NGRP groups packed — dry exit 0"; exit 0; fi

# ③b 活性仪表盘（20261019 假死定谳反制·用户令「环节显式表达」）：lane 静默期每
# PCHK_MON_SEC（默认30）s 向控制台打单行心跳——elapsed／各 lane checking 行数＋末模块／
# rc 收割数；lane 完结即时播报里程碑。只写控制台，不进 lane 日志与合并日志（gate2
# 口径零污染）。mac bash 3.2 兼容（纯 POSIX 形）。宕机/卡死时刻可由心跳断流精确到 30s。
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

# ③d lane 单次重试（扫描窗残余/瞬态自愈——真伤恒红 fail-loud 不变）
retry_done=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
  if [ "$rc" -ne 0 ] && [ "$retry_done" -eq 0 ]; then
    retry_done=1
    echo "PCHK retry: group $((j+1)) rc=$rc — single retry after 60s settle"
    sleep 60
    ldir="${LANE_ARR[$j]:-}"
    mods=$(sed -n "$((j+1))p" "$WORK/groups.txt" | tr '\037\r' '  ')
    if [ -n "$ldir" ] && [ -d "$ldir" ]; then
      ( export USER="lane$$-r$j" USERNAME="lane$$-r$j"; cd "$ldir" && "$K" -o -Q . "" $mods > "$WORK/g$j.log" 2>&1; echo $? > "$WORK/g$j.rc" ) &
    else
      ( export USER="lane$$-r$j" USERNAME="lane$$-r$j"; "$K" -o -Q . "" $mods > "$WORK/g$j.log" 2>&1; echo $? > "$WORK/g$j.rc" ) &
    fi
  fi
done
wait "${LANE_PIDS[@]}"

# ④ 日志按组序合并（gate2 兼容）+ fail-loud 终审
: > _chk_all.log
rc_total=0
for j in $(seq 0 $((NGRP-1))); do
  rc=$(cat "$WORK/g$j.rc" 2>/dev/null || echo 1)
  if [ "$rc" -eq 0 ]; then
    rc_total=$rc_total
  else
    rc_total=1
    # lane 失败直进 run 摘要注记（20261019 假死反制：失败面无需开日志即见）
    echo "::error::PCHK lane g$j FAILED (rc=$rc) — last module: $(tail -n 1 "$WORK/g$j.log" 2>/dev/null | sed 's/.*checking cst://;s/^[[:space:]]*//' | cut -c1-60)"
  fi
  cat "$WORK/g$j.log" >> _chk_all.log 2>/dev/null || rc_total=1
done
grep -q "Modules were successfully checked" _chk_all.log || rc_total=1

# ④b 认证附页（ATT-RECON 20261029）：跳过清单落 _chk_all.log 附页留痕——gate2 认证态
# 分支的档案覆盖断言以本附页为日志侧正本（与 attest_reconcile.json 逐项对账）。
# 附页行形（ATTEST-SKIP*/=== 边界行）经 gate2 块状态机 scope 纪律结构性不入 Axioms 段
# （沙箱负证实测：附页注入前后判定全等；真公理仍 DIRTY——附页不可掩毒）。
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
# ④a Step Summary 终表（run 摘要页直读每 lane 状态——环节显式表达收口）
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
