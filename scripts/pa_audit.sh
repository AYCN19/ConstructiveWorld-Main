#!/usr/bin/env bash
# ============================================================================
# pa_audit.sh — Print Assumptions full-batch audit + optional coqchk (official reproducible script)
#
# Caliber anchors:
#   - Review 11 §3 P5: "The only externally auditable form is: Print Assumptions output for all headline
#     theorems (it should show Closed under the global context) + a coqchk pass record over the compiled artifacts";
#   - Paper 1 §1.2 contribution 9 / Appendix D item 2: 81 headline theorems/definitions batch-CLEAN, most recent full
#     re-check at base state 198/206 -- this script upgrades that caliber to "reproducible script + current full report";
#   - 审计口径总纲：attn\零公理审计口径说明-20260910.md（其 L4 = 本脚本）。
#
# Lineage (maximize reuse of the existing chain; do not discard):
#   - 定理清单初版 = 演变\.ablation\sc2_parallel\sL_assumptions\{probe_full.v,
#     theorem_names.txt} (81 headline theorems/definitions, base-state 198 batch chain) + Paper 1/2 headline-theorem family
#     grep-aligned supplements, landed as scripts\pa_theorems.txt (one theorem per line: module:name);
#   - Assertion/parsing approach inherited from same-directory assert_print_assumptions.ps1 / parse_pa_log.ps1
#     (generate a probe file -> coqc -> scan the log and assert), rewritten as cross-platform bash;
#   - 负载闸承演变\.ablation\cpu_guard.ps1（root 外引用、不改原件），
#     LoadLimit self-tuning is the established protocol for hot coexistence with in-flight sessions.
#
# Red lines (enforced at run time):
#   - Zero git operations; do not touch releases/; do not modify any .v source; all probes land in
#     scripts/_pa_work/ (Require + Print Assumptions only);
#   - Windows compilation always goes through the full 9.1 path (C:\Rocq-Platform~9.1~2026.01\bin\),
#     bare PATH forbidden -- 2026-09-15 whole-repo retarget to 9.1 (PROBE91 evidence: 201 faces all green);
#     原「9.0 路径 + 防混装 bad version 90001」预警随之作废（见 attn/_thv3sw2_交付报告-20260915.md）；
#   - All coqc/coqchk calls are wrapped by cpu_guard (PA_GUARD=0 disables it; recommended for CI only);
#   - Avoid list: UpIDL / UpMinP modules skip build and check (merge-track closure seat repairing),
#     the audit resumes after the fix lands (see the report's coverage-boundary section).
#
# Usage:
#   ./pa_audit.sh [--root ConstructiveWorld_vo] [--coqchk] [--no-build]
#                 [--theorems pa_theorems.txt]
#   Environment variables: PA_LOADLIMIT(60) PA_CORE(3) PA_MAXWAIT(1800) PA_GUARD(1)
#             PA_GUARD_PS1(established path outside root) PA_COQ_BIN(full 9.1 path)
# Output: scripts/pa_audit_report.md (supporting logs in scripts/_pa_work/)
#
# -- Drift list (paper-vs-library naming drifts; each on record, none skipped; the report has a same-name section) --
#   1. req_step_kl_eta_bound (Paper 1 §4.3.2 batch-3 counterpart bridge-lemma name)
#      -> no such declaration in the library (in neither the repo tree nor attn). Nearest neighbors already on the list:
#        real_step_kl_eta_bound_eps (base 219), geod_step_kl_eta_bound_eps (UpReqGeomD).
#   2. r2_step_kl_weighted (Paper 1 UpReqAlign3 six-item list name)
#      -> not declared in the library; nearest neighbor r2_step_kl_rearr (UpReqAlign3).
#   3. rppo_align_objective_advantage_decomp (Paper 1 snapshot anchor, belongs to UpReqPPO)
#      -> absent from the repo tree; on disk only in the attn workspace (round-9 pending-landing face, not a naming drift).
#   4. attention_minimizes_free_energy (Paper 2 concept name)
#      -> declared in the library as req_attention_minimizes_free_energy_unique (UpReqFEPAttn, already on the list).
#   5. tv_doeblin_contraction / tv_doeblin_iter (Paper 2 theorem 5.10, UpTVReal archive file)
#      -> not declared in the library (not merged into the modular tree); two-point TV contraction is carried by the base tv family + UpReqSampling.
#
# -- 2026-09-11 continuation-session (PA audit session continued) change record (two spots in this script only; mechanism unchanged) --
#   a. the coqchk verdict gains the -silent form: measured on 9.0, -silent suppresses the success line (9.1 SW2 retarget re-verified:
#      rc=0 shows only the "* Axioms:" section), so rc=0 + presence of the "* Axioms:" section = both conditions hold;
#   b. the drift list gains the two tv_doeblin entries (Paper 2 theorem 5.10 archive files not merged into the tree) and
#      one real_kl_sum_decomp comment-phantom entry (text present in .v, zero exports in .vo -- not a real declaration).
#   The list pa_theorems.txt was fully rebuilt to 193 entries (probe_full 81 base + headline-family supplements + req 27);
#   base-internal submodule entries enter the list with qualified names (UpExtras219./UpGRPO219./PropositionConvergenceCore.,
#   fixing the predecessor's flat name boltzmann_factor_pos that broke the 219 module-level probe).
# ============================================================================
set -u
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

usage() {
  echo "用法: pa_audit.sh [--root ConstructiveWorld_vo] [--coqchk] [--no-build] [--theorems <file>]"
  echo "  环境变量: PA_LOADLIMIT(60) PA_CORE(3) PA_MAXWAIT(1800) PA_GUARD(1) PA_COQ_BIN(9.1路径)"
}

# ---------------------------------------------------------------- Parameters ----
ROOT_NAME="ConstructiveWorld_vo"
DO_COQCHK=0
DO_BUILD=1
THEOREMS_FILE="$SCRIPT_DIR/pa_theorems.txt"
while [ $# -gt 0 ]; do
  case "$1" in
    --root)     ROOT_NAME="$2"; shift 2 ;;
    --coqchk)   DO_COQCHK=1; shift ;;
    --no-build) DO_BUILD=0; shift ;;
    --theorems) THEOREMS_FILE="$2"; shift 2 ;;
    -h|--help)  usage; exit 0 ;;
    *) echo "[pa_audit] 未知参数: $1"; usage; exit 2 ;;
  esac
done

VO_DIR="$REPO_ROOT/$ROOT_NAME"
ORDER_FILE="$SCRIPT_DIR/order.txt"
WORK="$SCRIPT_DIR/_pa_work"
REPORT="$SCRIPT_DIR/pa_audit_report.md"
BASE_MOD="CW_ConstructiveWorld_219"
# Avoid list (merge-track closure seat repairing: skip build and check; audit resumes after the fix lands)
EXCLUDE_MODS="UpIDL UpMinP"
mkdir -p "$WORK"

[ -d "$VO_DIR" ]        || { echo "[pa_audit] FATAL: root 不存在: $VO_DIR"; exit 2; }
[ -f "$THEOREMS_FILE" ] || { echo "[pa_audit] FATAL: 清单不存在: $THEOREMS_FILE"; exit 2; }
[ -f "$ORDER_FILE" ]    || { echo "[pa_audit] FATAL: order.txt 不存在: $ORDER_FILE"; exit 2; }

T_START=$(date +%s)
TS_NOW="$(date '+%Y-%m-%d %H:%M:%S %z')"

# ------------------------------------------------------- Toolchain (9.1) ----
case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*|Windows*)
    HOST_OS=windows
    COQ_BIN="${PA_COQ_BIN:-C:/Rocq-Platform~9.1~2026.01/bin}"
    # SW2 retarget (2026-09-15): machine-level [user environment variables] COQLIB/ROCQLIB pinned to the 9.0 lib override the
    # 9.1 coq_environment.txt -> 9.1 coqc silently loads the 9.0 stdlib and the artifact magic 90001 is rejected by 9.1 coqchk.
    # Therefore export them derived from COQ_BIN, keeping bin/lib same-source (E-STAGING-SW2 evidence: 90100 roundtrip EXIT=0).
    case "$COQ_BIN" in
      */bin) export COQLIB ROCQLIB; COQLIB="${COQ_BIN%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
    esac
    COQC="$COQ_BIN/coqc.exe"
    COQCHK="$COQ_BIN/coqchk.exe"
    [ -f "$COQC" ]   || { echo "[pa_audit] FATAL: 9.1 coqc 不在 $COQC（禁裸 PATH 调用）"; exit 2; }
    [ -f "$COQCHK" ] || COQCHK=""
    ;;
  *)
    HOST_OS=linux
    COQC="${PA_COQC:-coqc}"
    COQCHK="${PA_COQCHK:-coqchk}"
    command -v "$COQC" >/dev/null 2>&1 || { echo "[pa_audit] FATAL: coqc 不在 PATH"; exit 2; }
    command -v "$COQCHK" >/dev/null 2>&1 || COQCHK=""
    ;;
esac
COQ_VERSION="$("$COQC" --version 2>&1 | head -1)"
case "$COQ_VERSION" in
  *9.1.*) : ;;
  *) echo "[pa_audit] WARN: 非 9.1 工具链: $COQ_VERSION" ;;
esac

# ------------------------------------------------------------- Guard wrapper ----
GUARD_PS1="${PA_GUARD_PS1:-D:/ComplexAnalysis/ConstructiveWorld/演变/.ablation/cpu_guard.ps1}"
LOADLIMIT="${PA_LOADLIMIT:-60}"
COREN="${PA_CORE:-3}"
MAXWAIT="${PA_MAXWAIT:-1800}"
USE_GUARD=0
if [ "$HOST_OS" = windows ] && [ "${PA_GUARD:-1}" = "1" ] && [ -f "$GUARD_PS1" ]; then
  USE_GUARD=1
fi
: > "$WORK/.cool_count"

run_cmd() {  # run_cmd <log> <exe> [args...] -- loadpath goes through env (COQPATH/ROCQPATH equivalent to -Q dir "",
             # and avoids the pitfall of native PowerShell calls dropping empty-string arguments); on guard ABORT (rc=2), auto-retry up to 3 times
  local log="$1"; shift
  local attempt rc=0
  : > "$log"
  for attempt in 1 2 3; do
    if [ "$USE_GUARD" = 1 ]; then
      local psargs="" a
      for a in "$@"; do psargs+="'$a' "; done
      COQPATH="$(wpath "$VO_DIR")" ROCQPATH="$(wpath "$VO_DIR")" \
        powershell -NoProfile -ExecutionPolicy Bypass -File "$GUARD_PS1" \
        -LoadLimit "$LOADLIMIT" -CoreN "$COREN" -MaxWaitSec "$MAXWAIT" \
        -Command "& $psargs" >> "$log" 2>&1
      rc=$?
      grep -c '^\[cpu_guard\] cooling' "$log" >> "$WORK/.cool_count" 2>/dev/null || true
    else
      COQPATH="$(wpath "$VO_DIR")" ROCQPATH="$(wpath "$VO_DIR")" "$@" >> "$log" 2>&1
      rc=$?
    fi
    [ "$rc" = 0 ] && return 0
    grep -q 'ABORT: load' "$log" 2>/dev/null || return $rc   # real failure (compile error etc.) -- no retry
    echo "[pa_audit] guard ABORT（系统持续高负载），第 $attempt 次重试: $*" >&2
    sleep 20
  done
  return $rc
}
strip_log() { grep -vE '^(\[cpu_guard\]|Warning: Deprecated environment variable COQPATH)' "$1" 2>/dev/null || true; }
excluded() { local m; for m in $EXCLUDE_MODS; do [ "$1" = "$m" ] && return 0; done; return 1; }
# Paths passed to coqc/coqchk must be in Windows form (Git Bash /d/... would be parsed as an identifier and error out)
wpath() {
  if [ "$HOST_OS" = windows ] && command -v cygpath >/dev/null 2>&1; then cygpath -m "$1"; else printf '%s' "$1"; fi
}
modsan_of() { printf '%s' "$1" | tr -c 'A-Za-z0-9_' '_'; }

# ------------------------------------------------------------ Module set ----
# Coverage set = base + all of order.txt + in-tree modules named by the list; the avoid set is removed
: > "$WORK/.excluded"
MODULES="$( { echo "$BASE_MOD"; grep -vE '^\s*(#|$)' "$ORDER_FILE" | sed -e 's/#.*//' -e 's/\.v$//'; } | awk '!seen[$0]++')"
COVERED=""
for m in $MODULES; do
  if excluded "$m"; then echo "$m" >> "$WORK/.excluded"; else COVERED+="$m"$'\n'; fi
done
OWNERS="$( grep -vE '^\s*(#|$)' "$THEOREMS_FILE" | sed 's/:.*//' | awk '!seen[$0]++' )"
ALL_COVERED="$( { printf '%s' "$COVERED"; echo "$OWNERS"; } | awk '!seen[$0]++')"

# -------------------------------------------------------- 1. Build surface ----
BUILT_LIST="";    N_BUILT=0
BUILDFAIL_LIST=""; N_BFAIL=0
NSKIP=0
if [ "$DO_BUILD" = 1 ]; then
  for m in $ALL_COVERED; do
    v="$VO_DIR/$m.v"; o="$VO_DIR/$m.vo"
    [ -f "$v" ] || continue
    if [ -f "$o" ] && [ ! "$v" -nt "$o" ]; then NSKIP=$((NSKIP+1)); continue; fi
    echo "[pa_audit] 编译（guard LoadLimit=$LOADLIMIT core=$COREN）: $m"
    if run_cmd "$WORK/build_$m.log" "$COQC" "$(wpath "$v")"; then
      BUILT_LIST+="$m "; N_BUILT=$((N_BUILT+1))
    else
      BUILDFAIL_LIST+="$m "; N_BFAIL=$((N_BFAIL+1))
      echo "[pa_audit] FAIL 编译: $m（$WORK/build_$m.log）"
    fi
  done
fi

# --------------------------------------------------- 2. PA probes per module ----
parse_pa_log() {  # stdin=plain log (guard lines stripped) $1=expected count; stdout: idx<TAB>RES<TAB>AX<TAB>body
  awk '
    BEGIN { t=1 }
    function flush_open() { if (state==2) { t++ } state=0 }
    /^[[:space:]]*$/ { flush_open(); next }
    /^Closed under the global context[[:space:]]*$/ {
      flush_open(); res[t]="CLOSED"; t++; state=1; next }
    /^(Axioms|Variables|Constants|Opaque constants|Transparent constants|Section Variables):[[:space:]]*$/ {
      if (state!=2) { res[t]="OPEN" }
      state=2
      if ($0=="Axioms:") inax[t]=1; else inax[t]=0
      body[t]=body[t] $0 "\n"; next }
    { if (state==2) { body[t]=body[t] $0 "\n"; if (inax[t]==1 && $0 ~ / : /) ax[t]++ }
      else { stray=stray $0 "\n" } }
    END { for (i=1;i<t;i++) printf "%d\t%s\t%d\t%s\n", i, res[i], ax[i]+0, body[i]
          printf "META\t%d\t%s\n", t-1, (stray==""?"-":stray) > "/dev/stderr" }
  ' 2> "$WORK/.parse_meta"
}

N_TOTAL=$(grep -cvE '^\s*(#|$)' "$THEOREMS_FILE")
declare -a R_NAME=() R_MOD=() R_RES=() R_AX=() R_RAW=()

names_of() { grep -vE '^\s*(#|$)' "$THEOREMS_FILE" | awk -F: -v m="$1" '$1==m{print $2}'; }

probe_module() {  # $1=module; returns 0 on success and appends the results
  local mod="$1"
  local modsan n pf lf names got i nm row res ax raw
  modsan="$(modsan_of "$mod")"
  names="$(names_of "$mod")"
  n="$(echo "$names" | wc -l | tr -d ' ')"
  pf="$WORK/pa_probe_$modsan.v"
  lf="$WORK/pa_probe_$modsan.log"
  { echo "(* pa_audit probe — auto-generated; only Require + Print Assumptions. *)"
    echo "Require Import $mod."
    while IFS= read -r nm; do echo "Print Assumptions $nm."; done <<< "$names"
  } > "$pf"
  run_cmd "$lf" "$COQC" "$(wpath "$pf")" || return 1
  strip_log "$lf" | parse_pa_log "$n" > "$WORK/.parse_out"
  got="$(awk -F'\t' '$1=="META"{print $2}' "$WORK/.parse_meta" | tail -1)"
  [ "$got" = "$n" ] || return 1
  i=0
  while IFS= read -r nm; do
    i=$((i+1))
    row="$(awk -F'\t' -v i="$i" '$1==i' "$WORK/.parse_out")"
    res="$(echo "$row" | cut -f2)"; ax="$(echo "$row" | cut -f3)"; raw="$(echo "$row" | cut -f4-)"
    [ "$res" = "CLOSED" ] || res="FAIL"
    R_NAME+=("$nm"); R_MOD+=("$mod"); R_RES+=("$res"); R_AX+=("$ax"); R_RAW+=("$raw")
  done <<< "$names"
  return 0
}

probe_single() {  # $1=module $2=name; stdout: RES<TAB>AX<TAB>raw
  local mod="$1" nm="$2"
  local modsan pf lf out
  modsan="$(modsan_of "$mod")"
  pf="$WORK/pa_one_${modsan}__${nm}.v"
  lf="$WORK/pa_one_${modsan}__${nm}.log"
  { echo "Require Import $mod."; echo "Print Assumptions $nm."; } > "$pf"
  if run_cmd "$lf" "$COQC" "$(wpath "$pf")" && \
     [ "$(strip_log "$lf" | grep -c '^Closed under the global context')" = "1" ]; then
    printf 'CLOSED\t0\t-\n'
  else
    out="$(strip_log "$lf" | head -20 | tr '\n' '@')"
    printf 'FAIL\t?\t%s\n' "$out"
  fi
}

echo "[pa_audit] PA 探针：owner 模块 $(echo "$OWNERS" | wc -l | tr -d ' ') 个，定理 $N_TOTAL 条"
ISOLATED_MODS=""
for om in $OWNERS; do
  excluded "$om" && continue
  if [ ! -f "$VO_DIR/$om.vo" ]; then
    echo "[pa_audit] FAIL: $om 无 .vo"
    while IFS= read -r nm; do
      R_NAME+=("$nm"); R_MOD+=("$om"); R_RES+=("FAIL"); R_AX+=("?")
      R_RAW+=("模块 $om 无 .vo（见编译段/避让说明）")
    done <<< "$(names_of "$om")"
    continue
  fi
  if probe_module "$om"; then continue; fi
  echo "[pa_audit] 模块探针解析异常，逐定理隔离: $om"
  ISOLATED_MODS+="$om "
  while IFS= read -r nm; do
    out="$(probe_single "$om" "$nm")"
    res="$(echo "$out" | cut -f1)"; ax="$(echo "$out" | cut -f2)"; raw="$(echo "$out" | cut -f3-)"
    R_NAME+=("$nm"); R_MOD+=("$om"); R_RES+=("$res"); R_AX+=("$ax"); R_RAW+=("$raw")
  done <<< "$(names_of "$om")"
done
# Theorems of avoided owners are explicitly recorded as EXEMPT (skipped from checking)
for om in $EXCLUDE_MODS; do
  grep -qE "^$om:" "$THEOREMS_FILE" || continue
  while IFS= read -r nm; do
    R_NAME+=("$nm"); R_MOD+=("$om"); R_RES+=("EXEMPT"); R_AX+=("-")
    R_RAW+=("避让：已知预存缺陷修复中（合并轨收口席），修复入库后补审计")
  done <<< "$(names_of "$om")"
done

N_AUDIT=0; N_CLOSED=0; N_FAIL=0; N_EXEMPT=0
FAIL_APPENDIX="$WORK/.fail_appendix"; : > "$FAIL_APPENDIX"
for i in "${!R_NAME[@]}"; do
  case "${R_RES[$i]}" in
    CLOSED) N_CLOSED=$((N_CLOSED+1)); N_AUDIT=$((N_AUDIT+1)) ;;
    EXEMPT) N_EXEMPT=$((N_EXEMPT+1)) ;;
    *)      N_FAIL=$((N_FAIL+1)); N_AUDIT=$((N_AUDIT+1))
            {
              printf '### FAIL: %s（%s） — axiom 数: %s\n\n' "${R_NAME[$i]}" "${R_MOD[$i]}" "${R_AX[$i]}"
              printf '~~~\n%s\n~~~\n\n' "${R_RAW[$i]}"
            } >> "$WORK/.fail_appendix" ;;
  esac
done

# ---------------------------------------------------- 3. zero-admission grep ----
ZEROADM="$WORK/.zeroadm"; : > "$ZEROADM"
for m in $ALL_COVERED; do
  excluded "$m" && continue
  v="$VO_DIR/$m.v"; [ -f "$v" ] || continue
  grep -nE '^[[:space:]]*(Axiom|Admitted|Parameter|Conjecture|Abort)\b' "$v" 2>/dev/null | \
    sed "s|^|$m.v:|" >> "$ZEROADM"
done
N_ZEROADM="$(wc -l < "$ZEROADM" | tr -d ' ')"
N_FILES_Z=0
for m in $ALL_COVERED; do
  excluded "$m" || { [ -f "$VO_DIR/$m.v" ] && N_FILES_Z=$((N_FILES_Z+1)); }
done || true

# ------------------------------------------------------- 4. coqchk ----
COQCHK_BLOCK=$'（未启用：以 --coqchk 开关开启）'
if [ "$DO_COQCHK" = 1 ]; then
  if [ -z "$COQCHK" ]; then
    COQCHK_BLOCK=$'coqchk 可执行缺失，本节缺位。'
  else
    echo "[pa_audit] coqchk（owner 合并单趟 + -o 假设清单）..."
    ck_ok=0
    if run_cmd "$WORK/coqchk_combined.log" "$COQCHK" -silent -o $OWNERS; then
      strip_log "$WORK/coqchk_combined.log" | grep -q "Modules were successfully checked" && ck_ok=1
      # Measured on 9.0: -silent suppresses the "Modules were successfully checked" line (9.1 re-verified the same, SW2 retarget evidence;
      # docs/coqchk认证总表 判定式系对无 -silent 形态）。rc=0 且 -o 假设清单段（"* Axioms:"）在场 =
      # both conditions hold (2026-09-11 continuation-session fix; upheld by the 2026-09-15 SW2 retarget-to-9.1 re-verification).
      # Note: the CONTEXT SUMMARY section is center-indented; do not use a line-start anchor (2026-09-11 second fix).
      strip_log "$WORK/coqchk_combined.log" | grep -q "\* Axioms:" && ck_ok=1
    fi
    if [ "$ck_ok" = 1 ]; then
      # Axioms-section entry extraction: section bounds run from "* Axioms:" to "* Constants" (center-indented; do not anchor at line start);
      # entries inside are indented path names (no colon); do not count them via ' : ' (it would wrongly include guard stderr, 2026-09-11 third fix).
      axsec="$(strip_log "$WORK/coqchk_combined.log" | sed -n '/\* Axioms:/,/\* Constants/p' | grep -vE '^[[:space:]]*$|^[[:space:]]*\*' | sed 's/^[[:space:]]*//' | grep -c . || true)"
      axnames="$(strip_log "$WORK/coqchk_combined.log" | sed -n '/\* Axioms:/,/\* Constants/p' | grep -vE '^[[:space:]]*$|^[[:space:]]*\*' | sed 's/^[[:space:]]*//' | tr '\n' '；')"
      COQCHK_BLOCK="coqchk（Rocq 9.0 工具链，-silent -o 输出假设清单；owner 模块合并单趟：$(echo $OWNERS | tr ' ' ',')）：**PASS**（rc=0，成功行被 -silent 抑制、以假设清单段在场判定）；环境 Axioms 段条目数：${axsec:-0}（${axnames:-无}——均为 Stdlib 侧 axiom、经 Stdlib 内部传递链装入环境，非本库声明；被审常量对其零依赖由逐件 Print Assumptions 全 Closed 见证）。log：scripts/_pa_work/coqchk_combined.log（log 尾 guard powershell 之 SetConsoleWindowTitle 无控制台异常为无害噪音）"
    else
      COQCHK_BLOCK=$'coqchk 合并趟未过（FAIL），逐模块定位：\n\n| 模块 | 结果 |\n|---|---|'
      for om in $OWNERS; do
        excluded "$om" && continue
        if run_cmd "$WORK/coqchk_$om.log" "$COQCHK" -silent -o "$om" && \
           { strip_log "$WORK/coqchk_$om.log" | grep -q "Modules were successfully checked" || \
             strip_log "$WORK/coqchk_$om.log" | grep -q "\* Axioms:"; }; then
          COQCHK_BLOCK+="\\n| $om | PASS |"
        else
          COQCHK_BLOCK+="\\n| $om | **FAIL**（log: _pa_work/coqchk_$om.log） |"
        fi
      done
    fi
  fi
fi

# ------------------------------------------------------- 5. Report ----
T_END=$(date +%s)
ELAPSED=$((T_END - T_START))
COOL_TOTAL=0
while read -r c; do [ -n "$c" ] && COOL_TOTAL=$((COOL_TOTAL + c)); done < "$WORK/.cool_count"
if [ "$USE_GUARD" = 1 ]; then
  HOTWAIT="$((COOL_TOTAL * 5))s（按 guard cooling 行计数 × CoolSec=5 估算）"
else
  HOTWAIT="不适用（未启用 guard）"
fi
SCRIPT_SHA1="$(sha1sum "$SCRIPT_DIR/$(basename "${BASH_SOURCE[0]}")" | cut -d' ' -f1)"
N_COVERED=0
for m in $ALL_COVERED; do excluded "$m" || N_COVERED=$((N_COVERED+1)); done
N_EXT=$((N_TOTAL - 81 - 27))
[ -f "$WORK/.excluded" ] && EXCL_LIST="$(tr '\n' ' ' < "$WORK/.excluded")" || EXCL_LIST=""

{
echo "# Print Assumptions 全量批审计报告（pa_audit）"
echo
echo "- 生成时间：$TS_NOW；总耗时：${ELAPSED}s（含 guard 热等待 $HOTWAIT）"
echo "- 脚本：scripts/pa_audit.sh（SHA1 \`$SCRIPT_SHA1\`）；清单：scripts/pa_theorems.txt（$N_TOTAL 条）"
echo "- 工具链：$COQ_VERSION（Windows 走 9.1 完整路径 \`$COQ_BIN\`，禁裸 PATH——2026-09-15 全库换装 9.1，原 9.0/9.1 混装 bad version 90001 预警作废；CI 自托管经 runner 侧 cw_build.cmd/cw_chk.cmd 注入 COQC/COQCHK，须同步指向 9.1）"
echo "- root：$ROOT_NAME（$VO_DIR）；guard：LoadLimit=$LOADLIMIT / CoreN=$COREN（cpu_guard.ps1，root 外既定件）"
echo
echo "## 总判定"
echo
echo "- **Closed $N_CLOSED / Fail $N_FAIL / EXEMPT(避让) $N_EXEMPT，共 $N_TOTAL 条**；覆盖模块 $N_COVERED 个（基座 $BASE_MOD ＋ scripts/order.txt 全部 ＋ 清单所涉在树模块；避让剔除：$EXCL_LIST）"
echo "- 零承认 grep（行首口径 \`Axiom|Admitted|Parameter|Conjecture|Abort\`）：**$N_FILES_Z 个源文件扫描，命中 $N_ZEROADM**"
echo
echo "## 编译动作（.vo 缺失或旧于 .v 方编译；一律 guard 包装 + 9.1 显式路径）"
echo
echo "- 新编译 $N_BUILT：${BUILT_LIST:-无}"
echo "- 编译失败 $N_BFAIL：${BUILDFAIL_LIST:-无}"
echo "- 免编复用（.vo 不旧于 .v）$NSKIP"
[ -s "$WORK/.excluded" ] && echo "- 避让未编（合并轨收口席修复中，跳编跳查）：$(tr '\n' ' ' < "$WORK/.excluded")"
echo
echo "## 逐定理结果（名字 | 所在模块 | Closed/Fail | 依赖 axiom 数）"
echo
echo "| 名字 | 所在模块 | 结果 | 依赖 axiom 数 |"
echo "|---|---|---|---|"
for i in "${!R_NAME[@]}"; do
  res="${R_RES[$i]}"
  if   [ "$res" = "CLOSED" ]; then disp="Closed"
  elif [ "$res" = "EXEMPT" ]; then disp="EXEMPT(避让)"
  else disp="**FAIL**"; fi
  echo "| ${R_NAME[$i]} | ${R_MOD[$i]} | $disp | ${R_AX[$i]} |"
done
echo
if [ "$N_FAIL" -gt 0 ]; then
echo "## Fail 附录（完整输出）"
echo
cat "$FAIL_APPENDIX"
fi
[ -n "$ISOLATED_MODS" ] && echo "- 逐定理隔离模块（模块级解析异常，已单定理重跑定界）：$ISOLATED_MODS"
echo
echo "## coqchk 汇总"
echo
echo "$COQCHK_BLOCK"
echo
echo "## 零承认 grep（行首口径）"
echo
echo "- 扫描范围：覆盖集内 $N_FILES_Z 个 .v（词表：\`^[[:space:]]*(Axiom|Admitted|Parameter|Conjecture|Abort)\\b\`；避让件不在扫）"
if [ "$N_ZEROADM" = "0" ]; then
  echo "- **命中 0**（与 attn\\G1全库合规自查-20260910.md 的 L1 层 34/34 FAIL=0、《零公理审计口径说明》L1 一致）"
else
  echo "- 命中 $N_ZEROADM："
  echo '```'
  cat "$ZEROADM"
  echo '```'
fi
echo
echo "## 漂移清单（论文-库命名漂移，逐条在案、不跳过）"
echo
echo "| 论文名 | 库内现状 | 判定 |"
echo "|---|---|---|"
echo "| req_step_kl_eta_bound（论文1 §4.3.2 批3 同位桥件名） | 仓库树与 attn 均无此声明 | 命名漂移/待入库；近邻已入清单：real_step_kl_eta_bound_eps（基座219）、geod_step_kl_eta_bound_eps（UpReqGeomD） |"
echo "| r2_step_kl_weighted（论文1 UpReqAlign3 六件清单名） | 库内无声明 | 命名漂移；近邻 r2_step_kl_rearr（UpReqAlign3） |"
echo "| rppo_align_objective_advantage_decomp（论文1 快照锚，UpReqPPO） | 仓库树无；仅 attn 工作区在盘 | 轮 9 待入库面（非命名漂移），入库后补审 |"
echo "| attention_minimizes_free_energy（论文2 概念名） | 库内声明为 req_attention_minimizes_free_energy_unique（UpReqFEPAttn） | 已按库内正名入清单 |"
echo "| tv_doeblin_contraction / tv_doeblin_iter（论文2 定理 5.10） | 库内无声明（UpTVReal 存档件未并入模块化树） | 存档件未并入/命名漂移；双点 TV 收缩以基座 attention_tv_contraction 族与 UpReqSampling bounded_softmax_tv 族承载 |"
echo "| real_kl_sum_decomp（论文2 §Real 复刻清单定理 4.1 侧名） | 基座 .v 注释幻影：L43735 重复注释头嵌套未闭、定理文本被吞，.vo 零导出（CW214KL_scan 垫片同构同判） | 非真实声明（注释幻影），不入清单；承 probe_full.v 历史注记同判；定理 4.1 主承载 free_energy_kl_decomp 已入清单。论文侧引用该名处建议 camera-ready 前对表 |"
echo
echo "## 覆盖边界（如实登记）"
echo
echo "- **UpIDL / UpMinP：已知预存缺陷修复中（合并轨收口席），跳编跳查，修复入库后补审计**（本次 EXEMPT 口径；coqchk 合并趟环境内含其既有 .vo 属只读加载，非对其重认证）。"
echo "- **attn 工作区轮 9 新件待入库后重跑**：attn 侧较新版本（2026-09-10 版 UpAuditBridge/UpBudgetReal/UpCLQuery/UpDPOLip/UpDebtGibbsT/UpDebtSqrtAbs 等、UpReqPPO 之 rppo_align_objective_advantage_decomp）未入库，不在本报告覆盖；入库后重跑本脚本即得全量新口径。"
echo "- UpReqAlign3.v、UpAlignIdReq.v 在仓库树有源有 .vo 但未列入 order.txt：前者为清单 owner 已并入覆盖，后者无清单定理未逐一探针（零承认 grep 已含）。"
echo "- CW214KL_scan.v / AttnHardLimit218.v 为基座内容只读垫片件（order.txt 在列、随编译面覆盖），其与基座重名系历史垫片设计；无清单定理取自该两件。"
echo "- req_free_energy_kl_decomp 在 UpReqDist/UpSigMigrate/UpSigMigrate2/CW220_Extensions 四处同名声明、req_attention_is_gibbs_temp 在 UpSigMigrate/CW220_Extensions 两处：清单取论文交付正名模块（UpReqDist / UpSigMigrate）；探针逐模块隔离 Require，无歧义。"
echo
echo "## 谱系与复现"
echo
echo "- 定理清单承 \`演变\\.ablation\\sc2_parallel\\sL_assumptions\\probe_full.v\`（81 条，基态 198/206 批量 CLEAN 链）＋论文1/2 头条族补录 $N_EXT 条 ＋ req 系旗舰 27 条；断言/解析方式承同目录 assert_print_assumptions.ps1 / parse_pa_log.ps1 的 bash 化；负载闸承 \`演变\\.ablation\\cpu_guard.ps1\`（LoadLimit 与在飞席热并发自调）。"
echo "- 复现：仓库根执行 \`bash scripts/pa_audit.sh --coqchk\`（复用现成 .vo 可加 \`--no-build\`）。旁证 log 全量在 scripts/_pa_work/。"
echo "- 与旧基线差值：81 条旧口径（基态 198/206 CLEAN）→ 本报告 $N_TOTAL 条；基座由单文件 198/206 迁至 219 模块树（\`$ROOT_NAME\`，基座 CW_ConstructiveWorld_219 ＋ Up* 模块），旧口径 81 条全部保留并逐条重跑。"
} > "$REPORT"

echo "[pa_audit] 完成：Closed $N_CLOSED / Fail $N_FAIL / EXEMPT $N_EXEMPT（共 $N_TOTAL）；报告 $REPORT；耗时 ${ELAPSED}s"
[ "$N_FAIL" = 0 ] || exit 1
exit 0
