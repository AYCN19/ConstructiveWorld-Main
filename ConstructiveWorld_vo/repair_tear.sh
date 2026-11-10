#!/bin/bash
# repair_tear.sh v2 — digest-aware tear self-repair (E-STAGING-RT2 upgrade; interface compatible with v1/9b42d46)
#
# Criterion 1 (kept from v1): consumer .vo mtime < the mtime of its Require dependency .vo => tear.
# v1 blind spot (P9/HC2 card evidence): mtime looks normal but the digest embedded in the .vo is stale -- after an upstream rebuild the consumer mtime
#   was backfilled by touch/seeding, or the upstream .vo was missing pending rebuild (its digest necessarily changes on rebuild); three CI rounds missed it
#   (UpReqEntropyDeficitTemp shape). v2 adds two further criteria:
# Criterion 2 (structural staleness, zero cost): dep .v in tree while dep .vo missing, yet the consumer .vo present => build
#   recompiles dep with a necessarily new digest => the consumer is necessarily stale; delete.
# Criterion 3 (digest smoke test, seconds per module): high-suspicion set (families with historical coqchk tears =
#   temperature/bridge/alignment/Gibbs/TVAbs) one `coqchk -silent -o` per module (full closure; measured to catch
#   "Inconsistent assumptions"; -norec crashes Rocq 9.0.1 internally with Invalid_argument, forbidden). Tear signature
#   in output => delete; EXIT!=0 without a signature = tool absent/environment fault => conservatively keep (run #53 lesson, postmortem of 139 wrongly deleted files).
# Umbrella whitelist (HC2 discriminant): umbrella files whose source `grep -cE "^(Definition|Fixpoint|Theorem|Lemma|
#   Corollary|Instance)"`=0 (e.g. the CW_ConstructiveWorld_219 thin shell: small size + zero cst is structural)
#   are marked UMBRELLA, exempt from content suspicion -- deletion follows positive digest evidence only, never size/zero-
#   cst alone as a sole verdict.
# Cascade: Require consumers of anything deleted this round are deleted too (their digest is necessarily stale after rebuild); one build round fully heals.
# Pitfall compliance (LC/HC2 cards): dependency names extracted with literal grep (awk character classes silently
#   output nothing in this environment); _CoqProject and comparisons always tr -d '\r' (measured mixed line endings here; v1 silently skipped CRLF lines).
# Interface (compatible with the CI workflow coq.yml build step): invoked before build, prints the TEAR list, zero interaction,
#   always exit 0. coqchk comes from PATH, falling back to the 9.1 full path when absent (run #53 lesson; 2026-09-15 whole-repo retarget to 9.1); COQCHK= overrides.
# Environment switches (all off by default; CI default behavior = delete; unset means v1-compatible semantics):
#   TRT2_DRYRUN=1    report only, delete nothing (diagnosis/acceptance)
#   TRT2_SUSPECT=RE  override the high-suspicion-set regex (whole match against the .v base name, -i)
#   COQCHK=path      override the coqchk executable
cd "$(dirname "$0")"
DRYRUN="${TRT2_DRYRUN:-0}"
# RT3 regression fix (E-STAGING-RT3): the default is family-name substring matching, .*<family-token>.*; the original default
#   anchored ^(...)$ whole matching, which zero-matched real family base names (UpReqEntropyDeficitTemp/UpReqTVAbsEps etc.,
#   names containing a family word), leaving criterion 3's digest smoke dead code in the default CI environment (sandbox TTempFam evidence: pure digest tear, 0 detections).
SUSPECT="${TRT2_SUSPECT:-.*Temp.*|.*Bridge.*|.*Gibbs.*|.*Align.*|.*TVAbs.*|.*Entropy.*}"
# run #53 lesson: the self-hosted runner's bash has no coqchk on PATH -- bare `coqchk` got EXIT=127.
# SW2 retarget (2026-09-15): user-level COQLIB/ROCQLIB pinned to the 9.0 lib overrides the 9.1 coq_environment.txt,
# so export them derived from the resolved coqchk path, keeping bin/lib same-source (E-STAGING-SW2).
COQCHK_BIN="${COQCHK:-$(command -v coqchk 2>/dev/null || echo "C:/Rocq-Platform~9.1~2026.01/bin/coqchk.exe")}"
case "$COQCHK_BIN" in
  */bin/coqchk.exe) export COQLIB ROCQLIB; COQLIB="${COQCHK_BIN%/coqchk.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
  */bin/coqchk)     export COQLIB ROCQLIB; COQLIB="${COQCHK_BIN%/coqchk}";     COQLIB="${COQLIB%/bin}/lib/coq"; ROCQLIB="$COQLIB" ;;
esac
n=0
declare -A REMOVED
note() { echo "repair_tear: $*"; }
remove_vo() { # $1=.v path  $2=reason tag
  local v="${1%.v}.vo"
  if [ "$DRYRUN" = "1" ]; then
    echo "TEAR($2): $v -> would be removed for rebuild (dryrun)"
  else
    echo "TEAR($2): $v -> removed for rebuild"
    rm -f "$v"
  fi
  REMOVED["${1%.v}"]=1
  n=$((n+1))
}
while IFS= read -r f; do
  f=$(printf '%s' "$f" | tr -d '\r')
  [ -n "$f" ] || continue
  [ -f "$f" ] || continue
  v="${f%.v}.vo"
  [ -f "$v" ] || continue
  base="${f%.v}"
  torn=""
  # ---- criteria 2+1: missing dependency / cascade / mtime inversion (dependency-name extraction verbatim v1) ----
  for dep in $(grep -oE 'Require[[:space:]]+(Import|Export)?[[:space:]]*[A-Za-z0-9_ ]+' "$f" \
      | sed 's/^Require[[:space:]]*//;s/^Import[[:space:]]*//;s/^Export[[:space:]]*//' \
      | tr ' ' '\n' | grep -E '^[A-Za-z0-9_]+$' | sort -u); do
    if [ -f "$dep.v" ] && [ ! -f "$dep.vo" ]; then
      torn="dep-missing:$dep"; break
    fi
    if [ -n "${REMOVED[$dep]:-}" ]; then
      torn="cascade:$dep"; break
    fi
    d="$dep.vo"
    if [ -f "$d" ] && [ "$d" -nt "$v" ]; then
      # v2.2 (run #54 postmortem): alphabetical-order cp seeding across a second boundary can leave the consumer
      #   mtime older than its dependency (219 shell copied first => "torn" by S-series => criterion-2 cascade, 128 deleted).
      #   Real staleness is minutes/days apart; copy noise is <=2s -- judge a tear only at a >=5s difference.
      gd=$(stat -c %Y "$d" 2>/dev/null || echo 0)
      gv=$(stat -c %Y "$v" 2>/dev/null || echo 0)
      if [ $((gd - gv)) -ge 5 ]; then
        torn="mtime-older-than:$d"; break
      fi
    fi
  done
  # ---- criterion 3 digest smoke (high-suspicion set only; skipped when a cheap criterion already tore) ----
  if [ -z "$torn" ]; then
    bname="$(basename "$base")"
    if printf '%s' "$bname" | grep -qiE "^($SUSPECT)$"; then
      smokelog="$(mktemp)"
      "$COQCHK_BIN" -silent -o -Q . "" "$base" > "$smokelog" 2>&1
      ec=$?
      # run #53 incident fix: deletion follows tear signatures only; nonzero exit without a signature = tool absent/environment
      #   fault => always conservatively keep (the old "nonzero => delete" rule once wrongly deleted all 139 healthy .vo files).
      if grep -qE 'Inconsistent assumptions|Anomaly|Fatal' "$smokelog"; then
        torn="digest-smoke:coqchk EXIT=$ec $(head -c 120 "$smokelog" | tr '\n' ' ')"
      elif [ "$ec" -ne 0 ]; then
        note "digest-smoke SKIP($base): coqchk EXIT=$ec 非撕裂签名，保守保全"
      fi
      rm -f "$smokelog"
    elif [ "$(grep -cE '^(Definition|Fixpoint|Theorem|Lemma|Corollary|Instance)' "$f")" -eq 0 ]; then
      note "UMBRELLA(benign whitelist): $f — 0 source Definitions, exempt from content suspicion"
    fi
  fi
  if [ -n "$torn" ]; then
    remove_vo "$f" "$torn"
  fi
done < <(grep '\.v$' _CoqProject | tr -d '\r')
echo "repair_tear: $n torn .vo removed"
exit 0
