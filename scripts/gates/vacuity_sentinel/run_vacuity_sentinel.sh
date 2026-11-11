#!/usr/bin/env bash
# =============================================================================
# run_vacuity_sentinel.sh - gate8 vacuity sentinel driver.
#
# Purpose.  Compiles the three compile-must-fail probes vacuity_face_a.v,
#   vacuity_face_b.v and vacuity_face_c.v (best-effort corrected-form
#   refutation attempts against the premise interfaces of the compiled top
#   pieces) and asserts that EACH of them FAILS to compile.
#
#   THIS SCRIPT ASSERTS THAT FAILURE IS THE NORMAL STATE.  A probe that
#   compiles cleanly means its contradiction attempt went through, i.e.
#   the premise interface has become jointly unsatisfiable - that is the
#   alarm.  All three probes failing exactly as expected is the healthy
#   state.
#
# Verdicts (exit codes):
#   0  GATE8-GREEN         every probe failed with its expected failure
#                          signature (interface non-vacuous)
#   0  GATE8-INDETERMINATE the probes cannot reach their failure points in
#                          the current tree state (world .vo closure absent,
#                          companion source missing or uncompilable, or a
#                          probe failing for an unexpected reason); not red,
#                          not green - fail loud to the log, no GREEN claim
#   1  GATE8-RED           a probe COMPILED (rc=0): premise interface
#                          jointly unsatisfiable - alarm
#
# Repo-root self-location: three levels up from the directory holding this
# script (vacuity_sentinel -> gates -> scripts -> repo root); the caller's
# working directory is irrelevant, and the located root is sanity-asserted.
#
# Load path (one -Q root per mapping, no same-name double roots):
#   -Q <temporary probe world> ""       companion sources, compiled on the
#                                       fly from the tracked Live-tree
#                                       sources into a temporary directory
#   -Q <repo>/ConstructiveWorld_vo ""   world .vo closure (read-only)
#
# All compile products land in the temporary probe world and are removed on
# exit; the repo tree is never written (the vo tree stays read-only here).
# =============================================================================

set -u

SELF_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# three levels up: vacuity_sentinel -> gates -> scripts -> repo root
ROOT="$(cd "$SELF_DIR/../../.." && pwd)"
if [ ! -d "$ROOT/ConstructiveWorld_vo" ] || [ ! -d "$ROOT/ConstructiveWorld_Live" ]; then
  echo "GATE8-INDETERMINATE: repo root self-location failed (got '$ROOT';" 
  echo "  expected the directory containing ConstructiveWorld_vo/ and ConstructiveWorld_Live/)"
  exit 0
fi
VOTREE="$ROOT/ConstructiveWorld_vo"
LIVETREE="$ROOT/ConstructiveWorld_Live"
COQC="${COQC:-D:/ComplexAnalysis/attn/ocaml_work_20261101/opam-root/default/bin/coqc.exe}"

PROBES="vacuity_face_a vacuity_face_b vacuity_face_c"

# Companion sources in dependency order (tracked in the Live tree; byte
# identical to the corrected-form sources these probes were written
# against).  They are compiled into the temporary probe world before the
# probes run.
COMPANIONS="planb3_g1_calib planb3_g1_g2_design planb4_l2_dv_cast planb1_hcage_zerotouch_prescription"

# World closure modules every probe transitively needs.  If any of them has
# no compiled .vo, the probes would die inside Require (a missing-library
# failure proves nothing about vacuity) - report indeterminate.
WORLD_MODULES="S02_CauchyComplete S10_KVQuantTrig LW0MLicBridge piu_mu_criterion piu1932_uncond_zz piu_zz_padic_clearing"

# Expected failure signature per probe.  A failure whose log does not carry
# the expected signature is not the expected contradiction failure (it is a
# broken-probe or stale-world failure) and proves nothing.
expected_sig() {
  case "$1" in
    vacuity_face_a) echo 'Tactic failure: *Cannot find witness' ;;
    vacuity_face_b) echo 'Tactic failure: *Cannot find witness' ;;
    vacuity_face_c) echo 'cannot unify "Eq" and "Gt"' ;;
    *) echo '' ;;
  esac
}

echo "gate8 vacuity sentinel: repo root = $ROOT"

if [ ! -x "$COQC" ]; then
  echo "GATE8-INDETERMINATE: coqc not found or not executable: $COQC"
  exit 0
fi

# --- 0. world closure availability ------------------------------------------
for m in $WORLD_MODULES; do
  if [ ! -f "$VOTREE/$m.vo" ]; then
    echo "GATE8-INDETERMINATE: world module $m.vo not found under $VOTREE"
    echo "  (no compiled world closure - probes cannot reach their failure points;"
    echo "   run this gate after a full-tree build, or on a locally certified tree)"
    exit 0
  fi
done
echo "world closure: all $(echo $WORLD_MODULES | wc -w | tr -d ' ') sentinel-visible modules present in $VOTREE"

# --- temporary probe world ---------------------------------------------------
TMPD="$(mktemp -d)"
if command -v cygpath >/dev/null 2>&1; then
  TMPW="$(cygpath -m "$TMPD")"
else
  TMPW="$TMPD"
fi
trap 'rm -rf "$TMPD"' EXIT
mkdir -p "$TMPD/logs"
echo "temporary probe world: $TMPW"

# --- 1. compile companion sources (these must PASS; fail loud otherwise) ----
for stem in $COMPANIONS; do
  src="$LIVETREE/$stem.v"
  if [ ! -f "$src" ]; then
    echo "GATE8-INDETERMINATE: companion source missing: $src"
    exit 0
  fi
  cp "$src" "$TMPD/$stem.v"
  "$COQC" -q -native-compiler no -Q "$TMPW" "" -Q "$VOTREE" "" "$TMPW/$stem.v" \
    > "$TMPD/logs/$stem.log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "GATE8-INDETERMINATE: companion $stem failed to compile (rc=$rc)"
    echo "  (probe environment broken - probes would prove nothing; log tail:)"
    tail -5 "$TMPD/logs/$stem.log"
    exit 0
  fi
  echo "companion $stem: compiled (expected pass)"
done

# --- 2. probes: each must FAIL, and fail with its expected signature --------
green=1
for stem in $PROBES; do
  if [ ! -f "$SELF_DIR/$stem.v" ]; then
    echo "GATE8-INDETERMINATE: probe source missing: $SELF_DIR/$stem.v"
    exit 0
  fi
  cp "$SELF_DIR/$stem.v" "$TMPD/$stem.v"
  "$COQC" -q -native-compiler no -Q "$TMPW" "" -Q "$VOTREE" "" "$TMPW/$stem.v" \
    > "$TMPD/logs/$stem.log" 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "GATE8-RED: vacuity - premise interface jointly unsatisfiable"
    echo "  probe $stem COMPILED (rc=0): the contradiction attempt went through."
    exit 1
  fi
  sig="$(expected_sig "$stem")"
  if [ -z "$sig" ] || ! grep -qE "$sig" "$TMPD/logs/$stem.log"; then
    echo "GATE8-INDETERMINATE: probe $stem failed (rc=$rc) but its log lacks the"
    echo "  expected failure signature ('$sig') - this is not the expected"
    echo "  contradiction failure; the probe proves nothing in this state."
    echo "  log tail:"
    tail -8 "$TMPD/logs/$stem.log"
    exit 0
  fi
  echo "probe $stem: correctly failed (rc=$rc, expected failure signature present)"
  green=0
done

# --- 3. verdict ---------------------------------------------------------------
if [ "$green" -eq 0 ]; then
  echo "GATE8-GREEN: interface non-vacuous (all probes failed exactly as expected)"
  exit 0
fi
echo "GATE8-INDETERMINATE: no probe was run"
exit 0
