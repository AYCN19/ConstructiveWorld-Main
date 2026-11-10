#!/bin/bash
# vo_sync_once.sh — one-shot cross-machine vo trust-cache sync (CI bootstrap-step form; also usable as a manual one-shot)
#
# Mission (baseline-4 inline-CI form): the local certification job starts by checking the peer's latest green
# run for a vo-trust-cache artifact -- if newer, download and mirror-merge it into the local cache directory
# so peer-added modules SKIP in this round's build (missing ones get built by parallel_build; changed ones
# get rebuilt via PBLD_CHANGED_SINCE generation invalidation) -- the inline half of the "one side pushes new
# modules to CI, the other auto-localizes + certifies" loop; vo_sync_watch.ps1/.sh runs the resident half.
#
# fail-open contract: network jitter / missing artifact / extract failure all WARN then exit 0 -- sync is an
# enhancement; the certification main chain does not depend on it (missing .vo are rebuilt by build, correctness unaffected). Never make this step a red gate.
#
# Environment variables:
#   SYNC_ARTIFACT   peer artifact name (vo-trust-cache-windows | vo-trust-cache-macos)
#   SYNC_CACHE_DIR  local cache directory (Windows seed source=/d/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo
#                   mac=/Users/apple/vo_ci_cache_mac)
#   SYNC_STATE_FILE synced-run record (default $SYNC_CACHE_DIR/.vo_sync_last_run)
#   REPO / GITHUB_TOKEN (git credential fill as fallback when token missing)
set -u
REPO="${REPO:-hy7pc8gfmf-dotcom/ConstructiveWorld-Main}"
ARTIFACT="${SYNC_ARTIFACT:?SYNC_ARTIFACT required}"
CACHE_DIR="${SYNC_CACHE_DIR:?SYNC_CACHE_DIR required}"
STATE="${SYNC_STATE_FILE:-$CACHE_DIR/.vo_sync_last_run}"
mkdir -p "$CACHE_DIR" 2>/dev/null || { echo "VO_SYNC_ONCE: cache dir not creatable - fail-open exit 0"; exit 0; }
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || { PY=python; command -v "$PY" >/dev/null 2>&1 || PY=py; }
command -v "$PY" >/dev/null 2>&1 || PY=""

TOKEN="${GITHUB_TOKEN:-}"
if [ -z "$TOKEN" ]; then
  TOKEN=$(printf "protocol=https\nhost=github.com\n" | git credential fill 2>/dev/null | grep '^password=' | cut -d= -f2)
fi
AUTH=""; [ -n "$TOKEN" ] && AUTH="Authorization: token $TOKEN"

RUN=$(curl -s -m 20 ${AUTH:+-H "$AUTH"} \
  "https://api.github.com/repos/$REPO/actions/runs?branch=main&status=success&per_page=1" \
  | ${PY:+"$PY"} -c "import json,sys
try: print(json.load(sys.stdin)['workflow_runs'][0]['id'])
except Exception: print(0)" 2>/dev/null || echo 0)
LAST=0; [ -f "$STATE" ] && LAST=$(cat "$STATE" 2>/dev/null || echo 0)
case "${RUN:-0}" in ''|*[!0-9]*) RUN=0 ;; esac
if [ "${RUN:-0}" -le "${LAST:-0}" ]; then
  echo "VO_SYNC_ONCE: no fresh green run ($RUN <= $LAST) - skip"
  exit 0
fi

AID=$(curl -s -m 20 ${AUTH:+-H "$AUTH"} \
  "https://api.github.com/repos/$REPO/actions/runs/$RUN/artifacts?per_page=100" \
  | ${PY:+"$PY"} -c "import json,sys
try:
    print(next(a['id'] for a in json.load(sys.stdin).get('artifacts', []) if a['name'] == '$ARTIFACT'))
except Exception:
    print(0)" 2>/dev/null || echo 0)
case "${AID:-0}" in ''|*[!0-9]*) AID=0 ;; esac
if [ "${AID:-0}" -eq 0 ]; then
  echo "VO_SYNC_ONCE: run $RUN has no $ARTIFACT (peer not green or not uploaded) - mark-seen (fail-open)"
  echo "$RUN" > "$STATE" 2>/dev/null || true
  exit 0
fi

TMP=$(mktemp -d)
if [ -z "$TOKEN" ]; then
  echo "VO_SYNC_ONCE: no token, artifact download skipped - fail-open (observe mode, state not written)"
  rm -rf "$TMP"; exit 0
fi
if curl -sL -m 600 -H "Authorization: token $TOKEN" \
     "https://api.github.com/repos/$REPO/actions/artifacts/$AID/zip" -o "$TMP/vo.zip" \
   && [ -s "$TMP/vo.zip" ] \
   && unzip -qo "$TMP/vo.zip" -d "$TMP/vo" 2>/dev/null; then
  N=$(find "$TMP/vo" -name '*.vo' | wc -l)
  find "$CACHE_DIR" -maxdepth 1 -name '*.vo' -delete 2>/dev/null
  find "$TMP/vo" -name '*.vo' -exec cp {} "$CACHE_DIR"/ \; 2>/dev/null
  echo "VO_SYNC_ONCE: run $RUN synced $N .vo -> $CACHE_DIR"
  echo "$RUN" > "$STATE" 2>/dev/null || true
else
  echo "VO_SYNC_ONCE: download or extract failed - fail-open (retry next round)"
fi
rm -rf "$TMP"
exit 0
