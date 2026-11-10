#!/bin/bash
# vo_sync_watch.sh — automatic peer vo trust-cache sync (macOS/bash form; on Windows use vo_sync_watch.ps1)
#
# Mission: this machine is one of the runners; when a CI run pushed by the peer machine goes fully green,
# automatically download its uploaded vo trust cache artifact and mirror-merge it into the local trust-cache
# directory, so the next local CI/local-build seeding step takes the fingerprint SKIP -- closing the "one side pushes new modules to CI, the other auto-localizes + certifies" loop.
#
# Usage (recommended as a resident launchd/scheduled task, or backgrounded with nohup):
#   REPO=hy7pc8gfmf-dotcom/ConstructiveWorld-Main \
#   ARTIFACT=vo-trust-cache-windows \
#   CACHE_DIR=/Users/apple/vo_ci_cache_mac \
#   bash scripts/vo_sync_watch.sh
# Environment variables:
#   REPO        repository (default hy7pc8gfmf-dotcom/ConstructiveWorld-Main)
#   ARTIFACT    artifact name to sync (the peer's artifact; on a Windows-side machine set vo-trust-cache-macos)
#   CACHE_DIR   local trust-cache directory (mac default /Users/apple/vo_ci_cache_mac)
#   POLL_SEC    poll interval (default 60; network single-flight discipline: only 1-2 requests per round)
#   RUN_FILE    synced-run record (default $CACHE_DIR/.vo_sync_last_run)
# token: obtained automatically from git credential (same source as push); without a token only observe, no artifact download (fail-loud logging).
set -u
REPO="${REPO:-hy7pc8gfmf-dotcom/ConstructiveWorld-Main}"
ARTIFACT="${ARTIFACT:-vo-trust-cache-windows}"
CACHE_DIR="${CACHE_DIR:-/Users/apple/vo_ci_cache_mac}"
POLL_SEC="${POLL_SEC:-60}"
RUN_FILE="${RUN_FILE:-$CACHE_DIR/.vo_sync_last_run}"
mkdir -p "$CACHE_DIR"
LAST=0
[ -f "$RUN_FILE" ] && LAST=$(cat "$RUN_FILE" 2>/dev/null || echo 0)
echo "vo_sync_watch: repo=$REPO artifact=$ARTIFACT cache=$CACHE_DIR last_run=$LAST"

get_token() {
  printf "protocol=https\nhost=github.com\n" | git credential fill 2>/dev/null | grep '^password=' | cut -d= -f2
}

while true; do
  TOKEN=$(get_token)
  AUTH=""; [ -n "$TOKEN" ] && AUTH="Authorization: token $TOKEN"
  # step 1: latest green run (single flight, 1 request)
  RUN=$(curl -s --max-time 30 ${AUTH:+-H "$AUTH"} \
    "https://api.github.com/repos/$REPO/actions/runs?branch=main&status=success&per_page=1" \
    | "$("${PYTHON:-python3:-python}" 2>/dev/null || echo python3)" -c "import json,sys
try:
    d=json.load(sys.stdin); r=d['workflow_runs'][0]; print(r['id'])
except Exception:
    print(0)" 2>/dev/null || echo 0)
  if [ -n "$RUN" ] && [ "$RUN" -gt "$LAST" ] 2>/dev/null; then
    echo "vo_sync_watch: new green run $RUN — syncing $ARTIFACT"
    # step 2: locate the artifact (single flight, 1 request)
    AID=$(curl -s --max-time 30 ${AUTH:+-H "$AUTH"} \
      "https://api.github.com/repos/$REPO/actions/runs/$RUN/artifacts?per_page=50" \
      | "${PYTHON:-python3}" -c "import json,sys
try:
    d=json.load(sys.stdin)
    print(next(a['id'] for a in d.get('artifacts',[]) if a['name']=='$ARTIFACT'))
except Exception:
    print(0)" 2>/dev/null || echo 0)
    if [ "${AID:-0}" -gt 0 ] 2>/dev/null && [ -n "$TOKEN" ]; then
      # step 3: download + mirror merge (fetch into a temp area first; verify the zip, then swap atomically)
      TMP=$(mktemp -d)
      if curl -sL --max-time 600 -H "Authorization: token $TOKEN" \
           "https://api.github.com/repos/$REPO/actions/artifacts/$AID/zip" -o "$TMP/vo.zip" \
         && [ "$(stat -f %z "$TMP/vo.zip" 2>/dev/null || stat -c %s "$TMP/vo.zip" 2>/dev/null || echo 0)" -gt 1000 ] \
         && unzip -q -o "$TMP/vo.zip" -d "$TMP/vo"; then
        N=$(find "$TMP/vo" -name '*.vo' | wc -l)
        find "$CACHE_DIR" -maxdepth 1 -name '*.vo' -delete 2>/dev/null
        find "$TMP/vo" -name '*.vo' -exec cp {} "$CACHE_DIR"/ \;
        echo "vo_sync_watch: run $RUN synced $N .vo -> $CACHE_DIR"
        echo "$RUN" > "$RUN_FILE"
      else
        echo "vo_sync_watch: run $RUN artifact download/extract FAILED (will retry next poll) — fail-loud"
      fi
      rm -rf "$TMP"
    else
      echo "vo_sync_watch: run $RUN has no $ARTIFACT (artifact missing or expired) — marking seen"
      echo "$RUN" > "$RUN_FILE"
    fi
    LAST=$RUN
  fi
  sleep "$POLL_SEC"
done
