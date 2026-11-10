#!/bin/bash
# parallel_build.sh — full-tree build, dependency-layered parallel edition v2 (20261019 set1557 revision)
#
# v1->v2 revision reasons (run#267 double-red root causes):
#   R1 Windows python /tmp path fix: the v1 heredoc Python used the POSIX absolute path
#      open('/tmp/...') -- native Windows python resolves it as <drive>:\tmp\... (cwd drive),
#      a different location from MSYS bash /tmp (%TEMP%) -> FileNotFoundError -> layer output 0 bytes
#      -> layers=0 zero-compile fake green (run#267 Build step evidence). v2 routes all Python data
#      through cwd-relative paths (_pbld_tmp/), identical on Windows/macOS.
#   R2 generation invalidation (cross-machine push consistency): when PBLD_CHANGED_SINCE=<base sha> is set, changed
#      files are collected via git diff -> coqdep reverse closure -> stale-generation .vo quadruples deleted, then rebuilt.
#      Judging a changed file's stale .vo "fresh" by mtime fingerprint is a tear source under cross-machine push (.vo burning an old-generation digest while .v has moved on).
#      Without a base, fall back to the pure mtime fingerprint (same-machine push semantics).
#   R3 three fail-loud assertions (run#267 layers=0 fake-green lesson): zero layer lines = exit 2;
#      layer total != source list = exit 2; order.txt registration surface missing source/.vo = exit 1. No silent downgrade.
#
# Principle: rocq dep builds the dependency graph -> Kahn topological layering (modules within a layer are mutually independent) -> per-layer parallelism:
# modules with missing/stale .vo are compiled in parallel via xargs -P (layers strictly serial -- dependencies land in earlier layers). The final build-face pass
# (ConstructiveWorld_vo/build.sh, walking the order topology module by module) is handled by a subsequent yml step.
#
# Environment variables: COQC (coqc path; Windows default derived from Rocq-Platform 9.1; on the mac side the yml step explicitly
# exports the mac_rocq shim) / CHK_ROCQDEP (rocq path override) / BLDJ_JOBS (parallelism, default 3) /
# PYTHON / PBLD_CHANGED_SINCE (base sha, generation invalidation) / PBLD_AUTO_BASE=1 (CI-inline
# auto-detection of the latest green run head as base, needs GITHUB_TOKEN) / GITHUB_TOKEN.
# fail-loud: any module failing to compile -> red-file list written to /tmp/_pbld_fail.txt + exit 1.
set -u
cd "$(dirname "$0")/../ConstructiveWorld_vo" || { echo "PBLD-PWD-FAIL"; exit 2; }
COQC_BIN="${COQC:-C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe}"
JOBS="${BLDJ_JOBS:-3}"
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || { PY=python; command -v "$PY" >/dev/null 2>&1 || PY=py; }
command -v "$PY" >/dev/null 2>&1 || { echo "PBLD-NO-PYTHON: python3/python/py 全缺席"; exit 2; }

# SW2 same-source export (same protocol as coqchk_all.sh/parallel_chk.sh)
case "$COQC_BIN" in
  */bin/coqc.exe) COQLIB="${COQC_BIN%/coqc.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqc)     COQLIB="${COQC_BIN%/coqc}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$COQC_BIN" in
  *coqc.exe) ROCQDEP="${COQC_BIN%coqc.exe}rocq.exe" ;;
  *coqc)     ROCQDEP="${COQC_BIN%coqc}rocq" ;;
esac
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

# Workspace: cwd-relative paths (R1 -- the only address form Windows python can open)
WORK="_pbld_tmp_$$"   # per-instance unique (same verdict as the parallel_chk multi-writer clobbering)
rm -rf "$WORK"; mkdir -p "$WORK"

# step 1: full source list + dependency graph (20261105 keeper4: maxdepth 2 covers the Local/ subdir -- order.txt has
#    a Local/LW0LeibSeparation.v registration line and assertion 3a demands source+artifact both present for it; with
#    maxdepth 1 it would be missed and the assertion would go red (PBLD-COV-NO-VO); lane log names are made subdir-safe
#    via tr '/' '_'. The old `! -name '_*'` exclusion is removed together with it: _twc_probe.v in the vo tree is a
#    registered module (order line) and is Required by UpReqPadeTransport.v:34 -- excluding it leaves the module with
#    zero artifact -> consumers red + assertion 3a red. A full-tree survey found exactly one _-prefixed source, _twc_probe.v (both trees surveyed), so removing the exclusion has no side effects.)
find . -maxdepth 2 -name '*.v' | sed 's|^\./||' | sort > "$WORK/allv.txt"
NALL=$(wc -l < "$WORK/allv.txt")
[ "$NALL" -gt 0 ] || { echo "PBLD-NO-SOURCES"; exit 2; }
"$ROCQDEP" dep -Q . "" $(cat "$WORK/allv.txt") > "$WORK/deps.txt" 2>/dev/null || true
[ -s "$WORK/deps.txt" ] || echo "PBLD-WARN-EMPTYDEP: rocq dep 零输出（依赖图空·分层退化名单层——fail-loud 留痕）"

# step 2: generation invalidation (R2): base sha -> changed .v set -> reverse closure -> delete stale-generation .vo
BASE="${PBLD_CHANGED_SINCE:-}"
if [ -z "$BASE" ] && [ "${PBLD_AUTO_BASE:-0}" = "1" ] && [ -n "${GITHUB_TOKEN:-}" ] && command -v git >/dev/null 2>&1; then
  API="https://api.github.com/repos/${GITHUB_REPOSITORY:-}/actions/runs?branch=main&status=success&per_page=1"
  BASE=$(curl -s -m 20 -H "Authorization: token $GITHUB_TOKEN" "$API" | "$PY" -c "import json,sys
try: print(json.load(sys.stdin)['workflow_runs'][0]['head_sha'])
except Exception: print('')" 2>/dev/null || true)
  [ "${BASE:-}" = "$(git rev-parse HEAD 2>/dev/null)" ] && BASE=""
fi
: > "$WORK/invalidate.txt"
if [ -n "$BASE" ] && { git cat-file -e "$BASE" 2>/dev/null || git fetch --depth=1 -q origin "$BASE" 2>/dev/null; }; then
  if git diff --name-only "$BASE" HEAD --relative > "$WORK/rawdiff.txt" 2>/dev/null; then
    # the changed set keeps cwd-relative paths (allv roster key shape; basename stripping once made Local/ subdir changes never hit the roster -- Main CI 9.3 run#5 same-class normalization bug)
    grep '\.v$' "$WORK/rawdiff.txt" 2>/dev/null | sort -u > "$WORK/changed.txt" || : > "$WORK/changed.txt"
    "$PY" - "$WORK/allv.txt" "$WORK/deps.txt" "$WORK/changed.txt" > "$WORK/invalidate.txt" <<'PYEOF'
import sys
from collections import defaultdict
allv_f, deps_f, changed_f = sys.argv[1], sys.argv[2], sys.argv[3]
allv = [l.strip() for l in open(allv_f, encoding='utf-8', errors='replace') if l.strip()]
allset = set(a[:-2] for a in allv)  # normalize to bare module names (allv holds .v filename shapes -- mixing the two rosters silently yields zero hits, evidenced in-run)
rdeps = defaultdict(set)
for line in open(deps_f, encoding='utf-8', errors='replace'):
    if ':' not in line:
        continue
    left, right = line.split(':', 1)
    vt = [t for t in left.split() if t.endswith('.vo')]
    if not vt:
        continue
    def norm(t):
        # full relative-path form first (roster keys of Local/ subdir files include the directory), basename form as
        # fallback -- stripping to a single basename once normalized Local/LW0LeibSeparation into LW0LeibSeparation
        # != roster key, silently dropping the whole dependency edge (one root cause of Main CI 9.3 run#5 fail=34).
        p = t.replace('\\', '/')
        if p.endswith('.vo'):
            p = p[:-3]
        return p if p in allset else p.split('/')[-1]
    src = norm(vt[0])
    if src not in allset:
        continue
    for t in right.split():
        if t.endswith('.vo') and not t.startswith('/'):
            d = norm(t)
            if d != src and d in allset:
                rdeps[d].add(src)
changed = [l.strip() for l in open(changed_f, encoding='utf-8', errors='replace') if l.strip()]
inv = set(); st = []
for c in changed:
    m = c[:-2] if c.endswith('.v') else c
    if m in allset:
        st.append(m)
if changed and not st:
    sys.stderr.write('PBLD-GEN-ANOMALY: changed=%d 但无一命中源清单（名册归一断言红）\n' % len(changed))
    sys.exit(3)
in_tree = len(st)
while st:
    x = st.pop()
    if x in inv:
        continue
    inv.add(x)
    st.extend(rdeps.get(x, ()))
sys.stderr.write('PBLD-GEN-INVALIDATE: changed=%d in-tree-changed=%d reverse-closure=%d of %d\n'
                 % (len(changed), in_tree, len(inv), len(allv)))
for m in sorted(inv):
    print(m)
PYEOF
    genrc=$?
    [ "$genrc" -eq 0 ] || { echo "PBLD-GEN-PY-FAIL: 失效面 python rc=$genrc —— fail-loud"; exit 2; }
    NINV=$(wc -l < "$WORK/invalidate.txt")
    echo "PBLD-GEN: base=$BASE invalidate_set=$NINV"
    while IFS= read -r m; do
      [ -n "$m" ] || continue
      for ext in vo vos vok glob; do rm -f "${m}.${ext}" 2>/dev/null || true; done
    done < "$WORK/invalidate.txt"
  else
    echo "PBLD-GEN: git diff 失败（base 非祖先/浅历史缺对象）——回退 mtime 指纹模式（fail-loud 留痕）"
    BASE=""
  fi
else
  if [ -n "$BASE" ]; then
    echo "PBLD-GEN: git fetch base 失败（网络窗）——回退 mtime 指纹模式（fail-loud 留痕）"
    BASE=""
  else
    echo "PBLD-GEN: no base（mtime 指纹模式——同机推送语义）"
  fi
fi

# step 3: Kahn layering -- a layer = one wave of zero-indegree stripping (parallel-safe within a layer)
# Native Windows python text-mode stdout redirection always emits CRLF: the trailing CR of a layer line survives bash
# read, a CR attached to the layer's last filename breaks the ${f%.v} suffix strip and makes the "name.v\r.vo" existence
# test always false -- every layer's tail module is fully rebuilt under a false "missing" (seed .vo fingerprint skip
# defeated; Main CI 9.3 run#8 evidence: 30 lanes = 29 layer-tails + Local). Correct form = pin LF on the producer; bash [ -f ]/[ -nt ] on the consumer never eats CR, so this is the only reliable fix point.
"$PY" - "$WORK/allv.txt" "$WORK/deps.txt" > "$WORK/layers.txt" <<'PYEOF'
import sys
sys.stdout.reconfigure(newline='\n')
from collections import defaultdict, deque
allv_f, deps_f = sys.argv[1], sys.argv[2]
allv = [l.strip() for l in open(allv_f, encoding='utf-8', errors='replace') if l.strip()]
allset = set(allv)
deps = defaultdict(set)
for line in open(deps_f, encoding='utf-8', errors='replace'):
    if ':' not in line:
        continue
    left, right = line.split(':', 1)
    vt = [t for t in left.split() if t.endswith('.vo')]
    if not vt:
        continue
    def norm(t):
        # full relative-path form first (roster keys of Local/ subdir files include the directory), basename form as
        # fallback -- stripping to a single basename once normalized Local/LW0LeibSeparation into LW0LeibSeparation
        # != roster key, the target line was silently skipped and its indegree recorded 0, so the module was misordered
        # into layer 1, compiling before its dependency S01_BaseRing.vo landed (root cause of Main CI 9.3 run#5 fail=34).
        p = t.replace('\\', '/')
        if p.endswith('.vo'):
            p = p[:-3] + '.v'
        return p if p in allset else p.split('/')[-1]
    src = norm(vt[0])
    if src not in allset:
        continue
    for t in right.split():
        if t.endswith('.vo') and not t.startswith('/'):
            d = norm(t)
            if d != src and d in allset:
                deps[src].add(d)
indeg = {f: len(deps[f]) for f in allv}
rdeps = defaultdict(list)
for f, ds in deps.items():
    for d in ds:
        rdeps[d].append(f)
q = deque(sorted(f for f in allv if indeg[f] == 0))
placed = set()
layers = []
while q:
    layer = sorted(q); q = deque()
    layers.append(layer)
    placed |= set(layer)
    for f in layer:
        for c in sorted(rdeps[f]):
            if c in placed:
                continue
            indeg[c] -= 1
            if indeg[c] == 0:
                q.append(c)
rest = sorted(allset - placed)
if rest:
    sys.stderr.write("PBLD-WARN-DEPCYCLE: %d 件环余量按名序追加尾层\n" % len(rest))
    layers.append(rest)
for layer in layers:
    print('\x1f'.join(layer))
PYEOF

# assertion 3a, fail-loud #1: zero layer lines (python crash/empty input -- run#267 fake-green lesson; no silent PASS)
[ -s "$WORK/layers.txt" ] || { echo "PBLD-NO-LAYERS: 分层输出 0 字节（python 分层崩或空输入）——fail-loud"; exit 2; }
# assertion 3b, fail-loud #2: layer total == source list total
NTOT=$(tr '\037' '\n' < "$WORK/layers.txt" | grep -c '\.v$' || true)
[ "${NTOT:-0}" -eq "$NALL" ] || { echo "PBLD-TOTAL-MISMATCH: layers_total=$NTOT sources=$NALL —— fail-loud"; exit 2; }

# step 4: per-layer parallel compile (compile only when missing or in the invalidation set; without a base, fall back to the mtime fingerprint)
# The lane body is written out as a script file (20261019 mac precedent: a multi-line single-quoted inline bash -c
# got truncated by BSD xargs -I{} -> "line 7: unexpected end of file", the whole layer compiling nothing; the file form is identical on both platforms, zero quote dance)
: > "$WORK/fail.txt"
cat > "$WORK/lane.sh" <<'LANE'
#!/bin/bash
f="$1"
log="$WORK/lane_$(printf '%s' "$f" | tr '/' '_').log"
if "$COQC_BIN_LANE" -native-compiler no -q -Q . "" "$f" > "$log" 2>&1; then
  echo "OK $f"
else
  echo "FAIL $f" >> "$WORK/fail.txt"
fi
LANE
export COQC_BIN_LANE="$COQC_BIN" WORK
chmod +x "$WORK/lane.sh" 2>/dev/null || true
nbuilt=0; nskip=0; nfail=0; layer_i=0
while IFS= read -r layer; do
  [ -n "$layer" ] || continue
  layer_i=$((layer_i+1))
  todo=""
  for f in $(printf '%s' "$layer" | tr '\037' ' '); do
    m="${f%.v}"
    if [ -f "${m}.vo" ]; then
      if [ -n "$BASE" ]; then
        # generation-invalidation mode: .vo on disk and not in the invalidation set => SKIP (source bytes match the base generation; layer-level induction preserved)
        if ! grep -qxF "$m" "$WORK/invalidate.txt" 2>/dev/null; then nskip=$((nskip+1)); continue; fi
      else
        # mtime fallback mode (v1 semantics)
        if [ "${m}.vo" -nt "$f" ]; then nskip=$((nskip+1)); continue; fi
      fi
    fi
    todo="$todo $f"
  done
  [ -n "$todo" ] || continue
  echo "$todo" | tr ' ' '\n' | grep -v '^$' | \
    xargs -P "$JOBS" -I{} "$WORK/lane.sh" {} | while read -r st f; do echo "  [L$layer_i] $st $f"; done
done < "$WORK/layers.txt"
# Count read directly (E-STAGING-R84-GATECHAIN lesson: avoids the pipeline-count short-circuit pitfall -- separate tally)
nf=$(grep -c "^FAIL" "$WORK/fail.txt" 2>/dev/null || true)
[ "${nf:-0}" -eq 0 ] || nfail=$nf
echo "parallel_build: layers=$layer_i total=$NALL compiled_or_invalidated=$((NTOT-nskip)) skip=$nskip fail=${nfail:-0}"

# assertion 4a, fail-loud #3: order.txt registration-surface coverage (missing source/.vo goes red -- no-missed-module gate)
covfail=0
while IFS= read -r line; do
  f=$(printf '%s' "$line" | sed 's/#.*//' | tr -d '\r' | tr -d ' ')
  case "$f" in *.v) ;; *) continue ;; esac
  if [ ! -f "$f" ]; then echo "PBLD-COV-MISSING-SRC: 注册面 $f 源缺席"; covfail=1; continue; fi
  if [ ! -f "${f%.v}.vo" ]; then echo "PBLD-COV-NO-VO: 注册面 $f 编译产物缺席"; covfail=1; fi
done < order.txt
[ "$covfail" -eq 0 ] || { echo "PBLD-COVERAGE-FAIL: 注册面覆盖断言红（清单见上）——fail-loud"; exit 1; }

if [ "${nfail:-0}" -eq 0 ]; then
  echo "PARALLEL_BUILD_PASS"
  exit 0
fi
echo "PARALLEL_BUILD_FAIL — red files:"
# 20261105 keeper4 bug fix: the original cat /tmp/_pbld_fail.txt and the fail.txt write location ($WORK/fail.txt)
# were misaligned -- the red list could never print (Windows python /tmp != MSYS /tmp; same family as the v1 lesson). fail-loud evidence output.
cat "$WORK/fail.txt"
exit 1
