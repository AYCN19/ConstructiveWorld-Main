#!/bin/bash
# parallel_build.sh — 全树构建·依赖分层并行版 v2（20261019 set1557 修订）
#
# v1→v2 修订缘由（run#267 双红根因）：
#   R1 Windows python /tmp 路径修复：v1 的 heredoc Python 以 POSIX 绝对路径
#      open('/tmp/...')——Windows 原生 python 将其解析为 <盘>:\tmp\...（cwd 盘），
#      与 MSYS bash 的 /tmp（%TEMP%）不同址 → FileNotFoundError → 分层输出 0 字节
#      → layers=0 零编译假绿（run#267 Build 步实证）。v2 全部 Python 数据面走
#      cwd 相对路径（_pbld_tmp/），Windows/macOS 双形同源。
#   R2 代差失效（跨机推送一致性）：PBLD_CHANGED_SINCE=<base sha> 时按 git diff
#      收集变面 → coqdep 反向闭包 → 删陈旧代 .vo 四件套后重编。变件陈旧 .vo 靠
#      mtime 指纹判"新鲜"是跨机推送下的撕裂源（.vo 烧录旧代 digest 而 .v 已换代）。
#      无 base 时回退纯 mtime 指纹（同机推送语义）。
#   R3 fail-loud 三断言（run#267 layers=0 假绿教训）：分层零行=exit 2；分层总数
#      != 源清单=exit 2；order.txt 注册面缺源/缺 .vo=exit 1。禁静默降级。
#
# 原理：rocq dep 生成依赖图 → Kahn 拓扑分层（层内模块互不依赖）→ 逐层并行：
# 层内缺失/陈旧 .vo 的件经 xargs -P 并行 coqc（层间必须串行——依赖在先层落盘）。
# 终审 build 面（ConstructiveWorld_vo/build.sh，order 拓扑逐件走）由 yml 后续步承担。
#
# 环境变量：COQC（coqc 路径，Windows 默认 Rocq-Platform 9.1 推导·mac 侧 yml 步显式
# export mac_rocq shim）/ CHK_ROCQDEP（rocq 路径覆盖）/ BLDJ_JOBS（并行度，默认 3）/
# PYTHON / PBLD_CHANGED_SINCE（base sha，代差失效）/ PBLD_AUTO_BASE=1（CI 内联
# 自动探测最近绿 run head 作 base，需 GITHUB_TOKEN）/ GITHUB_TOKEN。
# fail-loud：任何件编译红 → 红件清单落 /tmp/_pbld_fail.txt + exit 1。
set -u
cd "$(dirname "$0")/../ConstructiveWorld_vo" || { echo "PBLD-PWD-FAIL"; exit 2; }
COQC_BIN="${COQC:-C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe}"
JOBS="${BLDJ_JOBS:-3}"
PY="${PYTHON:-python3}"; command -v "$PY" >/dev/null 2>&1 || { PY=python; command -v "$PY" >/dev/null 2>&1 || PY=py; }
command -v "$PY" >/dev/null 2>&1 || { echo "PBLD-NO-PYTHON: python3/python/py 全缺席"; exit 2; }

# SW2 同源导出（与 coqchk_all.sh/parallel_chk.sh 同协议）
case "$COQC_BIN" in
  */bin/coqc.exe) COQLIB="${COQC_BIN%/coqc.exe}"; COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
  */bin/coqc)     COQLIB="${COQC_BIN%/coqc}";     COQLIB="${COQLIB%/bin}/lib/coq"; export COQLIB ROCQLIB="$COQLIB" ;;
esac
case "$COQC_BIN" in
  *coqc.exe) ROCQDEP="${COQC_BIN%coqc.exe}rocq.exe" ;;
  *coqc)     ROCQDEP="${COQC_BIN%coqc}rocq" ;;
esac
ROCQDEP="${CHK_ROCQDEP:-$ROCQDEP}"

# 工作区：cwd 相对路径（R1——Windows python 可 open 的唯一定址形）
WORK="_pbld_tmp_$$"   # 实例唯一（同 parallel_chk 多写者互踩定谳）
rm -rf "$WORK"; mkdir -p "$WORK"

# ① 全源清单+依赖图（20261105 keeper4：maxdepth 2 收 Local/ 子目录——order.txt 有
#    Local/LW0LeibSeparation.v 注册行，③a 覆盖断言对其要求源+产物双在，maxdepth 1
#    漏编则断言必红（PBLD-COV-NO-VO）；lane 日志名经 tr '/' '_' 子目录安全。
#    原 `! -name '_*'` 排除一并摘除：vo 树 _twc_probe.v 系注册件（order 行）且被
#    UpReqPadeTransport.v:34 Require——排除即该件零产物→消费件红+③a 断言红。
#    全树实勘 _ 前缀源=唯 _twc_probe.v 一件（双树同勘），摘除无旁效。）
find . -maxdepth 2 -name '*.v' | sed 's|^\./||' | sort > "$WORK/allv.txt"
NALL=$(wc -l < "$WORK/allv.txt")
[ "$NALL" -gt 0 ] || { echo "PBLD-NO-SOURCES"; exit 2; }
"$ROCQDEP" dep -Q . "" $(cat "$WORK/allv.txt") > "$WORK/deps.txt" 2>/dev/null || true
[ -s "$WORK/deps.txt" ] || echo "PBLD-WARN-EMPTYDEP: rocq dep 零输出（依赖图空·分层退化名单层——fail-loud 留痕）"

# ② 代差失效面（R2）：base sha → 变面 .v → 反向闭包 → 删陈旧代 .vo
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
    # changed 面保留 cwd 相对路径（allv 名册键形；basename 剥除曾使 Local/ 子目录变面永不命中名册——Main CI 9.3 run#5 同类归一病）
    grep '\.v$' "$WORK/rawdiff.txt" 2>/dev/null | sort -u > "$WORK/changed.txt" || : > "$WORK/changed.txt"
    "$PY" - "$WORK/allv.txt" "$WORK/deps.txt" "$WORK/changed.txt" > "$WORK/invalidate.txt" <<'PYEOF'
import sys
from collections import defaultdict
allv_f, deps_f, changed_f = sys.argv[1], sys.argv[2], sys.argv[3]
allv = [l.strip() for l in open(allv_f, encoding='utf-8', errors='replace') if l.strip()]
allset = set(a[:-2] for a in allv)  # 裸模块名归一（allv 为 .v 文件名形——两名册混用即静默零命中，run 内实证）
rdeps = defaultdict(set)
for line in open(deps_f, encoding='utf-8', errors='replace'):
    if ':' not in line:
        continue
    left, right = line.split(':', 1)
    vt = [t for t in left.split() if t.endswith('.vo')]
    if not vt:
        continue
    def norm(t):
        # 全相对路径形优先（Local/ 子目录件名册键含目录），basename 形兜底——
        # 单一 basename 剥除曾把 Local/LW0LeibSeparation 归一成 LW0LeibSeparation
        # ≠ 名册键，整行依赖边被静默丢弃（Main CI 9.3 run#5 fail=34 根因之一）。
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

# ③ Kahn 分层：层=入度零批次的逐波剥离（层内并行安全）
"$PY" - "$WORK/allv.txt" "$WORK/deps.txt" > "$WORK/layers.txt" <<'PYEOF'
import sys
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
        # 全相对路径形优先（Local/ 子目录件名册键含目录），basename 形兜底——
        # 单一 basename 剥除曾把 Local/LW0LeibSeparation 归一成 LW0LeibSeparation
        # ≠ 名册键，目标行被静默跳过、入度记 0，该件被误排第 1 层抢在依赖
        # S01_BaseRing.vo 落盘前编译（Main CI 9.3 run#5 fail=34 根因）。
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

# ③a fail-loud 断言一：分层零行（python 崩溃/空输入——run#267 假绿教训，禁静默 PASS）
[ -s "$WORK/layers.txt" ] || { echo "PBLD-NO-LAYERS: 分层输出 0 字节（python 分层崩或空输入）——fail-loud"; exit 2; }
# ③b fail-loud 断言二：分层总数 == 源清单总数
NTOT=$(tr '\037' '\n' < "$WORK/layers.txt" | grep -c '\.v$' || true)
[ "${NTOT:-0}" -eq "$NALL" ] || { echo "PBLD-TOTAL-MISMATCH: layers_total=$NTOT sources=$NALL —— fail-loud"; exit 2; }

# ④ 逐层并行编译（缺失/在失效集才编；无 base 时按 mtime 指纹回退）
# lane 体落盘为脚本文件（20261019 mac 判例：多行单引号内联 bash -c 经 BSD xargs -I{}
# 截断→"line 7: unexpected end of file" 整层零编；文件形双平台同源零引号 dance）
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
        # 代差失效模式：.vo 在盘且不在失效集 → SKIP（源字节与 base 代一致·层级 induction 保持）
        if ! grep -qxF "$m" "$WORK/invalidate.txt" 2>/dev/null; then nskip=$((nskip+1)); continue; fi
      else
        # mtime 回退模式（v1 语义）
        if [ "${m}.vo" -nt "$f" ]; then nskip=$((nskip+1)); continue; fi
      fi
    fi
    todo="$todo $f"
  done
  [ -n "$todo" ] || continue
  echo "$todo" | tr ' ' '\n' | grep -v '^$' | \
    xargs -P "$JOBS" -I{} "$WORK/lane.sh" {} | while read -r st f; do echo "  [L$layer_i] $st $f"; done
done < "$WORK/layers.txt"
# 计数直读（E-STAGING-R84-GATECHAIN 教义：管道计数短路坑规避——独立统计）
nf=$(grep -c "^FAIL" "$WORK/fail.txt" 2>/dev/null || true)
[ "${nf:-0}" -eq 0 ] || nfail=$nf
echo "parallel_build: layers=$layer_i total=$NALL compiled_or_invalidated=$((NTOT-nskip)) skip=$nskip fail=${nfail:-0}"

# ④a fail-loud 断言三：order.txt 注册面覆盖（缺源/缺 .vo 即红——禁漏件门）
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
# 20261105 keeper4 修 bug：原 cat /tmp/_pbld_fail.txt 与 fail.txt 落盘位（$WORK/fail.txt）
# 错位——红清单永远打不出（Windows python /tmp ≠ MSYS /tmp·v1 教训同族）。fail-loud 出证面。
cat "$WORK/fail.txt"
exit 1
