# CI 运维白皮书 · 通用层（全仓共用·单源正本·20261117）

> **适用域**：ConstructiveWorld 生态全部代码仓（Main／Set／rocqwash／rocq-pi-leibniz 及后续仓）。
> **单源声明**：本文件为 CI 运维通用原则与约束的唯一措辞源——各仓数据文档（ci-ops-data.json 等）引用本文件原则·禁各处改写。修订只改本文件。
> **依据**：近期 CI 修复实战经验蒸馏（20261114-17·SL/P7/y-carrier/vo-gap/attest 重铸/runner 管理/桥劫持/NETRED 等全波次）。

---

## §1 三捷径体系（全仓通用）

已认证模块通过三条捷径跳过重复验证·减轻维护压力：

| 捷径 | 机制 | 配置位 |
|---|---|---|
| **Build fingerprint skip** | .vo mtime ≥ .v mtime → 编译跳过 | parallel_build.sh（fingerprint 模式） |
| **Attest hash inheritance** | .vo sha256 ＝ 档案在册值 → coqchk 免列 | cw_attest.json（attest_reconcile 产出 skip 名册） |
| **Bytecode flag** | coqchk `-bytecode-compiler yes` | parallel_chk.sh 内置（vm_compute 证书 ≥30× 提速） |

**新模块入册规则**：新模块冷编 CI 全绿后 → 跑 `attest_cast.py` 重铸档案 → 新模块进入 skip 名册 → 后续炉走捷径。**每波次必做·不做的后果＝后续每炉冷编该模块**。

**档案重铸工具**：`scripts/gates/attest_cast.py`（单源重铸器·契约逐字对齐 reconcile loader）。

## §2 故障模式分类学（跨仓通用）

| 模式 | 症状 | 根因 | 修法 |
|---|---|---|---|
| checkout-red | `not our ref` / `couldn't find remote ref` | 镜像缺新 commit（API 铸后或他席推后镜像未同步） | 绕桥 fetch + update-ref + rerun |
| furnace-hang | coqc 0 CPU / 8MB 工作集 | **非挂**——rocqworker 子进程满负荷（巨常量单核重算） | 照常磨·采样须测 worker 子进程 |
| gate-false-positive | YAML schema 红 / 主炉不接单 | 注释续行顶格断 mapping | 修 YAML 缩进 |
| attest-stale | PBLD-COV-NO-VO（新件编译产物缺席） | 新模块无档案条目 | attest_cast 重铸 |
| vo-gap | Live-only 落岸 → vo 树缺源 | 双树不同步 | 补 vo 树源 + 册行 |
| runner-offline | API /actions/runners = offline | Listener 进程灭 | 双席重启（.env 钩变量须验） |
| yaml-syntax | schema 红 / jobs=0 | 注释续行顶格断 mapping | 修缩进 |
| w3-trigger | 大量 skip 失效 | W3 兜底周期触发 | 调周期（20→500）＋重类豁免 |
| netred-window | Connection reset / 超时 | hosts 钉过时 | 分面探活 + 重钉 |
| push-anomaly | non-commit object / needs force | API 铸对象本地不在 | PATCH ref 替代 push |
| merge-conflict | read-tree 基底错 → 静默回退 | parent/base 写错 | 重贴修复 blob |
| autofix-leg | autofix 修复带伤未落岸 | 宿主分支 checkout 失败 | 修 checkout 前置 |

## §3 Runner 管理

| 项 | 规则 |
|---|---|
| 双席架构 | clean 席（主认证·有钩）＋旧席（并存·须补钩对称） |
| 钩接线 | .env `ACTIONS_RUNNER_HOOK_JOB_STARTED` ＝钩脚本绝对路径 |
| 复活配方 | Start-Process Runner.Listener.exe run（WorkingDirectory 设 runner 根）→ API online/busy 复核 |
| 判据 | 「观察 ci 没拉起」九成 = runner offline（API /actions/runners status + WMI 进程探测两刀定位） |
| 重启生效 | .env 变更须 listener 重启才加载 |
| 挂死判据 | coqc **worker 子进程** 0 CPU + 8MB 工作集双采样 = 真 hang（包装壳 0 CPU 无意义） |

## §4 桥与镜像

| 项 | 规则 |
|---|---|
| 桥劫持 | 系统级 insteadOf github.com → 本地镜像——checkout/fetch 全落镜像 |
| PR 炉 | 镜像须有 refs/pull/N/head——job_started 钩自动同步 |
| push 炉 | 镜像须有最新 main commit——钩 fetch main + ff |
| API 铸 commit | 对象只在云端——镜像必落后 → PATCH ref 后须绕桥 fetch 同步 |
| 绕桥配方 | GIT_CONFIG_GLOBAL=空文件 + GIT_CONFIG_NOSYSTEM=1 + 真 GitHub URL |
| 认证回灌 | 绿炉 vo 树 → main93 沙箱整树拷贝（.v+.vo+册+BUILD_DONE） |

## §5 推岸规程

| 方式 | 适用 | 命令形 |
|---|---|---|
| git push | 本地有对象·NETRED 窗外 | 绕桥 + extraheader auth |
| API PATCH ref | API 铸 commit（对象在云端）| PATCH refs/heads/main {"sha": ...} |
| API git-data 全链 | 需逐 blob 断言时 | blob POST → tree POST → commit POST → ref PATCH |
| 禁 | 直推 main（工作流中）·零断言 push | — |

**NETRED 切面**：git 面（github.com:443）与 API 面（api.github.com）健康独立——一面断切另一面·分面探活（curl --resolve 逐 IP）。

## §6 层律（全仓通用·宪法级）

| 层 | 内容 | 权限 |
|---|---|---|
| 数据层 | taxonomy 行/词表/改写表 | 乙档自动（新类首准人工一次） |
| 代码层 | tools/ 代码面 | gated 人批 |
| 认证层 | 判定语义/语句体 | 零自动触达 |
| 宪法层 | 本白皮书＋五律 | 人类专属 |

## §7 rocqwash 对接面

| 对接件 | 消费什么 | 来源仓 |
|---|---|---|
| ci_triage 分诊表 | 故障模式分类→修复处方 | Main 仓 ci-ops-data.json |
| cw_sentinel | CI 状态监控→heal 触发 | Main 仓 coq93.yml 步链 |
| automerge 门 | PR 可合并性判定→自动合并 | Main 仓 PR 面 |
| symbiosis 喂送 | 跨仓经验条目→缺口账 | Main 仓 exp-ledger |
