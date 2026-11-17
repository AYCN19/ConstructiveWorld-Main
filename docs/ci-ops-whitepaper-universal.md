# CI 运维白皮书 · 通用层（全仓共用·单源正本·20261117）

> **适用域**：ConstructiveWorld 生态全部代码仓（Main／Set／rocqwash／rocq-pi-leibniz 及后续仓）。
> **单源声明**：本文件为 CI 运维通用原则与约束的唯一措辞源——各仓数据文档（ci-ops-data.json 等）引用本文件原则·禁各处改写。修订只改本文件。
> **依据**：近期 CI 修复实战经验蒸馏（20261114-17·SL/P7/y-carrier/vo-gap/attest 重铸/runner 管理/桥劫持/NETRED 等全波次）。
> **修订**：20261118 v1.2——§1 重写为正典形态（run#94 参照炉·种子链闭环·PBLD_AUTO_BASE 正形）＋档案保护条款；§2 三新故障模式对齐（skip-regression 三分类）；用户令「#94 最快三捷径规范入册·与不一致处对齐」。v1.1 原表述（mtime fingerprint 为 Build 捷径主形）经 run#107 实证勘误：mtime -nt 在 checkout 落盘序下不可靠·生成失效模式（AUTO_BASE）才是正形。

---

## §1 三捷径体系（全仓通用·正典形态＝run#94）

已认证模块通过三条捷径跳过重复验证。**正典参照炉＝Main CI run#94（head 32f0ea6·20261116）**：全炉 **19 分钟**——seed 播种 1049 .vo → **Build 步 97 秒（skip=1050·compiled=0）** → coqchk 继承 1049 只真验 1 件 → 收炉。任何偏离此形态（Build 大面积 [L*] OK 行、coqchk sent 数暴涨）＝捷径回潮，按 §2 skip-regression 处置。

| 捷径 | 机制 | 配置位 | 正典判定行（炉日志） |
|---|---|---|---|
| **①种子播种** | 炉前从本地信任缓存整树播种（furnace93_seed manifest 按源 sha 过滤＋main93 沙箱 BUILD_DONE 闸整层拷贝） | coq93.yml Seed 步＋`rocq93_work_20261101/furnace93_seed/`＋`main93/ConstructiveWorld_vo/_93m_BUILD_DONE` | `FURNACE93-SEED: manifest=N seeded_valid=M`＋`seeded (mirror-deleted stale) K .vo`（K 应≈全树） |
| **②Build 生成失效跳过** | **PBLD_AUTO_BASE=1（job env 必设）**：以最近绿炉 head 为 base→diff changed 集→反向依赖闭包失效→**其余全量 SKIP**；mtime 兜底仅作 base 判定失败的降级（其 `-nt` 判据在 checkout 落盘序下不可靠·勿依赖） | coq93.yml job env `PBLD_AUTO_BASE: "1"`＋parallel_build.sh | `parallel_build: layers=L total=T compiled_or_invalidated=X skip=Y fail=0`——**Y 应≈T**（X=本波真变更件数） |
| **③coqchk 档案继承** | .vo sha256＝档案在册值 → coqchk 免列；vm_compute 证书 `-bytecode-compiler yes` | cw_attest.json（唯一合法写手＝attest_cast.py）＋parallel_chk.sh | `PCHK-ATTEST-SKIP: inherited=N sent_to_chk=M`——M 应=本波新验件数 |

**种子链闭环（三捷径的生命线·20261118 补齐）**：新模块 → 冷编取得认证（首验·设计行为）→ **炉绿后「Recycle new-module .vo into the seed chain」步自动回流**（furnace93_seed 补拷＋manifest 追加 v_sha256/vo_sha256 契约＋main93 沙箱回灌）→ 下一炉种子播种覆盖它 → 走捷径。**此环缺失＝永久首编循环**（run#107 实证：wave-2 件首编后不回流·每炉重新冷编）。

**档案保护（跳过捷径回潮事故条款·run#105 波）**：

- `cw_attest.json` ＝**认证层账本**（§6 认证层同款待遇）——**零自动触达**：autofix／机械化扫荡／任何整文件重写类工具一律排除在触达面外；唯一合法写手＝`attest_cast.py` 重铸器（绿炉产物）。
- **回潮检测一刀**：commit 后对关键账本（档案/manifest/白皮书）做计数断言＋tree_sha/hash 对表（stale-base assembled commit 静默抹杀检测器——本族病两次实锤）。
- **新件首编豁免**：新件每炉首编＝设计行为（首验取得认证），**第二炉起必须跳**——跳不回去即查种子回流步与档案（先查 SEED-RECYCLE 行·再查 manifest 条目·最后查档案）。

## §2 故障模式分类学（跨仓通用）

| 模式 | 症状 | 根因 | 修法 |
|---|---|---|---|
| checkout-red | `not our ref` / `couldn't find remote ref` | 镜像缺新 commit（API 铸后或他席推后镜像未同步） | 绕桥 fetch + update-ref + rerun |
| furnace-hang | coqc 0 CPU / 8MB 工作集 | **非挂**——rocqworker 子进程满负荷（巨常量单核重算） | 照常磨·采样须测 worker 子进程 |
| gate-false-positive | YAML schema 红 / 主炉不接单 | 注释续行顶格断 mapping | 修 YAML 缩进 |
| attest-stale | PBLD-COV-NO-VO（新件编译产物缺席） | 新模块无档案条目 | attest_cast 重铸＋种子回流步（SEED-RECYCLE） |
| vo-gap | Live-only 落岸 → vo 树缺源 | 双树不同步 | 补 vo 树源 + 册行 |
| runner-offline | API /actions/runners = offline | Listener 进程灭 | 双席重启（.env 钩变量须验） |
| yaml-syntax | schema 红 / jobs=0 | 注释续行顶格断 mapping | 修缩进 |
| w3-trigger | 大量 skip 失效 | W3 兜底周期触发 | 调周期（20→500）＋重类豁免 |
| netred-window | Connection reset / 超时 | hosts 钉过时 | 分面探活 + 重钉 |
| push-anomaly | non-commit object / needs force | API 铸对象本地不在 | PATCH ref 替代 push |
| merge-conflict | read-tree 基底错 → 静默回退 | parent/base 写错 | 重贴修复 blob |
| autofix-leg | autofix 修复带伤未落岸 | 宿主分支 checkout 失败 | 修 checkout 前置 |
| skip-regression（回潮） | 老认证件每炉冷编／Build 大面积 [L*] OK／PBLD-GEN 无基底＋mtime 失效 | 三类：①档案被整文件重写回退②PBLD_AUTO_BASE 未设③种子链断环（新件不回流） | ①恢复档案 blob＋工具排除清单＋计数断言②job env 补 AUTO_BASE=1③核 SEED-RECYCLE 行与 manifest |
| runner-crash-netred | job 无红步即 fail／后继步全 None | Listener .NET SocketException 995（NETRED 阵发必死·事件日志 0xe0434352 铁证） | 复活配方＋看门狗／Listener 升级 |
| serial-rerun | 复跑炉把在飞炉取消 | rerun＝新 run 实例·同触发并发级联 | **在跑炉落定再发下一个**（或排队治理器接管） |

## §3 Runner 管理

| 项 | 规则 |
|---|---|
| 双席架构 | clean 席（主认证·有钩）＋旧席（并存·须补钩对称） |
| 钩接线 | .env `ACTIONS_RUNNER_HOOK_JOB_STARTED` ＝钩脚本绝对路径 |
| 复活配方 | Start-Process Runner.Listener.exe run（WorkingDirectory 设 runner 根）→ API online/busy 复核 |
| 判据 | 「观察 ci 没拉起」九成 = runner offline（API /actions/runners status + WMI 进程探测两刀定位） |
| 重启生效 | .env 变更须 listener 重启才加载 |
| 挂死判据 | coqc **worker 子进程** 0 CPU + 8MB 工作集双采样 = 真 hang（包装壳 0 CPU 无意义） |
| NETRED 崩溃自灭 | Listener .NET 未处理异常（SocketException 995 网络中止路径）＝**NETRED 阵发必死**·事件日志 0xe0434352 铁证 | 治＝看门狗自动重启／Listener 升级；判据配方见事件日志过滤（Application Id=1026 + Runner 字样） |

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

**NETRED 切面**：git 面（github.com:443）与 API 面（api.github.com）健康独立——一面断切另一面·分面探活（curl --resolve 逐 IP）。API 铸 commit 的 author/committer 字段带尾部换行＝422 Unprocessable（subprocess 输出须 strip）；DNS 阵发期 getaddrinfo 失败＝curl --resolve 钉 IP 绕过。

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
