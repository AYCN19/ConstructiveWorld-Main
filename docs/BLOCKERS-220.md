# 220 单文件版阻塞图谱（模块化拆分的依据）

> Historical planning record (the filename carries the version number 220, not a date; the as-of date 2026-09-08 is in the body below). Preserved verbatim for provenance; current certification facts live in README.md section 2.

单文件 `releases/CW_ConstructiveWorld_220.v`（129,396 行）截至 2026-09-08 的阻塞点：

| # | 位置 | 阻塞 | 模块级归属 | 模块化后状态 |
|---|---|---|---|---|
| 1 | L114786 | `sqrt_witness already exists`（顶层声明与基座吸收内容同名） | UpDebtSqrtAbs.v | **消解**（独立编译单元不拼接） |
| 2 | 同类隐患 8 件 | Z_thermo/boltzmann_dist_attn/boltzmann_factor/real_pow_pos/real_softmax_temp 等跨件同名 | EvictId/SigMigrate/DebtGibbsT/DebtDual/BudgetReal | **消解**（各自 .vo 命名空间） |
| 3 | L1021 起 | Q_scope 泄漏（219 尾部 Open Scope 影响追加文本，裸 0 解析为 Q） | StepKLM3（已补 nat_scope）；其余件编译时逐处一行修复 | 模块树逐一暴露、逐件修复 |
| 4 | 6MB 级编译 | harness 后台上下文 0 CPU 阻塞（交互终端正常，~40 分钟） | 基座/单文件 | 信任缓存绕开；基座终编留交互终端 |

## 教训（甄别工具链）
初轮 shell comm 甄别因 CRLF 残留 + locale 全体失敏报假零；Python 声明级终审（CR 清洗）才见真相——9 件已收录（含 GRPO/Extras 改名吸收）。见 已合并存档/README-甄别报告.md。

## 扩展层交付附录（2026-09-08）
- CW220_Extensions.v 四关全绿：15,254 行 / Qed 出现总数 553（`^s*Qed.` 513=行首 512+缩进 1）/ Defined 11 / SHA256 14d4f48a...cee6 / coqchk 通过
- v3 生成器 4 个结构性 bug（后续重生成时必须回写）：①多行 Extraction 探针被提头截断；②消费 Import 注在单元尾而非头；③漏建 Module Constitution 包裹；④单元间互撞重名检测缺失（tid/nle/leb 前置机三重名 → UpRecast/UpCLQuery 需 ISO 隔离）
- 其他装配级修复：Q_scope 泄漏包裹（UpMinP/PredRelax）、S/O 遮蔽（UpPLA Section + Local Notation）、EnhancedMod 劫持（EvictId 13 条别名前缀化）、Constitution.uc_qle_bool_false_inv 真坏证明重写（-vos 探测不到该类，全量才现形）
- v3 原始态备份：attn/_CW220_Extensions.v.bak_v3

## 大文件编译冻结机制画像（2026-09-08 攻坚席破壁，主会话归档）
- **根因**：coqc 默认异步证明机制（async proof workers）在大文件累积阈值处死锁——冻结跟随处理前沿（-vos 于 ~5.85MB / L112098 real_lt_le_bridge 实测），线程 Wait=EventPairLow（worker 交接等待），与文件内容具体命令无关（切片夹逼实证）。
- **CPU 计数器失真**：本机 coqc 产出 5.77MB 日志同时 bash time user=0.000s——0 CPU 不构成挂死证据；**活体判据 = `-time-file` 时间日志的持续推进**。
- **解药**：`-async-proofs off`（内联证明；切片 A 同挂点完整越墙实证）。大文件编译一律加此旗标。
- **适用**：单文件版全量、基座源码终编、一切 >1MB 级 .v；小文件（≤100KB）未复现。

## 补充：大文件 -vos 确定性冻结（2026-09-08 定罪）
冻结元凶 = `-vos` 模式本身（非内容/非平台/非上下文）：绝对字符位 ~5,850,9xx 处确定性冻结（五连证），全量模式免疫。**单文件 220 全量编译不用 -vos，直接 `coqc -async-proofs off`**。详见经验卡 E-STAGING-WangWW-runcoqc泛化 终版机制节。

## 全树 coqchk 认证态刷新（2026-09-08 实测）
**34/34 全过、0 败**（9.0.1 内核，`coqchk -Q . "" <模块名>` 逐件独立调用，判定 = 日志含 "Modules were successfully checked" 且退出码 0）。基座 CW_ConstructiveWorld_219 与全部新件（含 UpKVDrift/UpQKBound/UpLoeb/UpLoebD2/UpRefuted 五件）均实测 PASS。据此，"28 模块态 coqchk 29 过 0 败、5 新件认证在补"的旧口径**升级为全量认证态**：现存 .vo 面无任何"认证在补"尾项。逐模块结果/日志字节/时间戳见 `docs/coqchk认证总表-20260908.md`；注：UpIDL 源码在树但无 .vo，不占 .vo 认证面（34 .vo = 全树 .vo 面）。
