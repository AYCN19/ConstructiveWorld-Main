# y（γ）项目交接书（20261108·王小雪→曾栢源·全权委托移交）

> 用户令（20261108）：y 项目全权委托曾栢源推进；王小雪转交接＋善后位。本卷=交接正典：现势/裁定/护栏/配方/开口项全在此，接任先读。

## 一、交接时点现势（冻结态）

- **口径**：C1 17/17＋C2 5/18＋C3 11/28（条件化计）＝**33/85**（王小哥考古更正后·基态卷更正落笔随移交转曾栢源）。
- **波 2 冻结态**（工作流 dwfrun-2a8e8c7c 停飞时）：Z03＝GREEN（**条件化**·槽形装配·`GaC3_Z03_NonzeroLine.v` 40KB·四闸过·字面 ζ 承载候 GaC2_Iface_Eta 转正）；**C2.06＝GREEN**（一轮过证·`GaC2_06_AltMonoFace.v`）；Z04/Z05＝BLOCKED（候 C2.3/C2.4·前航 Z04 中间态三件 `GaC3_Z04_ZetaMainPart{,_b,_cert}` 同槽形隔离在树·不入认证面）；P08＝在铸中间态（`GaC3_P08_PerronCutoff{,_b,_cert}` .vo 已落·**未消费 P03 ML 面**·按 §六点3 二选一处置）；P06＝候 Z04。C2.07/08/09/10/Iface_Eta 未启。
- **认领面移交**：Z03/Z04/Z05/P06/P08＋C2.3 六件（06/07/08/09/10/Iface_Eta）＝王小雪在铸→**全部转曾栢源**（王小哥 13:46Z 已确认 C2.3/P08 归王小雪线·现随全权委托转曾栢源；外派包只留文献复审钩）。
- **他席面（不碰）**：G-MU-01＝曾栢源（已认领）；镜像同步＝王小哥值守席；Set PR #30＝AYCN19（CI 绿可合·归其评审线）。

## 二、护栏与裁定（全约束·接任必遵）

1. **born-clean 铁律**：承载位禁 Prop（informative 改载=Id (eqb…) true 载体反射＋bridge elim·正样本 `GaC3_P02_LineIntegralAlg.v` W2 认证形）；禁语句面凑绿；禁 Admitted/Axiom/Parameter。
2. **注释规范卡**（M波·两段式头注五字段句点形＋四域英化＋承认式词面注释零容忍＋CJK 零）——闸=`tools/annotation_gate.py` 逐件 clean 收工。
3. **C2.10 深水面护栏**（王小哥 14:06Z）：卡面 (b) 解析承载形（全纯谓词/局部幂级数）γ 段缺机器（三档=需突破）——本轮不定形则 (b) 按 P04 先例诚实登记深水面（铸 (a) 连续面等可得部分）·**禁前提槽偷渡解析性**（四闸查不出·人工判）。
4. **P08 依赖律**（spec §6 附记②·14:52Z）：需 P03/P04-06 面即直接 Require（树内认证形在盘）·波号加深·回执登记——禁重抄 ML 估计（复核员旧「禁 Require P03」作废·以 spec 为准）。现形疑 Q 级 Z01 级数尾路线·须补 Require 或 notes 论证（禁静默绕开）。
5. **C2.09 草稿头冲突**：drafts_C2.md:713 Require 含 GaC2_08 与 W1 无前置冲突——铸序 06→07→08→09 保证 08 在前：真用到保留（波号加深）·用不到删行（照抄编译红）。
6. **文献口径三钩**（王小哥 14:27Z·证据 `attn/_ylit_work_20261108/r3_hooks/H1-H3/`）：H-1 dVp 常数双档（BTY 4.896 arXiv 预印本＋MTY 5.558691 已刊最优·禁「MTY 已发表最优」单档）；H-2 vdC A 过程有 Lean 先例（rwst 0 sorry＋TomasOrtega 显式 ζ Weyl）·**唯 V02 B 过程显式常数未见先例**（V01 References retrofit 排队中）；H-3 两件准 RH 声明（Family 003/AxiomMath）全链缺证——不引为已验定理。
7. **V03/Z03 性质**：GREEN（条件化）——头注自述前提族（L-V03-A..D·zeta1 节变元）；基态卷计已闭时标「条件化」。
8. **P04/P05 口径**（基态卷更正时）：「步进承载面闭合·深水面（一般全纯 Cauchy–Goursat/积分公式）未铸」——不按 ✅ 直译。
9. **代际锚与 boot 配方**：附卷A 缓存=Windows Platform 产（曾栢源 Windows 侧可载·本机 mac 曾撕裂）；mac/异源机配方=Main@0ef0c40f（CI 绿炉 #9）的 S01–S14 十四件＋abl_Pr 六件（core_01/enum_02/euclid_03/lcmdecomp_04/lcm_eq）＋HansonLcm/Hanson3Pow 本机重编为 -Q 根（`tools/runner.py chain` 直用）。
10. **自验工具包**：分支 sandbox/y-selfverify@420d15b4（六道链验收·accept/<节点>.json＋判据行＋ledger md5 格式）——王小哥十点警示（-norec 判据/P04 探针排除/温控/清单校验）见协调台 14:52Z 帖。
11. **gate7**：Main 仓已移植（main `6be57c09`·scripts/gates/）——Main 专属 baseline 未生成（两案候排程：甲=Windows delta 炉侧实跑·乙=本机全树编）；Set baseline 不直用。
12. **镜像桥纪律**：Main/Set 两仓桥在役（PR 临时 ref 不入镜像→PR 认证跑结构性红＝常态·push 认证为准；推送后知会协调台候值守席同步窗 15–30 分钟）。

## 三、工艺与基建（移交可用）

- **tools/runner.py**：chain（coqdep 拓扑序编译）/furnace（coqchk -o -bytecode-compiler yes 全闭包炉）/pa（Print Assumptions 逐定理）/md5c1·md5c3/plan 五命令·结构化 JSON·cpu_guard 全包裹。
- **tools/annotation_gate.py**：规范卡法条铸闸（五字段/承认式/战役词面/日期戳/CJK 位态）。
- **craft 模板**：Prop→Set 改载（W2 认证形）·铸造席四闸环（编译链→炉→PA→注释闸）·三泳道并行结构（脚本在 `.zcode/workflow-drafts/y-W3-波-2*.dwf.ts`）。
- **workorders/**：工单 v1＋详版 v2（随卷）。

## 四、开口项（接任后动作面）

1. C2.3 余件：C2.07→C2.08→C2.09→C2.10（护栏 3/5 在身）→GaC2_Iface_Eta→Z03 字面承载转正（小面 retrofit）。
2. P08 处置：补 Require P03 或论证 Q 级路线（二选一·见护栏 4）。
3. C2.4（C2.11-18 八节点）：勘形候王小哥方用户裁·动前对表。
4. 波 3 面：V04-V06/P09/P10-P12（roster pre 链驱动）。
5. 基态卷更正落笔（33/85·条件化标注·P04/P05 口径）——随移交转曾栢源。
6. W5 落装（35 件子集进 Live 注册面＋gate7 gate 模式·baseline 就位后）＋W6 论文线（文献纪律见护栏 6）。
7. V01 References retrofit（H-2 两先例入引·注释级·随下批 PR·E949 换代重炉）。

## 五、证据链指针

- receipts/（11 卷：W1/W2/W3-wave1/PR-retrofit/W3cast/冲刺总报/gate4 json/L13×2/md5 换代/roster status）。
- logs_curated/（131 件·炉/PA 判据行裁尾）。
- 全量 logs 89MB 未随卷（本机留档·需即知会王小雪定向投递）。
- 认证语料正本（62 件 retrofit 终形）＝本仓 main `attn/kbgamma_20261108/`（PR #1 已并）。

——王小雪 交出（20261108·全权委托移交·用户令）
