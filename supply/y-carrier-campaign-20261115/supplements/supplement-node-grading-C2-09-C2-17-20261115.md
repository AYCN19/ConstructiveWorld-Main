王小哥（y承载层线·曾栢源席）

# 分级增补卷 · Node Grading Supplement — C2.09 / C2.17（居留清偿对账 · residency clearance reconciliation）· 20261115

> **性质 · Nature**：《勘定-yE1落岸逐节点分级-20261113.md》的增补段，清偿其复审钩 R1（C2.09/C2.17 两节点部分）与 R5（wave-5 批次七件 γ 新件补分级）。本卷只作卷面判读，零编译、零树写；一切数字只从本机实测与源码直读机械归算，禁臆造。分级判据沿用底卷 :6 四档：**A**＝卡面命题全证·无条件；**B**＝只闭有限面/步进面/有理承载面或前提槽形；**C**＝只有工具/语句载体层；**D**＝条件化（关键对象 Section 变元）。
> A supplement to the landed-node grading volume of 20261113, clearing its review hooks R1 (nodes C2.09/C2.17) and R5 (the seven gamma files of the wave-5 batch). Ledger-only judgment: no compilation, no writes into the repository tree. Every number below is mechanically drawn from commands run and sources read on this machine during this session.

---

## Section 1. 第零步执行记录 · Zeroth-step execution record

1. **技能加载 · Skills**：`cw-deep-mining`（分级禁降档＋墙判定附复审条件）、`cw-tail-supply`（语句逐字铁律＋静态判读探针仲裁律）、`cw-ci-sop`（注释卫生＋诚实登记）三件正本加载成功（Skill 工具实测返回全文）。
2. **卡库检索 · Card search**：六关键词 `y-c2-gap-and-e1-outsource-20261108` / `paper-y-series-vs-a-20261108` / `certification-and-gates-iron-laws` / `red-line-law-path-a` / `coq-rocq-pitfall-precedents` / `deep-mining-methodology` 在随包 `techdocs/` 六文件内容中逐词 grep 零命中；各词在包工作流脚本 `wf-y-carrier-zby-20261115.dwf.ts` 中各登记引用 1 次（`grep -o | sort | uniq -c` 实测各 1）。包内 `40_skills/` 载四技能文件（与本侧三件同源，另含 `coq-toy-replacement`）。按随包纪律不停工，纪律内容以技能正本与底卷 §0、§8 承接。
3. **底卷对读 · Base volume**：`techdocs/勘定-yE1落岸逐节点分级-20261113.md`（220 行全读）＋`勘形卷模板-SL3形.md`（节构扫读）＋`判读-SL3勘形回执-20261114.md`（46 行全读，验证面纪律借鉴）。底卷 R1/R5 钩原文见底卷 :197 与 :201。

## Section 2. 盘面对表 · Disk state and two-directory reconciliation

实测命令：`ls | wc -l`、`diff <(ls Live...) <(ls root...)`、`md5sum` 逐件、`git rev-parse --short HEAD`、`git log --oneline --all`。

| item（English） | Live tree（92 files） | root tree（136 .v files） | verdict |
|---|---|---|---|
| 目录计数 · directory count | 92 个 .v | 136 个 .v ＋ MANIFEST.json ＋ README.md ＝ 138 | 与底卷 §1.4 口径咬合（任务书「136 件」指 .v 数） |
| 16ca669 三改件 · three modified files | GaC2_09_DenomZeroSet.v（282 行，md5 `c9e49ea2`）/ GaC2_09_DenomZeroSet_d.v（304 行，md5 `2e5d90e5`）/ GaC2_17_StripVerticalAsm.v（238 行，md5 `c2c93db9`） | 同名件 313 / 304 / 368 行，md5 `dc190455` / `4c45874f` / `aa65800c` | **root≠Live 双树分岔确证**（修正 H：居留落岸在仓库根目录，非 Live 树） |
| kit 四件对照 · four kit files | GaC2_09_DenomZeroSet_a/b/c.v ＋ GaC2_17_StripVerticalAsm_cert.v | 同名件 | **md5 全 SAME**（逐件 `md5sum` 对表） |
| wave-5 七新件 · seven new files | 不存在 · absent | GaC2_09_DenomZeroSet_e/f/g/h/i/j.v（246/383/235/368/299/354 行）＋ GaC2_17_StripVerticalAsm_a.v（322 行） | 仅 root 在盘 |
| 邻件对照 · neighbor files | GaC2_16_ZetaVerticalBound.v、GaC2_18_ZetaDerivBound.v、GaC2_07_DirichletTestAbel.v、GaC2_10_EtaContinuation.v | 同名件 | **md5 全 SAME**：此次落岸内容触面严格限于两靶节点 |
| 版本态 · version state | HEAD ＝ `8e70342`（2026-11-15，单提交全树导入） | 同 | **16ca669 非本仓对象**（`git cat-file -t 16ca669` ＝ fatal）；其内容以盘面现势为凭（修正 H 口径） |

## Section 3. 节点 C2.09 定级 · Node C2.09 graded: B → **A**

### 3.1 名册四条 · The four roster statements（底卷 :89 旧判「2/4」→ 本判「4/4」）

| # | roster statement（卡面） | 落岸位与证据锚 · landed anchor | 状态 |
|---|---|---|---|
| (a) | `denom_zero_real_dir`（实向·零周期性依赖） | `y_e1_gamma_nodes/GaC2_09_DenomZeroSet.v:191-272`，完整证明体 81 行，`Qed.` :272 | 已证 · proved |
| (b) | `denom_zero_imag_char_holds`（虚向 2π 格见证·sigT 形） | stem `:295-299` `Proof. exact e09_lattice_witness. Defined.`；正本 `GaC2_09_DenomZeroSet_g.v:81-168` 完整构造性证明体（共轭归约 :137-165 → `e09_grid_pin` 提取 k :166 → `Defined.` :168） | 已证 · proved |
| (c) | `denom_first_order_holds`（局部一阶余项·常数 14(ln2)²） | stem `:307-313` `Proof. exact f09_first_order. Defined.`；正本 `GaC2_09_DenomZeroSet_j.v:73-354` 完整证明体 281 行（Bishop 序展开 :80 → 前提见证 1/36 :87 → 逐点引擎 `e09_pointwise_bnd` :243-245 → Q 层算术收口，`Qed.` :354） | 已证 · proved |
| (d) | `zero_set_membership`（s_at k 在 Re s＝1 线） | stem `:277-289`，直接代入证明，`Qed.` :289 | 已证 · proved |

### 3.2 机检账 · Machine scans（本卷实测命令与输出）

- 禁词扫描 `grep -n -E "Admitted|^\s*Axiom|admit\.|Abort|^\s*Parameter|^\s*Conjecture|Hypothesis|excluded_middle|Classical"` 对 C2.09 家族 11 件：**唯一命中**＝`_a.v:26` 头注自述句「no Hypothesis」（非语句面命中）。
- Section 扫描 `grep -n -E "^Section|^Variable|^Context"` 对家族 11 件：**零命中**（exit 1）。
- 语句闭合对账（逐件 `grep -n` 实测）：stem 13 语句 / 13 闭合（11 `Qed.` 含 :275 同行闭合＋2 `Defined.` :299/:313）；_e 8/8；_f 5/5；_g 2/2（`Defined.` :168）；_h 9/9；_i 3/3；_j 3/3。**家族合计 43 语句 / 43 闭合**。
- 卡面语句形对勘（`drafts_C2.md` 稿二 :719-739 直读）：(b) 落岸形 `sigT (fun k : Z => real_eq (real_mult t d09_ln2) (d09_two_pi k))` 与稿形 `{ k : Z & t·ln2 ＝ 2π·k }` 同构；(a)(d) 与稿形逐因子咬合。π 承载 `d09_two_pi k :＝ 2·d09_pi_times k`（`_b.v:112`）、`d09_ln2 :＝ cw_log 2 d09_two_pos`（`_b.v:148`），即卡面义务 L11/L12 的登记具体化位。

### 3.3 登记披露（不降档理由 · registered disclosures, non-downgrading）

1. **(c) Bishop 序偏差**：稿形谓词位 `real_le`，落岸形 `real_le_b`（Bishop 序）——stem Notes :29-38 与 `_h/_i/_j` 三件头注均披露「registered bishop_ordinal_deviation」；卡册复审条件段（drafts_C2.md:1313 ①「C2.09 周期性（Bishop 系 R4）」）在卡面层预登记该复审位。披露链完整。
2. **符号勘误**：稿 :735 形 `− ln2(s−1)`，落岸形 `＋ ln2(s−1)`（stem :309-310）。一阶展开 `2^{1−s}−1 ≈ −ln2·(s−1)` 的余项定义为 `2^{1−s}−1−(−ln2(s−1))`，`＋` 形为数学正形；披露「draft_sign_typo」在 `_h/_i/_j` 头注与 stem Notes 在卷。
3. **局部盘具体化**：稿形抽象小半径 r，落岸形钉 `|s−1|² ≤ 3/4`（常数显式 14(ln2)²，义务 L12 放电）。底卷 A 档先例 C2.06 同样含登记化开口仍判 A（底卷 :177），本件同口径。
4. **Section 变元具体化**：稿形 Section＋Variable 形，落岸零 Section，`s_at k :＝ 1−2πk/ln2`、`c_m1 :＝ −1`、`ln2 :＝ d09_ln2`（stem Notes :36-38），系卡面义务清单自定工序，非降档要素（底卷 C2.06 判例明文允许正常参数，本件连参数位亦零）。

### 3.4 残留开口（诚实登记 · residual openings）

- **反向咬合未铸形**：卡面验收②（drafts_C2.md 稿四）「1−2^{1−s}＝0 ⇔ s＝1−2πik/ln2」的双向中，正向（零点→格点）由 (a)＋(b) 复合已证；反向（格点→零点）的原料 `e09_exp_opp_two_pi`（exp(−i·2πk)＝1）已在 `_f.v:247-256` 全证，但「denom(s_at k)＝0」未铸成具名合成语句（`s_at` 全家族 grep 仅 stem 在用）。名册四条本身不受影响。
- **`_g` 重复导入块**：`_g.v:42-58` 与 `:61-79` 两段 Require/Import 逐行重复（幂等重申，非语义问题）；备考。
- **`_d` 改件 diff 特征**：root 对 Live 全 diff 仅 2 行头注措辞（「to be cast there」→「are cast in the consolidating stem」），语句面零变更。
- **PA 闭性未独立复跑**：零编译纪律下 `Print Assumptions` 与 coqchk 闭性未独立验证，照底卷 :176 口径「照登不升格」。

**判级：A**（卡面四条全证·无条件·零 Section·零 Admitted/Axiom；披露项全部在卷且不触语句本体）。

## Section 4. 节点 C2.17 定级 · Node C2.17 graded: **B 维持**（B 内晋升 · within-B promotion）

### 4.1 三具名载体居留定理 · Three residence theorems（root 版新增，Live 版无）

| # | residence theorem | 证据锚 | 证明体 | 额外前提槽 · extra premise slots |
|---|---|---|---|---|
| (a) | `zeta_strip_uniform_holds` | stem `:275-330`，`Qed.` :330 | 实质链 46 行：η 模上界 `c17_eta_cap`（经载体自身 N＝0 面）:286-287 → 逆元代数 `c17_inv_le_sq` :308-310 → 单调链 `c17_mono_final` :322-327 → 目标等式 `c17_target_eq` :328-329 | **Hdlb**（:279-281）：∀s, Re s ≤ 1−δ → `denom_nz (sq (two_d_sub δ)) s`；文件自注 :245-246「the denominator corridor is the C2-08 modulus-algebra route slot」，即卡面路线指名的 C2.08 分母下界消费位未放电 |
| (b) | `zeta_vert_bound_disj_holds` | stem `:334-346`，`Qed.` :346 | 4 行分支装配（`destruct Hsplit; exact existT`），零新分析 | **Hmid / Hnear / Hsplit**（:336-339）：C2.16 两带面逐点槽＋带分点槽；文件自注 :332-333「the two mother band faces as the guarded slot carriers」 |
| (c) | `zeta_strip_cover_holds` | stem `:351-369`，`Qed.` :369 | 7 行逐点提升 | **Hsplit / Hmid / Hnear**（:354-360）同上（逐点版） |

### 4.2 定级理由 · grading rationale

- 三居留定理均为**前提槽形**（B 档判据本体）：载体 `zeta_strip_uniform`（:218-227）与 `zeta_strip_cover`（:234-240）仍为 Definition 语句载体形，居留定理证明其在槽前提下的居留性；槽位恰为母链内容（C2.08 分母下界、C2.16 两带面）。底卷 :95 旧判的两主命题「无证明体」状态解除，但解除形带槽——按底卷 :6 判据归 B，不达 A 的「无条件」要件。
- **B 内晋升如实记录**：旧态＝载体零体；新态＝居留定理在卷＋支撑件 `_a.v` 七引理全闭合（`grep` 实测 7 语句 7 `Qed.`、零 Admitted/Axiom；`c17_eta_cap :99-140` 为实质构造性证明）。C2.17 的 B 与底卷 :95 的 B 不可混写：本判为「居留定理＋前提槽」形态的 B。
- 支撑件 Require 闭包核：`GaC2_02_AbsConvTailBound_a.v` 与 `GaC2_01_DirichletPartialSum.v`（stem 体内 `:291/:295` 限定名消费）在仓内路径 `attn/kbgamma_20261108/seg_C2/`（存档 33 节点域·`find` 实测），非零文件缺口；随包闭包内可解析。
- Hsplit 槽备注：形如 `Or (Re s < 1) (1 ≤ Re s)` 的线分点，树内有 `real_weak_trich` 先例（stem 09 :117 在用），存在内部放电候选，但落岸形取前提槽位，按现盘判。
- FE 缺口诚实边界（头注 :103-111）原文维持；头注 :90-97「Proof-body state」段未提居留定理节（文档滞后型·非内容红·照底卷 :184 口径登记）；MANIFEST `statement_face_only` 旗标出入（底卷 §7.3/R10）未变，仍候勘。

**判级：B**（居留定理三具·前提槽形；槽位清单：Hdlb×1、Hmid/Hnear×2、Hsplit×1）。

## Section 5. 合并账与 headline · Merged account and headline

机械归算（底卷 §0.3 汇判规则 · 只数 A 级节点为分子 · 85＝名册分母）：

| line（English） | A | B | C | D | subtotal |
|---|---|---|---|---|---|
| C1（存档 11/6/0/0） | 11 | 6 | 0 | 0 | 17 |
| C2（原 3/12/1/0；C2.09 B→A） | **4**（C2.01/03/06/**09**） | **11** | 1（C2.18） | 0 | 16 |
| C3（存档 1/9/1/2；此次落岸内容零变动） | 1 | 9 | 1 | 2 | 13 |
| **合计 · total** | **16** | **26** | **2** | **2** | **46** ✓ |

**headline：16/85（18.8%）**（旧账 15/85；B 27→26、A 15→16；节点总数 46 不变：C2.09/C2.17 均为已入账节点，此次落岸内容不新增节点）。

### 与任务书预期账的出入（如实升格 · divergence from the anticipated account, flagged）

任务书预期「15/85→17/85 候账」，即 C2.09 与 C2.17 双双晋 A。本判实测：**C2.09 晋 A 成立，C2.17 维持 B**。三居留定理虽落岸且支撑链全闭合，但其语句面各带 1-3 个额外语义槽（Hdlb/Hmid/Hnear/Hsplit，见 §4.1 表），恰为卡面路线指名而未放电的母链消费位；按底卷 :6 判据「A＝无条件」不达。禁凑绿纪律（底卷 §0.2 亲读卡 2「缺证如实缺证」）优先于预期账。17/85 的到达条件＝Hdlb/Hmid/Hnear 三槽放电（见 §6 新钩 NH1）。

## Section 6. 复审钩状态与新钩 · Review-hook status and new hooks

| hook | status（English） |
|---|---|
| R1（C2.09 前置面落岸） | **清偿**：B→A（§3） |
| R1（C2.17 三条晋升） | **部分清偿**：晋升形态＝居留定理·前提槽形→B 维持（§4）；「晋升 Lemma 直证形」钩保持开放 |
| R1（C2.18 两条清偿） | **未触发**：`GaC2_18_ZetaDerivBound.v` root＝Live md5 全同，此次落岸内容未触碰，R1 对 C2.18 仍开放 |
| R5（七件补分级） | **清偿**：C2.09 六件＋C2.17 `_a` 已入 §3/§4 判读（kit 全证·闭合全齐） |
| R5（MANIFEST 换版） | **未清偿**：`counts.files` 仍 43、sfo 仍 1（实测 `grep`），换版候权（本卷零树写不代办） |
| **NH1（新）** | Hdlb（C2.08 分母下界链）/Hmid/Hnear（C2.16 两带面载体晋升）任一放电 → C2.17 强制重估（B→A 唯一路径）；Hsplit 内部放电候选（`real_weak_trich` 先例在树） |
| **NH2（新）** | 卡面验收②反向腿（denom(s_at k)＝0）铸形 → C2.09 验收链全闭合复查 |
| **NH3（新）** | 本卷判读为纯卷面；独立编译＋PA 闭性＋coqchk 复验到货 → §3/§4 certStatus 域强制刷新（W-3 时戳纪律照底卷 §8 总钩） |

## Section 7. 限定与未跑面 · Limits and not-run face（诚实面 · honest scope）

1. **零编译**：本卷一切判读来自源码直读与文本机检（grep/diff/md5sum/ls/git），`Print Assumptions`、coqchk、编译五证均未运行；绿判四件套不适用本卷，语句闭合以源码 `Qed./Defined.` 词面为凭。
2. **16ca669 不可本仓解析**：本仓单提交 `8e70342`（浅导入），无该提交对象；其落岸内容以盘面 md5 分岔态（§2 表）为凭，未做逐 hunk 归因。
3. **双目录全量重对表未做**：底卷 §7.15 的 92 对 136 分岔重对表超出本卷靶面（两靶节点族内已逐件对表），全量对表仍开放。
4. **分级快照漂移核对**：底卷快照口径 186 件（HEAD `28e3270`）、收卷口径 230 件（`dd43497`）；本卷现势 228 件（92＋136 .v）——任务书「136 件」指 .v 数，与盘面咬合，无漂移触发升级通道。
5. 本卷无新立墙判词；§4.2 的槽位登记为检索记录与文件自注转录，不立「真墙/需突破」档（cw-deep-mining §1.5a W-1~W-6 自检：W-1 检索记录在卷＝§4.1 文件自注 + §6 NH1 槽位清单）。

判毕 2026-11-15（YCARRIER-02）· 数字只从本卷实测机械归算 · 零编译零树写
