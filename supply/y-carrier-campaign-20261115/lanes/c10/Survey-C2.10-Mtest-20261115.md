# 勘形卷 · Survey Volume: C2.10 Weierstrass M-test double series · 20261115

> **本卷性质 / Nature**: C2.10 节点（GaC2_10_EtaContinuation.v，321 行）勘形与可及段施工卷：12 面逐一定档＋可及段证明件（GaC2_10_MtestGeomTail.v）。照任务书 GD-20261115-YCARRIER-01 §一 C2.10 行与 techdocs/勘形卷模板-SL3形.md 六节形铸；零树写（施工只落本席交付目录）；main 零触碰；git 只读（克隆 status porcelain=空，本卷 §0 首手实测）。
> **单号 / Ticket**: GD-20261115-YCARRIER-01（四缺口勘形＋可及施工）C2.10 行（Weierstrass 级数面）。
> **判点 / Verdict anchor**: 基点 8e70342（20261115，任务书硬锚）；判定时点 2026-11-15；一切判词带时戳（W-3 纪律）。
> **施工件 / Construction piece**: `GaC2_10_MtestGeomTail.v`（同目录，四关验证记录见 §5）。

---

## §0 第零步三道证据（Zeroth-step evidence）

| 道 | 执行 | 结果（本侧首手实测） |
|---|---|---|
| ① 载技能 | Skill 工具载入三件 | **cw-deep-mining**（v1.0 全文在卷：§1.5 三档禁降档＋§1.5a 真墙判词红线 W-1~W-6＋§1.2 复审条件＋§1.3 杠杆先行）；**cw-tail-supply**（v1.2 全文在卷：§1 流水线＋§12 消费位洗波五律）；**cw-ci-sop**（v2.8 全文在卷：§R2 温控 v4 三机械闸＋§1 红线律 v2.5＋§1·B GAPASUME＋§1·H 两向门选律）。三件均在册全载，无缺载 |
| ② 卡库检索 | 在 techdocs（会话记忆本侧无卡库目录）grep 六关键词：`y-c2-gap-and-e1-outsource-20261108`、`paper-y-series-vs-a-20261108`、`certification-and-gates-iron-laws`、`red-line-law-path-a`、`coq-rocq-pitfall-precedents`、`deep-mining-methodology` | **六关键词全部零命中**（`for kw in ...; do grep -rn "$kw" .; done` 逐词实测输出为空），按随包纪律不停工，纪律内容以三技能正本＋勘定卷 §0＋§8 承接；零命中如实登记（E-GHOSTCONST 纪律） |
| ③ 技术文档 | techdocs 三件全读：`勘定-yE1落岸逐节点分级-20261113.md`（220 行全读）、`勘形卷模板-SL3形.md`（266 行全读）、`判读-SL3勘形回执-20261114.md`（47 行全读）＋靶件 `GaC2_10_EtaContinuation.v`（321 行全读）＋`GaC2_10_EtaContinuation_cert.v`（85 行全读）＋闭包杠杆件实读 | 全部在卷；闭包 39 件 Require 递归追踪全解析（§3）；关键杠杆件逐件实读：CxRealPairCore（334 行）、GaC1_15（221 行全读）、GaC1_14（语句面全录）、GaC2_01（316 行语句面全录）、GaC2_02_c（312 行语句面全录）、GaC2_07（关键段 :32-355）、GaC2_09_b（载体系与 d09_opp_opp :69）、S02 载体底形（:397-480/:2301-2325） |

**判定时点与基建状态（反陈旧锚律）**: 2026-11-15，克隆 `zby_ycarrier_20261115/ConstructiveWorld-Main` HEAD=`8e70342`（detached，`git log --oneline -3` 首行=8e70342 fix: restore gate4 comment fixes...），`git status --porcelain`=空（零树写首手实测）。基建现势：S01-S14 主线链＋kbgamma seg_C1/seg_C2 链＋y_e1_gamma_nodes 落岸件全部在位；**C2.08（GaC2_08_EtaZetaRelation）全树零文件**（`find . -name "GaC2_08*"` 零输出，首手实测），(a) 面上游件缺位维持。与勘定卷（20261113 快照 28e3270）相比靶件本体零漂移（同字节内容面，勘定卷 §2 行 4 分级 B 级的判定材料未变）。

---

## §1 链上现势：12 面逐一定档（Current state: the 12 faces graded）

12 面＝机群五引理＋语句载体七名（勘定卷 §2 行 4 口径：GaC2_10_EtaContinuation.v:174-321 七载体＋机群五引理）。定档档位：**已证**（Qed·机检级）／**载体**（Definition 语句面·无证明债·消费位注明）／**需突破**（缺件可命名·附突破方向）／**真墙**（0 项·见 §4）。

| # | Face | 位置 | 现态 | 定档 | 证据锚（首手） |
|---|---|---|---|---|---|
| 1 | `d10_eta_sgn_one` | :177-178 | Qed | **已证**（机群·reflexivity 面） | `Proof. apply c_eq_refl. Qed.` 实读；本次闭包编译复验（§5 log） |
| 2 | `d10_eta_part_zero` | :180-181 | Qed | **已证**（机群） | 同上 |
| 3 | `d10_cpow_zero` | :183-184 | Qed | **已证**（机群） | 同上 |
| 4 | `denom_sq_pos` | :226-233 | Qed | **已证**（实质·real_lt_trans 链） | 证明体 `exact (real_lt_trans ... Hep Hd)` 实读 |
| 5 | `d10_denom_is_d09` | :237-239 | Qed | **已证**（名实键·定义等） | c_eq_refl；d09_denom 定义面 :155-156 同构实证 |
| 6 | `d10_closed_disk` | :174-175 | Definition | **载体**（(b) 行磁盘谓词·本体无证明债） | Set 承载 real_le 平方房形；消费位在 (b) 行 Hetad/Hnz/Hval |
| 7 | `denom_nz` | :221-222 | Definition | **载体**（sketch 行逐字；eps_lb 显式首参=GAPASUME 放电位） | 消费位已闭：denom_sq_pos（#4）＋名实键（#5）＋cert Band 2 样带 |
| 8 | `d10_eta_conv` | :193-198 | Definition | **载体**（诚实前提接口·C2.07 消费槽） | sigT 见证形：「显式交替尾项模·两倍首漏项」；供给侧债在 GaC2_07（eta_conv_uniform 载体态） |
| 9 | `d10_zeta_conv` | :206-213 | Definition | **载体**（诚实前提接口·C2.02+C2.08 消费槽） | sigT 四层形：值＋阈值 M0＋尾界 B＋正性 |
| 10 | `zeta_tilde_agree`（(a) 面） | :269-274 | Definition 载体·未证 | **需突破**（缺件可命名＝C2.08 eta-zeta 极限恒等行；GaC2_08_EtaZetaRelation 全树零文件） | :80-84 头注自陈＋find 零输出（§0）；证明路线已注册（消费 C2.08 行） |
| 11 | `zeta_tilde_analytic`（(b) 面） | :284-307 | Definition 载体·未证 | **需突破**（Weierstrass 双级数构造地＝卡面突破档本体；距摊分解见 §2） | :281-283 头注自陈「the Weierstrass double series constructive land, zero in-tree precedent」·卡面预判带时戳引用（W-3）；本卷勘定其供给半边已在树闭（§2/§3：卡面「零先例」判词按反陈旧锚已部分过期·如实勘正） |
| 12 | `zeta_tilde_unif_bound`（(c) 面） | :314-321 | Definition 载体·未证 | **需突破**（受阻于 GaC2_07 eta_conv_uniform 载体态·在树未证） | :309-313 头注自陈消费 C2.07 均匀尾项；GaC2_07:379-386 eta_conv_uniform=Definition 载体实读（在树未晋升） |

**伴生载体（非 12 面计）**: `d10_npos`（:137·nat_real_pos 直装）、`eta_s`（:201·投影）、`zeta_tilde`（:248-254·无除法商实现）、`w_one`/`w_sq`（:259-263·权重走廊），全部 Definition，消费位见各行。证书面 `_cert.v` 六引理全 vm_compute 闭（Band 1 走廊 sigma0=1→2、sigma0=1/2→5/2；Band 2 分母下界样带 s=1/2、s=3/2；85 行实读）。

---

## §2 量化距离（Quantified distance）

**反向提取（链上今日隐含水平·全部首手实读）**:

| 链上位 | 已闭水平 | 位置 |
|---|---|---|
| 实标量几何尾部 | **全闭**：rtsum/rtail 链（ge0/zero/chain_add/chain/mono）＋r_geom_den_pos＋r_m1sig_pos/dyadic＋r_tail_dyadic＋r_gsum_lt_geom，15 Qed／0 Admitted | GaC2_02_AbsConvTailBound_c.v:69-283（312 行语句面全录） |
| 级数 Cauchy 槽形 | GAPASUME 槽形全闭（tailbound 供给＋smallness 检索→tail_closed＋cauchy） | GaC1_15_PowSeriesConv.v:174-221（221 行全读） |
| 复数二元三角 | ε-余量二元形：‖u+v‖² < 2(‖u‖²+‖v‖²)+d（任意有理 d） | gaC1_14_norm_sq_pair_lt，GaC1_14_SeriesCauchy.v:368 |
| 点态↔Cauchy 桥 | pointwise_to_cauchy＋cauchy_to_pointwise_slack | GaC1_14:205/:275 |
| 复指数范数 | gaC1_16_norm_sq_exp＋strip | GaC1_16_CExpNorm.v:66/:106 |
| n^{-s} 范数面 | c_powq_norm_sq（平方房形） | GaC2_01:226 |
| ζ 部分和代数 | c_zeta_part_tail_eq＋c_tail_zero_le＋c_powq_plus_law | GaC2_01:205/:248/:266 |
| 符号奇偶 B=1 供给行 | abssum_alt_pair＋eta_sgn_bounded_pair（已证 Qed） | GaC2_07:199/:271 |
| 分母零带与证书 | denom_sq_pos＋d10_denom_is_d09＋d09 面族＋cert 两带 | GaC2_10:226-239＋GaC2_09_b＋_cert 六引理 |
| 复代数全域 | c_eq/mult/plus/conj/norm_sq_mul 等 24 引理全闭 | CxRealPairCore.v（334 行实读） |

**目标水平（(b) 面本体）**: 存在 R>0、磁盘 eta 族 Hetad、系数列 c_n、磁盘 nz 带 Hnz、值一致面 Hval、以及 d10_psum 的一致有理余量 Cauchy 尾（:284-307 载体逐字）。

**距离分解（缺件清单·逐件定价【外推·未校准】）**:

| 环 | 缺件 | 性质 | 定价【外推·未校准】 |
|---|---|---|---|
| 环1 | 复数 n-折线性三角 ‖Σt_k‖² ≤ (Σ‖t_k‖)²+d（实标量侧已闭·复列装配未铸；GaC2_07:68 明文点名该行为其 abel_tail 门件） | 工程缺件（桥件级） | 2-5 席时 |
| 环2 | eta 磁盘族 Hetad（(b) 行内嵌前提·其见证由 C2.07 放电），门在 GaC2_07 eta_conv_uniform 晋升 | 上游缺件传导 | 1-3 席时（供给侧落岸后） |
| 环3 | 系数列 c_n 构造（双级数本体：eta 列×几何分母列 Cauchy 积；log-幂界 (log n)^k/k! 经 S07 log＋GaC1_16 exp 范数） | 卡面突破核心（工程重件·非新数学：mathlib RadiusOfConvergence 路线已由 GaC1_15:32-36 对标登记·经典载体不转录） | 4-12 席时 |
| 环4 | 值一致面 Hval（zeta_tilde 在磁盘上=级数值），环1-3 落岸后装配 | 装配段 | 2-4 席时 |
| 环5 | (a) 面：门在 GaC2_08（零文件·上游行定价，非本节点债） | 上游缺件 | C2.08 行定价 |
| 环6 | (c) 面：门在 GaC2_07 eta_conv_uniform/abel_tail 晋升；晋升后仅余权重走廊算术（w_one/w_sq 经 GaC2_06 r_npow 面）＋见证逆元转移（c_inv_wit_correct） | 上游缺件传导＋轻装配 | 1-2 席时（供给落岸后） |

**距离小结**: 供给半边（实标量几何尾部）**今日已在树全闭**：卡面「零 in-tree 先例」判词按反陈旧锚律部分过期，勘正为「复数列装配与系数构造未铸·供给半边已闭」。余距离全部为工程缺件与上游传导，零新数学缺件判词维持（W-2 判据：无任何「原则性障碍」类依据；两类装配路线（n-折三角购入／望远镜+除法链）均在卷可行）。

---

## §3 杠杆清单（In-tree reusable piece inventory·勘形前置律）

| # | 杠杆件 | 位置 | 现态 | 本票用途 |
|---|---|---|---|---|
| 1 | CxRealPairCore 复代数 24 引理 | seg_C1/CxRealPairCore.v（334 行） | 全 Qed | 施工件 Section 1/2 的代数底盘 |
| 2 | c_plus_congr/c_mult_congr/c_opp_congr | CxRealPairExpLog.v:80/:99/:110 | 全 Qed | 同上（等式同余三件） |
| 3 | gaC1_14_norm_sq_pair_lt（ε-余量二元三角） | GaC1_14:368 | Qed | 环1 的二元基座（GaC2_07 abel_tri_pair_step 即其直装 :354） |
| 4 | GaC1_15 GAPASUME 槽形（rsum/tail_closed/cauchy） | GaC1_15:64-72/:193/:203 | 全 Qed | d10_mtest_unif_face 槽形模板（本件同构复刻） |
| 5 | GaC1_16 exp 范数 | GaC1_16:66/:106 | Qed | 环3 log-幂系数界 |
| 6 | c_powq_norm_sq＋c_zeta_part_tail_eq | GaC2_01:226/:266 | Qed | eta 列范数账 |
| 7 | GaC2_02_c 实标量几何尾部（15 Qed） | seg_C2/GaC2_02_AbsConvTailBound_c.v:69-283 | 全闭 | 环1/环3 供给半边（实标量侧直供） |
| 8 | GaC2_02_a c_of_real_wd＋nat_real_pos | GaC2_02_a:126/:（closed witness） | Qed | 施工件 sgn 桥引理＋零前提穿线 |
| 9 | GaC2_06 幂序机（r_npow_anti/tozero 等·勘定卷 A 级） | y_e1_gamma_nodes/GaC2_06_AltMonoFace.v | 全证 | 环6 权重走廊 |
| 10 | GaC2_07 符号列＋奇偶供给行＋alt_sign/eta_sgn_cx | GaC2_07:90-146/:199/:271 | 引理 Qed·载体另计 | 施工件 sgn 名实键（d10_mtest_sgn_is_eta_sgn_cx）＋环2 供位 |
| 11 | d09_opp_opp＋two_pow_1ms/d09_denom | GaC2_09_b:69/:153-156 | Qed | 施工件 opp_opp／(c) 面权逆 |
| 12 | c_inv_wit/c_inv_wit_correct | GaC2_01:309/:312 | Qed | (c) 面见证逆元转移 |
| 13 | GaC2_10 语句面自身＋cert 两带 | y_e1_gamma_nodes/GaC2_10_*.v | 5 Qed＋载体＋6 vm_compute | 本票基座 |
| 14 | GaC1_Iface_Cx Export 链（RB01 real_le_b 桥＋G1_PYTH＋GaC1_17） | seg_C1/GaC1_Iface_Cx.v:48-55 | 链全解析 | Require 单点全量可见性 |

---

## §4 三档判定（Three-tier verdicts·证据义务逐档递增·禁降档）

| 分项 | 档 | 证据义务履行 |
|---|---|---|
| M-test 机群面（施工件 Section 1-2：签名机＋望远镜恒等式＋范数增长） | **可及→已施工** | 本卷 §5 四关验证记录在卷 |
| (b) 面本体（双级数装配：环1-4） | **需突破**（禁降档·不升真墙） | **W-1** 杠杆全量盘点（§3 十四件·三源：闭包递归追踪＋逐件实读＋勘定卷/SL3 卷交叉）；**W-2** 无「原则性」词面依据：两条装配路线（n-折三角购入／望远镜+除法链）均在卷可行，供给半边已闭为正面证据；**W-3** 复审钩 §6 R1-R8；**W-4** 对抗复核臂＝GaC2_Iface_Eta 的 R3 wave-end 交叉行（头注 :66-69 登记）＋本席独立闭包追踪与勘定卷分级对表零冲突；**W-5** 不适用（无翻案）；**W-6** 四件套齐（W-1＋W-2＋W-4＋W-3） |
| (a) 面 | **需突破**（缺件可命名＝GaC2_08_EtaZetaRelation 零文件行） | find 零输出首手在卷（§0）；证明路线已在载体头注注册（:265-268）；复审钩 R1 |
| (c) 面 | **需突破**（门在 GaC2_07 eta_conv_uniform/abel_tail 载体态·:379-386 首手实读） | 晋升后余量轻（环6·1-2 席时）；复审钩 R2 |
| 真墙 | **0 项（不判）** | W-1~W-6 自检如上行；本卷无一处新立墙判词；卡面「需突破」预判只作带时戳引用（勘定卷同律） |

---

## §5 施工切片（Construction slices·可及段直接施工）

**已施工（本卷交付件 `GaC2_10_MtestGeomTail.v`，11 名）**:

| Section | 语句名 | 内容 | 档 |
|---|---|---|---|
| §1 | d10_mtest_opp_opp | 复数双重否定消解（点态环） | 已证·Defined |
| §1 | d10_mtest_sgn_step | d10_eta_sgn 逐步反号 | 已证·Defined |
| §1 | d10_mtest_sgn_parity | d10_eta_sgn 2-周期面 | 已证·Defined |
| §1 | d10_mtest_norm_sq_opp | 反号保平方模 | 已证·Defined |
| §1 | d10_mtest_sgn_is_eta_sgn_cx | **名实键**：节点符号列=C2-07 符号列，GaC2_07 奇偶供给行（abssum_alt_pair/eta_sgn_bounded_pair）自此对节点机群可消费 | 已证·Defined |
| §2 | d10_mtest_psum_step | d10_psum 步进面（机群形） | 已证·Qed（定义等） |
| §2 | d10_mtest_norm_sq_cpow_succ | 单项平方模乘性增长（M-test 逐项账基座） | 已证·Qed（定义等） |
| §2 | d10_mtest_geom_telescope | **几何望远镜恒等式 (1-w)·S_N = 1-w^(N+1)**（分母几何列 M-test 尾项估计的闭式代数核心）| 已证·Defined（归纳实质链） |
| §3 | d10_qpow＋d10_mtest_margin_form＋d10_mtest_margin_band_q1_4 | 有理幂载体＋余量形＋可判定样带（q=1/4·M=12：尾余量 2·(1/4)^13/(3/4)≈3.98e-8<10^-6；严格面取 negb-Qle_bool 形＝节点证书面正典习语） | 样带 vm_compute 闭＋REPL 级探针先行绿（见下） |

**探针先验记录（沙箱 REPL 级·≤3 发纪律·cpu_guard 包裹·probe_run3/probe_run4 log 在 `_build_c10/`）**: 隔离探针 `_probe_margin.v`（Stdlib QArith 单依赖）先于闭包编译逮住两处真实错误：(1) 本树 QArith 的 `^` 记法带 Z 指数——`q^(M+1)`（nat 指数）型别红，正形＝显式 nat-递归幂载体 `d10_qpow`；(2) 9.3 无 `Qlt_bool`（仅 Qle_bool/Qeq_bool），严格面正形＝`negb (Qle_bool ...)`（节点证书面同款习语）。两错以探针一发定谳、施工件随改（探针终态 RC=0＋Closed＋.vo 落盘·probe_run4）。静态判读被探针证伪两例的仲裁律（cw-tail-supply §12.3）正面兑现。
| §3 | d10_mtest_unif_face | **M-test 消费面**（(b) 行一致 Cauchy 连言的 GAPASUME 槽形载体：Hdom 逐项支配＋Htail 标量尾小面为显式前提参·born-clean 零假设） | 载体（诚实接口·禁体已注册） |

**四关验证记录（Verification record）**: 本节记录以落盘 log 为准（同目录 `log/`）。四关＝①coqc rc=0（真取）②语句面毒词零命中（gate1 词面＋gate6 census）③Print Assumptions Closed（件尾两处审计）④coqchk 如可用。log 文件清单与实测值见卷尾「验证记录附录」。

**余切片（拆债表·候派·定价【外推·未校准】）**:

| 债 | 目标语句（方向形） | 依赖 | 定价 | 入口 |
|---|---|---|---|---|
| D1 复数 n-折线性三角 | ‖Σ_{k<M..N} t_k‖² ≤ (Σ‖t_k‖)²+d（GaC1_14/15 方言） | gaC1_14 pair 形＋GaC2_02_c 实标量侧 | 2-5 席时 | GaC1_14:368 基座 |
| D2 eta 磁盘族 Hetad | (b) 行 Hetad 放电（消费 GaC2_07 均匀行） | R2（上游晋升） | 1-3 席时 | GaC2_10:289 |
| D3 系数列构造 | c_n Cauchy 积铸造＋log-幂界 | D1＋GaC1_16＋S07 log | 4-12 席时 | GaC1_15:32-36 对标行 |
| D4 值一致面 | Hval 装配 | D1-D3 | 2-4 席时 | GaC2_10:295-299 |
| D5 (a) 面本体 | zeta_tilde_agree 证明体 | R1（GaC2_08 落岸） | C2.08 行定价 | GaC2_10:269-274 |
| D6 (c) 面本体 | zeta_tilde_unif_bound 证明体 | R2＋GaC2_06＋c_inv_wit_correct | 1-2 席时 | GaC2_10:314-321 |
| D7 d10_mtest_unif_face 放电 | Hdom/Htail 消费→(b) Cauchy 连言 | D1＋D3 | 1-2 席时 | 本件 §3 载体 |

---

## §6 复审钩（Review hooks·W-3 纪律·判词有效期至基建变动或 24h 先到者）

| # | 触发条件 | 重估对象 |
|---|---|---|
| R1 | GaC2_08_EtaZetaRelation 模块落树（现全树零文件） | (a) 面（需突破→可及） |
| R2 | GaC2_07 abel_tail/eta_conv_uniform 晋升 Qed（现 :366-386 载体态） | (c) 面＋环2（eta 磁盘族）＋D6/D7 开工 |
| R3 | 复数 n-折线性三角落树（C2-02-c 族·GaC2_07:68 点名行） | (b) 面装配段＋D1/D7 放电 |
| R4 | GaC2_02_c 注册进节点 Require 面（母链整合） | 环1/环3 供给面直接插接 |
| R5 | S07 log／S03 exp 范数面扩容（log-幂系数界需求） | 环3 重定价 |
| R6 | 基点漂移（8e70342 → 后续 commit） | 本卷全部判词（反陈旧锚·强制重估） |
| R7 | 本卷施工件与 GaC2_10 上游任一名实键漂移（载体改名/签名移位） | §1 表＋施工件 Require 面（签名稳定律迁移账） |
| R8 | 勘定卷 R2 钩（母链落岸使七载体任一体闭合晋升）联动 | 本卷 §1 定档全表 |

---

## §7 诚实面（Honest scope·本卷未跑面·负发现自划边界）

1. **已跑**: 三技能加载、六关键词检索（零命中）、techdocs 三件＋靶件两件＋闭包关键件实读、39 件闭包递归追踪、克隆 git 态零写验证、WHEA 危机闸与道闸预检（实测 whea=0/10min·发射遵 2 道安全档）。
2. **候窗中/延后**: 39 件闭包冷编（后台·等清发射器挂运行，发射与本卷收卷的先后以 log 时戳为准：发射完成则 §5 四关记录全量填实，未完成则如实标注未跑）；gate7 Obj.magic 面数报数（沙箱期口径·依赖施工件 .vo）；coqchk 全树闭性（候闭包绿后）。
3. **未跑面**: 零网络检索（F7/mathlib 对标行系靶件头注与 GaC1_15 头注在库转引·fetch-before-cite 义务归施工时逐发台账）；未重编上游机检件（cert 两带 vm_compute 态系实读登记）；kbgamma seg_C3 与 GB 系未勘（与 (b) 面无 Require 边·本卷闭包追踪零指向）。
4. **机器争用登记（编译闸时序证据·首手台账）**: 本侧闭包冷编采「道闸等清发射」纪律（并发编译道数 ≤2·cw-ci-sop §4 禁忌总表）：发射器每 150s 采样一次，机器持续被他线两道巨编占用（rocqworker PID 165064＝SL3 沙箱 `zby_sl1234_out_20261114/sl3_sbx/sl3_d2_flag_anchors.v`，PID 201412＝SL4 沙箱 `planb4_g1_calibwin_b3.v`；两 worker 全程 CPU delta≈300s/150s 墙钟＝满速在编·二相律判活实测；等清台账全量落 `_build_c10/waiter.log`）。本侧发射条件＝总道数 ≤1 或双采样零 delta 死滞；发射与收卷先后以 log 时戳为准，未发射则四关如实标注未跑（禁凑绿）。
5. **判词边界**: 「GaC2_08 零文件」「GaC2_07 载体态」「供给半边已闭」均为 8e70342 时点首手实测·非绝对主张；R6 基点漂移即全量重估。双副本登记：8e70342 下 `ConstructiveWorld_Live/y_e1_gamma_nodes/GaC2_10_EtaContinuation.v` 与仓库根 `y_e1_gamma_nodes/GaC2_10_EtaContinuation.v` md5 同值（da4e07a72643002ccde7413695440ca3，两处逐字节同）；GaC2_07 同（7fa414acbac5d59a372e47ad0fef182d）。本卷靶件以 Live 树副本为准。

---

## §8 验证记录附录（Verification record·四关＋双闸全量实测值）

**施工件四关（GaC2_10_MtestGeomTail.v·最终轮 20261115 20:40:50·log/piece_build_run1.log）**:

| 关 | 判据 | 实测值 | 判 |
|---|---|---|---|
| ① coqc 真取 | rc=0（无管道真取·cpu_guard 包裹·load=4%） | G1_COMPILE_RC=0 | PASS |
| ② 语句面毒词 | 锚定扫描（^Error/Error:） | G2_ANCHORED_ERR_COUNT=0 | PASS |
| ③ 产物三证 | 魔数＋新鲜度＋PA 闭 | VO_MAGIC=436f7121000160bc（9.3 树魔数形·与 9.1 房规 5ff4 尾不同·版本判读）；VO_NEWER_THAN_V=YES；PA_CLOSED_COUNT=2（Print Assumptions ×2 均 Closed under the global context） | PASS |
| ④ coqchk | -o 非静默·五段摘要 | RC=0＋Modules were successfully checked＋Axioms: <none>＋type-in-type <none>＋unsafe cofixpoints <none>＋positivity assumed <none>（终态复证二连绿：piece_coqchk_run1.log＋piece_coqchk_final.log） | PASS |

**闭包冷编（39 件·flat 沙箱·cpu_guard 包裹）**: [ALL_DONE]×2＋[FAIL]×0（closure_build.log；双轮记录系发射器孤儿实例与主实例同时放行所致·两轮均串行 born-in-place 全绿·终态 coqchk 二次复证排除混杂世代）。模块级 markers 75×[BUILD]＝两轮 39＋39－3 轮首行计入差·零 FAIL。

**双闸（沙箱期口径）**:
- gate6 census 三跑（run1/run2/final）：RC=0·ch1/ch2/ch3 全零·names 11→12→16（随施工件增面增长·零违规·gate6_census_final.log＝16 名终态）。
- gate7 提取执行：`GATE7 [1/1] GaC2_10_MtestGeomTail names=16 rc=0 magic=0/0 missing=0`＋`GATE7-CENSUS: modules=1 magic_total=0 missing_candidates=0`（4a 沙箱级：Obj.magic 双面（.ml/.mli）零·零擦除候选·gate7_report_c10.json 随卷）。

**REPL 级探针（先于闭包编译·cpu_guard 包裹）**: `_probe_margin.v` 四轮（run1 通路假绿·run2 逮 `^` Z-指数型别红·run3 逮 `Qlt_bool` 缺失红·run4 绿：RC=0＋Closed＋.vo 落盘）；`_probe_telescope.v` 两轮（步例点态目标态直显·定谳 stuck-fixpoint 阻断 simpl 级联→全 C-级代数链改铸）。探针逮真错四发，全部反哺施工件修复。

**施工件指纹**: md5 0598e6a4cc4e608d458e9218c6f15446·315 行·16 名逐面：Section1 六面全 Defined（opp_opp／sgn_step／sgn_parity／norm_sq_opp／opp_c_of_real 点态环链＋sgn_is_eta_sgn_cx 归纳实质链）；Section2 六面＝psum_step（Qed·定义等机群形）＋norm_sq_cpow_succ（Qed·已闭引理定义等转移）＋mult_opp_r／cplus_shuffle（Defined·点态环）＋mult_plus_opp_l（Defined·C-级链）＋geom_telescope（Defined·归纳实质链）；Section3 四面＝d10_qpow（Fixpoint）＋margin_form（Definition）＋margin_band_q1_4（Qed·vm_compute）＋unif_face（Definition·诚实槽载体）。实质律口径：机器簇辅助面（psum_step/norm_sq_cpow_succ）为定义等转移面（GaC2_07 eta_part_step 同类），实质推导链集中于签名机六面与望远镜四面；使命语句 (a)/(b)/(c) 仍为语句载体·零证明代写。

**修复轮指纹注记（PR 组装席补钉·20261115）**: gate4 注释修复轮（四巷五 cmtfix log·20261115 21:17:38·全 GREEN4_final=True）晚于本卷收卷——上行指纹系修复前值（md5 0598e6a4cc4e608d458e9218c6f15446·315 行）。修复后现盘实测重钉：**md5 5ecedb54c5e49bb619461789c5d6f7a6·296 行·14,313 字节**；语句名面未变（gate6 终态 files=1·ch1/ch2/ch3=0/0/0·names=16）。

**迭代红账（fail-loud 留痕·七轮迭代全录 piece_build_run1.log）**: ①apply 显式参序错（c_eq_sym 回退零进展）→term 型 exact 修；②桥引理 destruct 后 IH 阶差（S k/k）→同递归路线重铸＋d10_mtest_opp_c_of_real 新面；③步例点态 ring 拒解（stuck fixpoint 阻断 simpl·探针直显）→全 C-级代数链（三新面：mult_opp_r/cplus_shuffle/mult_plus_opp_l）；④Hs1 尾序 c_mult 参序误（批量替换溢出）→F3 输出面回补；⑤shuffle 映射错→RHS 首和修正；⑥括号失衡两处→机补。六实质红＋一通路假绿（PS banner 空转·改 .cmd 正道），零静默降级，全部以编译第一手仲裁。

——铸毕 2026-11-15 · C2.10 线（Weierstrass M-test double series lane）· 依据＝第零步三道回执＋39 件闭包实勘＋靶件 321 行全读＋四关双闸全绿实测；需突破段只登记不硬闯；真墙 0 项——
