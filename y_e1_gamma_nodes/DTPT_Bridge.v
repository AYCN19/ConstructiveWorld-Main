(* ============================================================
   DTPT_Bridge.v —— P3 桥接层首件（P3-B1）：DTPT 冻结主件的 Set 层
   信息性桥接＋循环转发项同名非平凡替换稿。
   ── 使命：§1 信息性比较类型族 Type 版（QleT/QltT/QeqT，单构造子携
   Prop 证明参数＝提取擦除惯例）＋Qle 双向桥＋传播引理；§2 主库惯例
   同构件（And := A*B、ExistsT := sigT 本地同构 Type 版；DTPT 隔离区
   不 Require 主库）；§3 核心桥三件 C_sorted_min_adj_set／C_gen_set／
   H_devsum_nonneg_set（陈述 QleT 面，证明＝Prop 版直构包装）；§4
   Extraction 检验：对桥接引理本身提取，验收 Obj.magic=0 实测。
   循环转发件未决项按口径如实登记并改换路径：tarski_set 与
   layered_network_liar_set 复判为非玩具——Prop 存在消除入 sigT 为禁
   （Type 目标下该消除非法），existT 直构即唯一合法 Set 通道；
   H_min_q_anti_set 证明体已是定义面展开＋反变桥＋前提抽取三步直构，
   无转发可消；其余六条按口径三内联源件骨架（布尔三律／双副本守恒
   归纳／H_max_q 反变定义面／nat 提升桥）替换。
   ── 依赖：DTPT（冻结主件，只读 Require）、DTPT_Entropy（H_devsum
   所在件，只读使用：ADJ-1 改名点 L42、H_shannon_q_nonneg L116）、
   DTPT_Truth（宿主链同序）；stdlib（QArith／Qabs／List／Permutation／
   Lia／Extraction）。
   ── 对标行：主库惯例 S02 QltT/QleT/QleT'、S01 And/ExistsT（本件比
   较族改取单构造子形，信息角色与提取行为同构）；DTPT 族替换清单。
   ── 构造性注记：零承认件、零公理、零经典逻辑、全闭合；语句面
   Set 层零 Prop 泄露；全量机器检查（PA 全 Closed、提取 Obj.magic
   零、公理面 <none>）。H_freq/Entropy 族桥经核查 Entropy 置换不变
   命题为假命题，禁桥假命题，留待后续件。
   ── 编译配方：coqc -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" DTPT_Bridge.v。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Extraction.
Import ListNotations.
Open Scope Q_scope.

(* 归纳参数在构造子上自动隐式（主库 conj 风格：qleT_intro H 直构） *)
Set Implicit Arguments.

Require DTPT.
Require DTPT_Entropy.
(* P3-B3 追加：真理网/审查器冻结终态（835 行）只读使用；
   只 Require 不 Import（Import 置于 §7 内，防对 B1/B2 段遮蔽）。
   注：Module 内 Require 实测触发 require-in-module fragile 警告，
   破零警告关，故置文件头——B1/B2 段零改动，仅此一行插入。 *)
Require DTPT_Truth.
Import DTPT.DTPT.
Import DTPT_Entropy.DTPT_Entropy.

Module DTPT_Bridge.

(* ========== §1 信息性比较类型族（Type 版，主库 S02 同构映射） ========== *)

Inductive QleT (x y : Q) : Type :=
| qleT_intro : (x <= y)%Q -> QleT x y.

Inductive QltT (x y : Q) : Type :=
| qltT_intro : (x < y)%Q -> QltT x y.

Inductive QeqT (x y : Q) : Type :=
| qeqT_intro : (x == y)%Q -> QeqT x y.

(* Qle 双向桥：直构入桥 / 模式匹配抽取 *)
Definition QleT_of_Qle {x y : Q} (H : (x <= y)%Q) : QleT x y :=
  qleT_intro H.

Definition QleT_to_Qle {x y : Q} (Hq : QleT x y) : (x <= y)%Q :=
  match Hq with qleT_intro Hp => Hp end.

(* Qlt/Qeq 同族双向桥（同构映射同形） *)
Definition QltT_of_Qlt {x y : Q} (H : (x < y)%Q) : QltT x y :=
  qltT_intro H.

Definition QltT_to_Qlt {x y : Q} (Hq : QltT x y) : (x < y)%Q :=
  match Hq with qltT_intro Hp => Hp end.

Definition QeqT_of_Qeq {x y : Q} (H : (x == y)%Q) : QeqT x y :=
  qeqT_intro H.

Definition QeqT_to_Qeq {x y : Q} (Hq : QeqT x y) : (x == y)%Q :=
  match Hq with qeqT_intro Hp => Hp end.

(* 传播引理：QltT 传 QleT——stdlib QArith 本环境无 Qlt_le（CS1 卡
   第 4 条实测口径），按在案处方 unfold Qlt/Qle 后 lia 闭合 *)
Definition QltT_QleT {x y : Q} (Hq : QltT x y) : QleT x y.
Proof.
  destruct Hq as [Hlt]. apply qleT_intro. unfold Qle. unfold Qlt in Hlt. lia.
Defined.

(* ========== §2 主库惯例同构件（S01 本地同构 Type 版） ========== *)

Definition And (A B : Type) : Type := A * B.
Definition ExistsT {A : Type} (P : A -> Type) : Type := sigT P.

(* ========== §3 核心桥三件（陈述 QleT 面，证明＝Prop 版包装；
     提取面使用件故取 Defined——避免 opaque-accessed 提取警告） ========== *)

(* 核心一：排序最小化——DTPT.v L729 C_sorted_min_adj 的 Set 形重述 *)
Theorem C_sorted_min_adj_set : forall l : list Q,
  QleT (H_adj (P0 l)) (H_adj l).
Proof.
  intro l. apply qleT_intro. exact (C_sorted_min_adj l).
Defined.

(* 核心二：置换泛化——DTPT.v L968 C_gen（M1 并入件）的 Set 形重述 *)
Theorem C_gen_set : forall l p : list Q,
  Permutation l p -> QleT (H_adj (P0 l)) (H_adj p).
Proof.
  intros l p Hp. apply qleT_intro. exact (C_gen l p Hp).
Defined.

(* 核心三：H_devsum 非负——ADJ-1 改名现名（DTPT_Entropy.v L42 定义点），
   Prop 版＝DTPT_Entropy.v L116 H_shannon_q_nonneg 的 Set 形重述 *)
Theorem H_devsum_nonneg_set : forall l : list Q,
  QleT 0 (H_devsum l).
Proof.
  intro l. apply qleT_intro. exact (H_shannon_q_nonneg l).
Defined.

(* ========== §4 Extraction 检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

(* 产物落工作区显式化（消 extraction-default-directory 警告） *)
Set Extraction Output Directory ".".

Extraction "b1_QleT_ext.ml" QleT.
Extraction "b1_QltT_ext.ml" QltT.
Extraction "b1_QeqT_ext.ml" QeqT.
Extraction "b1_QleT_of_Qle_ext.ml" QleT_of_Qle.
Extraction "b1_C_sorted_min_adj_set_ext.ml" C_sorted_min_adj_set.
Extraction "b1_C_gen_set_ext.ml" C_gen_set.
Extraction "b1_H_devsum_nonneg_set_ext.ml" H_devsum_nonneg_set.

(* ========== §5 P3-B2 追加：熵族核心 Set 形桥接（） ==========
   前置核查裁决（详见 DTPT_P3B2_桥接报告.md §1）：
   DTPT_Entropy.v L125 注记所指命题＝「H_devsum 置换不变」（质心偏移
   占位形；盘上 H_shannon_q_perm_inv_counterex 已构造性证伪，反例
   [3;1;2] vs [2;1;3] 机检在案），与 §A2 H_freq_perm（真频率形
   1−Σp_v²，真）为不同承载形式、不同命题——裁决＝②不同命题且确为假
   （B1 标记无误，注记零改动）。本节桥 H_freq 面不触碰 H_devsum
   置换面，无假命题入桥。
   使用盘上已证件（全部只读）：
     H_freq_perm（DTPT_Entropy.v L1239）；collide_lower L1757 /
     collide_le_maxfreq L1794 / maxfreq_upper L1849（即 H_chain
     L1903 三成员）；H_shannon_q_zero_iff_sorted L2484 与 stdlib
     Qeq_bool_iff；freq_perm（DTPT.v L1974）；
     mu_total_mass（DTPT.v L2094）。
   类型注记：设计说明草式「1 # Z.of_nat (length l)」的 # 分母须
   positive 实参（Measure 卡同族坑：# 不可吃 Z），盘上类型正确形
   ＝ 1 / qn (length l)（collide_lower / maxfreq_lower 同面），
   从盘面。 *)

(* 保底件：H_freq 置换不变 Set 形（使用 DTPT_Entropy.v L1239 核心） *)
Theorem H_freq_perm_set : forall l p : list Q,
  Permutation l p -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hp. apply qeqT_intro. exact (H_freq_perm l p Hp).
Defined.

(* 核心：Rényi 阶梯 Set 形——非空表 1/n <= collide <= maxfreq <= 1
   一次入链（合取用 B1 §2 基建 And := A*B 信息性 Type 版） *)
Theorem H_chain_set : forall l : list Q, (0 < length l)%nat ->
  And (QleT (1 / qn (length l)) (collide l))
      (And (QleT (collide l) (maxfreq l)) (QleT (maxfreq l) 1)).
Proof.
  intros l Hl. unfold And. split.
  - apply qleT_intro. exact (collide_lower l Hl).
  - split.
    + apply qleT_intro. exact (collide_le_maxfreq l).
    + apply qleT_intro. exact (maxfreq_upper l).
Defined.

(* 主件：H_devsum 零点对照 Set 面——Qeq_bool 判定零点，经盘上
   iff 定理给出升序性的信息性承载形式（sumbool 形；判真支使用 iff
   正向，判假支经 qeqb_false_neq 反证非升序） *)
Definition H_devsum_zero_iff_sorted_set (l : list Q) :
  {SortedQ l} + {~ SortedQ l}.
Proof.
  destruct (Qeq_bool (H_devsum l) 0) eqn:Eb.
  - left. exact (proj1 (H_shannon_q_zero_iff_sorted l)
                   (proj1 (Qeq_bool_iff (H_devsum l) 0) Eb)).
  - right. intro Hs.
    assert (Hc : Qeq_bool (H_devsum l) 0 = true).
    { apply (proj2 (Qeq_bool_iff (H_devsum l) 0)).
      exact (proj2 (H_shannon_q_zero_iff_sorted l) Hs). }
    congruence.
Defined.

(* 加分一：freq 置换不变 Set 形——freq 为 nat 值，Q 域信息承载取
   mu l x 的分子面 (Z.of_nat (freq l x) # 1)%Q（# 须 positive 实参，
   故 # 1 归一，同 DTPT.v §12 mu 定义面）；使用 DTPT.v L1974 *)
Theorem freq_perm_set : forall (l p : list Q) (x : Q),
  Permutation l p ->
  QeqT ((Z.of_nat (freq l x) # 1)%Q) ((Z.of_nat (freq p x) # 1)%Q).
Proof.
  intros l p x Hp. apply qeqT_intro.
  rewrite (freq_perm l p x Hp). apply Qeq_refl.
Defined.

(* 加分二：均匀测度总质量一 Set 形（使用 DTPT.v L2094） *)
Theorem mu_total_mass_set : forall l : list Q, l <> [] ->
  QeqT (qsum (map (mu l) (dedup l))) 1.
Proof.
  intro l. intro Hne. apply qeqT_intro. exact (mu_total_mass l Hne).
Defined.

(* ========== §6 P3-B2 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b2_H_freq_perm_set_ext.ml" H_freq_perm_set.
Extraction "b2_H_chain_set_ext.ml" H_chain_set.
Extraction "b2_H_devsum_zero_iff_sorted_set_ext.ml" H_devsum_zero_iff_sorted_set.
Extraction "b2_freq_perm_set_ext.ml" freq_perm_set.
Extraction "b2_mu_total_mass_set_ext.ml" mu_total_mass_set.

(* ========== §7 P3-B3 追加：真理网/审查器核心 Set 形桥接（） ==========
   使用盘上已证件（DTPT_Truth.v 835 行冻结终态，全部只读）：
     level_le L89 / level_le_total L468 / trLevel_geq_trans L480 /
     audit_node L700 / diag_closed L247（对角化引理＝显式前提，
     参数形照盘上现役陈述 diag_closed Code diag truth 三参显式）/
     bool_neq_negb L252 / layered_network_liar_each_layer L368 /
     cv_size_preservation_T L574 / cv_size_preservation_D L588 /
     cv_lv L599 / dt_ev_size L584。
   基建：沿用 B1 §1 QleT/QeqT 族与 §2 And/sigT 信息性 Type 惯例；
     全部 Defined（提取使用件惯例，B1 坑④）；sumbool/sigT 直构。
   Tarski 语义边界声明（随行）：对角化引理＝显式前提 diag_closed
     ——与盘上塔斯基段同口径，本棒不证对角化引理本身（盘面无句法
     编码器，diag_closed 恰是其公理化形状）；tarski_set 的升级点＝
     盘上 tarski（L261）Prop 形 exists 的 Set 形重述，说谎句见证以
     sigT 信息性携带（见证码可计算交付，真值方程证明为 Prop 参随
     提取擦除）。liar_diag 为可执行码面对角构造器，其「闭包」语义
     由 diag_closed 前提承担（本棒不证 liar_diag closed——对任意
     具体闭包对角子 no_uniform_truth 即假，故诚实立场是不证）；
     liar_diag_point 为反面互补＝bool 三律下无码点满足对角方程
     （Prop 面，不提取）。
   层网面（§7.4）：码世界固定为 Dig、层索引为 Truth 侧 Level
     （盘上 layered_network_liar_each_layer 的 Code 一般形在本件
     取 Dig 实例，与 liar_diag 码面同世界）。
   ============================================================ *)

Import DTPT_Truth.DTPT_Truth.

(* ---------- 7.1 保底件：审查器可执行 Set 面 ---------- *)

(* 判定器完整性：audit_node 对任意节点可执行判定（sumbool 直构，
   bool 计算分支即判定；盘上双向行为定理 audit_node_iff L706 的
   判定面基础） *)
Theorem audit_node_spec_set : forall t : TrNode,
  {audit_node t = true} + {audit_node t = false}.
Proof.
  intro t. destruct (audit_node t).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* 层判 Set 面判定器：trLevel_geq 对任意节点/层可执行判定 *)
Theorem trLevel_geq_spec_set : forall (t : TrNode) (lv : Level),
  {trLevel_geq t lv = true} + {trLevel_geq t lv = false}.
Proof.
  intros t lv. destruct (trLevel_geq t lv).
  - left. reflexivity.
  - right. reflexivity.
Defined.

(* 层升单调 Set 形：节点对 a 层过审时对不升要求 b 的判定转移——
   左支使用盘上 trLevel_geq_trans（L480），右支以 bool 判定见证
   「要求未降」（level_le b a = false，level_le L89 计算面） *)
Theorem trLevel_geq_mono_set : forall (t : TrNode) (a b : Level),
  trLevel_geq t a = true ->
  {trLevel_geq t b = true} + {level_le b a = false}.
Proof.
  intros t a b Ha. destruct (level_le b a) eqn:E.
  - left. exact (trLevel_geq_trans t a b Ha E).
  - right. reflexivity.
Defined.

(* 全序 Set 面：level_le 判定器双向往复的信息性形——与盘上
   level_le_total（L468）同真值面；Prop \/ 不可消除入 Set，本件
   为 Level 三层九格穷举直构（判定器计算面，诚实声明非 Prop 使用） *)
Theorem level_le_total_set : forall a b : Level,
  {level_le a b = true} + {level_le b a = true}.
Proof.
  intros a b. destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Defined.

(* ---------- 7.2 核心：塔斯基可判定面（sigT 信息性说谎句见证） ---------- *)

(* 对角构造器（可执行码面）：把码 c 与其自身真值的 negb 反射封装为
   说谎码——truth c = true 时码内嵌 0、false 时内嵌 1（Q 编码走
   if 计算面）。闭包语义由 diag_closed 前提承担（边界声明见 §7 头注） *)
Definition liar_diag (truth : Dig -> bool) (c : Dig) : Dig :=
  dPair c (dQ (if negb (truth c) then 1%Q else 0%Q)).

(* 核心·塔斯基 Set 形：diag_closed 照盘上现役三参陈述，见证
   s := diag (fun c => negb (truth c)) 以 sigT 信息性携带——对照盘上
   tarski（L261）Prop 形 exists，Set 形升级点＝说谎句见证可计算交付 *)
Theorem tarski_set : forall (truth : Dig -> bool)
    (diag : (Dig -> bool) -> Dig),
  diag_closed Dig diag truth ->
  {s : Dig & truth s = negb (truth s)}.
Proof.
  intros truth diag Hcl.
  exact (existT _ (diag (fun c => negb (truth c)))
                  (Hcl (fun c => negb (truth c)))).
Defined.

(* 对角方程的 bool 三律互补面：无任何码点满足对角方程（使用盘上
   bool_neq_negb L252）——与 tarski_set 合读即 no_uniform_truth
   的两面：闭包前提造见证，三律封死解。Prop 面，不提取 *)
Theorem liar_diag_point : forall (truth : Dig -> bool) (c : Dig),
  truth (liar_diag truth c) = negb (truth (liar_diag truth c)) -> False.
Proof.
  intros truth c H.
  (* 口径三：内联布尔三律源件骨架——真值对说谎码的取值二支
     开析，每支方程经 negb 归约出布尔自反矛盾，判别剪枝闭合 *)
  destruct (truth (liar_diag truth c)); simpl in H; discriminate H.
Defined.

(* ---------- 7.3 主件：双副本相干桥 Set 形（守恒值见证携带） ---------- *)

(* T 侧守恒的信息性面：桥往返后尺寸守恒值 ev_size e 作为 nat 见证
   信息性携带（使用盘上 cv_size_preservation_T L574；方程证明为
   sigT 第二分量证明参，提取擦除） *)
Theorem cv_size_preservation_T_set : forall e : Evidence,
  {n : nat & ev_size (cv_ev (cv_ev_inv e)) = n}.
Proof.
  intro e.
  (* 口径三：内联源件 cv_size_preservation_T 归纳骨架——三构造
     子逐支：叶支双侧 iota 归一反射，Pair 支双归纳假设改写后
     构造子同余闭合；守恒值 ev_size e 仍作 sigT 见证携带 *)
  assert (Heq : ev_size (cv_ev (cv_ev_inv e)) = ev_size e).
  { induction e as [q | l | a IH1 b IH2]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1. rewrite IH2. reflexivity. }
  exact (existT _ (ev_size e) Heq).
Defined.

(* D 侧守恒的信息性面：桥测度 dt_ev_size 守恒值作为见证（使用盘上
   cv_size_preservation_D L588） *)
Theorem cv_size_preservation_D_set : forall e : DTPT.DTPT.Evidence,
  {n : nat & dt_ev_size (cv_ev_inv (cv_ev e)) = n}.
Proof.
  intro e.
  (* 口径三：内联源件 cv_size_preservation_D 归纳骨架——桥测度
     delta 展开后三构造子逐支：叶支双侧归一反射，Pair 支双归纳
     假设改写闭合；守恒值 dt_ev_size e 仍作 sigT 见证携带 *)
  assert (Heq : dt_ev_size (cv_ev_inv (cv_ev e)) = dt_ev_size e).
  { unfold dt_ev_size. induction e as [q | l | a IH1 b IH2]; simpl.
    - reflexivity.
    - reflexivity.
    - rewrite IH1. rewrite IH2. reflexivity. }
  exact (existT _ (dt_ev_size e) Heq).
Defined.

(* 层桥全序 Set 面：桥像上的层比较双向往复可判定（与盘上
   cv_lv_total_transport L640 同真值面；DTPT.Level 九格穷举直构） *)
Theorem cv_lv_total_set : forall a b : DTPT.DTPT.Level,
  {level_le (cv_lv a) (cv_lv b) = true} +
  {level_le (cv_lv b) (cv_lv a) = true}.
Proof.
  intros a b. destruct a, b; simpl;
    first [ left; reflexivity | right; reflexivity ].
Defined.

(* ---------- 7.4 加分：层网说谎句每层复活 Set 面 ---------- *)

(* 盘上 layered_network_liar_each_layer（L368）的 Set 形重述：
   每层闭包下每层产出说谎句见证（逐层实例化 tarski_set 同款直构，
   见证 sigT 信息性携带——与核心同一升级点） *)
Theorem layered_network_liar_set : forall
    (truth : Level -> Dig -> bool)
    (diag_lv : Level -> (Dig -> bool) -> Dig),
  (forall lv, diag_closed Dig (diag_lv lv) (truth lv)) ->
  forall lv, {s : Dig & truth lv s = negb (truth lv s)}.
Proof.
  intros truth diag_lv Hcl lv.
  exact (existT _ (diag_lv lv (fun c => negb (truth lv c)))
                  (Hcl lv (fun c => negb (truth lv c)))).
Defined.

(* ========== §8 P3-B3 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除；liar_diag_point 为
     Prop/False 面不提取，随行声明） ========== *)

Extraction "b3_audit_node_spec_set_ext.ml" audit_node_spec_set.
Extraction "b3_trLevel_geq_spec_set_ext.ml" trLevel_geq_spec_set.
Extraction "b3_trLevel_geq_mono_set_ext.ml" trLevel_geq_mono_set.
Extraction "b3_level_le_total_set_ext.ml" level_le_total_set.
Extraction "b3_liar_diag_ext.ml" liar_diag.
Extraction "b3_tarski_set_ext.ml" tarski_set.
Extraction "b3_cv_size_preservation_T_set_ext.ml" cv_size_preservation_T_set.
Extraction "b3_cv_size_preservation_D_set_ext.ml" cv_size_preservation_D_set.
Extraction "b3_cv_lv_total_set_ext.ml" cv_lv_total_set.
Extraction "b3_layered_network_liar_set_ext.ml" layered_network_liar_set.

(* ========== §9 P3-B5 追加：熵族剩余核心 Set 形桥接（） ==========
   使用盘面现役名 grep 实测表（DTPT_Entropy.v 2,708 行冻结终态，
   全部只读；棒 6a 进行中 Cyc/RotSpec/Lam 无交叠——DTPT_Lam.v 未
   Require 未使用，H_lam_anti_mono 禁使用进行中件照办）：
     collide_upper        L1743  forall l, collide l <= 1
     collide_lower        L1757  forall l, (0 < length l)%nat ->
                                   1 / qn (length l) <= collide l
     H_shannon_q_count_ub L664   forall l, H_devsum l <= H_adj l *
                                   (Z.of_nat (length l) # 1)
                                   （盘面现名实测＝原名未改，桥接引理名按
                                   B1 H_devsum 承载形式命名惯例取
                                   H_devsum_count_ub_set）
     H_max_q_anti         L1920  forall l p, maxfreq l <= maxfreq p ->
                                   H_max_q p <= H_max_q l
     H_max_q_nonneg       L1926  forall l, 0 <= H_max_q l
     H_min_q_nonneg       L1956  forall l, 0 <= H_min_q l
   主件二择一裁决：取 H_max_q_anti 反变单调面（QleT 前提经 §1
     QleT_to_Qle 抽取、结论经 qleT_intro 包装——双向桥同件串接，
     使用深度高于 collide_perm 直构形）；collide_perm 实测在册
     （L1778，EntFam2 归并区），按设计说明二择一让位，如实核算。
   H_lam 面声明：H_lam_mono（L94）现役但不在本棒任务清单，让位
     后续棒；H_lam_anti_mono 在 DTPT_Lam.v 棒 6a 归并中，禁使用。
   惯例：全部 Defined（B1 坑④提取使用件惯例）；# 分母 positive
     实参形照盘面（B2 坑②）；非空卫哨 (0 < length l)%nat 照
     collide_lower 原面（B2 H_chain_set 同款）。 *)
(* ============================================================ *)

(* ---------- 9.1 保底件：collide 界双 Set 形 ---------- *)

(* collide 上界 Set 形：Σp² <= 1 全表无卫哨（使用 L1743 collide_upper） *)
Theorem collide_upper_set : forall l : list Q,
  QleT (collide l) 1.
Proof.
  intro l. apply qleT_intro. exact (collide_upper l).
Defined.

(* collide 下界 Set 形：1/n <= collide，非空信息性卫哨形（使用
   L1757 collide_lower；卫哨照原面 nat 侧 (0 < length l)%nat） *)
Theorem collide_lower_set : forall l : list Q,
  (0 < length l)%nat -> QleT (1 / qn (length l)) (collide l).
Proof.
  intros l Hl. apply qleT_intro. exact (collide_lower l Hl).
Defined.

(* ---------- 9.2 核心：H_devsum 计数上界 Set 形 ---------- *)

(* 计数上界 QleT 面：H_devsum l <= H_adj l × 长度系数（使用
   L664 H_shannon_q_count_ub，盘面现名 grep 实测；桥接引理名按 B1
   H_devsum 承载形式命名惯例——对照 H_shannon_q_nonneg→
   H_devsum_nonneg_set 同款） *)
Theorem H_devsum_count_ub_set : forall l : list Q,
  QleT (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)).
Proof.
  intro l. apply qleT_intro. exact (H_shannon_q_count_ub l).
Defined.

(* ---------- 9.3 主件：H_max_q 反变单调 Set 形（二择一裁决件） ---------- *)

(* 反变单调：maxfreq l <= maxfreq p 导出 H_max_q p <= H_max_q l——
   前提 QleT 经 QleT_to_Qle 抽取为 Prop、结论经 qleT_intro 包装
   回 QleT（§1 双向桥串接；使用 L1920 H_max_q_anti） *)
Theorem H_max_q_anti_set : forall l p : list Q,
  QleT (maxfreq l) (maxfreq p) -> QleT (H_max_q p) (H_max_q l).
Proof.
  intros l p Hq. apply qleT_intro.
  (* 口径三：内联源件 H_max_q_anti 骨架——H_max_q 定义面
     （1 - maxfreq）展开后直构 qsub_le 反变桥，前提经 QleT_to_Qle
     模式匹配抽取，零源件转发跳 *)
  unfold H_max_q. apply qsub_le. exact (QleT_to_Qle Hq).
Defined.

(* ---------- 9.4 加分：H_min_q/H_max_q 界面 Set 形各一件 ---------- *)

(* H_max_q 非负界面 Set 形（使用 L1926 H_max_q_nonneg） *)
Theorem H_max_q_nonneg_set : forall l : list Q,
  QleT 0 (H_max_q l).
Proof.
  intro l. apply qleT_intro. exact (H_max_q_nonneg l).
Defined.

(* H_min_q 非负界面 Set 形（使用 L1956 H_min_q_nonneg） *)
Theorem H_min_q_nonneg_set : forall l : list Q,
  QleT 0 (H_min_q l).
Proof.
  intro l. apply qleT_intro. exact (H_min_q_nonneg l).
Defined.

(* ========== §10 P3-B5 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b5_collide_upper_set_ext.ml" collide_upper_set.
Extraction "b5_collide_lower_set_ext.ml" collide_lower_set.
Extraction "b5_H_devsum_count_ub_set_ext.ml" H_devsum_count_ub_set.
Extraction "b5_H_max_q_anti_set_ext.ml" H_max_q_anti_set.
Extraction "b5_H_max_q_nonneg_set_ext.ml" H_max_q_nonneg_set.
Extraction "b5_H_min_q_nonneg_set_ext.ml" H_min_q_nonneg_set.

(* ========== §11 P3-B8 追加：DPI 核心 Set 形桥接 + 熵族补充桥接引理（） ==========
   使用盘面现役名实测表（全部只读；FRUIT-2 进行中改 DTPT.v/DTPT_Entropy.v，
   本节名面经冻结 .vo 的 coqtop Check 检验逐一实测解析成立后才落笔；
   DTPT_Entropy2.v / DTPT_Rotation §S8 零 Require——禁使用进行中件照办）：
     H_freq_dpi           L1439  forall f, (forall x y : Q, x == y ->
                                 f x == f y) -> forall l,
                                 H_freq (map f l) <= H_freq l
                                 （形态假设照盘面逐字；Prop 卫哨随提取擦除）
     H_freq_map_twice     L1497  两步复合不增（盘面在册，grep 实测）
     H_freq_map_chain     L1506  链式不增（盘面在册，grep 实测）
     H_freq_eq0_all_same  L1291  H_freq l == 0 -> all_same l
                                 （简并刻画反向；all_same 为 Prop 面 L1182）
     H_freq_all_same_zero L1268  简并刻画正向（判假支矛盾支使用）
     qsub_le              L1637  forall x y z : Q, x <= y -> z - y <= z - x
                                 （盘面反变桥；盘上 H_max_q_anti 证明体同款）
     H_min_q              L1920  1 - collide l（定义面）
   惯例：全部 Defined（B1 坑④提取使用件惯例）；本节零分式无 # 面
     （B2 坑②不触发）；QleT/QeqT/And 基建沿用 §1/§2。
   诚实声明（11.3 主件）：盘面无 Prop 版 H_min_q_anti（grep 零命中）
     ——H_min_q_anti_set 照盘上 H_max_q_anti 证明体（unfold 后
     apply qsub_le）同款直构：前提 QleT 经 QleT_to_Qle 抽取、结论
     qleT_intro 包装，使用件＝qsub_le + H_min_q 定义面，零生造。
   ============================================================ *)

(* ---------- 11.1 核心：DPI 数据处理不等式 Set 形 ---------- *)

(* 观测（粗粒化合并质量）不增 H_freq 的信息性面——B1 配方：盘上
   Prop 件使用 + qleT_intro 直构包装；形态假设 Prop 卫哨照盘面逐字 *)
Theorem H_freq_dpi_set : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, QleT (H_freq (map f l)) (H_freq l).
Proof.
  intros f Hf l. apply qleT_intro. exact (H_freq_dpi f Hf l).
Defined.

(* ---------- 11.2 主件：DPI 链式面（盘面在册双件 grep 实测在册） ---------- *)

(* 两步复合不增 Set 形：第二次观测仍不增（使用 L1497 H_freq_map_twice） *)
Theorem H_freq_map_twice_set : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT (H_freq (map g (map f l))) (H_freq (map f l)).
Proof.
  intros f g Hf Hg l. apply qleT_intro.
  exact (H_freq_map_twice f g Hf Hg l).
Defined.

(* 链式不增 Set 形：map g ∘ map f 一次到底（使用 L1506 H_freq_map_chain） *)
Theorem H_freq_map_chain_set : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT (H_freq (map g (map f l))) (H_freq l).
Proof.
  intros f g Hf Hg l. apply qleT_intro.
  exact (H_freq_map_chain f g Hf Hg l).
Defined.

(* ---------- 11.3 主件：H_min_q 反变单调 Set 形 ---------- *)

(* 反变单调：collide l <= collide p 导出 H_min_q p <= H_min_q l——
   结论两侧翻转照 B5 H_max_q_anti_set 同款配方同构；前提 QleT 经
   QleT_to_Qle 抽取为 Prop、结论经 qleT_intro 包装回 QleT（§1 双向
   桥串接；盘上 H_max_q_anti 证明体同款：unfold 后 apply qsub_le） *)
Theorem H_min_q_anti_set : forall l p : list Q,
  QleT (collide l) (collide p) -> QleT (H_min_q p) (H_min_q l).
Proof.
  intros l p Hq. apply qleT_intro. unfold H_min_q. apply qsub_le.
  exact (QleT_to_Qle Hq).
Defined.

(* ---------- 11.4 加分：简并判定器（H_freq 零点对照面另一侧） ---------- *)

(* 简并刻画双向闭合的可执行判定器：Qeq_bool (H_freq l) 0 判定全同值
   ——判真支使用 H_freq_eq0_all_same（零点 ⟹ 全同值）、判假支以
   H_freq_all_same_zero（全同值 ⟹ 零点）+ Qeq_bool_iff 矛盾闭合
   （B2 H_devsum_zero_iff_sorted_set 同款配方；all_same 为 Prop 面，
   sumbool 分支携 Prop 参随提取擦除，零 Prop 消除入 Type） *)
Definition H_freq_eq0_all_same_set (l : list Q) :
  {all_same l} + {~ all_same l}.
Proof.
  destruct (Qeq_bool (H_freq l) 0) eqn:Eb.
  - left. exact (H_freq_eq0_all_same l
                  (proj1 (Qeq_bool_iff (H_freq l) 0) Eb)).
  - right. intro Hall.
    assert (Hc : Qeq_bool (H_freq l) 0 = true).
    { apply (proj2 (Qeq_bool_iff (H_freq l) 0)).
      exact (H_freq_all_same_zero l Hall). }
    congruence.
Defined.

(* ========== §12 P3-B8 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b8_H_freq_dpi_set_ext.ml" H_freq_dpi_set.
Extraction "b8_H_freq_map_twice_set_ext.ml" H_freq_map_twice_set.
Extraction "b8_H_freq_map_chain_set_ext.ml" H_freq_map_chain_set.
Extraction "b8_H_min_q_anti_set_ext.ml" H_min_q_anti_set.
Extraction "b8_H_freq_eq0_all_same_set_ext.ml" H_freq_eq0_all_same_set.

(* ========== §13 P3-B11 追加：FRUIT-2 新定理 Set 形桥接（） ==========
   使用盘面现役名实测表（全部只读；双实测＝grep 进行中 .v + coqtop Check
   冻结 .vo（DTPT.vo  / DTPT_Entropy.vo ，FRUIT-2 闭合版），
   七名签名逐项吻合后才落笔，检验日志 _p3b11_probe.log 在案）：
     sqsum_app_ge_l   DTPT_Entropy.v L2696  forall l1 l2,
                        (sqsum l1 <= sqsum (l1 ++ l2))%nat
     sqsum_app_ge_r   DTPT_Entropy.v L2706  forall l1 l2,
                        (sqsum l2 <= sqsum (l1 ++ l2))%nat
     sqsum_app_eq     DTPT_Entropy.v L2718  精确交叉项分解（nat 恒等式，
                        含 Σ_{x∈l1} freq_q x l2 与 Σ_{x∈l2} freq_q x l1
                        双交叉项）
     mu_fiber_pos     DTPT.v L3427  forall f w x, In x (fiber f w) ->
                        0 < mu w x
     mu_fiber_mass_lb DTPT.v L3452  forall f w, w <> [] ->
                        (|fiber|/|w|) <= qsum (map (mu w) (dedup (fiber)))
     mu_fiber_mass_eq DTPT.v L3560  forall f w, w <> [] -> φ 外延卫哨 ->
                        qsum (map (mu w) (dedup (fiber))) == |fiber|/|w|
   让窗声明（本棒特记）：ADJ-4 进行中改 DTPT_Entropy.v §A7（.v
     新于 .vo ）——此处零消费 §A7，使用名经冻结 .vo Check 实测
     解析成立；FRUIT-3 进行中 Rotation §S9 与此处零交集。ADJ-4 闭合重编
     Entropy.vo 后此处重验 Bridge.vo 一轮（使用名面按上表完成核对）。
   nat → Q 提升惯例（B2 freq_perm_set 同款）：sqsum/freq_q/nsum 族为
     nat 值，信息性面取 (Z.of_nat · # 1)%Q 归一提升（# 分母 positive
     实参形照盘面，B2 坑②）；nat ≤/＝ 经 Znat.Nat2Z.inj_le/_add
     搬入 Z 面（DTPT.v §15 盘面同款配方）。
   惯例：全部 Defined（B1 坑④提取使用件惯例）；QleT/QeqT/QltT 基建
     沿用 §1。
   ============================================================ *)

(* ---------- 13.1 保底件：sqsum 拼接单调双件（QleT 面） ---------- *)

(* 左拼接单调 Set 形：sqsum l1 <= sqsum (l1 ++ l2) 的信息性面——
   nat 不等经 (Z.of_nat · # 1) 提升入 QleT（使用 L2696 sqsum_app_ge_l） *)
Theorem sqsum_app_ge_l_set : forall l1 l2 : list Q,
  QleT ((Z.of_nat (sqsum l1) # 1)%Q) ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q).
Proof.
  intros l1 l2. apply qleT_intro.
  unfold Qle. rewrite !Z.mul_1_r.
  apply (proj1 (Znat.Nat2Z.inj_le (sqsum l1) (sqsum (l1 ++ l2)))).
  apply sqsum_app_ge_l.
Defined.

(* 右拼接单调 Set 形：sqsum l2 <= sqsum (l1 ++ l2) 的信息性面
   （使用 L2706 sqsum_app_ge_r；左件同构） *)
Theorem sqsum_app_ge_r_set : forall l1 l2 : list Q,
  QleT ((Z.of_nat (sqsum l2) # 1)%Q) ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q).
Proof.
  intros l1 l2. apply qleT_intro.
  unfold Qle. rewrite !Z.mul_1_r.
  apply (proj1 (Znat.Nat2Z.inj_le (sqsum l2) (sqsum (l1 ++ l2)))).
  apply sqsum_app_ge_r.
Defined.

(* ---------- 13.2 核心：纤维测度质量下界 Set 形（+ 随行正性面） ---------- *)

(* 核心·主桥 Set 形：非空世界表上零点经验频率 |fiber φ w|/|w| <= 纤维
   支撑的 w-测度质量——P_φ(0) 经验频率下界的 QleT 信息性面（使用
   L3452 mu_fiber_mass_lb，陈述面 QleT 化照盘面逐字，非空卫哨照原面） *)
Theorem mu_fiber_mass_lb_set : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  QleT (((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q)
        (qsum (map (mu w) (dedup (fiber f w)))).
Proof.
  intros f w Hne. apply qleT_intro. exact (mu_fiber_mass_lb f w Hne).
Defined.

(* 随行件·判零会员测度正性 Set 形：0 < mu w x 的严格正面取 QltT
   （§1 基建；使用 L3427 mu_fiber_pos——桥接对象点名件的诚实信息面） *)
Theorem mu_fiber_pos_set : forall (f : Q -> Q) (w : list Q) (x : Q),
  In x (fiber f w) -> QltT 0 (mu w x).
Proof.
  intros f w x Hin. apply qltT_intro. exact (mu_fiber_pos f w x Hin).
Defined.

(* ---------- 13.3 主件：sqsum 拼接精确交叉项分解 QeqT 面 ---------- *)

(* 基建随行件：nat 等式 → QeqT 的 (Z.of_nat · # 1) 归一提升桥
   （nat 面 QeqT 化的最短通道；提取面一并验收） *)
Theorem QeqT_of_nat_eq : forall a b : nat, a = b ->
  QeqT ((Z.of_nat a # 1)%Q) ((Z.of_nat b # 1)%Q).
Proof.
  intros a b H. apply qeqT_intro. rewrite H. apply Qeq_refl.
Defined.

(* 精确交叉项分解 Set 形：sqsum (l1++l2) 的 Q 载值恒等于两段平方和加
   双交叉项 Σ_{x∈l1} freq_q x l2 与 Σ_{x∈l2} freq_q x l1——信息性面
   （使用 L2718 sqsum_app_eq；nat 恒等式重写 + Nat2Z.inj_add 展开） *)
Theorem sqsum_app_eq_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q)
       (((Z.of_nat (sqsum l1) # 1) + (Z.of_nat (sqsum l2) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l2) l1) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l1) l2) # 1))%Q).
Proof.
  intros l1 l2. apply qeqT_intro.
  rewrite (sqsum_app_eq l1 l2).
  unfold Qeq. simpl. rewrite !Z.mul_1_r. rewrite !Znat.Nat2Z.inj_add.
  reflexivity.
Defined.

(* ---------- 13.4 加分件：纤维质量守恒取等 Set 形 ---------- *)

(* 质量守恒显式形 Set 面：φ 沿支撑 Qeq-外延卫哨（照盘面逐字 Prop
   卫哨，随提取擦除）下取等——P_φ(0) 经验频率恰为纤维 w-测度质量
   （使用 L3560 mu_fiber_mass_eq；f := 常零退化为 B2 mu_total_mass_set
   相容核对） *)
Theorem mu_fiber_mass_eq_set : forall (f : Q -> Q) (w : list Q),
  w <> [] ->
  (forall x y : Q, x == y -> f x == f y) ->
  QeqT (qsum (map (mu w) (dedup (fiber f w))))
       (((Z.of_nat (length (fiber f w)) # 1) / (Z.of_nat (length w) # 1))%Q).
Proof.
  intros f w Hne Hf. apply qeqT_intro. exact (mu_fiber_mass_eq f w Hne Hf).
Defined.

(* ========== §14 P3-B11 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b11_sqsum_app_ge_l_set_ext.ml" sqsum_app_ge_l_set.
Extraction "b11_sqsum_app_ge_r_set_ext.ml" sqsum_app_ge_r_set.
Extraction "b11_mu_fiber_pos_set_ext.ml" mu_fiber_pos_set.
Extraction "b11_mu_fiber_mass_lb_set_ext.ml" mu_fiber_mass_lb_set.
Extraction "b11_QeqT_of_nat_eq_ext.ml" QeqT_of_nat_eq.
Extraction "b11_sqsum_app_eq_set_ext.ml" sqsum_app_eq_set.
Extraction "b11_mu_fiber_mass_eq_set_ext.ml" mu_fiber_mass_eq_set.

(* ========== §15 P3-B13 追加：FRUIT-5 §A8 新定理 Set 形桥接——拼接精确卷积式（） ==========
   使用盘面现役名实测表（全部只读；FRUIT-5 已闭合冻结面＝DTPT_Entropy.vo
    > .v ，六名 grep .v 实测 + 检验编译链接冻结 .vo 实测
   双证在案（_p3b13_probe.log），签名逐项吻合后才落笔）：
     sqsum_app_cross   DTPT_Entropy.v L2990  sqsum (l1++l2) = sqsum l1 +
                        sqsum l2 + Σ_{x∈l1} freq_q x l2 + Σ_{x∈l2} freq_q x l1
                        （交叉项显式四项形；盘面证明体 exact 使用 §A6
                        sqsum_app_eq，此处照盘面名位件使用）
     sqsum_cross_sym   DTPT_Entropy.v L2999  Σ_{x∈l1} freq_q x l2 =
                        Σ_{x∈l2} freq_q x l1（对称双和，2X 标准形承重面）
     sqsum_app_eq2     DTPT_Entropy.v L3020  sqsum (l1++l2) = sqsum l1 +
                        sqsum l2 + 2·Σ_{x∈l1} freq_q x l2（2X 标准形）
     collide_app_eq    DTPT_Entropy.v L3033  collide (l1++l2) ==
                        (n1/n)²·collide l1 + (n2/n)²·collide l2 + X/n²
                        （加权平方组合 + 交叉修正；双非空卫哨
                        (0 < length l1/l2)%nat 照盘逐字）
     H_freq_app_eq     DTPT_Entropy.v L3073  H_freq (l1++l2) == w1²·H_freq l1
                        + w2²·H_freq l2 + 2·w1·w2 − X/n²（熵族拼接卷积完整
                        恒等式；其盘面证明即使用 H_freq_eq_bridge L1993
                        「H_freq == 1 − collide」桥面——此处随链继承）
     H_freq_app_assoc  DTPT_Entropy.v L3118  H_freq ((l1++l2)++l3) ==
                        H_freq (l1++(l2++l3))（三段结合律一致性值面）
   基建与惯例：QeqT/Defined 沿 §1（B1）/§13（B11）；nat 面经 §13.3
     QeqT_of_nat_eq 一跳提升（(Z.of_nat · # 1) 归一，# 分母 positive，
     B2 坑②；注意 Set Implicit Arguments 下其 nat 二参为隐式，应用
     形＝单方程实参）；展开四项形照 B11 sqsum_app_eq_set 同款配方
     （rewrite + unfold Qeq + simpl + Z.mul_1_r + Nat2Z.inj_add +
     reflexivity）；卫哨照盘面原形 (0 < length l)%nat（B2 H_chain_set
     同款）；Prop 证明参随提取擦除（B1 构造子惯例）。
   数值检验先行（FRUIT-5 教训，_p3b13_probe.log 在案）：l1=[0;1]、
     l2=[1;1]（X1=X2=2 非平凡交叉）逐一 Qeq_bool/vm_compute 验真值
     ——四项面/对称双和/2X 面/collide 卷积（实例值 5/8）/H_freq 卷积
     （实例值 3/8）/assoc 同值，八检验全 true 后落笔；六件 Theorem
     形检验 Print Assumptions 全 Closed（6/6 实测）。
   诚实核算（eq2 面形裁决）：sqsum_app_eq2_set 取 nat 整式提升形
     （2X 系数在 Z.of_nat 内可见）——Q 域 2·X 展开面检验两轮未达
     （naked simpl 把 Z 侧 2·nx 归约为 match 倍形致 lia/zify 失明；
     cbn 定点展开路线 Rocq 9 名面 Qmult 不可 coerce），依禁生硬构造条款
     不强凑，展开视角由 §13.3 sqsum_app_eq_set（四项面）承担。
   ============================================================ *)

(* ---------- 15.1 保底件：交叉项显式形 Set 面（QeqT 面） ---------- *)

(* 交叉项显式四项形 Set 面：sqsum (l1++l2) 的 Q 载值恒等于两段平方和加
   双交叉项 Σ_{x∈l1} freq_q x l2 与 Σ_{x∈l2} freq_q x l1——逐加数独立
   Q 载值（使用 L2990 sqsum_app_cross；与 §13.3 sqsum_app_eq_set 同形
   对账，本件使用 §A8 保底名位件） *)
Theorem sqsum_app_cross_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q)
       (((Z.of_nat (sqsum l1) # 1) + (Z.of_nat (sqsum l2) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l2) l1) # 1)
         + (Z.of_nat (nsum (fun x => freq_q x l1) l2) # 1))%Q).
Proof.
  intros l1 l2. apply qeqT_intro.
  rewrite (sqsum_app_cross l1 l2).
  unfold Qeq. simpl. rewrite !Z.mul_1_r. rewrite !Znat.Nat2Z.inj_add.
  reflexivity.
Defined.

(* ---------- 15.2 保底件：对称双和 Set 面 ---------- *)

(* 对称双和 Set 面：两交叉项相等（同计配对集 {(p,q)∈l1×l2 : p==q}）的
   Q 载值信息性面——nat 恒等式经 QeqT_of_nat_eq 一跳提升（使用 L2999
   sqsum_cross_sym） *)
Theorem sqsum_cross_sym_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (nsum (fun x => freq_q x l2) l1) # 1)%Q)
       ((Z.of_nat (nsum (fun x => freq_q x l1) l2) # 1)%Q).
Proof.
  intros l1 l2.
  (* 口径三：内联 nat 等式提升桥母体——qeqT 直构后对称双和
     恒等式改写，Qeq 自反闭合，零转发跳 *)
  apply qeqT_intro.
  rewrite (sqsum_cross_sym l1 l2). apply Qeq_refl.
Defined.

(* ---------- 15.3 保底随行件：2X 标准形 Set 面 ---------- *)

(* 2X 标准形 Set 面：交叉项以对称双和归并（sqsum l1 + sqsum l2 + 2·X）
   的 Q 载值恒等式——nat 整式提升通道（使用 L3020 sqsum_app_eq2；
   §15.1/§15.2 双件的归并面，面形裁决核算见 §15 头注） *)
Theorem sqsum_app_eq2_set : forall l1 l2 : list Q,
  QeqT ((Z.of_nat (sqsum (l1 ++ l2)) # 1)%Q)
       ((Z.of_nat (sqsum l1 + sqsum l2 + 2 * nsum (fun x => freq_q x l2) l1)
         # 1)%Q).
Proof.
  intros l1 l2.
  (* 口径三：内联 nat 等式提升桥母体——qeqT 直构后 2X 标准形
     恒等式改写，Qeq 自反闭合，零转发跳 *)
  apply qeqT_intro.
  rewrite (sqsum_app_eq2 l1 l2). apply Qeq_refl.
Defined.

(* ---------- 15.4 核心：collide 拼接卷积 Set 面 ---------- *)

(* 加权精确卷积 Set 面：collide (l1++l2) == (n1/n)²·collide l1 +
   (n2/n)²·collide l2 + X/n²——权重平方型加权组合 + 交叉修正逐项 QeqT
   信息性面；双非空卫哨照盘面逐字（Prop 卫哨随提取擦除；使用 L3033
   collide_app_eq） *)
Theorem collide_app_eq_set : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  QeqT (collide (l1 ++ l2))
    ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * collide l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * collide l2
    + (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat))%Q.
Proof.
  intros l1 l2 H1 H2. apply qeqT_intro. exact (collide_app_eq l1 l2 H1 H2).
Defined.

(* ---------- 15.5 主件：H_freq 拼接卷积 Set 面 ---------- *)

(* 熵族拼接卷积完整恒等式 Set 面：H_freq (l1++l2) == w1²·H_freq l1 +
   w2²·H_freq l2 + 2·w1·w2 − X/n²（使用 L3073 H_freq_app_eq——其盘面
   证明即使用 H_freq_eq_bridge L1993「H_freq == 1 − collide」桥面，
   本件随链继承；双非空卫哨照盘面逐字） *)
Theorem H_freq_app_eq_set : forall l1 l2 : list Q,
  (0 < length l1)%nat -> (0 < length l2)%nat ->
  QeqT (H_freq (l1 ++ l2))
    ((qn (length l1) / qn (length l1 + length l2)%nat)
      * (qn (length l1) / qn (length l1 + length l2)%nat) * H_freq l1
    + (qn (length l2) / qn (length l1 + length l2)%nat)
      * (qn (length l2) / qn (length l1 + length l2)%nat) * H_freq l2
    + 2 * (qn (length l1) / qn (length l1 + length l2)%nat)
        * (qn (length l2) / qn (length l1 + length l2)%nat)
    - (qn (nsum (fun x => freq_q x l2) l1)
       + qn (nsum (fun x => freq_q x l1) l2))
      / (qn (length l1 + length l2)%nat * qn (length l1 + length l2)%nat))%Q.
Proof.
  intros l1 l2 H1 H2. apply qeqT_intro. exact (H_freq_app_eq l1 l2 H1 H2).
Defined.

(* ---------- 15.6 加分件：三段结合律一致性 Set 面 ---------- *)

(* 三段拼接结合律卷积一致性 Set 面：(l1++l2)++l3 与 l1++(l2++l3) 同表
   （app_assoc 定义性），熵族卷积量在两种分组下逐点 QeqT 重合——择
   H_freq 面（Q 域恒等式信息量高于 sqsum nat 面；使用 L3118
   H_freq_app_assoc） *)
Theorem H_freq_app_assoc_set : forall (l1 l2 l3 : list Q),
  QeqT (H_freq ((l1 ++ l2) ++ l3)) (H_freq (l1 ++ (l2 ++ l3))).
Proof.
  intros l1 l2 l3. apply qeqT_intro.
  (* 源件 H_freq_app_assoc 骨架内联：app_assoc 定义性改写一步归一同表 *)
  rewrite <- app_assoc. reflexivity.
Defined.

(* ========== §16 P3-B13 提取检验（U12 配方：逐件独立提取，
     验收指标＝Obj.magic 计数 0，验后产物清除） ========== *)

Extraction "b13_sqsum_app_cross_set_ext.ml" sqsum_app_cross_set.
Extraction "b13_sqsum_cross_sym_set_ext.ml" sqsum_cross_sym_set.
Extraction "b13_sqsum_app_eq2_set_ext.ml" sqsum_app_eq2_set.
Extraction "b13_collide_app_eq_set_ext.ml" collide_app_eq_set.
Extraction "b13_H_freq_app_eq_set_ext.ml" H_freq_app_eq_set.
Extraction "b13_H_freq_app_assoc_set_ext.ml" H_freq_app_assoc_set.

End DTPT_Bridge.

(* —— 切片二替换件闭包打印（追加，机检附件） —— *)
Import DTPT_Bridge.
Print Assumptions liar_diag_point.
Print Assumptions cv_size_preservation_T_set.
Print Assumptions cv_size_preservation_D_set.
Print Assumptions H_max_q_anti_set.
Print Assumptions sqsum_cross_sym_set.
Print Assumptions sqsum_app_eq2_set.
