(* ============================================================
   UpReqPadeTransport.v —— Q→Real 运输桥族：把 Q 层 Padé 界运到
   Real 层 cauchy_real_exp 的 eps/Bishop 形，Real 层首获 Padé 精度
   exp 界。
   ── 使命：G1① qtr_embed_mono／qtr_embed_le——Q→Real 嵌入保序桥
   （QltT a b ⟹ real_const a < real_const b；见证 eps := (b−a)/2、
   N := 0，自建单跳）；G1② qtr_exp_gt_partial／qtr_exp_ge_partial——
   级数桥：Real 层 e^y 与第 n 部分和嵌入的 eps/Bishop 序（见证
   eps := (y^{n+1}/(n+1)!)/2、N := n+1）；G2 qtr_mult_eq_compat_l＋
   qtr_pade_lower_real——运输引擎与 Padé 精度 Real 层下界首件
   （检验值任取 w ≡ e^y，乘开免除法形，取用 cpl_lower_even）；
   G2b qtr_pade_lower_extract——Real→逐点证书反射：cpl 的 real_lt
   见证解包为显式 N/eps 的逐点 QltT 形。
   ── 依赖：UpReqPadeExp（pade_num/pade_den）、UpReqQExpTail
   （qtail_*）、UpReqPadeLower（cpl_lower_even 系）、DTPT_Bridge、
   S01_BaseRing、S02_CauchyComplete、S03_QExp、S07_RealSetoidExpLog；
   只 Require 不改源。
   ── 构造性注记：全员 Print Assumptions 预期 Closed（无公理依赖）；
   纯构造性、零 LPO、零经典极限／积分性质；Set 层假设位全走
   QltT/QleT（S01 Set 序），无 Prop 假设位。
   ── 证法风格：除法规避＝乘开形态＋Qmult_inv_r 证书（库内 cpl
   先例）；Qeq 传递链一律 assert 具名＋apply-with，禁证明槽占位
   （elaboration 不可推断）。
   ── 编译配方：coqc -q -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" UpReqPadeTransport.v。
   ============================================================ *)

Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeLower.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia Setoid.
Require Import DTPT_Bridge.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S01_BaseRing.
Require Import S07_RealSetoidExpLog.

(* ============================================================ *)
(* B0 桥接件：Q 层小组合件（自持零外部依赖）                          *)
(* ============================================================ *)

(* a < b ⟹ 0 < b − a（QltT 面）。
   证法：Qplus_lt_r（z+x < z+y <-> x<y，z := −a）+ Qplus_opp_r/
   Qplus_comm setoid 换形；Qminus b a 定义性 == b + (−a)。
   （destruct-lia 不可行：分母正性不在 lia 可达面。） *)
Lemma qtr_qlt_sub : forall a b : Q, QltT a b -> QltT 0 (b - a).
Proof.
  intros a b H.
  assert (Hlt : Qlt a b) by (apply QltT_to_Qlt; exact H).
  assert (H1 : Qlt (- a + a) (- a + b)).
  { exact (proj2 (Qplus_lt_r a b (- a)) Hlt). }
  apply Qlt_to_QltT.
  setoid_rewrite (Qplus_comm (- a) a) in H1.
  setoid_rewrite (Qplus_opp_r a) in H1.
  setoid_rewrite (Qplus_comm (- a) b) in H1.
  exact H1.
Qed.

(* 0 < x ⟹ x/2 < x（半额严格收缩）。
   destruct-lia：H 多项式形 0 < nx·dx，目标 −(nx·dx) < 2·(nx·dx)，
   线性于 P := nx·dx（micromega 环形范化；cpl_qlt_le 同族）。 *)
Lemma qtr_div2_lt : forall x : Q, Qlt 0 x -> Qlt (x / 2) x.
Proof.
  intro x. unfold Qlt in *.
  destruct x as [nx dx]. simpl in *. lia.
Qed.

Lemma qtr_div2_ltT : forall x : Q, QltT 0 x -> QltT (x / 2) x.
Proof.
  intros x H. apply Qlt_to_QltT. apply qtr_div2_lt.
  apply QltT_to_Qlt. exact H.
Qed.

(* 约分证书：m ≠ 0 ⟹ (a/m)·m == a（Qmult_inv_r，零除法目标面） *)
Lemma qtr_div_cancel : forall a m : Q, ~ (m == 0) -> a / m * m == a.
Proof.
  intros a m Hm. unfold Qdiv.
  rewrite <- (Qmult_assoc a (/ m) m).
  rewrite (Qmult_comm (/ m) m).
  rewrite (Qmult_inv_r m Hm).
  apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* G1① 嵌入保序桥：Q 层序 ⟹ Real 层嵌入序                          *)
(* ============================================================ *)

(* 严格形：a < b ⟹ real_const a < real_const b。
   见证 eps := (b−a)/2 > 0、N := 0（常值序列逐点合同）。 *)
Theorem qtr_embed_mono : forall a b : Q, QltT a b ->
  real_lt (real_const a) (real_const b).
Proof.
  intros a b Hab.
  assert (Hsub : QltT 0 (b - a)) by (apply qtr_qlt_sub; exact Hab).
  assert (Hhalf : QltT ((b - a) / 2) (b - a)) by (apply qtr_div2_ltT; exact Hsub).
  unfold real_lt.
  exists ((b - a) / 2)%Q. split.
  - apply qltT_div_pos.
    + exact Hsub.
    + exact qltT_0_2.
  - exists 0%nat. intros n _.
    assert (Hraw : projT1 (real_const b) n - projT1 (real_const a) n
                   == b - a).
    { apply Qminus_comp; apply real_const_proj. }
    apply qltT_eq_compat_r with (a' := (b - a)%Q).
    + exact Hraw.
    + exact Hhalf.
Qed.

(* 弱形：a ≤ b ⟹ real_const a ≤ real_const b（real_le 三形：
   严格支走嵌入桥；Id 等值支走 Qabs 零合同）。 *)
Theorem qtr_embed_le : forall a b : Q, QleT a b ->
  real_le (real_const a) (real_const b).
Proof.
  intros a b Hab. destruct Hab as [Hlt | H0].
  - left. apply qtr_embed_mono. exact Hlt.
  - right. intros eps Heps. exists 0%nat. intros n _.
    assert (Hab0 : a - b == 0).
    { destruct H0. ring. }
    assert (Habs0 : Qabs (projT1 (real_const a) n
                          - projT1 (real_const b) n) == 0).
    { apply Qeq_trans with (y := Qabs (a - b)).
      - apply Qabs_wd. apply Qminus_comp; apply real_const_proj.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. exact Hab0.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ============================================================ *)
(* G1② 级数桥墩：Q 层部分和尾差下界（e^y ≥ 部分和 的 Q 内核）        *)
(* ============================================================ *)

(* 尾差首项下界：0 ≤ y、d ≥ 0 ⟹
   y^{n+1}/(n+1)! ≤ E_{n+1+d}(y) − E_n(y)。
   归纳不变式：每步追加非负项 y^k/k!（q_pow_fact_nonneg）。 *)
Lemma qtr_partial_gap : forall (y : Q) (n d : nat), QleT 0 y ->
  Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
      (exp_partial (Datatypes.S n + d) y - exp_partial n y).
Proof.
  intros y n d Hy. revert d.
  assert (Hy0 : Qle 0 y) by (apply qtail_QleT_to_Qle; exact Hy).
  induction d as [| d IH].
  - replace (Datatypes.S n + 0)%nat with (Datatypes.S n)%nat by lia.
    change (exp_partial (Datatypes.S n) y) with
      (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    (* 除法原子化：ring 不吃 Qdiv 原子（库内同款坑） *)
    set (T := q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    apply qeq_imp_qle. ring.
  - replace (Datatypes.S n + Datatypes.S d)%nat
      with (Datatypes.S (Datatypes.S n + d))%nat by lia.
    change (exp_partial (Datatypes.S (Datatypes.S n + d)) y) with
      (exp_partial (Datatypes.S n + d) y
       + q_pow y (Datatypes.S (Datatypes.S n + d))
         / q_fact (Datatypes.S (Datatypes.S n + d))).
    set (T2 := q_pow y (Datatypes.S (Datatypes.S n + d))
                 / q_fact (Datatypes.S (Datatypes.S n + d))).
    apply (Qle_trans _
             ((exp_partial (Datatypes.S n + d) y - exp_partial n y) + T2)%Q _).
    + (* 首项 ≤ 旧尾差 ≤ 旧尾差 + 非负新项 *)
      apply (Qle_trans _ (exp_partial (Datatypes.S n + d) y - exp_partial n y) _).
      * exact IH.
      * apply qtail_le_plus_r.
        unfold T2. apply q_pow_fact_nonneg. exact Hy0.
    + (* 换形：(E − F) + T2 == E + T2 − F（ring，除法已原子化） *)
      apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* G1② 级数桥：Real 层 e^y ≥ 第 n 部分和（eps/Bishop 形）           *)
(* ============================================================ *)

(* 严格形：y > 0 ⟹ real_const(E_n(y)) < e^y。
   见证 eps := (y^{n+1}/(n+1)!)/2 > 0、N := n+1；逐点差
   E_m(y) − E_n(y) ≥ y^{n+1}/(n+1)! > eps（m ≥ n+1，尾差递增）。 *)
Theorem qtr_exp_gt_partial : forall (y : Q) (n : nat), QltT 0 y ->
  real_lt (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy.
  assert (Hterm : QltT 0 (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
  { apply qltT_div_pos.
    - apply Qlt_to_QltT. apply (cpl_qpow_pos y (Datatypes.S n)).
      apply QltT_to_Qlt. exact Hy.
    - apply Qlt_to_QltT. apply q_fact_pos. }
  unfold real_lt.
  exists (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)%Q.
  split.
  - apply qltT_div_pos.
    + exact Hterm.
    + exact qltT_0_2.
  - exists (Datatypes.S n). intros m Hm.
    assert (Hle : (Datatypes.S n <= m)%nat) by (apply NatLe_drop; exact Hm).
    assert (Hraw : projT1 (cauchy_real_exp (real_const y)) m
                   - projT1 (real_const (exp_partial n y)) m
                   == exp_partial m y - exp_partial n y).
    { apply Qminus_comp.
      - apply exp_const_proj.
      - apply real_const_proj. }
    assert (Hgap : Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
                       (exp_partial m y - exp_partial n y)).
    { replace m with (Datatypes.S n + (m - Datatypes.S n))%nat by lia.
      apply qtr_partial_gap.
      left. exact Hy. }
    assert (HgapT : QltT (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)
                         (exp_partial m y - exp_partial n y)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans _ (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      - apply qtr_div2_lt. apply QltT_to_Qlt. exact Hterm.
      - exact Hgap. }
    apply qltT_eq_compat_r with (a' := (exp_partial m y - exp_partial n y)%Q).
    + exact Hraw.
    + exact HgapT.
Qed.

(* 弱形：y ≥ 0 ⟹ real_const(E_n(y)) ≤ e^y（real_le 三形：
   严格支走级数桥；y == 0 支走全 1 部分和的 real_eq 合同，
   Id 分支经 destruct 收 Qeq）。 *)
Theorem qtr_exp_ge_partial : forall (y : Q) (n : nat), QleT 0 y ->
  real_le (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy. destruct Hy as [Hlt | H0].
  - left. apply qtr_exp_gt_partial. exact Hlt.
  - assert (H0q : 0 == y) by (destruct H0; apply Qeq_refl).
    assert (Hn1 : exp_partial n y == 1%Q).
    { apply Qeq_trans with (y := exp_partial n 0).
      - apply Qeq_sym. apply (cpl_ep_ext n 0 y H0q).
      - apply exp_partial_zero. }
    assert (Hk1 : forall k : nat, exp_partial k y == 1%Q).
    { intro k. apply Qeq_trans with (y := exp_partial k 0).
      - apply Qeq_sym. apply (cpl_ep_ext k 0 y H0q).
      - apply exp_partial_zero. }
    right. intros eps Heps. exists 0%nat. intros k _.
    assert (Habs0 : Qabs (projT1 (real_const (exp_partial n y)) k
                          - projT1 (cauchy_real_exp (real_const y)) k) == 0).
    { apply Qeq_trans with (y := Qabs (1%Q - 1%Q)).
      - apply Qabs_wd.
        apply Qminus_comp.
        + apply Qeq_trans with (y := exp_partial n y).
          * apply real_const_proj.
          * exact Hn1.
        + apply Qeq_trans with (y := exp_partial k y).
          * apply exp_const_proj.
          * apply Hk1.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. ring.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ============================================================ *)
(* G2 核心：real_mult 对 real_eq 的左合同（运输引擎）                *)
(* ============================================================ *)

(* 约分证书已备（qtr_div_cancel）。
   左合同：x ≡ z ⟹ x·v ≡ z·v（real_eq 面）。
   证法：real_norm_bounded 取 |v| ≤ Mv，半额松弛 eps/2：
   |u_n−z_n|·|w_n| ≤ (eps/2/Mv')·Mv' == eps/2 < eps
   （Qmult_le_compat_nonneg + Qmult_inv_r 证书；零除法目标面）。 *)
Lemma qtr_mult_eq_compat_l : forall x z v : Real,
  real_eq x z -> real_eq (real_mult x v) (real_mult z v).
Proof.
  intros [u Hu] [z Hz] [w Hw] Heq eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) w Hw))
    as [Mv [HMvT HMv]].
  set (Mv' := (Qabs Mv + 1)%Q).
  assert (HMv'0 : Qlt 0 Mv').
  { unfold Mv'. setoid_rewrite <- (Qplus_comm 1%Q (Qabs Mv)).
    apply (Qlt_le_trans 0%Q 1%Q).
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (HMv'posT : QltT 0 Mv') by (apply Qlt_to_QltT; exact HMv'0).
  (* 半额放大：以 eps/2 喂 Heq，末段 eps/2 < eps 补严格性 *)
  destruct (Heq (eps / 2 / Mv')
    (qltT_div_pos (eps / 2) Mv'
       (qltT_div_pos eps 2%Q Heps qltT_0_2) HMv'posT)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* HN : QltT |u_n − z_n| (eps/2/Mv') *)
  assert (Hwn : Qle (Qabs (w n)) Mv').
  { apply (Qle_trans _ Mv _).
    - apply (QleT'_to_Qle _ _ (HMv n)).
    - apply (Qle_trans _ (Qabs Mv) _).
      + apply Qle_Qabs.
      + apply Qle_plus_nonneg_r.
        (* 0 <= 1：Qle 展开后 lia（Z 层平凡） *)
        unfold Qle. simpl. lia. }
  assert (Hle2 : Qle (Qabs (u n - z n) * Qabs (w n))
                     ((eps / 2 / Mv') * Mv')).
  { apply (Qmult_le_compat_nonneg (Qabs (u n - z n))
             (eps / 2 / Mv')%Q (Qabs (w n)) Mv').
    - split.
      + apply Qabs_nonneg.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact HN.
    - split.
      + apply Qabs_nonneg.
      + exact Hwn. }
  assert (Hab : Qabs (u n * w n - z n * w n)
                == Qabs (u n - z n) * Qabs (w n)).
  { apply Qeq_trans with (y := Qabs ((u n - z n) * w n)).
    - apply Qabs_wd. ring.
    - apply Qabs_Qmult. }
  assert (Hchain : QltT (Qabs (u n - z n) * Qabs (w n)) eps).
  { apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (eps / 2) eps).
    - apply (Qle_trans _ ((eps / 2 / Mv') * Mv')).
      + exact Hle2.
      + apply qeq_imp_qle.
        apply qtr_div_cancel. apply qtail_neq0. exact HMv'0.
    - apply qtr_div2_lt.
      apply QltT_to_Qlt. exact Heps. }
  apply qltT_eq_compat_l with (a := Qabs (u n - z n) * Qabs (w n)).
  - apply Qeq_sym. exact Hab.
  - exact Hchain.
Qed.

(* ============================================================ *)
(* G2 主件：Padé 精度 Real 层下界首件（检验值任取）                    *)
(* ============================================================ *)

(* y > 0、w ≡ e^y（real_eq 意义下任意 Real 检验值）⟹
   P₂(y) < w·Q₂(y)（乘开免除法形）。
   运输路径：cpl_lower_even（特定对角见证）→ real_lt_eq_lt +
   real_mult 左合同（qtr_mult_eq_compat_l）→ 任意检验值。 *)
Theorem qtr_pade_lower_real : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw.
  apply (real_lt_eq_lt _ _ _ (cpl_lower_even y Hy)).
  apply qtr_mult_eq_compat_l.
  apply real_eq_sym. exact Hw.
Qed.

(* ============================================================ *)
(* G2b 反桥：real_lt 证书解包为显式 N/eps 的逐点 QltT 形              *)
(* （eps/Bishop 见证反射：Real 层语句 ⟹ 逐点 Q 层精度账；            *)
(*   N/eps 由 cpl 的 sigT 见证原样透传：y⁵/720、N := 6）             *)
(* ============================================================ *)

Theorem qtr_pade_lower_extract : forall y : Q, QltT 0 y ->
  sigT (fun N : nat => sigT (fun eps : Q => And (QltT 0 eps)
    (forall m : nat, NatLe N m ->
      QltT eps (exp_partial m y * pade_den 2%nat y
                - pade_num 2%nat y)%Q))).
Proof.
  intros y Hy.
  destruct (cpl_lower_even y Hy) as [eps [Heps [N HN]]].
  exists N. exists eps. split.
  - exact Heps.
  - intros m Hm.
    specialize (HN m Hm).
    assert (Hmult : projT1 (real_mult (cauchy_real_exp (real_const y))
                                      (real_const (pade_den 2%nat y))) m
                    == exp_partial m y * pade_den 2%nat y).
    { apply Qeq_trans with
        (y := projT1 (cauchy_real_exp (real_const y)) m
              * projT1 (real_const (pade_den 2%nat y)) m).
      - apply real_mult_proj.
      - apply Qmult_comp.
        + apply exp_const_proj.
        + apply real_const_proj. }
    assert (Hconst : projT1 (real_const (pade_num 2%nat y)) m
                     == pade_num 2%nat y).
    { apply real_const_proj. }
    assert (Hraw : projT1 (real_mult (cauchy_real_exp (real_const y))
                                     (real_const (pade_den 2%nat y))) m
                   - projT1 (real_const (pade_num 2%nat y)) m
                   == exp_partial m y * pade_den 2%nat y
                      - pade_num 2%nat y).
    { apply Qminus_comp.
      - exact Hmult.
      - exact Hconst. }
    exact (qltT_eq_compat_r _ _ _ (Qeq_sym _ _ Hraw) HN).
Qed.

(* 弱形补全（real_le 三形）：y > 0、w ≡ e^y ⟹ P₂(y) ≤ w·Q₂(y)。 *)
Theorem qtr_pade_lower_real_le : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_le (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw. left.
  apply (qtr_pade_lower_real y w Hy Hw).
Qed.

(* ============================================================ *)
(* 认证面（公理面：预期全员 Closed）                                *)
(* ============================================================ *)

Print Assumptions qtr_embed_mono.
Print Assumptions qtr_embed_le.
Print Assumptions qtr_partial_gap.
Print Assumptions qtr_exp_gt_partial.
Print Assumptions qtr_exp_ge_partial.
Print Assumptions qtr_mult_eq_compat_l.
Print Assumptions qtr_pade_lower_real.
Print Assumptions qtr_pade_lower_extract.
Print Assumptions qtr_pade_lower_real_le.
