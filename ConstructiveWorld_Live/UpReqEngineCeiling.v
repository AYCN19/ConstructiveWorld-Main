(* ============================================================
   UpReqEngineCeiling.v —— 引擎族常数天花板 Q 层定理（前缀 cec_）。
   ── 使命：① cec_H_lower：调和数下界——k≥5 ⟹ H_k − 1/(k+1) ≥ 2
   （QleT' Set 面；归纳：单调步 (k+3)/((k+1)(k+2)) > 0＋基例 k=5 精确
   分数 127/60 ≥ 2，fractions 锁形）。② cec_trunc_sup：截断引擎族
   天花板 c*(k) = min(H_k−1/(k+1), 2) 的 min 分段形——k=1..4 逐角点
   精确值 1/2, 7/6, 19/12, 113/60 四条＋k≥5 段 =2 一条，五条全 Qeq
   And 合取（repeat apply conj）。③ cec_kernel_coef：R6 嵌套切线族
   k 阶核二阶系数 = −(k+1)/(2k)（经抽象二项反演引理 cec_inv2 承载；
   系数指纹 (k+1)/(2k) > 1/2 对一般 k 无条件）。④ cec_tangent_ceiling：
   嵌套切线族天花板 2(k−1)/k < 2 严格（k 有限 ⟹ 缺口 2/k > 0；
   QltT Set 面＋cec_tangent_gap 恒等式 2 − 2m/(m+1) == 2/(m+1)）。
   ── 数学内核（python fractions 全量精确复核，含 492 样本 ρ 抽检）：
   f(k) := H_k − 1/(k+1)；f(k+1) − f(k) = (k+3)/((k+1)(k+2)) > 0；
   f(5) = 127/60 > 2 ⟹ k≥5 段 min(f,2) = 2。cec_inv2：凡 s = a·v +
   b·v² + v³w（a>0, s≠0）的引擎，其像 a·v 的 s² 系数恰为 −b/a²；
   R6 实例化 a=k, b=k(k+1)/2 ⟹ b/a² = (k+1)/(2k)。
   ── 替换声明：cec_tangent_le／cec_H_lower／cec_div_same_denom_lt／
   cec_mult_neq0／cec_neq_of_pos 五槽证明体替换为直接构造证，余面零改。
   ── 诚实边界：cec_kernel_coef 一般 k 形以参数化恒等式
   s == k·v + k(k+1)/2·v² + v³w 为显式假设（条件形），k=1 无条件实例全闭。
   ── 依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp；Stdlib
   QArith（QArith/Qring/Qabs/Qminmax）、Lists.List、Bool.Bool、
   Arith.Arith、Setoid、Morphisms、Lia。
   ── 构造性注记：纯构造性；Q 层 Qeq＋QleT'/QltT 纪律——Set 面件零
   And 混装；非零性统一 Qeq 面 ≠（闭法 cec_nz）；非平凡真实现
   （cec_inv2 为抽象反演引擎非重述）；零公理、全 Qed 闭合。
   ── 编译配方：coqc -q -native-compiler no -Q . "" UpReqEngineCeiling.v
   （9.1 工具链；COQLIB=ROCQLIB=C:/Rocq-Platform~9.1~2026.01/lib/coq）。
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qabs
               Lists.List Bool.Bool Arith.Arith.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.

(* ---- 0. 通用小件（Q 层地基，全部 cec_ 前缀） ---- *)

(* Z.of_nat (n+1) # 1 > 0（Q 层正性；lia 走 Nat2Z） *)
Lemma cec_nat_pos : forall n : nat, Qlt 0 (Z.of_nat (n + 1) # 1).
Proof. intro n. unfold Qlt. simpl. lia. Qed.

Lemma cec_nat_pos0 : forall n : nat, (1 <= n)%nat -> Qlt 0 (Z.of_nat n # 1).
Proof. intros n Hn. unfold Qlt. simpl. lia. Qed.

(* Qeq 面非零性（S03 q_neq_of_lt 同款：field 侧条件实测为 ~ (x == 0)） *)
Lemma cec_neq_of_pos : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof. exact S03_QExp.q_neq_of_lt. Qed.

(* 乘积非零（Qeq 面；Qmult_integral_l 本为 Qeq 面） *)
Lemma cec_mult_neq0 : forall x y : Q, ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0).
Proof.
  intros x y Hx Hy H.
  apply Hy.
  exact (Qmult_integral_l x y Hx H).
Qed.

(* field 侧条件统一闭法：实测 field 产出合取 ~ d == 0 /\ ...（S03 split 同款）；
   闭法：split 分裂 / 假设直取 / 乘积分裂 / 正性 lia（全 Qeq 面） *)
Ltac cec_nz :=
  repeat first
    [ assumption
    | split; cec_nz
    | apply cec_mult_neq0; cec_nz
    | apply cec_neq_of_pos; (assumption || (unfold Qlt; simpl; lia)) ].

(* 倒数正性（按 Qnum 三分构造；Qinv 定义面） *)
Lemma cec_inv_pos : forall x : Q, Qlt 0 x -> Qlt 0 (/ x).
Proof.
  intros x Hx. destruct x as [a b]. unfold Qlt in Hx. simpl in Hx.
  destruct a.
  - lia.
  - unfold Qlt. simpl. lia.
  - lia.
Qed.

Lemma cec_inv_mult_pos : forall x y : Q, Qlt 0 x -> Qlt 0 y -> Qlt 0 (/ (x * y)).
Proof.
  intros x y Hx Hy. rewrite Qinv_mult_distr.
  apply Qmult_lt_0_compat; apply cec_inv_pos; assumption.
Qed.

(* x + y ≥ x（供归纳单调步；Qplus_le_r 为 iff 形不便直用，自证） *)
Lemma cec_plus_r_le : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy. apply (Qle_trans x (x + 0) (x + y)).
  - apply qeq_imp_qle. rewrite Qplus_0_r. apply Qeq_refl.
  - apply (Qplus_le_compat x x 0 y); [apply Qle_refl | exact Hy].
Qed.

(* 自己的 min（Qle_bool 反映形，与 QleT' 同基；避免 stdlib Qminmax 名漂移） *)
Definition cec_min (x y : Q) : Q := if Qle_bool x y then x else y.

Lemma cec_min_ge : forall x y : Q, Qle y x -> cec_min x y == y.
Proof.
  intros x y Hyx. unfold cec_min. destruct (Qle_bool x y) eqn:E.
  - apply Qle_antisym; [| exact Hyx].
    apply (QleT'_to_Qle x y). unfold QleT'. rewrite E. exact id_refl.
  - reflexivity.
Qed.

(* 同分母严格除比较（Qmult_lt_compat_r 的 /e 槽：倒数正性桥） *)
Lemma cec_div_same_denom_lt : forall a c e : Q,
  Qlt 0 e -> Qlt a c -> Qlt (a / e) (c / e).
Proof.
  intros a c e He Hac.
  unfold Qdiv.
  apply (Qmult_lt_compat_r _ _ _ (cec_inv_pos e He) Hac).
Qed.

(* 跨分母严格除比较：a*d < c*b, b,d > 0 ⟹ a/b < c/d *)
Lemma cec_lt_div_lt : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qlt (a * d) (c * b) -> Qlt (a / b) (c / d).
Proof.
  intros a b c d Hb Hd H.
  assert (E1 : a / b == (a * d) / (b * d)) by (field; cec_nz).
  assert (E2 : c / d == (c * b) / (b * d)) by (field; cec_nz).
  rewrite E1, E2.
  apply cec_div_same_denom_lt.
  - apply Qmult_lt_0_compat; assumption.
  - exact H.
Qed.

(* ---- 1. 调和数与角点常数（G1 地基） ---- *)

(* H_k := Σ_{j=1..k} 1/j（内项统一 n+1 形，防 S k 的 Z 形错位） *)
Fixpoint cec_H (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => cec_H m + ((1 # 1) / (Z.of_nat (m + 1) # 1))
  end.

(* 角点常数 f(k) := H_k − 1/(k+1)（EXP-D1 T1 角点极限的 Q 层精确形） *)
Definition cec_pt (k : nat) : Q := cec_H k - ((1 # 1) / (Z.of_nat (k + 1) # 1)).

(* 四个角点精确值（EXP-D1 表：1/2, 7/6, 19/12, 113/60） *)
Lemma cec_pt_1 : cec_pt 1 == (1 # 2).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_2 : cec_pt 2 == (7 # 6).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_3 : cec_pt 3 == (19 # 12).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_pt_4 : cec_pt 4 == (113 # 60).
Proof. vm_compute. reflexivity. Qed.

(* 单调步的显式增量（fractions 验证：f(k+1) − f(k) = (k+3)/((k+1)(k+2))） *)
Lemma cec_pt_step_eq : forall k : nat,
  cec_pt (Datatypes.S k) ==
  cec_pt k + ((Z.of_nat (k + 3) # 1) / ((Z.of_nat (k + 1) # 1) * (Z.of_nat (k + 2) # 1))).
Proof.
  intro k.
  (* S n / n+c 的 Z 形统一（lia zify 直吃，Nat2Z 名漂移零依赖） *)
  assert (EA : forall n : nat, (Z.of_nat (Datatypes.S n) # 1) == (Z.of_nat n # 1) + (1 # 1)).
  { intro n. unfold Qeq, Qplus. simpl. lia. }
  assert (EB0 : (Z.of_nat (k + 1) # 1) == (Z.of_nat k # 1) + (1 # 1)).
  { unfold Qeq, Qplus. simpl. lia. }
  assert (EB1 : (Z.of_nat (k + 2) # 1) == (Z.of_nat k # 1) + ((1 # 1) + (1 # 1))).
  { unfold Qeq, Qplus. simpl. lia. }
  assert (EB2 : (Z.of_nat (k + 3) # 1) == (Z.of_nat k # 1) + ((1 # 1) + ((1 # 1) + (1 # 1)))).
  { unfold Qeq, Qplus. simpl. lia. }
  unfold cec_pt.
  change ((Datatypes.S k + 1)%nat) with (Datatypes.S (k + 1)).
  rewrite (EA (k + 1)%nat).
  cbn [cec_H].
  rewrite EB0.
  rewrite EB1, EB2.
  field; cec_nz.
Qed.

Lemma cec_pt_step_pos : forall k : nat,
  Qlt 0 ((Z.of_nat (k + 3) # 1) / ((Z.of_nat (k + 1) # 1) * (Z.of_nat (k + 2) # 1))).
Proof.
  intro k. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply (cec_nat_pos0 (k + 3)%nat). lia.
  - apply cec_inv_mult_pos.
    + apply (cec_nat_pos0 (k + 1)%nat). lia.
    + apply (cec_nat_pos0 (k + 2)%nat). lia.
Qed.

(* 基例：f(5) = 127/60（fractions 精确）且 > 2 *)
Lemma cec_pt_5 : cec_pt 5 == (127 # 60).
Proof. vm_compute. reflexivity. Qed.

Lemma cec_two_lt_127_60 : Qlt (1 + 1)%Q (127 # 60).
Proof. unfold Qlt. simpl. lia. Qed.

(* 严格下界归纳：k ≥ 5 ⟹ 2 < f(k)（严格版，供 min 段取 2） *)
Lemma cec_pt_gt2 : forall k : nat, (5 <= k)%nat -> Qlt (1 + 1)%Q (cec_pt k).
Proof.
  induction k as [| m IH]; intro Hk.
  - lia.
  - destruct (Nat.eq_dec m 4) as [E4 | Hne].
    + subst m. rewrite cec_pt_5. apply cec_two_lt_127_60.
    + assert (Hm5 : (5 <= m)%nat) by lia.
      specialize (IH Hm5).
      assert (Hstep : Qle (cec_pt m) (cec_pt (Datatypes.S m))).
      { pose proof (cec_pt_step_pos m) as Hp.
        pose proof (cec_pt_step_eq m) as E.
        rewrite E.
        apply (cec_plus_r_le (cec_pt m)
                ((Z.of_nat (m + 3) # 1) /
                 ((Z.of_nat (m + 1) # 1) * (Z.of_nat (m + 2) # 1)))).
        apply Qlt_le_weak. exact Hp. }
      apply (Qlt_le_trans (1 + 1)%Q (cec_pt m) (cec_pt (Datatypes.S m)) IH Hstep).
Qed.

(* G1 主件：调和数下界引理（QleT' Set 面，独立成件零 And 混装） *)
Theorem cec_H_lower : forall k : nat, (5 <= k)%nat -> QleT' (1 + 1)%Q (cec_pt k).
Proof.
  intros k Hk.
  exact (Qle_to_QleT' (1 + 1)%Q (cec_pt k)
    (Qlt_le_weak (1 + 1)%Q (cec_pt k) (cec_pt_gt2 k Hk))).
Qed.


(* ---- 2. 截断引擎族天花板 c*(k) = min(H_k − 1/(k+1), 2)（G2a） ---- *)

Definition cec_cstar (k : nat) : Q := cec_min (cec_pt k) (1 + 1)%Q.

(* k≥5 段：min(f(k), 2) = 2（由严格下界经 min_ge 取右枝） *)
Theorem cec_cstar_tail : forall k : nat, (5 <= k)%nat -> cec_cstar k == (1 + 1)%Q.
Proof.
  intros k Hk. unfold cec_cstar. apply cec_min_ge.
  apply Qlt_le_weak. apply cec_pt_gt2. exact Hk.
Qed.

(* 五条 min 分段账（全 Qeq Prop And；Q2 卡：repeat apply conj 防转换穿透） *)
Theorem cec_trunc_sup :
  cec_cstar 1 == (1 # 2) /\
  cec_cstar 2 == (7 # 6) /\
  cec_cstar 3 == (19 # 12) /\
  cec_cstar 4 == (113 # 60) /\
  (forall k : nat, (5 <= k)%nat -> cec_cstar k == (1 + 1)%Q).
Proof.
  repeat apply conj.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - exact cec_cstar_tail.
Qed.

(* ---- 3. R6 嵌套切线族核二阶系数 −(k+1)/(2k)（G2b） ---- *)

(* 抽象二项反演引擎：s = a·v + b·v² + v³w ⟹ a·v 的 s² 系数恰 −b/a²，
   残差 s³·ρ 显式（ρ 分母 (a+bv+v²w)³ 在 v=0 取值 a³≠0，正则性可见；
   python fractions 492 样本抽检恒等式为零）。 *)
Definition cec_smap (a b w v : Q) : Q := a * v + b * v * v + v * v * v * w.

Definition cec_rho (a b w v : Q) : Q :=
  (((2 * b * b / a - w) + (b * (b * b + (1 + 1)%Q * a * w) / (a * a)) * v
    + ((1 + 1)%Q * b * b * w / (a * a)) * v * v
    + (b * w * w / (a * a)) * v * v * v)
   / ((a + b * v + v * v * w)
      * ((a + b * v + v * v * w) * (a + b * v + v * v * w)))).

Lemma cec_inv2 : forall (a b w v : Q),
  Qlt 0 a -> ~ (cec_smap a b w v == 0) ->
  Qeq (a * v)
      (cec_smap a b w v - (b / (a * a)) * (cec_smap a b w v * cec_smap a b w v)
       + cec_smap a b w v * cec_smap a b w v * cec_smap a b w v
         * cec_rho a b w v).
Proof.
  intros a b w v Ha Hs.
  assert (Ha0 : ~ (a == 0)) by (apply cec_neq_of_pos; exact Ha).
  assert (Hden : ~ ((a + b * v + v * v * w) == 0)).
  { intro Hd. apply Hs. unfold cec_smap.
    assert (Ef : a * v + b * v * v + v * v * v * w == v * (a + b * v + v * v * w)) by ring.
    rewrite Ef, Hd. ring. }
  unfold cec_smap, cec_rho.
  field; cec_nz.
Qed.

(* R6 族的 a, b, 系数：a = k，b = k(k+1)/2，|系数| = b/a² = (k+1)/(2k) *)
Definition cec_r6_s (k : nat) (v : Q) : Q := (1 # 1) / q_pow (1 - v) k - (1 # 1).
Definition cec_r6_bcoef (k : nat) : Q :=
  ((Z.of_nat k # 1) * ((Z.of_nat k # 1) + 1)) / ((1 + 1)%Q).
Definition cec_r6_coef (k : nat) : Q :=
  ((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)).

Lemma cec_bcoef_div_a2 : forall k : nat, (1 <= k)%nat ->
  cec_r6_bcoef k / ((Z.of_nat k # 1) * (Z.of_nat k # 1)) == cec_r6_coef k.
Proof.
  intros k Hk. unfold cec_r6_bcoef, cec_r6_coef.
  field; cec_nz.
Qed.

(* R6 指纹（一般 k 无条件）：(k+1)/(2k) > 1/2 ——「每支亏 1/(2k)」的族推广 *)
Lemma cec_coef_fingerprint : forall k : nat, (1 <= k)%nat -> Qlt (1 # 2) (cec_r6_coef k).
Proof.
  intros k Hk. unfold cec_r6_coef.
  apply (cec_lt_div_lt (1 # 1) ((1 + 1)%Q) ((Z.of_nat k # 1) + 1)
                       ((1 + 1)%Q * (Z.of_nat k # 1))).
  - unfold Qlt. simpl. lia.
  - apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply (cec_nat_pos0 k Hk)].
  - (* Qmult 在 Qplus 参数上卡 match；ring 只证多项式恒等式（Qmake(Z和) 是
     不透明原子），故把交叉积归到原子 z#1 的加法多项式形再 unfold+lia *)
    assert (E1 : (1 # 1) * (((1 + 1)%Q) * (Z.of_nat k # 1))
                 == (Z.of_nat k # 1) + (Z.of_nat k # 1)) by ring.
    assert (E2 : ((Z.of_nat k # 1) + 1) * ((1 + 1)%Q)
                 == ((Z.of_nat k # 1) + (Z.of_nat k # 1)) + ((1 + 1)%Q)) by ring.
    rewrite E1, E2.
    unfold Qlt. simpl. lia.
Qed.

(* R6 指纹上侧：|系数| = (k+1)/(2k) ≤ 1 *)
Lemma cec_coef_le_1 : forall k : nat, (1 <= k)%nat -> Qle (cec_r6_coef k) (1 # 1).
Proof.
  intros k Hk. unfold cec_r6_coef.
  change (Qle (((Z.of_nat k # 1) + 1) / ((1 + 1)%Q * (Z.of_nat k # 1)))
              ((1 # 1) / (1 # 1))).
  apply (S03_QExp.q_le_div_le ((Z.of_nat k # 1) + 1)
            ((1 + 1)%Q * (Z.of_nat k # 1)) (1 # 1) (1 # 1)).
  - apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply (cec_nat_pos0 k Hk)].
  - unfold Qlt. simpl. lia.
  - assert (E1 : ((Z.of_nat k # 1) + 1) * (1 # 1)
                 == (Z.of_nat k # 1) + (1 # 1)) by ring.
    assert (E2 : (1 # 1) * (((1 + 1)%Q) * (Z.of_nat k # 1))
                 == (Z.of_nat k # 1) + (Z.of_nat k # 1)) by ring.
    rewrite E1, E2.
    unfold Qle. simpl. lia.
Qed.

(* G2b 主件（一般 k 条件形：参数化恒等式为显式假设，诚实登记未决项） *)
Theorem cec_kernel_coef : forall (k : nat) (v w : Q), (1 <= k)%nat ->
  ~ (cec_r6_s k v == 0) ->
  cec_r6_s k v == (Z.of_nat k # 1) * v + cec_r6_bcoef k * v * v + v * v * v * w ->
  Qeq ((Z.of_nat k # 1) * v)
      (cec_r6_s k v - cec_r6_coef k * (cec_r6_s k v * cec_r6_s k v)
       + cec_r6_s k v * cec_r6_s k v * cec_r6_s k v
         * cec_rho (Z.of_nat k # 1) (cec_r6_bcoef k) w v).
Proof.
  intros k v w Hk Hs Hpar.
  assert (Ha : Qlt 0 (Z.of_nat k # 1)) by (apply (cec_nat_pos0 k Hk)).
  assert (E : cec_r6_s k v == cec_smap (Z.of_nat k # 1) (cec_r6_bcoef k) w v).
  { unfold cec_smap. exact Hpar. }
  assert (Hs2 : ~ (cec_smap (Z.of_nat k # 1) (cec_r6_bcoef k) w v == 0)).
  { intro H0. apply Hs. rewrite E. exact H0. }
  pose proof (cec_inv2 (Z.of_nat k # 1) (cec_r6_bcoef k) w v Ha Hs2) as H.
  rewrite <- E in H.
  rewrite cec_bcoef_div_a2 in H by exact Hk.
  exact H.
Qed.

(* k=1 无条件参数化（field 全闭）：1/(1−v) − 1 == v + v² + v³/(1−v) *)
Lemma cec_r6_param_k1 : forall v : Q, ~ ((1 # 1) - v == 0) ->
  cec_r6_s 1 v == (1 # 1) * v + cec_r6_bcoef 1 * v * v + v * v * v * ((1 # 1) / (1 - v)).
Proof.
  intros v Hv. unfold cec_r6_s, cec_r6_bcoef.
  cbn [q_pow].
  field; cec_nz.
Qed.

(* k=1 无条件系数实例：s² 系数 = −cec_r6_coef 1 = −1 = −(1+1)/(2·1) *)
Theorem cec_kernel_coef_k1 : forall v : Q, ~ ((1 # 1) - v == 0) ->
  ~ (cec_r6_s 1 v == 0) ->
  Qeq ((1 # 1) * v)
      (cec_r6_s 1 v - cec_r6_coef 1 * (cec_r6_s 1 v * cec_r6_s 1 v)
       + cec_r6_s 1 v * cec_r6_s 1 v * cec_r6_s 1 v
         * cec_rho (1 # 1) (cec_r6_bcoef 1) ((1 # 1) / (1 - v)) v).
Proof.
  intros v Hv Hs.
  apply (cec_kernel_coef 1 v ((1 # 1) / (1 - v))).
  - lia.
  - exact Hs.
  - apply cec_r6_param_k1. exact Hv.
Qed.

(* 教科书字面形（s 变量，s/(1+s) = s − s² + s³/(1+s)，系数 −1 恰） *)
Lemma cec_kernel_coef_literal_s : forall s : Q, ~ ((s + (1 # 1)) == 0) ->
  Qeq (s / (s + (1 # 1)))
      (s - (1 # 1) * (s * s) + s * s * s * ((1 # 1) / (s + (1 # 1)))).
Proof.
  intros s Hs. field; cec_nz.
Qed.

(* ---- 4. 嵌套切线族天花板 2(k−1)/k < 2 严格（G2c） ---- *)

Definition cec_tg (m : nat) : Q :=
  ((1 + 1)%Q * (Z.of_nat m # 1)) / (Z.of_nat (m + 1) # 1).

(* 严格天花板（QltT Set 面）：2m/(m+1) < 2 ⟸ 2m < 2(m+1) *)
Theorem cec_tangent_ceiling : forall m : nat, QltT (cec_tg m) (1 + 1)%Q.
Proof.
  intro m. apply Qlt_to_QltT.
  apply (cec_lt_div_lt ((1 + 1)%Q * (Z.of_nat m # 1)) (Z.of_nat (m + 1) # 1)
                       (1 + 1)%Q (1 # 1)).
  - apply (cec_nat_pos m).
  - unfold Qlt. simpl. lia.
  - assert (E1 : (((1 + 1)%Q * (Z.of_nat m # 1)) * (1 # 1))
                 == (Z.of_nat m # 1) + (Z.of_nat m # 1)) by ring.
    assert (E2 : ((1 + 1)%Q * (Z.of_nat (m + 1) # 1))
                 == (Z.of_nat (m + 1) # 1) + (Z.of_nat (m + 1) # 1)) by ring.
    rewrite E1, E2.
    unfold Qlt. simpl. lia.
Qed.

(* QleT' 影子件（Set 面 ≤ 形） *)
Theorem cec_tangent_le : forall m : nat, QleT' (cec_tg m) (1 + 1)%Q.
Proof.
  intro m. exact (qltT_leT' (cec_tg m) (1 + 1)%Q (cec_tangent_ceiling m)). Qed.

(* 缺口恒等式：2 − 2m/(m+1) == 2/(m+1)（缺口恰 2/k 的 Q 层精确形） *)
Theorem cec_tangent_gap : forall m : nat,
  (1 + 1)%Q - cec_tg m == ((1 + 1)%Q) / (Z.of_nat (m + 1) # 1).
Proof.
  intro m. unfold cec_tg.
  (* 先统一 Z 形：z_{m+1} ≡ z_m + 1（lia 桥），化单原子后 field 收 *)
  assert (EB : (Z.of_nat (m + 1) # 1) == (Z.of_nat m # 1) + (1 # 1)).
  { unfold Qeq, Qplus. simpl. lia. }
  rewrite EB.
  field; cec_nz.
Qed.

(* ---- 5. 公理面审计 ---- *)

Print Assumptions cec_trunc_sup.
Print Assumptions cec_H_lower.
Print Assumptions cec_kernel_coef.
Print Assumptions cec_kernel_coef_k1.
Print Assumptions cec_tangent_ceiling.
Print Assumptions cec_tangent_gap.
