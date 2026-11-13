(* ==========================================================================)
   UpReqQExpTail.v — Q 指数尾和的 Cauchy 模量
   使命: qtail_sum 簇（尾和非负/单调/几何上界）、qtail_term_decay（项衰减）、qtail_cauchy_modulus 及 ord 形（Cauchy 模量的显式构造）、qtail_ratio_chain（比率链）。
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp；Stdlib QArith、Setoid、Morphisms、Lia、QArith.Qminmax。
   对标: 指数衰减级数尾和的控制与 Cauchy 模量（收敛性构造）。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith Arith.Factorial.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms Lia QArith.Qminmax.

(* ================= S2-nat 引擎 ================= *)

Lemma qtail_two_pow_ge : forall t : nat, (Datatypes.S t <= 2 ^ t)%nat.
Proof.
  induction t as [| t IH]; simpl; lia.
Qed.

(* 阶乘压倒 2 的幂（nat 归纳；4! = 24 ≥ 16 = 2^4 起步） *)
Lemma qtail_fact_ge_pow : forall k : nat, (4 <= k)%nat -> (2 ^ k <= fact k)%nat.
Proof.
  induction k as [| k IH]; intro Hk.
  - lia.
  - assert (H1 : (2 ^ Datatypes.S k = 2 * 2 ^ k)%nat) by reflexivity.
    assert (H2 : (fact (Datatypes.S k)
                  = Datatypes.S k * fact k)%nat) by reflexivity.
    rewrite H1, H2.
    destruct (Nat.eq_dec k 3%nat) as [Hk3 | Hkne].
    + subst k. simpl. lia.
    + assert (Hk4 : (4 <= k)%nat) by lia.
      specialize (IH Hk4).
      apply Nat.mul_le_mono.
      * lia.
      * exact IH.
Qed.

(* ================= Q 侧小引擎（Prop 内核） ================= *)

Lemma qtail_Qlt01 : Qlt 0 1.
Proof.
  unfold Qlt. cbn [Qnum Qden].
  (* 目标即 Z 严格序 0·den(1) < 1·den(0)：乘法以 Z.mul_0_l/Z.mul_1_l    *)
  (* 显式归约，余下 0 < 1 由 1 的正性见证 Pos2Z.is_pos 构造             *)
  rewrite Z.mul_0_l, Z.mul_1_l.
  exact (Pos2Z.is_pos 1%positive).
Qed.

Lemma qtail_neq0 : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof. intros x H. apply (q_neq_of_lt x). exact H. Qed.

Lemma qtail_neq0_mul : forall v s : Q, ~ (v == 0) -> ~ (s == 0) -> ~ (v * s == 0).
Proof.
  intros v s Hv Hs Hz.
  exact (Hs (Qmult_integral_l v s Hv Hz)).
Qed.

(* 除法裂积：(u·r)/(v·s) == (u/v)·(r/s) *)
Lemma qtail_div_split : forall u v r s : Q,
  ~ (v == 0) -> ~ (s == 0) -> (u * r) / (v * s) == (u / v) * (r / s).
Proof.
  intros u v r s Hv Hs.
  assert (Hvs : ~ (v * s == 0)) by (apply qtail_neq0_mul; assumption).
  field. repeat split; assumption.
Qed.

Lemma qtail_QleT_to_Qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [H | H].
  - apply (Qlt_le_weak x y). apply (QltT_to_Qlt x y). exact H.
  - apply qeq_le. destruct H. reflexivity.
Qed.

Lemma qtail_le_plus_r : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy.
  apply (Qle_trans x (x + 0) (x + y)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat x x 0 y).
    + apply Qle_refl.
    + exact Hy.
Qed.

(* x ≥ 0 ⟹ x ≤ (Z.of_nat (Z.to_nat (Qnum x)))#1（显式数值上界，可计算） *)
Lemma qtail_pos_upper : forall x : Q, Qle 0 x -> Qle x (Z.of_nat (Z.to_nat (Qnum x)) # 1).
Proof.
  intros x Hx. destruct x as [n d]. simpl.
  assert (Hn : (0 <= n)%Z).
  { unfold Qle in Hx. simpl in Hx. lia. }
  replace (Z.of_nat (Z.to_nat n)) with n by lia.
  unfold Qle.
  apply Z.mul_le_mono_nonneg_l.
  - exact Hn.
  - assert (H1 : (1 <= Z.pos d)%Z) by (induction d as [p IHp | p IHp | ]; simpl; lia).
    exact H1.
Qed.

(* 2^t 的显式 Q 表示分母正（field 副目标复用） *)
Lemma qtail_pow2_denom_pos : forall t : nat, Qlt 0 (Z.of_nat (2 ^ t) # 1).
Proof.
  intro t.
  assert (Hp : (0 < 2 ^ t)%nat)
    by (apply (proj1 (Nat.neq_0_lt_0 (2 ^ t))); apply Nat.pow_nonzero; lia).
  unfold Qlt. simpl. lia.
Qed.

(* (1/2)^t ≤ 1/(t+1)：由 2^t ≥ t+1 显式推出 *)
Lemma qtail_half_pow_le_invT : forall t : nat,
  Qle (q_pow (1 / 2) t) (1 / (Z.of_nat (Datatypes.S t) # 1)).
Proof.
  intro t.
  assert (H2pos : (0 < 2 ^ t)%nat).
  { apply (proj1 (Nat.neq_0_lt_0 (2 ^ t))).
    apply Nat.pow_nonzero. lia. }
  assert (E : forall t0 : nat, q_pow (1 / 2) t0 == 1 / (Z.of_nat (2 ^ t0) # 1)).
  { intro t0. induction t0 as [| t0 IH].
    - reflexivity.
    - rewrite (q_pow_succ (1 / 2) t0), IH.
      assert (Hz2 : (2 ^ Datatypes.S t0 = 2 * 2 ^ t0)%nat) by reflexivity.
      rewrite Hz2.
      assert (Hb : (0 < Z.of_nat (2 ^ t0))%Z).
      { assert (Hp : (0 < 2 ^ t0)%nat)
          by (apply (proj1 (Nat.neq_0_lt_0 (2 ^ t0))); apply Nat.pow_nonzero; lia).
        lia. }
      assert (HZ : ((Z.of_nat (2 * 2 ^ t0)) # 1
                    == (((Z.of_nat (2 ^ t0)) # 1) + ((Z.of_nat (2 ^ t0)) # 1)))%Q)
        by (unfold Qeq; simpl; lia).
      rewrite HZ.
      field.
      repeat split;
        first [ assumption
              | apply qtail_neq0; unfold Qlt; simpl; lia ]. }
  rewrite (E t).
  apply (q_le_div_le 1 (Z.of_nat (2 ^ t) # 1) 1 (Z.of_nat (Datatypes.S t) # 1)).
  - apply (Qlt_of_nat_lt 0 (2 ^ t)). exact H2pos.
  - apply (Qlt_of_nat_lt 0 (Datatypes.S t)). lia.
  - setoid_replace (1 * (Z.of_nat (Datatypes.S t) # 1))
      with (Z.of_nat (Datatypes.S t) # 1) by ring.
    setoid_replace (1 * (Z.of_nat (2 ^ t) # 1))
      with (Z.of_nat (2 ^ t) # 1) by ring.
    apply (Qle_of_nat (Datatypes.S t) (2 ^ t)).
    exact (qtail_two_pow_ge t).
Qed.

(* 严格交叉乘：a·d < c·b ⟹ a/b < c/d（分母正） *)
Lemma qtail_div_lt : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qlt (a * d) (c * b) -> Qlt (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hcore.
  assert (Hnb : ~ (b == 0)) by (apply qtail_neq0; exact Hb).
  assert (Hnd : ~ (d == 0)) by (apply qtail_neq0; exact Hd).
  assert (Hle : Qle (a / b) (c / d)).
  { apply (q_le_div_le a b c d).
    - exact Hb.
    - exact Hd.
    - apply (Qlt_le_weak _ _ Hcore). }
  destruct (Qle_lt_or_eq _ _ Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso.
    assert (Hs : (a / b) * (b * d) == (c / d) * (b * d)) by (rewrite Heq; reflexivity).
    assert (E1 : (a / b) * (b * d) == a * d) by (field; repeat split; assumption).
    assert (E2 : (c / d) * (b * d) == c * b) by (field; repeat split; assumption).
    rewrite E1 in Hs. rewrite E2 in Hs.
    exact (Qlt_not_eq _ _ Hcore Hs).
Qed.

(* 0 < u, 0 < v ⟹ 0 < u/v *)
Lemma qtail_div_pos : forall u v : Q, Qlt 0 u -> Qlt 0 v -> Qlt 0 (u / v).
Proof.
  intros u v Hu Hv.
  assert (Hcore : Qlt (0 * v) (u * 1)).
  { apply (Qle_lt_trans (0 * v) (0 * 1) (u * 1)).
    - apply qeq_le. ring.
    - apply (Qmult_lt_compat_r 0 u 1).
      + apply qtail_Qlt01.
      + exact Hu. }
  apply (qtail_div_lt 0 1 u v).
  - apply qtail_Qlt01.
  - exact Hv.
  - exact Hcore.
Qed.

(* 本平台无 Qmult_le_compat_l/Qmult_lt_compat_l，以 r 变体 + qeq 环收尾自建 *)
Lemma qtail_mult_le_compat_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H1 H2.
  apply (Qle_trans _ (x * z)).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (y * z)).
    + apply (Qmult_le_compat_r x y z).
      * exact H1.
      * exact H2.
    + apply qeq_le. ring.
Qed.

Lemma qtail_mult_lt_compat_l : forall z x y : Q,
  Qlt 0 z -> Qlt x y -> Qlt (z * x) (z * y).
Proof.
  intros z x y Hz Hxy.
  apply (Qle_lt_trans _ (x * z)).
  - apply qeq_le. ring.
  - apply (Qlt_le_trans (x * z) (y * z) (z * y)).
    + pose proof (Qmult_lt_compat_r x y z Hz Hxy) as Hr.
      exact Hr.
    + apply qeq_le. ring.
Qed.

(* ================= S1：尾和定义 + 非负 + 单调 ================= *)

(* qtail_sum b m n = Σ_{k=m}^{n-1} b^k/k!；n<m 守卫防 nat 减法截断（空和 = 0） *)
Fixpoint qtail_sum (b : Q) (m n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => (if Nat.leb m n' then q_pow b n' / q_fact n' else 0)
                      + qtail_sum b m n'
  end.

Lemma qtail_sum_le_m : forall b m n, (n <= m)%nat -> qtail_sum b m n == 0.
Proof.
  intros b m n Hn. revert Hn.
  induction n as [| n IH]; intro Hn.
  - reflexivity.
  - change (qtail_sum b m (Datatypes.S n))
      with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E. exfalso. lia.
    + rewrite IH by lia. reflexivity.
Qed.

Lemma qtail_sum_add : forall b m p n, (m <= p)%nat -> (p <= n)%nat ->
  qtail_sum b m n == qtail_sum b m p + qtail_sum b p n.
Proof.
  intros b m p n Hmp Hpn. revert Hpn.
  induction n as [| n IH]; intro Hpn.
  - assert (Hp : p = 0%nat) by lia. subst p.
    rewrite (qtail_sum_le_m b 0 0) by lia.
    ring.
  - destruct (Nat.eq_dec p (Datatypes.S n)) as [HpSn | Hplt].
    + subst p.
      rewrite (qtail_sum_le_m b (Datatypes.S n) (Datatypes.S n)) by lia.
      ring.
    + assert (Hpn' : (p <= n)%nat) by lia.
      change (qtail_sum b m (Datatypes.S n))
        with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
      change (qtail_sum b p (Datatypes.S n))
        with ((if Nat.leb p n then q_pow b n / q_fact n else 0) + qtail_sum b p n).
      rewrite (IH Hpn').
      destruct (Nat.leb m n) eqn:Em; destruct (Nat.leb p n) eqn:Ep.
      * ring.
      * apply Nat.leb_gt in Ep. exfalso. lia.
      * apply Nat.leb_gt in Em. exfalso. lia.
      * ring.
Qed.

Lemma qtail_geo_nonneg : forall n : nat, Qle 0 (geo_sum n).
Proof.
  induction n as [| n IH].
  - apply Qle_refl.
  - change (geo_sum (Datatypes.S n)) with (geo_sum n + q_pow (1 / 2) n).
    apply (Qle_trans _ (q_pow (1 / 2) n) _).
    + apply q_pow_nonneg. apply Qhalf_nonneg.
    + apply (Qle_trans (q_pow (1 / 2) n) (0 + q_pow (1 / 2) n)
                       (geo_sum n + q_pow (1 / 2) n)).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat 0 (geo_sum n) (q_pow (1 / 2) n) (q_pow (1 / 2) n)).
        -- exact IH.
        -- apply Qle_refl.
Qed.

Lemma qtail_sum_nonneg_aux : forall b m n, Qle 0 b -> Qle 0 (qtail_sum b m n).
Proof.
  intros b m n Hb. induction n as [| n IH].
  - apply Qle_refl.
  - change (qtail_sum b m (Datatypes.S n))
      with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      apply (Qle_trans _ (q_pow b n / q_fact n) _).
      * apply q_pow_fact_nonneg. exact Hb.
      * apply (qtail_le_plus_r _ (qtail_sum b m n)). apply IH.
    + setoid_replace (0 + qtail_sum b m n) with (qtail_sum b m n) by ring.
      apply IH.
Qed.

(* n 增尾和增（单调性） *)
Lemma qtail_sum_mono_aux : forall b m n1 n2,
  Qle 0 b -> (m <= n1)%nat -> (n1 <= n2)%nat -> Qle (qtail_sum b m n1) (qtail_sum b m n2).
Proof.
  intros b m n1 n2 Hb H1 H2. revert H2.
  induction n2 as [| n2 IH]; intro H2.
  - assert (Hn1 : n1 = 0%nat) by lia. subst n1. apply Qle_refl.
  - destruct (Nat.eq_dec n1 (Datatypes.S n2)) as [He | Hd].
    + rewrite He. apply Qle_refl.
    + assert (H12 : (n1 <= n2)%nat) by lia.
      apply (Qle_trans _ (qtail_sum b m n2) _).
      * apply IH; assumption.
      * change (qtail_sum b m (Datatypes.S n2))
          with ((if Nat.leb m n2 then q_pow b n2 / q_fact n2 else 0) + qtail_sum b m n2).
        destruct (Nat.leb m n2) eqn:E.
        -- apply Nat.leb_le in E.
           apply (Qle_trans (qtail_sum b m n2) (0 + qtail_sum b m n2)
                            (q_pow b n2 / q_fact n2 + qtail_sum b m n2)).
           ++ apply qeq_le. ring.
           ++ apply (Qplus_le_compat 0 (q_pow b n2 / q_fact n2)
                          (qtail_sum b m n2) (qtail_sum b m n2)).
              ** apply q_pow_fact_nonneg. exact Hb.
              ** apply Qle_refl.
        -- apply Nat.leb_gt in E. exfalso. lia.
Qed.

(* S1 出口（Set 层，QleT' 形） *)
Lemma qtail_sum_nonneg : forall b m n, QleT' 0 b -> QleT' 0 (qtail_sum b m n).
Proof.
  intros b m n Hb. apply Qle_to_QleT'.
  apply qtail_sum_nonneg_aux. apply (QleT'_to_Qle 0 b). exact Hb.
Qed.

Lemma qtail_sum_mono : forall b m n1 n2,
  QleT' 0 b -> (m <= n1)%nat -> (n1 <= n2)%nat ->
  QleT' (qtail_sum b m n1) (qtail_sum b m n2).
Proof.
  intros b m n1 n2 Hb H1 H2. apply Qle_to_QleT'.
  apply qtail_sum_mono_aux.
  - apply (QleT'_to_Qle 0 b). exact Hb.
  - exact H1.
  - exact H2.
Qed.

(* ================= S2-Q：尾项衰减控制 ================= *)

(* b^k/k! ≤ (b^4/4!)·(b/2)^(k-4)（k ≥ 4；对任意 b ≥ 0 成立，分段在主件处理） *)
Lemma qtail_term_decay_aux : forall (b : Q) (j : nat), Qle 0 b ->
  Qle (q_pow b (4 + j) / q_fact (4 + j)) ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j).
Proof.
  intros b j Hb. induction j as [| j IH].
  - apply qeq_le. simpl. ring.
  - replace (4 + Datatypes.S j)%nat with (Datatypes.S (4 + j))%nat by lia.
    rewrite (q_pow_succ b (4 + j)), (q_fact_succ (4 + j)).
    assert (Hc0 : ~ ((Z.of_nat (Datatypes.S (4 + j)) # 1) == 0)).
    { apply qtail_neq0. apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia. }
    assert (Hfc0 : ~ (q_fact (4 + j) == 0)) by (apply qtail_neq0; apply q_fact_pos).
    assert (HCj : Qle 0 ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j)).
    { apply Qmult_le_0_compat.
      - apply q_pow_fact_nonneg. exact Hb.
      - apply q_pow_nonneg.
        apply (Qle_trans 0 (b * (1 / 2)) (b / 2)).
        + apply (Qmult_le_0_compat).
          * exact Hb.
          * apply Qhalf_nonneg.
        + apply qeq_le. reflexivity. }
    assert (Hbc0 : Qle 0 (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
    { apply (q_le_div_le 0 1 b (Z.of_nat (Datatypes.S (4 + j)) # 1)).
      - apply qtail_Qlt01.
      - apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia.
      - apply (Qle_trans (0 * (Z.of_nat (Datatypes.S (4 + j)) # 1)) 0 (b * 1)).
        + apply qeq_le. ring.
        + apply (Qle_trans 0 b (b * 1)).
          * exact Hb.
          * apply qeq_le. ring. }
    apply (Qle_trans _
      ((q_pow b (4 + j) / q_fact (4 + j)) * (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))) _).
    + apply qeq_le.
      rewrite (Qmult_comm (q_pow b (4 + j) / q_fact (4 + j))
                          (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
      apply (qtail_div_split b (Z.of_nat (Datatypes.S (4 + j)) # 1)
                              (q_pow b (4 + j)) (q_fact (4 + j))).
      * exact Hc0.
      * exact Hfc0.
    + apply (Qle_trans _
        ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j
           * (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))) _).
      * apply (Qmult_le_compat_r _ _ (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
        -- exact IH.
        -- exact Hbc0.
      * apply (Qle_trans _
          ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j * (b / 2)%Q) _).
        -- apply (qtail_mult_le_compat_l
                    (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))
                    (b / 2)%Q ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j)).
           ++ apply (q_le_div_le b (Z.of_nat (Datatypes.S (4 + j)) # 1) b 2%Q).
              ** apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia.
              ** apply Q2_pos.
              ** apply (Qle_trans _ (2 * b)%Q).
                 --- apply qeq_le. ring.
                 --- apply (Qle_trans _
                              ((Z.of_nat (Datatypes.S (4 + j)) # 1) * b)).
                     +++ apply (Qmult_le_compat_r 2
                                  (Z.of_nat (Datatypes.S (4 + j)) # 1) b).
                         *** apply (Qle_of_nat 2 (Datatypes.S (4 + j))). lia.
                         *** exact Hb.
                     +++ apply qeq_le. ring.
           ++ exact HCj.
        -- apply qeq_le.
           rewrite (q_pow_succ (b / 2) j).
           ring.
Qed.

Lemma qtail_term_decay : forall (b : Q) (k : nat), QleT' 0 b -> (4 <= k)%nat ->
  QleT' (q_pow b k / q_fact k) ((q_pow b 4 / q_fact 4) * q_pow (b / 2) (k - 4)).
Proof.
  intros b k Hb Hk. apply Qle_to_QleT'.
  remember (k - 4)%nat as j eqn:Ej.
  replace k with (4 + j)%nat by lia.
  apply qtail_term_decay_aux. apply (QleT'_to_Qle 0 b). exact Hb.
Qed.

(* ================= S3：显式比值机 + 几何尾 + 构造性柯西模量 ================= *)

(* 显式上界：2b ≤ (2·⌊b⌋₊+1)#1 *)
Lemma qtail_two_b_le : forall b : Q, Qle 0 b ->
  Qle ((1 + 1)%Q * b) (Z.of_nat (2 * Z.to_nat (Qnum b) + 1) # 1).
Proof.
  intros b Hb.
  pose proof (qtail_pos_upper b Hb) as Hp.
  apply (Qle_trans _ ((Z.of_nat (Z.to_nat (Qnum b)) # 1) * (1 + 1)%Q) _).
  - apply (Qle_trans ((1 + 1)%Q * b)
                     ((1 + 1)%Q * (Z.of_nat (Z.to_nat (Qnum b)) # 1))
                     ((Z.of_nat (Z.to_nat (Qnum b)) # 1) * (1 + 1)%Q)).
    + apply (qtail_mult_le_compat_l b (Z.of_nat (Z.to_nat (Qnum b)) # 1) (1 + 1)%Q).
      * exact Hp.
      * apply Q2_nonneg.
    + apply qeq_le. ring.
  - apply (Qle_trans _ (Z.of_nat (2 * Z.to_nat (Qnum b)) # 1) _).
    + apply qeq_le.
      replace (2 * Z.to_nat (Qnum b))%nat
        with (Z.to_nat (Qnum b) + Z.to_nat (Qnum b))%nat by lia.
      unfold Qeq. simpl. lia.
    + apply (Qle_of_nat (2 * Z.to_nat (Qnum b)) (2 * Z.to_nat (Qnum b) + 1)). lia.
Qed.

(* 单步比值：k ≥ K 且 2b ≤ K+1 ⟹ 项_{k+1} ≤ 项_k·(1/2) *)
Lemma qtail_ratio_step : forall (b : Q) (K k : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) -> (K <= k)%nat ->
  Qle (q_pow b (Datatypes.S k) / q_fact (Datatypes.S k))
      ((q_pow b k / q_fact k) * (1 / 2)%Q).
Proof.
  intros b K k Hb H2b Hk.
  assert (Hc0 : ~ ((Z.of_nat (Datatypes.S k) # 1) == 0)).
  { apply qtail_neq0. apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia. }
  assert (Hf0 : ~ (q_fact k == 0)) by (apply qtail_neq0; apply q_fact_pos).
  assert (Hbc0 : Qle 0 (b / (Z.of_nat (Datatypes.S k) # 1))).
  { apply (q_le_div_le 0 1 b (Z.of_nat (Datatypes.S k) # 1)).
    - apply qtail_Qlt01.
    - apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia.
    - apply (Qle_trans (0 * (Z.of_nat (Datatypes.S k) # 1)) 0 (b * 1)).
      + apply qeq_le. ring.
      + apply (Qle_trans 0 b (b * 1)).
        * exact Hb.
        * apply qeq_le. ring. }
  apply (Qle_trans _ ((q_pow b k / q_fact k) * (b / (Z.of_nat (Datatypes.S k) # 1))) _).
  - apply qeq_le.
    rewrite (q_pow_succ b k), (q_fact_succ k).
    rewrite (Qmult_comm (q_pow b k / q_fact k) (b / (Z.of_nat (Datatypes.S k) # 1))).
    apply (qtail_div_split b (Z.of_nat (Datatypes.S k) # 1) (q_pow b k) (q_fact k)).
    + exact Hc0.
    + exact Hf0.
  - apply (qtail_mult_le_compat_l (b / (Z.of_nat (Datatypes.S k) # 1))
             (1 / 2)%Q (q_pow b k / q_fact k)).
    + apply (q_le_div_le b (Z.of_nat (Datatypes.S k) # 1) 1 2%Q).
      * apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia.
      * apply Q2_pos.
      * apply (Qle_trans _ ((1 + 1)%Q * b) _).
        -- apply qeq_le. ring.
        -- apply (Qle_trans _ (Z.of_nat (Datatypes.S K) # 1) _).
           ++ exact H2b.
           ++ apply (Qle_of_nat (Datatypes.S K) (Datatypes.S k)). lia.
    + apply q_pow_fact_nonneg. exact Hb.
Qed.

(* 链式：k ≥ K ⟹ 项_k ≤ 项_K·(1/2)^(k-K) *)
Lemma qtail_ratio_chain : forall (b : Q) (K k : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) -> (K <= k)%nat ->
  Qle (q_pow b k / q_fact k) ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K)).
Proof.
  intros b K k Hb H2b. revert k.
  induction k as [| k IH]; intro Hk.
  - assert (HK : K = 0%nat) by lia. subst K.
    apply qeq_le. simpl. ring.
  - destruct (Nat.eq_dec (Datatypes.S k) K) as [He | Hne].
    + rewrite He.
      replace (K - K)%nat with 0%nat by lia.
      apply qeq_le. simpl. ring.
    + assert (Hk' : (K <= k)%nat) by lia.
      replace (Datatypes.S k - K)%nat with (Datatypes.S (k - K))%nat by lia.
      apply (Qle_trans _ ((q_pow b k / q_fact k) * (1 / 2)%Q) _).
      * apply (qtail_ratio_step b K k).
        -- exact Hb.
        -- exact H2b.
        -- lia.
      * apply (Qle_trans _
                 ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K) * (1 / 2)%Q)).
        -- apply (Qmult_le_compat_r (q_pow b k / q_fact k)
                     ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K)) (1 / 2)%Q).
           ++ apply IH. exact Hk'.
           ++ apply Qhalf_nonneg.
        -- apply qeq_le.
           rewrite (q_pow_succ (1 / 2) (k - K)).
           ring.
Qed.

(* 几何和：Σ_{k=K+t}^{M-1} 项_k ≤ 项_K·(1/2)^t·geo_sum(M-(K+t)) *)
Lemma qtail_sum_geo : forall (b : Q) (K t M : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) ->
  ((K + t) <= M)%nat ->
  Qle (qtail_sum b (K + t) M)
      ((q_pow b K / q_fact K) * q_pow (1 / 2) t * geo_sum (M - (K + t))).
Proof.
  intros b K t M Hb H2b. revert t.
  induction M as [| M IH]; intros t Ht.
  - assert (HK : K = 0%nat) by lia.
    assert (Ht0 : t = 0%nat) by lia.
    rewrite HK, Ht0.
    apply qeq_le. simpl. ring.
  - destruct (Nat.leb (K + t) M) eqn:E.
    + apply Nat.leb_le in E.
      assert (HM : (K + t <= M)%nat) by lia.
      specialize (IH t HM).
      change (qtail_sum b (K + t) (Datatypes.S M))
        with ((if Nat.leb (K + t) M then q_pow b M / q_fact M else 0)
              + qtail_sum b (K + t) M).
      assert (HL : Nat.leb (K + t) M = true) by (apply Nat.leb_le; exact E).
      replace (if Nat.leb (K + t) M then q_pow b M / q_fact M else 0)
        with (q_pow b M / q_fact M) by (rewrite HL; reflexivity).
      replace (Datatypes.S M - (K + t))%nat with (Datatypes.S (M - (K + t)))%nat by lia.
      change (geo_sum (Datatypes.S (M - (K + t))))
        with (geo_sum (M - (K + t)) + q_pow (1 / 2) (M - (K + t))).
      assert (Hterm : Qle (q_pow b M / q_fact M)
                        ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                           * q_pow (1 / 2) (M - (K + t)))).
      { apply (Qle_trans _ ((q_pow b K / q_fact K) * q_pow (1 / 2) (M - K)) _).
        - apply qtail_ratio_chain.
          + exact Hb.
          + exact H2b.
          + lia.
        - apply qeq_le.
          replace (M - K)%nat with (t + (M - (K + t)))%nat by lia.
          rewrite (q_pow_add (1 / 2) t (M - (K + t))).
          ring. }
      apply (Qle_trans _
        (((q_pow b K / q_fact K) * q_pow (1 / 2) t * q_pow (1 / 2) (M - (K + t)))
          + (q_pow b K / q_fact K) * q_pow (1 / 2) t * geo_sum (M - (K + t))) _).
      * apply (Qplus_le_compat (q_pow b M / q_fact M)
                  ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                     * q_pow (1 / 2) (M - (K + t)))
                  (qtail_sum b (K + t) M)
                  ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                     * geo_sum (M - (K + t)))).
        -- exact Hterm.
        -- exact IH.
      * apply qeq_le. ring.
    + apply Nat.leb_gt in E.
      apply (Qle_trans _ 0 _).
      * apply qeq_le. apply qtail_sum_le_m. lia.
      * apply Qmult_le_0_compat.
        -- apply Qmult_le_0_compat.
           ++ apply q_pow_fact_nonneg. exact Hb.
           ++ apply q_pow_nonneg. apply Qhalf_nonneg.
        -- apply qtail_geo_nonneg.
Qed.

(* ===== 主件：构造性柯西模量（Prop 内核；N = max(4,2·⌊b⌋₊) + t0 全显式） ===== *)
Lemma qtail_cauchy_modulus_aux : forall b e : Q, Qle 0 b -> Qlt 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    Qlt (qtail_sum b (Nat.min m n) (Nat.max m n)) e).
Proof.
  intros b e Hb He.
  assert (Hne : ~ (e == 0)) by (apply qtail_neq0; exact He).
  (* K = max(4, 2·⌊b⌋₊)：显式，比值自 K 起折半 *)
  assert (H2b : Qle ((1 + 1)%Q * b)
                     (Z.of_nat (Datatypes.S (Nat.max 4 (2 * Z.to_nat (Qnum b)))) # 1)).
  { apply (Qle_trans _ (Z.of_nat (2 * Z.to_nat (Qnum b) + 1) # 1) _).
    - apply qtail_two_b_le. exact Hb.
    - apply (Qle_of_nat (2 * Z.to_nat (Qnum b) + 1)
                        (Datatypes.S (Nat.max 4 (2 * Z.to_nat (Qnum b))))). lia. }
  set (K := Nat.max 4 (2 * Z.to_nat (Qnum b))) in *.
  set (C := q_pow b K / q_fact K).
  assert (HC : Qle 0 C) by (unfold C; apply q_pow_fact_nonneg; exact Hb).
  destruct (Qeq_dec C 0) as [Hz | Hnz].
  - (* C = 0：第 K 项起全零 *)
    remember (Z.to_nat (Qnum ((C * (1 + 1)) / e))) as t0 eqn:Et0.
    exists (K + t0)%nat.
    intros m n Hm Hn.
    assert (Hsum : Qle (qtail_sum b (Nat.min m n) (Nat.max m n))
                        (C * q_pow (1 / 2) t0 * (1 + 1)%Q)).
    { assert (HAnn : Qle 0 (qtail_sum b (K + t0) (Nat.min m n)))
        by (apply qtail_sum_nonneg_aux; exact Hb).
      apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.min m n)
                            + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
      - apply (Qle_trans _ (0 + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
        + apply qeq_le. ring.
        + apply (Qplus_le_compat 0 (qtail_sum b (K + t0) (Nat.min m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))).
          * exact HAnn.
          * apply Qle_refl.
      - apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.max m n)) _).
        + apply qeq_le. apply Qeq_sym.
          apply (qtail_sum_add b (K + t0) (Nat.min m n) (Nat.max m n)); lia.
        + apply (Qle_trans _
                   (C * q_pow (1 / 2) t0 * geo_sum (Nat.max m n - (K + t0))) _).
          * apply (qtail_sum_geo b K t0 (Nat.max m n) Hb H2b). lia.
          * apply (qtail_mult_le_compat_l (geo_sum (Nat.max m n - (K + t0)))
                     (1 + 1)%Q (C * q_pow (1 / 2) t0)).
            -- apply geo_sum_le_two.
            -- apply Qmult_le_0_compat.
               ++ exact HC.
               ++ apply q_pow_nonneg. apply Qhalf_nonneg. }
    apply (Qle_lt_trans _ (C * q_pow (1 / 2) t0 * (1 + 1)%Q) _).
    + exact Hsum.
    + apply (Qle_lt_trans _ 0 _).
      * apply qeq_le. rewrite Hz. ring.
      * exact He.
  - (* C > 0：几何余项 + 2^t ≥ t+1 显式 *)
    assert (HC2 : Qle 0 (C * (1 + 1)%Q))
      by (apply Qmult_le_0_compat; [ exact HC | apply Q2_nonneg ]).
    assert (HC2pos : Qlt 0 (C * (1 + 1)%Q)).
    { apply Qmult_lt_0_compat.
      - destruct (Qle_lt_or_eq 0 C HC) as [H | H].
        + exact H.
        + exfalso. exact (Hnz (Qeq_sym _ _ H)).
      - apply Q2_pos. }
    assert (HC2ne : ~ ((C * (1 + 1)%Q) == 0)) by (apply qtail_neq0; exact HC2pos).
    set (w := (C * (1 + 1)%Q) / e).
    assert (Hw0 : Qle 0 w).
    { unfold w. apply (q_le_div_le 0 1 (C * (1 + 1)%Q) e).
      - apply qtail_Qlt01.
      - exact He.
      - apply (Qle_trans (0 * e) 0 ((C * (1 + 1)%Q) * 1)).
        + apply qeq_le. ring.
        + apply (Qle_trans 0 (C * (1 + 1)%Q) ((C * (1 + 1)%Q) * 1)).
          * exact HC2.
          * apply qeq_le. ring. }
    assert (Hwpos : Qlt 0 w) by (unfold w; apply qtail_div_pos; assumption).
    assert (Hwne : ~ (((C * (1 + 1)%Q) / e) == 0)).
    { apply qtail_neq0. unfold w. exact Hwpos. }
    assert (Hwlt : Qlt w (Z.of_nat (Datatypes.S (Z.to_nat (Qnum w))) # 1)).
    { assert (Hup : Qle w (Z.of_nat (Z.to_nat (Qnum w)) # 1))
        by (apply qtail_pos_upper; exact Hw0).
      apply (Qle_lt_trans w (Z.of_nat (Z.to_nat (Qnum w)) # 1)
                           (Z.of_nat (Datatypes.S (Z.to_nat (Qnum w))) # 1)).
      - exact Hup.
      - apply (Qlt_of_nat_lt (Z.to_nat (Qnum w))
                             (Datatypes.S (Z.to_nat (Qnum w)))). lia. }
    remember (Z.to_nat (Qnum w)) as t0 eqn:Et0.
    exists (K + t0)%nat.
    intros m n Hm Hn.
    assert (Hsum : Qle (qtail_sum b (Nat.min m n) (Nat.max m n))
                        (C * q_pow (1 / 2) t0 * (1 + 1)%Q)).
    { assert (HAnn : Qle 0 (qtail_sum b (K + t0) (Nat.min m n)))
        by (apply qtail_sum_nonneg_aux; exact Hb).
      apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.min m n)
                            + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
      - apply (Qle_trans _ (0 + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
        + apply qeq_le. ring.
        + apply (Qplus_le_compat 0 (qtail_sum b (K + t0) (Nat.min m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))).
          * exact HAnn.
          * apply Qle_refl.
      - apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.max m n)) _).
        + apply qeq_le. apply Qeq_sym.
          apply (qtail_sum_add b (K + t0) (Nat.min m n) (Nat.max m n)); lia.
        + apply (Qle_trans _
                   (C * q_pow (1 / 2) t0 * geo_sum (Nat.max m n - (K + t0))) _).
          * apply (qtail_sum_geo b K t0 (Nat.max m n) Hb H2b). lia.
          * apply (qtail_mult_le_compat_l (geo_sum (Nat.max m n - (K + t0)))
                     (1 + 1)%Q (C * q_pow (1 / 2) t0)).
            -- apply geo_sum_le_two.
            -- apply Qmult_le_0_compat.
               ++ exact HC.
               ++ apply q_pow_nonneg. apply Qhalf_nonneg. }
    assert (Hst0 : ~ ((Z.of_nat (Datatypes.S t0) # 1) == 0)).
    { apply qtail_neq0. apply (Qlt_of_nat_lt 0 (Datatypes.S t0)). lia. }
    assert (Hinv : Qle ((C * (1 + 1)%Q) * q_pow (1 / 2) t0)
                        ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1)))).
    { apply (qtail_mult_le_compat_l (q_pow (1 / 2) t0)
                               (1 / (Z.of_nat (Datatypes.S t0) # 1))
                               (C * (1 + 1)%Q)).
      - apply qtail_half_pow_le_invT.
      - exact HC2. }
    assert (Hwdef : ((C * (1 + 1)%Q) / w) == e).
    { unfold w. field. repeat split; assumption. }
    assert (Hst0pos : Qlt 0 (Z.of_nat (Datatypes.S t0) # 1)).
    { apply (Qlt_of_nat_lt 0 (Datatypes.S t0)). lia. }
    assert (Hstrict : Qlt ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1))) e).
    { assert (Hdv : Qlt ((C * (1 + 1)%Q) / (Z.of_nat (Datatypes.S t0) # 1))
                        ((C * (1 + 1)%Q) / w)).
      { apply (qtail_div_lt (C * (1 + 1)%Q) (Z.of_nat (Datatypes.S t0) # 1)
                            (C * (1 + 1)%Q) w).
        - exact Hst0pos.
        - exact Hwpos.
        - apply (qtail_mult_lt_compat_l (C * (1 + 1)%Q) w
                    (Z.of_nat (Datatypes.S t0) # 1)).
          + exact HC2pos.
          + exact Hwlt. }
      apply (Qle_lt_trans _ ((C * (1 + 1)%Q) / (Z.of_nat (Datatypes.S t0) # 1)) e).
      - apply qeq_le. field. repeat split; assumption.
      - apply (Qlt_le_trans _ ((C * (1 + 1)%Q) / w) e).
        + exact Hdv.
        + apply qeq_le. unfold w. exact Hwdef. }
    apply (Qle_lt_trans _ ((C * q_pow (1 / 2) t0) * (1 + 1)%Q) _).
    + exact Hsum.
    + apply (Qle_lt_trans _
               ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1))) _).
      * apply (Qle_trans _ ((C * (1 + 1)%Q) * q_pow (1 / 2) t0)).
        -- apply qeq_le. ring.
        -- exact Hinv.
      * exact Hstrict.
Qed.

(* S3 主件出口（Set 层，QltT/sigT；对称参序 min/max 形） *)
Lemma qtail_cauchy_modulus : forall b e : Q,
  QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    QltT (qtail_sum b (Nat.min m n) (Nat.max m n)) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus_aux b e (qtail_QleT_to_Qle 0 b Hb)
              (QltT_to_Qlt 0 e He)) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT. apply HN; assumption.
Qed.

(* S3 有序参序形（n ≤ m 双端 ≥ N）——路径 B 柯西判据直用形 *)
Lemma qtail_cauchy_modulus_ord : forall b e : Q,
  QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= n)%nat -> (n <= m)%nat ->
    QltT (qtail_sum b n m) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus b e Hb He) as [N HN].
  exists N. intros m n Hn Hnm.
  assert (HB : QltT (qtail_sum b (Nat.min n m) (Nat.max n m)) e)
    by (apply (HN n m); lia).
  replace (Nat.min n m) with n in HB by lia.
  replace (Nat.max n m) with m in HB by lia.
  exact HB.
Qed.

(* ================= S4：与 S03 exp 级数件的对接注记 =================
   1) 路径 B（Banach exp 级数柯西性）：exp_partial m x 的差经
      exp_partial_diff_tail 归约为尾和；对 |x| ≤ b 直接使用
      qtail_cauchy_modulus_ord（N(b,e) 显式可算，替代 S03 的
      q_arch_geom + arch_decay 双 Qarchimedean witness 链）。
   2) 路径 C（Padé 误差界）：Padé 截断余项 Σ b^k/k! 以
      qtail_sum_mono 控制增长、qtail_sum_nonneg 保号、
      qtail_cauchy_modulus 给显式尾界 N。
   3) 与 S03 件关系：qtail_sum b m n == exp_tail (pred m) (pred n) b
      （m,n ≥ 1，恒等式未证，仅注记）；qtail_fact_ge_pow 与
      qtail_term_decay 可为 S03 pow_fact 系列提供 2^k ≤ k! 显式下界。 *)
