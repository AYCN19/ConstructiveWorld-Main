(** * GaC2_09_DenomZeroSet_c - rational deviation base, trigonometric
      deviation face, and window pin of the denominator zero set.
    Mission.  Node C2-09 (segment C2, slot W1), locate piece.  The
      rational-layer deviation base of the stem first-order estimate
      (eleven [d09_q_*] faces, roster in Notes); the trigonometric
      deviation face [d09_q_trig_dev] (|cos_partial n t - 1| <= t*t
      and |sin_partial n t - t| <= t*t on |t| <= 1); the order face
      [d09_lt_opp_both]; the window kit [d09_abs_split],
      [d09_half_const_pos], [d09_quarter_lt_two]; the half-angle
      collapse [d09_sin_half_zero_of_cos_one]; the window pin
      [d09_window_pin] (companion faces and the registered-open items
      reserved for the stem: see Notes).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [QArith.Qpower], [QArith.Qround], [Setoid], [Morphisms],
      [Arith.Arith], [Lia]; [S01_BaseRing] (selective [NatLe]/[And]
      import), [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [S10_KVQuantTrig], [CxRealPairCore], [CxRealPairExpLog], [G1_PYTH],
      [GaC1_Iface_Cx], [GaC1_Iface_Real], [GaC2_09_DenomZeroSet_a],
      [GaC2_09_DenomZeroSet_b].
    References.  drafts_C2.md C2.09 sketch (the L11 obligation: the pi
      carrier pinned to the C1-17 output face [pi_R]); Bishop-Bridges
      Ch. 2 (the half-angle collapse through the Pythagorean identity);
      the alternating-series remainder estimates (trig deviation face).
    Constructivity.  Every named construction is carried by [Set]; the
      window pin runs the weak trichotomy (pi + 1/4 margin) and the
      deviation base carries the explicit factorial bounds; zero assumed
      constants; every proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_c.v] from the flat build
      directory, thermal guard wrapper. *)
Require S01_BaseRing.
(** Notes.  Full roster behind the Mission field.  The rational-layer
    deviation base: [d09_q_mult_le_r], [d09_q_abs_le_of_both],
    [d09_q_abs_pow_le_one], [d09_q_pow_half_nonneg],
    [d09_q_half_pow_step], [d09_q_half_pow_anti],
    [d09_q_fact_inv_le2], [d09_q_pow_m1_abs], [d09_q_abs_pow_le_sq],
    [d09_q_sqr_eq_abs], [d09_q_abs_sq_le_sq].  The half-angle
    collapse [d09_sin_half_zero_of_cos_one]: cos x == 1 forces
    sin(x/2) == 0.  The window pin [d09_window_pin]: cos d == 1 and
    sin d == 0 with d inside the pi + 1/4 window force d == 0.
    Companion faces (live in GaC2_09_DenomZeroSet_b): the logarithm
    constant [d09_ln2], the distributivity, associativity, and
    telescoping faces [d09_mult_distr_r]/[d09_mult_assoc]/
    [d09_sub_split], the pi carrier, and the inverse constant.
    Registered-open items reserved for the consolidating stem
    GaC2_09_DenomZeroSet, to be cast there and absent from this
    piece: the strict upper bound bridge kit, the stem bound
    [d09_ln2_lt_one], the faces [d09_one_minus_eq], the
    two-less-than-e comparison kit, and the exponential deviation
    face of the stem. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import G1_PYTH.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import QArith.Qpower.
From Stdlib Require Import QArith.Qround.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.

Lemma d09_q_pow_half_nonneg : forall k : nat, Qle 0 (q_pow (1 / 2)%Q k). Proof. intro k. induction k as [| k IH].
  - unfold Qle. simpl. lia.
  - rewrite (q_pow_succ (1 / 2)%Q k). apply Qmult_le_0_compat; [unfold Qle; simpl; lia | exact IH]. Qed.
Lemma d09_q_mult_le_r : forall x y z : Q, Qle x y -> Qle 0 z -> Qle (x * z) (y * z). Proof. intros x y z Hxy Hz.
  assert (Hpos : Qle 0 (y - x)) by exact (proj1 (Qle_minus_iff x y) Hxy). assert (Hd : Qle 0 ((y - x) * z)).
  { apply Qmult_le_0_compat; [exact Hpos | exact Hz]. } assert (Hz2 : (y * z)%Q == ((y - x) * z + x * z)%Q) by ring. rewrite Hz2. apply (Qle_trans (x * z) (0 + x * z)).
  - apply qeq_le. ring.
  - apply Qplus_le_compat; [exact Hd | apply Qle_refl]. Qed.
Lemma d09_q_abs_le_of_both : forall z c : Q, Qle z c -> Qle (- c) z -> Qle (Qabs z) c.
Proof. intros z c H1 H2. apply (proj2 (Qabs_Qle_condition z c)). split.
  - exact H2. - exact H1. Qed.
Lemma d09_q_abs_pow_le_one : forall (t : Q) (k : nat), Qle (Qabs t) 1 -> Qle (Qabs (q_pow t k)) 1. Proof. intros t k Ht. induction k as [| k IH].
  - cbn [q_pow Qabs]. apply Qle_refl.
  - cbn [q_pow]. rewrite Qabs_Qmult. apply (Qle_trans (Qabs t * Qabs (q_pow t k)) (1 * Qabs (q_pow t k))).
    + apply (d09_q_mult_le_r (Qabs t) 1 (Qabs (q_pow t k)) Ht (Qabs_nonneg _)).
    + apply (Qle_trans (1 * Qabs (q_pow t k)) (Qabs (q_pow t k))).
      * apply qeq_le. ring.
      * exact IH. Qed.
Lemma d09_q_half_pow_step : forall d : nat, Qle (q_pow (1 / 2)%Q (Datatypes.S d)) (q_pow (1 / 2)%Q d). Proof. intro d.
  assert (Hs : Qle (1 / 2)%Q 1) by (unfold Qle; simpl; lia). rewrite (q_pow_succ (1 / 2)%Q d). apply (Qle_trans _ (1%Q * q_pow (1 / 2)%Q d)).
  { exact (Qmult_le_compat_r (1 / 2)%Q 1%Q (q_pow (1 / 2)%Q d) Hs (d09_q_pow_half_nonneg d)). }
  { apply qeq_le. ring. } Qed.
Lemma d09_q_half_pow_anti : forall a b : nat, (b <= a)%nat -> Qle (q_pow (1 / 2)%Q a) (q_pow (1 / 2)%Q b).
Proof. assert (Hs1 : Qle (Qabs (1 / 2)%Q) 1) by (unfold Qle; simpl; lia). induction a as [| a IHa]; intros b Hb.
  - assert (Hb0 : b = 0%nat) by lia. subst b. apply Qle_refl.
  - destruct b as [| b'].
    + apply (Qle_trans (q_pow (1 / 2)%Q (Datatypes.S a)) (Qabs (q_pow (1 / 2)%Q (Datatypes.S a)))).
      { apply Qle_Qabs. }
      { apply (d09_q_abs_pow_le_one (1 / 2)%Q (Datatypes.S a) Hs1). }
    + assert (H2 : (b' <= a)%nat) by lia. rewrite (q_pow_succ (1 / 2)%Q a), (q_pow_succ (1 / 2)%Q b').
      rewrite (Qmult_comm (1 / 2)%Q (q_pow (1 / 2)%Q a)), (Qmult_comm (1 / 2)%Q (q_pow (1 / 2)%Q b')). apply (d09_q_mult_le_r (q_pow (1 / 2)%Q a) (q_pow (1 / 2)%Q b') (1 / 2)%Q).
      * exact (IHa b' H2).
      * unfold Qle. simpl. lia. Qed.
Lemma d09_q_fact_inv_le2 : forall m : nat, Qle (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) (q_pow (1 / 2)%Q (Datatypes.S m)).
Proof. induction m as [| m IH].
  - assert (Hf : q_fact (Datatypes.S (Datatypes.S 0)) == (2 / 1)%Q) by (cbn [q_fact]; unfold Qeq; simpl; ring). rewrite Hf. cbn [Qinv q_pow]. apply Qle_refl.
  - assert (Hf3 : q_fact (Datatypes.S (Datatypes.S (Datatypes.S m))) == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m))) # 1)
                         * q_fact (Datatypes.S (Datatypes.S m))) by reflexivity. rewrite Hf3, Qinv_mult_distr, (q_pow_succ (1 / 2)%Q (Datatypes.S m)).
    assert (Hq2 : Qle (Qinv ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m)))) # 1)) (1 / 2)%Q).
    { apply (Qlt_le_weak _ _). apply (Qinv_lt_contravar ((Z.of_nat (Datatypes.S (Datatypes.S 0))) # 1) ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m)))) # 1)).
      - unfold Qlt. simpl. lia.
      - unfold Qlt. simpl. lia.
      - unfold Qlt. simpl. lia. } assert (Hz0 : Qle 0 (Qinv (q_fact (Datatypes.S (Datatypes.S m)))))
      by exact (Qlt_le_weak 0 _ (Qinv_lt_0_compat (q_fact (Datatypes.S (Datatypes.S m))) (q_fact_pos (Datatypes.S (Datatypes.S m))))).
    apply (Qle_trans _ ((1 / 2)%Q * Qinv (q_fact (Datatypes.S (Datatypes.S m))))).
    + apply (Qmult_le_compat_r (Qinv ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m)))) # 1)) (1 / 2)%Q (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) Hq2 Hz0).
    + rewrite (Qmult_comm (1 / 2)%Q (Qinv (q_fact (Datatypes.S (Datatypes.S m))))), (Qmult_comm (1 / 2)%Q (q_pow (1 / 2)%Q (Datatypes.S m))).
      apply (d09_q_mult_le_r (Qinv (q_fact (Datatypes.S (Datatypes.S m)))) (q_pow (1 / 2)%Q (Datatypes.S m)) (1 / 2)%Q).
      * exact IH.
      * unfold Qle. simpl. lia. Qed.
Lemma d09_q_pow_m1_abs : forall j : nat, Qabs (q_pow (-1)%Q j) == 1. Proof. intro j. induction j as [| j IH].
  - cbn [q_pow Qabs]. reflexivity.
  - cbn [q_pow]. rewrite Qabs_Qmult. cbn [Qabs]. rewrite IH. reflexivity. Qed.
Lemma d09_q_abs_pow_le_sq : forall (t : Q) (k : nat),
  Qle (Qabs t) 1 -> (2 <= k)%nat -> Qle (Qabs (q_pow t k)) (Qabs t * Qabs t). Proof. intros t k Ht Hk.
  assert (Hbase : forall k0 : nat, Qle (Qabs (q_pow t (Datatypes.S (Datatypes.S k0)))) (Qabs t * Qabs t)).
  { intro k0. cbn [q_pow]. assert (Hq : q_pow t (Datatypes.S (Datatypes.S k0)) == q_pow t k0 * (t * t))
      by (rewrite q_pow_succ, q_pow_succ; ring). rewrite Hq, Qabs_Qmult, Qabs_Qmult. apply (Qle_trans _ (1 * (Qabs t * Qabs t))).
    - exact (d09_q_mult_le_r (Qabs (q_pow t k0)) 1 (Qabs t * Qabs t) (d09_q_abs_pow_le_one t k0 Ht) (Qmult_le_0_compat (Qabs t) (Qabs t) (Qabs_nonneg t) (Qabs_nonneg t))).
    - apply qeq_le. ring.
  } destruct k as [| k].
  - lia.
  - destruct k as [| j].
    + lia.
    + apply Hbase. Qed.
Lemma d09_q_sqr_eq_abs : forall t : Q, Qle 0 (t * t) -> QeqT (Qabs t * Qabs t) (t * t). Proof. intros t Hnn.
  apply (qeq_imp_qeqT (Qabs t * Qabs t) (t * t)). apply (Qeq_trans (Qabs t * Qabs t) (Qabs (t * t)) (t * t)).
  { apply Qeq_sym. apply Qabs_Qmult. }
  { apply (Qabs_pos (t * t)). exact Hnn. } Qed.
Lemma d09_q_abs_sq_le_sq : forall t : Q, Qle 0 (t * t) -> Qle (Qabs t * Qabs t) (t * t). Proof. intros t Hnn. apply QleT'_to_Qle.
  apply (qeq_leT' (Qabs t * Qabs t) (t * t)). apply (qeqT_imp_qeq (Qabs t * Qabs t) (t * t)). exact (d09_q_sqr_eq_abs t Hnn). Qed.
Lemma d09_q_trig_dev : forall (n : nat) (t : Q), Qle (Qabs t) 1 -> And (Qle (Qabs (cos_partial n t - 1)) (t * t)) (Qle (Qabs (sin_partial n t - t)) (t * t)). Proof.
  intros n t Ht. assert (Htsq : Qle 0 (t * t)) by apply Qsqr_nonneg. assert (Hsq2 : forall k : nat, Qle (Qabs (q_pow t (Datatypes.S (Datatypes.S k)))) (t * t)).
  { intro k. apply (Qle_trans _ (Qabs t * Qabs t)).
    - apply (d09_q_abs_pow_le_sq t (Datatypes.S (Datatypes.S k)) Ht); lia.
    - exact (d09_q_abs_sq_le_sq t Htsq). } assert (Hck : forall k : nat, Qle (Qabs (cos_term (Datatypes.S k) t)) ((t * t) * q_pow (1 / 2)%Q (Datatypes.S (k + k)))).
  { intro k. unfold cos_term. rewrite Qabs_Qmult. rewrite (d09_q_pow_m1_abs (Datatypes.S k)), Qmult_1_l.
    replace (2 * Datatypes.S k)%nat with (Datatypes.S (Datatypes.S (k + k))) by lia.
    assert (Hd : (q_pow t (Datatypes.S (Datatypes.S (k + k))) / q_fact (Datatypes.S (Datatypes.S (k + k))))%Q == q_pow t (Datatypes.S (Datatypes.S (k + k)))
                    * Qinv (q_fact (Datatypes.S (Datatypes.S (k + k))))) by reflexivity.
    rewrite Hd, Qabs_Qmult, Qabs_Qinv. rewrite (Qabs_pos (q_fact (Datatypes.S (Datatypes.S (k + k)))) (Qlt_le_weak 0 _ (q_fact_pos (Datatypes.S (Datatypes.S (k + k)))))).
    apply (Qle_trans _ ((t * t) * Qinv (q_fact (Datatypes.S (Datatypes.S (k + k)))))).
    - exact (d09_q_mult_le_r (Qabs (q_pow t (Datatypes.S (Datatypes.S (k + k))))) (t * t) (Qinv (q_fact (Datatypes.S (Datatypes.S (k + k))))) (Hsq2 (k + k)%nat)
               (Qlt_le_weak 0 _ (Qinv_lt_0_compat (q_fact (Datatypes.S (Datatypes.S (k + k)))) (q_fact_pos (Datatypes.S (Datatypes.S (k + k))))))).
    - rewrite (Qmult_comm (t * t) (Qinv (q_fact (Datatypes.S (Datatypes.S (k + k)))))), (Qmult_comm (t * t) (q_pow (1 / 2)%Q (Datatypes.S (k + k)))).
      exact (d09_q_mult_le_r (Qinv (q_fact (Datatypes.S (Datatypes.S (k + k))))) (q_pow (1 / 2)%Q (Datatypes.S (k + k))) (t * t) (d09_q_fact_inv_le2 (k + k)%nat) Htsq). }
  assert (Hsk : forall k : nat, Qle (Qabs (sin_term (Datatypes.S k) t)) ((t * t) * q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S (k + k))))).
  { intro k. unfold sin_term. rewrite Qabs_Qmult. rewrite (d09_q_pow_m1_abs (Datatypes.S k)), Qmult_1_l.
    replace (Datatypes.S (2 * Datatypes.S k))%nat with (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))) by lia.
    assert (Hd : (q_pow t (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))))%Q
                 == q_pow t (Datatypes.S (Datatypes.S (Datatypes.S (k + k))))
                    * Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))))) by reflexivity. rewrite Hd, Qabs_Qmult, Qabs_Qinv.
    rewrite (Qabs_pos (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k))))) (Qlt_le_weak 0 _ (q_fact_pos (Datatypes.S (Datatypes.S (Datatypes.S (k + k))))))).
    apply (Qle_trans _ ((t * t)
                           * Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k))))))).
    - exact (d09_q_mult_le_r (Qabs (q_pow t (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))))) (t * t)
               (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))))) (Hsq2 (Datatypes.S (k + k)))
               (Qlt_le_weak 0 _ (Qinv_lt_0_compat (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k))))) (q_fact_pos (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))))))).
    - rewrite (Qmult_comm (t * t) (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k))))))), (Qmult_comm (t * t) (q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S (k + k))))).
      exact (d09_q_mult_le_r (Qinv (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (k + k)))))) (q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S (k + k)))) (t * t)
               (d09_q_fact_inv_le2 (Datatypes.S (k + k))%nat) Htsq). } split.
  - assert (Hind : forall m : nat, Qle (Qabs (cos_partial m t - 1)) ((t * t) * (1 - q_pow (1 / 2)%Q m))).
    { intro m. induction m as [| m IHm].
      - unfold Qle. simpl. lia.
      - assert (Hle1 : (Datatypes.S m <= Datatypes.S (m + m))%nat) by lia. cbn [cos_partial]. assert (Hre : cos_partial m t + cos_term (Datatypes.S m) t - 1
                        == (cos_partial m t - 1) + cos_term (Datatypes.S m) t) by ring. rewrite Hre. apply (Qle_trans _ (Qabs (cos_partial m t - 1)
                              + Qabs (cos_term (Datatypes.S m) t))).
        + apply Qabs_triangle.
        + apply (Qle_trans _ ((t * t) * (1 - q_pow (1 / 2)%Q m)
                                + q_pow (1 / 2)%Q (Datatypes.S (m + m)) * (t * t))).
          * apply Qplus_le_compat; [exact IHm |]. rewrite (Qmult_comm (q_pow (1 / 2)%Q (Datatypes.S (m + m))) (t * t)). exact (Hck m).
          * apply (Qle_trans _ ((t * t) * (1 - q_pow (1 / 2)%Q m)
                                  + (t * t) * q_pow (1 / 2)%Q (Datatypes.S m))).
            -- apply Qplus_le_compat; [apply Qle_refl |]. rewrite (Qmult_comm (t * t) (q_pow (1 / 2)%Q (Datatypes.S m))).
               exact (d09_q_mult_le_r (q_pow (1 / 2)%Q (Datatypes.S (m + m))) (q_pow (1 / 2)%Q (Datatypes.S m)) (t * t)
                        (d09_q_half_pow_anti (Datatypes.S (m + m)) (Datatypes.S m) Hle1) Htsq).
            -- rewrite (q_pow_succ (1 / 2)%Q m). apply qeq_le. field. } apply (Qle_trans _ ((t * t) * (1 - q_pow (1 / 2)%Q n))).
    + exact (Hind n).
    + assert (Hq1 : Qle (1 - q_pow (1 / 2)%Q n) 1).
      { apply (proj2 (Qle_minus_iff (1 - q_pow (1 / 2)%Q n) 1)). apply (Qle_trans 0 (q_pow (1 / 2)%Q n) (1 - (1 - q_pow (1 / 2)%Q n))).
        - exact (d09_q_pow_half_nonneg n).
        - apply qeq_le. ring. } rewrite (Qmult_comm (t * t) (1 - q_pow (1 / 2)%Q n)). apply (Qle_trans _ (1 * (t * t))).
      * exact (d09_q_mult_le_r (1 - q_pow (1 / 2)%Q n) 1 (t * t) Hq1 Htsq).
      * apply qeq_le. ring.
  - assert (Hind2 : forall m : nat, Qle (Qabs (sin_partial m t - t)) ((t * t) * (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S m)))).
    { intro m. induction m as [| m IHm].
      - assert (Hs0 : sin_partial 0 t - t == 0) by (unfold sin_partial, sin_term; simpl; field). rewrite Hs0. cbn [Qabs]. unfold Qle. simpl. lia.
      - assert (Hle2 : (Datatypes.S (Datatypes.S m) <= Datatypes.S (Datatypes.S (m + m)))%nat) by lia.
        cbn [sin_partial]. assert (Hre : sin_partial m t + sin_term (Datatypes.S m) t - t == (sin_partial m t - t) + sin_term (Datatypes.S m) t) by ring. rewrite Hre.
        apply (Qle_trans _ (Qabs (sin_partial m t - t)
                              + Qabs (sin_term (Datatypes.S m) t))).
        + apply Qabs_triangle.
        + apply (Qle_trans _ ((t * t) * (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S m))
                                + q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S (m + m)))
                                   * (t * t))).
          * apply Qplus_le_compat; [exact IHm |]. rewrite (Qmult_comm (q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S (m + m)))) (t * t)). exact (Hsk m).
          * apply (Qle_trans _ ((t * t) * (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S m))
                                  + (t * t) * q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S m)))).
            -- apply Qplus_le_compat; [apply Qle_refl |]. rewrite (Qmult_comm (t * t) (q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S m)))).
               exact (d09_q_mult_le_r (q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S (m + m)))) (q_pow (1 / 2)%Q (Datatypes.S (Datatypes.S m))) (t * t)
                        (d09_q_half_pow_anti (Datatypes.S (Datatypes.S (m + m))) (Datatypes.S (Datatypes.S m)) Hle2) Htsq).
            -- rewrite (q_pow_succ (1 / 2)%Q (Datatypes.S m)). apply qeq_le. field. } apply (Qle_trans _ ((t * t) * (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S n)))).
    + exact (Hind2 n).
    + assert (Hq2 : Qle (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S n)) (1 / 2)).
      { apply (proj2 (Qle_minus_iff (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S n)) (1 / 2))).
        apply (Qle_trans 0 (q_pow (1 / 2)%Q (Datatypes.S n)) (1 / 2 - (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S n)))).
        - exact (d09_q_pow_half_nonneg (Datatypes.S n)).
        - apply qeq_le. field. } assert (Hq3 : Qle (1 / 2) 1) by (unfold Qle; simpl; lia).
      rewrite (Qmult_comm (t * t) (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S n))). apply (Qle_trans _ ((1 / 2) * (t * t))).
      * exact (d09_q_mult_le_r (1 / 2 - q_pow (1 / 2)%Q (Datatypes.S n)) (1 / 2) (t * t) Hq2 Htsq).
      * apply (Qle_trans _ (1 * (t * t))).
        -- exact (d09_q_mult_le_r (1 / 2) 1 (t * t) Hq3 Htsq).
        -- apply qeq_le. ring. Qed.
Lemma d09_lt_opp_both : forall x y : Real, real_lt x y -> real_lt (real_opp y) (real_opp x).
Proof. intros x y H. destruct x as [xu Hx]. destruct y as [yu Hy]. destruct H as [eps [Heps [N HN]]]. exists eps. split; [exact Heps |]. exists N. intros n Hn.
  assert (Hs : projT1 (real_opp (existT (fun s : Qseq => cauchy s) xu Hx)) n
               - projT1 (real_opp (existT (fun s : Qseq => cauchy s) yu Hy)) n == projT1 (existT (fun s : Qseq => cauchy s) yu Hy) n
                  - projT1 (existT (fun s : Qseq => cauchy s) xu Hx) n).
  { cbn [projT1 real_opp]. ring. } exact (qltT_eq_compat_r (projT1 (real_opp (existT (fun s : Qseq => cauchy s) xu Hx)) n
            - projT1 (real_opp (existT (fun s : Qseq => cauchy s) yu Hy)) n) (projT1 (existT (fun s : Qseq => cauchy s) yu Hy) n
            - projT1 (existT (fun s : Qseq => cauchy s) xu Hx) n) eps Hs (HN n Hn)). Qed.
Lemma d09_abs_split : forall (d w : Real), real_lt (real_abs d) w -> And (real_lt d w) (real_lt (real_opp w) d). Proof.
  intros d w Hwin. destruct Hwin as [eps [Heps [N HN]]]. split.
  - exists eps. split; [exact Heps |]. exists N. intros n Hn. assert (Hle : Qle (projT1 d n) (Qabs (projT1 d n))) by apply Qle_Qabs. apply Qlt_to_QltT.
    apply (Qlt_le_trans eps (projT1 w n - Qabs (projT1 d n))).
    + rewrite <- (real_abs_proj d n). exact (QltT_to_Qlt _ _ (HN n Hn)).
    + apply Qplus_le_compat; [apply Qle_refl |]. apply (Qopp_le_compat (projT1 d n) (Qabs (projT1 d n)) Hle).
  - exists eps. split; [exact Heps |]. exists N. intros n Hn. assert (Hle2 : Qle (- projT1 d n) (Qabs (projT1 d n))).
    { apply (Qle_trans _ (Qabs (- projT1 d n))); [apply Qle_Qabs |]. apply qeq_le. apply Qabs_opp. } assert (Habs2 : Qle (- Qabs (projT1 d n)) (projT1 d n)).
    { apply (Qle_trans _ (- (- projT1 d n))).
      - exact (Qopp_le_compat (- projT1 d n) (Qabs (projT1 d n)) Hle2).
      - exact (qeq_le _ _ (Qopp_involutive (projT1 d n))). } apply Qlt_to_QltT. apply (Qlt_le_trans eps (projT1 w n - Qabs (projT1 d n))).
    + rewrite <- (real_abs_proj d n). exact (QltT_to_Qlt _ _ (HN n Hn)).
    + rewrite (real_opp_proj w n). apply (Qle_trans _ (projT1 w n + projT1 d n)).
      -- apply Qplus_le_compat; [apply Qle_refl | exact Habs2].
      -- apply qeq_le. ring. Qed.
Lemma d09_half_const_pos : real_lt real_zero (real_const (1 / 2)). Proof. apply real_const_pos. apply Qlt_to_QltT. unfold Qlt. simpl. lia. Qed.
Lemma d09_sin_half_zero_of_cos_one : forall u : Real, real_eq (cauchy_real_cos u) real_one ->
  real_eq (cauchy_real_sin (real_mult u (real_const (1 / 2)))) real_zero. Proof. intros u Hc.
  assert (Hsplit : real_eq (real_plus (real_mult u (real_const (1 / 2))) (real_mult u (real_const (1 / 2)))) u).
  { apply real_eq_of_zero_diff. intro n. rewrite ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n), ?(real_const_proj _ n). field. }
  assert (Hdbl : real_eq (real_plus (real_mult (cauchy_real_cos (real_mult u (real_const (1 / 2)))) (cauchy_real_cos (real_mult u (real_const (1 / 2)))))
                                    (real_opp (real_mult (cauchy_real_sin (real_mult u (real_const (1 / 2)))) (cauchy_real_sin (real_mult u (real_const (1 / 2))))))) real_one).
  { apply (real_eq_trans _ (cauchy_real_cos u)).
    - apply (real_eq_trans _ (cauchy_real_cos (real_plus (real_mult u (real_const (1 / 2))) (real_mult u (real_const (1 / 2)))))).
      + exact (real_eq_sym _ _ (rs_add_cos (real_mult u (real_const (1 / 2))) (real_mult u (real_const (1 / 2))))).
      + exact (real_cos_eq_compat _ _ Hsplit).
    - exact Hc. } assert (Hss : real_eq (real_plus (real_mult (cauchy_real_sin (real_mult u (real_const (1 / 2)))) (cauchy_real_sin (real_mult u (real_const (1 / 2)))))
                                   (real_mult (cauchy_real_sin (real_mult u (real_const (1 / 2)))) (cauchy_real_sin (real_mult u (real_const (1 / 2)))))) real_zero).
  { apply (real_eq_trans _ (real_plus (real_plus (real_mult (cauchy_real_cos (real_mult u (real_const (1 / 2)))) (cauchy_real_cos (real_mult u (real_const (1 / 2)))))
                                  (real_mult (cauchy_real_sin (real_mult u (real_const (1 / 2)))) (cauchy_real_sin (real_mult u (real_const (1 / 2))))))
                        (real_opp (real_plus (real_mult (cauchy_real_cos (real_mult u (real_const (1 / 2)))) (cauchy_real_cos (real_mult u (real_const (1 / 2)))))
                                             (real_opp (real_mult (cauchy_real_sin (real_mult u (real_const (1 / 2)))) (cauchy_real_sin (real_mult u (real_const (1 / 2)))))))))).
    - apply real_eq_of_zero_diff. intro n. repeat (rewrite !(real_plus_proj _ _ n)); repeat (rewrite !(real_mult_proj _ _ n)); repeat (rewrite !(real_opp_proj _ n));
      repeat (rewrite !(real_plus_proj _ _ n)); repeat (rewrite !(real_mult_proj _ _ n)); repeat (rewrite !(real_opp_proj _ n)); repeat (rewrite !(real_plus_proj _ _ n));
      repeat (rewrite !(real_mult_proj _ _ n)); repeat (rewrite !(real_opp_proj _ n)). cbn [projT1 real_one real_zero real_const]. ring.
    - apply (real_eq_trans _ (real_plus real_one (real_opp real_one))).
      + apply real_eq_minus_compat.
        * exact (real_pyth_cos_sq_sin_sq (real_mult u (real_const (1 / 2)))).
        * exact Hdbl.
      + apply real_eq_of_zero_diff. intro n. repeat (rewrite !(real_plus_proj _ _ n)); repeat (rewrite !(real_opp_proj _ n)); repeat (rewrite !(real_plus_proj _ _ n));
        repeat (rewrite !(real_opp_proj _ n)). cbn [projT1 real_one real_zero real_const]. ring. } exact (d09_sq_zero (cauchy_real_sin (real_mult u (real_const (1 / 2))))
           (d09_two_zero_cancel (real_mult (cauchy_real_sin (real_mult u (real_const (1 / 2)))) (cauchy_real_sin (real_mult u (real_const (1 / 2))))) Hss)). Qed.
Lemma d09_quarter_lt_two : real_lt (real_mult (real_const (1 / 2)) (real_plus pi_R (real_const (1 / 4)))) (real_const 2). Proof. assert (Hpi4 : real_lt pi_R (real_const 4)).
  { apply (real_lt_trans pi_R (real_const (10 / 3)) (real_const 4)).
    - exact d09_pi_R_lt_ten_thirds.
    - apply real_const_lt. unfold Qlt. simpl. lia. } assert (Hw : real_lt (real_plus pi_R (real_const (1 / 4))) (real_const 4)).
  { apply (real_lt_trans _ (real_const (10 / 3 + 1 / 4))).
    - apply (real_eq_lt_lt (real_plus pi_R (real_const (1 / 4))) (real_plus (real_const (1 / 4)) pi_R) (real_const (10 / 3 + 1 / 4))).
      + apply real_eq_of_zero_diff. intro n. rewrite ?(real_plus_proj _ _ n), ?(real_const_proj _ n). field.
      + apply (real_lt_eq_lt (real_plus (real_const (1 / 4)) pi_R) (real_plus (real_const (1 / 4)) (real_const (10 / 3))) (real_const (10 / 3 + 1 / 4))).
        -- exact (real_lt_plus_translate (real_const (1 / 4)) pi_R (real_const (10 / 3)) d09_pi_R_lt_ten_thirds).
        -- apply (real_eq_trans _ (real_plus (real_const (10 / 3)) (real_const (1 / 4)))).
           ** apply real_eq_of_zero_diff. intro n. rewrite ?(real_plus_proj _ _ n), ?(real_const_proj _ n). field.
           ** apply (real_eq_sym _ _ (d09_const_plus (10 / 3) (1 / 4))).
    - apply real_const_lt. unfold Qlt. simpl. lia. } apply (real_lt_eq_lt (real_mult (real_const (1 / 2)) (real_plus pi_R (real_const (1 / 4))))
             (real_mult (real_const (1 / 2)) (real_const 4)) (real_const 2)).
  - exact (real_mult_lt_compat_l (real_plus pi_R (real_const (1 / 4))) (real_const 4) (real_const (1 / 2)) Hw d09_half_const_pos).
  - apply real_eq_of_zero_diff. intro n. rewrite ?(real_plus_proj _ _ n), ?(real_mult_proj _ _ n), ?(real_const_proj _ n). field. Qed.
Lemma d09_window_pin : forall d : Real,
  real_lt (real_abs d) (real_plus pi_R (real_const (1 / 4))) -> real_eq (cauchy_real_cos d) real_one -> real_eq (cauchy_real_sin d) real_zero -> real_eq d real_zero. Proof.
  intros d Hwin Hc Hs. destruct (d09_abs_split d (real_plus pi_R (real_const (1 / 4))) Hwin) as [Hup Hdn].
  assert (Hhalf : forall u : Real, real_lt real_zero u -> real_lt real_zero (real_mult u (real_const (1 / 2)))).
  { intros u Hu. exact (d09_mult_pos_gen u (real_const (1 / 2)) Hu d09_half_const_pos). } assert (Hlt2 : forall u : Real, real_lt u (real_plus pi_R (real_const (1 / 4))) ->
            real_lt (real_mult u (real_const (1 / 2))) (real_const 2)).
  { intros u Hu. apply (real_eq_lt_lt (real_mult u (real_const (1 / 2))) (real_mult (real_const (1 / 2)) u) (real_const 2)).
    - apply real_eq_of_zero_diff. intro n. rewrite (real_mult_proj u (real_const (1 / 2)) n), (real_mult_proj (real_const (1 / 2)) u n). ring.
    - apply (real_lt_trans _ (real_mult (real_const (1 / 2)) (real_plus pi_R (real_const (1 / 4))))).
      + exact (real_mult_lt_compat_l u (real_plus pi_R (real_const (1 / 4))) (real_const (1 / 2)) Hu d09_half_const_pos).
      + exact d09_quarter_lt_two. } apply real_weak_trich.
  - intro Hneg. assert (Hu : real_lt real_zero (real_opp d)) by exact (d09_lt_zero_opp d Hneg). assert (Huw : real_lt (real_opp d) (real_plus pi_R (real_const (1 / 4)))).
    { apply (real_lt_eq_lt (real_opp d) (real_opp (real_opp (real_plus pi_R (real_const (1 / 4))))) (real_plus pi_R (real_const (1 / 4)))).
      - exact (d09_lt_opp_both (real_opp (real_plus pi_R (real_const (1 / 4)))) d Hdn).
      - exact (d09_opp_opp (real_plus pi_R (real_const (1 / 4)))). } assert (Hcu : real_eq (cauchy_real_cos (real_opp d)) real_one).
    { apply (real_eq_trans _ (cauchy_real_cos d)).
      - exact (real_cos_opp d).
      - exact Hc. } apply (real_lt_not_eq real_zero (cauchy_real_sin (real_mult (real_opp d) (real_const (1 / 2))))).
    + apply real_sin_pos_lt_two.
      * exact (Hhalf (real_opp d) Hu).
      * exact (Hlt2 (real_opp d) Huw).
    + exact (real_eq_sym _ _ (d09_sin_half_zero_of_cos_one (real_opp d) Hcu)).
  - intro Hpos. apply (real_lt_not_eq real_zero (cauchy_real_sin (real_mult d (real_const (1 / 2))))).
    + apply real_sin_pos_lt_two.
      * exact (Hhalf d Hpos).
      * exact (Hlt2 d Hup).
    + exact (real_eq_sym _ _ (d09_sin_half_zero_of_cos_one d Hc)).
Qed.