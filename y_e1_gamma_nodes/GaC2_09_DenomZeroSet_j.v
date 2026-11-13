(* ConstructiveWorld-Main - the first-order face of the denominator zero set *)
(** * GaC2_09_DenomZeroSet_j - the (c) roster statement of the denominator zero
      set
    Mission.  Node C2-09 (segment C2, slot W1), first-order face of the
      denominator zero set family.  Casts [f09_first_order], the (c) roster
      statement of the C2-09 card: on the disk where |s - 1|^2 is Bishop-
      bounded by 3/4, the first-order Taylor remainder of the denominator
      R = (2^(1-s) - 1) + ln 2 (s - 1) satisfies
      |R|^2 <= 14 (ln 2)^2 |s - 1|^2 in the Bishop order [real_le_b],
      discharged through the pointwise engine of GaC2_09_DenomZeroSet_i.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [ZArith], [Setoid], [Morphisms], [Arith.Arith], [Lia];
      [S01_BaseRing] (selective [NatLe]/[And] import), [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [S10_KVQuantTrig],
      [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx],
      [GaC1_Iface_Real], and the family pieces [GaC2_09_DenomZeroSet_b],
      [d], [g], [i] (named faces in Notes).
    References.  drafts_C2.md C2-09 card (:718-739) with the registered
      L11/L12 concretizations and the bishop_ordinal_deviation and
      draft_sign_typo disclosures of the acceptance checkpoint.
    Constructivity.  Every named construction is carried by [Set]; zero
      Sections, zero assumed constants, zero admitted goals; every proof
      closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_j.v]; flat build
      directory, acceptance via 50_toolkit/accept_node.py. *)
Require S01_BaseRing.
(** Notes.  Named consumed faces behind the Dependencies field:
    [b]: [d09_ln2], [two_pow_1ms]; [d]: [d09_ln2_pos]; [g]:
    [f09_ln2_lt_one]; [i]: [e09_pointwise_bnd]; [e]: [e09q_abs_le_of_sq]
    (through the [h] chain); [h]: [e09_sub_norm_pt], [e09_rem_re_pt],
    [e09_rem_im_pt]; [CxRealPairCore]: [c_norm_sq_pt], [real_zero_pt],
    [real_one_pt]; [S02_CauchyComplete]: [real_mult_proj],
    [real_plus_proj], [real_const_proj]; [S03_QExp]: [q_square_nonneg];
    stdlib [QArith]: [Qlt_le_weak], [Qlt_le_trans], [Qle_minus_iff],
    [Qlt_minus_iff], [QltT_to_Qlt], [Qlt_to_QltT], [Qle_refl]. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
Require Import GaC2_09_DenomZeroSet_e.
Require Import GaC2_09_DenomZeroSet_g.
Require Import GaC2_09_DenomZeroSet_h.
Require Import GaC2_09_DenomZeroSet_i.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Local Open Scope Q_scope.

Lemma e09_sq_le_sum : forall u v : Q, Qle (u * u) (u * u + v * v).
Proof.
  intros u v. apply (Qle_trans _ (u * u + 0)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat (u * u) (u * u) 0 (v * v)
             (Qle_refl _) (q_square_nonneg v)).
Qed.

Lemma e09_sq_le_sum_r : forall u v : Q, Qle (v * v) (u * u + v * v).
Proof.
  intros u v. rewrite (Qplus_comm (u * u) (v * v)).
  apply (e09_sq_le_sum v u).
Qed.

Theorem f09_first_order : forall (s : Cx),
  real_le_b (c_norm_sq (c_plus s (c_opp c_one))) (real_const (3 / 4)) ->
  real_le_b (c_norm_sq (c_plus (c_plus (two_pow_1ms s) (c_opp c_one))
                                (c_scale d09_ln2 (c_plus s (c_opp c_one)))))
            (real_mult (real_mult (real_mult (real_const 14) d09_ln2) d09_ln2)
                       (c_norm_sq (c_plus s (c_opp c_one)))).
Proof.
  intros s Hpre. unfold real_le_b. intros epsr Hepsr.
  destruct Hepsr as [eps_q [H0q [N_eps Heps_pt]]].
  assert (Hq36 : real_lt real_zero (real_const (1 / 36))).
  { exists (1 / 72). split.
    - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
    - exists 0%nat. intros n Hn.
      apply Qlt_to_QltT. unfold Qlt. simpl. lia. }
  destruct (Hpre (real_const (1 / 36)) Hq36) as [eps_m [Hm0 [N_m Hpt_m]]].
  destruct f09_ln2_lt_one as [eps_l [Hl0 [N_l Hpt_l]]].
  destruct d09_ln2_pos as [eps_p [Hp0 [N_p Hpt_p]]].
  exists eps_q. split.
  - exact H0q.
  - exists (Nat.max N_eps (Nat.max N_m (Nat.max N_l (Nat.max N_p 3)))).
    intros n Hn. apply NatLe_drop in Hn.
    assert (Hne : (N_eps <= n)%nat) by lia.
    assert (Hnm : (N_m <= n)%nat) by lia.
    assert (Hnl : (N_l <= n)%nat) by lia.
    assert (Hnp : (N_p <= n)%nat) by lia.
    assert (Hge1 : (1 <= n)%nat) by lia.
    apply Qlt_to_QltT.
    rewrite (real_plus_proj _ _ n).
    rewrite ?(real_mult_proj _ _ n).
    rewrite (real_const_proj 14 n).
    rewrite (e09_sub_norm_pt s n).
    rewrite c_norm_sq_pt.
    rewrite (e09_rem_re_pt s n), (e09_rem_im_pt s n).
    assert (Hz : projT1 real_zero n == 0) by apply real_zero_pt.
    assert (Hep : Qlt eps_q (projT1 epsr n)).
    { pose proof (Heps_pt n (NatLe_lift N_eps n Hne)) as Hhp.
      apply QltT_to_Qlt in Hhp. rewrite Hz in Hhp.
      assert (Hz2 : projT1 epsr n - 0 == projT1 epsr n) by ring.
      rewrite Hz2 in Hhp. exact Hhp. }
    assert (HLlt : Qlt eps_l (1 - projT1 d09_ln2 n)).
    { pose proof (Hpt_l n (NatLe_lift N_l n Hnl)) as Hhp.
      apply QltT_to_Qlt in Hhp. rewrite (real_one_pt n) in Hhp.
      exact Hhp. }
    assert (HLup : Qle (projT1 d09_ln2 n) 1).
    { apply (Qlt_le_weak _ _).
      apply (Qlt_trans _ (1 - eps_l) 1).
      - apply (proj2 (Qlt_minus_iff (projT1 d09_ln2 n) (1 - eps_l))).
        assert (Hrw : ((1 - eps_l) - projT1 d09_ln2 n)%Q
                      == ((1 - projT1 d09_ln2 n) - eps_l)%Q) by ring.
        rewrite Hrw.
        exact (proj1 (Qlt_minus_iff eps_l (1 - projT1 d09_ln2 n)) HLlt).
      - apply (proj2 (Qlt_minus_iff (1 - eps_l) 1)).
        assert (Hrw2 : (1 - (1 - eps_l))%Q == eps_l) by ring.
        rewrite Hrw2. exact (QltT_to_Qlt 0 eps_l Hl0). }
    assert (HLgt : Qlt 0 (projT1 d09_ln2 n)).
    { pose proof (Hpt_p n (NatLe_lift N_p n Hnp)) as Hhp.
      apply QltT_to_Qlt in Hhp. rewrite Hz in Hhp.
      assert (Hz2 : projT1 d09_ln2 n - 0 == projT1 d09_ln2 n) by ring.
      rewrite Hz2 in Hhp.
      apply (Qlt_trans 0 eps_p (projT1 d09_ln2 n)).
      - exact (QltT_to_Qlt 0 eps_p Hp0).
      - exact Hhp. }
    assert (HLsq : Qle (projT1 d09_ln2 n * projT1 d09_ln2 n) 1).
    { apply (Qle_trans _ (1 * projT1 d09_ln2 n) 1).
      - apply (Qmult_le_compat_r (projT1 d09_ln2 n) 1 (projT1 d09_ln2 n)).
        + exact HLup.
        + apply (Qlt_le_weak 0 _). exact HLgt.
      - rewrite Qmult_1_l. exact HLup. }
    assert (HX0 : Qle 0 ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                           + projT1 (cIm s) n * projT1 (cIm s) n)).
    { apply (Qle_trans _ (0 + 0)).
      - apply qeq_le. ring.
      - apply Qplus_le_compat; apply q_square_nonneg. }
    assert (HX79 : Qlt ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                          + projT1 (cIm s) n * projT1 (cIm s) n) (7 / 9)).
    { pose proof (Hpt_m n (NatLe_lift N_m n Hnm)) as Hhm.
      apply QltT_to_Qlt in Hhm.
      rewrite (real_plus_proj _ _ n), (real_const_proj (3 / 4) n),
        (real_const_proj (1 / 36) n) in Hhm.
      assert (Hc79 : (3 / 4 + 1 / 36)%Q == (7 / 9)) by field.
      rewrite Hc79 in Hhm.
      rewrite (e09_sub_norm_pt s n) in Hhm.
      assert (Hm0q : Qlt 0 eps_m) by (apply QltT_to_Qlt; exact Hm0).
      apply (Qlt_le_trans _ ((7 / 9) - eps_m) (7 / 9)).
      - apply (proj2 (Qlt_minus_iff _ ((7 / 9) - eps_m))).
        assert (Hrw : (((7 / 9) - eps_m)
                         - ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                            + projT1 (cIm s) n * projT1 (cIm s) n))%Q
                      == (((7 / 9) - ((projT1 (cRe s) n - 1)
                                        * (projT1 (cRe s) n - 1)
                                         + projT1 (cIm s) n * projT1 (cIm s) n))
                            - eps_m)%Q) by ring.
        rewrite Hrw.
        exact (proj1 (Qlt_minus_iff eps_m
                       ((7 / 9) - ((projT1 (cRe s) n - 1)
                                     * (projT1 (cRe s) n - 1)
                                      + projT1 (cIm s) n * projT1 (cIm s) n)))
                 Hhm).
      - apply (Qlt_le_weak _ _).
        apply (proj2 (Qlt_minus_iff ((7 / 9) - eps_m) (7 / 9))).
        assert (Hrw2 : ((7 / 9) - ((7 / 9) - eps_m))%Q == eps_m) by ring.
        rewrite Hrw2. exact Hm0q. }
    assert (HW9lt : Qlt (projT1 d09_ln2 n * projT1 d09_ln2 n
                           * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                              + projT1 (cIm s) n * projT1 (cIm s) n)) (7 / 9)).
    { apply (Qle_lt_trans _ ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                               + projT1 (cIm s) n * projT1 (cIm s) n) (7 / 9)).
      - apply (Qle_trans _ (1 * ((projT1 (cRe s) n - 1)
                                   * (projT1 (cRe s) n - 1)
                                  + projT1 (cIm s) n * projT1 (cIm s) n))).
        + apply (Qmult_le_compat_r
                   (projT1 d09_ln2 n * projT1 d09_ln2 n) 1
                   ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                    + projT1 (cIm s) n * projT1 (cIm s) n)).
          ++ exact HLsq.
          ++ exact HX0.
        + rewrite Qmult_1_l. apply Qle_refl.
      - exact HX79. }
    assert (HWeq : ((projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                      * (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                    + (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                      * (- (projT1 d09_ln2 n * projT1 (cIm s) n)))%Q
                   == (projT1 d09_ln2 n * projT1 d09_ln2 n
                         * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                            + projT1 (cIm s) n * projT1 (cIm s) n))%Q)
      by field.
    assert (HA1' : Qle (Qabs (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))) 1).
    { apply (e09q_abs_le_of_sq _ 1).
      - apply (Qlt_le_weak 0 1). unfold Qlt. simpl. lia.
      - apply (Qle_trans _ ((projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                              * (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                            + (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                              * (- (projT1 d09_ln2 n * projT1 (cIm s) n)))).
        + apply (e09_sq_le_sum
                   (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                   (- (projT1 d09_ln2 n * projT1 (cIm s) n))).
        + rewrite HWeq.
          apply (Qle_trans _ (7 / 9)).
          * exact (Qlt_le_weak _ _ HW9lt).
          * unfold Qle. simpl. lia. }
    assert (HB1' : Qle (Qabs (- (projT1 d09_ln2 n * projT1 (cIm s) n))) 1).
    { apply (e09q_abs_le_of_sq _ 1).
      - apply (Qlt_le_weak 0 1). unfold Qlt. simpl. lia.
      - apply (Qle_trans _ ((projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                              * (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                            + (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                              * (- (projT1 d09_ln2 n * projT1 (cIm s) n)))).
        + apply (e09_sq_le_sum_r
                   (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                   (- (projT1 d09_ln2 n * projT1 (cIm s) n))).
        + rewrite HWeq.
          apply (Qle_trans _ (7 / 9)).
          * exact (Qlt_le_weak _ _ HW9lt).
          * unfold Qle. simpl. lia. }
    assert (Hmachine : Qle
      ((exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
          * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
          + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
         * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
              * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
              + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
        + (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
             * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
             + projT1 d09_ln2 n * projT1 (cIm s) n)
           * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                + projT1 d09_ln2 n * projT1 (cIm s) n))
      (14 * projT1 d09_ln2 n * projT1 d09_ln2 n
         * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
            + projT1 (cIm s) n * projT1 (cIm s) n))).
    { apply (e09_pointwise_bnd n (projT1 d09_ln2 n) (projT1 (cRe s) n)
               (projT1 (cIm s) n) HA1' HB1'
               (Qlt_le_weak _ _ HW9lt) Hge1). }
    assert (HD : Qle 0
      (14 * projT1 d09_ln2 n * projT1 d09_ln2 n
         * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
            + projT1 (cIm s) n * projT1 (cIm s) n)
       - ((exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
             * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
             + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
            * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                 * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
                 + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
          + (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
               * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
               + projT1 d09_ln2 n * projT1 (cIm s) n)
             * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                  * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                  + projT1 d09_ln2 n * projT1 (cIm s) n)))).
    { exact (proj1 (Qle_minus_iff _ _) Hmachine). }
    assert (HTle : Qle (projT1 epsr n)
      ((14 * projT1 d09_ln2 n * projT1 d09_ln2 n
          * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
             + projT1 (cIm s) n * projT1 (cIm s) n)
         + projT1 epsr n)
        - ((exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
              * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
              + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
             * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                  * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                  - 1 + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
           + (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                + projT1 d09_ln2 n * projT1 (cIm s) n)
              * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                   * sin_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                   + projT1 d09_ln2 n * projT1 (cIm s) n)))).
    { apply (proj2 (Qle_minus_iff _ _)).
      assert (Hrw : (((14 * projT1 d09_ln2 n * projT1 d09_ln2 n
                         * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                            + projT1 (cIm s) n * projT1 (cIm s) n)
                        + projT1 epsr n)
                      - ((exp_partial n (projT1 d09_ln2 n
                                              * (1 - projT1 (cRe s) n))
                            * cos_partial n
                              (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
                            + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
                           * (exp_partial n (projT1 d09_ln2 n
                                                * (1 - projT1 (cRe s) n))
                              * cos_partial n
                                (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
                                + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
                         + (exp_partial n (projT1 d09_ln2 n
                                              * (1 - projT1 (cRe s) n))
                              * sin_partial n
                                (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                                + projT1 d09_ln2 n * projT1 (cIm s) n)
                           * (exp_partial n (projT1 d09_ln2 n
                                                * (1 - projT1 (cRe s) n))
                              * sin_partial n
                                (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                                + projT1 d09_ln2 n * projT1 (cIm s) n)))
                     - projT1 epsr n)%Q
                    == (14 * projT1 d09_ln2 n * projT1 d09_ln2 n
                          * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                             + projT1 (cIm s) n * projT1 (cIm s) n)
                       - ((exp_partial n (projT1 d09_ln2 n
                                               * (1 - projT1 (cRe s) n))
                             * cos_partial n
                               (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
                               + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
                            * (exp_partial n (projT1 d09_ln2 n
                                                 * (1 - projT1 (cRe s) n))
                               * cos_partial n
                                 (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                                 - 1
                                 + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
                          + (exp_partial n (projT1 d09_ln2 n
                                               * (1 - projT1 (cRe s) n))
                             * sin_partial n
                               (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                               + projT1 d09_ln2 n * projT1 (cIm s) n)
                            * (exp_partial n (projT1 d09_ln2 n
                                                 * (1 - projT1 (cRe s) n))
                               * sin_partial n
                                 (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                                 + projT1 d09_ln2 n * projT1 (cIm s) n)))%Q)
      by ring.
      rewrite Hrw. exact HD. }
    apply (Qlt_le_trans eps_q (projT1 epsr n)
             ((14 * projT1 d09_ln2 n * projT1 d09_ln2 n
                 * ((projT1 (cRe s) n - 1) * (projT1 (cRe s) n - 1)
                    + projT1 (cIm s) n * projT1 (cIm s) n)
                + projT1 epsr n)
               - ((exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                    * cos_partial n (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                    - 1 + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
                   * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                        * cos_partial n
                          (- (projT1 d09_ln2 n * projT1 (cIm s) n)) - 1
                          + projT1 d09_ln2 n * (projT1 (cRe s) n - 1))
                  + (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                       * sin_partial n
                         (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                         + projT1 d09_ln2 n * projT1 (cIm s) n)
                     * (exp_partial n (projT1 d09_ln2 n * (1 - projT1 (cRe s) n))
                          * sin_partial n
                            (- (projT1 d09_ln2 n * projT1 (cIm s) n))
                            + projT1 d09_ln2 n * projT1 (cIm s) n)))).
    + exact Hep.
    + exact HTle.
Qed.
