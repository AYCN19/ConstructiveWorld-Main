(* ConstructiveWorld-Main - the two-pi lattice witness of the denominator zero set *)
(** * GaC2_09_DenomZeroSet_g - - the two-pi lattice witness of the denominator zero
      set
    Mission.  Node C2-09 (segment C2, slot W1), witness piece of the
      denominator zero set family.  Casts the (b) roster statement of the C2-09 card
      [e09_lattice_witness]: a vanishing denominator at Re s = 1
      yields an explicit integer k with t * ln 2 = 2 pi k.  The front
      reduces the vanishing denominator to exp(i (ln 2 * t)) = 1 by
      the pair-projection faces; the witness comes from the rounding
      core [e09_grid_pin] of GaC2_09_DenomZeroSet_f.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [ZArith], [Setoid], [Morphisms],
      [Arith.Arith], [Lia]; [S01_BaseRing] (selective [NatLe]/[And]
      import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog],
      [GaC1_Iface_Cx], [GaC1_Iface_Real], [GaC2_09_DenomZeroSet_a]
      through [f] (named faces in Notes).
    References.  drafts_C2.md C2-09 card (:718-739) with the registered
      L11/L12 concretizations; the v16 receipt section VII casting spec.
    Constructivity.  Every named construction is carried by [Set]; zero
      Sections, zero assumed constants, zero admitted goals; every
      proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_g.v]; flat build
      directory, acceptance via 50_toolkit/accept_node.py. *)
Require S01_BaseRing.
(** Notes.  Named consumed faces behind the Dependencies field:
    [a]: [d09_rmult_zero_l_pt], [d09_rmult_opp_l_pt],
    [d09_cRe_scale], [d09_cIm_scale]; [b]: [d09_ln2],
    [d09_two_pi], [d09_opp_opp], [d09_rone_minus_rone],
    [d09_c_plus_one_opp_eq_zero], [d09_denom], [two_pow_1ms],
    [d09_cRe_one_minus], [d09_cIm_opp_shift]; [f]:
    [e09_grid_pin], [e09_exp_opp_two_pi], [e09_exp_shift],
    [e09_proj_cos_sin]; [CxRealPairExpLog]: [c_exp_conj],
    [c_norm_sq_zero_elim], [c_mult_one], [c_mult_congr],
    [cauchy_real_exp_zero]; [S07_RealSetoidExpLog]:
    [RealSetoid.real_eq_plus_compat],
    [RealSetoid.real_eq_mult_compat],
    [RealSetoid.real_eq_opp_compat], [real_eq_of_zero_diff];
    [GaC1_Iface_Cx] supplies [c_exp] and the pair carrier faces. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Local Open Scope Q_scope.

Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Require Import GaC2_09_DenomZeroSet_e.
Require Import GaC2_09_DenomZeroSet_f.

Lemma e09_lattice_witness : forall (s : Cx) (t : Real),
  real_eq (cIm s) t -> real_eq (cRe s) real_one ->
  real_eq (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms s)))) real_zero ->
  sigT (fun k : Z => real_eq (real_mult t d09_ln2) (d09_two_pi k)).
Proof.
  intros s t Ht Hre Hn.
  assert (Hde : c_eq (d09_denom s) c_zero)
    by (apply c_norm_sq_zero_elim; exact Hn).
  assert (Hep : c_eq (two_pow_1ms s) c_one)
    by (apply (d09_c_plus_one_opp_eq_zero (two_pow_1ms s)); exact Hde).
  assert (Hone : real_eq (real_plus real_one (real_opp (cRe s)))
                         (real_plus real_one (real_opp real_one))).
  { apply RealSetoid.real_eq_plus_compat;
      [apply real_eq_refl
      | exact (RealSetoid.real_eq_opp_compat (cRe s) real_one Hre)]. }
  assert (Hw0 : real_eq (cRe (c_scale d09_ln2 (c_plus c_one (c_opp s))))
                        real_zero).
  { apply (real_eq_trans _ (real_mult d09_ln2 (cRe (c_plus c_one (c_opp s))))).
    - exact (d09_cRe_scale d09_ln2 (c_plus c_one (c_opp s))).
    - apply (real_eq_trans _
               (real_mult d09_ln2 (real_plus real_one (real_opp (cRe s))))).
      + apply RealSetoid.real_eq_mult_compat;
          [apply real_eq_refl | exact (d09_cRe_one_minus s)].
      + apply (real_eq_trans _
                 (real_mult d09_ln2 (real_plus real_one (real_opp real_one)))).
        * apply RealSetoid.real_eq_mult_compat;
            [apply real_eq_refl | exact Hone].
        * apply (real_eq_trans _ (real_mult d09_ln2 real_zero)).
          -- apply RealSetoid.real_eq_mult_compat;
               [apply real_eq_refl | exact d09_rone_minus_rone].
          -- exact (real_eq_sym _ _ (d09_rmult_zero_l_pt d09_ln2)). }
  assert (Hw1 : real_eq (cIm (c_scale d09_ln2 (c_plus c_one (c_opp s))))
                        (real_opp (real_mult d09_ln2 t))).
  { apply (real_eq_trans _ (real_mult d09_ln2 (cIm (c_plus c_one (c_opp s))))).
    - exact (d09_cIm_scale d09_ln2 (c_plus c_one (c_opp s))).
    - apply (real_eq_trans _ (real_mult d09_ln2 (real_opp (cIm s)))).
      + apply RealSetoid.real_eq_mult_compat;
          [apply real_eq_refl | exact (d09_cIm_opp_shift s)].
      + apply (real_eq_trans _ (real_mult d09_ln2 (real_opp t))).
        * apply RealSetoid.real_eq_mult_compat;
            [apply real_eq_refl
            | exact (RealSetoid.real_eq_opp_compat (cIm s) t Ht)].
        * apply (real_eq_trans _ (real_mult (real_opp t) d09_ln2)).
          -- apply real_mult_comm.
          -- apply (real_eq_trans _ (real_opp (real_mult t d09_ln2))).
             ++ exact (d09_rmult_opp_l_pt t d09_ln2).
             ++ apply RealSetoid.real_eq_opp_compat.
                exact (real_mult_comm t d09_ln2). }
  assert (Hpair : c_eq (c_scale d09_ln2 (c_plus c_one (c_opp s)))
                        (real_zero, real_opp (real_mult d09_ln2 t))).
  { unfold c_eq. split; assumption. }
  assert (Hce : c_eq (c_exp (real_zero, real_opp (real_mult d09_ln2 t))) c_one).
  { apply (c_eq_trans (c_exp (real_zero, real_opp (real_mult d09_ln2 t)))
             (c_exp (c_scale d09_ln2 (c_plus c_one (c_opp s))))).
    - apply (c_eq_sym _ _). apply d09_c_exp_congr. exact Hpair.
    - exact Hep. }
  assert (Hcf : c_eq (c_exp (real_zero, real_mult d09_ln2 t)) c_one).
  { assert (Hcj : c_eq (real_zero, real_mult d09_ln2 t)
                        (c_conj (real_zero, real_opp (real_mult d09_ln2 t)))).
    { unfold c_conj, c_eq. split.
      - apply real_eq_refl.
      - exact (real_eq_sym _ _ (d09_opp_opp (real_mult d09_ln2 t))). }
    apply (c_eq_trans _
             (c_conj (c_exp (real_zero, real_opp (real_mult d09_ln2 t))))).
    - apply (c_eq_trans (c_exp (real_zero, real_mult d09_ln2 t))
               (c_exp (c_conj (real_zero, real_opp (real_mult d09_ln2 t))))).
      + apply d09_c_exp_congr. exact Hcj.
      + exact (c_exp_conj (real_zero, real_opp (real_mult d09_ln2 t))).
    - apply (c_eq_trans _ (c_conj c_one)).
      + assert (Hcg : forall z w : Cx, c_eq z w -> c_eq (c_conj z) (c_conj w)).
        { intros z w Hz. unfold c_conj, c_eq. destruct Hz as [Hq1 Hq2].
          split; [exact Hq1 | exact (RealSetoid.real_eq_opp_compat _ _ Hq2)]. }
        apply (Hcg _ _ Hce).
      + unfold c_conj, c_one, c_eq. split.
        * apply real_eq_refl.
        * apply real_eq_of_zero_diff. intro n.
          cbn [projT1 real_opp real_zero fst snd]. ring_simplify. reflexivity. }
  assert (Hcf2 : c_eq (c_exp (real_zero, real_mult t d09_ln2)) c_one).
  { apply (c_eq_trans (c_exp (real_zero, real_mult t d09_ln2))
             (c_exp (real_zero, real_mult d09_ln2 t))).
    - apply d09_c_exp_congr.
      unfold c_eq. split.
      + apply real_eq_refl.
      + exact (real_mult_comm t d09_ln2).
    - exact Hcf. }
  destruct (e09_grid_pin (real_mult t d09_ln2) Hcf2) as [k Hk].
  exists k. exact Hk.
Defined.


(* ===================================================================== *)
(* Section 3. The ln 2 order face.                                       *)
(* ===================================================================== *)

Lemma f09_ln2_lt_one : real_lt d09_ln2 real_one.
Proof.
  assert (He1p : real_lt real_zero (cauchy_real_exp real_one))
    by exact (cauchy_real_exp_pos real_one).
  assert (Hlog : real_eq (cw_log (cauchy_real_exp real_one) He1p) real_one)
    by exact (log_inv_exp_neg_thm real_one He1p).
  assert (H12 : real_lt real_one (real_const 2)).
  { apply (real_eq_lt_lt real_one (real_const 1) (real_const 2)).
    - apply real_eq_of_zero_diff. intro n.
      unfold real_one, real_const. cbn [projT1]. ring.
    - apply real_const_lt. unfold Qlt. simpl. lia. }
  assert (H2e : real_lt (real_const 2) (cauchy_real_exp real_one)).
  { exists (1 / 4). split.
    - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
    - exists 2%nat. intros n Hn.
      assert (Hge : Qle (exp_partial 2%nat 1) (exp_partial n 1)).
      { apply (d09_q_ep_mono 1 2%nat n).
        - unfold Qle. simpl. lia.
        - apply NatLe_drop in Hn. lia. }
      assert (H512 : Qle (2 + 1 / 2) (exp_partial n 1)).
      { apply (Qle_trans (2 + 1 / 2) (exp_partial 2%nat 1) (exp_partial n 1)).
        - apply qeq_le. reflexivity.
        - exact Hge. }
      assert (H2lt : Qlt (1 / 4) (exp_partial n 1 - 2)).
      { apply (Qlt_le_trans (1 / 4) (1 / 2) (exp_partial n 1 - 2)).
        - change (Qlt (1 # 4) (1 # 2)). unfold Qlt. simpl. lia.
        - apply (proj2 (Qle_minus_iff (1 / 2) (exp_partial n 1 - 2))).
          change (0 <= exp_partial n 1 - 2 + - (1 / 2)).
          assert (Hbr : (exp_partial n 1 - 2 + - (1 / 2))%Q
                        == (exp_partial n 1 + - (2 + 1 / 2))) by field.
          rewrite Hbr.
          exact (proj1 (Qle_minus_iff (2 + 1 / 2) (exp_partial n 1)) H512). }
      assert (Heq : (exp_partial n 1 - 2)%Q
                    == (projT1 (cauchy_real_exp (real_const 1)) n
                        - projT1 (real_const 2) n)).
      { rewrite (exp_const_proj 1 n). cbn [projT1 real_const real_one]. ring. }
      assert (Hone : (projT1 (cauchy_real_exp (real_const 1)) n
                      - projT1 (real_const 2) n)%Q
                     == (projT1 (cauchy_real_exp real_one) n
                         - projT1 (real_const 2) n)).
      { cbn [projT1 real_one]. reflexivity. }
      assert (Heq2 : (exp_partial n 1 - 2)%Q
                     == (projT1 (cauchy_real_exp real_one) n
                         - projT1 (real_const 2) n)).
      { apply (Qeq_trans (exp_partial n 1 - 2)
                 (projT1 (cauchy_real_exp (real_const 1)) n
                  - projT1 (real_const 2) n)).
        - exact Heq.
        - exact Hone. }
      exact (qltT_eq_compat_r
                  (projT1 (cauchy_real_exp real_one) n - projT1 (real_const 2) n)
                  (exp_partial n 1 - 2) (1 / 4) (Qeq_sym _ _ Heq2)
                  (Qlt_to_QltT (1 / 4) (exp_partial n 1 - 2) H2lt)). }
  assert (Hmono : real_lt (cw_log (real_const 2) d09_two_pos)
                         (cw_log (cauchy_real_exp real_one) He1p)).
  { exact (real_log_lt_mono (real_const 2) (cauchy_real_exp real_one)
             d09_two_pos He1p H2e). }
  apply (RealSetoid.real_lt_compat (cw_log (real_const 2) d09_two_pos)
           d09_ln2 (cw_log (cauchy_real_exp real_one) He1p) real_one
           (real_eq_refl (cw_log (real_const 2) d09_two_pos)) Hlog Hmono).
Qed.
