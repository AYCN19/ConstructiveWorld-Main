(* ConstructiveWorld-Main - the machine cluster piece of the
   denominator zero set: the real-order cancellation kit, the
   pointwise real algebra faces, and the pair helpers. *)

(** * GaC2_09_DenomZeroSet_a: machine cluster of the denominator zero set.

    Mission.  Node C2-09 (segment C2, slot W1), machine piece.  The
      real-order cancellation kit consumed by the zero set faces
      ([d09_lt_zero_opp_rev], [d09_lt_zero_opp], [d09_mult_pos_gen],
      [d09_mult_cancel_pos], [d09_sq_zero], [d09_two_zero_cancel]),
      the pointwise algebra faces ([d09_rplus_zero_l_pt],
      [d09_rmult_zero_l_pt], [d09_rmult_opp_opp],
      [d09_rmult_opp_l_pt], [d09_rone_minus_rone]), and the pair
      helpers ([d09_cRe_scale], [d09_cIm_scale], [d09_norm_wd],
      [d09_norm_one], [d09_c_eq_shift], [d09_c_opp_zero],
      [d09_cIm_plus_opp]).  All 18 items are pure real/pair algebra,
      consumed by the on-disk companion pieces
      GaC2_09_DenomZeroSet_b.v and GaC2_09_DenomZeroSet_c.v.

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires [S01_BaseRing] (selective [NatLe] import), [S02]
      (real carrier, order algebra, [real_eq_of_zero_diff] ring
      route, [real_mult_comm], [real_mult_zero], [real_plus_comm],
      [real_plus_zero]), [S03_QExp] ([cauchy_real_exp]),
      [S07_RealSetoidExpLog] ([real_weak_trich],
      [real_lt_mult_compat], [real_lt_plus_compat],
      [real_lt_opp_plus], [real_log_one], [real_lt_zero_one],
      [cauchy_real_exp_zero], [cauchy_real_exp_wd]),
      [S10_KVQuantTrig] ([real_cos_opp], [real_sin_opp],
      [real_cos_eq_compat], [real_sin_eq_compat]),
      [CxRealPairCore] + [CxRealPairExpLog] (pair carrier,
      [real_mult_opp_r], [real_mult_one_l]), [GaC1_Iface_Cx] (the
      C1-16 modulus identity [gaC1_16_norm_sq_exp]), and
      [GaC1_Iface_Real] (C1-01 strict log monotonicity
      [gaC1_01_log_lt_mono], C1-04 rational bridge
      [gaC1_04_qlt_const_lt], C1-05 exp injectivity
      [gaC1_05_exp_inj]) of this development.

    References.  drafts_C2.md C2.09 statement sketch (the machine
      cluster slot W1: pure real-order and pair algebra consumed by
      the zero set faces of the companion pieces); the polar form of
      the complex exponential mirrored by [CxRealPairExpLog];
      Titchmarsh Ch.1 the eta quotient denominator 1 - 2^(1-s).

    Constructivity.  Every named construction is carried by [Set];
      the order predicates are the Set-sorted [real_lt] / [real_eq];
      no Section, no Hypothesis, no assumed constant; every proof
      closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_a.v] from the flat build
      directory, thermal guard wrapper. *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Arith.Arith Lia.

Search Qabs Qeq.


(* ===================================================================== *)
(* Section 1. Pointwise real ring faces (constructor-form arguments).     *)
(* ===================================================================== *)

Lemma d09_rplus_zero_l_pt : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. exact (g1_plus_zero_l x).
Qed.

Lemma d09_rmult_zero_l_pt : forall q : Real,
  real_eq real_zero (real_mult q real_zero).
Proof.
  intros [qa Ha]. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_rmult_opp_opp : forall p q : Real,
  real_eq (real_mult (real_opp p) (real_opp q)) (real_mult p q).
Proof.
  intros [pa Hpa] [qa Haq]. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_rmult_opp_l_pt : forall p q : Real,
  real_eq (real_mult (real_opp p) q) (real_opp (real_mult p q)).
Proof.
  intros [pa Hpa] [qa Haq]. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_lt_zero_opp_rev : forall x : Real,
  real_lt real_zero (real_opp x) -> real_lt x real_zero.
Proof.
  intros [u Hu] H.
  destruct H as [eps [Heps [N HN]]].
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn.
    specialize (HN n Hn).
    assert (Hcmp : (eps ?= projT1 real_zero n - projT1
                             (existT (fun s : Qseq => cauchy s) u Hu) n)
                   = (eps ?= projT1 (real_opp (existT (fun s : Qseq => cauchy s)
                                               u Hu)) n
                        - projT1 real_zero n)).
    assert (Hid : projT1 real_zero n
                    - projT1 (existT (fun s : Qseq => cauchy s) u Hu) n
                  == projT1 (real_opp (existT (fun s : Qseq => cauchy s)
                                         u Hu)) n
                    - projT1 real_zero n).
    { cbn [projT1 real_zero real_opp]. ring. }
    { apply Qcompare_comp.
      - apply Qeq_refl.
      - exact Hid. }
    unfold QltT, Qlt_bool. rewrite Hcmp. exact HN.
Qed.

Lemma d09_lt_zero_opp : forall x : Real,
  real_lt x real_zero -> real_lt real_zero (real_opp x).
Proof.
  intros x H.
  apply (real_lt_eq_lt real_zero (real_plus real_zero (real_opp x)) (real_opp x)).
  - exact (real_lt_opp_plus x real_zero H).
  - exact (d09_rplus_zero_l_pt (real_opp x)).
Qed.

Lemma d09_mult_pos_gen : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_lt real_zero (real_mult a b).
Proof.
  intros a b Ha Hb.
  apply (real_eq_lt_lt real_zero (real_mult a real_zero) (real_mult a b)).
  - exact (d09_rmult_zero_l_pt a).
  - exact (real_lt_mult_compat real_zero b a Ha Hb).
Qed.

Lemma d09_mult_cancel_pos : forall p q : Real,
  real_lt real_zero q ->
  real_eq (real_mult p q) real_zero -> real_eq p real_zero.
Proof.
  intros p q Hq Hpq. apply real_weak_trich.
  - intro Hp.
    assert (Hnp : real_lt real_zero (real_opp p))
      by (apply d09_lt_zero_opp; exact Hp).
    assert (Hlt : real_lt (real_mult p q) real_zero).
    { apply (d09_lt_zero_opp_rev (real_mult p q)).
      apply (real_lt_eq_lt real_zero
               (real_mult (real_opp p) q)
               (real_opp (real_mult p q))).
      - exact (d09_mult_pos_gen (real_opp p) q Hnp Hq).
      - exact (d09_rmult_opp_l_pt p q). }
    exact (real_lt_not_eq (real_mult p q) real_zero Hlt Hpq).
  - intro Hp.
    exact (real_lt_not_eq real_zero (real_mult p q)
             (d09_mult_pos_gen p q Hp Hq) (real_eq_sym _ _ Hpq)).
Qed.

Lemma d09_sq_zero : forall v : Real,
  real_eq (real_mult v v) real_zero -> real_eq v real_zero.
Proof.
  intros v Hv. apply real_weak_trich.
  - intro Hvneg.
    assert (Hn : real_lt real_zero (real_opp v))
      by (apply d09_lt_zero_opp; exact Hvneg).
    assert (Hlt : real_lt real_zero (real_mult v v)).
    { apply (real_lt_eq_lt real_zero
               (real_mult (real_opp v) (real_opp v)) (real_mult v v)).
      - exact (d09_mult_pos_gen (real_opp v) (real_opp v) Hn Hn).
      - exact (d09_rmult_opp_opp v v). }
    exact (real_lt_not_eq real_zero (real_mult v v) Hlt
             (real_eq_sym _ _ Hv)).
  - intro Hvpos.
    exact (real_lt_not_eq real_zero (real_mult v v)
             (d09_mult_pos_gen v v Hvpos Hvpos) (real_eq_sym _ _ Hv)).
Qed.

Lemma d09_two_zero_cancel : forall v : Real,
  real_eq (real_plus v v) real_zero -> real_eq v real_zero.
Proof.
  intros [u Hu] H eps Heps.
  destruct (H eps Heps) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  assert (Hle : Qle (Qabs (u n)) (Qabs (u n + u n - 0))).
  { apply (Qle_trans _ (Qabs (u n * (1 + 1)%Q))).
    - assert (Hid2 : Qabs (u n * (1 + 1)%Q) == (1 + 1)%Q * Qabs (u n)).
      { assert (Hq3 : Qabs (u n * (1 + 1)%Q)
                          == Qabs (u n) * Qabs (1 + 1)%Q)
          by exact (Qabs_Qmult (u n) (1 + 1)%Q).
        assert (Hq4 : Qabs (1 + 1)%Q == (1 + 1)%Q) by reflexivity.
        rewrite Hq3. rewrite Hq4. ring. }
      apply (Qle_trans _ ((1 + 1)%Q * Qabs (u n))).
      + apply (Qle_trans _ (1 * Qabs (u n))%Q).
        * assert (Hid : Qabs (u n) == 1 * Qabs (u n)) by ring.
          exact (qeq_le (Qabs (u n)) (1 * Qabs (u n)) Hid).
        * apply (Qmult_le_compat_r 1 (1 + 1)%Q (Qabs (u n))).
          -- assert (H12 : Qlt 1 (1 + 1)%Q) by (unfold Qlt; simpl; lia).
             exact (Qlt_le_weak 1 (1 + 1)%Q H12).
          -- apply Qabs_nonneg.
      + exact (qeq_le ((1 + 1)%Q * Qabs (u n))
                 (Qabs (u n * (1 + 1)%Q)) (Qeq_sym _ _ Hid2)).
    - assert (Hid3 : u n * (1 + 1)%Q == u n + u n - 0) by ring.
      exact (qeq_le _ _ (Qabs_wd _ _ Hid3)). }
  pose proof (QltT_to_Qlt _ _ HN) as Hq.
  assert (Hq2 : Qlt (Qabs (u n)) eps).
  { exact (Qle_lt_trans (Qabs (u n)) (Qabs (u n + u n - 0)) eps Hle Hq). }
  assert (Hcmp : (Qabs (projT1 (existT (fun s : Qseq => cauchy s) u Hu) n
                           - projT1 real_zero n) ?= eps)
                 = (Qabs (u n) ?= eps)).
  { apply Qcompare_comp.
    - apply Qabs_wd. cbn [projT1 real_zero]. ring.
    - apply Qeq_refl. }
  unfold QltT, Qlt_bool. rewrite Hcmp.
  exact (Qlt_to_QltT _ _ Hq2).
Qed.

(* ===================================================================== *)
(* Section 2. Pair helpers.                                               *)
(* ===================================================================== *)

Lemma d09_cRe_scale : forall (a : Real) (z : Cx),
  real_eq (cRe (c_scale a z)) (real_mult a (cRe z)).
Proof.
  intros a [p q]. destruct a as [ra Ha].
  destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_cIm_scale : forall (a : Real) (z : Cx),
  real_eq (cIm (c_scale a z)) (real_mult a (cIm z)).
Proof.
  intros a [p q]. destruct a as [ra Ha].
  destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_norm_wd : forall z w : Cx,
  c_eq z w -> real_eq (c_norm_sq z) (c_norm_sq w).
Proof.
  intros z w Hz. unfold c_eq in Hz. destruct Hz as [Hr Hi].
  apply (real_eq_trans (c_norm_sq z)
           (real_plus (real_mult (cRe z) (cRe z))
                      (real_mult (cIm z) (cIm z)))
           (c_norm_sq w)).
  - apply real_eq_refl.
  - apply (real_eq_trans _
           (real_plus (real_mult (cRe w) (cRe w))
                      (real_mult (cIm w) (cIm w)))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply RealSetoid.real_eq_mult_compat. exact Hr. exact Hr.
      * apply RealSetoid.real_eq_mult_compat. exact Hi. exact Hi.
    + apply real_eq_refl.
Qed.

Lemma d09_norm_one : real_eq (c_norm_sq c_one) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 c_norm_sq c_one cRe cIm real_plus real_mult real_one real_zero fst snd].
  ring.
Qed.

(* Pointwise ring face: z == 1 - (1 - z) on the pair carrier. *)
Lemma d09_c_eq_shift : forall z : Cx,
  c_eq z (c_plus c_one (c_opp (c_plus c_one (c_opp z)))).
Proof.
  intros [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_c_opp_zero : c_eq (c_opp c_zero) c_zero.
Proof.
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_one c_zero c_scale c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma d09_rone_minus_rone : real_eq (real_plus real_one (real_opp real_one)) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_opp real_one real_zero]. ring.
Qed.

Lemma d09_cIm_plus_opp : forall z : Cx,
  real_eq (cIm (c_plus c_one (c_opp z))) (real_opp (cIm z)).
Proof.
  intros [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_opp real_zero real_one c_one
       c_plus c_opp cRe cIm fst snd]. ring.
Qed.

(* The faces that consume this machine cluster are cast in the on-disk
   companion pieces GaC2_09_DenomZeroSet_b.v (the pi carrier, the
   lattice exponential, the logarithm constant, and the power carrier
   with its zero-set faces) and GaC2_09_DenomZeroSet_c.v (the
   rational-layer bounds, the trigonometric deviation face, and the
   pi-window pin). *)
