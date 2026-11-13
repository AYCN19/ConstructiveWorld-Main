(* ConstructiveWorld-Main - auxiliary faces of the C2-17 strip assembly. *)
(** * GaC2_17_StripVerticalAsm_a: auxiliary faces of node C2-17.

    Mission.  Auxiliary faces for the residence theorems of the C2-17
      strip assembly: the unit-modulus face of the n = 1 eta column
      term, the eta modulus cap read off the carrier's own eta slot,
      the inverse-order face reading the squared corridor inverse off
      a denominator lower bound, the quotient norm assembly, the
      target normalization, and the final monotone chain.

    Dependencies.  Stdlib [QArith.QArith]; [S01_BaseRing] (qualified [NatLe]), [S02_CauchyComplete],
      [S03_QExp] ([real_inv_pos], [real_inv_pos_correct],
      [real_inv_pos_pos]), [S07_RealSetoidExpLog]
      ([real_le_mult_compat_weak], [real_mult_positive],
      [real_eq_le]), [CxRealPairCore], [CxRealPairExpLog],
      [GaC2_01_DirichletPartialSum] ([c_powq], [c_exp_wd]),
      [GaC2_02_AbsConvTailBound_a] ([real_log_wd], [nat_real_one]),
      [GaC2_10_EtaContinuation] ([d10_eta_conv], [eta_s],
      [d10_eta_part]), [GaC2_16_ZetaVerticalBound].

    References.  drafts_C2.md C2.17 (obligation L24 and the card (a)
      chain); cards_C2.md C2.17.

    Constructivity.  Every statement Set-sorted; the proofs close by
      forward monotone chains, pointwise rational identities and the
      born inverse carriers; zero assumed constants, zero abandoned
      proofs, zero classical principles.

    Build.  [coqc -native-compiler no -q -Q . ""
      GaC2_17_StripVerticalAsm_a.v]; consumed by the mother node. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_10_EtaContinuation.
Require Import GaC2_16_ZetaVerticalBound.
From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* 1 < 2 on the embedded rational line, the factor-two step face. *)
Lemma c17_one_lt_two : real_lt real_one (real_const (2#1)).
Proof.
  exists (1#2)%Q. split.
  - unfold QltT, Qlt_bool. reflexivity.
  - exists 0%nat. intro n. reflexivity.
Qed.

(* The n = 1 eta column term carries unit modulus: 1^{-s} = 1, since     *)
(* ln 1 = 0 on the born log and exp 0 = 1.                              *)
Lemma c17_powq_one :
  forall (Hnpos : forall n : nat,
            S01_BaseRing.NatLe 1%nat n -> real_lt real_zero (nat_real n))
         (s : Cx),
    real_eq (c_norm_sq (c_powq Hnpos 1%nat (NatLe_one_S 0) s)) real_one.
Proof.
  intros Hnpos s.
  assert (Hm0 : c_eq (c_mult s (c_of_real
                   (real_log (nat_real 1%nat)
                      (Hnpos 1%nat (NatLe_one_S 0)))))
                 c_zero).
  { apply (c_eq_trans _ (c_mult s c_zero)).
    - apply c_mult_congr.
      + apply c_eq_refl.
      + apply GaC2_02_AbsConvTailBound_a.c_of_real_wd.
        apply (real_eq_trans _ (real_log real_one real_lt_zero_one)).
        * apply GaC2_02_AbsConvTailBound_a.real_log_wd. apply nat_real_one.
        * exact (real_log_one real_lt_zero_one).
    - apply (c_eq_trans _ (c_mult c_zero s)).
      + apply c_mult_comm.
      + apply c_mult_zero. }
  apply (real_eq_trans _ (c_norm_sq c_one)).
  - apply c_norm_sq_wd.
    apply (c_eq_trans _ (c_exp c_zero)).
    + apply c_exp_wd.
      apply (c_eq_trans _ (c_scale (real_opp real_one) c_zero)).
      * apply c_scale_wd. exact Hm0.
      * cbn [c_scale c_zero c_eq cRe cIm fst snd].
        split; apply real_mult_zero.
    + exact c_exp_zero.
  - unfold c_norm_sq, c_one, cRe, cIm. cbn [fst snd].
    apply real_eq_of_zero_diff. intro n.
    rewrite (real_plus_proj (real_mult real_one real_one)
               (real_mult real_zero real_zero) n).
    rewrite (real_mult_proj real_one real_one n).
    rewrite (real_mult_proj real_zero real_zero n).
    rewrite (real_one_pt n). rewrite (real_zero_pt n).
    ring.
Qed.


(* The eta modulus cap: the carrier's own eta slot pins |eta|^2 below 2  *)
(* through its N = 0 face (1^{-s} = 1 by the born log-exp unit faces).  *)
Lemma c17_eta_cap : forall (s : Cx) (Heta : d10_eta_conv s),
  real_le (c_norm_sq (eta_s s Heta)) (real_const (2#1)).
Proof.
  intros s Heta.
  destruct Heta as [v Hew].
  assert (Hop0 : c_eq (c_opp c_zero) c_zero).
  { unfold c_opp, c_zero, c_eq, cRe, cIm. cbn [fst snd].
    split; apply real_eq_of_zero_diff; intro n; reflexivity. }
  assert (Hev : c_eq (c_plus v (c_opp (d10_eta_part 0%nat s))) v).
  { apply (c_eq_trans _ (c_plus v (c_opp c_zero))).
    - apply c_plus_congr;
        [apply c_eq_refl | apply c_opp_congr, d10_eta_part_zero].
    - apply (c_eq_trans _ (c_plus (c_opp c_zero) v)).
      + apply c_plus_comm.
      + apply (c_eq_trans _ (c_plus c_zero v)).
        * apply c_plus_congr; [exact Hop0 | apply c_eq_refl].
        * apply c_plus_zero. }
  assert (Hstep : real_lt (c_norm_sq v)
                    (real_mult (real_const (2#1)) (c_norm_sq (c_powq d10_npos
                                   1%nat (NatLe_one_S 0) s)))).
  { exact (real_eq_lt_lt (c_norm_sq v)
             (c_norm_sq (c_plus v (c_opp (d10_eta_part 0%nat s))))
             (real_mult (real_const (2#1))
                (c_norm_sq (c_powq d10_npos 1%nat (NatLe_one_S 0) s)))
             (real_eq_sym _ _ (c_norm_sq_wd _ _ Hev)) (Hew 0%nat)). }
  apply (real_lt_le_iff _ _ (inl
           (real_lt_eq_lt (c_norm_sq v)
              (real_mult (real_const (2#1))
                 (c_norm_sq (c_powq d10_npos 1%nat (NatLe_one_S 0) s)))
              (real_const (2#1)) Hstep
              (real_eq_trans (real_mult (real_const (2#1))
                                  (c_norm_sq (c_powq d10_npos 1%nat
                                       (NatLe_one_S 0) s)))
                 (real_mult (real_const (2#1)) real_one)
                 (real_const (2#1))
                 (RealSetoid.real_eq_mult_compat (real_const (2#1))
                    (c_norm_sq (c_powq d10_npos 1%nat (NatLe_one_S 0) s))
                    (real_const (2#1)) real_one
                    (real_eq_refl (real_const (2#1))) (c17_powq_one d10_npos s))
                 (real_mult_one (real_const (2#1))))))).
Qed.

(* Inverse-order face: if the squared corridor ww sits below x, both     *)
(* positive, then the witness inverse of x is bounded by the squared     *)
(* witness inverse of w.  Route: ww * B^2 = (w B)(w B) = 1 by the born   *)
(* inverse correctness, then a forward monotone chain through the        *)
(* positive multiplier B^2.                                             *)
Lemma c17_inv_le_sq : forall (x w : Real)
  (Hx : real_lt real_zero x) (Hw : real_lt real_zero w)
  (Hww : real_lt real_zero (real_mult w w)),
  real_le (real_mult w w) x ->
  real_le (real_inv_pos x Hx)
          (real_mult (real_inv_pos w Hw) (real_inv_pos w Hw)).
Proof.
  intros x w Hx Hw Hww Hle.
  assert (Hiw : real_lt real_zero (real_inv_pos w Hw))
    by exact (real_inv_pos_pos w Hw).
  assert (Hix : real_lt real_zero (real_inv_pos x Hx))
    by exact (real_inv_pos_pos x Hx).
  assert (HB0 : real_le real_zero
                 (real_mult (real_inv_pos w Hw) (real_inv_pos w Hw)))
    by exact (real_lt_le_iff _ _ (inl (real_mult_positive _ _ Hiw Hiw))).
  assert (Hstep1 : real_le (real_mult (real_mult w w) (real_inv_pos x Hx))
                    real_one).
  { apply (real_le_trans _ (real_mult x (real_inv_pos x Hx))).
    - apply real_le_mult_compat_weak.
      + apply (real_lt_le_iff _ _ (inl Hix)).
      + exact Hle.
    - apply (RealSetoid.real_eq_le _ _ (real_inv_pos_correct x Hx)). }
  assert (Hone : real_eq (real_mult (real_mult w w)
                              (real_mult (real_inv_pos w Hw)
                                         (real_inv_pos w Hw)))
                  real_one).
  { apply (real_eq_trans _
             (real_mult (real_mult w (real_inv_pos w Hw))
                        (real_mult w (real_inv_pos w Hw)))).
    - apply (real_eq_trans _
               (real_mult w (real_mult w
                  (real_mult (real_inv_pos w Hw) (real_inv_pos w Hw))))).
      + apply real_eq_sym. apply real_mult_assoc.
      + apply (real_eq_trans _
                 (real_mult w (real_mult (real_inv_pos w Hw)
                            (real_mult w (real_inv_pos w Hw))))).
        * apply RealSetoid.real_eq_mult_compat.
          -- apply real_eq_refl.
          -- apply (real_eq_trans _
                       (real_mult (real_mult w (real_inv_pos w Hw))
                                  (real_inv_pos w Hw))).
             ++ apply real_mult_assoc.
             ++ apply real_mult_comm.
        * apply real_mult_assoc.
    - apply (real_eq_trans _ (real_mult real_one real_one)).
      + apply RealSetoid.real_eq_mult_compat;
          apply real_inv_pos_correct.
      + apply real_mult_one. }
  assert (Hmain : real_le (real_inv_pos x Hx)
                    (real_mult (real_inv_pos w Hw)
                               (real_inv_pos w Hw))).
  { apply (real_le_trans _
             (real_mult (real_inv_pos x Hx)
                (real_mult (real_mult w w)
                   (real_mult (real_inv_pos w Hw)
                              (real_inv_pos w Hw))))).
    - apply (RealSetoid.real_eq_le _ _).
      apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) real_one)).
      + apply real_eq_sym. apply real_mult_one.
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact (real_eq_sym _ _ Hone).
    - apply (RealSetoid.real_le_compat _ _ _ _
               (real_eq_sym _ _ (real_mult_assoc (real_inv_pos x Hx)
                                  (real_mult w w)
                                  (real_mult (real_inv_pos w Hw)
                                             (real_inv_pos w Hw))))
               (real_mult_one_l (real_mult (real_inv_pos w Hw)
                                  (real_inv_pos w Hw)))).
      apply real_le_mult_compat_weak.
      + exact HB0.
      + apply (RealSetoid.real_le_compat _ _ _ _
                 (real_mult_comm (real_mult w w) (real_inv_pos x Hx))
                 (real_eq_refl _)).
        exact Hstep1. }
  exact Hmain.
Qed.

(* The quotient norm face: the squared modulus of the scaled quotient   *)
(* collapses to A |v|^2 once u^2 = v^2 D and A D = 1; the whole         *)
(* eta-quotient squared-modulus assembly in one face.                  *)
Lemma c17_norm_leg : forall (A D v : Real) (u : Cx)
  (HAD : real_eq (real_mult A D) real_one)
  (Hu2 : real_eq (c_norm_sq u) (real_mult v D)),
  real_eq (c_norm_sq (c_scale A u)) (real_mult A v).
Proof.
  intros A D v u HAD Hu2.
  apply (real_eq_trans _ (real_mult A (real_mult A (real_mult v D)))).
  - apply (real_eq_trans _ (real_mult A (real_mult A (c_norm_sq u)))).
    + unfold c_scale, c_norm_sq, cRe, cIm. cbn [fst snd].
      apply real_eq_of_zero_diff. intro n.
      repeat (rewrite real_mult_proj || rewrite real_plus_proj). ring.
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- exact Hu2.
  - apply (real_eq_trans _ (real_mult A (real_mult (real_mult A D) v))).
    + apply (RealSetoid.real_eq_mult_compat A (real_mult A (real_mult v D))
               A (real_mult (real_mult A D) v)
               (real_eq_refl A)
               (real_eq_trans (real_mult A (real_mult v D))
                  (real_mult A (real_mult D v))
                  (real_mult (real_mult A D) v)
                  (RealSetoid.real_eq_mult_compat A (real_mult v D) A
                     (real_mult D v) (real_eq_refl A) (real_mult_comm v D))
                  (real_mult_assoc A D v))).
    + apply (real_eq_trans _ (real_mult A v)).
      * apply (RealSetoid.real_eq_mult_compat A (real_mult (real_mult A D) v)
                 A v (real_eq_refl A)
                 (real_eq_trans (real_mult (real_mult A D) v)
                    (real_mult real_one v) v
                    (RealSetoid.real_eq_mult_compat (real_mult A D) v real_one v
                       HAD (real_eq_refl v))
                    (real_mult_one_l v))).
      * apply real_eq_refl.
Qed.

(* Target normalization: (a B) (a B) = a (a (B B)), the squared          *)
(* corridor form of the statement right side.                           *)
Lemma c17_target_eq : forall a b : Real,
  real_eq (real_mult (real_mult a b) (real_mult a b))
          (real_mult a (real_mult a (real_mult b b))).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n.
  repeat (rewrite real_mult_proj || rewrite real_plus_proj). ring.
Qed.

(* The final forward monotone chain: a x <= 2 (2 bb) from x <= 2 and     *)
(* a <= bb with both factors positive; every step is a forward          *)
(* multiplier-monotone step, no cancellation.                           *)
Lemma c17_mono_final : forall (a x bb : Real)
  (Hapos : real_lt real_zero a)
  (Hbpos : real_le real_zero bb)
  (Hle2 : real_le real_zero (real_const (2#1)))
  (H12le : real_le real_one (real_const (2#1)))
  (HA : real_le a bb)
  (Hx2 : real_le x (real_const (2#1))),
  real_le (real_mult a x)
          (real_mult (real_const (2#1))
             (real_mult (real_const (2#1)) bb)).
Proof.
  intros a x bb Hapos Hbpos Hle2 H12le HA Hx2.
  assert (HBB2 : real_le bb (real_mult (real_const (2#1)) bb)).
  { apply (RealSetoid.real_le_compat (real_mult real_one bb) bb
             (real_mult (real_const (2#1)) bb)
             (real_mult (real_const (2#1)) bb)
             (real_mult_one_l bb) (real_eq_refl _)).
    exact (real_le_mult_compat_weak real_one (real_const (2#1)) bb
             Hbpos H12le). }
  apply (real_le_trans _ (real_mult (real_const (2#1)) a)).
  - apply (RealSetoid.real_le_compat (real_mult x a) (real_mult a x)
             (real_mult (real_const (2#1)) a)
             (real_mult (real_const (2#1)) a)
             (real_mult_comm x a) (real_eq_refl _)).
    exact (real_le_mult_compat_weak x (real_const (2#1)) a
             (real_lt_le_iff _ _ (inl Hapos)) Hx2).
  - apply (real_le_trans _ (real_mult (real_const (2#1)) bb)).
    + apply (RealSetoid.real_le_compat (real_mult a (real_const (2#1)))
               (real_mult (real_const (2#1)) a)
               (real_mult bb (real_const (2#1)))
               (real_mult (real_const (2#1)) bb)
               (real_mult_comm a (real_const (2#1)))
               (real_mult_comm bb (real_const (2#1)))).
      exact (real_le_mult_compat_weak a bb (real_const (2#1)) Hle2 HA).
    + apply (RealSetoid.real_le_compat (real_mult bb (real_const (2#1)))
               (real_mult (real_const (2#1)) bb)
               (real_mult (real_mult (real_const (2#1)) bb)
                  (real_const (2#1)))
               (real_mult (real_const (2#1))
                  (real_mult (real_const (2#1)) bb))
               (real_mult_comm bb (real_const (2#1)))
               (real_mult_comm (real_mult (real_const (2#1)) bb)
                  (real_const (2#1)))).
      exact (real_le_mult_compat_weak bb (real_mult (real_const (2#1)) bb)
               (real_const (2#1)) Hle2 HBB2).
Qed.
