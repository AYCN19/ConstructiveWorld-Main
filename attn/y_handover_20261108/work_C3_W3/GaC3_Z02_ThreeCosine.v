(* ===================================================================== *)
(* GaC3_Z02_ThreeCosine.v                                                 *)
(*                                                                       *)
(* Mission: the three-cosine inequality face (node C3-Z02, segment C3    *)
(*   wave W1).  The double-angle identity cos 2u = 2 cos^2 u - 1, the    *)
(*   algebraic identity 3 + 4 cos u + cos 2u = 2 (1 + cos u)^2, and the  *)
(*   nonnegativity face of that expression.  Consumed by the            *)
(*   nonvanishing chain (C3-Z03 speedometer) through the nonnegativity  *)
(*   face only.                                                         *)
(* Dependencies: S01_BaseRing (NatLe face), S02_CauchyComplete (Real     *)
(*   carrier, order), S07_RealSetoidExpLog (real_ge_relax, RealSetoid   *)
(*   compat), S10_KVQuantTrig (cauchy_real_cos/sin, rs_add_cos, born    *)
(*   Pythagorean closure real_cos_sq_plus_sin_sq_one).                  *)
(* References: AFP PNT_with_Remainder Zeta_Zerofree cos_inequality_1     *)
(*   (:9-23, verbatim statement precedent 3 + 4 cos x + cos 2x >= 0,     *)
(*   route cos_double -> square -> nonneg); cards_C3-Z02; drafts_C3 Z02  *)
(*   study card (the equality-determining face is dropped: it requires   *)
(*   2pi periodicity, a C1.4 residue - only the inequality face is cast).*)
(* Constructivity: Set-carried statements.  The nonnegativity face is    *)
(*   carried by real_ge_relax (S07:3598, the tree-native asymptotic      *)
(*   order): an Or-form real_le real_zero (square) would decide          *)
(*   equality-versus-positivity of a general real and is not             *)
(*   constructively provable; the relaxed face is reached from the exact *)
(*   pointwise nonnegativity of rational squares.  Zero Axiom, zero      *)
(*   Parameter, zero classical choice.                                   *)
(* Build: coqc -native-compiler no -q (sandbox -Q path), cpu_guard v3.   *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround QArith.Qring.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.

(* ===================================================================== *)
(* Section 1. Atomic algebra anchors.                                     *)
(* ===================================================================== *)

(* x + (-x) == 0 at the Real layer. *)
Lemma GaC3_Z02_plus_opp_r : forall x : Real,
  real_eq (real_plus x (real_opp x)) real_zero.
Proof.
  intro x. apply real_eq_of_zero_diff. intro n.
  rewrite (real_plus_proj x (real_opp x) n).
  rewrite (real_opp_proj x n).
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hz.
  ring.
Qed.

(* real_eq is compatible with real_opp. *)
Lemma GaC3_Z02_eq_opp_compat : forall a b : Real,
  real_eq a b -> real_eq (real_opp a) (real_opp b).
Proof.
  intros a b Hab eps Heps.
  destruct (Hab eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  apply (qltT_eq_compat_l (Qabs (projT1 a n - projT1 b n))
                          (Qabs (projT1 (real_opp a) n - projT1 (real_opp b) n)) eps).
  - assert (Hr2 : Qabs (projT1 (real_opp a) n - projT1 (real_opp b) n)
                  == Qabs (projT1 a n - projT1 b n)).
    { rewrite <- (Qabs_opp (projT1 a n - projT1 b n)).
      apply Qabs_wd.
      assert (Hr : (projT1 (real_opp a) n - projT1 (real_opp b) n)%Q
                   == (- (projT1 a n - projT1 b n))%Q).
      { rewrite (real_opp_proj a n). rewrite (real_opp_proj b n). ring. }
      exact Hr. }
    exact (Qeq_sym _ _ Hr2).
  - exact HN.
Qed.

(* ===================================================================== *)
(* Section 2. Transfer: real_eq moves the relaxed nonnegativity face.     *)
(* ===================================================================== *)

Lemma GaC3_Z02_eq_relax_transfer : forall a b : Real,
  real_eq a b -> real_ge_relax b real_zero -> real_ge_relax a real_zero.
Proof.
  intros a b Hab Hb. unfold real_ge_relax in *. intros eps Heps.
  assert (Hh : QltT 0 (eps / 2)).
  { apply Qlt_to_QltT. apply (Qlt_shift_div_l 0 eps 2).
    - change (Qlt 0 2). compute. reflexivity.
    - simpl. apply QltT_to_Qlt. exact Heps. }
  specialize (Hb (eps / 2) Hh). destruct Hb as [N2 HN2].
  specialize (Hab (eps / 2) Hh). destruct Hab as [N1 HN1].
  exists (Nat.max N1 N2). intros n Hn.
  assert (HN1n : QltT (Qabs (projT1 a n - projT1 b n)) (eps / 2)).
  { apply HN1. apply NatLe_lift. apply (Nat.le_trans _ (Nat.max N1 N2) _);
      [apply Nat.le_max_l | exact Hn]. }
  assert (HN2n : QltT (projT1 real_zero n - projT1 b n) (eps / 2)).
  { apply HN2. apply (Nat.le_trans _ (Nat.max N1 N2) _);
      [apply Nat.le_max_r | exact Hn]. }
  apply Qlt_to_QltT.
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  assert (Hsum : (0 - projT1 a n)%Q
                 == ((projT1 real_zero n - projT1 b n)
                     + (projT1 b n - projT1 a n))%Q).
  { rewrite Hz. ring. }
  rewrite Hsum.
  apply (Qlt_le_trans _ (eps / 2 + eps / 2)%Q _).
  - apply Qplus_lt_compat.
    + apply QltT_to_Qlt. exact HN2n.
    + apply (Qle_lt_trans _ (Qabs (projT1 b n - projT1 a n)) _).
      * apply Qle_Qabs.
      * rewrite (Qabs_Qminus (projT1 b n) (projT1 a n)).
        exact (QltT_to_Qlt _ _ HN1n).
  - assert (Hf : (eps / 2 + eps / 2)%Q == eps) by field.
    rewrite Hf. apply Qle_refl.
Qed.

(* ===================================================================== *)
(* Section 3. The double-angle identity.                                  *)
(* ===================================================================== *)

Lemma GaC3_Z02_cos_double : forall u : Real,
  real_eq (cauchy_real_cos (real_plus u u))
          (real_plus (real_mult (real_const 2)
                                 (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))
                     (real_opp real_one)).
Proof.
  intro u.
  (* Hsin : sin^2 u == 1 + (-cos^2 u), from the born Pythagorean closure.
     Both faces meet at the pointwise level:
     |S_n - (1 - C_n)| == |(C_n + S_n) - 1| < eps. *)
  assert (Hsin : real_eq (real_mult (cauchy_real_sin u) (cauchy_real_sin u))
                         (real_plus real_one
                            (real_opp (real_mult (cauchy_real_cos u)
                                                 (cauchy_real_cos u))))).
  { intros eps Heps.
    destruct (real_cos_sq_plus_sin_sq_one u eps Heps) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    apply (qltT_eq_compat_l (Qabs (projT1 (real_plus (real_mult (cauchy_real_cos u) (cauchy_real_cos u)) (real_mult (cauchy_real_sin u) (cauchy_real_sin u))) n - projT1 real_one n))
                            (Qabs (projT1 (real_mult (cauchy_real_sin u) (cauchy_real_sin u)) n - projT1 (real_plus real_one (real_opp (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))) n)) eps).
    - apply Qabs_wd.
      assert (Hring : (projT1 (real_plus (real_mult (cauchy_real_cos u) (cauchy_real_cos u)) (real_mult (cauchy_real_sin u) (cauchy_real_sin u))) n
                       - projT1 real_one n)%Q
                      == (projT1 (real_mult (cauchy_real_sin u) (cauchy_real_sin u)) n
                          - projT1 (real_plus real_one (real_opp (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))) n)%Q).
      { rewrite (real_plus_proj (real_mult (cauchy_real_cos u) (cauchy_real_cos u))
                                (real_mult (cauchy_real_sin u) (cauchy_real_sin u)) n).
        rewrite (real_plus_proj real_one
                   (real_opp (real_mult (cauchy_real_cos u) (cauchy_real_cos u))) n).
        rewrite (real_opp_proj (real_mult (cauchy_real_cos u) (cauchy_real_cos u)) n).
        ring. }
      exact Hring.
    - exact HN. }
  (* cos(u+u) == cos^2 + (-sin^2) == cos^2 + -(1 + -cos^2) == 2 cos^2 + -1 *)
  apply (real_eq_trans _
          (real_plus (real_mult (cauchy_real_cos u) (cauchy_real_cos u))
                     (real_opp (real_mult (cauchy_real_sin u) (cauchy_real_sin u))))).
  - exact (rs_add_cos u u).
  - apply (real_eq_trans _
            (real_plus (real_mult (cauchy_real_cos u) (cauchy_real_cos u))
                       (real_opp (real_plus real_one
                          (real_opp (real_mult (cauchy_real_cos u)
                                               (cauchy_real_cos u))))))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * apply GaC3_Z02_eq_opp_compat. exact Hsin.
    + apply real_eq_of_zero_diff. intro n.
      rewrite (real_plus_proj (real_mult (cauchy_real_cos u) (cauchy_real_cos u))
                              (real_opp (real_plus real_one (real_opp (real_mult (cauchy_real_cos u) (cauchy_real_cos u))))) n).
      rewrite (real_opp_proj (real_plus real_one (real_opp (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))) n).
      rewrite (real_plus_proj real_one (real_opp (real_mult (cauchy_real_cos u) (cauchy_real_cos u))) n).
      rewrite (real_opp_proj (real_mult (cauchy_real_cos u) (cauchy_real_cos u)) n).
      rewrite (real_plus_proj
                (real_mult (real_const 2) (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))
                (real_opp real_one) n).
      rewrite (real_mult_proj (real_const 2) (real_mult (cauchy_real_cos u) (cauchy_real_cos u)) n).
      rewrite (real_const_proj 2 n).
      rewrite (real_opp_proj real_one n).
      assert (H1 : projT1 real_one n == 1) by reflexivity.
      rewrite H1.
      ring.
Qed.

(* ===================================================================== *)
(* Section 4. The three-cosine identity and nonnegativity face.           *)
(* ===================================================================== *)

Lemma GaC3_Z02_three_cosine_sq : forall u : Real,
  real_eq (real_plus (real_const 3)
                     (real_plus (real_mult (real_const 4) (cauchy_real_cos u))
                                (cauchy_real_cos (real_plus u u))))
          (real_mult (real_const 2)
                     (real_mult (real_plus real_one (cauchy_real_cos u))
                                (real_plus real_one (cauchy_real_cos u)))).
Proof.
  intro u.
  apply (real_eq_trans _
          (real_plus (real_const 3)
                     (real_plus (real_mult (real_const 4) (cauchy_real_cos u))
                                (real_plus (real_mult (real_const 2)
                                            (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))
                                           (real_opp real_one))))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_eq_refl.
      * exact (GaC3_Z02_cos_double u).
  - apply real_eq_of_zero_diff. intro n.
    rewrite (real_plus_proj (real_const 3)
               (real_plus (real_mult (real_const 4) (cauchy_real_cos u))
                          (real_plus (real_mult (real_const 2)
                                     (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))
                                    (real_opp real_one))) n).
    rewrite (real_plus_proj (real_mult (real_const 4) (cauchy_real_cos u))
               (real_plus (real_mult (real_const 2)
                          (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))
                         (real_opp real_one)) n).
    rewrite (real_plus_proj (real_mult (real_const 2)
                               (real_mult (cauchy_real_cos u) (cauchy_real_cos u)))
                            (real_opp real_one) n).
    rewrite (real_mult_proj (real_const 4) (cauchy_real_cos u) n).
    rewrite (real_const_proj 3 n).
    rewrite (real_const_proj 4 n).
    rewrite (real_mult_proj (real_const 2)
               (real_mult (cauchy_real_cos u) (cauchy_real_cos u)) n).
    rewrite (real_const_proj 2 n).
    rewrite (real_mult_proj (cauchy_real_cos u) (cauchy_real_cos u) n).
    rewrite (real_opp_proj real_one n).
    rewrite (real_mult_proj (real_const 2)
               (real_mult (real_plus real_one (cauchy_real_cos u))
                          (real_plus real_one (cauchy_real_cos u))) n).
    rewrite (real_const_proj 2 n).
    rewrite (real_mult_proj (real_plus real_one (cauchy_real_cos u))
               (real_plus real_one (cauchy_real_cos u)) n).
    rewrite (real_plus_proj real_one (cauchy_real_cos u) n).
    assert (H1 : projT1 real_one n == 1) by reflexivity.
    rewrite H1.
    ring.
Qed.

(* Pointwise nonnegativity of the squared form: 0 <= 2 (1+c)^2 in Q.
   Route: the sign case on (1+c); the negative face transports the square
   onto the absolute value via Qabs_neg, and both faces close with the
   stdlib product-positivity lemma Qmult_le_0_compat. *)
Lemma GaC3_Z02_sq_pointwise_nonneg : forall u : Real,
  (forall n : nat,
    Qle (projT1 real_zero n)
        (projT1 (real_mult (real_const 2)
                  (real_mult (real_plus real_one (cauchy_real_cos u))
                             (real_plus real_one (cauchy_real_cos u)))) n)).
Proof.
  intro u. intro n.
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hz.
  assert (Hpt : projT1 (real_mult (real_const 2)
                  (real_mult (real_plus real_one (cauchy_real_cos u))
                             (real_plus real_one (cauchy_real_cos u)))) n
             == ((2 * (1 + projT1 (cauchy_real_cos u) n))
                 * (1 + projT1 (cauchy_real_cos u) n))%Q).
  { rewrite (real_mult_proj (real_const 2)
               (real_mult (real_plus real_one (cauchy_real_cos u))
                          (real_plus real_one (cauchy_real_cos u))) n).
    rewrite (real_const_proj 2 n).
    rewrite (real_mult_proj (real_plus real_one (cauchy_real_cos u))
               (real_plus real_one (cauchy_real_cos u)) n).
    rewrite (real_plus_proj real_one (cauchy_real_cos u) n).
    assert (H1 : projT1 real_one n == 1) by reflexivity.
    rewrite H1.
    ring. }
  rewrite Hpt.
  assert (Hr2 : ((2 * (1 + projT1 (cauchy_real_cos u) n))
                 * (1 + projT1 (cauchy_real_cos u) n))%Q
                == (2 * ((1 + projT1 (cauchy_real_cos u) n)
                         * (1 + projT1 (cauchy_real_cos u) n)))%Q) by ring.
  rewrite Hr2.
  assert (Hcore : Qle 0 ((1 + projT1 (cauchy_real_cos u) n)
                         * (1 + projT1 (cauchy_real_cos u) n))).
  { destruct (Q_dec (1 + projT1 (cauchy_real_cos u) n) 0) as [Hc1 | Heq].
    destruct Hc1 as [Hlt | Hgt].
    - assert (Habs : Qabs (1 + projT1 (cauchy_real_cos u) n)
                     == Qopp (1 + projT1 (cauchy_real_cos u) n))
        by (apply Qabs_neg; apply Qlt_le_weak; exact Hlt).
      assert (Hr : (1 + projT1 (cauchy_real_cos u) n)
                   * (1 + projT1 (cauchy_real_cos u) n)
                   == Qabs (1 + projT1 (cauchy_real_cos u) n)
                      * Qabs (1 + projT1 (cauchy_real_cos u) n))
        by (rewrite Habs; ring).
      rewrite Hr.
      apply Qmult_le_0_compat; apply Qabs_nonneg.
    - assert (HXle : Qle 0 (1 + projT1 (cauchy_real_cos u) n))
        by (apply Qlt_le_weak; exact Hgt).
      apply Qmult_le_0_compat; exact HXle.
    - rewrite Heq. apply qeq_le. ring. }
  assert (H02 : Qle 0 2) by (apply Qlt_le_weak; reflexivity).
  apply Qmult_le_0_compat; [exact H02 | exact Hcore].
Qed.

(* Main face: 3 + 4 cos u + cos 2u >=relax 0 (relaxed asymptotic order,
   the tree-native carrier for the AFP cos_inequality_1 face). *)
Theorem GaC3_Z02_three_cosine_nonneg_relax : forall u : Real,
  real_ge_relax
    (real_plus (real_const 3)
               (real_plus (real_mult (real_const 4) (cauchy_real_cos u))
                          (cauchy_real_cos (real_plus u u))))
    real_zero.
Proof.
  intro u.
  apply (GaC3_Z02_eq_relax_transfer _ _ (GaC3_Z02_three_cosine_sq u)).
  apply (real_ge_relax_of_pointwise _ _ 0).
  intro n. intro Hn0.
  exact (GaC3_Z02_sq_pointwise_nonneg u n).
Qed.
