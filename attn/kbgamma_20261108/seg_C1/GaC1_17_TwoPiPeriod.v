(* ConstructiveWorld-Main - the 2*pi periodicity of the constructive sine
   and cosine through the pi/2 anchors and the addition formulas. *)

(** * GaC1_17_TwoPiPeriod: the two-pi periodicity of sin and cos.

    Mission.  The 2*pi periodicity of the constructive sine and cosine:
      sin(pi/2) = 1 ([G1_PYTH] sign fixing) and cos(pi/2) = 0 as the
      pi/2 anchors, pi := pi/2 + pi/2 as [pi_R] and
      two_pi_R := pi + pi as [two_pi_R], the constant identities
      [gaC1_17_sin_pi] (sin pi = 0), [gaC1_17_cos_pi] (cos pi = -1),
      [gaC1_17_sin_two_pi] (sin 2pi = 0), [gaC1_17_cos_two_pi]
      (cos 2pi = 1), and the periodicity laws [gaC1_17_sin_period]/
      [gaC1_17_cos_period].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [Setoid],
      [Morphisms].  Requires [S02_CauchyComplete],
      [S07_RealSetoidExpLog] (RealSetoid compat),
      [S10_KVQuantTrig] ([cauchy_real_sin]/[cauchy_real_cos],
      [cos_pi_half], [real_cos_pi_half_zero], [real_pi_geom],
      [rs_add_sin]/[rs_add_cos]), [CxRealPairExpLog], and [G1_PYTH]
      (the shared block; C1-17 requires it and never names C1-16) of
      this development.

    References.  mathlib [Trigonometric.lean] exp_mul_I (polar form
      confirmation); the periodicity lemma body has no in-tree
      precedent, and mathlib's periodicity file was not located in the
      reference fetches (recorded fail-honest).  [two_pi_R] is cast as
      the pi/2 four-fold sum; its equality with 2 * [real_pi_geom] is
      the named bridge [gaC1_17_two_pi_eq_geom] (consumers transport
      through sine/cosine congruence as needed).

    Constructivity.  Every named construction is carried by [Set];
      predicates are Set-sorted ([real_eq], [real_lt], [QltT], [Id]);
      zero classical choice; closed under the global context;
      [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_17_TwoPiPeriod.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairExpLog.
Require Import G1_PYTH.

(* ===================================================================== *)
(* Section 1. Carriers and constant identities.                           *)
(* ===================================================================== *)

Section Carriers17.

Definition pi_R : Real := real_plus cos_pi_half cos_pi_half.
Definition two_pi_R : Real := real_plus pi_R pi_R.

(* two_pi_R == 2 * real_pi_geom. *)
Lemma gaC1_17_two_pi_eq_geom :
  real_eq two_pi_R (real_mult (real_const 2) real_pi_geom).
Proof.
  unfold two_pi_R, pi_R, real_pi_geom.
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_const projT1 cos_pi_half].
  ring.
Qed.

(* x + 0 == x. *)
Lemma g17_plus_zero_r : forall x : Real, real_eq (real_plus x real_zero) x.
Proof.
  intro x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_zero projT1].
  ring.
Qed.

(* x + (-0) == x. *)
Lemma g17_plus_opp_zero_r : forall x : Real,
  real_eq (real_plus x (real_opp real_zero)) x.
Proof.
  intro x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_opp real_zero projT1].
  ring.
Qed.

(* 0 * x == 0. *)
Lemma g17_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_mult real_zero projT1].
  ring.
Qed.

(* Constant identities. *)
Lemma g17_c1 : real_eq (real_plus (real_mult real_one real_zero)
                                  (real_mult real_zero real_one)) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_one real_zero projT1]. ring.
Qed.

Lemma g17_c2 : real_eq (real_plus (real_mult real_zero real_zero)
                                  (real_opp (real_mult real_one real_one)))
                       (real_opp real_one).
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_opp real_one real_zero projT1]. ring.
Qed.

Lemma g17_c3 : real_eq (real_plus (real_mult real_zero (real_opp real_one))
                                  (real_mult (real_opp real_one) real_zero))
                       real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_opp real_one real_zero projT1]. ring.
Qed.

Lemma g17_c4 : real_eq (real_plus (real_mult (real_opp real_one) (real_opp real_one))
                                  (real_opp (real_mult real_zero real_zero)))
                       real_one.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_opp real_one real_zero projT1]. ring.
Qed.

End Carriers17.

(* ===================================================================== *)
(* Section 2. The periodicity chain.                                      *)
(* ===================================================================== *)

Section PeriodChain.

Local Notation c := cos_pi_half.

(* sin pi == 0. *)
Lemma gaC1_17_sin_pi : real_eq (cauchy_real_sin pi_R) real_zero.
Proof.
  unfold pi_R.
  apply (real_eq_trans _ _ _ (rs_add_sin c c)).
  apply (real_eq_trans _ (real_plus (real_mult real_one real_zero)
                                    (real_mult real_zero real_one))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * exact real_sin_pi_half_one.
      * exact real_cos_pi_half_zero.
    + apply RealSetoid.real_eq_mult_compat.
      * exact real_cos_pi_half_zero.
      * exact real_sin_pi_half_one.
  - exact g17_c1.
Qed.

(* cos pi == -1. *)
Lemma gaC1_17_cos_pi : real_eq (cauchy_real_cos pi_R) (real_opp real_one).
Proof.
  unfold pi_R.
  apply (real_eq_trans _ _ _ (rs_add_cos c c)).
  apply (real_eq_trans _ (real_plus (real_mult real_zero real_zero)
                                    (real_opp (real_mult real_one real_one)))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * exact real_cos_pi_half_zero.
      * exact real_cos_pi_half_zero.
    + apply RealSetoid.real_eq_opp_compat.
      apply RealSetoid.real_eq_mult_compat.
      * exact real_sin_pi_half_one.
      * exact real_sin_pi_half_one.
  - exact g17_c2.
Qed.

(* sin 2pi == 0. *)
Lemma gaC1_17_sin_two_pi : real_eq (cauchy_real_sin two_pi_R) real_zero.
Proof.
  unfold two_pi_R.
  apply (real_eq_trans _ _ _ (rs_add_sin pi_R pi_R)).
  apply (real_eq_trans _ (real_plus (real_mult real_zero (real_opp real_one))
                                    (real_mult (real_opp real_one) real_zero))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * exact gaC1_17_sin_pi.
      * exact gaC1_17_cos_pi.
    + apply RealSetoid.real_eq_mult_compat.
      * exact gaC1_17_cos_pi.
      * exact gaC1_17_sin_pi.
  - exact g17_c3.
Qed.

(* cos 2pi == 1. *)
Lemma gaC1_17_cos_two_pi : real_eq (cauchy_real_cos two_pi_R) real_one.
Proof.
  unfold two_pi_R.
  apply (real_eq_trans _ _ _ (rs_add_cos pi_R pi_R)).
  apply (real_eq_trans _ (real_plus (real_mult (real_opp real_one) (real_opp real_one))
                                    (real_opp (real_mult real_zero real_zero)))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * exact gaC1_17_cos_pi.
      * exact gaC1_17_cos_pi.
    + apply RealSetoid.real_eq_opp_compat.
      apply RealSetoid.real_eq_mult_compat.
      * exact gaC1_17_sin_pi.
      * exact gaC1_17_sin_pi.
  - exact g17_c4.
Qed.

(* J1. sin(theta + 2pi) == sin theta. *)
Lemma gaC1_17_sin_period : forall th : Real,
  real_eq (cauchy_real_sin (real_plus th two_pi_R)) (cauchy_real_sin th).
Proof.
  intro th.
  apply (real_eq_trans _ _ _ (rs_add_sin th two_pi_R)).
  apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_sin th) real_one)
                                    (real_mult (cauchy_real_cos th) real_zero))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact gaC1_17_cos_two_pi.
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact gaC1_17_sin_two_pi.
  - apply (real_eq_trans _ (real_plus (cauchy_real_sin th) real_zero)).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_mult_one.
      * apply real_mult_zero.
    + apply g17_plus_zero_r.
Qed.

(* J2. cos(theta + 2pi) == cos theta. *)
Lemma gaC1_17_cos_period : forall th : Real,
  real_eq (cauchy_real_cos (real_plus th two_pi_R)) (cauchy_real_cos th).
Proof.
  intro th.
  apply (real_eq_trans _ _ _ (rs_add_cos th two_pi_R)).
  apply (real_eq_trans _ (real_plus (real_mult (cauchy_real_cos th) real_one)
                                    (real_opp (real_mult (cauchy_real_sin th) real_zero)))).
  - apply RealSetoid.real_eq_plus_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact gaC1_17_cos_two_pi.
    + apply RealSetoid.real_eq_opp_compat.
      apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact gaC1_17_sin_two_pi.
  - apply (real_eq_trans _ (real_plus (cauchy_real_cos th) (real_opp real_zero))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply real_mult_one.
      * apply RealSetoid.real_eq_opp_compat. apply real_mult_zero.
    + apply g17_plus_opp_zero_r.
Qed.

End PeriodChain.
