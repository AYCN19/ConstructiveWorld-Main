(* ConstructiveWorld-Main - the modulus identity and strip bound of the
   complex exponential on the pair carrier. *)

(** * GaC1_16_CExpNorm: the modulus of the complex exponential.

    Mission.  The modulus identity of the complex exponential on the
      pair carrier: [gaC1_16_norm_sq_exp],
      c_norm_sq (c_exp z) == exp(Re z + Re z), the sqrt-free
      squared-norm form of |e^z| = e^{Re z}; and the strip bound
      [gaC1_16_strip]: |Re z| controlled through the exp-value
      hypothesis gives c_norm_sq (c_exp z) <= exp(M)^2 in Bishop
      form.  Honest note: |e^z| <= e^{|z|} is the consumer-side
      corollary of the identity plus the strip bound and is not
      separately named; the strip hypothesis is taken in squared-exp
      form, and the exp-level form needs the Bishop mult-compat craft
      (inverse-margin dance), deferred explicitly.

    Dependencies.  Stdlib [Arith.PeanoNat], [QArith.QArith],
      [QArith.Qring], [Setoid], [Morphisms].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig],
      [CxRealPairCore]/[CxRealPairExpLog],
      [G1_PYTH] (the shared Pythagorean block; C1-16 requires it and
      never names C1-17), [GaC1_14_SeriesCauchy]/
      [GaC1_15_PowSeriesConv] (the Bishop transports of C1-15 are
      used), and [GaC1_RB01_RealLeB] ([real_le_b], the Bishop-form
      order) of this development.

    References.  mathlib [Trigonometric.lean] norm_exp :
      |exp z| = exp z.re; the Real-layer Pythagorean closure
      [real_cos_sq_plus_sin_sq_one] (S10:6496), the anchor that makes
      the G1_PYTH cast a pure consumption.

    Constructivity.  Every named construction is carried by [Set];
      predicates are Set-sorted ([real_eq], [real_lt], [real_le_b],
      [QltT], [Id]); zero classical choice; closed under the global
      context; [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_16_CExpNorm.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_RB01_RealLeB.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import G1_PYTH.
Require Import GaC1_14_SeriesCauchy.
Require Import GaC1_15_PowSeriesConv.

(* ===================================================================== *)
(* Section 2. I1: the modulus identity (squared-norm form).               *)
(* ===================================================================== *)

Section NormIdentity.

(* I1. c_norm_sq (c_exp z) == exp(Re z + Re z): the squared form of      *)
(*     |e^z| = e^{Re z} through the Pythagorean closure.                  *)
Lemma gaC1_16_norm_sq_exp :
  forall z : Cx,
    real_eq (c_norm_sq (c_exp z))
            (cauchy_real_exp (real_plus (cRe z) (cRe z))).
Proof.
  intro z.
  set (E := cauchy_real_exp (cRe z)).
  set (C := cauchy_real_cos (cIm z)).
  set (S := cauchy_real_sin (cIm z)).
  change (real_eq
    (real_plus (real_mult (real_mult E C) (real_mult E C))
               (real_mult (real_mult E S) (real_mult E S)))
    (cauchy_real_exp (real_plus (cRe z) (cRe z)))).
  apply (real_eq_trans _
    (real_mult (real_mult E E) (real_plus (real_mult C C) (real_mult S S)))).
  - (* (EC)(EC) + (ES)(ES) == (EE)(CC + SS): the distributivity lemma *)
    apply (real_eq_sym _ _).
    exact (real_mult_plus_distr_r E E C C S S).
  - apply (real_eq_trans _ (real_mult (real_mult E E) real_one)).
    + (* CC + SS == 1: the shared Pythagorean closure *)
      apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact (real_pyth_cos_sq_sin_sq (cIm z)).
    + apply (real_eq_trans _ (real_mult E E)).
      * apply real_mult_one.
      * apply (real_eq_sym _ _).
        exact (cauchy_real_exp_plus (cRe z) (cRe z)).
Qed.

End NormIdentity.

(* ===================================================================== *)
(* Section 3. I3: the strip bound (Bishop form).                          *)
(* ===================================================================== *)

Section StripBound.

(* I3. Under the squared strip hypothesis exp(Re z)^2 <=_b exp(M)^2, the *)
(*     squared modulus is <=_b exp(M)^2 (consumption shape; the band     *)
(*     |Re z| <= M materializes as this hypothesis on the consumer side). *)
Lemma gaC1_16_strip :
  forall (z : Cx) (M : Real),
    real_le_b (real_mult (cauchy_real_exp (cRe z)) (cauchy_real_exp (cRe z)))
              (real_mult (cauchy_real_exp M) (cauchy_real_exp M)) ->
    real_le_b (c_norm_sq (c_exp z))
              (real_mult (cauchy_real_exp M) (cauchy_real_exp M)).
Proof.
  intros z M Hup.
  apply (gaC1_15_le_b_eq_l _ _ _ (gaC1_16_norm_sq_exp z)).
  apply (gaC1_15_le_b_eq_l _ _ _
    (cauchy_real_exp_plus (cRe z) (cRe z))).
  exact Hup.
Qed.

End StripBound.
