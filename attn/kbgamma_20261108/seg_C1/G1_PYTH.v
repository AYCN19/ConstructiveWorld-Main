(* ConstructiveWorld-Main - the shared Real-layer Pythagorean closure
   block consumed by the complex transcendental modules. *)

(** * G1_PYTH: the Real-layer Pythagorean closure and the sine sign at pi/2.

    Mission.  The shared Pythagorean closure block at the Real layer:
      the identity cos^2 + sin^2 == 1 consumed from the S10 Pythagorean
      closure lemma as [real_pyth_cos_sq_sin_sq], the squared sine at
      pi/2 [real_sq_sin_pi_half_one], and the sign fixing
      [real_sin_pi_half_one].  C1-16 and C1-17 each Require this file
      and never name each other.

    Dependencies.  Stdlib [QArith.Qring].  Requires [S02_CauchyComplete]
      (Real carrier, order algebra), [S07_RealSetoidExpLog] (RealSetoid
      compat lemmas), and [S10_KVQuantTrig] (cauchy_real_cos/sin, pi/2
      anchors) of this development.

    References.  This development, [S10_KVQuantTrig], the baseline
      module in ConstructiveWorld-Main whose Real-layer Pythagorean
      closure [real_cos_sq_plus_sin_sq_one] (S10_KVQuantTrig.v:6496)
      and pi/2 anchors [cos_pi_half] (S10:8403),
      [real_cos_pi_half_zero] (S10:8425), [real_sin_pi_half_pos]
      (S10:8906) are carried over here; mirrors the norm_exp route of
      mathlib [Trigonometric].

    Constructivity.  Every named construction is carried by [Set]; all
      predicates are Set-sorted ([real_eq], [real_lt], [QltT]); zero
      classical choice; the development is closed under the global
      context; [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" G1_PYTH.v] compiles cleanly (exit 0), wrapped by
      [cpu_guard v3]. *)

From Stdlib Require Import QArith.Qring.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.

(* ===================================================================== *)
(* Section 1. Carrier helpers (zero-addition at the Real layer).          *)
(* ===================================================================== *)

Section PythHelpers.

(* 0 + x == x, pointwise by the canonical zero-difference idiom. *)
Lemma g1_plus_zero_l : forall x : Real,
  real_eq (real_plus real_zero x) x.
Proof.
  intro x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus projT1 real_zero].
  ring.
Qed.

End PythHelpers.

(* ===================================================================== *)
(* Section 2. The Pythagorean identity (shared consumption point).        *)
(* ===================================================================== *)

Section Pythagoras.

(* P1. cos^2 X + sin^2 X == 1: the Real-layer Pythagorean closure,        *)
(*     re-stated here as the single shared consumption point of the       *)
(*     S10 block for the whole C1 segment.                                *)
Lemma real_pyth_cos_sq_sin_sq : forall X : Real,
  real_eq (real_plus (real_mult (cauchy_real_cos X) (cauchy_real_cos X))
                     (real_mult (cauchy_real_sin X) (cauchy_real_sin X)))
          real_one.
Proof.
  intro X. exact (real_cos_sq_plus_sin_sq_one X).
Qed.

(* P2. sin(pi/2)^2 == 1: P1 at X := cos_pi_half with cos(pi/2) == 0.      *)
Lemma real_sq_sin_pi_half_one :
  real_eq (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))
          real_one.
Proof.
  apply (real_eq_trans _
    (real_plus (real_mult (cauchy_real_cos cos_pi_half) (cauchy_real_cos cos_pi_half))
               (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half)))).
  - (* s*s == 0 + s*s == c*c + s*s *)
    apply (real_eq_trans _ (real_plus real_zero
      (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half)))).
    + apply (real_eq_sym _ _). apply g1_plus_zero_l.
    + apply RealSetoid.real_eq_plus_compat.
      * (* 0 == c*c, through c*0 *)
        apply (real_eq_trans _ (real_mult (cauchy_real_cos cos_pi_half) real_zero)).
        -- apply (real_eq_sym _ _). apply real_mult_zero.
        -- apply RealSetoid.real_eq_mult_compat.
           ++ apply real_eq_refl.
           ++ apply (real_eq_sym _ _). apply real_cos_pi_half_zero.
      * apply real_eq_refl.
  - (* c*c + s*s == 1 *)
    apply real_pyth_cos_sq_sin_sq.
Qed.

(* P3. sin(pi/2) == 1: sign fixing from P2 and the positivity lemma      *)
(*     [real_sin_pi_half_pos] via the weak trichotomy.                   *)
Lemma real_sin_pi_half_one :
  real_eq (cauchy_real_sin cos_pi_half) real_one.
Proof.
  apply real_weak_trich.
  - (* Not (s < 1): s*s < s*1 == s < 1 contradicts P2 *)
    intro Hlt.
    assert (H1 : real_lt (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))
                         (real_mult (cauchy_real_sin cos_pi_half) real_one))
      by exact (real_mult_lt_compat_l _ _ _ Hlt real_sin_pi_half_pos).
    assert (H2 : real_lt (real_mult (cauchy_real_sin cos_pi_half) real_one) real_one)
      by exact (real_eq_lt_lt _ _ _ (real_mult_one _) Hlt).
    assert (H3 : real_lt (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half))
                         real_one)
      by exact (real_lt_trans _ _ _ H1 H2).
    exact (real_lt_not_eq _ _ H3 (real_sq_sin_pi_half_one)).
  - (* Not (1 < s): s*1 < s*s == s < s*s so 1 < s*s contradicts P2 *)
    intro Hlt.
    assert (H1 : real_lt (real_mult (cauchy_real_sin cos_pi_half) real_one)
                         (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half)))
      by exact (real_mult_lt_compat_l _ _ _ Hlt real_sin_pi_half_pos).
    assert (H2 : real_lt (cauchy_real_sin cos_pi_half)
                         (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half)))
      by exact (real_eq_lt_lt _ _ _ (real_eq_sym _ _ (real_mult_one _)) H1).
    assert (H3 : real_lt real_one
                         (real_mult (cauchy_real_sin cos_pi_half) (cauchy_real_sin cos_pi_half)))
      by exact (real_lt_trans _ _ _ Hlt H2).
    exact (real_lt_not_eq _ _ H3 (real_eq_sym _ _ (real_sq_sin_pi_half_one))).
Qed.

End Pythagoras.
