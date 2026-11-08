(* ConstructiveWorld-Main - the x^s growth-characterization core of the
   Perron chain. *)
(** * GaC3_P07_PowerGrowth: the power-growth modulus core.
    Mission.  The x^s growth-characterization core (node C3-P07): the
      complex-exponential modulus identity in the squared norm
      [GaC3_P07_cexp_norm_sq], |e^z|^2 == (e^{Re z})^2; the
      rational-embedded power carriers [GaC3_P07_cpowR]
      (x^sigma := exp(sigma * ln x), real) and [GaC3_P07_cpow]
      (x^s := exp(s * ln x), complex); the (s,t)*(L,0) reduction faces
      [GaC3_P07_cmult_L0]/[GaC3_P07_cRe_mult_L0]; and the modulus
      theorem [GaC3_P07_xpow_mod], |x^{sigma+it}|^2 == (x^sigma)^2.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qround], [QArith.Qring], [PeanoNat], [Setoid],
      [Morphisms].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog] ([real_log],
      [cauchy_real_exp_wd]), [S10_KVQuantTrig] (the Pythagorean
      closure), [CxRealPairCore] (Cx carrier), and
      [CxRealPairExpLog] (the [c_exp] polar form) of this development.
    References.  AFP Dirichlet_Series_At_I_Infinity_Bound
      (eval_fds_smallo_Im_going_to_infinity :484-515, quantitative
      restatement shape); cards_C3-P07; drafts_C3 P07 study card (the
      |x^s| = x^sigma face is carried in squared norm form, on the
      [c_norm_sq] carrier; the 1/|s| bound and zero-term decay faces
      are deferred: they need the complex inverse carrier and
      cert-face numerics).
    Constructivity.  Set-carried statements; [real_eq] via the
      pointwise Cauchy predicate; the Pythagorean step consumes the
      S10 closure at [real_eq] level; zero classical choice; [coqchk]
      reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC3_P07_PowerGrowth.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround QArith.Qring.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.

(* ===================================================================== *)
(* Section 1. The c_exp modulus identity (squared carrier).               *)
(* ===================================================================== *)

(* |e^z|^2 == (e^{Re z})^2 in the squared norm. *)
Lemma GaC3_P07_cexp_norm_sq : forall z : Cx,
  real_eq (c_norm_sq (c_exp z))
          (real_mult (cauchy_real_exp (cRe z)) (cauchy_real_exp (cRe z))).
Proof.
  intro z.
  unfold c_norm_sq, c_exp, cRe, cIm.
  cbn [fst snd].
  (* middle term: (a*a) * (cos^2 + sin^2) with a := e^{Re z} *)
  apply (real_eq_trans _
    (real_mult (real_mult (cauchy_real_exp (fst z)) (cauchy_real_exp (fst z)))
               (real_plus (real_mult (cauchy_real_cos (snd z)) (cauchy_real_cos (snd z)))
                          (real_mult (cauchy_real_sin (snd z)) (cauchy_real_sin (snd z)))))).
  - (* step 1 (pointwise): (a*c)^2 + (a*s)^2 == (a*a)*(c^2 + s^2) *)
    apply real_eq_of_zero_diff. intro n.
    rewrite (real_plus_proj
              (real_mult (real_mult (cauchy_real_exp (fst z)) (cauchy_real_cos (snd z)))
                         (real_mult (cauchy_real_exp (fst z)) (cauchy_real_cos (snd z))))
              (real_mult (real_mult (cauchy_real_exp (fst z)) (cauchy_real_sin (snd z)))
                         (real_mult (cauchy_real_exp (fst z)) (cauchy_real_sin (snd z)))) n).
    rewrite (real_mult_proj (real_mult (cauchy_real_exp (fst z)) (cauchy_real_cos (snd z)))
                            (real_mult (cauchy_real_exp (fst z)) (cauchy_real_cos (snd z))) n).
    rewrite (real_mult_proj (real_mult (cauchy_real_exp (fst z)) (cauchy_real_sin (snd z)))
                            (real_mult (cauchy_real_exp (fst z)) (cauchy_real_sin (snd z))) n).
    rewrite (real_mult_proj (cauchy_real_exp (fst z)) (cauchy_real_cos (snd z)) n).
    rewrite (real_mult_proj (cauchy_real_exp (fst z)) (cauchy_real_sin (snd z)) n).
    rewrite (real_mult_proj (real_mult (cauchy_real_exp (fst z)) (cauchy_real_exp (fst z)))
                            (real_plus (real_mult (cauchy_real_cos (snd z)) (cauchy_real_cos (snd z)))
                                       (real_mult (cauchy_real_sin (snd z)) (cauchy_real_sin (snd z)))) n).
    rewrite (real_mult_proj (cauchy_real_exp (fst z)) (cauchy_real_exp (fst z)) n).
    rewrite (real_plus_proj (real_mult (cauchy_real_cos (snd z)) (cauchy_real_cos (snd z)))
                            (real_mult (cauchy_real_sin (snd z)) (cauchy_real_sin (snd z))) n).
    rewrite (real_mult_proj (cauchy_real_cos (snd z)) (cauchy_real_cos (snd z)) n).
    rewrite (real_mult_proj (cauchy_real_sin (snd z)) (cauchy_real_sin (snd z)) n).
    ring.
  - (* step 2: (a*a) * (cos^2 + sin^2) == (a*a) * 1 == a*a *)
    apply (real_eq_trans _ (real_mult (real_mult (cauchy_real_exp (fst z)) (cauchy_real_exp (fst z)))
                                      real_one)).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact (real_cos_sq_plus_sin_sq_one (snd z)).
    + exact (real_mult_one (real_mult (cauchy_real_exp (fst z)) (cauchy_real_exp (fst z)))).
Qed.

(* ===================================================================== *)
(* Section 2. Power carriers and the (s,t)*(L,0) reduction.               *)
(* ===================================================================== *)

(* Real-layer power x^sigma := e^{sigma * ln x} for x > 0. *)
Definition GaC3_P07_cpowR (x : Real) (Hx : real_lt real_zero x) (s : Real) : Real :=
  cauchy_real_exp (real_mult s (real_log x Hx)).

(* Complex-layer power x^{s+it} := e^{(s+it) * ln x}. *)
Definition GaC3_P07_cpow (x : Real) (Hx : real_lt real_zero x) (s t : Real) : Cx :=
  c_exp (c_mult (s, t) (real_log x Hx, real_zero)).

(* (s,t) * (L,0) == (s*L, t*L) as complex equality. *)
Lemma GaC3_P07_cmult_L0 : forall s t L : Real,
  c_eq (c_mult (s, t) (L, real_zero)) (real_mult s L, real_mult t L).
Proof.
  intros s t L. unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    unfold cRe, c_mult. cbn [fst snd].
    rewrite (real_plus_proj
              (real_mult s L)
              (real_opp (real_mult t real_zero)) n).
    rewrite (real_mult_proj s L n).
    rewrite (real_opp_proj (real_mult t real_zero) n).
    rewrite (real_mult_proj t real_zero n).
    assert (Hz : projT1 real_zero n == 0) by reflexivity.
    rewrite Hz.
    ring.
  - apply real_eq_of_zero_diff. intro n.
    unfold cIm, c_mult. cbn [fst snd].
    rewrite (real_plus_proj
              (real_mult s real_zero)
              (real_mult t L) n).
    rewrite (real_mult_proj s real_zero n).
    rewrite (real_mult_proj t L n).
    assert (Hz : projT1 real_zero n == 0) by reflexivity.
    rewrite Hz.
    ring.
Qed.

(* The real-part reduction cRe((s,t)*(L,0)) == s*L (real_eq). *)
Lemma GaC3_P07_cRe_mult_L0 : forall s t L : Real,
  real_eq (cRe (c_mult (s, t) (L, real_zero))) (real_mult s L).
Proof.
  intros s t L. unfold cRe, c_mult. cbn [fst snd].
  apply real_eq_of_zero_diff. intro n.
  rewrite (real_plus_proj
            (real_mult s L)
            (real_opp (real_mult t real_zero)) n).
  rewrite (real_mult_proj s L n).
  rewrite (real_opp_proj (real_mult t real_zero) n).
  rewrite (real_mult_proj t real_zero n).
  assert (Hz : projT1 real_zero n == 0) by reflexivity.
  rewrite Hz.
  ring.
Qed.

(* ===================================================================== *)
(* Section 3. The modulus theorem for complex powers.                     *)
(* ===================================================================== *)

(* |x^{s+it}|^2 == (x^s)^2 for x > 0. *)
Theorem GaC3_P07_xpow_mod : forall (x s t : Real) (Hx : real_lt real_zero x),
  real_eq (c_norm_sq (GaC3_P07_cpow x Hx s t))
          (real_mult (GaC3_P07_cpowR x Hx s) (GaC3_P07_cpowR x Hx s)).
Proof.
  intros x s t Hx. unfold GaC3_P07_cpow, GaC3_P07_cpowR.
  apply (real_eq_trans
           (c_norm_sq (c_exp (c_mult (s, t) (real_log x Hx, real_zero))))
           (real_mult (cauchy_real_exp (cRe (c_mult (s, t) (real_log x Hx, real_zero))))
                      (cauchy_real_exp (cRe (c_mult (s, t) (real_log x Hx, real_zero)))))).
  - exact (GaC3_P07_cexp_norm_sq (c_mult (s, t) (real_log x Hx, real_zero))).
  - apply RealSetoid.real_eq_mult_compat.
    + apply cauchy_real_exp_wd.
      exact (GaC3_P07_cRe_mult_L0 s t (real_log x Hx)).
    + apply cauchy_real_exp_wd.
      exact (GaC3_P07_cRe_mult_L0 s t (real_log x Hx)).
Qed.
