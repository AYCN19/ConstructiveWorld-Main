(* ConstructiveWorld-Main - the real k-th root and square root as explicit
   exp/log witnesses on the constructive real line. *)

(** * GaC1_05_RealPowRoot: the real k-th root via exp and log.

    Mission.  The real k-th root as an explicit exp/log witness
      [kroot] (kroot k x Hx := exp((1/k) * ln x), red-line path A:
      witness first), its positivity [gaC1_05_kroot_pos], its defining
      log characterization [gaC1_05_log_kroot], the injectivity
      engines [gaC1_05_exp_inj] (strict monotonicity + weak
      trichotomy), [gaC1_05_log_wd] (log witness-independence,
      resolving pit E845), [gaC1_05_log_eq_transfer],
      [gaC1_05_log_inj], and the square-root instance
      [gaC1_05_sqrt_sq]: sqrt x * sqrt x == x with the uniqueness of
      the positive square root [gaC1_05_sqrt_unique].  Honest
      deferral: the general-k power identity (kroot)^k == x and the
      general-k uniqueness need the [natmulR]/const bridge (k-fold sum
      == k * y) and its cancellation; they are deferred explicitly
      (the k = 2 instance is delivered in full through the
      half-scaling argument).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [Setoid],
      [Morphisms].  Requires [S02_CauchyComplete], [S03_QExp]
      ([cauchy_real_exp], [cauchy_real_exp_pos]),
      [S07_RealSetoidExpLog] ([cw_log], [real_log],
      [cauchy_real_exp_mono], [cauchy_real_exp_wd],
      [real_weak_trich], [real_lt_not_eq], [real_log_mult]),
      [GaC1_01_LogMono], and [GaC1_02_LogPowBridge]
      ([gaC1_02_log_exp]) of this development.

    References.  mathlib [Pow/Real.lean] rpow_def_of_pos
      (x^y = exp(log x * y)), rpow_pos_of_pos, sqrt_eq_rpow; KB36:141
      c_log main-branch witness form.

    Constructivity.  Every named construction is carried by [Set];
      predicates are Set-sorted ([real_eq], [real_lt], [QltT], [Id]);
      zero classical choice; closed under the global context;
      [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_05_RealPowRoot.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_01_LogMono.
Require Import GaC1_02_LogPowBridge.

(* ===================================================================== *)
(* Section 1. The witness (E1 shape) and positivity (E3).                 *)
(* ===================================================================== *)

Section RootWitness.

Definition kroot (k : positive) (x : Real) (Hx : real_lt real_zero x) : Real :=
  cauchy_real_exp (real_mult (real_const (1 # k)%Q) (real_log x Hx)).

(* E3. kroot is positive. *)
Lemma gaC1_05_kroot_pos : forall (k : positive) (x : Real) (Hx : real_lt real_zero x),
  real_lt real_zero (kroot k x Hx).
Proof.
  intros k x Hx. unfold kroot. apply cauchy_real_exp_pos.
Qed.

(* The defining log characterization: ln(kroot) == (1/k) * ln x         *)
(* (at the canonical positivity witness of exp).                          *)
Lemma gaC1_05_log_kroot : forall (k : positive) (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (kroot k x Hx)
             (cauchy_real_exp_pos (real_mult (real_const (1 # k)%Q) (real_log x Hx))))
          (real_mult (real_const (1 # k)%Q) (real_log x Hx)).
Proof.
  intros k x Hx. unfold kroot.
  exact (gaC1_02_log_exp (real_mult (real_const (1 # k)%Q) (real_log x Hx))).
Qed.

End RootWitness.

(* ===================================================================== *)
(* Section 2. Injectivity engines (exp_inj, log witness-independence,     *)
(* log_inj).                                                              *)
(* ===================================================================== *)

Section InjEngines.

(* exp is injective: strict monotonicity + weak trichotomy. *)
Lemma gaC1_05_exp_inj : forall u v : Real,
  real_eq (cauchy_real_exp u) (cauchy_real_exp v) -> real_eq u v.
Proof.
  intros u v H. apply real_weak_trich.
  - intro Hlt. exact (real_lt_not_eq _ _ (cauchy_real_exp_mono u v Hlt) H).
  - intro Hlt.
    exact (real_lt_not_eq _ _ (cauchy_real_exp_mono v u Hlt) (real_eq_sym _ _ H)).
Qed.

(* real_log is independent of the positivity witness (pit E845). *)
Lemma gaC1_05_log_wd : forall (x : Real) (H1 H2 : real_lt real_zero x),
  real_eq (real_log x H1) (real_log x H2).
Proof.
  intros x H1 H2. apply gaC1_05_exp_inj. unfold real_log.
  apply (real_eq_trans _ x).
  - exact (cw_log_exp_right x H1).
  - apply (real_eq_sym _ _). exact (cw_log_exp_right x H2).
Qed.

(* log is congruent on positives (any witnesses). *)
Lemma gaC1_05_log_eq_transfer :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_eq a b -> real_eq (cw_log a Ha) (cw_log b Hb).
Proof.
  intros a b Ha Hb H. apply gaC1_05_exp_inj.
  apply (real_eq_trans _ a).
  - exact (cw_log_exp_right a Ha).
  - apply (real_eq_trans _ b).
    + exact H.
    + apply (real_eq_sym _ _). exact (cw_log_exp_right b Hb).
Qed.

(* log is injective on positives (any witnesses). *)
Lemma gaC1_05_log_inj : forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_log a Ha) (real_log b Hb) -> real_eq a b.
Proof.
  intros a b Ha Hb H. unfold real_log in H.
  apply (real_eq_trans _ (cauchy_real_exp (cw_log a Ha))).
  - apply (real_eq_sym _ _). exact (cw_log_exp_right a Ha).
  - apply (real_eq_trans _ (cauchy_real_exp (cw_log b Hb))).
    + exact (cauchy_real_exp_wd _ _ H).
    + exact (cw_log_exp_right b Hb).
Qed.

End InjEngines.

(* ===================================================================== *)
(* Section 3. The square-root instance (E4) and its uniqueness (E2, k=2). *)
(* ===================================================================== *)

Section SqrtInstance.

Definition sqrtR (x : Real) (Hx : real_lt real_zero x) : Real := kroot 2 x Hx.

(* half + half == whole, through the literal 1/2. *)
Lemma g05_half_twice : forall L : Real,
  real_eq (real_plus (real_mult (real_const (1 # 2)%Q) L)
                     (real_mult (real_const (1 # 2)%Q) L)) L.
Proof.
  intro L. destruct L as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_mult real_const projT1].
  ring.
Qed.

(* E4. sqrt x * sqrt x == x. *)
Lemma gaC1_05_sqrt_sq : forall (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_mult (sqrtR x Hx) (sqrtR x Hx)) x.
Proof.
  intros x Hx.
  apply (gaC1_05_log_inj _ _
    (real_mult_positive _ _ (gaC1_05_kroot_pos 2 x Hx) (gaC1_05_kroot_pos 2 x Hx)) Hx).
  apply (real_eq_trans _ (real_plus (real_log (sqrtR x Hx) (gaC1_05_kroot_pos 2 x Hx))
                                    (real_log (sqrtR x Hx) (gaC1_05_kroot_pos 2 x Hx)))).
  - exact (real_log_mult _ _ (gaC1_05_kroot_pos 2 x Hx) (gaC1_05_kroot_pos 2 x Hx)).
  - apply (real_eq_trans _ (real_plus (real_mult (real_const (1 # 2)%Q) (real_log x Hx))
                                      (real_mult (real_const (1 # 2)%Q) (real_log x Hx)))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply (real_eq_trans _ (real_log (sqrtR x Hx)
                 (cauchy_real_exp_pos (real_mult (real_const (1 # 2)%Q) (real_log x Hx))))).
        -- apply gaC1_05_log_wd.
        -- exact (gaC1_05_log_kroot 2 x Hx).
      * apply (real_eq_trans _ (real_log (sqrtR x Hx)
                 (cauchy_real_exp_pos (real_mult (real_const (1 # 2)%Q) (real_log x Hx))))).
        -- apply gaC1_05_log_wd.
        -- exact (gaC1_05_log_kroot 2 x Hx).
    + exact (g05_half_twice (real_log x Hx)).
Qed.

(* E2 (k=2). The positive square root is unique. *)
Lemma gaC1_05_sqrt_unique :
  forall (x s t : Real) (Hx : real_lt real_zero x)
         (Hs : real_lt real_zero s) (Ht : real_lt real_zero t),
    real_eq (real_mult s s) x -> real_eq (real_mult t t) x -> real_eq s t.
Proof.
  intros x s t Hx Hs Ht Hss Htt.
  apply (gaC1_05_log_inj s t Hs Ht).
  (* ln s == (1/2)(ln s + ln s) == (1/2) ln(s*s) == (1/2) ln x == ... == ln t *)
  apply (real_eq_trans _ (real_mult (real_const (1 # 2)%Q)
                            (real_plus (real_log s Hs) (real_log s Hs)))).
  { apply (real_eq_sym _ _).
    apply (real_eq_trans _ (real_plus (real_mult (real_const (1 # 2)%Q) (real_log s Hs))
                                      (real_mult (real_const (1 # 2)%Q) (real_log s Hs)))).
    - apply real_eq_of_zero_diff. intro n.
      generalize (real_log s Hs). intro L. destruct L as [u Hu].
      cbn [real_plus real_mult real_const projT1]. ring.
    - exact (g05_half_twice (real_log s Hs)). }
  apply (real_eq_trans _ (real_mult (real_const (1 # 2)%Q)
                            (real_plus (real_log t Ht) (real_log t Ht)))).
  { apply RealSetoid.real_eq_mult_compat.
    - apply real_eq_refl.
    - (* ln s + ln s == ln(s*s) == ln x == ln(t*t) == ln t + ln t *)
      apply (real_eq_trans _ (real_log (real_mult s s) (real_mult_positive s s Hs Hs))).
      + apply (real_eq_sym _ _). exact (real_log_mult s s Hs Hs).
      + apply (real_eq_trans _ (real_log (real_mult t t) (real_mult_positive t t Ht Ht))).
        * (* ln(s*s) == ln(t*t) via s*s == x == t*t with witness transfer *)
          apply (real_eq_trans _ (real_log x Hx)).
          -- unfold real_log. exact (gaC1_05_log_eq_transfer _ _ _ _ Hss).
          -- unfold real_log. apply (real_eq_sym _ _).
             exact (gaC1_05_log_eq_transfer _ _ _ _ Htt).
        * exact (real_log_mult t t Ht Ht). }
  (* (1/2)(ln t + ln t) == ln t *)
  apply (real_eq_trans _ (real_plus (real_mult (real_const (1 # 2)%Q) (real_log t Ht))
                                    (real_mult (real_const (1 # 2)%Q) (real_log t Ht)))).
  - apply real_eq_of_zero_diff. intro n.
    generalize (real_log t Ht). intro L. destruct L as [u Hu].
    cbn [real_plus real_mult real_const projT1]. ring.
  - exact (g05_half_twice (real_log t Ht)).
Qed.

End SqrtInstance.
