(* ConstructiveWorld-Main - the effective linear bound on the constructive
   logarithm in Bishop form. *)

(** * GaC1_RB03_LogLeLinearB: ln x <= x + (-1) in the Bishop order.

    Mission.  The effective linear bound on the constructive logarithm
      in Bishop form: ln x <=_B x + (-1) for every real x > 0
      ([real_log_le_linear_B], on the bookkeeping identity
      [gaC1_rb03_mult_const_one]).  The S07 development provides, for
      every margin delta > 0, the disjunctive estimate
      ln x <= (x - 1) + delta.  Given eps > 0 the proof chooses the
      explicit margin delta := eps * (1/2), which satisfies
      0 < delta < eps, and turns each disjunct into the strict
      inequality ln x < (x - 1) + eps by additive translation by
      delta < eps; the resulting epsilon statement is exactly
      [real_le_b].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [Setoid],
      [Morphisms].  Requires [S01_BaseRing], [S02_CauchyComplete]
      ([real_const], [real_mult], [real_eq_of_zero_diff],
      [real_lt_trans], [real_lt_eq_lt], [real_eq_lt_lt],
      [QltT_to_Qlt]), [S07_RealSetoidExpLog] ([real_log],
      [real_const_pos], [real_const_lt], [real_mult_positive],
      [real_mult_lt_compat_l], [real_lt_plus_translate],
      [RealInterfaceEnhancedMod.real_log_le_linear_eps]), and
      [GaC1_RB01_RealLeB] ([real_le_b]) of this development.

    References.  mathlib
      [Analysis/SpecialFunctions/Log/Basic.lean]
      log_le_sub_one_of_pos (classical form of the bound); E. Bishop
      and D. Bridges, Constructive Analysis (Springer, 1985),
      Chapter 2, for the epsilon order.

    Constructivity.  The statement and every auxiliary lemma are
      Set-sorted; the margin delta is an explicit real-number term, so
      no choice principle is invoked; the rational facts 0 < 1/2 < 1
      are decided by computation on [QltT]; the ring tactic is used
      only in the bookkeeping identity e * 1 == e; closed under the
      global context; [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <this directory> ""
      -Q <S-tree directory> "" GaC1_RB03_LogLeLinearB.v] compiles
      cleanly (exit 0), wrapped by [cpu_guard v3]. *)

From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_RB01_RealLeB.

(* Bookkeeping identity: multiplication by the rational constant 1 is
   the identity, checked pointwise on the Cauchy representatives. *)
Lemma gaC1_rb03_mult_const_one : forall e : Real,
  real_eq (real_mult e (real_const 1%Q)) e.
Proof.
  intro e. apply real_eq_of_zero_diff. intro n.
  destruct e as [u Hu]. cbn [real_mult real_const projT1]. ring.
Qed.

(* Main bound: the logarithm is bounded by the line x + (-1), in the
   Bishop-style order. *)
Lemma real_log_le_linear_B : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx. unfold real_le_b. intros eps Heps.
  assert (HhalfQ : QltT 0 (1#2)%Q) by reflexivity.
  assert (Hhalf_pos : real_lt real_zero (real_const (1#2)%Q))
    by exact (real_const_pos (1#2)%Q HhalfQ).
  assert (Hhalf_lt : real_lt (real_const (1#2)%Q) (real_const 1%Q)).
  { apply real_const_lt. apply QltT_to_Qlt. reflexivity. }
  assert (Hdelta_pos : real_lt real_zero (real_mult eps (real_const (1#2)%Q)))
    by exact (real_mult_positive eps (real_const (1#2)%Q) Heps Hhalf_pos).
  assert (Hdelta_lt : real_lt (real_mult eps (real_const (1#2)%Q)) eps).
  { apply (real_lt_eq_lt _ (real_mult eps (real_const 1%Q)) _).
    - exact (real_mult_lt_compat_l (real_const (1#2)%Q)
               (real_const 1%Q) eps Hhalf_lt Heps).
    - exact (gaC1_rb03_mult_const_one eps). }
  destruct (RealInterfaceEnhancedMod.real_log_le_linear_eps x
              (real_mult eps (real_const (1#2)%Q)) Hx Hdelta_pos)
    as [Hlt | Heq].
  - exact (real_lt_trans _ _ _ Hlt
             (real_lt_plus_translate _ _ _ Hdelta_lt)).
  - exact (real_eq_lt_lt _ _ _ Heq
             (real_lt_plus_translate _ _ _ Hdelta_lt)).
Qed.

Print Assumptions gaC1_rb03_mult_const_one.
Print Assumptions real_log_le_linear_B.
