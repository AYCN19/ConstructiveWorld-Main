(* ConstructiveWorld-Main - monotonicity and the basic effective bound of
   the constructive real logarithm. *)

(** * GaC1_01_LogMono: log monotonicity and the Bishop-form linear bound.

    Mission.  Monotonicity and the basic effective bound of the
      constructive real logarithm: strict monotonicity
      [gaC1_01_log_lt_mono], weak Or-form monotonicity
      [gaC1_01_log_le_mono], and the Bishop-form bound
      ln x <= x + (-1) [gaC1_01_log_le_linear_B].

    Dependencies.  Requires [S02_CauchyComplete],
      [S07_RealSetoidExpLog] ([real_log], [real_log_lt_mono]),
      [S14_B5BatchBlock] ([real_log_le_mono]), [GaC1_RB01_RealLeB]
      ([real_le_b], the Bishop-form order), and
      [GaC1_RB03_LogLeLinearB] ([real_log_le_linear_B]) of this
      development.

    References.  mathlib [Log/Basic.lean] log_lt_log / log_le_log /
      log_le_sub_one_of_pos.  Statement provenance: A1 is already
      available as [real_log_lt_mono] at S07:6540, so A1/A1le are thin
      consumption restatements; the draft's Or-form A2 ([real_le]) is
      constructively unavailable, because [real_le_to_le_b] is one-way
      by design and the Or-form bound ln x <= x - 1 would decide
      x = 1, so A2 is recast in the Bishop form [real_le_b].  The
      strict variant A2' (x <> 1 -> ln x < x - 1) is dropped: it needs
      the classical trichotomy on x = 1 and is not constructively
      provable in this Set-sorted carrier; the omission is explicit,
      not silent.

    Constructivity.  Every named construction is carried by [Set]; all
      predicates are Set-sorted ([real_eq], [real_lt], [real_le],
      [real_le_b], [QltT]); zero classical choice; the development is
      closed under the global context; [coqchk] reports zero assumed
      constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_01_LogMono.v] compiles cleanly (exit 0), wrapped
      by [cpu_guard v3]. *)

Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S14_B5BatchBlock.
Require Import GaC1_RB01_RealLeB.
Require Import GaC1_RB03_LogLeLinearB.

(* ===================================================================== *)
(* Section 1. Log monotonicity (consumption restatements).                *)
(* ===================================================================== *)

Section LogMono.

(* A1. Strict monotonicity: 0 < x < y  ->  ln x < ln y.                   *)
Lemma gaC1_01_log_lt_mono :
  forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
    real_lt x y -> real_lt (real_log x Hx) (real_log y Hy).
Proof.
  intros x y Hx Hy Hlt.
  unfold real_log.
  exact (real_log_lt_mono x y Hx Hy Hlt).
Qed.

(* A1le. Weak monotonicity: 0 < x, 0 < y, x <= y  ->  ln x <= ln y        *)
(*       (Or-form carried through from the S14 statement).                *)
Lemma gaC1_01_log_le_mono :
  forall (a b : Real) (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
    real_le a b -> real_le (real_log a Ha) (real_log b Hb).
Proof.
  intros a b Ha Hb Hab.
  exact (real_log_le_mono a b Ha Hb Hab).
Qed.

End LogMono.

(* ===================================================================== *)
(* Section 2. The basic effective bound (Bishop form).                    *)
(* ===================================================================== *)

Section LogLinear.

(* A2. ln x <= x + (-1) for 0 < x, in the Bishop form real_le_b.          *)
(*     This is the constructively correct reading of the draft's          *)
(*     statement A2; the Or-form reading would decide x = 1.              *)
Lemma gaC1_01_log_le_linear_B :
  forall (x : Real) (Hx : real_lt real_zero x),
    real_le_b (real_log x Hx) (real_plus x (real_opp real_one)).
Proof.
  intros x Hx.
  exact (real_log_le_linear_B x Hx).
Qed.

End LogLinear.
