(* ConstructiveWorld-Main - the Bishop-style non-strict order on the
   constructive reals. *)

(** * GaC1_RB01_RealLeB: the Bishop-form order [real_le_b].

    Mission.  The Bishop-style non-strict order on the constructive
      reals: x <=_B y := for every real eps > 0, x < y + eps
      ([real_le_b]).  This is the epsilon characterization of the
      non-strict order in constructive analysis.  It is implied by the
      disjunctive order [real_le] x y = (x < y) + (x == y), but it
      does not require deciding which disjunct holds, so it is the
      form in which effective estimates (such as ln x <= x - 1) are
      stated and consumed.

    Dependencies.  Requires [S02_CauchyComplete] ([Real],
      [real_lt], [real_plus], [real_zero]) of this development.

    References.  E. Bishop and D. Bridges, Constructive Analysis
      (Springer, 1985), Chapter 2, the order on real numbers and its
      epsilon form; classical analogue in mathlib:
      [le_of_forall_pos_lt_add].

    Constructivity.  [real_le_b] is a transparent definition whose
      value is a Set-sorted dependent product over [Real]; the inner
      premise ([real_lt real_zero eps]) and conclusion
      ([real_lt x (real_plus y eps)]) are Set-sorted; zero Prop
      component; closed under the global context; [coqchk] reports
      zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <this directory> ""
      -Q <S-tree directory> "" GaC1_RB01_RealLeB.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3]. *)

Require Import S02_CauchyComplete.

(* Bishop-style non-strict order: x <=_B y holds when x < y + eps is
   witnessed for every positive margin eps. *)
Definition real_le_b (x y : Real) : Set :=
  forall eps : Real, real_lt real_zero eps -> real_lt x (real_plus y eps).

Print Assumptions real_le_b.
