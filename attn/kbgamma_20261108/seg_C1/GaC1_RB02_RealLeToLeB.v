(* ConstructiveWorld-Main - the one-way bridge from the disjunctive real
   order to the Bishop-style epsilon order. *)

(** * GaC1_RB02_RealLeToLeB: real_le implies real_le_b.

    Mission.  The one-way bridge from the disjunctive order
      [real_le] x y = (x < y) + (x == y) to the Bishop-style order
      [real_le_b] x y: in either disjunct, x < y + eps holds for every
      eps > 0 ([real_le_to_le_b], on the lifting step
      [real_lt_plus_eps_r]).  The lt disjunct is lifted by
      transitivity through y < y + eps; the eq disjunct is transported
      by [real_eq_lt_lt] through the same step.  The converse
      direction would decide x < y or x == y from an epsilon estimate
      and is not available constructively; only this direction is
      provided.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete]
      ([real_le], [real_lt_trans], [real_eq_lt_lt], [real_eq_sym],
      [real_plus_zero]), [S07_RealSetoidExpLog]
      ([real_lt_plus_translate]), and [GaC1_RB01_RealLeB]
      ([real_le_b]) of this development.

    References.  E. Bishop and D. Bridges, Constructive Analysis
      (Springer, 1985), Chapter 2; the auxiliary step y < y + eps is
      the additive translation of 0 < eps.

    Constructivity.  Both statements are Set-sorted ([real_le] is the
      Set-valued sum type, [real_le_b] the Set-valued product); the
      proof is a case analysis on the sum followed by transitivity and
      transport; zero Prop statement; closed under the global context;
      [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <this directory> ""
      -Q <S-tree directory> "" GaC1_RB02_RealLeToLeB.v] compiles
      cleanly (exit 0), wrapped by [cpu_guard v3]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_RB01_RealLeB.

(* A positive margin lifts any point: 0 < eps implies y < y + eps.
   Proof: y equals y + 0, and the strict inequality translates on the
   right by eps. *)
Lemma real_lt_plus_eps_r : forall (y eps : Real),
  real_lt real_zero eps -> real_lt y (real_plus y eps).
Proof.
  intros y eps Heps.
  apply (real_eq_lt_lt y (real_plus y real_zero) (real_plus y eps)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_translate. exact Heps.
Qed.

(* One-way bridge: the disjunctive order implies the Bishop-style order. *)
Lemma real_le_to_le_b : forall x y : Real, real_le x y -> real_le_b x y.
Proof.
  intros x y Hle. unfold real_le_b. intros eps Heps.
  assert (Hup : real_lt y (real_plus y eps))
    by exact (real_lt_plus_eps_r y eps Heps).
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans x y (real_plus y eps) Hlt Hup).
  - exact (real_eq_lt_lt x y (real_plus y eps) Heq Hup).
Qed.

Print Assumptions real_lt_plus_eps_r.
Print Assumptions real_le_to_le_b.
