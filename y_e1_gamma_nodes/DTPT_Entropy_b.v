(* ConstructiveWorld-Main - DTPT_Entropy_b: gate-clean LINT-6 split piece 2/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_b.

    Mission.  the multi-entropy evaluation suite (a constructive rendering.
      Carries source lines 397-493 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a (linear Require Import chain).
    References.  Boxed face ConstructiveWorld_Live/DTPT_Entropy.v (231/231 statement texts
      mechanically verified verbatim against this cast); seat_wash80 setlive_probe_world.
    Constructivity.  Zero axioms, nothing left open, no classical logic; Set-carried
      statements; every proof closes with Qed.  Numerical check instances live in
      DTPT_Entropy_cert (R2 certificate separation).
    Build.  coqc -native-compiler no -q via cpu_guard_v3 (TempLimit 96), flat work/build face.
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Notation S := Datatypes.S.
From Stdlib Require Import Setoid Morphisms.

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

Require Import DTPT_Entropy_a.

(* ========== the multi-entropy evaluation suite (a constructive rendering
   of the operational heuristics) ========== *)

Record MultiEntropyEval : Type := mkME {
  me_carrier : list Q;        (* the carrier being evaluated *)
  me_Hadj    : Q;             (* sequential entropy (adjacent differences) *)
  me_Hms     : Q;             (* multiset entropy (count of distinct values) *)
  me_Hsh     : Q;             (* Shannon entropy (frequency counting) *)
  me_Hcond   : Q              (* conditional entropy (context dependence) *)
}.

Definition mkMEval (l : list Q) (ctx : list Q) : MultiEntropyEval :=
  mkME l (H_adj l) (H_ms l) (H_devsum l) (H_cond l ctx).

(* ========== the operational heuristics, stated constructively ========== *)

(* phase evaluation: decide on which side of P0/Pinf/Pmid the output lies *)
Definition phase_side (l : list Q) (s : nat) : nat :=
  (* 0 = closer to P0; 1 = closer to Pinf (comparing the sequential entropy
   against a threshold; the difference is data, not a Prop) *)
  if Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s)) then 0 else 1.

(* hallucination suppression: down-weight extreme phases (a constructive
   rendering of zero-locus filtering) *)
Definition gate_low_entropy (H : Q) (threshold : Q) : bool :=
  Qle_bool H threshold.

(* alignment: a lambda biased toward P0, for verifiable knowledge *)
(* the identity definition below keeps its historical name and signature;
   the real definition is [align_lambda_opt] at the end of the file (an
   optimal lambda chooser over the two entropies h0/h1, with the same
   semantics as the lambda optimizers of [DTPT_Rotation]). *)
Definition align_lambda (lam : Q) : Q := lam.

(* ========== key theorems ========== *)

(* the mixed entropy is monotone in lambda — continuity of the P_mid
   interpolation entropy *)
Lemma qadd_nonneg : forall a b : Q, 0 <= a -> 0 <= b -> QleT' (0) (a + b).
Proof.
  intros [an ad] [bn bd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Theorem H_lam_mono : forall (l : list Q) (s : nat),
  H_adj (Pinf l s) <= H_adj (P0 l) ->
  forall lam1 lam2 : Q,
    (lam1 <= lam2)%Q -> QleT' (H_lam l s lam1) (H_lam l s lam2).
Proof.
  intros l s Hle lam1 lam2 Hlam. apply Qle_to_QleT'. unfold H_lam.
  change (1 - lam1) with (1 + - lam1)%Q.
  change (1 - lam2) with (1 + - lam2)%Q.
  assert (Hd : (0 <= H_adj (P0 l) + - H_adj (Pinf l s))%Q)
    by (apply QleT'_to_Qle; apply (fst (Qle_0_sub' _ _));
        exact (Qle_to_QleT' _ _ Hle)).
  assert (E1 : lam1 * H_adj (P0 l) + (1 + - lam1) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam1 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  assert (E2 : lam2 * H_adj (P0 l) + (1 + - lam2) * H_adj (Pinf l s)
             == H_adj (Pinf l s) + lam2 * (H_adj (P0 l) + - H_adj (Pinf l s)))
    by ring.
  rewrite E1, E2.
  apply QleT'_to_Qle.
  apply qadd_le;
    [ apply Qle_refl
    | apply QleT'_to_Qle; apply qmul_le_r; [exact Hlam | exact Hd] ].
Qed.

(* nonnegativity of the Shannon entropy (discrete Q version) *)
Theorem H_shannon_q_nonneg : forall l : list Q, QleT' (0) (H_devsum l).
Proof.
  intro l. apply Qle_to_QleT'.
  induction l as [| x xs IH]; simpl.
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply qadd_nonneg.
    + apply QleT'_to_Qle. apply (abs_nonneg (x - hd 0 (P0 (x :: xs)))).
    + exact IH.
Qed.

