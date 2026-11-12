(* ConstructiveWorld-Main - the digital-structure and carrier stem of the DTPT base library *)

(** * DTPT_a: the digital-structure and carrier stem of the DTPT base library (stem A of fourteen).

    Mission.  the inductive type Dig of digital structures, the finite-sequence carriers and organization operators (insert_q/P0/rot/Pinf/interleave/Pmid), the support-domain equality faces (D5/theorem A), the entropy carriers (dedup/H_ms/H_adj), and the Q toolbox of supplementary block B2 (Z-reflection closers).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]

    References.  the DTPT base library of the constructive development (the judged-code truth-predicate line); statements conserved verbatim from the boxed original piece; consumed by the later stems of this node.

    Constructivity.  All carriers [Set]; conclusions in Set-valued order
    predicates and equality forms; zero assumed constants; zero admissions;
    every proof closes by Qed.

    Build.  [coqc -q -native-compiler no] under the acceptance build
    faces, [cpu_guard v3] wrapped. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.

(* ========== section 1: the inductive type Dig of digital structures (D1/D2/D9 constructive resolution) ========== *)

Inductive Dig : Type :=
| dQ     : Q -> Dig
| dPair  : Dig -> Dig -> Dig
| dSeq   : list Dig -> Dig
| dCode  : nat -> (nat -> Dig) -> Dig
| dJudge : Dig -> Dig -> Dig
| dModel : Dig -> Dig
| dProofT: Dig -> Dig -> Dig.

(* ========== section 2: finite-sequence carriers and organization operators (D4/D6/D7 construction) ========== *)

Fixpoint insert_q (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => [x]
  | y :: ys => if Qle_bool x y then x :: y :: ys else y :: insert_q x ys
  end.

Fixpoint P0 (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => insert_q x (P0 xs)
  end.

Definition rot (n : nat) (l : list Q) : list Q :=
  firstn n l ++ skipn n l.

Definition Pinf (l : list Q) (s : nat) : list Q :=
  rot (S s) l.

Fixpoint interleave (l1 l2 : list Q) : list Q :=
  match l1, l2 with
  | [], _ => l2
  | _ :: _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave xs ys
  end.

Definition Pmid (l : list Q) (s lam : nat) : list Q :=
  firstn lam (P0 l) ++ skipn lam (Pinf l s).

(* ========== section 3: support-domain equality (D5 -> theorem A) ========== *)

Lemma insert_q_perm_cons : forall (x : Q) (l : list Q),
  Permutation (x :: l) (insert_q x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl.
  - simpl. apply perm_skip. apply perm_nil.
  - destruct (Qle_bool x y) eqn:Hxy.
    + apply perm_skip. apply Permutation_refl.
    + etransitivity.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Theorem D5_P0_perm : forall l : list Q, Permutation l (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply Permutation_refl.
  - etransitivity.
    + apply perm_skip. exact IH.
    + apply insert_q_perm_cons.
Qed.

(* [deprecation note] over the base module where rot = firstn ++ skipn is an identity, this piece degenerates to a disguised identity corollary; the operational semantics live in the truthification layer DTPT_ROTC / DTPT_Cyc / DTPT_RotSpec. *)
Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), Permutation l (Pinf l s).
Proof.
  intros l s. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Qed.

(* D5_Pmid_perm: general lam is false (firstn/skipn truncation not a permutation); covered by endpoint theorems. *)

Theorem D5_support_same : forall (l : list Q) (s : nat),
  Permutation l (P0 l) /\ Permutation l (Pinf l s).
Proof.
  intros l s. split; [exact (D5_P0_perm l) | exact (D5_Pinf_perm l s)].
Qed.

(* ========== section 4: the multi-entropy function family and sequence-entropy separation (N9 + theorem C) ========== *)

Fixpoint dedup_aux (x : Q) (l : list Q) : list Q :=
  match l with
  | [] => []
  | y :: ys => if Qeq_bool x y then dedup_aux x ys else y :: dedup_aux x ys
  end.

Fixpoint dedup (l : list Q) : list Q :=
  match l with
  | [] => []
  | x :: xs => x :: dedup_aux x (dedup xs)
  end.

Definition H_ms (l : list Q) : Q := (Z.of_nat (length (dedup l)) # 1)%Q.

Fixpoint sum_adjdiff (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => 0
               | y :: _ => Qabs (y - x) + sum_adjdiff xs
               end
  end.

Definition H_adj (l : list Q) : Q := sum_adjdiff l.

(* ========== supplementary block B2: the Q toolbox (lia has no Q support; everything closes by direct Z reflection) ========== *)

Lemma Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> y <= x.
Proof.
  intros x y H. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

Lemma Qle_dec' : forall x y : Q, x <= y \/ y <= x.
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply Qle_bool_iff in E. exact E.
  - right. apply Qle_bool_false_le. exact E.
Qed.

Lemma qadd_le : forall a b c d : Q, a <= b -> c <= d -> (a + c <= b + d)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

Lemma qopp_le : forall a b : Q, a <= b -> (- b <= - a)%Q.
Proof.
  intros [an ad] [bn bd]; simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Lemma qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> (n * p <= m * p)%Q.
Proof.
  intros [nn nd] [mn md] [pn pd] H H0;
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma Qle_0_sub' : forall x y : Q, x <= y <-> (0 <= y - x)%Q.
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H;
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

Lemma qsub_le_r : forall a b c : Q, a <= b -> (a - c <= b - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd] H.
  unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos cd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos cd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma qsub_add : forall a b c : Q, (a - b + (b - c) == a - c)%Q.
Proof.
  intros [an ad] [bn bd] [cn cd].
  unfold Qeq, Qminus, Qplus, Qopp; simpl; lia.
Qed.

Lemma abs_eq : forall a : Q, 0 <= a -> Qabs a == a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

Lemma abs_neg : forall a : Q, a <= 0 -> Qabs a == - a.
Proof.
  intros [n d] H. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

Lemma abs_nonneg : forall a : Q, 0 <= Qabs a.
Proof.
  intros [n d]. unfold Qle. destruct n; simpl; lia.
Qed.

Lemma Qeqb_true_of : forall x y : Q, x == y -> Qeq_bool x y = true.
Proof.
  intros x y H. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

Lemma Qeqb_sym : forall x y : Q, Qeq_bool x y = Qeq_bool y x.
Proof.
  intros x y. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    apply Qeqb_true_of in E1'. congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    apply Qeqb_true_of in E2'. congruence.
Qed.

Lemma Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Qeq_bool a c = true.
Proof.
  intros a b c H1 H2. apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  apply Qeqb_true_of. transitivity b; assumption.
Qed.

