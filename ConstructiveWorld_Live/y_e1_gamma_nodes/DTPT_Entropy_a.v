(* ConstructiveWorld-Main - DTPT_Entropy_a: gate-clean LINT-6 split piece 1/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_a.

    Mission.  Set-carrier bridge twins (mirroring the [DTPT] toolbox).
      Carries source lines 43-396 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete.
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


(* ========== Set-carrier bridge twins (mirroring the [DTPT] toolbox)
   ========== *)
(* [Id]/[NatLe]/[QeqT]/[QleT']/[QltT] and their up/down bridges are supplied
   by [S01_BaseRing]/[S02_CauchyComplete]; *)
(* this section adds the eq -> Id bridge twins and the [IffT] carrier (not
   exported by [S01]; twin copies of the [DTPT] definitions). *)
(* zero Prop statement face and nothing admitted; [IffT A B] := (A -> B) *
   (B -> A) is the Set-carried if and only if. *)

Lemma eq_imp_id {A : Set} {x y : A} (H : x = y) : Id x y.
Proof. destruct H. apply id_refl. Qed.

Definition IffT (A B : Set) : Set := (A -> B) * (B -> A).
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

(* Deprecation note: under the base module where [rot] satisfies the
   identity [rot = firstn ++ skipn], this statement is a direct consequence
   of that identity; the operational semantics are carried by [DTPT_ROTC],
   [DTPT_Cyc] and [DTPT_RotSpec]. *)

Theorem D5_Pinf_perm : forall (l : list Q) (s : nat), Permutation l (Pinf l s).
Proof.
  intros l s. unfold Pinf, rot.
  rewrite firstn_skipn.
  apply Permutation_refl.
Qed.

(* D5_Pmid_perm: general lam is false (firstn/skipn truncation not a permutation); covered by endpoint theorems. *)

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

(* ========== Q toolbox ([Lia] does not support [Q]; everything is decided
   by Z reflection) ========== *)

Lemma Qle_bool_false_le : forall x y : Q, Qle_bool x y = false -> QleT' (y) (x).
Proof.
  intros x y H. apply Qle_to_QleT'. unfold Qle_bool in H. unfold Qle.
  destruct (Z.leb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E.
  - discriminate.
  - apply Z.leb_gt in E. lia.
Qed.

Lemma Qle_dec' : forall x y : Q, Or (QleT' x y) (QleT' y x).
Proof.
  intros x y. destruct (Qle_bool x y) eqn:E.
  - left. apply Qle_to_QleT'. apply Qle_bool_iff in E. exact E.
  - right. apply Qle_bool_false_le. exact E.
Qed.

Lemma qadd_le : forall a b c d : Q, a <= b -> c <= d -> QleT' (a + c) (b + d).
Proof.
  intros [an ad] [bn bd] [cn cd] [dn dd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((an * Zpos bd) * (Zpos cd * Zpos dd)
                <= (bn * Zpos ad) * (Zpos cd * Zpos dd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  assert (H2 : ((cn * Zpos dd) * (Zpos ad * Zpos bd)
                <= (dn * Zpos cd) * (Zpos ad * Zpos bd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H0]).
  lia.
Qed.

Lemma qopp_le : forall a b : Q, a <= b -> QleT' (- b) (- a).
Proof.
  intros [an ad] [bn bd] H.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *;
  unfold Qle; simpl; lia.
Qed.

Lemma qmul_le_r : forall n m p : Q, n <= m -> 0 <= p -> QleT' (n * p) (m * p).
Proof.
  intros [nn nd] [mn md] [pn pd] H H0.
  apply Qle_to_QleT'.
  simpl in *; unfold Qle in *; simpl in *; unfold Qle; simpl.
  assert (H1 : ((nn * Zpos md) * (pn * Zpos pd)
                <= (mn * Zpos nd) * (pn * Zpos pd))%Z) by
    (apply Z.mul_le_mono_nonneg_r; [lia | exact H]).
  lia.
Qed.

Lemma Qle_0_sub' : forall x y : Q, IffT (QleT' x y) (QleT' 0 (y - x)).
Proof.
  intros [nx dx] [ny dy]; simpl; split; intros H.
  - apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ H) as Hq.
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
  - apply Qle_to_QleT'.
    pose proof (QleT'_to_Qle _ _ H) as Hq.
    unfold Qle, Qminus, Qplus, Qopp in *; simpl in *; simpl; lia.
Qed.

Lemma abs_eq : forall a : Q, 0 <= a -> QeqT (Qabs a) (a).
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - reflexivity.
  - exfalso. lia.
Qed.

Lemma abs_neg : forall a : Q, a <= 0 -> QeqT (Qabs a) (- a).
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qle in H. simpl in H. unfold Qeq.
  destruct n as [| p | p].
  - simpl. lia.
  - exfalso. lia.
  - reflexivity.
Qed.

Lemma abs_nonneg : forall a : Q, QleT' (0) (Qabs a).
Proof.
  intros [n d]. apply Qle_to_QleT'. unfold Qle. destruct n; simpl; lia.
Qed.

Lemma Qeqb_true_of : forall x y : Q, x == y -> Id (Qeq_bool x y) (true).
Proof.
  intros x y H. apply eq_imp_id. unfold Qeq in H. unfold Qeq_bool.
  destruct (Z.eqb (Qnum x * QDen y)%Z (Qnum y * QDen x)%Z) eqn:E; [reflexivity|].
  exfalso. apply Z.eqb_neq in E. lia.
Qed.

Lemma Qeqb_sym : forall x y : Q, Id (Qeq_bool x y) (Qeq_bool y x).
Proof.
  intros x y. apply eq_imp_id. destruct (Qeq_bool x y) eqn:E1, (Qeq_bool y x) eqn:E2; try reflexivity.
  - exfalso. apply Qeq_bool_eq in E1.
    assert (E1' : y == x) by (apply Qeq_sym; exact E1).
    assert (E1b : Id (Qeq_bool y x) true) by (apply Qeqb_true_of; exact E1').
    assert (E1c : Qeq_bool y x = true) by (destruct (id_sym E1b); reflexivity).
    congruence.
  - exfalso. apply Qeq_bool_eq in E2.
    assert (E2' : x == y) by (apply Qeq_sym; exact E2).
    assert (E2b : Id (Qeq_bool x y) true) by (apply Qeqb_true_of; exact E2').
    assert (E2c : Qeq_bool x y = true) by (destruct (id_sym E2b); reflexivity).
    congruence.
Qed.

Lemma Qeqb_trans : forall a b c : Q,
  Qeq_bool a b = true -> Qeq_bool b c = true -> Id (Qeq_bool a c) (true).
Proof.
  intros a b c H1 H2. apply Qeqb_true_of.
  apply Qeq_bool_eq in H1. apply Qeq_bool_eq in H2.
  transitivity b; assumption.
Qed.

(* ========== infrastructure for the [H_ms] permutation invariance lemmas
   ([Qeq] membership and the dedup characterization) ========== *)

Definition Qmem (a : Q) (l : list Q) : Set :=
  Id (existsb (fun y => Qeq_bool a y) l) true.

Lemma Qmem_cons : forall a x (l : list Q),
  IffT (Qmem a (x :: l))
       (Or (Id (Qeq_bool a x) true) (Qmem a l)).
Proof.
  intros a x l. split.
  - intro H. unfold Qmem in *. simpl in H.
    assert (Hb : (Qeq_bool a x || existsb (fun y => Qeq_bool a y) l)%bool = true)
      by (destruct (id_sym H); reflexivity).
    destruct (Qeq_bool a x) eqn:Ex.
    + left. apply eq_imp_id. reflexivity.
    + right. apply eq_imp_id. exact Hb.
  - intro H. destruct H as [E | Hl].
    + apply eq_imp_id. simpl. rewrite E. reflexivity.
    + apply eq_imp_id. simpl. destruct (id_sym Hl). apply orb_true_r.
Qed.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof.
  intros x l. apply (snd (Qmem_cons x x l)). left.
  apply eq_imp_id. apply Qeq_bool_refl.
Qed.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. inversion H.
  - intros H. destruct (Qeq_bool x y).
    + apply (snd (Qmem_cons _ _ _)). right. exact (IH H).
    + apply (fst (Qmem_cons _ _ _)) in H. destruct H as [H|H].
      * apply (snd (Qmem_cons _ _ _)). left. exact H.
      * apply (snd (Qmem_cons _ _ _)). right. exact (IH H).
Qed.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> Qeq_bool a x = false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. inversion H.
  - intros H Hax. apply (fst (Qmem_cons _ _ _)) in H.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hay : Qeq_bool a y = true) by (destruct (id_sym H); reflexivity).
        apply Qeq_bool_sym in Hay.
        assert (HxaI : Id (Qeq_bool x a) true)
          by (apply (Qeqb_trans x y a); assumption).
        assert (Hxa : Qeq_bool x a = true)
          by (destruct (id_sym HxaI); reflexivity).
        apply Qeq_bool_sym in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + apply (snd (Qmem_cons _ _ _)). destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. inversion H.
  - intros H. apply (fst (Qmem_cons _ _ _)) in H. destruct H as [H|H].
    + apply (snd (Qmem_cons _ _ _)). left. exact H.
    + apply (snd (Qmem_cons _ _ _)). right. apply IH.
      exact (Qmem_dedup_aux_keep a x _ H).
Qed.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - intros H. inversion H.
  - intros H. apply (snd (Qmem_cons _ _ _)).
    apply (fst (Qmem_cons _ _ _)) in H.
    destruct H as [H|H].
    + left. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * left. apply eq_imp_id. reflexivity.
      * right. apply Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

Definition gate_pass (threshold H : Q) : bool :=
  if Qle_bool H threshold then true else false.

(* ============================================================
   The generalized sorting family for [H_adj]: the [C_gen] theorems.
   ============================================================ *)
(* ============================================================
   The [C_gen] family: minimality of the sorted sequence generalized from
   the identity permutation to the whole permutation class.
   Main theorem:
     [C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p]
   Route: [H_adj (P0 l)] == lastq - hd by the telescoping identity
   ([xq_telescope]); endpoint membership is transported to p by
   [D5_P0_perm] and transitivity of Permutation; closed by
   [xq_pair_dist_le] (the span lower bound: the Qabs distance of any two
   elements is <= H_adj).
   Companions:
     [C_gen_sym_rev]  — reversal invariance: [H_adj (rev l) == H_adj l]
     [C_gen_attained] — the bound is attained at p := P0 l
     [C_gen_sorted]   — the sorted case re-derived (sanity specialization)
   Q-layer [lia] is unavailable; all inequalities go through the [xq_]
   bridges and [ring], with [Qabs]/[lastq]/[H_adj] as atoms.
   ============================================================ *)



(* ========== snoc-level helpers (for the reversal invariance) ========== *)

(* after appending one element at the end of the list, the tail element is
   that element (Leibniz form) *)



(* ========== discrete Shannon entropy over Q (frequency counting; Shannon
   on Q-lists) ========== *)

Fixpoint count_val (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_val x ys) else count_val x ys
  end.

Fixpoint H_devsum (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => Qabs (x - hd 0 (P0 l)) + H_devsum xs
  end.

(* compatibility notation for the old name ([only parsing]); the semantics
   is unchanged *)
Notation H_shannon_q := H_devsum (only parsing).

Definition H_cond (l : list Q) (ctx : list Q) : Q :=
  H_devsum l - H_devsum ctx.

(* ========== lambda-interpolated mixed entropy (the entropy version of the
   P_mid interpolation) ========== *)
Definition H_lam (l : list Q) (s : nat) (lam : Q) : Q :=
  lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s).
