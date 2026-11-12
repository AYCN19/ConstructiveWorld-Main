(* ConstructiveWorld-Main - the measure-and-generalization stem of the DTPT base library *)

(** * DTPT_d: the measure-and-generalization stem of the DTPT base library (stem D of fourteen).

    Mission.  the counting measure base (D8, theorem B), the evidence-layered judgment network (D10), the LLM phase view record (section 7), and merged block M1: the C_gen sort-generalization family (snoc tools, reversal invariance, the all-permutation-class generalization of theorem C, the tightness witness).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c]

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
Require Import DTPT_a.
Require Import DTPT_b.
Require Import DTPT_c.
(* ========== section 5: the counting measure (D8 -> theorem B) ========== *)

Fixpoint nat_fact (n : nat) : nat :=
  match n with
  | O => 1
  | S m => S m * nat_fact m
  end.

Definition q_fact (n : nat) : Q := (Z.of_nat (nat_fact n) # 1)%Q.

Lemma Zpos_le_roundtrip : forall d : positive,
  (Z.pos d <= Z.of_nat (Pos.to_nat d))%Z.
Proof.
  induction d as [p IH | p IH | ].
  - rewrite Pos2Nat.inj_xI, Znat.Nat2Z.inj_succ, Znat.Nat2Z.inj_mul.
    rewrite Pos2Z.inj_xI. change (Z.of_nat 2) with (2%Z). lia.
  - rewrite Pos2Nat.inj_xO, Znat.Nat2Z.inj_mul, Pos2Z.inj_xO.
    change (Z.of_nat 2) with (2%Z). lia.
  - simpl. lia.
Qed.

Lemma nat_fact_ge1 : forall n : nat, (1 <= nat_fact n)%nat.
Proof.
  induction n as [| n IH]; simpl.
  - apply le_n.
  - assert (H2 : (1 * nat_fact n <= S n * nat_fact n)%nat)
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Theorem D8_sorted_frac_pos : forall K : nat, (0 < K)%nat -> 0 < (1 / (q_fact K))%Q.
Proof.
  intros K HK. unfold q_fact.
  assert (Hf : (1 <= nat_fact K)%nat) by apply nat_fact_ge1.
  assert (HfZ : (1 <= Z.of_nat (nat_fact K))%Z)
    by (apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact K))); exact Hf).
  destruct (Z.of_nat (nat_fact K)) as [| p | p] eqn:EF.
  - exfalso. lia.
  - assert (Hinv : (1 / (Z.pos p # 1) == 1 # p)%Q).
    { unfold Qdiv, Qinv. reflexivity. }
    rewrite Hinv. unfold Qlt. simpl. lia.
  - exfalso. lia.
Qed.

Theorem D8_tends_zero : forall eps : Q, 0 < eps ->
  exists K : nat, (0 < K)%nat /\ (1 / (q_fact K)%Q < eps)%Q.
Proof.
  intros eps Heps. unfold Qlt in Heps. simpl in Heps.
  remember (Qden eps) as d eqn:Ed.
  assert (Hn : (1 <= Qnum eps)%Z) by lia.
  assert (Hd : (0 < Z.pos d)%Z) by lia.
  assert (Hle : (Z.pos d <= Z.of_nat (Pos.to_nat d))%Z) by apply Zpos_le_roundtrip.
  destruct (Z.of_nat (Pos.to_nat d)) as [| p | p] eqn:EF.
  - exfalso. lia.
  - exists (S (S (Pos.to_nat d))). split.
    + lia.
    + assert (Hbound : (Z.succ (Z.succ (Z.of_nat (Pos.to_nat d)))
                        <= Z.of_nat (nat_fact (S (S (Pos.to_nat d)))))%Z).
      { rewrite <- !Znat.Nat2Z.inj_succ.
        apply (proj1 (Znat.Nat2Z.inj_le _ _)).
        simpl.
        assert (Hg : (1 <= nat_fact (S (Pos.to_nat d)))%nat) by apply nat_fact_ge1.
        assert (H2 : (S (S (Pos.to_nat d)) * 1
                      <= S (S (Pos.to_nat d)) * nat_fact (S (Pos.to_nat d)))%nat)
          by (apply Nat.mul_le_mono_l; exact Hg).
        simpl in H2. lia. }
      unfold q_fact.
      destruct (Z.of_nat (nat_fact (S (S (Pos.to_nat d))))) as [| p2 | p2] eqn:EF2.
      -- exfalso. lia.
      -- assert (Hinv : (1 / (Z.pos p2 # 1) == 1 # p2)%Q).
         { unfold Qdiv, Qinv. reflexivity. }
         rewrite Hinv. unfold Qlt. simpl.
         assert (Hp2 : (0 <= Z.pos p2)%Z) by lia.
         assert (Hmul : (1 * Z.pos p2 <= Qnum eps * Z.pos p2)%Z)
           by (apply Z.mul_le_mono_nonneg_r; [lia | exact Hn]).
         lia.
      -- exfalso. lia.
  - exfalso. try rewrite EF in Hle.
    assert (Hnn : (Z.neg p < 0)%Z).
    { change (Z.neg p) with (- Z.pos p)%Z. lia. }
    lia.
Qed.

(* ========== section 6: the evidence-layered judgment network (D10 recast) ========== *)

Inductive Level : Type := Lv0 | Lv1 | Lv2.

Inductive Evidence : Type :=
| evNum  : Q -> Evidence
| evSeq  : list Q -> Evidence
| evPair : Evidence -> Evidence -> Evidence.

Record TrNode : Type := mkTrNode {
  trLevel : Level;
  trPhi   : Dig;
  trModel : Dig;
  trValue : Evidence
}.

Definition Tex (phi : Dig) : Type := { t : TrNode & trPhi t = phi }.

Definition Tabs (phi : Dig) : Type := forall (m : Dig), Evidence.

(* ========== section 7: the LLM phase view (appendix correspondence) ========== *)

Record LLMPhaseView : Type := mkLLMView {
  lam_param      : Q;
  phase_marker   : list Q;
  gate_threshold : Q
}.

Definition gate_pass (threshold H : Q) : bool :=
  if Qle_bool H threshold then true else false.

(* ============================================================
   merged block M1 (section 8): the merge of DTPT_CGen.v - the C_gen sort-generalization family
   source piece DTPT-U1 (the Top-1 hotspot upgrade unit). Only the standalone-file
   Require/Import/Open Scope headers (carried uniformly by this file's header)
   were removed; comments, all proof bodies, the Qed face and the Print Assumptions audit exits are zero-change migrations.
   ============================================================ *)
(* ============================================================
   DTPT_CGen.v - hotspot upgrade unit C-GEN (the scan Top-1 recommendation)
   source piece: DTPT-U1 (a new file requiring DTPT, touching none of the existing eight pieces)

   main theorem (the all-permutation-class generalization of theorem C):
     C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p
   the active main theorem DTPT.C_sorted_min_adj only proves 'the sorted form <= the identity permutation';
   this piece generalizes the comparison object to any permutation p of l (the full permutation class).

   route: H_adj (P0 l) via xq_telescope (the sorted telescope) == lastq - hd;
   the first/last-element memberships are transported to p via D5_P0_perm + permutation transitivity, then closed
   with xq_pair_dist_le (the spread lower bound: the Qabs distance of any two list elements is <= H_adj).

   bonus items:
     C_gen_sym_rev  - the SYM prerequisite: reversal invariance H_adj (rev l) == H_adj l
     C_gen_attained - the tightness witness: p := P0 l built directly; the bound is attained within the permutation class
     C_gen_sorted   - the generalized re-derivation of the active main theorem C_sorted_min_adj (special-case cross-check)

   discipline: zero assumed constants, zero admissions, zero aborts, Qed throughout; Q-level lia disabled;
   all inequalities go through the xq_ bridges + ring (with Qabs/lastq/H_adj as atoms).
   ============================================================ *)

(* the standalone-file Require/Import/Open Scope headers (From Stdlib QArith/List/Permutation,
   Require Import DTPT, Import ListNotations, Open Scope Q_scope) were removed at merge time. *)

(* ========== section 0: small snoc-face tools (the SYM prerequisite) ========== *)

(* after appending one element at the end of the list, the tail element is exactly it (the Leibniz form) *)
Lemma cgen_lastq_app : forall (l : list Q) (x : Q), lastq (l ++ [x]) = x.
Proof.
  induction l as [| y ys IH]; intros x; cbn [app].
  - reflexivity.
  - destruct ys as [| b bs].
    + reflexivity.
    + exact (IH x).
Qed.

(* the snoc entropy equation: appending x at the end of a nonempty list increases the adjacent-difference sum exactly by Qabs (x - the tail element) *)
Lemma cgen_H_adj_snoc : forall (l : list Q) (x : Q),
  l <> [] -> H_adj (l ++ [x]) == (H_adj l + Qabs (x - lastq l))%Q.
Proof.
  induction l as [| y ys IH]; intros x Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct ys as [| b bs].
    + cbn [app]. unfold H_adj. cbn [sum_adjdiff lastq]. ring.
    + assert (IH' : H_adj ((b :: bs) ++ [x])
                    == (H_adj (b :: bs) + Qabs (x - lastq (b :: bs)))%Q)
        by (apply IH; discriminate).
      cbn [app].
      change (H_adj (y :: b :: (bs ++ [x])))
        with (Qabs (b - y) + H_adj ((b :: bs) ++ [x]))%Q.
      rewrite IH'.
      change (H_adj (y :: b :: bs)) with (Qabs (b - y) + H_adj (b :: bs))%Q.
      change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
      ring.
Qed.

(* the reverse of a cons list is necessarily nonempty *)
Lemma cgen_rev_cons_ne : forall (x : Q) (xs : list Q), rev (x :: xs) <> [].
Proof.
  intros x xs. change (rev (x :: xs)) with (rev xs ++ [x]).
  destruct (rev xs) as [| r rs]; cbn [app]; discriminate.
Qed.

(* the tail element of the reversed list equals the head of the original list *)
Lemma cgen_lastq_rev_cons : forall (b : Q) (bs : list Q),
  lastq (rev (b :: bs)) == b.
Proof.
  intros b bs. change (rev (b :: bs)) with (rev bs ++ [b]).
  rewrite cgen_lastq_app. reflexivity.
Qed.

(* ========== section 1: bonus item SYM, reversal invariance ========== *)

Theorem C_gen_sym_rev : forall l : list Q, H_adj (rev l) == H_adj l.
Proof.
  induction l as [| a rest IH].
  - reflexivity.
  - cbn [rev].
    destruct rest as [| b bs].
    + reflexivity.
    + rewrite cgen_H_adj_snoc by (apply cgen_rev_cons_ne).
      rewrite IH.
      rewrite cgen_lastq_rev_cons.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      rewrite (xq_abs_sub_comm a b).
      ring.
Qed.

(* ========== section 2: main theorem, the all-permutation-class generalization of theorem C ========== *)

(* C_gen: the sort-minimality holds for any permutation p of l.
   the special case p := l is exactly the active main theorem C_sorted_min_adj; the proof skeleton is isomorphic to it,
   with only the membership-transport segment changed to a 'permutation-transitivity composition': P0 l ~> l ~> p in one step. *)
Theorem C_gen : forall (l p : list Q), Permutation l p -> H_adj (P0 l) <= H_adj p.
Proof.
  intros l p Hperm. destruct l as [| a rest].
  - (* l = []: the permutation class contains only the empty list *)
    assert (Hp : p = []) by (apply Permutation_nil; exact Hperm).
    rewrite Hp. apply Qle_refl.
  - (* l = a :: rest: P0 l is nonempty, telescope expansion + spread lower bound *)
    assert (Hne : P0 (a :: rest) <> []) by (apply xq_P0_cons_ne).
    assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest)))).
      apply xq_abs_id.
      apply (proj1 (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    (* permutation-transitivity composition: P0 l is a permutation of l (D5 reversed), and l is a permutation of p *)
    assert (Hrev : Permutation (P0 (a :: rest)) (a :: rest))
      by (apply Permutation_sym; apply D5_P0_perm).
    assert (HpermP : Permutation (P0 (a :: rest)) p).
    { apply perm_trans with (l' := a :: rest).
      - exact Hrev.
      - exact Hperm. }
    (* the first and last elements transported into the membership of p *)
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_hd_In_gen. exact Hne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) p).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - exact HpermP.
      - apply xq_lastq_In. exact Hne. }
    (* the spread lower bound holds over p *)
    assert (HPd : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  <= H_adj p)
      by (apply xq_pair_dist_le; assumption).
    (* closed by the Qeq setoid chain: H_adj (P0 l) == tail - head == Qabs(head - tail) <= H_adj p *)
    rewrite HP. rewrite <- HP2. exact HPd.
Qed.

(* ========== section 3: the tightness witness and the generalization cross-check ========== *)

(* tightness: the bound is attained within the permutation class (the infimum is the minimum), witnessed by P0 l directly.
   read together with C_gen: H_adj (P0 l) is the minimum of H_adj over the permutation class
   {p : Permutation l p} - the generalized bound cannot be lowered further. *)
Theorem C_gen_attained : forall l : list Q,
  exists p : list Q, Permutation l p /\ H_adj p == H_adj (P0 l).
Proof.
  intro l. exists (P0 l). split.
  - apply D5_P0_perm.
  - apply Qeq_refl.
Qed.

(* the active main theorem C_sorted_min_adj is a special case of C_gen (re-derivation cross-check at p := l) *)
Corollary C_gen_sorted : forall l : list Q, H_adj (P0 l) <= H_adj l.
Proof.
  intro l. apply (C_gen l l). apply Permutation_refl.
Qed.

(* ========== the G4 assumption audit (expecting Closed under the global context) ========== *)

Print Assumptions C_gen.
Print Assumptions C_gen_sym_rev.
Print Assumptions C_gen_attained.
Print Assumptions C_gen_sorted.

