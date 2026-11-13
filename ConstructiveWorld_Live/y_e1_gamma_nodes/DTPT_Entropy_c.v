(* ConstructiveWorld-Main - DTPT_Entropy_c: gate-clean LINT-6 split piece 3/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_c.

    Mission.  main theorem 1: P0 minimizes the sequential entropy.
      Carries source lines 494-848 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b.

(* ============================================================
   Cross-phase entropy bridging theorems:
     (1) P0 minimizes the sequential entropy: [H_adj (P0 l) <= H_adj l]
         (pairing/telescoping route: a sorted list has entropy max - min,
         and any pairing has distance <= the sequential entropy)
     (2) cross-phase lower bound: [H_adj (P0 l) <= H_adj (Pinf l s)]
         (key fact: [rot = firstn ++ skipn], so [Pinf l s] = l)
     (3) lambda-interpolated mixed entropy sandwich:
         [H_adj (P0 l) <= H_lam l s lam <= H_adj (Pinf l s)],
         [0 <= lam <= 1]
     (4) vanishing of the Shannon deviation entropy at phase P0:
         [H_devsum (P0 l) == 0], and its minimality
     (5) permutation invariance of the frequency counts and cross-phase
         invariance of the spectrum (contrasting with the sequential
         entropy family)
     (6) conditional entropy: self-conditional zero, antisymmetry,
         guarded nonnegativity, and a negative example delimiting scope
   The local [xq_] lemmas of this block are auxiliary tools, depending only
   on [D5_P0_perm] / [D5_Pinf_perm] / [insert_q_perm_cons] / [qadd_le] /
   [Qle_bool_false_le].
   ============================================================ *)

(* ---------- local [xq] tools: Q order and absolute value ---------- *)

Lemma xq_Qle_bool_true : forall x y : Q, (x <= y)%Q -> Id (Qle_bool x y) (true).
Proof.
  intros [nx dx] [ny dy] H. apply eq_imp_id.
  unfold Qle in H. unfold Qle_bool; simpl. apply Z.leb_le. unfold Z.le.
  destruct (Z.compare (nx * Z.pos dy) (ny * Z.pos dx)) eqn:E.
  - discriminate.
  - discriminate.
  - exfalso. apply H. exact E.
Qed.

Lemma xq_Qle_bool_le : forall x y : Q, Qle_bool x y = true -> QleT' (x) (y).
Proof.
  intros [nx dx] [ny dy] H. apply Qle_to_QleT'.
  unfold Qle_bool; simpl. apply Z.leb_le. exact H.
Qed.

Lemma xq_Qle_antisym : forall x y : Q, (x <= y)%Q -> (y <= x)%Q -> QeqT x y.
Proof.
  intros [nx dx] [ny dy] H1 H2. apply qeq_imp_qeqT.
  unfold Qle in H1, H2; simpl in H1, H2.
  unfold Qeq; simpl. lia.
Qed.

(* [Qabs] in Rocq 9 is implemented via [Z.abs]: Qabs (n # d) = (Z.abs n # d) *)
Lemma xq_abs_id : forall x : Q, (0 <= x)%Q -> QeqT (Qabs x) (x).
Proof.
  intros [n d] Hx. apply qeq_imp_qeqT. unfold Qle in Hx; simpl in Hx.
  assert (Hn : (0 <= n)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite (Z.abs_eq n Hn). reflexivity.
Qed.

Lemma xq_abs_eq0 : forall x : Q, x == 0 -> QeqT (Qabs x) 0.
Proof.
  intros [n d] Hx. apply qeq_imp_qeqT.
  unfold Qeq in Hx; simpl in Hx.
  assert (Hn : (n = 0)%Z) by lia.
  unfold Qabs; simpl. unfold Qeq; simpl.
  rewrite Hn. reflexivity.
Qed.

Lemma xq_minus_self : forall x : Q, QeqT (x - x) 0.
Proof.
  intros [n d]. apply qeq_imp_qeqT.
  unfold Qminus, Qeq; simpl. lia.
Qed.

Lemma xq_abs_zero : forall x : Q, QeqT (Qabs (x - x)) 0.
Proof.
  intro x. apply xq_abs_eq0.
  apply qeqT_imp_qeq. apply xq_minus_self.
Qed.

Lemma xq_abs_eq : forall x y : Q, x == y -> QeqT (Qabs x) (Qabs y).
Proof.
  intros [n1 d1] [n2 d2] Hxy. apply qeq_imp_qeqT.
  unfold Qeq in Hxy; simpl in Hxy.
  unfold Qabs; simpl. unfold Qeq; simpl.
  pose proof (Z.abs_spec n1) as Ha1. pose proof (Z.abs_spec n2) as Ha2.
  destruct Ha1 as [[A1 B1] | [A1 B1]];
    destruct Ha2 as [[A2 B2] | [A2 B2]];
    try rewrite B1; try rewrite B2; lia.
Qed.

Lemma xq_abs_opp : forall x : Q, QeqT (Qabs (- x)) (Qabs x).
Proof.
  intros [n d]. apply qeq_imp_qeqT.
  unfold Qabs, Qopp; simpl. unfold Qeq; simpl.
  rewrite Z.abs_opp. reflexivity.
Qed.

Lemma xq_minus_opp : forall a b : Q, QeqT (b - a) (- (a - b)).
Proof.
  intros [na da] [nb db]. apply qeq_imp_qeqT.
  unfold Qminus, Qopp, Qeq; simpl.
  rewrite (Pos.mul_comm db da). ring.
Qed.

Lemma xq_abs_sub_comm : forall a b : Q, QeqT (Qabs (a - b)) (Qabs (b - a)).
Proof.
  intros a b. apply qeq_imp_qeqT.
  assert (H1 : Qabs (-(a - b)) == Qabs (a - b)) by (apply qeqT_imp_qeq; apply xq_abs_opp).
  rewrite <- H1.
  apply qeqT_imp_qeq. apply xq_abs_eq. symmetry. apply qeqT_imp_qeq. apply xq_minus_opp.
Qed.

Lemma xq_H_adj_nonneg : forall l : list Q, QleT' (0) (H_adj l).
Proof.
  intro l. apply Qle_to_QleT'. induction l as [| a rest IH].
  - apply Qle_refl.
  - destruct rest as [| b bs].
    + apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      apply QleT'_to_Qle. apply qadd_nonneg;
        [ apply QleT'_to_Qle; apply abs_nonneg | exact IH ].
Qed.

Lemma xq_le_add_abs : forall t h : Q, QleT' (h) (Qabs t + h).
Proof.
  intros t h.
  pose proof (qadd_le 0 (Qabs t) h h
    (QleT'_to_Qle _ _ (abs_nonneg t)) (Qle_refl h)) as HS.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HS) as HS2.
  rewrite Qplus_0_l in HS2.
  exact HS2.
Qed.

(* ---------- local [xq] tools: the ascending predicate and the P0 normal
   form ---------- *)

Inductive SortedQ : list Q -> Set :=
| sortQ_nil : SortedQ []
| sortQ_cons : forall x xs,
    SortedQ xs -> Forall (fun z => (x <= z)%Q) xs -> SortedQ (x :: xs).

Lemma xq_sortQ_insert : forall (x : Q) (l : list Q),
  SortedQ l -> SortedQ (insert_q x l).
Proof.
  intros x l. revert x. induction l as [| y ys IH]; intros x HS.
  - simpl. apply sortQ_cons; [ apply sortQ_nil | apply Forall_nil ].
  - inversion HS as [| x0 xs0 HSys HFall]; subst.
    rewrite Forall_forall in HFall.
    simpl. destruct (Qle_bool x y) eqn:E.
    + apply sortQ_cons; [ exact HS | ].
      rewrite Forall_forall. intros z Hz. destruct Hz as [Heq | Hz].
      * subst. apply QleT'_to_Qle. apply xq_Qle_bool_le. exact E.
      * apply (Qle_trans x y z).
        -- apply QleT'_to_Qle. apply xq_Qle_bool_le. exact E.
        -- apply HFall. exact Hz.
    + apply sortQ_cons; [ apply IH; exact HSys | ].
      rewrite Forall_forall. intros z Hz.
      assert (Hin : In z (x :: ys)).
      { apply Permutation_in with (l := insert_q x ys).
        - apply Permutation_sym. apply insert_q_perm_cons.
        - exact Hz. }
      destruct Hin as [Heq | Hin].
      * subst. apply QleT'_to_Qle. apply Qle_bool_false_le. exact E.
      * apply HFall. exact Hin.
Qed.

Lemma xq_P0_sorted : forall l : list Q, SortedQ (P0 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - apply sortQ_nil.
  - apply xq_sortQ_insert. exact IH.
Qed.

(* [xq_insert_q_head_aux]: when the insertion point is >= the compared
   element, [insert_q] places the element at the head directly *)
Lemma xq_insert_q_head_aux : forall (a b : Q) (bs : list Q),
  (a <= b)%Q -> Id (insert_q a (b :: bs)) (a :: b :: bs).
Proof.
  intros a b bs H. apply eq_imp_id. simpl.
  destruct (id_sym (xq_Qle_bool_true _ _ H)). reflexivity.
Qed.

Lemma xq_sortQ_P0_id : forall l : list Q, SortedQ l -> Id (P0 l) (l).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply eq_imp_id.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    rewrite Forall_forall in HFa.
    change (P0 (a :: rest)) with (insert_q a (P0 rest)).
    destruct (id_sym (IH HSr)). destruct rest as [| b bs].
    + reflexivity.
    + destruct (id_sym (xq_insert_q_head_aux a b bs
                   (HFa b (or_introl eq_refl)))).
      reflexivity.
Qed.

(* ---------- local [xq] tools: the [lastq] tail element and the telescoping
   equation ---------- *)

Fixpoint lastq (l : list Q) : Q :=
  match l with
  | [] => 0
  | x :: xs => match xs with
               | [] => x
               | _ :: _ => lastq xs
               end
  end.

Lemma xq_lastq_In : forall m : list Q, m <> [] -> In (lastq m) m.
Proof.
  induction m as [| a rest IH]; intros Hne.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b bs].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. simpl. discriminate.
Qed.

Lemma xq_hd_In_gen : forall m : list Q, m <> [] -> In (hd 0 m) m.
Proof.
  intros [| h t] H; [ exfalso; apply H; reflexivity | simpl; left; reflexivity ].
Qed.

Lemma xq_P0_cons_ne : forall (x : Q) (xs : list Q), P0 (x :: xs) <> [].
Proof.
  intros x xs. cbn [P0].
  destruct (P0 xs) as [| y ys]; cbn [insert_q].
  - discriminate.
  - destruct (Qle_bool x y); discriminate.
Qed.

Lemma xq_hd_le_lastq : forall l : list Q, SortedQ l -> QleT' (hd 0 l) (lastq l).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply Qle_to_QleT'.
  - simpl. apply Qle_refl.
  - destruct rest as [| b bs].
    + simpl. apply Qle_refl.
    + inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      apply (Qle_trans a b).
      * apply HFa. left. reflexivity.
      * apply QleT'_to_Qle. apply IH. exact HSr.
Qed.

(* telescoping equation: the sum of adjacent differences of an ascending
   list equals the last element minus the first *)
Lemma xq_telescope : forall l : list Q, SortedQ l -> QeqT (H_adj l) (lastq l - hd 0 l).
Proof.
  induction l as [| a rest IH]; intro HS.
  - apply qeq_imp_qeqT. reflexivity.
  - destruct rest as [| b bs].
    + apply qeq_imp_qeqT.
      change (H_adj [a]) with 0%Q.
      change (lastq [a] - hd 0 [a]) with (a - a)%Q.
      symmetry. apply qeqT_imp_qeq. apply xq_minus_self.
    + apply qeq_imp_qeqT.
      inversion HS as [| x0 xs0 HSr HFa]; subst.
      rewrite Forall_forall in HFa.
      change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      assert (Hab : (0 <= b - a)%Q).
      { apply QleT'_to_Qle. apply (fst (Qle_0_sub' a b)).
        apply Qle_to_QleT'. apply HFa. left. reflexivity. }
      rewrite (qeqT_imp_qeq _ _ (xq_abs_id _ Hab)).
      rewrite (qeqT_imp_qeq _ _ (IH HSr)).
      change (lastq (a :: b :: bs)) with (lastq (b :: bs)).
      change (hd 0 (a :: b :: bs)) with a.
      change (hd 0 (b :: bs)) with b.
      ring.
Qed.

(* pairing distance bound: the Qabs distance of any two elements of the list
   is at most the sequential entropy *)
Lemma xq_pair_dist_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> QleT' (Qabs (x - y)) (H_adj l).
Proof.
  intro l. induction l as [| a rest IH]; intros x y Hx Hy; apply Qle_to_QleT'.
  - exfalso. exact Hx.
  - destruct rest as [| b bs].
    + destruct Hx as [Hx | []]; destruct Hy as [Hy | []]; subst.
      rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)). apply Qle_refl.
    + change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
      destruct Hx as [<- | Hx]; destruct Hy as [<- | Hy].
      * rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)).
        apply QleT'_to_Qle. apply qadd_nonneg;
          [ apply QleT'_to_Qle; apply abs_nonneg
          | apply QleT'_to_Qle; apply xq_H_adj_nonneg ].
      * assert (Hr1 : a - y == (a - b) + (b - y)) by ring.
        rewrite Hr1.
        apply (Qle_trans _ (Qabs (a - b) + Qabs (b - y))).
        -- apply Qabs_triangle.
        -- rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm a b)).
           apply QleT'_to_Qle. apply qadd_le; [ apply Qle_refl
                          | apply QleT'_to_Qle; apply IH;
                            [ left; reflexivity | exact Hy ] ].
      * assert (Hr2 : x - a == (x - b) + (b - a)) by ring.
        rewrite Hr2.
        apply (Qle_trans _ (Qabs (x - b) + Qabs (b - a))).
        -- apply Qabs_triangle.
        -- rewrite (Qplus_comm (Qabs (x - b)) (Qabs (b - a))).
           apply QleT'_to_Qle. apply qadd_le; [ apply Qle_refl
                          | apply QleT'_to_Qle; apply IH;
                            [ exact Hx | left; reflexivity ] ].
      * apply (Qle_trans _ (H_adj (b :: bs))).
        -- apply QleT'_to_Qle. apply IH; assumption.
        -- apply QleT'_to_Qle. apply xq_le_add_abs.
Qed.

(* ========== main theorem 1: P0 minimizes the sequential entropy
   ========== *)

Theorem H_adj_P0_min : forall l : list Q, QleT' (H_adj (P0 l)) (H_adj l).
Proof.
  intro l. apply Qle_to_QleT'. destruct l as [| a rest].
  - apply Qle_refl.
  - assert (HP : H_adj (P0 (a :: rest))
                 == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest)))
      by (apply qeqT_imp_qeq; apply xq_telescope; apply xq_P0_sorted).
    assert (HP2 : Qabs (hd 0 (P0 (a :: rest)) - lastq (P0 (a :: rest)))
                  == lastq (P0 (a :: rest)) - hd 0 (P0 (a :: rest))).
    { rewrite (qeqT_imp_qeq _ _ (xq_abs_sub_comm (hd 0 (P0 (a :: rest))) (lastq (P0 (a :: rest))))).
      apply qeqT_imp_qeq. apply xq_abs_id.
      apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply xq_hd_le_lastq. apply xq_P0_sorted. }
    rewrite HP. rewrite <- HP2.
    assert (Hm1 : In (hd 0 (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_hd_In_gen. apply xq_P0_cons_ne. }
    assert (Hm2 : In (lastq (P0 (a :: rest))) (a :: rest)).
    { apply Permutation_in with (l := P0 (a :: rest)).
      - apply Permutation_sym. apply D5_P0_perm.
      - apply xq_lastq_In. apply xq_P0_cons_ne. }
    apply QleT'_to_Qle. apply xq_pair_dist_le; assumption.
Qed.

(* ========== main theorem 2: cross-phase lower bound (Pinf side)
   ========== *)

Corollary Pinf_eq_l : forall (l : list Q) (s : nat), Id (Pinf l s) (l).
Proof.
  intros l. induction l as [| a rest IH]; intros s; apply eq_imp_id.
  - reflexivity.
  - unfold Pinf, rot. destruct s as [| s'].
    + reflexivity.
    + change (firstn (S (S s')) (a :: rest) ++ skipn (S (S s')) (a :: rest) = a :: rest)
        with (a :: (firstn (S s') rest ++ skipn (S s') rest) = a :: rest).
      f_equal. change (firstn (S s') rest ++ skipn (S s') rest) with (Pinf rest s').
      destruct (id_sym (IH s')). reflexivity.
Qed.

Theorem H_adj_cross_phase_lb : forall (l : list Q) (s : nat), QleT' (H_adj (P0 l)) (H_adj (Pinf l s)).
Proof.
  intros l s. apply Qle_to_QleT'.
  destruct (id_sym (Pinf_eq_l l s)).
  apply QleT'_to_Qle. apply H_adj_P0_min.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions xq_Qle_bool_true.
Print Assumptions xq_Qle_bool_le.
Print Assumptions Pinf_eq_l.