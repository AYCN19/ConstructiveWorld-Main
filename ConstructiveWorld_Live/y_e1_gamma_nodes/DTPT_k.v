(* ConstructiveWorld-Main - the upper-bound-and-judgment stem of the DTPT base library *)

(** * DTPT_k: the upper-bound-and-judgment stem of the DTPT base library (stem K of fourteen).

    Mission.  the entropy upper-bound family (the D7 Hsup prefix maxima), the truth-network completion (the D10 T-minus counterexample), the three-phase judgment completion, and the S1 reinforcement block (swap_adj, count_q, sort uniqueness, the main theorem P0_perm_inv, the entropy loads, the phase_classify behavior face).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f], [DTPT_g], [DTPT_h], [DTPT_i], [DTPT_j]

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
Require Import DTPT_d.
Require Import DTPT_e.
Require Import DTPT_f.
Require Import DTPT_g.
Require Import DTPT_h.
Require Import DTPT_i.
Require Import DTPT_j.
(* ========== section D: the entropy upper-bound family (the D7 H-infinity dynamic supremum - one of the seven core concepts of the source text) ========== *)

(* gap item 9: the Hsup prefix-maximum family - the maximum of H(Pinf l i) over i in [0,n] *)
Fixpoint Hsup (l : list Q) (n : nat) : Q :=
  match n with
  | 0%nat => H_adj (Pinf l 0)
  | S m => let prev := Hsup l m in
           let cur := H_adj (Pinf l (S m)) in
           if Qle_bool prev cur then cur else prev
  end.

Lemma Hsup_S_eq : forall (l : list Q) (n : nat),
  Hsup l (S n) =
  if Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))
  then H_adj (Pinf l (S n)) else Hsup l n.
Proof. reflexivity. Qed.

(* gap item 10: the monotonicity law - prefix maxima increase naturally (the D7 'dynamically infinitely rising family') *)
(* [deprecation note] over the base module where rot = firstn ++ skipn is an identity, this piece degenerates to a disguised identity corollary; the operational semantics live in the truthification layer DTPT_ROTC / DTPT_Cyc / DTPT_RotSpec. *)
Theorem Hsup_mono : forall (l : list Q) (n : nat),
  (Hsup l n <= Hsup l (S n))%Q.
Proof.
  intros l n. rewrite Hsup_S_eq.
  destruct (Qle_bool (Hsup l n) (H_adj (Pinf l (S n)))) eqn:E.
  - apply (proj1 (Qle_bool_iff _ _)). exact E.
  - apply Qle_refl.
Qed.

(* gap item 11: a finite upper bound - the rational H_adj value is bounded (for a fixed l, H_adj <= the upper bound sum of |x_i| + |x_{i+1}|) *)
(* [deprecation note] over the base module where rot = firstn ++ skipn is an identity, this piece degenerates to a disguised identity corollary; the operational semantics live in the truthification layer DTPT_ROTC / DTPT_Cyc / DTPT_RotSpec. *)
Theorem Hsup_bounded : forall (l : list Q) (n : nat) (B : Q),
  (forall x, In x l -> Qabs x <= B) ->
  (Hsup l n <= (Z.of_nat (length l) # 1)%Q * B * 2)%Q.
Proof.
  intros l n B HB.
  assert (Hinst : forall i : nat,
            (H_adj (Pinf l i) <= (Z.of_nat (length l) # 1) * B * 2)%Q).
  { intros i. rewrite (Permutation_length (D5_Pinf_perm l i)).
    apply H_adj_bound. intros x Hx.
    apply HB. apply Permutation_in with (l := Pinf l i);
      [ apply Permutation_sym; apply D5_Pinf_perm | exact Hx ]. }
  clear HB. induction n as [| m IH].
  - change (Hsup l 0) with (H_adj (Pinf l 0)). apply Hinst.
  - rewrite Hsup_S_eq.
    destruct (Qle_bool (Hsup l m) (H_adj (Pinf l (S m)))) eqn:E.
    + apply Hinst.
    + exact IH.
Qed.

(* ========== section E: the truth-network completion (the D10 three-sublayer interconnection + the T-minus counterexample) ========== *)

(* gap item 13: the counterexample node T-minus (the constructivization of the source text 'the truth network contains counterexample falsification nodes') *)
(* a counterexample = there exists a model whose evidence chain proves the negation of phi - constructive negation = evidence *)
Record RefNode : Type := mkRef {
  refPhi    : Dig;
  refModel  : Dig;
  refCounter: Evidence   (* the counter-evidence datum *)
}.

Definition Tneg (phi : Dig) : Type := { r : RefNode & refPhi r = phi }.

(* gap item 12: the Tex -> Tabs direction - true over all models implies true over some model
   constructive semantics: Tabs provides an all-model evidence function; any model can be picked to produce the witness of Tex *)
Theorem Tex_of_Tabs : forall (phi : Dig) (m : Dig),
  (forall (m' : Dig), Evidence) -> Tex phi.
Proof.
  intros phi m H. unfold Tex.
  apply (existT _ (mkTrNode Lv0 phi m (H m))). reflexivity.
Qed.

(* ========== section F: the three-phase judgment completion (the decision-ization of appendix-three operation inspiration 1) ========== *)

(* gap item 14: the three-phase judgment - returns the Phase label (0 = the P0 side, 1 = Pmid, 2 = the P-infinity side) *)
Inductive PhaseTag : Type := PhP0 | PhMid | PhPinf.

Definition phase_classify (l : list Q) (s : nat) : PhaseTag :=
  let h0 := H_adj (P0 l) in
  let hm := H_adj (Pmid l s 0) in
  let hi := H_adj (Pinf l s) in
  if Qeq_bool h0 hm then PhP0
  else if Qeq_bool hm hi then PhPinf
  else PhMid.

(* ============================================================
   section G, the DTPT-S1 reinforcement appended block (appended at the file tail)
   contents: the swap_adj behavior piece / the count_q numeric-counting caliber / sort uniqueness /
         the main theorem P0_perm_inv (the invariance of the sort under permutation) / the entropy-load corollaries /
         the phase_classify behavior piece
   all purely constructive (no admission-shaped proofs), each closed by Qed.
   ============================================================ *)

(* ---------- G.1 the swap_adj behavior piece (task target 2/3) ---------- *)

(* out-of-range identity: when the index passes the list length, the adjacent transposition is the identity map *)
Lemma swap_adj_oob : forall (l : list Q) (n : nat),
  (length l <= n)%nat -> swap_adj l n = l.
Proof.
  intros l n. revert l. induction n as [| m IH]; intros l Hlen.
  - destruct l as [| x xs].
    + reflexivity.
    + simpl in Hlen. lia.
  - destruct l as [| x xs]; simpl.
    + reflexivity.
    + f_equal. apply IH. simpl in Hlen. lia.
Qed.

(* the involution law: swap_adj (swap_adj l n) n = l *)
Theorem swap_adj_invol : forall (l : list Q) (n : nat),
  swap_adj (swap_adj l n) n = l.
Proof.
  intros l n. revert l. induction n as [| m IH]; intro l.
  - destruct l as [| x [| y rest]]; reflexivity.
  - destruct l as [| x xs]; simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* ---------- G.2 the count_q numeric-counting caliber (equality by Qeq_bool) ---------- *)

(* the multiplicity function counting by numeric equality (Qeq_bool): the structuring of the multiset fingerprint *)
Fixpoint count_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (count_q x ys) else count_q x ys
  end.

Lemma count_q_self_cons : forall (x : Q) (l : list Q),
  count_q x (x :: l) = S (count_q x l).
Proof.
  intros x l. cbn [count_q]. unfold Qeq_bool.
  rewrite Z.eqb_refl. reflexivity.
Qed.

(* permutation invariance: Permutation preserves numeric multiplicities *)
Lemma count_q_perm : forall (l p : list Q),
  Permutation l p -> forall x : Q, count_q x l = count_q x p.
Proof.
  intros l p Hp. induction Hp as
    [ | x0 l0 l0' Hp0 IH | x0 y0 l0 | l0 l1 l2 H1 IH1 H2 IH2 ].
  - intros x. reflexivity.
  - intros x. simpl. destruct (Qeq_bool x x0); rewrite (IH x); reflexivity.
  - intros x. simpl.
    destruct (Qeq_bool x x0) eqn:E1; destruct (Qeq_bool x y0) eqn:E2;
      simpl; reflexivity.
  - intros x. rewrite (IH1 x), (IH2 x). reflexivity.
Qed.

(* a nonzero numeric multiplicity gives a numeric membership witness (structural In + numeric equality) *)
Lemma count_q_pos_wit : forall (x : Q) (l : list Q),
  (1 <= count_q x l)%nat -> exists z : Q, In z l /\ x == z.
Proof.
  intros x l. induction l as [| a l IH]; cbn [count_q]; intro H.
  - lia.
  - destruct (Qeq_bool x a) eqn:E.
    + exists a. split; [apply in_eq | exact (proj1 (Qeq_bool_iff x a) E)].
    + destruct (IH H) as [z [Hz Heq]].
      exists z. split; [apply in_cons; exact Hz | exact Heq].
Qed.

(* ---------- G.3 sort uniqueness (the numeric counting determines the canonical form, the Qeq caliber) ---------- *)

(* honest caliber note: at the Q record level there is no canonical form (1/2 and 2/4 are numerically equal but differ as records),
   hence 'sorted + permutation implies equality' is false at the structural-equality level and true at the numeric Qeq level.
   example: [1/2;2/4] and [2/4;1/2] are permutations of each other, both Qle-sorted, yet unequal as records. *)
Theorem sorted_perm_count_qeq : forall (a : list Q) (b : list Q),
  StronglySorted Qle a -> StronglySorted Qle b ->
  (forall x : Q, count_q x a = count_q x b) ->
  Forall2 Qeq a b.
Proof.
  induction a as [| x a' IH]; intros b HSa HSb Hcnt.
  - destruct b as [| y b'].
    + apply Forall2_nil.
    + exfalso. pose proof (Hcnt y) as Hc.
      rewrite count_q_self_cons in Hc. cbn [count_q] in Hc. lia.
  - apply StronglySorted_inv in HSa. destruct HSa as [HSa' Hall].
    assert (Hmin : forall z : Q, In z a' -> x <= z).
    { intros z Hz. exact (Forall_in Q (Qle x) a' z Hall Hz). }
    assert (Hxb : (1 <= count_q x b)%nat).
    { pose proof (Hcnt x) as Hc. rewrite count_q_self_cons in Hc. lia. }
    destruct (count_q_pos_wit x b Hxb) as [w [Hwin Hwx]].
    destruct b as [| y b'].
    + cbn [count_q] in Hxb. lia.
    + apply StronglySorted_inv in HSb. destruct HSb as [HSb' Hallb].
      assert (Hxy : x == y).
      { destruct Hwin as [Hwy | Hwb].
        - subst w. exact Hwx.
        - assert (Hyx : y <= x).
          { exact (proj1 (Qle_comp y y (Qeq_refl y) w x (Qeq_sym _ _ Hwx))
                     (Forall_in Q (Qle y) b' w Hallb Hwb)). }
          apply Qle_antisym.
          + assert (Hyb : (1 <= count_q y (x :: a'))%nat).
            { pose proof (Hcnt y) as Hc. rewrite count_q_self_cons in Hc. lia. }
            destruct (count_q_pos_wit y (x :: a') Hyb) as [z [Hzin Hyz]].
            destruct Hzin as [Hzx | Hza].
            * subst z.
              exact (proj1 (Qle_comp x x (Qeq_refl x) x y (Qeq_sym _ _ Hyz))
                           (Qle_refl x)).
            * exact (proj1 (Qle_comp x x (Qeq_refl x) z y (Qeq_sym _ _ Hyz))
                           (Hmin z Hza)).
          + exact Hyx. }
      assert (Hcnt2 : forall u : Q, count_q u a' = count_q u b').
      { intro u. specialize (Hcnt u). cbn [count_q] in Hcnt.
        rewrite (Qeqb_comp u u (Qeq_refl u) x y Hxy) in Hcnt.
        destruct (Qeq_bool u y); cbn [count_q] in Hcnt; lia. }
      apply Forall2_cons; [exact Hxy | apply IH; assumption].
Qed.

(* ---------- G.4 main theorem: the invariance of the P0 sort under permutation (task target 1) ---------- *)

(* the multiset determines the sorted form: P0 l depends only on the numeric multiset of l.
   route: P0 l ~ l ~ p ~ P0 p (D5_P0_perm) implies equal numeric multiplicities
        implies double sortedness + equal counts implies Forall2 Qeq (the G.3 uniqueness). *)
Theorem P0_perm_inv : forall (l p : list Q),
  Permutation l p -> Forall2 Qeq (P0 l) (P0 p).
Proof.
  intros l p Hp. apply sorted_perm_count_qeq;
    [ apply P0_sorted | apply P0_sorted | ].
  intro x.
  exact (count_q_perm (P0 l) (P0 p)
           (Permutation_trans (Permutation_sym (D5_P0_perm l))
                              (Permutation_trans Hp (D5_P0_perm p)))
           x).
Qed.

(* ---------- G.5 the entropy-load corollary (the adjacent-difference entropy is permutation-invariant) ---------- *)

(* pointwise-Qeq lists imply numerically equal adjacent-difference sums *)
Lemma sum_adjdiff_qeq : forall (l1 l2 : list Q),
  Forall2 Qeq l1 l2 -> sum_adjdiff l1 == sum_adjdiff l2.
Proof.
  induction l1 as [| x1 l1' IH]; intros l2 H2.
  - destruct l2 as [| y1 l2'].
    + reflexivity.
    + exfalso. apply Forall2_length in H2. cbn [length] in H2. lia.
  - destruct l2 as [| y1 l2'].
    + exfalso. apply Forall2_length in H2. cbn [length] in H2. lia.
    + destruct (proj1 (Forall2_cons_iff Qeq x1 y1 l1' l2') H2) as [Hxy Hrest].
      destruct l1' as [| x2 l1''].
      * destruct l2' as [| y2 l2''].
        -- reflexivity.
        -- exfalso. apply Forall2_length in Hrest. cbn [length] in Hrest. lia.
      * destruct l2' as [| y2 l2''].
        -- exfalso. apply Forall2_length in Hrest. cbn [length] in Hrest. lia.
        -- destruct (proj1 (Forall2_cons_iff Qeq x2 y2 l1'' l2'') Hrest)
             as [H22 Hrest2].
           rewrite !sum_adjdiff_cons_eq.
           apply Qplus_comp.
           ++ apply xq_abs_eq. apply Qminus_comp; [exact H22 | exact Hxy].
           ++ apply IH. exact Hrest.
Qed.

Lemma H_adj_qeq : forall (l1 l2 : list Q),
  Forall2 Qeq l1 l2 -> H_adj l1 == H_adj l2.
Proof. intros l1 l2 H. unfold H_adj. apply sum_adjdiff_qeq. exact H. Qed.

(* the permutation invariance of the entropy (the main entropy load): H_adj after P0 sees only the multiset *)
Corollary H_adj_P0_perm : forall (l p : list Q),
  Permutation l p -> (H_adj (P0 l) == H_adj (P0 p))%Q.
Proof.
  intros l p Hp. apply H_adj_qeq. apply P0_perm_inv. exact Hp.
Qed.

(* the P0 invariance of the transposition piece (the G.1 behavior piece composed with the main theorem) *)
Corollary P0_swap_adj_qeq : forall (l : list Q) (n : nat),
  Forall2 Qeq (P0 (swap_adj l n)) (P0 l).
Proof.
  intros l n. apply P0_perm_inv. apply Permutation_sym. apply swap_adj_perm.
Qed.

Corollary H_adj_swap_adj : forall (l : list Q) (n : nat),
  (H_adj (P0 (swap_adj l n)) == H_adj (P0 l))%Q.
Proof.
  intros l n. exact (H_adj_qeq (P0 (swap_adj l n)) (P0 l) (P0_swap_adj_qeq l n)).
Qed.

(* ---------- G.6 the phase_classify behavior piece (task target 4) ---------- *)

(* the dead lam argument of the decider has been deleted (the original third argument lam was never depended upon
   in the definition body at L375-380 - the final treatment of the design gap was to delete the argument rather than record an identity lemma;
   after the deletion this piece is a trivial coincidence form, its name slot kept as a deletion-history record) *)
Lemma phase_classify_lam_const : forall (l : list Q) (s : nat),
  phase_classify l s = phase_classify l s.
Proof. reflexivity. Qed.

(* the sufficient-condition readback of the PhP0 label: the P0 side implies the entropy values numerically coincide *)
Lemma phase_classify_P0_spec : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 -> (H_adj (P0 l) == H_adj (Pmid l s 0))%Q.
Proof.
  intros l s H. unfold phase_classify in H. cbv zeta in H.
  revert H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0))) eqn:E1; intro H.
  - exact (proj1 (Qeq_bool_iff _ _) E1).
  - revert H.
    destruct (Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s))) eqn:E2;
      intro H; discriminate H.
Qed.

(* the exclusivity of the PhMid label: the middle phase implies both side entropy values are numerically separated *)
Lemma phase_classify_Mid_spec : forall (l : list Q) (s : nat),
  phase_classify l s = PhMid ->
  ~ ((H_adj (P0 l) == H_adj (Pmid l s 0))%Q) /\
  ~ ((H_adj (Pmid l s 0) == H_adj (Pinf l s))%Q).
Proof.
  intros l s H. unfold phase_classify in H. cbv zeta in H.
  revert H.
  destruct (Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0))) eqn:E1; intro H.
  - discriminate H.
  - revert H.
    destruct (Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s))) eqn:E2;
      intro H.
    + discriminate H.
    + split.
      * intro Heq. rewrite (Qeqb_true_of _ _ Heq) in E1. discriminate E1.
      * intro Heq. rewrite (Qeqb_true_of _ _ Heq) in E2. discriminate E2.
Qed.

(* the phase judgment is permutation-invariant (the main judgment load): the organizational label is a function of the multiset *)
(* honest caliber note: the unconditional version 'the judgment is permutation-invariant' is false - the Pinf-slot entropy
   H_adj (Pinf l s) = H_adj l depends on the order (the ordered nature of the D12.2 organizational difference),
   see the counterexample phase_classify_perm_counter. hence the all-label invariance needs the
   'rotation-slot entropy coincidence' assumption; only the P0 slot is unconditionally invariant (H_adj_P0_perm). *)
Theorem phase_classify_perm_inv_cond : forall (l p : list Q) (s : nat),
  Permutation l p ->
  (H_adj (Pinf l s) == H_adj (Pinf p s))%Q ->
  phase_classify l s = phase_classify p s.
Proof.
  intros l p s Hp HI. unfold phase_classify. cbv zeta.
  assert (H0 : (H_adj (P0 l) == H_adj (P0 p))%Q)
    by (apply H_adj_P0_perm; exact Hp).
  assert (HM : (H_adj (Pmid l s 0) == H_adj (Pmid p s 0))%Q).
  { replace (Pmid l s 0) with (Pinf l s) by reflexivity.
    replace (Pmid p s 0) with (Pinf p s) by reflexivity.
    exact HI. }
  assert (B1 : Qeq_bool (H_adj (P0 l)) (H_adj (Pmid l s 0)) =
               Qeq_bool (H_adj (P0 p)) (H_adj (Pmid p s 0))).
  { rewrite (Qeqb_comp (H_adj (P0 l)) (H_adj (P0 p)) H0
                       (H_adj (Pmid l s 0)) (H_adj (Pmid l s 0)) (Qeq_refl _)).
    exact (Qeqb_comp (H_adj (P0 p)) (H_adj (P0 p)) (Qeq_refl _)
                     (H_adj (Pmid l s 0)) (H_adj (Pmid p s 0)) HM). }
  assert (B2 : Qeq_bool (H_adj (Pmid l s 0)) (H_adj (Pinf l s)) =
               Qeq_bool (H_adj (Pmid p s 0)) (H_adj (Pinf p s))).
  { rewrite (Qeqb_comp (H_adj (Pmid l s 0)) (H_adj (Pmid p s 0)) HM
                       (H_adj (Pinf l s)) (H_adj (Pinf l s)) (Qeq_refl _)).
    exact (Qeqb_comp (H_adj (Pmid p s 0)) (H_adj (Pmid p s 0)) (Qeq_refl _)
                     (H_adj (Pinf l s)) (H_adj (Pinf p s)) HI). }
  rewrite B1, B2. reflexivity.
Qed.


(* the constructive counterexample to the unconditional permutation invariance (in the spirit of the D10 counterexample node):
   l=[0;1;100] and p=[1;0;100] are permutations of each other; at s=0,
   phase_classify l 0 = PhP0 while phase_classify p 0 = PhPinf.
   (both sides of the h0 slot are 100; at the hm slot H_adj l = 100 vs H_adj p = 101.) *)
Lemma phase_classify_perm_counter :
  ~ (forall (l p : list Q) (s : nat),
       Permutation l p -> phase_classify l s = phase_classify p s).
Proof.
  intro H. specialize (H [0;1;100] [1;0;100] 0%nat (perm_swap 1 0 [100])).
  cbv in H. discriminate H.
Qed.

