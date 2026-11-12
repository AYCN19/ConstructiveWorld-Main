(* ConstructiveWorld-Main - the membership-and-dedup stem of the DTPT base library *)

(** * DTPT_b: the membership-and-dedup stem of the DTPT base library (stem B of fourteen).

    Mission.  the N9_ms_perm_inv infrastructure: the Qeq-membership family (Qmem), the Qnodup dedup characterization, remove_one, same_set_length, the permutation-invariance theorem N9_ms_perm_inv, and the separating witness N9_seq_separates.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a]

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
(* ========== supplementary block B2: the N9_ms_perm_inv infrastructure (Qeq membership + dedup characterization) ========== *)

Definition Qmem (a : Q) (l : list Q) : Prop :=
  existsb (fun y => Qeq_bool a y) l = true.

Lemma Qmem_cons : forall a x (l : list Q),
  Qmem a (x :: l) <-> (Qeq_bool a x = true \/ Qmem a l).
Proof.
  intros a x l. unfold Qmem. simpl. rewrite orb_true_iff. reflexivity.
Qed.

Lemma Qmem_refl_cons : forall x (l : list Q), Qmem x (x :: l).
Proof. intros x l. rewrite Qmem_cons. left. apply Qeq_bool_refl. Qed.

Lemma Qmem_weaken : forall a b (l : list Q),
  Qmem a l -> Qeq_bool a b = true -> Qmem b l.
Proof.
  intros a b l H Hab. unfold Qmem in H. apply existsb_exists in H.
  destruct H as [w [Hw Hq]].
  unfold Qmem. apply existsb_exists. exists w. split; [exact Hw|].
  apply (Qeqb_trans b a w). rewrite (Qeqb_sym b a). exact Hab. exact Hq.
Qed.

Lemma Qmem_dedup_aux_keep : forall a x (l : list Q),
  Qmem a (dedup_aux x l) -> Qmem a l.
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H. discriminate.
  - intros H. destruct (Qeq_bool x y).
    + rewrite Qmem_cons. right. exact (IH H).
    + rewrite Qmem_cons in H. destruct H as [H|H].
      * rewrite Qmem_cons. left. exact H.
      * rewrite Qmem_cons. right. exact (IH H).
Qed.

Lemma Qmem_dedup_aux_drop : forall a x (l : list Q),
  Qmem a l -> Qeq_bool a x = false -> Qmem a (dedup_aux x l).
Proof.
  intros a x l. induction l as [| y ys IH]; simpl.
  - intros H _. discriminate.
  - intros H Hax. rewrite Qmem_cons in H.
    destruct (Qeq_bool x y) eqn:Hxy.
    + destruct H as [H|H].
      * exfalso.
        assert (Hya : Qeq_bool y a = true) by (rewrite (Qeqb_sym y a); exact H).
        assert (Hxa : Qeq_bool x a = true) by (apply (Qeqb_trans x y a); assumption).
        rewrite (Qeqb_sym x a) in Hxa. rewrite Hxa in Hax. discriminate.
      * exact (IH H Hax).
    + rewrite Qmem_cons. destruct H as [H|H].
      * left. exact H.
      * right. exact (IH H Hax).
Qed.

Lemma dedup_aux_duck : forall a (l : list Q),
  Qmem a (dedup_aux a l) -> False.
Proof.
  intros a l. induction l as [| y ys IH]; simpl.
  - discriminate.
  - destruct (Qeq_bool a y) eqn:E.
    + apply IH.
    + rewrite Qmem_cons. intros [H|H].
      * rewrite E in H. discriminate.
      * apply IH. exact H.
Qed.

Fixpoint Qnodup (l : list Q) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~ Qmem x xs /\ Qnodup xs
  end.

Lemma dedup_aux_Qnodup : forall x (l : list Q), Qnodup l -> Qnodup (dedup_aux x l).
Proof.
  intros x l. induction l as [| y ys IH]; simpl; [intros _; exact I |].
  - intros [Hny Hys]. destruct (Qeq_bool x y).
    + apply IH. exact Hys.
    + split.
      * intros Hm. apply Hny. exact (Qmem_dedup_aux_keep y x _ Hm).
      * apply IH. exact Hys.
Qed.

Lemma dedup_Qnodup : forall l : list Q, Qnodup (dedup l).
Proof.
  induction l as [| x xs IH]; simpl.
  - exact I.
  - split.
    + intros Hm. exfalso. exact (dedup_aux_duck x (dedup xs) Hm).
    + apply dedup_aux_Qnodup. exact IH.
Qed.

Lemma dedup_Qmem_l : forall (l : list Q) a, Qmem a (dedup l) -> Qmem a l.
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - discriminate.
  - rewrite Qmem_cons. intros [H|H].
    + rewrite Qmem_cons. left. exact H.
    + rewrite Qmem_cons. right. apply IH.
      exact (Qmem_dedup_aux_keep a x _ H).
Qed.

Lemma dedup_Qmem_r : forall (l : list Q) a, Qmem a l -> Qmem a (dedup l).
Proof.
  induction l as [| x xs IH]; intros a; simpl.
  - discriminate.
  - intros H. rewrite Qmem_cons. rewrite Qmem_cons in H.
    destruct H as [H|H].
    + left. exact H.
    + destruct (Qeq_bool a x) eqn:Hax.
      * left. reflexivity.
      * right. apply Qmem_dedup_aux_drop.
        -- apply IH. exact H.
        -- exact Hax.
Qed.

Lemma Qmem_perm : forall (l p : list Q) a, Permutation l p -> Qmem a l <-> Qmem a p.
Proof.
  intros l p a Hp. unfold Qmem. rewrite !existsb_exists. split; intros [y [Hy Hq]].
  - exists y. split; [apply (Permutation_in _ Hp); exact Hy | exact Hq].
  - exists y. split; [apply (Permutation_in _ (Permutation_sym Hp)); exact Hy | exact Hq].
Qed.

Lemma Qmem_cons_nodup : forall a x (xs : list Q),
  ~ Qmem x xs -> (Qmem a xs <-> (Qmem a (x :: xs) /\ Qeq_bool a x = false)).
Proof.
  intros a x xs Hx. split.
  - intros Ha. split.
    + rewrite Qmem_cons. right. exact Ha.
    + destruct (Qeq_bool a x) eqn:E.
      * exfalso. apply Hx. exact (Qmem_weaken a x xs Ha E).
      * reflexivity.
  - intros [Ha Hax]. rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
    + exfalso. rewrite Ha in Hax. discriminate.
    + exact Ha.
Qed.

Lemma remove_one : forall (x : Q) (n : list Q), Qnodup n -> Qmem x n ->
  exists n' : list Q, length n = S (length n') /\ Qnodup n'
    /\ (forall a, Qmem a n' <-> (Qmem a n /\ Qeq_bool a x = false)).
Proof.
  intros x n. induction n as [| y ys IH]; intros Hn Hx.
  - exfalso. unfold Qmem in Hx. simpl in Hx. discriminate.
  - destruct Hn as [Hy Hys]. rewrite Qmem_cons in Hx. destruct Hx as [Hxy|Hx].
    + (* x ~ y: remove the head y *)
      exists ys. split; [reflexivity | split].
      * exact Hys.
      * intros a. split.
        -- intros Ha. split.
           ++ rewrite Qmem_cons. right. exact Ha.
           ++ destruct (Qeq_bool a x) eqn:E.
              ** exfalso.
                 assert (Hya : Qeq_bool y a = true)
                   by (apply (Qeqb_trans y x a);
                       [rewrite <- (Qeqb_sym x y); exact Hxy | rewrite <- (Qeqb_sym a x); exact E]).
                 rewrite (Qeqb_sym y a) in Hya. apply Hy. exact (Qmem_weaken a y ys Ha Hya).
              ** reflexivity.
        -- intros [Ha Hax]. rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
           ++ exfalso.
              assert (Hay : Qeq_bool a x = true)
                by (apply (Qeqb_trans a y x); [exact Ha | rewrite <- (Qeqb_sym x y); exact Hxy]).
              rewrite Hay in Hax. discriminate.
           ++ exact Ha.
    + (* x is a Q-member of ys: recursive removal inside, n' := y :: ys' *)
      destruct (IH Hys Hx) as [ys' [Hlen [Hnd Hiff]]].
      exists (y :: ys'). split; [simpl; rewrite Hlen; reflexivity | split].
      * split.
        -- intros Hm. exfalso. exact (Hy (proj1 (proj1 (Hiff y) Hm))).
        -- exact Hnd.
      * intros a. split.
        -- intros Ha. rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
           ++ split.
              ** rewrite Qmem_cons. left. exact Ha.
              ** destruct (Qeq_bool a x) eqn:E.
                 *** exfalso.
                     assert (Hxa : Qeq_bool x a = true)
                       by (rewrite <- (Qeqb_sym a x); exact E).
                     assert (Hxy' : Qeq_bool x y = true)
                       by (apply (Qeqb_trans x a y); [exact Hxa | exact Ha]).
                     apply Hy. exact (Qmem_weaken x y ys Hx Hxy').
                 *** reflexivity.
           ++ split.
              ** rewrite Qmem_cons. right. exact (proj1 (proj1 (Hiff a) Ha)).
              ** exact (proj2 (proj1 (Hiff a) Ha)).
        -- intros [Ha Hax].
           ++ destruct (Qeq_bool a y) eqn:Hbay.
              ** rewrite Qmem_cons. left. exact Hbay.
              ** rewrite Qmem_cons. right.
                 rewrite Qmem_cons in Ha. destruct Ha as [Ha|Ha].
                 { exfalso. rewrite Ha in Hbay. discriminate. }
                 { exact (proj2 (Hiff a) (conj Ha Hax)). }
Qed.

Lemma same_set_length : forall m n : list Q,
  Qnodup m -> Qnodup n -> (forall a, Qmem a m <-> Qmem a n) -> length m = length n.
Proof.
  induction m as [| x xs IH]; intros n Hm Hn Heq.
  - destruct n as [| y ys]; [reflexivity | exfalso].
    pose proof (proj2 (Heq y) (Qmem_refl_cons y ys)) as Hb.
    unfold Qmem in Hb. simpl in Hb. discriminate.
  - destruct n as [| y ys].
    + exfalso.
      pose proof (proj1 (Heq x) (Qmem_refl_cons x xs)) as Hb.
      unfold Qmem in Hb. simpl in Hb. discriminate.
    + assert (Hxs : Qmem x (y :: ys))
        by (apply (proj1 (Heq x)); apply Qmem_refl_cons).
      destruct (remove_one x (y :: ys) Hn Hxs)
        as [n' [Hlen1 [Hnd1 Hiff1]]].
      assert (Hss : forall a, Qmem a xs <-> Qmem a n').
      { intros a. split; intros Ha.
        - assert (Hpair := proj1 (Qmem_cons_nodup a x xs (proj1 Hm)) Ha).
          apply (proj2 (Hiff1 a)). split.
          + exact (proj1 (Heq a) (proj1 Hpair)).
          + exact (proj2 Hpair).
        - assert (Hpair := proj1 (Hiff1 a) Ha).
          apply (proj2 (Qmem_cons_nodup a x xs (proj1 Hm))).
          split.
          + exact (proj2 (Heq a) (proj1 Hpair)).
          + exact (proj2 Hpair). }
      assert (Hlen2 : length xs = length n')
        by (apply IH; [apply (proj2 Hm) | exact Hnd1 | exact Hss]).
      simpl. rewrite Hlen2. rewrite <- Hlen1. simpl. reflexivity.
Qed.

Theorem N9_ms_perm_inv : forall (l p : list Q),
  Permutation l p -> H_ms l = H_ms p.
Proof.
  intros l p Hp. unfold H_ms. f_equal. f_equal.
  apply same_set_length.
  - apply dedup_Qnodup.
  - apply dedup_Qnodup.
  - intros a. split; intros H.
    + apply dedup_Qmem_r.
      apply (proj1 (Qmem_perm l p a Hp)). apply dedup_Qmem_l. exact H.
    + apply dedup_Qmem_r.
      apply (proj2 (Qmem_perm l p a Hp)). apply dedup_Qmem_l. exact H.
Qed.

Theorem N9_seq_separates : exists (l1 l2 : list Q),
  Permutation l1 l2 /\ H_adj l1 <> H_adj l2.
Proof.
  exists [0; 1; 2], [0; 2; 1]. split.
  - apply perm_skip. apply perm_swap.
  - intro Hc. cbv in Hc. discriminate.
Qed.

