(* ConstructiveWorld-Main - the N9 extremal-family stem of the DTPT base library *)

(** * DTPT_e: the N9 extremal-family stem of the DTPT base library (stem E of fourteen).

    Mission.  merged block M1, the N9 extremal family: perm3_cases (the six-form exhaustive case analysis of the length-3 permutation class), the extremal theorems over the witness list n9_l0 (n9_max/n9_max_attained/n9_min_is_sorted), the separation-ratio faces (n9_const_ratio/n9_separation_exact), and the naive general-length upper bounds.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d]

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
(* ============================================================
   merged block M1 (section 9): the merge of DTPT_N9Opt.v - the N9 extremal family
   source piece DTPT-U14R (the N9O separation-constant optimality). Only the standalone-file
   Require/Import/Open Scope headers (carried uniformly by this file's header),
   comments, all proof bodies, the Qed face and the Print Assumptions audit exits are zero-change migrations.
   ============================================================ *)
(* ============================================================
   DTPT_N9Opt.v - the N9O separation-constant optimality (the U14R continuation piece)
   base module: Require Import DTPT (stdlib QArith/List/Lia/Permutation)
   discipline: zero admission bodies; every theorem closes by Qed; statements fully general, numeric faces by direct computation.
   contents:
     [floor piece] perm3_cases          - the six-form exhaustive case analysis of the length-3 permutation class
     [main]   n9_max / n9_max_attained / n9_min_is_sorted
                               - the three universal theorems over the witness list n9_l0 = [0;1;2]
     [main piece]   n9_const_ratio / n9_separation_exact
                               - the separation ratio 3/2 exact, attained on both sides
     [bonus]   n9_naive_bound / n9_naive_bound_Hadj
                               - naive general-length upper bounds (the spread face and the H_adj face)
   numeric facts: the six H_adj forms = 2,3,3,3,3,2; max 3 = (3/2)*2, min 2.
   ============================================================ *)
(* the standalone-file Require/Import/Open Scope headers (From Stdlib QArith/List/Lia/Permutation,
   Require Import DTPT, Import ListNotations, Open Scope Q_scope) were removed at merge time. *)

(* ---------- the witness list and the spread face ---------- *)

Definition n9_l0 : list Q := [0; 1; 2].

Definition spread (l : list Q) : Q := lastq (P0 l) - hd 0 (P0 l).

(* ---------- head/tail-element control for sorted lists (the companion pieces of the spread face) ---------- *)

Lemma sorted_hd_le_in : forall (m : list Q) (x : Q),
  SortedQ m -> In x m -> (hd 0 m <= x)%Q.
Proof.
  intros m x HS. revert x.
  induction HS as [| y ys HSr _ HFall]; intros x Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst. apply Qle_refl.
    + rewrite Forall_forall in HFall. apply HFall. exact Hin.
Qed.

Lemma sorted_in_le_last : forall (m : list Q) (x : Q),
  SortedQ m -> In x m -> (x <= lastq m)%Q.
Proof.
  intros m x HS. revert x.
  induction HS as [| y ys HSr IH HFall]; intros x Hin.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst x. destruct ys as [| b bs].
      * simpl. apply Qle_refl.
      * change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
        rewrite Forall_forall in HFall.
        apply HFall. apply xq_lastq_In. discriminate.
    + destruct ys as [| b bs].
      * destruct Hin.
      * change (lastq (y :: b :: bs)) with (lastq (b :: bs)).
        apply IH. exact Hin.
Qed.

(* the pairwise spread bound: the Qabs distance of any two elements of the list never exceeds the spread *)
Lemma spread_pair_le : forall (l : list Q) (x y : Q),
  In x l -> In y l -> (Qabs (x - y) <= spread l)%Q.
Proof.
  intros l x y Hx Hy. unfold spread.
  assert (Hlne : l <> []) by (intro Hc; rewrite Hc in Hx; exact Hx).
  assert (HPne : P0 l <> []).
  { destruct l as [| a rest].
    - exfalso. apply Hlne. reflexivity.
    - apply xq_P0_cons_ne. }
  assert (HS : SortedQ (P0 l)) by apply xq_P0_sorted.
  assert (Hxl : In x (P0 l)) by
    (apply Permutation_in with (l := l); [ apply D5_P0_perm | exact Hx ]).
  assert (Hyl : In y (P0 l)) by
    (apply Permutation_in with (l := l); [ apply D5_P0_perm | exact Hy ]).
  assert (H1 : (hd 0 (P0 l) <= x)%Q) by (apply sorted_hd_le_in; assumption).
  assert (H2 : (x <= lastq (P0 l))%Q) by (apply sorted_in_le_last; assumption).
  assert (H3 : (hd 0 (P0 l) <= y)%Q) by (apply sorted_hd_le_in; assumption).
  assert (H4 : (y <= lastq (P0 l))%Q) by (apply sorted_in_le_last; assumption).
  destruct (Qle_dec' x y) as [Hxy | Hyx].
  - assert (Habs : Qabs (x - y) == y - x).
    { rewrite xq_abs_sub_comm. apply abs_eq.
      apply (proj1 (Qle_0_sub' x y)). exact Hxy. }
    rewrite Habs.
    apply (Qle_trans _ (lastq (P0 l) - x)).
    + apply qsub_le_r. exact H4.
    + unfold Qminus. apply qadd_le;
        [ apply Qle_refl | apply qopp_le; exact H1 ].
  - assert (Habs : Qabs (x - y) == x - y).
    { apply abs_eq. apply (proj1 (Qle_0_sub' y x)). exact Hyx. }
    rewrite Habs.
    apply (Qle_trans _ (lastq (P0 l) - y)).
    + apply qsub_le_r. exact H2.
    + unfold Qminus. apply qadd_le;
        [ apply Qle_refl | apply qopp_le; exact H3 ].
Qed.

(* ---------- the length-coefficient stepping identity (the S2 card recipe: prove by Z-level lia first, then rewrite) ---------- *)

Lemma qcoef_step : forall (n : nat) (k : Q),
  k + ((Z.of_nat n - 1)%Z # 1) * k == ((Z.of_nat (S n) - 1)%Z # 1) * k.
Proof.
  intros n k.
  assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz.
  destruct k as [kn kd].
  unfold Qeq, Qplus, Qminus, Qmult. cbn [Qnum Qden]. lia.
Qed.

(* the pointwise induction of the adjacent-difference sum over 'pairwise bound x (length - 1)' (with a nonempty guard) *)
Lemma H_adj_pair_bound : forall (m : list Q) (k : Q), m <> [] ->
  (forall x y, In x m -> In y m -> (Qabs (x - y) <= k)%Q) ->
  H_adj m <= ((Z.of_nat (length m) - 1)%Z # 1) * k.
Proof.
  intros m. induction m as [| a rest IH]; intros k Hne Hpair.
  - exfalso. apply Hne. reflexivity.
  - destruct rest as [| b rest2].
    + (* single element: H_adj = 0, the coefficient 1-1 = 0 *)
      change (H_adj [a]) with 0%Q.
      cbn [length].
      replace ((Z.of_nat 1 - 1)%Z # 1) with 0%Q by reflexivity.
      rewrite Qmult_0_l. apply Qle_refl.
    + (* several elements: |b-a| <= k added to the IH *)
      change (H_adj (a :: b :: rest2))
        with (Qabs (b - a) + H_adj (b :: rest2))%Q.
      assert (Hbp : (Qabs (b - a) <= k)%Q).
      { apply Hpair; [ right; left; reflexivity | left; reflexivity ]. }
      assert (IHr : H_adj (b :: rest2)
                    <= ((Z.of_nat (length (b :: rest2)) - 1)%Z # 1) * k).
      { apply IH; [ discriminate | ].
        intros x y Hx Hy. apply Hpair.
        - destruct Hx as [Hx | Hx].
          + subst x. right; left; reflexivity.
          + right; right; exact Hx.
        - destruct Hy as [Hy | Hy].
          + subst y. right; left; reflexivity.
          + right; right; exact Hy. }
      assert (Hq : k + ((Z.of_nat (length (b :: rest2)) - 1)%Z # 1) * k
                   == ((Z.of_nat (length (a :: b :: rest2)) - 1)%Z # 1) * k).
      { change (length (b :: rest2)) with (S (length rest2)).
        change (length (a :: b :: rest2)) with (S (S (length rest2))).
        apply qcoef_step. }
      rewrite <- Hq.
      apply qadd_le; [ exact Hbp | exact IHr ].
Qed.

(* ========== [floor piece] the six-form exhaustive case analysis of the length-3 permutation class ========== *)

Lemma perm3_cases : forall (a b c : Q) (p : list Q),
  Permutation [a; b; c] p ->
  p = [a; b; c] \/ p = [a; c; b] \/ p = [b; a; c] \/
  p = [b; c; a] \/ p = [c; a; b] \/ p = [c; b; a].
Proof.
  intros a b c p Hp.
  assert (Hlen : length p = 3%nat).
  { pose proof (Permutation_length Hp) as HL. simpl in HL. lia. }
  destruct p as [| x1 [| x2 [| x3 [| x4 p4]]]].
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - simpl in Hlen. discriminate.
  - (* p = [x1;x2;x3]: resolved by element-wise membership transport *)
    assert (Hin1 : In x1 [a; b; c]).
    { apply Permutation_in with (l := [x1; x2; x3]).
      - apply Permutation_sym. exact Hp.
      - left; reflexivity. }
    simpl in Hin1.
    destruct Hin1 as [E1 | [E1 | [E1 | []]]]; subst x1.
    + (* x1 = a *)
      assert (Hp1 : Permutation [b; c] [x2; x3])
        by exact (Permutation_cons_inv Hp).
      assert (Hin2 : In x2 [b; c]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [c] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [c]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. left; reflexivity.
      * assert (Hp2 : Permutation [b] [x3]).
        { apply (Permutation_cons_inv (a := c)).
          eapply perm_trans with (l' := [b; c]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [b]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. right; left; reflexivity.
    + (* x1 = b *)
      assert (Hp1 : Permutation [a; c] [x2; x3]).
      { apply (Permutation_cons_inv (a := b)).
        eapply perm_trans with (l' := [a; b; c]).
        - apply Permutation_sym. apply perm_swap.
        - exact Hp. }
      assert (Hin2 : In x2 [a; c]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [c] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [c]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3. right; right; left; reflexivity.
      * assert (Hp2 : Permutation [a] [x3]).
        { apply (Permutation_cons_inv (a := c)).
          eapply perm_trans with (l' := [a; c]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [a]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; left; reflexivity.
    + (* x1 = c *)
      assert (Hp1 : Permutation [a; b] [x2; x3]).
      { apply (Permutation_cons_inv (a := c)).
        eapply perm_trans with (l' := [a; b; c]).
        - etransitivity.
          + apply perm_swap.
          + apply perm_skip. apply perm_swap.
        - exact Hp. }
      assert (Hin2 : In x2 [a; b]).
      { apply Permutation_in with (l := [x2; x3]).
        - apply Permutation_sym. exact Hp1.
        - left; reflexivity. }
      simpl in Hin2. destruct Hin2 as [E2 | [E2 | []]]; subst x2.
      * assert (Hp2 : Permutation [b] [x3])
          by exact (Permutation_cons_inv Hp1).
        assert (Hin3 : In x3 [b]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; right; left; reflexivity.
      * assert (Hp2 : Permutation [a] [x3]).
        { apply (Permutation_cons_inv (a := b)).
          eapply perm_trans with (l' := [a; b]).
          - apply Permutation_sym. apply perm_swap.
          - exact Hp1. }
        assert (Hin3 : In x3 [a]).
        { apply Permutation_in with (l := [x3]).
          - apply Permutation_sym. exact Hp2.
          - left; reflexivity. }
        simpl in Hin3. destruct Hin3 as [E3 | []]; subst x3.
        right; right; right; right; right; reflexivity.
  - (* length >= 4: contradicts 3 *)
    simpl in Hlen. lia.
Qed.

(* ========== [main] the three extremal theorems over the witness list n9_l0 = [0;1;2] ==========
   numeric facts: the six H_adj forms = 2,3,3,3,3,2, max 3, min 2. ========== *)

Theorem n9_max : forall p, Permutation n9_l0 p -> H_adj p <= 3.
Proof.
  intros p Hp. unfold n9_l0 in Hp. apply perm3_cases in Hp.
  destruct Hp as [E | [E | [E | [E | [E | E]]]]]; subst p;
    apply xq_Qle_bool_le; reflexivity.
Qed.

Theorem n9_max_attained : exists p, Permutation n9_l0 p /\ H_adj p == 3.
Proof.
  exists [0; 2; 1]. split.
  - unfold n9_l0. apply perm_skip. apply perm_swap.
  - reflexivity.
Qed.

Theorem n9_min_is_sorted : forall p, Permutation n9_l0 p -> 2 <= H_adj p.
Proof.
  intros p Hp. unfold n9_l0 in Hp. apply perm3_cases in Hp.
  destruct Hp as [E | [E | [E | [E | [E | E]]]]]; subst p;
    apply xq_Qle_bool_le; reflexivity.
Qed.

(* ========== [main piece] the separation ratio 3/2 exact (attained on both sides) ========== *)

Theorem n9_const_ratio :
  (3 # 2)%Q * 2 == 3 /\
  (exists pmax : list Q, Permutation n9_l0 pmax /\ H_adj pmax == 3) /\
  (exists pmin : list Q, Permutation n9_l0 pmin /\ H_adj pmin == 2).
Proof.
  split; [| split].
  - reflexivity.
  - exists [0; 2; 1]. split.
    + unfold n9_l0. apply perm_skip. apply perm_swap.
    + reflexivity.
  - exists [0; 1; 2]. split.
    + unfold n9_l0. apply Permutation_refl.
    + reflexivity.
Qed.

(* the class-wide form: the H_adj of any permutation is sandwiched between [(3#2)*2 lower face, (3#2)*2 upper face] *)
Theorem n9_separation_exact : forall p, Permutation n9_l0 p ->
  H_adj p <= (3 # 2)%Q * 2 /\ (3 # 2)%Q * 2 <= (3 # 2)%Q * H_adj p.
Proof.
  intros p Hp.
  assert (I : (3 # 2)%Q * 2 == 3) by reflexivity.
  split.
  - rewrite I. apply n9_max. exact Hp.
  - rewrite (Qmult_comm (3 # 2)%Q 2). rewrite (Qmult_comm (3 # 2)%Q (H_adj p)).
    apply qmul_le_r.
    + apply n9_min_is_sorted. exact Hp.
    + apply xq_Qle_bool_le. reflexivity.
Qed.

(* ========== [bonus] the naive general-length upper bound ========== *)

(* the spread face: H_adj p <= (n-1) * spread l *)
Theorem n9_naive_bound : forall (l p : list Q), Permutation l p -> p <> [] ->
  H_adj p <= ((Z.of_nat (length l) - 1)%Z # 1) * spread l.
Proof.
  intros l p Hp Hne.
  pose proof (Permutation_length Hp) as HL.
  rewrite HL.
  apply H_adj_pair_bound; [ exact Hne | ].
  intros x y Hx Hy.
  assert (Hxl : In x l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hx ]).
  assert (Hyl : In y l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hy ]).
  apply spread_pair_le; assumption.
Qed.

(* the H_adj face (the original route: pointwise via xq_pair_dist_le) *)
Theorem n9_naive_bound_Hadj : forall (l p : list Q), Permutation l p -> p <> [] ->
  H_adj p <= ((Z.of_nat (length l) - 1)%Z # 1) * H_adj l.
Proof.
  intros l p Hp Hne.
  pose proof (Permutation_length Hp) as HL.
  rewrite HL.
  apply H_adj_pair_bound; [ exact Hne | ].
  intros x y Hx Hy.
  assert (Hxl : In x l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hx ]).
  assert (Hyl : In y l) by
    (apply Permutation_in with (l := p);
       [ apply Permutation_sym; exact Hp | exact Hy ]).
  apply (xq_pair_dist_le l); assumption.
Qed.

(* ---------- audit exit ---------- *)

Print Assumptions perm3_cases.
Print Assumptions n9_max.
Print Assumptions n9_max_attained.
Print Assumptions n9_min_is_sorted.
Print Assumptions n9_const_ratio.
Print Assumptions n9_separation_exact.
Print Assumptions n9_naive_bound.
Print Assumptions n9_naive_bound_Hadj.

