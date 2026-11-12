(* ConstructiveWorld-Main - the frequency-measure stem of the DTPT base library *)

(** * DTPT_h: the frequency-measure stem of the DTPT base library (stem H of fourteen).

    Mission.  merged block S1, the frequency measure layer: the freq function and its concat additivity, permutation invariance, frequency mass conservation, the uniform measure, and the total-mass-one theorem.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f], [DTPT_g]

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
(* ============================================================
   merged block S1 (section 12): the merge of DTPT_Measure.v - the frequency measure layer
   source piece DTPT-S5 (freq frequencies / freq_perm permutation invariance / sumf, Sigma_freq mass
   conservation sum_freq_dedup / mu uniform measure, mu_total_mass total mass one).
   Only the standalone-file Require/Import/Open Scope headers and Module shell lines
   were peeled off (carried uniformly by this file's header); comments, all proof bodies and the Qed face are zero-change verbatim migrations.
   ============================================================ *)

(* ========== section 1: the frequency function ========== *)

(* freq l x: the number of occurrences of element x (equality by Qeq_bool) in the list l.
   it takes values in nat; nonnegativity holds trivially and needs no proof. *)
Fixpoint freq (l : list Q) (x : Q) : nat :=
  match l with
  | [] => O
  | y :: ys => if Qeq_bool y x then Datatypes.S (freq ys x) else freq ys x
  end.

Lemma freq_nonneg : forall (l : list Q) (x : Q), (0 <= freq l x)%nat.
Proof. intros l x. lia. Qed.

(* concatenation additivity: frequencies add linearly along the list decomposition *)
Lemma freq_app : forall (l p : list Q) (x : Q),
  freq (l ++ p) x = (freq l x + freq p x)%nat.
Proof.
  induction l as [| y ys IH]; intros p x; simpl.
  - reflexivity.
  - destruct (Qeq_bool y x); rewrite IH; reflexivity.
Qed.

(* the congruence of frequencies over Qeq-equal elements: renaming under equality does not change the frequency *)
Lemma freq_eq_congr : forall (x y : Q) (l : list Q),
  x == y -> freq l x = freq l y.
Proof.
  intros x y l Hxy. induction l as [| a l IH]; simpl.
  - reflexivity.
  - destruct (Qeq_bool a x) eqn:Ex; destruct (Qeq_bool a y) eqn:Ey.
    + f_equal. exact IH.
    + exfalso.
      assert (Hay : Qeq_bool a y = true).
      { apply (Qeqb_trans a x y);
          [exact Ex | apply Qeqb_true_of; exact Hxy]. }
      rewrite Hay in Ey. discriminate.
    + exfalso.
      assert (Hyx : Qeq_bool y x = true)
        by (rewrite (Qeqb_sym y x); apply Qeqb_true_of; exact Hxy).
      assert (Hax : Qeq_bool a x = true)
        by (apply (Qeqb_trans a y x); [exact Ey | exact Hyx]).
      rewrite Hax in Ex. discriminate.
    + exact IH.
Qed.

(* non-membership gives a zero frequency *)
Lemma freq_zero_of_notQmem : forall (x : Q) (l : list Q),
  ~ Qmem x l -> freq l x = O.
Proof.
  intros x l. induction l as [| a l IH]; intros Hn.
  - reflexivity.
  - simpl.
    assert (Hax : Qeq_bool a x = false).
    { destruct (Qeq_bool a x) eqn:E.
      - exfalso. apply Hn. apply (proj2 (Qmem_cons x a l)).
        left. rewrite (Qeqb_sym x a). exact E.
      - reflexivity. }
    rewrite Hax. apply IH.
    intro Hc. apply Hn. apply (proj2 (Qmem_cons x a l)). right. exact Hc.
Qed.

(* ========== section 2: frequency permutation invariance (main piece) ========== *)

(* adjacent-transposition conservation: the four-case enumeration of the two equality booleans, each case closed by reflexivity *)
Lemma freq_swap : forall (a b : Q) (l : list Q) (x : Q),
  freq (a :: b :: l) x = freq (b :: a :: l) x.
Proof.
  intros a b l x. simpl.
  destruct (Qeq_bool a x); destruct (Qeq_bool b x); reflexivity.
Qed.

(* main piece: frequencies are invariant along permutations - perm_nil trivial / perm_skip by the equality split /
   perm_swap via freq_swap / perm_trans transitivity chain, verified constructor by constructor *)
Theorem freq_perm : forall (l p : list Q) (x : Q),
  Permutation l p -> freq l x = freq p x.
Proof.
  intros l p x Hp.
  induction Hp as [| y l0 p0 H IH | a b l0 | l1 l2 l3 H1 IH1 H2 IH2].
  - reflexivity.
  - simpl. destruct (Qeq_bool y x); rewrite IH; reflexivity.
  - exact (freq_swap b a l0 x).
  - rewrite IH1. exact IH2.
Qed.

(* ========== section 3: frequency mass conservation (main piece) ========== *)

(* the frequency mass sum over the support list m; at m := dedup l this is the total mass Sigma_freq *)
Fixpoint sumf (m l : list Q) : nat :=
  match m with
  | [] => O
  | y :: ys => (freq l y + sumf ys l)%nat
  end.

Definition Sigma_freq (l : list Q) : nat := sumf (dedup l) l.

(* key lemma: on a Qnodup support list, the mass share of x is relayed from dedup_aux x m to the
   (x :: l) counting face - the swallowed element (at most one element of the same frequency as x) is carried over by congruence,
   while the remaining elements keep their frequency in the consed list. *)
Lemma sumf_dedup_aux : forall (m : list Q) (x : Q) (l : list Q),
  Qnodup m ->
  sumf m l
  = ((if existsb (fun z => Qeq_bool x z) m then freq l x else O)
     + sumf (dedup_aux x m) (x :: l))%nat.
Proof.
  intros m x l. induction m as [| y m' IH]; intros Hnd.
  - simpl. reflexivity.
  - simpl in Hnd. destruct Hnd as [Hny Hnd'].
    destruct (Qeq_bool x y) eqn:Hxy.
    + (* the head y has the same frequency as x: swallowed, the frequency is carried over by congruence *)
      simpl. rewrite ?Hxy. simpl.
      assert (Hfeq : freq l y = freq l x).
      { apply (freq_eq_congr y x l).
        apply (proj1 (Qeq_bool_iff y x)).
        rewrite (Qeqb_sym y x). exact Hxy. }
      destruct (existsb (fun z => Qeq_bool x z) m') eqn:Em'.
      * exfalso. apply Hny.
        apply (Qmem_weaken x y m'); [unfold Qmem; exact Em' | exact Hxy].
      * specialize (IH Hnd'). simpl in IH.
        rewrite Hfeq. rewrite IH. reflexivity.
    + (* the head y differs in frequency from x: kept in the list, consing x does not increase its frequency *)
      simpl. rewrite ?Hxy. simpl. rewrite ?Hxy. simpl.
      specialize (IH Hnd'). rewrite IH.
      destruct (existsb (fun z => Qeq_bool x z) m'); lia.
Qed.

(* mass conservation: the frequency sum over the support image is exactly the list length
   (at the empty list both sides are zero, no nonempty guard needed; the nonempty version is a special case) *)
Theorem sum_freq_dedup : forall l : list Q, Sigma_freq l = length l.
Proof.
  intros l. unfold Sigma_freq.
  induction l as [| x xs IH].
  - reflexivity.
  - assert (Hkey := sumf_dedup_aux (dedup xs) x xs (dedup_Qnodup xs)).
    simpl. rewrite (Qeq_bool_refl x). simpl.
    destruct (existsb (fun z => Qeq_bool x z) (dedup xs)) eqn:Hb.
    + simpl in Hkey. rewrite IH in Hkey.
      rewrite Hkey. lia.
    + simpl in Hkey. rewrite IH in Hkey.
      assert (Hnx : ~ Qmem x xs).
      { intro Hc.
        assert (Hp : Qmem x (dedup xs)) by (apply (dedup_Qmem_r xs x); exact Hc).
        unfold Qmem in Hp. rewrite Hp in Hb. discriminate. }
      assert (H0 : freq xs x = O) by (apply freq_zero_of_notQmem; exact Hnx).
      rewrite H0. rewrite Hkey. reflexivity.
Qed.

(* ========== section 4: the uniform measure and the total mass (main piece) ========== *)

(* Q list summation (the stdlib list_sum is the nat version; the Q version is self-built) *)
Fixpoint qsum (m : list Q) : Q :=
  match m with
  | [] => 0
  | y :: ys => (y + qsum ys)%Q
  end.

(* the # notation requires positive denominators, so the uniform measure takes (freq # 1) / (length # 1),
   semantically freq/length; at length = 0 (the empty list) it is a degenerate value, and the theorem faces carry a nonempty guard. *)
Definition mu (l : list Q) (x : Q) : Q :=
  ((Z.of_nat (freq l x) # 1) / (Z.of_nat (length l) # 1))%Q.

(* the uniform measure is invariant along permutations: resolved by directly instantiating the double invariance of frequencies and length *)
Theorem mu_perm : forall (l p : list Q) (x : Q),
  Permutation l p -> mu l x = mu p x.
Proof.
  intros l p x Hp.
  assert (Hf : freq l x = freq p x) by (apply (freq_perm l p x Hp)).
  assert (Hn : length l = length p) by (apply Permutation_length; exact Hp).
  unfold mu. rewrite Hf, Hn. reflexivity.
Qed.

(* the Q sum of the (freq # 1)-shaped frequency list = the Z-ification of the mass sum *)
Lemma qsum_freq_map : forall (l m : list Q),
  qsum (map (fun y => (Z.of_nat (freq l y) # 1)%Q) m)
  == (Z.of_nat (sumf m l) # 1)%Q.
Proof.
  intros l m. induction m as [| y ys IH]; simpl.
  - reflexivity.
  - rewrite IH.
    rewrite (Znat.Nat2Z.inj_add (freq l y) (sumf ys l)).
    unfold Qplus, Qeq. simpl. lia.
Qed.

(* pointwise distributivity of sums dividing by one and the same Q (the load-bearing piece of Q-domain division balancing) *)
Lemma qsum_map_div : forall (D : Q) (f : Q -> Q) (m : list Q),
  qsum (map (fun y => (f y / D)%Q) m) == (qsum (map f m) / D)%Q.
Proof.
  intros D f m. induction m as [| y ys IH].
  - cbn [qsum map]. symmetry. apply Qmult_0_l.
  - cbn [qsum map]. rewrite IH. unfold Qdiv. ring.
Qed.

(* total mass one: the uniform measure of a nonempty list summed over the support image is exactly one
   - mass conservation is lifted to the Q domain via Z-ification, then division balances after dividing by the total length D *)
Theorem mu_total_mass : forall l : list Q, l <> [] ->
  qsum (map (mu l) (dedup l)) == 1.
Proof.
  intros l Hne.
  assert (Hpos : (1 <= Z.of_nat (length l))%Z).
  { apply (proj1 (Znat.Nat2Z.inj_le 1 (length l))).
    destruct l as [| y ys].
    - exfalso. apply Hne. reflexivity.
    - simpl. lia. }
  assert (HDne : ~ ((Z.of_nat (length l) # 1)%Q == 0%Q)).
  { intros Hc. unfold Qeq in Hc. simpl in Hc. lia. }
  assert (Hfun : forall y : Q,
           mu l y = ((Z.of_nat (freq l y) # 1) / (Z.of_nat (length l) # 1))%Q)
    by (intros y; reflexivity).
  rewrite (map_ext (mu l)
             (fun y => ((Z.of_nat (freq l y) # 1) / (Z.of_nat (length l) # 1))%Q)
             Hfun).
  rewrite (qsum_map_div (Z.of_nat (length l) # 1)%Q
                        (fun y => (Z.of_nat (freq l y) # 1)%Q)).
  rewrite (qsum_freq_map l (dedup l)).
  pose proof (sum_freq_dedup l) as HS. unfold Sigma_freq in HS. rewrite HS.
  field.
  intros Hc. apply HDne. rewrite Hc. reflexivity.
Qed.

