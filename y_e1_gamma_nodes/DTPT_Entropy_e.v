(* ConstructiveWorld-Main - DTPT_Entropy_e: gate-clean LINT-6 split piece 5/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_e.

    Mission.  part 5 of the multi-entropy family face.
      Carries source lines 994-1346 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d.

(* ============================================================
   Counting bounds, coherence of the evaluation record, endpoint degeneracy
   of [H_lam], and gating behavior:
     (1) counting upper bounds: [count_val <= length] (nat and Q forms),
         plus the [H_devsum] counting bound (each term |x - suffix minimum|
         is bounded by the pairing bound <= H_adj, so the sum is bounded by
         the length factor times H_adj, the factor reduced to S form)
     (2) coherence of [MultiEntropyEval]: the round trip of the [mkMEval]
         projections (eta form), and degeneracy [H_ms == 1] implies
         [H_devsum == 0] (dedup count -> all values equal -> sorted ->
         vanishing, a four-step bridge), with a constructive counterexample
         for the converse
     (3) endpoint degeneracy of [H_lam]: lam = 1 / lam = 0 recover the P0 /
         Pinf phase entropies
     (4) behavior of [gate_low_entropy] / [phase_side] (Qle_bool bridges in
         both directions)
   Reuses the toolbox proved in this file ([qmul_le_r], [Qle_bool_iff],
   [Qle_bool_false_le], [dedup_Qmem_r] and the [xq_] tools); no new
   premises.
   ============================================================ *)

(* ---------- local [xq] tools: the Q bridge for the length factor
   ---------- *)

Lemma xq_Zlen_nonneg : forall n : nat, QleT' (0) ((Z.of_nat n # 1)%Q).
Proof.
  intro n. apply Qle_to_QleT'. unfold Qle; simpl. lia.
Qed.

Lemma xq_Zlen_S : forall n : nat,
  QeqT (Z.of_nat (S n) # 1) (1 + (Z.of_nat n # 1))%Q.
Proof.
  intro n. apply qeq_imp_qeqT.
  assert (Hz : (Z.of_nat (S n) = 1 + Z.of_nat n)%Z) by lia.
  rewrite Hz. unfold Qeq, Qplus. cbn [Qnum Qden]. lia.
Qed.

Lemma xq_Zlen_inj1 : forall n : nat, ((Z.of_nat n # 1) == 1)%Q -> Id (n) (1%nat).
Proof.
  intros n H. apply eq_imp_id. unfold Qeq in H; simpl in H. lia.
Qed.

Lemma xq_Qeq_le : forall x y : Q, x == y -> QleT' (x) (y).
Proof.
  intros [nx dx] [ny dy] Hxy. apply Qle_to_QleT'. unfold Qeq in Hxy; simpl in Hxy.
  unfold Qle; simpl. lia.
Qed.

(* ---------- main theorem 1a: the length upper bound of the frequency
   counts (nat form) ---------- *)

Lemma count_val_le_length : forall (x : Q) (l : list Q), NatLe (count_val x l) ((length l)%nat).
Proof.
  intros x l. apply NatLe_lift. induction l as [| y ys IH]; simpl.
  - lia.
  - destruct (Qeq_bool x y); lia.
Qed.

(* main theorem 1b: the same upper bound in Q form (same length-factor
   convention) *)
Lemma count_val_Zle_length : forall (x : Q) (l : list Q),
  QleT' (Z.of_nat (count_val x l) # 1) (Z.of_nat (length l) # 1).
Proof.
  intros x l. apply Qle_to_QleT'.
  pose proof (count_val_le_length x l) as Hn.
  pose proof (NatLe_drop _ _ Hn) as Hn2.
  unfold Qle; simpl. lia.
Qed.

(* ---------- main theorem 1c: the [H_devsum] counting bound ----------
   Each term of [H_devsum] is |x - suffix minimum|: the pairing bound gives
   termwise <= H_adj, hence the sum <= length factor * H_adj.  Nontrivial
   points: suffix monotonicity (prepending only increases), reduction of
   the factor to S form, and unifying the order of the factors. ---------- *)

Lemma xq_H_adj_suffix_le : forall (a : Q) (l : list Q), QleT' (H_adj l) (H_adj (a :: l)).
Proof.
  intros a l. apply Qle_to_QleT'. destruct l as [| b bs].
  - cbn [H_adj sum_adjdiff]. apply Qle_refl.
  - change (H_adj (a :: b :: bs)) with (Qabs (b - a) + H_adj (b :: bs))%Q.
    apply QleT'_to_Qle. apply xq_le_add_abs.
Qed.

Lemma xq_head_term_le : forall (x : Q) (xs : list Q), QleT' (Qabs (x - hd 0 (P0 (x :: xs)))) (H_adj (x :: xs)).
Proof.
  intros x xs. apply Qle_to_QleT'. apply QleT'_to_Qle. apply xq_pair_dist_le.
  - left. reflexivity.
  - apply Permutation_in with (l := P0 (x :: xs)).
    + apply Permutation_sym. apply D5_P0_perm.
    + apply xq_hd_In_gen. apply xq_P0_cons_ne.
Qed.

Theorem H_shannon_q_count_ub : forall l : list Q, QleT' (H_devsum l) (H_adj l * (Z.of_nat (length l) # 1)).
Proof.
  intro l. induction l as [| x xs IH]; apply Qle_to_QleT'.
  - cbn [H_devsum]. apply QleT'_to_Qle. apply xq_mul_nonneg.
    + apply QleT'_to_Qle. apply xq_H_adj_nonneg.
    + apply QleT'_to_Qle. apply xq_Zlen_nonneg.
  - cbn [H_devsum].
    assert (Hs : (H_devsum xs
                  <= H_adj (x :: xs) * (Z.of_nat (length xs) # 1))%Q).
    { apply (Qle_trans _ (H_adj xs * (Z.of_nat (length xs) # 1))).
      - apply QleT'_to_Qle. exact IH.
      - apply QleT'_to_Qle. apply qmul_le_r.
        + apply QleT'_to_Qle. apply xq_H_adj_suffix_le.
        + apply QleT'_to_Qle. apply xq_Zlen_nonneg. }
    assert (Hh : (Qabs (x - hd 0 (P0 (x :: xs))) <= H_adj (x :: xs))%Q)
      by (apply QleT'_to_Qle; apply xq_head_term_le).
    assert (Hlen : ((Z.of_nat (length (x :: xs)) # 1)
                    == 1 + (Z.of_nat (length xs) # 1))%Q)
      by (cbn [length]; apply qeqT_imp_qeq; apply xq_Zlen_S).
    apply (Qle_trans _ (H_adj (x :: xs)
                        + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))).
    + apply QleT'_to_Qle. apply qadd_le; [exact Hh | exact Hs].
    + rewrite Hlen.
      assert (Heq : H_adj (x :: xs) * (1 + (Z.of_nat (length xs) # 1))
                    == H_adj (x :: xs)
                       + H_adj (x :: xs) * (Z.of_nat (length xs) # 1))
        by ring.
      rewrite Heq. apply Qle_refl.
Qed.

(* ---------- coherence 2a: vanishing of [H_devsum] on an all-equal list
   ---------- *)

Lemma xq_insert_const_head : forall (a y : Q) (ys : list Q),
  y == a -> Id (insert_q a (y :: ys)) (a :: y :: ys).
Proof.
  intros a y ys Hya. apply eq_imp_id. cbn [insert_q].
  destruct (id_sym (xq_Qle_bool_true a y
              (QleT'_to_Qle _ _ (xq_Qeq_le a y (Qeq_sym y a Hya))))).
  reflexivity.
Qed.

Lemma xq_P0_const_id : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> Id (P0 l) (l).
Proof.
  intros a l. induction l as [| x xs IH]; intro Hfa; apply eq_imp_id.
  - reflexivity.
  - inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [P0]. destruct (id_sym (IH Hfxs)).
    destruct xs as [| y ys].
    + cbn [insert_q]. reflexivity.
    + destruct (id_sym (xq_insert_const_head x y ys
                   (Qeq_trans y a x (Forall_inv Hfxs) (Qeq_sym x a Hzx)))).
      reflexivity.
Qed.

Theorem H_shannon_q_const_zero : forall (a : Q) (l : list Q),
  Forall (fun z => z == a) l -> QeqT (H_devsum l) (0).
Proof.
  intros a l. revert a. induction l as [| x xs IH]; intros a Hfa;
    apply qeq_imp_qeqT.
  - reflexivity.
  - assert (Hfa' : Forall (fun z => z == a) (x :: xs)) by exact Hfa.
    inversion Hfa as [| z zs Hzx Hfxs]; subst.
    cbn [H_devsum].
    destruct (id_sym (xq_P0_const_id a (x :: xs) Hfa')).
    cbn [hd]. rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)).
    rewrite (qeqT_imp_qeq _ _ (IH a Hfxs)). ring.
Qed.

(* ---------- coherence 2b: multiset-entropy degeneracy implies vanishing
   of the Shannon deviation entropy ---------- *)

Lemma xq_len1_el : forall m : list Q,
  length m = 1%nat -> sigT (fun a : Q => Id m (a :: nil)).
Proof.
  intros [| b bs] H; cbn [length] in H.
  - discriminate H.
  - destruct bs as [| c cs].
    + apply (existT _ b). apply eq_imp_id. reflexivity.
    + discriminate H.
Qed.

Lemma xq_In_Qmem : forall (z : Q) (l : list Q), In z l -> Qmem z l.
Proof.
  intros z l. induction l as [| y ys IH]; intro Hind.
  - destruct Hind.
  - simpl in Hind. destruct (Qeq_bool z y) eqn:E.
    + apply (snd (Qmem_cons _ _ _)). left. apply eq_imp_id. exact E.
    + apply (snd (Qmem_cons _ _ _)). right. apply IH.
      destruct Hind as [Heq | Hind].
      * rewrite <- Heq in E. rewrite Qeq_bool_refl in E. discriminate E.
      * exact Hind.
Qed.

Lemma xq_dedup1_all_eq : forall (l : list Q) (a : Q),
  dedup l = a :: nil -> forall z : Q, In z l -> QeqT z a.
Proof.
  intros l a Hd z Hz.
  assert (Hm : Qmem z (dedup l)).
  { apply dedup_Qmem_r. apply xq_In_Qmem. exact Hz. }
  rewrite Hd in Hm.
  destruct (fst (Qmem_cons z a nil) Hm) as [Hm1 | Hm1].
  - assert (E : Qeq_bool z a = true)
      by (destruct (id_sym Hm1); reflexivity).
    apply qeq_imp_qeqT. apply Qeq_bool_eq. exact E.
  - simpl in Hm1. inversion Hm1.
Qed.

Theorem H_ms1_Hshannon0 : forall l : list Q,
  (H_ms l == 1)%Q -> QeqT (H_devsum l) 0.
Proof.
  intro l. unfold H_ms. intro H.
  assert (HI : Id (length (dedup l)) 1%nat)
    by (apply (xq_Zlen_inj1 (length (dedup l))); exact H).
  assert (Hlen : length (dedup l) = 1%nat)
    by (destruct (id_sym HI); reflexivity).
  destruct (xq_len1_el (dedup l) Hlen) as [b Hb].
  apply (H_shannon_q_const_zero b l).
  assert (Hbe : dedup l = [b]) by (destruct (id_sym Hb); reflexivity).
  apply Forall_forall. intros z Hz. apply qeqT_imp_qeq.
  apply (xq_dedup1_all_eq l b Hbe z Hz).
Qed.


(* ---------- coherence 2c: the projections of [mkMEval] round-trip (eta
   form) ---------- *)

Theorem mkMEval_eta : forall (l ctx : list Q),
  And (Id (me_carrier (mkMEval l ctx)) l)
  (And (QeqT (me_Hadj (mkMEval l ctx)) (H_adj l))
  (And (QeqT (me_Hms (mkMEval l ctx)) (H_ms l))
  (And (QeqT (me_Hsh (mkMEval l ctx)) (H_devsum l))
       (QeqT (me_Hcond (mkMEval l ctx)) (H_cond l ctx))))).
Proof.
  intros l ctx. repeat split.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
  - apply qeq_imp_qeqT. unfold Qeq. simpl. reflexivity.
Qed.

Theorem mkMEval_Hms1_Hsh0 : forall (l ctx : list Q),
  (me_Hms (mkMEval l ctx) == 1)%Q -> QeqT (me_Hsh (mkMEval l ctx)) (0).
Proof.
  intros l ctx H. apply qeq_imp_qeqT. unfold mkMEval in H. simpl in H.
  unfold mkMEval. simpl. exact (qeqT_imp_qeq _ _ (H_ms1_Hshannon0 l H)).
Qed.

(* ---------- endpoint 3: degeneracy of [H_lam] at lambda = 1 /
   lambda = 0 ---------- *)

Theorem H_lam_lam1 : forall (l : list Q) (s : nat),
  QeqT (H_lam l s 1) (H_adj (P0 l)).
Proof.
  intros l s. apply qeq_imp_qeqT. unfold H_lam.
  replace (1 - 1)%Q with 0%Q by reflexivity.
  ring.
Qed.

Theorem H_lam_lam0 : forall (l : list Q) (s : nat),
  QeqT (H_lam l s 0) (H_adj (Pinf l s)).
Proof.
  intros l s. apply qeq_imp_qeqT. unfold H_lam.
  replace (1 - 0)%Q with 1%Q by reflexivity.
  ring.
Qed.

(* ---------- gating 4: behavior of [gate_low_entropy] / [phase_side]
   ---------- *)

Theorem gate_low_entropy_spec : forall H threshold : Q,
  IffT (Id (gate_low_entropy H threshold) true) (QleT' H threshold).
Proof.
  intros H threshold. split.
  - intro E. apply Qle_to_QleT'.
    assert (Eb : Qle_bool H threshold = true)
      by (unfold gate_low_entropy in E; destruct (id_sym E); reflexivity).
    apply (proj1 (Qle_bool_iff H threshold)). exact Eb.
  - intro Hle. apply eq_imp_id. unfold gate_low_entropy.
    apply (proj2 (Qle_bool_iff H threshold)).
    apply (QleT'_to_Qle _ _ Hle).
Qed.

Theorem gate_low_entropy_false_le : forall H threshold : Q,
  gate_low_entropy H threshold = false -> QleT' threshold H.
Proof.
  intros H threshold Hfalse.
  exact (Qle_bool_false_le _ _ Hfalse).
Qed.

Theorem gate_low_entropy_dec : forall H threshold : Q,
  Or (Id (gate_low_entropy H threshold) true)
     (Id (gate_low_entropy H threshold) false).
Proof.
  intros H threshold. unfold gate_low_entropy.
  destruct (Qle_bool H threshold).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

Theorem phase_side_spec : forall (l : list Q) (s : nat),
  IffT (Id (phase_side l s) 0%nat) (QleT' (H_adj (P0 l)) (H_adj (Pinf l s))).
Proof.
  intros l s. split.
  - intro E. assert (Eb : phase_side l s = 0%nat)
      by (destruct (id_sym E); reflexivity).
    unfold phase_side in Eb.
    destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:Ex.
    + apply Qle_to_QleT'. apply (proj1 (Qle_bool_iff _ _)). exact Ex.
    + simpl in Eb. discriminate Eb.
  - intro Hle. apply eq_imp_id. unfold phase_side.
    destruct (id_sym (xq_Qle_bool_true _ _ (QleT'_to_Qle _ _ Hle))).
    reflexivity.
Qed.

Theorem phase_side_values : forall (l : list Q) (s : nat),
  Or (Id (phase_side l s) 0%nat) (Id (phase_side l s) 1%nat).
Proof.
  intros l s. unfold phase_side.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

(* ============================================================
   The true-frequency Shannon entropy ([H_freq]) theorem family and the
   data-processing inequality family.
   ============================================================ *)

(* ============================================================
   True-frequency Shannon entropy, permutation invariance, and the
   data-processing inequality.
   Content: the self-contained definition face of the true-frequency
   Shannon entropy (a rational surrogate over Q): [qn] (nat -> Q
   embedding), [freq_q] (frequency counting with Qeq_bool equality),
   [nsum] (general summation), [sqsum] (collision sum without dedup), and
   [H_freq] = 1 - sum_v p_v^2 with its theorem family (permutation
   invariance [H_freq_perm], nonnegativity, and a two-sided degeneracy
   characterization).  Background: [H_devsum] is a centroid-offset sum and
   is NOT permutation invariant (see the counterexample above); [H_freq]
   is its faithful replacement, lies in [0,1), and takes 0 on all-equal
   lists and lists of length <= 1.
   Data-processing inequality family: a coarse-grained observation
   ([map f]) does not increase [H_freq] — the counting form [freq_q_map],
   pointwise domination [freq_q_map_ge] (a Qeq-shape assumption enters
   here), collision-sum monotonicity [sqsum_map_ge], the complement sign
   flip [hfreq_core_anti], the main theorem [H_freq_dpi], endpoint
   examples, and the iterated no-decay chain.
   ============================================================ *)
