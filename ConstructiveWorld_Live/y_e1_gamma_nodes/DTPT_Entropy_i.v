(* ConstructiveWorld-Main - DTPT_Entropy_i: gate-clean LINT-6 split piece 9/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_i.

    Mission.  [maxfreq]: normalized maximum frequency, closing the order.
      Carries source lines 2308-2661 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f, DTPT_Entropy_g, DTPT_Entropy_h (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g DTPT_Entropy_h.

(* ========== [maxfreq]: normalized maximum frequency, closing the order
   chain (main theorem) ========== *)

Definition maxcount (l : list Q) : nat := nmax (fun x => freq_q x l) l.

Definition maxfreq (l : list Q) : Q := qn (maxcount l) / qn (length l).

(* main theorem, the order chain [collide <= maxfreq]:
   nat side [sqsum <= n * maxcount] (pointwise, from the sum bound and
   [nmax_bound]), Q side same-denominator monotonicity plus in-context
   normalization (the field side condition discharged from the context) *)
Theorem collide_le_maxfreq : forall l : list Q, QleT' (collide l) (maxfreq l).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ collide_zero).
    assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num;
         reflexivity).
    rewrite Hz. apply Qle_refl.
  - unfold collide, maxfreq.
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    pose proof (qpos_neq0 _ HPP) as HP2.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    assert (Hnat : (sqsum (x :: xs)
                    <= length (x :: xs) * maxcount (x :: xs))%nat).
    { unfold sqsum, maxcount. apply NatLe_drop. apply nsum_bound.
      intros x0 Hx0. apply NatLe_drop.
      exact (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x0 Hx0). }
    assert (HQ : qn (sqsum (x :: xs))
                 <= qn (length (x :: xs)) * qn (maxcount (x :: xs))).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                         (maxcount (x :: xs)))).
      apply QleT'_to_Qle. apply qn_le. exact Hnat. }
    assert (HA : qn (sqsum (x :: xs)) / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 <= (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                    / (qn (length (x :: xs)) * qn (length (x :: xs)))).
    { apply QleT'_to_Qle. apply qdiv_ge_num.
      - exact HPP.
      - exact HQ. }
    assert (HB : (qn (length (x :: xs)) * qn (maxcount (x :: xs)))
                 / (qn (length (x :: xs)) * qn (length (x :: xs)))
                 == qn (maxcount (x :: xs)) / qn (length (x :: xs))).
    { field; assumption. }
    exact (Qle_to_QleT' _ _
      (Qle_trans _ _ _ HA (QleT'_to_Qle _ _ (qeq_le_l _ _ HB)))).
Qed.

(* lower bound: [1/n <= maxfreq] (nonempty; [maxcount >= 1] since every
   member has frequency >= 1) *)
Theorem maxfreq_lower : forall l : list Q,
  (0 < length l)%nat -> QleT' (1 / qn (length l)) (maxfreq l).
Proof.
  intros l Hl. apply Qle_to_QleT'. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hge : (1 <= maxcount (x :: xs))%nat).
    { pose proof (NatLe_drop _ _
          (freq_q_ge1 x (x :: xs) (or_introl eq_refl))) as H1.
      assert (Hb : (freq_q x (x :: xs) <= maxcount (x :: xs))%nat).
      { unfold maxcount.
        exact (NatLe_drop _ _
                 (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                    (or_introl eq_refl))). }
      lia. }
    apply QleT'_to_Qle. apply qdiv_ge_num.
    + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos.
    + assert (Hq1 : qn 1 == (1:Q)) by reflexivity.
      rewrite <- Hq1. exact (QleT'_to_Qle _ _ (qn_le 1 (maxcount (x :: xs)) Hge)).
Qed.

(* upper bound: [maxfreq <= 1] (whole list; [maxcount <= length] pointwise
   from [nmax_le_bound]) *)
Theorem maxfreq_upper : forall l : list Q, QleT' (maxfreq l) (1).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. assert (Hz : maxfreq [] == 0)
      by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num; reflexivity).
    rewrite Hz. apply (Qlt_le_weak 0 1). reflexivity.
  - unfold maxfreq. apply qdiv_le_1.
    + assert (Hb : (maxcount (x :: xs) <= length (x :: xs))%nat).
      { unfold maxcount. apply NatLe_drop. apply nmax_le_bound.
        intros y Hy. apply NatLe_drop. apply freq_q_le_length. }
      apply (QleT'_to_Qle _ _ (qn_le (maxcount (x :: xs)) (length (x :: xs)) Hb)).
    + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos.
Qed.

(* degenerate form: all values equal implies [maxfreq] takes 1
   ([maxcount == length], squeezed from both sides) *)
Theorem maxfreq_all_same_one : forall l : list Q,
  all_same l -> (0 < length l)%nat -> QeqT (maxfreq l) 1.
Proof.
  intros l Hs Hl. apply qeq_imp_qeqT. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold maxfreq.
    assert (Hmc : (maxcount (x :: xs) = length (x :: xs))%nat).
    { unfold maxcount. apply Nat.le_antisymm.
      - apply NatLe_drop. apply nmax_le_bound.
        intros y Hy. apply NatLe_drop. apply freq_q_le_length.
      - apply (Nat.le_trans (length (x :: xs)) (freq_q x (x :: xs))
                 (nmax (fun x0 => freq_q x0 (x :: xs)) (x :: xs))).
        + destruct (id_sym (freq_q_eq_all x (x :: xs)
                        (fun z Hz => qeqT_imp_qeq _ _
                           (Hs z x Hz (or_introl eq_refl))))).
          apply Nat.le_refl.
        + exact (NatLe_drop _ _
                   (nmax_bound (fun x0 => freq_q x0 (x :: xs)) (x :: xs) x
                      (or_introl eq_refl))). }
    rewrite Hmc.
    assert (HPne : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    field; assumption.
Qed.

(* [maxcount] is permutation invariant ([nmax_ext_in] pointwise bridge
   plus [nmax_perm]) *)
Theorem maxcount_perm : forall l p : list Q,
  Permutation l p -> Id (maxcount l) (maxcount p).
Proof.
  intros l p H. unfold maxcount.
  assert (Hex : forall x, In x l -> freq_q x l = freq_q x p).
  { intros x _. destruct (freq_q_perm x l p H). reflexivity. }
  destruct (id_sym (nmax_ext_in (fun x => freq_q x l)
              (fun x => freq_q x p) l Hex)).
  exact (nmax_perm (fun x => freq_q x p) l p H).
Qed.

(* [maxfreq] is permutation invariant *)
Theorem maxfreq_perm : forall l p : list Q,
  Permutation l p -> QeqT (maxfreq l) (maxfreq p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold maxfreq.
  destruct (id_sym (maxcount_perm l p H)).
  rewrite (Permutation_length H). reflexivity.
Qed.

(* order chain read together: for nonempty l,
   [1/n <= collide <= maxfreq <= 1], all three members in one chain *)
Theorem H_chain : forall l : list Q, (0 < length l)%nat ->
  And (QleT' (1 / qn (length l)) (collide l))
      (And (QleT' (collide l) (maxfreq l)) (QleT' (maxfreq l) 1)).
Proof.
  intros l Hl. split.
  - apply collide_lower. exact Hl.
  - split.
    + apply collide_le_maxfreq.
    + apply maxfreq_upper.
Qed.

(* ========== [H_max_q] / [H_min_q]: the complement rational surrogates of
   the entropy family ========== *)

Definition H_max_q (l : list Q) : Q := 1 - maxfreq l.

Definition H_min_q (l : list Q) : Q := 1 - collide l.

(* monotonicity: the larger [maxfreq], the smaller [H_max_q] (via the
   order-reversing [qsub_le] bridge) *)
Theorem H_max_q_anti : forall l p : list Q,
  maxfreq l <= maxfreq p -> QleT' (H_max_q p) (H_max_q l).
Proof.
  intros l p H. unfold H_max_q. exact (qsub_le (maxfreq l) (maxfreq p) 1 H).
Qed.

Theorem H_max_q_nonneg : forall l : list Q, QleT' 0 (H_max_q l).
Proof.
  intros l. unfold H_max_q. exact (fst (Qle_0_sub' (maxfreq l) 1) (maxfreq_upper l)).
Qed.

Theorem H_max_q_le_one : forall l : list Q, QleT' (H_max_q l) 1.
Proof.
  intros l. apply Qle_to_QleT'. unfold H_max_q.
  assert (H0 : 0 <= maxfreq l).
  { destruct l as [| x xs].
    - assert (Hz : maxfreq [] == 0)
        by (unfold maxfreq; apply qeqT_imp_qeq; apply qdiv_zero_num;
           reflexivity).
      rewrite Hz. apply Qle_refl.
    - unfold maxfreq. apply QleT'_to_Qle. apply qdiv_nonneg.
      + apply QleT'_to_Qle. apply qn_nonneg.
      + apply QltT_to_Qlt. apply qn_pos. apply NatLe_drop. apply qlen_pos. }
  apply (Qle_trans (1 - maxfreq l) (1 - 0) 1).
  - apply QleT'_to_Qle. apply qsub_le. exact H0.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* coupling with the lower bound: [H_max_q l <= 1 - 1/n] (nonempty) *)
Theorem H_max_q_le_inv : forall l : list Q, (0 < length l)%nat ->
  QleT' (H_max_q l) (1 - 1 / qn (length l)).
Proof.
  intros l Hl. unfold H_max_q.
  exact (qsub_le (1 / qn (length l)) (maxfreq l) 1
    (QleT'_to_Qle _ _ (maxfreq_lower l Hl))).
Qed.

Theorem H_min_q_nonneg : forall l : list Q, QleT' 0 (H_min_q l).
Proof.
  intros l. unfold H_min_q. exact (fst (Qle_0_sub' (collide l) 1) (collide_upper l)).
Qed.

Theorem H_min_q_le_one : forall l : list Q, QleT' (H_min_q l) 1.
Proof.
  intros l. apply Qle_to_QleT'. unfold H_min_q.
  assert (Hc : 0 <= collide l).
  { destruct l as [| x xs].
    - rewrite (qeqT_imp_qeq _ _ collide_zero). apply Qle_refl.
    - unfold collide. apply QleT'_to_Qle. apply qdiv_nonneg.
      + apply QleT'_to_Qle. apply qn_nonneg.
      + apply QltT_to_Qlt. apply qlen_mul_pos. }
  apply (Qle_trans (1 - collide l) (1 - 0) 1).
  - apply QleT'_to_Qle. apply qsub_le. exact Hc.
  - assert (Hz : (1:Q) - 0 == 1) by reflexivity.
    rewrite Hz. apply Qle_refl.
Qed.

(* internal coherence bridge of the entropy family:
   [H_freq == 1 - collide] (nonempty; direct from the definitions, closed
   by field reasoning) *)
Theorem H_freq_eq_bridge : forall l : list Q,
  (0 < length l)%nat -> QeqT (H_freq l) (H_min_q l).
Proof.
  intros l Hl. apply qeq_imp_qeqT. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold H_freq, H_min_q, collide.
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    assert (HP2 : ~ (qn (length (x :: xs)) * qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 _ HPP (qeq_imp_qeqT _ _ Hc)). }
    field; assumption.
Qed.

(* degenerate form: all values equal implies [H_max_q] takes 0 (dual of the
   all-equal vanishing of [H_freq]) *)
Theorem H_max_q_all_same_zero : forall l : list Q,
  all_same l -> (0 < length l)%nat -> QeqT (H_max_q l) 0.
Proof.
  intros l Hs Hl. apply qeq_imp_qeqT. unfold H_max_q.
  assert (H1 : maxfreq l == 1) by (apply qeqT_imp_qeq; apply maxfreq_all_same_one; assumption).
  rewrite H1. reflexivity.
Qed.

(* ========== permutation-invariance closure (bonus) ========== *)

Theorem H_min_q_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_min_q l) (H_min_q p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold H_min_q.
  rewrite (qeqT_imp_qeq _ _ (collide_perm l p H)). reflexivity.
Qed.

Theorem H_max_q_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_max_q l) (H_max_q p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold H_max_q.
  rewrite (qeqT_imp_qeq _ _ (maxfreq_perm l p H)). reflexivity.
Qed.


(* ============================================================
   Coherence of the [MultiEntropyEval] record: local tools (abs triangle /
   aggregate weights / dedup counting), the five-field definitional
   equations, the joint coherence certificate [me_cert], suite-level lifts
   and cross-field bridges, and the [me_total] aggregate.
   ============================================================ *)

(* ============================================================
   The [MultiEntropyEval] coherence suite: from a data bundle to a
   self-certifying record.
   Basis (reused, no new premises): [mkMEval]/[mkMEval_eta],
   [H_shannon_q_nonneg], [xq_H_adj_nonneg], [H_shannon_q_count_ub],
   [H_adj_P0_min], [H_cond_nonneg_guarded], [mkMEval_Hms1_Hsh0],
   [xq_Zlen_nonneg], [xq_Qle_bool_le], [qadd_nonneg], [H_ms], [gate_pass],
   [Qle_dec'], [abs_eq], [abs_neg], [Qle_0_sub'], [qmul_le_r], [qadd_le],
   [qsub], and stdlib [Qle_trans]/[Qle_refl]/[ring]/[lia].
   Layered delivery:
   - baseline: the five field equations, one by one (composed from
     [mkMEval_eta], no re-proofs)
   - main theorem: [me_cert] — carrier agreement + the four entropy
     equalities + nonnegativity of Hadj/Hsh + the counting upper bound on
     Hsh + the triangle bound on Hcond, a nine-way joint coherence
     conjunction ([me_coherent], certified by the construction [mkMEval])
   - main piece: suite-level lifts, the contrapositive bridge
     [H_ms == 1 -> Hsh == 0], the triangle/counting certificate forms of
     |me_Hcond|, and the two-gate bridge ([H_cond_abs_bound] is not
     available here and is not used)
   - bonus: the equal-weight aggregate [me_total] with guarded
     nonnegativity and a twofold Shannon upper bound
   ============================================================ *)

(* ============================================================
   Local tools (abs triangle / aggregate weights / dedup counting)
   ============================================================ *)

(* abs triangle for nonnegative differences:
   0 <= a -> 0 <= b -> |a - b| <= a + b
   (case split by [Qle_dec'], then [abs_eq]/[abs_neg]; each branch
   rearranged by [Qle_0_sub']) *)
Lemma me2_abs_sub_triangle : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> QleT' (Qabs (a - b)) (a + b).
Proof.
  intros a b Ha Hb.
  apply Qle_to_QleT'.
  destruct (Qle_dec' a b) as [Hab | Hba].
  - (* branch a <= b: |a-b| = -(a-b) = b-a, via (a+b)-(b-a) = 2a >= 0 *)
    assert (Hneg : (a - b <= 0)%Q).
    { apply QleT'_to_Qle. apply (snd (Qle_0_sub' (a - b) 0)).
      apply Qle_to_QleT'.
      assert (Hr : (0 - (a - b))%Q == b - a) by ring.
      rewrite Hr. exact (QleT'_to_Qle _ _ (fst (Qle_0_sub' a b) Hab)). }
    rewrite (qeqT_imp_qeq _ _ (abs_neg (a - b) Hneg)).
    assert (Heq : (- (a - b))%Q == b - a) by ring.
    rewrite Heq.
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' (b - a) (a + b))).
    apply Qle_to_QleT'.
    assert (Hr2 : ((a + b) - (b - a))%Q == a + a) by ring.
    rewrite Hr2. apply QleT'_to_Qle. apply qadd_nonneg; exact Ha.
  - (* branch b <= a: |a-b| = a-b, via (a+b)-(a-b) = 2b >= 0 *)
    assert (Hpos : (0 <= a - b)%Q).
    { apply QleT'_to_Qle. apply (fst (Qle_0_sub' b a)). exact Hba. }
    rewrite (qeqT_imp_qeq _ _ (abs_eq (a - b) Hpos)).
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' (a - b) (a + b))).
    apply Qle_to_QleT'.
    assert (Hr3 : ((a + b) - (a - b))%Q == b + b) by ring.
    rewrite Hr3. apply QleT'_to_Qle. apply qadd_nonneg; exact Hb.
Qed.

(* the aggregate weight 1/4 is nonnegative (literal Qle_bool computation) *)
Lemma me2_weight_nonneg : QleT' (0) ((1 # 4)%Q).
Proof. apply Qle_to_QleT'.
  change (Z.le (0 * 4) (1 * 1))%Z.
  lia.
Qed.

(* the dedup count of a nonempty list is >= 1 *)
Lemma me2_dedup_len_ge1 : forall l : list Q,
  l <> [] -> NatLe (1) ((length (dedup l))%nat).
Proof.
  intros [| x xs] H.
  apply NatLe_lift.
  - exfalso. apply H. reflexivity.
  - cbn [dedup length]. reflexivity.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions collide_le_maxfreq.
Print Assumptions maxfreq_lower.
Print Assumptions maxfreq_upper.
Print Assumptions H_freq_eq_bridge.
Print Assumptions H_max_q_anti.
Print Assumptions H_chain.
Print Assumptions maxfreq_perm.
Print Assumptions H_max_q_perm.
Print Assumptions H_min_q_perm.
Print Assumptions me2_weight_nonneg.