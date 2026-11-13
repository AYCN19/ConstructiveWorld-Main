(* ConstructiveWorld-Main - DTPT_Entropy_j: gate-clean LINT-6 split piece 10/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_j.

    Mission.  part 10 of the multi-entropy family face.
      Carries source lines 2662-2984 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f, DTPT_Entropy_g, DTPT_Entropy_h, DTPT_Entropy_i (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g DTPT_Entropy_h DTPT_Entropy_i.

(* ============================================================
   Baseline: the five field equations, one by one (reusing [mkMEval_eta],
   no re-proofs)
   ============================================================ *)

Theorem me2_carrier_eq : forall (l ctx : list Q), Id (me_carrier (mkMEval l ctx)) (l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc _]. exact Hc.
Qed.

Theorem me2_Hadj_eq : forall (l ctx : list Q), QeqT (me_Hadj (mkMEval l ctx)) (H_adj l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [Ha _]]. exact Ha.
Qed.

Theorem me2_Hms_eq : forall (l ctx : list Q),
  QeqT (me_Hms (mkMEval l ctx)) (H_ms l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [Hm _]]]. exact Hm.
Qed.

Theorem me2_Hsh_eq : forall (l ctx : list Q), QeqT (me_Hsh (mkMEval l ctx)) (H_devsum l).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [Hs _]]]]. exact Hs.
Qed.

Theorem me2_Hcond_eq : forall (l ctx : list Q), QeqT (me_Hcond (mkMEval l ctx)) (H_cond l ctx).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [_ [_ [_ [_ Hc]]]]. exact Hc.
Qed.

(* ============================================================
   Main theorem: [me_cert] — the self-certifying record of [mkMEval]
   (nine-way joint coherence conjunction: carrier agreement + the four
   entropy equalities + nonnegativity of Hadj/Hsh + the counting upper
   bound on Hsh + the triangle bound on Hcond)
   ============================================================ *)

Definition me_coherent (m : MultiEntropyEval) (l ctx : list Q) : Set :=
  And (Id (me_carrier m) l)
  (And (QeqT (me_Hadj m) (H_adj l))
  (And (QeqT (me_Hms m) (H_ms l))
  (And (QeqT (me_Hsh m) (H_devsum l))
  (And (QeqT (me_Hcond m) (H_cond l ctx))
  (And (QleT' 0 (me_Hadj m))
  (And (QleT' 0 (me_Hsh m))
  (And (QleT' (me_Hsh m) (me_Hadj m * (Z.of_nat (length (me_carrier m)) # 1)))
       (QleT' (Qabs (me_Hcond m)) (me_Hsh m + H_devsum ctx))))))))).

Theorem me_cert : forall (l ctx : list Q),
  me_coherent (mkMEval l ctx) l ctx.
Proof.
  intros l ctx.
  destruct (mkMEval_eta l ctx) as [Hc [Ha [Hm [Hs Hcond]]]].
  (* [repeat split] closes the first five definitional conjuncts (carrier
   equality + four Qeq; Z.eq is a Prop-level single constructor, solvable
   by eq_refl after projection delta reduction); the remaining four Qle
   coherence conjuncts reuse the baseline lemmas one by one *)
  unfold me_coherent, And. repeat split.
  - exact Ha.
  - exact Hm.
  - exact Hs.
  - exact Hcond.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ Ha).
    apply QleT'_to_Qle. apply xq_H_adj_nonneg.
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ Hs).
    apply QleT'_to_Qle. apply H_shannon_q_nonneg.
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ Hs), (qeqT_imp_qeq _ _ Ha).
    destruct (id_sym Hc).
    exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ Hcond), (qeqT_imp_qeq _ _ Hs).
    unfold H_cond.
    apply QleT'_to_Qle. apply me2_abs_sub_triangle;
      apply QleT'_to_Qle, H_shannon_q_nonneg.
Qed.

(* ============================================================
   Main piece: suite-level lifts and cross-field bridges (certificate
   forms)
   ============================================================ *)

(* lift of P0 minimality: [H_adj (P0 carrier)] <= [me_Hadj] *)
Theorem mkMEval_Hadj_min : forall (l ctx : list Q),
  QleT' (H_adj (P0 (me_carrier (mkMEval l ctx)))) (me_Hadj (mkMEval l ctx)).
Proof.
  intros l ctx. destruct (mkMEval_eta l ctx) as [Hc [Ha _]].
  apply Qle_to_QleT'.
  destruct (id_sym Hc).
  rewrite (qeqT_imp_qeq _ _ Ha).
  exact (QleT'_to_Qle _ _ (H_adj_P0_min l)).
Qed.

(* nonnegativity of the Shannon field *)
Theorem mkMEval_Hsh_nonneg : forall (l ctx : list Q),
  QleT' 0 (me_Hsh (mkMEval l ctx)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)).
  exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
Qed.

(* counting upper bound of the Shannon field ([H_adj] times the length
   factor) *)
Theorem mkMEval_Hsh_ub : forall (l ctx : list Q),
  QleT' (me_Hsh (mkMEval l ctx))
        (me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)),
          (qeqT_imp_qeq _ _ (me2_Hadj_eq l ctx)).
  exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
Qed.

(* nonempty lower bound of the multiset entropy: a nonempty carrier gives
   [1 <= me_Hms] (Z bridge) *)
Theorem mkMEval_Hms_ge1 : forall (l ctx : list Q),
  l <> [] -> QleT' 1 (me_Hms (mkMEval l ctx)).
Proof.
  intros l ctx Hl. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hms_eq l ctx)). unfold H_ms.
  assert (Hn : (1 <= length (dedup l))%nat)
    by (apply NatLe_drop; apply me2_dedup_len_ge1; exact Hl).
  assert (Hz : (1 <= Z.of_nat (length (dedup l)))%Z) by lia.
  unfold Qle. cbn [Qnum Qden]. lia.  (* the record field's true name is lowercase [Qden] *)
Qed.

(* negative-side bound of the conditional entropy:
   [-H_sh ctx <= me_Hcond] (rearranged [H_shannon_q_nonneg]) *)
Theorem mkMEval_Hcond_lb : forall (l ctx : list Q),
  QleT' (- H_devsum ctx) (me_Hcond (mkMEval l ctx)).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hcond_eq l ctx)). unfold H_cond.
  apply QleT'_to_Qle. apply (snd (Qle_0_sub' (- H_devsum ctx)
                           (H_devsum l - H_devsum ctx))).
  apply Qle_to_QleT'.
  assert (Hr : (H_devsum l - H_devsum ctx) - (- H_devsum ctx)
               == H_devsum l) by ring.
  rewrite Hr. exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
Qed.

(* both gates use the same Qle_bool: the low-entropy gate equals
   [gate_pass] (across the two definitions) *)
Theorem mkMEval_gate_bridge : forall (l ctx : list Q) (t : Q), Id (gate_low_entropy (me_Hsh (mkMEval l ctx)) t) (gate_pass t (H_devsum l)).
Proof.
  intros l ctx t. apply eq_imp_id. unfold gate_low_entropy, gate_pass, mkMEval.
  cbn [me_Hsh]. destruct (Qle_bool (H_devsum l) t); reflexivity.
Qed.

(* cross-field bridge, certificate form: the contrapositive of
   [H_ms == 1 -> Hsh == 0] (reusing [mkMEval_Hms1_Hsh0], no re-proof) *)
Theorem mkMEval_notHsh0_notHms1 : forall (l ctx : list Q),
  ~ (me_Hsh (mkMEval l ctx) == 0)%Q -> Not (QeqT (me_Hms (mkMEval l ctx)) 1).
Proof.
  intros l ctx H0 Hms1. apply qeqT_imp_qeq in Hms1.
  exact (False_rect Empty_set
    (H0 (qeqT_imp_qeq _ _ (mkMEval_Hms1_Hsh0 l ctx Hms1)))).
Qed.

(* triangle bound, certificate form:
   [|me_Hcond| <= me_Hsh + H_sh ctx] (composed from lemmas of this file;
   the abs-bound lemma of the zero-locus suite is not available here and
   is not used) *)
Theorem mkMEval_Hcond_abs_ub : forall (l ctx : list Q),
  QleT' (Qabs (me_Hcond (mkMEval l ctx)))
        (me_Hsh (mkMEval l ctx) + H_devsum ctx).
Proof.
  intros l ctx. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (me2_Hcond_eq l ctx)),
          (qeqT_imp_qeq _ _ (me2_Hsh_eq l ctx)). unfold H_cond.
  apply QleT'_to_Qle. apply me2_abs_sub_triangle;
    [ exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l))
    | exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)) ].
Qed.

(* counting bound, certificate form:
   [|me_Hcond| <= me_Hadj * n_l + H_adj ctx * n_ctx]
   (the triangle bound combined with [H_shannon_q_count_ub] on both arms) *)
Theorem mkMEval_Hcond_count_ub : forall (l ctx : list Q), QleT' (Qabs (me_Hcond (mkMEval l ctx))) (me_Hadj (mkMEval l ctx) * (Z.of_nat (length l) # 1)
       + H_adj ctx * (Z.of_nat (length ctx) # 1)).
Proof.
  intros l ctx. pose proof (mkMEval_eta l ctx) as Heta.
  destruct Heta as [Hc Hr1]. destruct Hr1 as [Ha Hr2].
  destruct Hr2 as [Hm Hr3]. destruct Hr3 as [Hs Hcond].
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ Hcond), (qeqT_imp_qeq _ _ Ha).
  unfold H_cond.
  apply (Qle_trans _ (H_devsum l + H_devsum ctx)%Q).
  - apply QleT'_to_Qle. apply me2_abs_sub_triangle;
      [ exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l))
      | exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)) ].
  - apply QleT'_to_Qle. apply qadd_le.
    + exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub l)).
    + exact (QleT'_to_Qle _ _ (H_shannon_q_count_ub ctx)).
Qed.

(* ============================================================
   Bonus: the aggregate [me_total] (equal weights 1/4) with guarded
   nonnegativity and a twofold upper bound
   ============================================================ *)

Definition me_total (m : MultiEntropyEval) : Q :=
  (1 # 4)%Q * (me_Hadj m + me_Hms m + me_Hsh m + me_Hcond m)%Q.

(* the aggregate's defining equations (definitional projections of
   [mkMEval]) *)
Theorem me_total_eq : forall (l ctx : list Q), QeqT (me_total (mkMEval l ctx)) ((1 # 4)%Q * (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
Proof.
  intros l ctx.
  apply qeq_imp_qeqT.
  change (me_total (mkMEval l ctx))
    with ((1 # 4)%Q * (me_Hadj (mkMEval l ctx) + me_Hms (mkMEval l ctx)
          + me_Hsh (mkMEval l ctx) + me_Hcond (mkMEval l ctx))%Q).
  change (me_Hadj (mkMEval l ctx)) with (H_adj l).
  change (me_Hms (mkMEval l ctx)) with (H_ms l).
  change (me_Hsh (mkMEval l ctx)) with (H_devsum l).
  change (me_Hcond (mkMEval l ctx)) with (H_cond l ctx).
  reflexivity.
Qed.

(* guarded nonnegativity: [H_sh ctx <= H_sh l -> 0 <= me_total]
   (under the guard all four entropies are nonnegative; a chain of
   [qadd_nonneg] and [qmul_le_r]) *)
Theorem me_total_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q ->
  QleT' 0 (me_total (mkMEval l ctx)).
Proof.
  intros l ctx Hle. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (me_total_eq l ctx)).
  assert (Hc : (0 <= H_cond l ctx)%Q)
    by (apply QleT'_to_Qle; apply H_cond_nonneg_guarded; exact Hle).
  assert (Hms : (0 <= H_ms l)%Q)
    by (unfold H_ms; apply QleT'_to_Qle; apply xq_Zlen_nonneg).
  assert (Hsum : (0 <= H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q).
  { apply QleT'_to_Qle. apply qadd_nonneg.
    - apply QleT'_to_Qle. apply qadd_nonneg.
      + apply QleT'_to_Qle. apply qadd_nonneg;
          [ apply QleT'_to_Qle; apply xq_H_adj_nonneg | exact Hms ].
      + exact (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)).
    - exact Hc. }
  exact (QleT'_to_Qle _ _ (xq_mul_nonneg ((1 # 4)%Q)
    ((H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q)
    (QleT'_to_Qle _ _ me2_weight_nonneg) Hsum)).
Qed.

(* aggregate upper bound: [me_total <= (1/4) * (H_adj + H_ms + 2 * H_sh)]
   (the negative side is exactly absorbed by [H_cond <= H_sh l], since
   [-H_sh ctx <= 0]) *)
Theorem me_total_ub : forall (l ctx : list Q), QleT' (me_total (mkMEval l ctx)) ((1 # 4)%Q * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
Proof.
  intros l ctx. apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ (me_total_eq l ctx)).
  assert (Hcc : (H_cond l ctx <= H_devsum l)%Q).
  { unfold H_cond. apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)).
    apply Qle_to_QleT'.
    assert (Hr : H_devsum l - (H_devsum l - H_devsum ctx)
                 == H_devsum ctx) by ring.
    rewrite Hr. apply QleT'_to_Qle. apply H_shannon_q_nonneg. }
  assert (Hsub : (H_devsum l + H_cond l ctx
                  <= (2 # 1)%Q * H_devsum l)%Q).
  { assert (Hr2 : (2 # 1)%Q * H_devsum l
                  == H_devsum l + H_devsum l) by ring.
    rewrite Hr2. apply QleT'_to_Qle. apply qadd_le.
    - apply Qle_refl.
    - exact Hcc. }
  assert (Hassoc : (H_adj l + H_ms l + H_devsum l + H_cond l ctx)%Q
                   == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q)
    by ring.
  rewrite Hassoc.
  assert (Hinner : (H_adj l + H_ms l + (H_devsum l + H_cond l ctx)
                    <= H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q).
  { apply QleT'_to_Qle. apply qadd_le.
    - apply Qle_refl.
    - exact Hsub. }
  (* [qmul_le_r] multiplies on the right and requires a common multiplier:
   rearrange both weighted sides to the right by ring *)
  assert (Hsw1 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
               == (H_adj l + H_ms l + (H_devsum l + H_cond l ctx))%Q
                    * (1 # 4)%Q) by ring.
  assert (Hsw2 : (1 # 4)%Q
                   * (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
               == (H_adj l + H_ms l + (2 # 1)%Q * H_devsum l)%Q
                    * (1 # 4)%Q) by ring.
  rewrite Hsw1, Hsw2. apply QleT'_to_Qle. apply qmul_le_r.
  - exact Hinner.
  - exact (QleT'_to_Qle _ _ me2_weight_nonneg).
Qed.

(* ============================================================
   Zero-locus characterization of the placeholder Shannon deviation
   entropy [H_devsum]: tools, the main theorem (zero locus iff ascending
   list), the all-equal characterization of [H_ms == 1], the [H_cond]
   family, and the restricted positive forms of the counterexamples.
   ============================================================ *)

(* ============================================================
   Zero-locus characterization of the placeholder centroid-offset Shannon
   deviation entropy [H_devsum] (the termwise |x - suffix P0 minimum| sum):
   the zero locus is exactly the ascending lists ([SortedQ]).
   Content grading:
   main theorem [H_shannon_q_zero_iff_sorted] (forward = the existing
     [xq_H_shannon_sortQ]; backward proved here: a vanishing sum with
     termwise nonnegativity forces each term to zero, so the head equals
     the suffix P0 minimum at every step — ascending cons, with the new
     head-minimality lemma [xqz_sorted_hd_min])
   piece A [H_ms1_all_eq] / [H_ms1_iff_const] (characterizing [H_ms == 1]
     as all members equal; honest convention: [H_ms []] == 0 while all
     members of the empty list are vacuously equal, so the right side of
     the iff carries the [l <> []] guard)
   piece B [H_cond_nonneg_iff] / [H_cond_abs_bound] / [H_cond_zero_iff]
     (absolute-value bound: |H_cond| <= H_devsum l + H_devsum ctx)
   bonus [H_shannon_q_perm_inv_if_sorted] (the restricted positive form of
     the permutation counterexample: invariance holds when both sides are
     ascending), [zero_locus_joint] (the positive twin: double zero locus
     iff a nonempty constant list), and
     [zero_locus_contrast_sorted_not_const] (the [1;2] contrast anchor)
   Contrast with the true-frequency entropy: the placeholder [H_devsum] can
   vanish on lists with distinct values ([1;2] is a zero locus but not
   constant), while the zero locus of the true-frequency [H_freq] is
   exactly the constant lists; new names carry the [xqz_] prefix.
   ============================================================ *)


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
(* ========== zero-axiom attestation of the coherence / zero-locus sections
   ========== *)
Print Assumptions me_cert.
Print Assumptions mkMEval_gate_bridge.
Print Assumptions mkMEval_Hcond_count_ub.
Print Assumptions me_total_ub.
Print Assumptions me_total_eq.