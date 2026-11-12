(* ConstructiveWorld-Main - DTPT_Entropy_d: gate-clean LINT-6 split piece 4/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_d.

    Mission.  main theorem 3: cross-phase sandwich for the.
      Carries source lines 849-993 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c.

(* ========== main theorem 3: cross-phase sandwich for the
   lambda-interpolated mixed entropy ========== *)

Lemma xq_mul_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> QleT' (0) (a * b).
Proof.
  intros [an ad] [bn bd] Ha Hb. apply Qle_to_QleT'. unfold Qle in Ha, Hb; simpl in Ha, Hb.
  unfold Qle, Qmult; simpl. lia.
Qed.

Theorem H_lam_cross_phase_bounds : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam)%Q -> (lam <= 1)%Q ->
  And (QleT' (H_adj (P0 l)) (H_lam l s lam))
      (QleT' (H_lam l s lam) (H_adj (Pinf l s))).
Proof.
  intros l s lam Hlam0 Hlam1.
  assert (Hle : (H_adj (P0 l) <= H_adj (Pinf l s))%Q)
    by (apply QleT'_to_Qle; apply H_adj_cross_phase_lb).
  unfold H_lam.
  assert (Hlo : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - H_adj (P0 l))%Q).
  { assert (Er1 : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                  - H_adj (P0 l)
                  == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er1.
    apply QleT'_to_Qle. apply xq_mul_nonneg.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)).
      apply Qle_to_QleT'. exact Hlam1.
    - apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
      apply Qle_to_QleT'. exact Hle. }
  assert (Hup : (0 <= H_adj (Pinf l s)
                 - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)))%Q).
  { assert (Er2 : H_adj (Pinf l s)
                  - (lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s))
                  == lam * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
    rewrite Er2.
    apply QleT'_to_Qle; apply xq_mul_nonneg;
      [ exact Hlam0
      | apply QleT'_to_Qle; apply (fst (Qle_0_sub' _ _));
        apply Qle_to_QleT'; exact Hle ]. }
  split.
  - apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hlo.
  - apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hup.
Qed.

(* ========== main theorem 4: vanishing of the Shannon deviation entropy at
   phase P0, and minimality ========== *)

Lemma xq_H_shannon_sortQ : forall l : list Q, SortedQ l -> QeqT (H_devsum l) (0).
Proof.
  intro l. induction l as [| a rest IH]; intro HS; apply qeq_imp_qeqT.
  - reflexivity.
  - inversion HS as [| x0 xs0 HSr HFa]; subst.
    cbn [H_devsum].
    destruct (id_sym (xq_sortQ_P0_id (a :: rest) HS)).
    change (hd 0 (a :: rest)) with a.
    rewrite (qeqT_imp_qeq _ _ (IH HSr)).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_zero _)). ring.
Qed.

Theorem H_shannon_q_P0_zero : forall l : list Q, QeqT (H_devsum (P0 l)) 0.
Proof.
  intro l. apply xq_H_shannon_sortQ. apply xq_P0_sorted.
Qed.

Theorem H_shannon_q_P0_min : forall l : list Q,
  QleT' (H_devsum (P0 l)) (H_devsum l).
Proof.
  intro l. apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (H_shannon_q_P0_zero l)).
  apply QleT'_to_Qle. apply H_shannon_q_nonneg.
Qed.

(* ========== main theorem 5: permutation/cross-phase invariance of the
   frequency counts (in contrast with the sequential entropy)
   ========== *)

Theorem count_val_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> Id (count_val x l) (count_val x p).
Proof.
  intros x l p H.
  apply eq_imp_id.
  induction H; simpl.
  - reflexivity.
  - match goal with
    | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
    end.
    reflexivity.
  - match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E1
    end;
    match goal with
    | [ |- context[Qeq_bool x ?u] ] => destruct (Qeq_bool x u) eqn:E2
    end;
    simpl; try match goal with
                  | [ I : count_val x _ = count_val x _ |- _ ] => rewrite I
                  end; reflexivity.
  - match goal with
    | [ I1 : count_val x ?u = count_val x ?v,
        I2 : count_val x ?v = count_val x ?w |- _ ] =>
        etransitivity; [ exact I1 | exact I2 ]
    end.
Qed.

Theorem count_val_phase_spectrum : forall (x : Q) (l : list Q) (s : nat),
  And (Id (count_val x (P0 l)) (count_val x l))
      (Id (count_val x (Pinf l s)) (count_val x l)).
Proof.
  intros x l s. split.
  - apply eq_imp_id.
    rewrite <- (count_val_perm x l (P0 l) (D5_P0_perm l)). reflexivity.
  - apply eq_imp_id.
    rewrite <- (count_val_perm x l (Pinf l s) (D5_Pinf_perm l s)). reflexivity.
Qed.

(* ========== main theorem 6: the conditional entropy quartet (guarded
   nonnegativity plus counterexamples delimiting scope) ========== *)

Theorem H_cond_self : forall l : list Q, QeqT (H_cond l l) 0.
Proof.
  intro l. apply qeq_imp_qeqT. unfold H_cond. ring.
Qed.

Theorem H_cond_antisym : forall (l ctx : list Q),
  QeqT (H_cond l ctx) (- H_cond ctx l).
Proof.
  intros l ctx. apply qeq_imp_qeqT. unfold H_cond. ring.
Qed.

Theorem H_cond_nonneg_guarded : forall (l ctx : list Q),
  (H_devsum ctx <= H_devsum l)%Q -> QleT' (0) (H_cond l ctx).
Proof.
  intros l ctx H. apply Qle_to_QleT'. unfold H_cond.
  apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
  apply Qle_to_QleT'. exact H.
Qed.

