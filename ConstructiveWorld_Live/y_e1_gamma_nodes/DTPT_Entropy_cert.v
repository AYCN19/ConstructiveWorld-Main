(* ConstructiveWorld-Main - DTPT_Entropy_cert: R2 numerical-certificate face of the multi-entropy family. *)
(** * DTPT_Entropy_cert.

    Mission.  The numerical check instances (vm_compute-verified value lemmas and the
      four constructive counterexample theorems) relocated whole (statement + proof
      body verbatim) out of the lint pieces per the R2 certificate-separation rule.
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing;
      S02_CauchyComplete; all sibling pieces DTPT_Entropy_a..DTPT_Entropy_m.
    References.  Boxed face ConstructiveWorld_Live/DTPT_Entropy.v; seat_wash80 setlive cast.
    Constructivity.  Zero axioms, nothing left open; statements Set-carried; proofs close
      with Qed (vm_compute is reduction machinery, not an axiom source).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g DTPT_Entropy_h DTPT_Entropy_i DTPT_Entropy_j DTPT_Entropy_k DTPT_Entropy_l DTPT_Entropy_m.

(* unconditional nonnegativity is false: conditioning an empty list on a
   high-entropy context gives H_cond = -2 < 0 *)
Theorem H_cond_neg_counterex :
  sigT (fun l : list Q => sigT (fun ctx : list Q => QltT (H_cond l ctx) 0)).
Proof.
  apply (existT _ []). apply (existT _ [5; 3]). apply Qlt_to_QltT.
  unfold H_cond. vm_compute. reflexivity.
Qed.

(* concrete value face (closed by [vm_compute]; used in the counterexample
   rewrites) *)
Lemma H_freq_01_val : QeqT (H_freq [0;1]) (1#2)%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma H_freq_0_val : QeqT (H_freq [0]) 0%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

Lemma H_freq_app_eq_rhs_val : QeqT ((qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat) * H_freq [0;1]
  + (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat) * H_freq [1;1]
  + 2 * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
      * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
  - (qn (nsum (fun x => freq_q x [1;1]) [0;1])
     + qn (nsum (fun x => freq_q x [0;1]) [1;1]))
    / (qn (length [0;1] + length [1;1])%nat
       * qn (length [0;1] + length [1;1])%nat)) ((3#8)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma H_freq_app_eq_val : QeqT (H_freq ([0;1] ++ [1;1])) (3#8)%Q.
Proof. apply qeq_imp_qeqT. unfold H_freq. vm_compute. reflexivity. Qed.

(* [H_freq] is not monotone under concatenation: adding one distinct
   element increases the entropy (0 < H_freq [0;1] = 1/2 collides with the
   assumed 1/2 <= 0) *)
Lemma H_freq_app_mono_false :
  Not (forall l1 l2 : list Q, QleT' (H_freq (l1 ++ l2)) (H_freq l1)).
Proof.
  intro H. specialize (H [0] [1]). apply QleT'_to_Qle in H.
  assert (Hn : H_freq ([0] ++ [1]) == H_freq [0;1]) by reflexivity.
  rewrite Hn in H. rewrite (qeqT_imp_qeq _ _ H_freq_01_val) in H.
  rewrite (qeqT_imp_qeq _ _ H_freq_0_val) in H.
  assert (Hgt : 0%Q < (1#2)%Q) by (unfold Qlt; simpl; lia).
  exact (False_rect Empty_set
    (Qlt_irrefl 0%Q (Qlt_le_trans 0%Q (1#2)%Q 0%Q Hgt H))).
Qed.

(* [H_devsum] recursively takes a suffix minimum along the list
   (hd 0 (P0 l)), so a permutation changes the suffix structure.
   A constructive counterexample replaces the original claim below. *)
Theorem H_shannon_q_perm_inv_counterex :
  sigT (fun l : list Q => sigT (fun p : list Q =>
    And (Permutation l p) (Not (Id (H_devsum l) (H_devsum p))))).
Proof.
  apply (existT _ [3; 1; 2]). apply (existT _ [2; 1; 3]). split.
  - apply perm_trans with (l' := [1; 3; 2]).
    + apply perm_swap.
    + apply perm_trans with (l' := [1; 2; 3]).
      * apply perm_skip. apply perm_swap.
      * apply perm_swap.
  - intro Hc. vm_compute in Hc. inversion Hc.
Qed.

(* the converse is false: the ascending list [1;2] has zero Shannon
   deviation but multiset entropy = 2 <> 1 *)
Theorem Hshannon0_not_Hms1_counterex :
  And (QeqT (H_devsum [1; 2]) 0) (Not (QeqT (H_ms [1; 2]) 1)).
Proof.
  split.
  - apply qeq_imp_qeqT. vm_compute. reflexivity.
  - intro Hc. apply (False_rect Empty_set). apply qeqT_imp_qeq in Hc.
    unfold H_ms in Hc. vm_compute in Hc. discriminate Hc.
Qed.

Lemma collide_01_val : QeqT (collide [0;1]) (1#2)%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

Lemma collide_0_val : QeqT (collide [0]) 1%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

Lemma collide_app_eq_rhs_val : QeqT ((qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [0;1]) / qn (length [0;1] + length [1;1])%nat) * collide [0;1]
  + (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat)
    * (qn (length [1;1]) / qn (length [0;1] + length [1;1])%nat) * collide [1;1]
  + (qn (nsum (fun x => freq_q x [1;1]) [0;1])
     + qn (nsum (fun x => freq_q x [0;1]) [1;1]))
    / (qn (length [0;1] + length [1;1])%nat
       * qn (length [0;1] + length [1;1])%nat)) ((5#8)%Q).
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma collide_app_eq_val : QeqT (collide ([0;1] ++ [1;1])) (5#8)%Q.
Proof. apply qeq_imp_qeqT. unfold collide. vm_compute. reflexivity. Qed.

(* [collide] has no directed monotonicity under concatenation: adding a
   distinct element to an all-equal list decreases the collision entropy
   (the assumed 1 <= 1/2 collides with 1/2 < 1) *)
Lemma collide_app_mono_false :
  Not (forall l1 l2 : list Q, QleT' (collide l1) (collide (l1 ++ l2))).
Proof.
  intro H. specialize (H [0] [1]). apply QleT'_to_Qle in H.
  assert (Hn : collide ([0] ++ [1]) == collide [0;1]) by reflexivity.
  rewrite Hn in H. rewrite (qeqT_imp_qeq _ _ collide_01_val) in H.
  rewrite (qeqT_imp_qeq _ _ collide_0_val) in H.
  assert (Hlt : (1#2)%Q < 1%Q) by (unfold Qlt; simpl; lia).
  exact (False_rect Empty_set
    (Qlt_irrefl 1%Q (Qle_lt_trans 1%Q (1#2)%Q 1%Q H Hlt))).
Qed.

(* executable contrast anchor: [1;2] is ascending and a zero locus of the
   placeholder entropy, yet not a constant list — a constructive witness
   that the zero loci of the two entropies differ *)
Theorem zero_locus_contrast_sorted_not_const :
  And (SortedQ [1; 2]) (And (QeqT (H_devsum [1; 2]) 0)
    (Not (sigT (fun a : Q => Forall (fun z => z == a) [1; 2])))).
Proof.
  split.
  - apply (sortQ_cons 1 [2]).
    + apply (sortQ_cons 2 []).
      * apply sortQ_nil.
      * apply Forall_nil.
    + apply Forall_cons; [ unfold Qle; simpl; lia | apply Forall_nil ].
  - split.
    + apply qeq_imp_qeqT. vm_compute. reflexivity.
    + intros [a Hfa]. apply (False_rect Empty_set).
      inversion Hfa as [| z1 zs1 Hz1 Hf1]; subst.
      inversion Hf1 as [| z2 zs2 Hz2 Hf2]; subst.
      assert (H12 : (1 == 2)%Q)
        by (apply (Qeq_trans 1 a 2 Hz1 (Qeq_sym 2 a Hz2))).
      vm_compute in H12. discriminate H12.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions H_freq_app_mono_false.
Print Assumptions collide_app_mono_false.
Print Assumptions collide_app_eq_val.
Print Assumptions collide_app_eq_rhs_val.
Print Assumptions H_freq_app_eq_val.
Print Assumptions H_freq_app_eq_rhs_val.