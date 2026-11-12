(* ConstructiveWorld-Main - the endpoint-and-OrgDiff stem of the DTPT base library *)

(** * DTPT_l: the endpoint-and-OrgDiff stem of the DTPT base library (stem L of fourteen).

    Mission.  the M2 merged blocks: the PmidEnd endpoint family (section H, the lambda = length endpoint laws with the firstn_all2/skipn_all2 route) and the OrgDiff closed-form/nonnegativity/absorption family (section I, the collapse semantics, the nonnegativity face, the composition collapse law and its honest counterexample).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f], [DTPT_g], [DTPT_h], [DTPT_i], [DTPT_j], [DTPT_k]

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
Require Import DTPT_k.
(* ========== section H, M2 merged block one: the DTPT_PmidEnd endpoint family (merged) ==========
   the nontrivial endpoint laws of the general Pmid truncation at lambda: at lambda = the list length the three phases degenerate back to P0.
   it repays the registered honest legacy: the notes at DTPT_Dig.v L65-69 and DTPT.v L86 that
   D5_Pmid_perm fails for general lambda - this family completes the lambda = length l endpoint.
   the legacy defect and its fix: the pattern of firstn_all, firstn (length ?l) ?l, fails to unify against
   the goal subterm firstn (length l) (P0 l) (?l would have to be both l and P0 l);
   switch to the premise-carrying forms firstn_all2 / skipn_all2, with the premise supplied by permutation length conservation
   (D5_P0_perm / D5_Pinf_perm + Permutation_length).
   after the merge this family shares the main file: the file header/Require face/
   file-tail self-audit segment of the original DTPT_PmidEnd.v were removed per the merge discipline (self-audit concentrated in the file-tail section J). ========== *)

(* ---------- H.1 the length-conservation premise (permutation implies equal lengths) ---------- *)

Lemma pmid_len_l_eq_P0 : forall l : list Q, length l = length (P0 l).
Proof.
  intros l. exact (Permutation_length (D5_P0_perm l)).
Qed.

Lemma pmid_len_l_eq_Pinf : forall (l : list Q) (s : nat),
  length l = length (Pinf l s).
Proof.
  intros l s. exact (Permutation_length (D5_Pinf_perm l s)).
Qed.

(* ---------- H.2 main theorem: the lambda = length l endpoint (the legacy repayment) ---------- *)

(* the fix of the legacy defect: the pattern of firstn_all, firstn (length ?l) ?l, fails to unify against
   firstn (length l) (P0 l); the explicit-argument order of firstn_all2/skipn_all2 drifts across versions in 9.0 -
   hence apply by unifying the conclusion (immune to argument order) first lands the two equation lemmas,
   and the main theorem only rewrites equations. *)
(* the <= form, premise-independent lemma: rewrite backwards uses the concrete instance (no pattern-variable back-biting loop on the RHS).
   pitfall: rewrite pmid_len_l_eq_P0 (the pattern length ?x) would first bite the length (P0 l) inside the goal
   and rewrite it into length (P0 (P0 l)) - the same family as the S1 card. *)
Lemma pmid_len_l_le_P0 : forall l : list Q,
  (length (P0 l) <= length l)%nat.
Proof.
  intros l. rewrite <- (pmid_len_l_eq_P0 l). apply le_n.
Qed.

Lemma pmid_len_Pinf_le_l : forall (l : list Q) (s : nat),
  (length (Pinf l s) <= length l)%nat.
Proof.
  intros l s. rewrite <- (pmid_len_l_eq_Pinf l s). apply le_n.
Qed.

Lemma pmid_firstn_len : forall l : list Q,
  firstn (length l) (P0 l) = P0 l.
Proof.
  intros l. apply firstn_all2. apply pmid_len_l_le_P0.
Qed.

Lemma pmid_skipn_len : forall (l : list Q) (s : nat),
  skipn (length l) (Pinf l s) = [].
Proof.
  intros l s. apply skipn_all2. apply pmid_len_Pinf_le_l.
Qed.

Theorem Pmid_len_endpoint : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof.
  intros l s. unfold Pmid.
  rewrite pmid_firstn_len. rewrite pmid_skipn_len.
  apply app_nil_r.
Qed.

(* the original name of X1-checklist hotspot 3, an alias piece with the same statement (for easy cross-checking) *)
Corollary Pmid_len_eq_P0 : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof. exact Pmid_len_endpoint. Qed.

Theorem Pmid_len_perm : forall (l : list Q) (s : nat),
  Permutation l (Pmid l s (length l)).
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply D5_P0_perm.
Qed.

(* ---------- H.3 the secondary endpoint: lambda = 0 (the all-Pinf phase, definitional) ---------- *)

Theorem Pmid_zero_endpoint : forall (l : list Q) (s : nat),
  Pmid l s 0 = Pinf l s.
Proof.
  intros l s. unfold Pmid. reflexivity.
Qed.

Theorem Pmid_zero_perm : forall (l : list Q) (s : nat),
  Permutation l (Pmid l s 0).
Proof.
  intros l s. rewrite Pmid_zero_endpoint. apply D5_Pinf_perm.
Qed.

(* ---------- H.4 the equivalent permutation forms, mutual derivation (bonus one) ---------- *)

Theorem Pmid_len_perm_eq : forall (l : list Q) (s : nat),
  Permutation (Pmid l s (length l)) (P0 l).
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply Permutation_refl.
Qed.

Theorem Pmid_len_perm_P0_left : forall (l : list Q) (s : nat),
  Permutation (P0 l) (Pmid l s (length l)).
Proof.
  intros l s. exact (Permutation_sym (Pmid_len_perm_eq l s)).
Qed.

(* ---------- H.5 the length genealogy: at lam <= length l the length = lam + (|l| - lam) (bonus two) ---------- *)

Theorem Pmid_len_spectrum : forall (l : list Q) (s lam : nat),
  (lam <= length l)%nat ->
  length (Pmid l s lam) = (lam + (length l - lam))%nat.
Proof.
  intros l s lam Hlam. unfold Pmid.
  rewrite length_app.
  rewrite pmid_len_l_eq_P0 in Hlam.
  rewrite (firstn_length_le (P0 l) Hlam).
  rewrite (length_skipn _ _).
  rewrite <- (pmid_len_l_eq_Pinf l s).
  reflexivity.
Qed.


(* ========== section I, M2 merged block two: the DTPT_OrgDiff closed-form/nonnegativity/absorption family (merged) ==========
   the X1-checklist hotspot 7 [ORG] upgrade + the U2 legacy repayment (the U15R delivery face).
   merge treatment: the original line Require Import DTPT DTPT_Phases DTPT_PmidEnd was
   deleted wholesale - the Pmid_len_endpoint reference became a direct section-H reference in this file, the P0_idempotent
   reference a direct section-A reference, OrgDiff is defined in section B of this file, and the remaining base modules
   (Pinf/rot/firstn_skipn/C_sorted_min_adj/Qle_0_sub'/xq_minus_self)
   are all in DTPT (required by the file header).
   the realized shape of the base module: OrgDiff l s := H_adj (Pinf l s) - H_adj (P0 l) (section B);
   Pinf l s = rot (S s) l = firstn (S s) l ++ skipn (S s) l = l
   (firstn_skipn), so the realized OrgDiff = H_adj l - H_adj (P0 l). ========== *)

(* ---------- I.1 the U2 legacy: the lam = |l| endpoint of P0 absorbing Pmid ---------- *)

(* the organizational fixed point swallows the full-length endpoint of the general lambda truncation:
   rewrite Pmid_len_endpoint (section H of this file), then
   apply P0_idempotent (section A of this file) - two steps. *)
Theorem P0_absorbs_Pmid_len : forall (l : list Q) (s : nat),
  P0 (Pmid l s (length l)) = P0 l.
Proof.
  intros l s. rewrite Pmid_len_endpoint. apply P0_idempotent.
Qed.

(* ---------- I.2 ORG-1, the closed form: the collapse semantics of OrgDiff, registered ---------- *)

(* the 'semantics not registered' of the X1 face-4 evidence is registered here: the Pinf slot is the identity rotation,
   and the organizational difference depends only on the gap between the original order of l and its organizational canonical form. *)
Theorem OrgDiff_eq : forall (l : list Q) (s : nat),
  OrgDiff l s == H_adj l - H_adj (P0 l).
Proof.
  intros l s. unfold OrgDiff. unfold Pinf, rot.
  rewrite firstn_skipn. reflexivity.
Qed.

(* ---------- I.3 ORG-1, the nonnegativity form: organizational differences are always nonnegative ---------- *)

(* a one-step corollary of P0 minimizing the adjacent-difference entropy (C_sorted_min_adj):
   0 <= H_adj l - H_adj (P0 l), read backwards via Qle_0_sub', is exactly C_sorted_min_adj l. *)
Theorem OrgDiff_nonneg : forall (l : list Q) (s : nat),
  (0 <= OrgDiff l s)%Q.
Proof.
  intros l s. unfold OrgDiff. unfold Pinf, rot. rewrite firstn_skipn.
  exact (proj1 (Qle_0_sub' (H_adj (P0 l)) (H_adj l)) (C_sorted_min_adj l)).
Qed.

(* the decidable comparison certificate: the boolean readback of nonnegativity (the Qle_bool computational face) *)
Theorem OrgDiff_nonneg_dec : forall (l : list Q) (s : nat),
  Qle_bool 0 (OrgDiff l s) = true.
Proof.
  intros l s. apply (proj2 (Qle_bool_iff 0 (OrgDiff l s))).
  apply OrgDiff_nonneg.
Qed.

(* ---------- I.4 ORG-2, the composition face: the Pmid endpoint composition collapse law ---------- *)

(* composition with the phase operator Pmid (the provable direction): at the lambda = |l| endpoint the truncated sequence
   is already the organizational canonical form, and the organizational difference collapses to zero - the entropy load of the I.1 absorption law. *)
Theorem OrgDiff_Pmid_len_zero : forall (l : list Q) (s t : nat),
  OrgDiff (Pmid l s (length l)) t == 0.
Proof.
  intros l s t. unfold OrgDiff. unfold Pinf, rot.
  rewrite firstn_skipn. rewrite Pmid_len_endpoint.
  rewrite P0_idempotent. apply xq_minus_self.
Qed.

(* the honest obstacle: the composition collapse for general lam is false. counterexample l=[2;0;3;1], s=0, lam=2:
   Pmid = firstn 2 (P0 l) ++ skipn 2 l = [0;1] ++ [3;1] = [0;1;3;1],
   H_adj = 1+2+2 = 5 while H_adj (P0 [0;1;3;1]) = 1+0+2 = 3, the difference = 2 <> 0.
   a constructive counterexample node, demarcating the scope of the I.4 collapse law (collapse only at the lambda in {0, |l|} endpoints). *)
Lemma OrgDiff_Pmid_general_nonzero :
  ~ (forall (l : list Q) (s lam t : nat), OrgDiff (Pmid l s lam) t == 0).
Proof.
  intro H. specialize (H [2;0;3;1] 0%nat 2%nat 0%nat).
  cbv in H. congruence.
Qed.

