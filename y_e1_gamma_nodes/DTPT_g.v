(* ConstructiveWorld-Main - the LLM mapping-layer stem of the DTPT base library *)

(** * DTPT_g: the LLM mapping-layer stem of the DTPT base library (stem G of fourteen).

    Mission.  merged block S1, the LLM mapping layer: generic firstn/skipn helpers, the interleave structure theorem, the gate_pass behavior family, the rot cyclic-rotation theory, the Pmid endpoint degeneration faces, and the Tex/Tabs semantic bridge.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f]

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
(* ============================================================
   merged block S1 (section 11): the merge of DTPT_LLM.v - the LLM mapping-layer theorem family
   source piece DTPT-S4 (interleave/gate_pass/rot cyclic rotation/Pmid endpoints/
   the Tex/Tabs semantic bridge/the gate_pass behavior family). Only the standalone-file Require/
   Import/Open Scope headers and the Module shell lines (carried uniformly by this file's header)
   were peeled off; comments, all proof bodies and the Qed face are zero-change verbatim migrations.
   ============================================================ *)

(* ========== section 0: generic list helpers (firstn/skipn boundary lemmas) ========== *)

(* when n is not shorter than the list length, firstn takes the whole list *)
Lemma llm_firstn_ge_full : forall (n : nat) (l : list Q),
  (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n as [| n IH]; intros [| x xs] H; simpl in *.
  - reflexivity.
  - inversion H.
  - reflexivity.
  - rewrite IH by lia. reflexivity.
Qed.

(* when n is not shorter than the list length, skipn takes the empty list *)
Lemma llm_skipn_ge_nil : forall (n : nat) (l : list Q),
  (length l <= n)%nat -> skipn n l = [].
Proof.
  induction n as [| n IH]; intros [| x xs] H; simpl in *.
  - reflexivity.
  - inversion H.
  - reflexivity.
  - apply IH. lia.
Qed.

(* ========== section A: the interleave structure theorem (floor piece) ========== *)

Theorem llm_interleave_length : forall l1 l2 : list Q,
  length (interleave l1 l2) = (length l1 + length l2)%nat.
Proof.
  induction l1 as [| x xs IH]; intros l2.
  - simpl. reflexivity.
  - destruct l2 as [| y ys]; simpl; rewrite ?IH; lia.
Qed.

Theorem llm_interleave_perm : forall l1 l2 : list Q,
  Permutation (interleave l1 l2) (l1 ++ l2).
Proof.
  induction l1 as [| x xs IH]; intros l2.
  - simpl. apply Permutation_refl.
  - destruct l2 as [| y ys].
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + simpl. apply perm_skip.
      etransitivity.
      * apply Permutation_cons_append.
      * etransitivity.
        -- apply Permutation_app_tail. apply IH.
        -- rewrite <- app_assoc. apply Permutation_app_head.
           exact (Permutation_sym (Permutation_cons_append ys y)).
Qed.

(* ========== section B: the gate_pass behavior theorem (floor piece) ========== *)

(* the boolean reflection bridge of the pass criterion: gate_pass = true exactly when H <= threshold *)
Theorem llm_gate_pass_iff : forall (t H : Q),
  gate_pass t H = true <-> (H <= t)%Q.
Proof.
  intros t H. unfold gate_pass. split.
  - intro Hp. destruct (Qle_bool H t) eqn:E.
    + apply (proj1 (Qle_bool_iff H t)). exact E.
    + discriminate Hp.
  - intro Hle. rewrite (proj2 (Qle_bool_iff H t) Hle). reflexivity.
Qed.

(* the fail criterion: gate_pass = false exactly when threshold < H *)
Theorem llm_gate_pass_false_iff : forall (t H : Q),
  gate_pass t H = false <-> (t < H)%Q.
Proof.
  intros t H. unfold gate_pass. split.
  - intro Hp. destruct (Qle_bool H t) eqn:E.
    + discriminate Hp.
    + unfold Qle_bool in E. apply Z.leb_gt in E. unfold Qlt. exact E.
  - intro Hlt. destruct (Qle_bool H t) eqn:E.
    + exfalso. apply (Qlt_irrefl H). apply (Qle_lt_trans H t H).
      * apply (proj1 (Qle_bool_iff H t)). exact E.
      * exact Hlt.
    + reflexivity.
Qed.

(* threshold monotonicity: relaxing the threshold does not change those already passed *)
Theorem llm_gate_pass_mono_thr : forall (H t1 t2 : Q), (t1 <= t2)%Q ->
  gate_pass t1 H = true -> gate_pass t2 H = true.
Proof.
  intros H t1 t2 Hle Hp.
  apply (proj2 (llm_gate_pass_iff t2 H)).
  apply (Qle_trans H t1 t2).
  - apply (proj1 (llm_gate_pass_iff t1 H)). exact Hp.
  - exact Hle.
Qed.

(* criterion-value antitonicity: the smaller the value, the easier to pass *)
Theorem llm_gate_pass_anti_H : forall (H1 H2 t : Q), (H1 <= H2)%Q ->
  gate_pass t H2 = true -> gate_pass t H1 = true.
Proof.
  intros H1 H2 t Hle Hp.
  apply (proj2 (llm_gate_pass_iff t H1)).
  apply (Qle_trans H1 H2 t).
  - exact Hle.
  - apply (proj1 (llm_gate_pass_iff t H2)). exact Hp.
Qed.

(* ========== section C: the rot cyclic-rotation theory (main piece) ========== *)

(* key finding: the on-disc rot is defined in the firstn ++ skipn order and the identity is provable -
   rot is a 'cut-and-reattach' reconstruction for every n, i.e. rot n l = l holds unconditionally.
   the genuine cyclic rotation (the skipn ++ firstn order) gets its own permutation and length theory. *)
Theorem llm_rot_id : forall (n : nat) (l : list Q), rot n l = l.
Proof.
  intros n. unfold rot.
  (* caliber three, structural derivation: a complete induction on the cut depth + constructor-wise reduction over the list constructors,
     replacing the original one-hop forwarding to the concatenation case-split library lemma *)
  induction n as [| n IHn]; intro l.
  - (* zero cut: the head and tail segments both reduce back to the original list *)
    reflexivity.
  - destruct l as [| x xs].
    + (* cut depth beyond the list length: the concatenation of two empty lists is still empty *)
      reflexivity.
    + (* head-element position kept: after the cons reduction of the single-element concatenation, the IH closes *)
      cbn [firstn skipn].
      change ((x :: firstn n xs) ++ skipn n xs)
        with (x :: (firstn n xs ++ skipn n xs)).
      rewrite IHn. reflexivity.
Qed.

Theorem llm_rot_full : forall l : list Q, rot (length l) l = l.
Proof.
  intros l. exact (llm_rot_id (length l) l).
Qed.

(* the cyclic inverse form: rot (length l - n) (rot n l) = l (n <= length l) *)
Theorem llm_rot_cyclic_inv : forall (n : nat) (l : list Q),
  (n <= length l)%nat -> rot (length l - n) (rot n l) = l.
Proof.
  intros n l Hn. rewrite !llm_rot_id. reflexivity.
Qed.

(* the genuine cyclic rotation skipn n l ++ firstn n l is a permutation of l *)
Theorem llm_rot_cyclic_perm : forall (n : nat) (l : list Q),
  Permutation (skipn n l ++ firstn n l) l.
Proof.
  intros n l. etransitivity.
  - apply Permutation_app_comm.
  - rewrite firstn_skipn. apply Permutation_refl.
Qed.

Theorem llm_rot_cyclic_length : forall (n : nat) (l : list Q),
  length (skipn n l ++ firstn n l) = length l.
Proof.
  intros n l. exact (Permutation_length (llm_rot_cyclic_perm n l)).
Qed.

(* ========== section D: Pmid endpoint degeneration (main piece) ========== *)

Theorem llm_P0_length : forall l : list Q, length (P0 l) = length l.
Proof.
  intros l. symmetry. apply (Permutation_length (D5_P0_perm l)).
Qed.

Theorem llm_Pinf_length : forall (l : list Q) (s : nat),
  length (Pinf l s) = length l.
Proof.
  intros l s. unfold Pinf, rot. rewrite firstn_skipn. reflexivity.
Qed.

(* endpoint lam = 0: Pmid degenerates to Pinf *)
(* [deprecation note] over the base module where rot = firstn ++ skipn is an identity, this piece degenerates to a disguised identity corollary; the operational semantics live in the truthification layer DTPT_ROTC / DTPT_Cyc / DTPT_RotSpec. *)
Theorem llm_Pmid_zero : forall (l : list Q) (s : nat), Pmid l s 0 = Pinf l s.
Proof.
  intros l s. unfold Pmid, Pinf, rot. exact (@eq_refl _ (firstn (Datatypes.S s) l ++ skipn (Datatypes.S s) l)).
Qed.

(* endpoint lam = length l: Pmid degenerates to P0 *)
Theorem llm_Pmid_len_endpoint : forall (l : list Q) (s : nat),
  Pmid l s (length l) = P0 l.
Proof.
  intros l s. unfold Pmid, Pinf, rot.
  rewrite firstn_skipn.
  assert (HP : length (P0 l) = length l)
    by (symmetry; apply (Permutation_length (D5_P0_perm l))).
  assert (H1 : firstn (length l) (P0 l) = P0 l).
  { apply llm_firstn_ge_full. rewrite HP. apply le_n. }
  assert (H2 : skipn (length l) l = []).
  { apply llm_skipn_ge_nil. apply le_n. }
  rewrite H1, H2, app_nil_r. reflexivity.
Qed.

(* endpoint lam >= length l: Pmid is constantly P0 *)
Theorem llm_Pmid_full : forall (l : list Q) (s lam : nat),
  (length l <= lam)%nat -> Pmid l s lam = P0 l.
Proof.
  intros l s lam Hlen. unfold Pmid, Pinf, rot.
  rewrite firstn_skipn.
  assert (HP : length (P0 l) = length l)
    by (symmetry; apply (Permutation_length (D5_P0_perm l))).
  assert (H1 : firstn lam (P0 l) = P0 l).
  { apply llm_firstn_ge_full. rewrite HP. exact Hlen. }
  assert (H2 : skipn lam l = []).
  { apply llm_skipn_ge_nil. exact Hlen. }
  rewrite H1, H2, app_nil_r. reflexivity.
Qed.

(* ========== section E: the Tex/Tabs semantic bridge (bonus item) ========== *)

(* Tex is the fiber of TrNode over phi (a subtype): any node with trPhi t = phi
   can be lifted to a Tex witness, and the projection preserves the trace *)
Theorem llm_Tex_fiber : forall (phi : Dig) (t : TrNode),
  trPhi t = phi -> exists T : Tex phi, projT1 T = t.
Proof.
  intros phi t H. exists (existT _ t H). reflexivity.
Qed.

Theorem llm_Tex_fiber_inv : forall (phi : Dig) (T : Tex phi),
  trPhi (projT1 T) = phi.
Proof.
  intros phi T. destruct T as [t H]. exact H.
Qed.

(* Tabs always has an implementation (the constant-evidence family): the abstract face can be instantiated at any phi *)
Theorem llm_Tabs_const : forall phi : Dig, Tabs phi.
Proof.
  intros phi.
  (* caliber two, explicit construction: unfold the truth-carrier type aliases and give the witness function verbatim -
     drop the constant evidence node evNum zero for any model slot *)
  unfold Tabs.
  exact (fun _ : Dig => evNum 0%Q).
Qed.

(* the canonical bridge: the Tex witness induces the canonical evidence function on Tabs, taking node values pointwise *)
Definition llm_canon_tab (phi : Dig) (T : Tex phi) : Tabs phi :=
  fun _ => trValue (projT1 T).

Theorem llm_canon_tab_eval : forall (phi : Dig) (T : Tex phi) (m : Dig),
  llm_canon_tab phi T m = trValue (projT1 T).
Proof.
  intros phi T m.
  (* derivation chain (caliber one): after unfolding the canonical bridge definition body (delta), do
     an inverted-tower reduction (beta) on the model argument; both projection sides close in the same shape *)
  change (llm_canon_tab phi T m) with (trValue (projT1 T)).
  reflexivity.
Qed.

(* layer composition: the LLM phase-view gate criterion is an instance of llm_gate_pass_iff *)
Theorem llm_view_gate_iff : forall (v : LLMPhaseView) (H : Q),
  gate_pass (gate_threshold v) H = true <-> (H <= gate_threshold v)%Q.
Proof.
  intros v H. apply llm_gate_pass_iff.
Qed.

