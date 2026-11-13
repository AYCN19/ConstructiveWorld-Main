(* ConstructiveWorld-Main - the truthification-and-audit stem of the DTPT base library *)

(** * DTPT_n: the truthification-and-audit stem of the DTPT base library (stem N of fourteen).

    Mission.  results segment F4: the AUDIT-2 class-C deep-water truthification (section 16, the OrgDiff s-irrelevance theorem, the three LLMPhaseView theoremizations, the Tex_of_Tabs premise theoremization), the merged-block retirement records, and the replacement-piece assumption prints.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e], [DTPT_f], [DTPT_g], [DTPT_h], [DTPT_i], [DTPT_j], [DTPT_k], [DTPT_l], [DTPT_m]

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
Require Import DTPT_l.
Require Import DTPT_m.
(* ============================================================
   section 16, results segment F4: the AUDIT-2 audit class-C deep-water truthification (append-style)
   targets (section three class C + section four F8 of the trivial-placeholder audit and new-results checklist):
     - C5/F8 floor: the zero consumption of the s argument of OrgDiff - upgrading 'unused argument' to
       an 'explicit irrelevance theorem' (a placeholder-nature proof), not the delete-argument route (deleting the argument
       would touch the section-B definition body and all its dependency points; the ADJ-2 precedent is a source-edit action;
       here we take the append-style evidence route: preparing the supply piece for a later argument deletion;
       phase_classify_lam_const keeps its name slot in the same-source format);
     - C2 main piece: three truthification pieces over the theorem-free face of LLMPhaseView (the section-7 record) -
       the projection-equation face / the view-vs-phase-decider agreement face (phase_classify is a native
       dependency, with zero overlap with the bridge lemmas P3-B10/P3-B11) / the constructive round-trip face;
     - bonus: the theoremization of the ever-true premise of Tex_of_Tabs - the audited 'premise always true'
       upgraded to an explicit theorem (the premise discharged by instantiating the registered llm_Tabs_const).
   discipline: pure append, zero retirements, zero changes to existing pieces; all Qed; the dependent pieces are all the active names of
   sections A-J and sections 7/14 (phase_classify_P0_spec / llm_view_gate_iff /
   llm_Tabs_const / Tex_of_Tabs / P0_idempotent / Qle_refl).
   ============================================================ *)

(* ---------- section 16.1, floor (C5/F8): the irrelevance theorem of the lazy s argument of OrgDiff ---------- *)

(* the C5 audit verbatim: the laziness of the s argument is already theoremized (OrgDiff_eq is universal in s),
   but 's is lazy' itself had not been upgraded to a theorem. this piece is that upgrade: OrgDiff is constant in s
   universally - s is an essentially lazy argument, not a defect (a direct semantic consequence of the identity
   rotation firstn_skipn of the Pinf slot; depends on the section-I.2 closed form OrgDiff_eq). *)
Theorem OrgDiff_s_irrelevant : forall (l : list Q) (s t : nat),
  OrgDiff l s == OrgDiff l t.
Proof.
  intros l s t.
  rewrite (OrgDiff_eq l s). rewrite (OrgDiff_eq l t).
  reflexivity.
Qed.

(* the dependency face (established dependencies): composed with the section-I.3 nonnegativity into the s-independent
   nonnegativity-transport corollary - the nonnegativity at any s slot migrates for free, along the lazy argument, to any t slot. *)
Corollary OrgDiff_nonneg_transport : forall (l : list Q) (s t : nat),
  (0 <= OrgDiff l s)%Q -> (0 <= OrgDiff l t)%Q.
Proof.
  intros l s t H.
  rewrite <- (OrgDiff_s_irrelevant l s t).
  exact H.
Qed.

(* ---------- section 16.2, main piece (C2): the three theoremizations of LLMPhaseView ----------
   the C2 audit verbatim: the only theorem of LLMPhaseView is llm_view_gate_iff (section 11,
   pure packaging); the two fields lam_param/phase_marker have zero theorems and zero consumption. this section upgrades
   the record level to three theorem faces. the canonical constructor llm_view_of is a new definition
   (zero changes to existing pieces); its three fields take the active P0-phase construction: the lambda slot = the threshold slot =
   H_adj (P0 l), the marker slot = P0 l - all three fields with active semantics, zero fabrication. *)

(* ---------- 16.2a the projection-equation face: constructor field equations + the record eta ---------- *)

(* the three constructor field projection equations: the left-inverse property of mkLLMView against the three projections *)
Theorem llm_view_mk_proj : forall (lam : Q) (mk : list Q) (gt : Q),
  lam_param (mkLLMView lam mk gt) = lam /\
  phase_marker (mkLLMView lam mk gt) = mk /\
  gate_threshold (mkLLMView lam mk gt) = gt.
Proof.
  intros lam mk gt. split; [reflexivity |]. split; reflexivity.
Qed.

(* the record eta: the view is uniquely determined by its three projections (records carry no hidden state) *)
Theorem llm_view_eta : forall v : LLMPhaseView,
  mkLLMView (lam_param v) (phase_marker v) (gate_threshold v) = v.
Proof.
  intros v. destruct v as [lam mk gt]. reflexivity.
Qed.

(* ---------- 16.2b the view-vs-phase-decider agreement face (the native phase_classify dependency) ---------- *)

(* the canonical view: minted from (list, seed). all three fields land on the active faces of sections A/B. *)
Definition llm_view_of (l : list Q) (s : nat) : LLMPhaseView :=
  mkLLMView (H_adj (P0 l)) (P0 l) (H_adj (P0 l)).

Lemma llm_view_of_marker : forall (l : list Q) (s : nat),
  phase_marker (llm_view_of l s) = P0 l.
Proof.
  intros l s.
  (* derivation chain (caliber one): after unfolding the view constructor take the marker-slot projection, reducing layer by layer
     to land the insertion-sort image *)
  change (phase_marker (llm_view_of l s)) with (P0 l).
  reflexivity.
Qed.

Lemma llm_view_of_gate : forall (l : list Q) (s : nat),
  gate_threshold (llm_view_of l s) == H_adj (P0 l).
Proof.
  intros l s.
  (* derivation chain (caliber one): after unfolding the view constructor take the threshold-slot projection, closing by the
     same-source reduction as the marker entropy slot *)
  change (gate_threshold (llm_view_of l s)) with (H_adj (P0 l)).
  reflexivity.
Qed.

(* the self-consistency face (unconditional): the lambda slot = the threshold slot = the marker entropy - the three fields of
   the canonical view share one semantics, with the threshold exactly at the marker entropy (the Qle_refl boundary). *)
Theorem llm_view_self_consistent : forall (l : list Q) (s : nat),
  lam_param (llm_view_of l s) == gate_threshold (llm_view_of l s) /\
  H_adj (phase_marker (llm_view_of l s)) == gate_threshold (llm_view_of l s) /\
  (gate_threshold (llm_view_of l s) <= gate_threshold (llm_view_of l s))%Q.
Proof.
  intros l s. split; [reflexivity |]. split.
  - rewrite llm_view_of_marker, llm_view_of_gate. reflexivity.
  - apply Qle_refl.
Qed.

(* agreement face 1 (the P0 branch): the decider judges P0 implies the two canonical-view fields numerically coincide with
   the Pmid-0 slot entropy - depends on the section-G.6 phase_classify_P0_spec (a native piece, zero overlap with the bridge lemmas). *)
Theorem llm_view_PhP0_consistent : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 ->
  gate_threshold (llm_view_of l s) == H_adj (Pmid l s 0) /\
  H_adj (phase_marker (llm_view_of l s)) == H_adj (Pmid l s 0).
Proof.
  intros l s H.
  assert (Hs := phase_classify_P0_spec l s H).
  split.
  - rewrite llm_view_of_gate. exact Hs.
  - rewrite llm_view_of_marker. exact Hs.
Qed.

(* agreement face 2 (the P0 branch, the gate behavior): the decider judges P0 implies the canonical view's gate lets the Pmid-0
   slot entropy through - the gate criterion goes through the registered llm_view_gate_iff on the numeric face, and the
   nonnegativity transport closes by Qeq reflexivity. honest caliber: Qeq_bool/Qle_bool are both record-level comparisons,
   hence the agreement faces are stated with numeric ==/<= (the section-G.6 caliber). *)
Theorem llm_view_PhP0_gate_exact : forall (l : list Q) (s : nat),
  phase_classify l s = PhP0 ->
  gate_pass (gate_threshold (llm_view_of l s)) (H_adj (Pmid l s 0)) = true.
Proof.
  intros l s H.
  assert (Hs := phase_classify_P0_spec l s H).
  apply (proj2 (llm_view_gate_iff (llm_view_of l s) (H_adj (Pmid l s 0)))).
  rewrite llm_view_of_gate. rewrite Hs. apply Qle_refl.
Qed.

(* ---------- 16.2c the view-construction round-trip face ---------- *)

(* round trip 1 (general form): construction -> projection -> reconstruction = identity (the constructor instance of eta) *)
Theorem llm_view_roundtrip : forall (lam : Q) (mk : list Q) (gt : Q),
  mkLLMView (lam_param (mkLLMView lam mk gt))
            (phase_marker (mkLLMView lam mk gt))
            (gate_threshold (mkLLMView lam mk gt)) = mkLLMView lam mk gt.
Proof.
  intros lam mk gt.
  (* derivation chain (caliber one): each of the three projections unfolds the record constructor and retrieves the original interface arguments,
     reducing layer by layer to close in the same shape as the original record *)
  change (mkLLMView (lam_param (mkLLMView lam mk gt))
                    (phase_marker (mkLLMView lam mk gt))
                    (gate_threshold (mkLLMView lam mk gt)))
    with (mkLLMView lam mk gt).
  reflexivity.
Qed.

(* round trip 2 (the canonical-view marker fixed point): re-minting the canonical view's marker yields the same
   view - the view-level payload of the P0 idempotence law (section-14 section-A P0_idempotent):
   the organizational canonical form is a fixed point of view minting. *)
Theorem llm_view_of_roundtrip : forall (l : list Q) (s : nat),
  llm_view_of (phase_marker (llm_view_of l s)) s = llm_view_of l s.
Proof.
  intros l s.
  rewrite llm_view_of_marker. unfold llm_view_of.
  rewrite P0_idempotent. reflexivity.
Qed.

(* ---------- section 16.3, bonus: the theoremization of the ever-true premise of Tex_of_Tabs ----------
   audited and on record: the premise (forall m', Evidence) of Tex_of_Tabs (section E) is always true -
   the registered llm_Tabs_const (section 11) already provides the constant-evidence family. truthification = upgrading 'always true'
   from an audit note to an explicit theorem: the premise is discharged by instantiating the registered piece, giving the unconditional form;
   plus a constructive witness (the minted node is verbatim readable) and the inhabitance corollary. *)

(* the theoremization of the ever-true premise: the unconditional simplification face of Tex_of_Tabs after its premise is
   discharged by instantiating llm_Tabs_const - Tex phi is constructible at every phi, with no premise at all. *)
Theorem Tex_of_Tabs_premise_trivial : forall (phi m : Dig), Tex phi.
Proof.
  intros phi m. exact (Tex_of_Tabs phi m (llm_Tabs_const phi)).
Qed.

(* the constructive witness: the witness node of the unconditional form registered verbatim (the Lv0 level,
   the constant evidence evNum 0) - 'always true' turns from a note into a checkable constructive object. *)
Theorem Tex_of_Tabs_premise_trivial_witness : forall (phi m : Dig),
  exists T : Tex phi, projT1 T = mkTrNode Lv0 phi m (evNum 0%Q).
Proof.
  intros phi m.
  exists (existT _ (mkTrNode Lv0 phi m (evNum 0%Q)) (eq_refl phi)).
  reflexivity.
Qed.

(* the inhabitance corollary: the Tex fiber is nonempty over the whole domain (model-selection independence -
   any Dig can serve as the model slot of the witness node). *)
Corollary Tex_inhabited : forall phi : Dig, Tex phi.
Proof.
  intros phi. exact (Tex_of_Tabs_premise_trivial phi (dQ 0%Q)).
Qed.

(* ---------- section 16.4, final audit: Print Assumptions (the G4 gate) ---------- *)

Print Assumptions OrgDiff_s_irrelevant.
Print Assumptions OrgDiff_nonneg_transport.
Print Assumptions llm_view_mk_proj.
Print Assumptions llm_view_eta.
Print Assumptions llm_view_self_consistent.
Print Assumptions llm_view_PhP0_consistent.
Print Assumptions llm_view_PhP0_gate_exact.
Print Assumptions llm_view_roundtrip.
Print Assumptions llm_view_of_roundtrip.
Print Assumptions Tex_of_Tabs_premise_trivial.
Print Assumptions Tex_of_Tabs_premise_trivial_witness.
Print Assumptions Tex_inhabited.


(* ============================================================
   merged block M1 retirement record: DTPT_Dig.v - not merged, retired directly
   the basis of the ruling: all of its declarations (Inductive Dig, insert_q, P0, rot, Pinf,
   Pmid, insert_q_perm_cons, D5_P0_perm, D5_Pinf_perm) repeat this file's
   sections 1-3 verbatim; its only unique content is comments (the Pmid endpoint legacy note has been repaid by
   DTPT_PmidEnd.v). the source piece is retained as a .retired_-prefixed snapshot.
   ============================================================ *)

(* ============================================================
   merged block S2 retirement record: DTPT_CoZero.v / DTPT_Phases.v
   - merged into sections 13/14 of this file and then retired; zero consumers in the main tree (the downstream of Phases,
   OrgDiff, had been merged into Phases itself earlier in M2; a workspace-wide grep finds no Require/Import
   residue); both source pieces are retained as .retired_S2-prefixed snapshots.
   ============================================================ *)

(* ========== slice-replacement appendix: the replacement-piece assumption-closure prints (the G4 face) ========== *)

Print Assumptions llm_rot_id.
Print Assumptions insert_q_cons_eq.
Print Assumptions sum_adjdiff_single.
Print Assumptions llm_Tabs_const.
Print Assumptions llm_view_roundtrip.
