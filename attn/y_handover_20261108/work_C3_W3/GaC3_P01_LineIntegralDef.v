(* ===================================================================== *)
(* GaC3_P01_LineIntegralDef.v                                             *)
(*                                                                       *)
(* Mission: construction slices 1-2 of node C3-P01 (segment C3 wave W1   *)
(*   chain head) - the definition layer of the line integral.  Slice 1   *)
(*   carries the Q-partition step-sum base case of the Riemann-type      *)
(*   segment integral: complex-valued Q-step data on a real interval,    *)
(*   the weighted Q sums (real/imaginary parts), the constant-integrand  *)
(*   refinement-invariance base block (splitting a cell at an interior   *)
(*   point preserves the sum) with append stability, the concatenation   *)
(*   additivity, the Cx embedding, and the constant-integrand segment    *)
(*   theorem plus the vline seed (2*T*i*v face) that the Perron vline    *)
(*   contours (P08/P09) consume.  Slice 2 carries the uniform per-cell   *)
(*   refinement block: splitting every cell at its own point preserves   *)
(*   the step sums (map-split invariance, both components) and the Cx-   *)
(*   level step-integral invariance - the well-definedness seed of the   *)
(*   segment integral under partition refinement.  The full node         *)
(*   (general continuous integrands, refinement invariance via uniform-  *)
(*   continuity moduli, path type and its well-definedness) remains      *)
(*   open and continues in later slices of the same file series.         *)
(* Dependencies: S01_BaseRing, S02_CauchyComplete (Real line, real_eq,   *)
(*   real_const, real_eq_of_zero_diff), CxRealPairCore (Cx carrier,      *)
(*   c_of_Q, c_mult, c_eq and projection lemmas, born).  Stdlib:         *)
(*   QArith, List.                                                       *)
(* References: AFP Perrons_Formula (Eberl 2026-06-17): L c T :=          *)
(*   linepath (Complex c (-T)) (Complex c T) at :51-53 and               *)
(*   perron_aux_integral a c T = contour_integral (L c T) (fun z =>      *)
(*   of_real a powr z / z) at :56-57 - the vline shape transcribed here  *)
(*   as the finite-T vline seed (no infinite-limit face; finite-T        *)
(*   truncation discipline).  AFP PNT_with_Remainder (Song & Yao         *)
(*   2024-05-05) Perron_Formula.thy perron_integrable :124 (the          *)
(*   integrability side-condition shape this definition layer must       *)
(*   eventually supply).  Card: cards_C3 C3-P01 incl. 20261103 AFP       *)
(*   comparison record; drafts_C3 P01 statement skeleton.  Retrieval     *)
(*   ledger: prec_fetch/fetch_ledger_20261103.md.                        *)
(* Constructivity: Set-carried statements throughout; zero Axiom, zero   *)
(*   Parameter, zero classical choice; all numerics of this slice stay   *)
(*   in Q (decidable, exact); Real embedding via real_const/c_of_Q;      *)
(*   real_eq discharged pointwise via real_eq_of_zero_diff.              *)
(* Build: coqc -native-compiler no -q (sandbox -Q paths), cpu_guard v3    *)
(*   wrapper (-AllowG3 -GearForce 0 -TempLimit 98 -LoadLimit 60 -CoreN 2). *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. Q-step cells and the weighted step sums.                    *)
(* ===================================================================== *)

(* A complex-valued Q-step cell on [l,u]: value (vr,vi) held constant.  *)
Definition GaC3_P01_cell : Set := ((Q * Q) * (Q * Q))%type.

(* Weighted contribution (u-l)*(vr,vi) of one cell (pure Q). *)
Definition GaC3_P01_cw (c : GaC3_P01_cell) : Q * Q :=
  match c with
  | ((l, u), (vr, vi)) => ((u - l) * vr, (u - l) * vi)
  end.

(* Real part of the step sum over a cell list. *)
Definition GaC3_P01_qstep_sumR (cs : list GaC3_P01_cell) : Q :=
  fold_right (fun c acc => fst (GaC3_P01_cw c) + acc) 0 cs.

(* Imaginary part of the step sum over a cell list. *)
Definition GaC3_P01_qstep_sumI (cs : list GaC3_P01_cell) : Q :=
  fold_right (fun c acc => snd (GaC3_P01_cw c) + acc) 0 cs.

(* Cx embedding of the step sum: the segment-integral carrier (slice 1). *)
Definition GaC3_P01_step_integral (cs : list GaC3_P01_cell) : Cx :=
  c_of_Q (GaC3_P01_qstep_sumR cs) (GaC3_P01_qstep_sumI cs).

(* Head-step unfolding (definitional; named for reuse). *)
Lemma GaC3_P01_qstep_sumR_cons : forall (c : GaC3_P01_cell) cs,
  GaC3_P01_qstep_sumR (c :: cs) == fst (GaC3_P01_cw c) + GaC3_P01_qstep_sumR cs.
Proof. reflexivity. Qed.

Lemma GaC3_P01_qstep_sumI_cons : forall (c : GaC3_P01_cell) cs,
  GaC3_P01_qstep_sumI (c :: cs) == snd (GaC3_P01_cw c) + GaC3_P01_qstep_sumI cs.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* Section 2. Cx product algebra over the rational embedding.             *)
(* ===================================================================== *)

(* c_mult of two rational-embedded complex numbers is the rational        *)
(* product formula (componentwise, born-carrier level).                   *)
Lemma GaC3_P01_cmuloQ : forall p q r s : Q,
  c_eq (c_mult (c_of_Q p q) (c_of_Q r s)) (c_of_Q (p * r - q * s) (p * s + q * r)).
Proof.
  intros p q r s.
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n.
  - rewrite (cRe_of_Q_pt (p * r - q * s) (p * s + q * r) n).
    rewrite (cRe_mult_pt (c_of_Q p q) (c_of_Q r s) n).
    rewrite (cRe_of_Q_pt p q n). rewrite (cRe_of_Q_pt r s n).
    rewrite (cIm_of_Q_pt p q n). rewrite (cIm_of_Q_pt r s n).
    ring.
  - rewrite (cIm_of_Q_pt (p * r - q * s) (p * s + q * r) n).
    rewrite (cIm_mult_pt (c_of_Q p q) (c_of_Q r s) n).
    rewrite (cRe_of_Q_pt p q n). rewrite (cRe_of_Q_pt r s n).
    rewrite (cIm_of_Q_pt p q n). rewrite (cIm_of_Q_pt r s n).
    ring.
Qed.

(* Rational-embedded equality transport (componentwise Q equality).     *)
Lemma GaC3_P01_cofQ_eq : forall x y x' y' : Q,
  x == x' -> y == y' -> c_eq (c_of_Q x y) (c_of_Q x' y').
Proof.
  intros x y x' y' Hx Hy.
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n.
  - rewrite (cRe_of_Q_pt x y n). rewrite (cRe_of_Q_pt x' y' n).
    rewrite Hx. ring.
  - rewrite (cIm_of_Q_pt x y n). rewrite (cIm_of_Q_pt x' y' n).
    rewrite Hy. ring.
Qed.

(* ===================================================================== *)
(* Section 3. Refinement invariance (constant-integrand base block).      *)
(* ===================================================================== *)

(* Base block: splitting cell ((l,u),v) at an interior point q into the  *)
(* two-cell block ((l,q),v),((q,u),v) preserves the weighted sum.        *)
Theorem GaC3_P01_split_block_R : forall (l q u vr vi : Q),
  GaC3_P01_qstep_sumR [((l, q), (vr, vi)); ((q, u), (vr, vi))]
  == GaC3_P01_qstep_sumR [((l, u), (vr, vi))].
Proof.
  intros l q u vr vi.
  unfold GaC3_P01_qstep_sumR, GaC3_P01_cw. simpl. ring.
Qed.

Theorem GaC3_P01_split_block_I : forall (l q u vr vi : Q),
  GaC3_P01_qstep_sumI [((l, q), (vr, vi)); ((q, u), (vr, vi))]
  == GaC3_P01_qstep_sumI [((l, u), (vr, vi))].
Proof.
  intros l q u vr vi.
  unfold GaC3_P01_qstep_sumI, GaC3_P01_cw. simpl. ring.
Qed.

(* Append stability: the split invariance lifts over any prefix list.    *)
Theorem GaC3_P01_split_invariant_append_R :
  forall (cs : list GaC3_P01_cell) (l q u vr vi : Q),
  GaC3_P01_qstep_sumR (cs ++ [((l, q), (vr, vi)); ((q, u), (vr, vi))])
  == GaC3_P01_qstep_sumR (cs ++ [((l, u), (vr, vi))]).
Proof.
  intros cs l q u vr vi.
  induction cs as [| a cs IH].
  - (* nil: the base block itself (nil ++ x reduces definitionally) *)
    exact (GaC3_P01_split_block_R l q u vr vi).
  - (* cons: peel the head step, apply IH on the tail *)
    cbn [app].
    rewrite GaC3_P01_qstep_sumR_cons, GaC3_P01_qstep_sumR_cons.
    rewrite IH. reflexivity.
Qed.

Theorem GaC3_P01_split_invariant_append_I :
  forall (cs : list GaC3_P01_cell) (l q u vr vi : Q),
  GaC3_P01_qstep_sumI (cs ++ [((l, q), (vr, vi)); ((q, u), (vr, vi))])
  == GaC3_P01_qstep_sumI (cs ++ [((l, u), (vr, vi))]).
Proof.
  intros cs l q u vr vi.
  induction cs as [| a cs IH].
  - exact (GaC3_P01_split_block_I l q u vr vi).
  - cbn [app].
    rewrite GaC3_P01_qstep_sumI_cons, GaC3_P01_qstep_sumI_cons.
    rewrite IH. reflexivity.
Qed.

(* Concatenation additivity of the step sums. *)
Theorem GaC3_P01_step_concat_R : forall cs1 cs2 : list GaC3_P01_cell,
  GaC3_P01_qstep_sumR (cs1 ++ cs2) == GaC3_P01_qstep_sumR cs1 + GaC3_P01_qstep_sumR cs2.
Proof.
  intros cs1 cs2.
  induction cs1 as [| a cs1 IH].
  - cbn [app].
    change (GaC3_P01_qstep_sumR (@nil GaC3_P01_cell)) with 0%Q.
    ring.
  - cbn [app].
    rewrite GaC3_P01_qstep_sumR_cons, IH, GaC3_P01_qstep_sumR_cons.
    ring.
Qed.

Theorem GaC3_P01_step_concat_I : forall cs1 cs2 : list GaC3_P01_cell,
  GaC3_P01_qstep_sumI (cs1 ++ cs2) == GaC3_P01_qstep_sumI cs1 + GaC3_P01_qstep_sumI cs2.
Proof.
  intros cs1 cs2.
  induction cs1 as [| a cs1 IH].
  - cbn [app].
    change (GaC3_P01_qstep_sumI (@nil GaC3_P01_cell)) with 0%Q.
    ring.
  - cbn [app].
    rewrite GaC3_P01_qstep_sumI_cons, IH, GaC3_P01_qstep_sumI_cons.
    ring.
Qed.

(* ===================================================================== *)
(* Section 4. Cx-level theorems: constant integrand and the vline seed.   *)
(* ===================================================================== *)

(* Constant integrand on one segment: the slice-1 integral of the single *)
(* cell ((a,b),v) equals (b-a) * v in the born Cx carrier.  Shape-wise   *)
(* this is the degenerate case of the AFP linepath integral (L c T at    *)
(* :51-53) with constant integrand.                                      *)
Theorem GaC3_P01_step_integral_const : forall (a b vr vi : Q),
  c_eq (GaC3_P01_step_integral [((a, b), (vr, vi))])
       (c_mult (c_of_Q (b - a) 0) (c_of_Q vr vi)).
Proof.
  intros a b vr vi.
  unfold GaC3_P01_step_integral, GaC3_P01_qstep_sumR, GaC3_P01_qstep_sumI.
  cbn [GaC3_P01_cw fold_right].
  apply (c_eq_trans _ (c_of_Q ((b - a) * vr) ((b - a) * vi))).
  - apply (GaC3_P01_cofQ_eq ((b - a) * vr + 0) ((b - a) * vi + 0)
             ((b - a) * vr) ((b - a) * vi)); ring.
  - apply (c_eq_trans _ (c_mult (c_of_Q (b - a) 0) (c_of_Q vr vi))).
    + apply (GaC3_P01_cofQ_eq ((b - a) * vr) ((b - a) * vi)
               ((b - a) * vr - 0 * vi) ((b - a) * vi + 0 * vr)); ring.
    + exact (GaC3_P01_cmuloQ (b - a) 0 vr vi).
Qed.

(* The vline seed: for the vertical-line parametrisation z(t) = c + i*t  *)
(* with t in [-T,T] (AFP L c T shape, finite T), the constant-integrand  *)
(* line integral equals (2*T) * i * v, i.e. the complex number with real *)
(* part -(2*T)*vi and imaginary part (2*T)*vr.  This is the finite-T     *)
(* truncation face; no infinite-limit form is stated (red-line          *)
(* discipline of the study card).                                        *)
Theorem GaC3_P01_vline_const_seed : forall (T vr vi : Q),
  c_eq (c_mult (c_of_Q (2 * T) 0) (c_mult (c_of_Q 0 1) (c_of_Q vr vi)))
       (c_of_Q (- (2 * T) * vi) (2 * T * vr)).
Proof.
  intros T vr vi.
  apply (c_eq_trans _ (c_mult (c_of_Q (2 * T) 0)
                              (c_of_Q (0 * vr - 1 * vi) (0 * vi + 1 * vr)))).
  - apply c_mult_congr.
    + apply c_eq_refl.
    + exact (GaC3_P01_cmuloQ 0 1 vr vi).
  - apply (c_eq_trans _
             (c_of_Q (2 * T * (0 * vr - 1 * vi) - 0 * (0 * vi + 1 * vr))
                     (2 * T * (0 * vi + 1 * vr) + 0 * (0 * vr - 1 * vi)))).
    + exact (GaC3_P01_cmuloQ (2 * T) 0 (0 * vr - 1 * vi) (0 * vi + 1 * vr)).
    + apply (GaC3_P01_cofQ_eq
               (2 * T * (0 * vr - 1 * vi) - 0 * (0 * vi + 1 * vr))
               (2 * T * (0 * vi + 1 * vr) + 0 * (0 * vr - 1 * vi))
               (- (2 * T) * vi) (2 * T * vr)); ring.
Qed.

(* ===================================================================== *)
(* Section 5. Per-cell refinement points (slice 2: well-definedness       *)
(* block).  Splitting every cell of a partition at its own point          *)
(* preserves the weighted sums - the refinement-invariance seed of the    *)
(* segment integral (the general continuous-integrand face remains for    *)
(* later slices).                                                         *)
(* ===================================================================== *)

(* Split one cell at the point q into the two-cell block.  No hypothesis  *)
(* on q: the weight identity (q-l)+(u-q) = u-l is pure Q algebra.         *)
Definition GaC3_P01_split_cell (q : Q) (c : GaC3_P01_cell) : list GaC3_P01_cell :=
  match c with
  | ((l, u), v) => [((l, q), v); ((q, u), v)]
  end.

(* The weight identity of the single split block (real component). *)
Lemma GaC3_P01_split_cell_cw_R : forall (q : Q) (c : GaC3_P01_cell),
  GaC3_P01_qstep_sumR (GaC3_P01_split_cell q c) == fst (GaC3_P01_cw c).
Proof.
  intros q c. destruct c as [[l u] v]. destruct v as [vr vi].
  cbn [GaC3_P01_split_cell GaC3_P01_qstep_sumR GaC3_P01_cw fold_right fst snd].
  ring.
Qed.

(* The weight identity of the single split block (imaginary component). *)
Lemma GaC3_P01_split_cell_cw_I : forall (q : Q) (c : GaC3_P01_cell),
  GaC3_P01_qstep_sumI (GaC3_P01_split_cell q c) == snd (GaC3_P01_cw c).
Proof.
  intros q c. destruct c as [[l u] v]. destruct v as [vr vi].
  cbn [GaC3_P01_split_cell GaC3_P01_qstep_sumI GaC3_P01_cw fold_right fst snd].
  ring.
Qed.

(* Map-split invariance (real component): splitting every cell at the     *)
(* same point q preserves the weighted sum. *)
Theorem GaC3_P01_split_map_R : forall (cs : list GaC3_P01_cell) (q : Q),
  GaC3_P01_qstep_sumR (flat_map (GaC3_P01_split_cell q) cs) == GaC3_P01_qstep_sumR cs.
Proof.
  intros cs q. induction cs as [| c cs IH].
  - reflexivity.
  - cbn [flat_map].
    rewrite GaC3_P01_step_concat_R, GaC3_P01_split_cell_cw_R, IH.
    reflexivity.
Qed.

(* Map-split invariance (imaginary component). *)
Theorem GaC3_P01_split_map_I : forall (cs : list GaC3_P01_cell) (q : Q),
  GaC3_P01_qstep_sumI (flat_map (GaC3_P01_split_cell q) cs) == GaC3_P01_qstep_sumI cs.
Proof.
  intros cs q. induction cs as [| c cs IH].
  - reflexivity.
  - cbn [flat_map].
    rewrite GaC3_P01_step_concat_I, GaC3_P01_split_cell_cw_I, IH.
    reflexivity.
Qed.

(* Cx level: the step integral is invariant under uniform q-refinement. *)
Theorem GaC3_P01_step_integral_split_map : forall (cs : list GaC3_P01_cell) (q : Q),
  c_eq (GaC3_P01_step_integral (flat_map (GaC3_P01_split_cell q) cs))
       (GaC3_P01_step_integral cs).
Proof.
  intros cs q. unfold GaC3_P01_step_integral.
  apply GaC3_P01_cofQ_eq;
    [ exact (GaC3_P01_split_map_R cs q) | exact (GaC3_P01_split_map_I cs q) ].
Qed.

(* Per-cell refinement points: each cell splits at its own point (the     *)
(* cell-specific pt).  This is the partition-refinement shape that the    *)
(* well-definedness theorem (general refinement, later slice) lifts.      *)
Definition GaC3_P01_refine_pt (pt : GaC3_P01_cell -> Q) (cs : list GaC3_P01_cell)
  : list GaC3_P01_cell :=
  flat_map (fun c => GaC3_P01_split_cell (pt c) c) cs.

(* Refinement invariance under per-cell points (real component). *)
Lemma GaC3_P01_refine_pt_R : forall (pt : GaC3_P01_cell -> Q) (cs : list GaC3_P01_cell),
  GaC3_P01_qstep_sumR (GaC3_P01_refine_pt pt cs) == GaC3_P01_qstep_sumR cs.
Proof.
  intros pt cs. unfold GaC3_P01_refine_pt.
  induction cs as [| c cs IH].
  - reflexivity.
  - cbn [flat_map].
    rewrite GaC3_P01_step_concat_R, GaC3_P01_split_cell_cw_R, IH.
    reflexivity.
Qed.

(* Refinement invariance under per-cell points (imaginary component). *)
Lemma GaC3_P01_refine_pt_I : forall (pt : GaC3_P01_cell -> Q) (cs : list GaC3_P01_cell),
  GaC3_P01_qstep_sumI (GaC3_P01_refine_pt pt cs) == GaC3_P01_qstep_sumI cs.
Proof.
  intros pt cs. unfold GaC3_P01_refine_pt.
  induction cs as [| c cs IH].
  - reflexivity.
  - cbn [flat_map].
    rewrite GaC3_P01_step_concat_I, GaC3_P01_split_cell_cw_I, IH.
    reflexivity.
Qed.

(* Cx level: the step integral is invariant under per-cell refinement. *)
Theorem GaC3_P01_step_integral_refine_pt : forall (pt : GaC3_P01_cell -> Q)
  (cs : list GaC3_P01_cell),
  c_eq (GaC3_P01_step_integral (GaC3_P01_refine_pt pt cs))
       (GaC3_P01_step_integral cs).
Proof.
  intros pt cs. unfold GaC3_P01_step_integral.
  apply GaC3_P01_cofQ_eq;
    [ exact (GaC3_P01_refine_pt_R pt cs) | exact (GaC3_P01_refine_pt_I pt cs) ].
Qed.
