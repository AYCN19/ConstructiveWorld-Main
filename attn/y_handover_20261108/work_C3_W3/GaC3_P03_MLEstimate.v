(* ===================================================================== *)
(* GaC3_P03_MLEstimate.v                                                  *)
(*                                                                       *)
(* Mission: node C3-P03 (segment C3 wave W3) - the ML-type estimate       *)
(*   layer of the line integral over the P02 path carrier: the L1 (Man-  *)
(*   hattan) path length, the componentwise value-bound predicate, and   *)
(*   the ML bounds |Re sum| <= B * L1 and |Im sum| <= B * L1 for zip-    *)
(*   matched constant-per-segment data with every value componentwise   *)
(*   bounded by B - the estimate engine that P09 (horizontal tail) and   *)
(*   P11 (four-edge merge) consume.  The vertical/horizontal closed-    *)
(*   form lengths and their ML instances are included; the certificate  *)
(*   face lives in GaC3_P03_MLEstimate_cert.v (exact-Q spot checks by   *)
(*   compile-by-vm checks).  The AFP same_Im reduction (:378-395, vline *)
(*   to a real-interval integral) is definitional at this carrier: the  *)
(*   vline integral IS a Q sum already - recorded, no separate theorem. *)
(* Dependencies: GaC3_P02_LineIntegralAlg (path carrier, path sums,      *)
(*   seg_dz/seg_contrib), GaC3_P01_LineIntegralDef (Cx bridges),         *)
(*   CxRealPairCore (born), S01_BaseRing, S02_CauchyComplete (qeq_leT',  *)
(*   qleT'_to_Qle order bridge).  Stdlib: QArith (incl. Qabs), List.    *)
(* References: AFP Perron_Prerequisites (Eberl 2026-06-17)              *)
(*   contour_integral_bound_linepath' :372-375 - the ML statement shape *)
(*   (bounded integrand on the path image, bound = B * path length),    *)
(*   rebuilt partwise (real/imaginary) at the Q-step carrier; the       *)
(*   squared-norm B*L form needs a Qsqrt-free order face and is         *)
(*   deferred.  Card: cards_C3 C3-P03 incl. 20261103 AFP comparison     *)
(*   record; drafts_C3 P03 statement skeleton.  Retrieval ledger:       *)
(*   prec_fetch/fetch_ledger_20261103.md.                               *)
(* Constructivity: Set-carried statements; zero Axiom, zero Parameter,  *)
(*   zero classical choice; all numerics stay in Q (decidable, exact);  *)
(*   order reasoning by explicit QArith lemma chains - no ring on goals *)
(*   carrying reducible constant applications (session craft note);     *)
(*   zero-product goals discharged through the S02 QleT' bridge.        *)
(* Build: coqc -native-compiler no -q (sandbox -Q paths), cpu_guard v3   *)
(*   wrapper (-AllowG3 -GearForce 0 -TempLimit 98 -LoadLimit 60 -CoreN 2). *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import GaC3_P01_LineIntegralDef.
Require Import GaC3_P02_LineIntegralAlg.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. L1 path length, value bounds, and order micro-helpers.      *)
(* ===================================================================== *)

(* L1 (componentwise-abs) length of a polyline: sum over segments of     *)
(* |dx| + |dy| - exact in Q, no square roots (the squared-norm length    *)
(* face is a cert/consumer-side concern).                                *)
Fixpoint GaC3_P03_path_len1 (ps : GaC3_P02_cpath) : Q :=
  match ps with
  | nil => 0
  | p :: ps' =>
      (Qabs (fst (GaC3_P02_seg_dz p)) + Qabs (snd (GaC3_P02_seg_dz p)))%Q
      + GaC3_P03_path_len1 ps'
  end.

(* Componentwise bound of one value vector by B.  Set-level bearing: four     *)
(* Qcompare reflections (S02 QleT') through the S01 And product - the        *)
(* QltT-family Set-apartness carrier; each component is carried data.        *)
Definition GaC3_P03_val_bounded (v : Q * Q) (B : Q) : Set :=
  And (QleT' (- B) (fst v))
      (And (QleT' (fst v) B)
           (And (QleT' (- B) (snd v)) (QleT' (snd v) B))).

(* Bridge (elim): Set bearer -> native Qle conjunction. *)
Lemma GaC3_P03_val_bounded_Qle : forall (v : Q * Q) (B : Q),
  GaC3_P03_val_bounded v B ->
  (- B <= fst v)%Q /\ (fst v <= B)%Q /\ (- B <= snd v)%Q /\ (snd v <= B)%Q.
Proof.
  intros v B H. destruct H as [H1 [H2 [H3 H4]]].
  split; [ | split; [ | split ] ].
  - exact (QleT'_to_Qle _ _ H1).
  - exact (QleT'_to_Qle _ _ H2).
  - exact (QleT'_to_Qle _ _ H3).
  - exact (QleT'_to_Qle _ _ H4).
Qed.

(* Bridge (intro): native Qle conjunction -> Set bearer (Qle_to_QleT' 显式值参垫 _). *)
Lemma GaC3_P03_val_bounded_of_Qle : forall (v : Q * Q) (B : Q),
  (- B <= fst v)%Q /\ (fst v <= B)%Q /\ (- B <= snd v)%Q /\ (snd v <= B)%Q ->
  GaC3_P03_val_bounded v B.
Proof.
  intros v B [H1 [H2 [H3 H4]]].
  split; [ | split; [ | split ] ].
  - exact (Qle_to_QleT' _ _ H1).
  - exact (Qle_to_QleT' _ _ H2).
  - exact (Qle_to_QleT' _ _ H3).
  - exact (Qle_to_QleT' _ _ H4).
Qed.

(* Left-multiplication order step (QArith provides the r-form). *)
Lemma GaC3_P03_qmult_le_l : forall a b c : Q,
  (0 <= a)%Q -> b <= c -> a * b <= a * c.
Proof.
  intros a b c Ha Hbc.
  rewrite (Qmult_comm a b), (Qmult_comm a c).
  apply Qmult_le_compat_r; assumption.
Qed.

(* The L1 length is nonnegative (abs sums). *)
Lemma GaC3_P03_len1_nonneg : forall ps : GaC3_P02_cpath,
  (0 <= GaC3_P03_path_len1 ps)%Q.
Proof.
  intros ps. induction ps as [| p ps' IH].
  - cbn [GaC3_P03_path_len1]. apply Qle_refl.
  - cbn [GaC3_P03_path_len1].
    rewrite <- (Qplus_0_r 0).
    apply Qplus_le_compat.
    + rewrite <- (Qplus_0_r 0).
      apply Qplus_le_compat; apply Qabs_nonneg.
    + exact IH.
Qed.

(* Zero absorbs products: two order micro-facts (through the S02 QleT'  *)
(* bridge; ring carries the Qeq side).                                   *)
Lemma GaC3_P03_le0_absorb : forall c : Q, (0 <= 0 * c)%Q.
Proof. intros c. apply QleT'_to_Qle. apply qeq_leT'. ring. Qed.

Lemma GaC3_P03_le_absorb0 : forall c : Q, (0 <= c * 0)%Q.
Proof. intros c. apply QleT'_to_Qle. apply qeq_leT'. ring. Qed.

(* ===================================================================== *)
(* Section 2. The per-segment absolute-contribution bounds.               *)
(* ===================================================================== *)

(* Real component: |dx*vr - dy*vi| <= |dx|*B + |dy|*B. *)
Lemma GaC3_P03_contrib_abs_le_R : forall (p : GaC3_P02_pseg) (v : Q * Q) (B : Q),
  (0 <= B)%Q -> GaC3_P03_val_bounded v B ->
  Qabs (fst (GaC3_P02_seg_contrib p v))
  <= (Qabs (fst (GaC3_P02_seg_dz p)) * B + Qabs (snd (GaC3_P02_seg_dz p)) * B)%Q.
Proof.
  intros p v B HB Hv.
  destruct p as [[x0 y0] [x1 y1]]. destruct v as [vr vi].
  cbn [GaC3_P02_seg_contrib GaC3_P02_seg_dz fst snd] in *.
  destruct Hv as [Hvr1 [Hvr2 [Hvi1 Hvi2]]].
  assert (Hvr : Qabs vr <= B) by (apply (proj2 (Qabs_Qle_condition vr B));
    split; [ exact (QleT'_to_Qle _ _ Hvr1) | exact (QleT'_to_Qle _ _ Hvr2) ]).
  assert (Hvi : Qabs vi <= B) by (apply (proj2 (Qabs_Qle_condition vi B));
    split; [ exact (QleT'_to_Qle _ _ Hvi1) | exact (QleT'_to_Qle _ _ Hvi2) ]).
  unfold Qminus.
  eapply Qle_trans; [ apply Qabs_triangle | ].
  rewrite Qabs_Qmult, Qabs_opp, Qabs_Qmult.
  apply (Qplus_le_compat
           (Qabs (x1 - x0) * Qabs vr) (Qabs (x1 - x0) * B)
           (Qabs (y1 - y0) * Qabs vi) (Qabs (y1 - y0) * B)).
  - apply GaC3_P03_qmult_le_l; [ apply Qabs_nonneg | assumption ].
  - apply GaC3_P03_qmult_le_l; [ apply Qabs_nonneg | assumption ].
Qed.

(* Imaginary component: |dx*vi + dy*vr| <= |dx|*B + |dy|*B. *)
Lemma GaC3_P03_contrib_abs_le_I : forall (p : GaC3_P02_pseg) (v : Q * Q) (B : Q),
  (0 <= B)%Q -> GaC3_P03_val_bounded v B ->
  Qabs (snd (GaC3_P02_seg_contrib p v))
  <= (Qabs (fst (GaC3_P02_seg_dz p)) * B + Qabs (snd (GaC3_P02_seg_dz p)) * B)%Q.
Proof.
  intros p v B HB Hv.
  destruct p as [[x0 y0] [x1 y1]]. destruct v as [vr vi].
  cbn [GaC3_P02_seg_contrib GaC3_P02_seg_dz fst snd] in *.
  destruct Hv as [Hvr1 [Hvr2 [Hvi1 Hvi2]]].
  assert (Hvr : Qabs vr <= B) by (apply (proj2 (Qabs_Qle_condition vr B));
    split; [ exact (QleT'_to_Qle _ _ Hvr1) | exact (QleT'_to_Qle _ _ Hvr2) ]).
  assert (Hvi : Qabs vi <= B) by (apply (proj2 (Qabs_Qle_condition vi B));
    split; [ exact (QleT'_to_Qle _ _ Hvi1) | exact (QleT'_to_Qle _ _ Hvi2) ]).
  eapply Qle_trans; [ apply Qabs_triangle | ].
  rewrite Qabs_Qmult, Qabs_Qmult.
  apply (Qplus_le_compat
           (Qabs (x1 - x0) * Qabs vi) (Qabs (x1 - x0) * B)
           (Qabs (y1 - y0) * Qabs vr) (Qabs (y1 - y0) * B)).
  - apply GaC3_P03_qmult_le_l; [ apply Qabs_nonneg | assumption ].
  - apply GaC3_P03_qmult_le_l; [ apply Qabs_nonneg | assumption ].
Qed.

(* ===================================================================== *)
(* Section 3. The ML bounds (both components).                            *)
(* ===================================================================== *)

Theorem GaC3_P03_path_sumR_ml : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (B : Q),
  (0 <= B)%Q ->
  (forall v, In v vs -> GaC3_P03_val_bounded v B) ->
  Qabs (GaC3_P02_path_sumR ps vs) <= B * GaC3_P03_path_len1 ps.
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs B HB Hv.
  - cbn [GaC3_P02_path_sumR GaC3_P03_path_len1].
    apply (Qle_trans _ 0).
    + apply Qle_refl.
    + apply GaC3_P03_le_absorb0.
  - destruct vs as [| v vs'].
    + cbn [GaC3_P02_path_sumR].
      apply (Qle_trans _ (0 * GaC3_P03_path_len1 (p :: ps'))).
      * apply (Qle_trans (Qabs 0) 0 (0 * GaC3_P03_path_len1 (p :: ps'))).
        -- apply Qle_refl.
        -- apply GaC3_P03_le0_absorb.
      * apply Qmult_le_compat_r; [ exact HB | apply GaC3_P03_len1_nonneg ].
    + assert (H1 : Qabs (fst (GaC3_P02_seg_contrib p v) + GaC3_P02_path_sumR ps' vs')
                   <= (Qabs (fst (GaC3_P02_seg_dz p)) * B
                       + Qabs (snd (GaC3_P02_seg_dz p)) * B
                       + B * GaC3_P03_path_len1 ps')%Q).
      { eapply Qle_trans; [ apply Qabs_triangle | ].
        apply Qplus_le_compat.
        - apply GaC3_P03_contrib_abs_le_R; [ exact HB | apply Hv, in_eq ].
        - apply IH; [ exact HB | ].
          intros w Hw. apply Hv. exact (in_cons v w vs' Hw). }
      cbn [GaC3_P02_path_sumR GaC3_P03_path_len1].
      rewrite Qmult_plus_distr_r, Qmult_plus_distr_r,
              (Qmult_comm B (Qabs (fst (GaC3_P02_seg_dz p)))),
              (Qmult_comm B (Qabs (snd (GaC3_P02_seg_dz p)))).
      exact H1.
Qed.

Theorem GaC3_P03_path_sumI_ml : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (B : Q),
  (0 <= B)%Q ->
  (forall v, In v vs -> GaC3_P03_val_bounded v B) ->
  Qabs (GaC3_P02_path_sumI ps vs) <= B * GaC3_P03_path_len1 ps.
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs B HB Hv.
  - cbn [GaC3_P02_path_sumI GaC3_P03_path_len1].
    apply (Qle_trans _ 0).
    + apply Qle_refl.
    + apply GaC3_P03_le_absorb0.
  - destruct vs as [| v vs'].
    + cbn [GaC3_P02_path_sumI].
      apply (Qle_trans _ (0 * GaC3_P03_path_len1 (p :: ps'))).
      * apply (Qle_trans (Qabs 0) 0 (0 * GaC3_P03_path_len1 (p :: ps'))).
        -- apply Qle_refl.
        -- apply GaC3_P03_le0_absorb.
      * apply Qmult_le_compat_r; [ exact HB | apply GaC3_P03_len1_nonneg ].
    + assert (H1 : Qabs (snd (GaC3_P02_seg_contrib p v) + GaC3_P02_path_sumI ps' vs')
                   <= (Qabs (fst (GaC3_P02_seg_dz p)) * B
                       + Qabs (snd (GaC3_P02_seg_dz p)) * B
                       + B * GaC3_P03_path_len1 ps')%Q).
      { eapply Qle_trans; [ apply Qabs_triangle | ].
        apply Qplus_le_compat.
        - apply GaC3_P03_contrib_abs_le_I; [ exact HB | apply Hv, in_eq ].
        - apply IH; [ exact HB | ].
          intros w Hw. apply Hv. exact (in_cons v w vs' Hw). }
      cbn [GaC3_P02_path_sumI GaC3_P03_path_len1].
      rewrite Qmult_plus_distr_r, Qmult_plus_distr_r,
              (Qmult_comm B (Qabs (fst (GaC3_P02_seg_dz p)))),
              (Qmult_comm B (Qabs (snd (GaC3_P02_seg_dz p)))).
      exact H1.
Qed.

(* The ML pair at Cx level: both components bounded by B * L1. *)
Theorem GaC3_P03_line_integral_ml_pair : forall (ps : GaC3_P02_cpath)
  (vs : list (Q * Q)) (B : Q),
  (0 <= B)%Q ->
  (forall v, In v vs -> GaC3_P03_val_bounded v B) ->
  Qabs (GaC3_P02_path_sumR ps vs) <= B * GaC3_P03_path_len1 ps
  /\ Qabs (GaC3_P02_path_sumI ps vs) <= B * GaC3_P03_path_len1 ps.
Proof.
  intros ps vs B HB Hv. split.
  - apply GaC3_P03_path_sumR_ml; assumption.
  - apply GaC3_P03_path_sumI_ml; assumption.
Qed.

(* ===================================================================== *)
(* Section 4. Closed-form lengths and the vline/hline ML instances.       *)
(* ===================================================================== *)

Theorem GaC3_P03_len1_vline : forall c T : Q, (0 <= T)%Q ->
  GaC3_P03_path_len1 (GaC3_P02_vline_seg c T) == 2 * T.
Proof.
  intros c T HT.
  cbn [GaC3_P03_path_len1 GaC3_P02_vline_seg GaC3_P02_seg_dz fst snd].
  assert (Ecc : (c - c == 0)%Q) by ring.
  rewrite Ecc.
  assert (Hm : (T - (-T) == T + T)%Q) by ring.
  rewrite Hm.
  assert (H2 : (0 + 0 <= T + T)%Q) by (apply Qplus_le_compat; assumption).
  rewrite Qplus_0_l in H2.
  rewrite (Qabs_pos 0 (Qle_refl 0)), (Qabs_pos (T + T) H2). ring.
Qed.

Theorem GaC3_P03_len1_hline : forall x0 x1 T : Q, (0 <= x1 - x0)%Q ->
  GaC3_P03_path_len1 (GaC3_P02_hline_seg x0 x1 T) == x1 - x0.
Proof.
  intros x0 x1 T Hdx.
  cbn [GaC3_P03_path_len1 GaC3_P02_hline_seg GaC3_P02_seg_dz fst snd].
  assert (Ett : (T - T == 0)%Q) by ring.
  rewrite Ett.
  rewrite (Qabs_pos (x1 - x0) Hdx), (Qabs_pos 0 (Qle_refl 0)). ring.
Qed.

(* ML instance on the vertical path (P08/P09 consumption shape). *)
Theorem GaC3_P03_ml_vline : forall (c T : Q) (vs : list (Q * Q)) (B : Q),
  (0 <= T)%Q -> (0 <= B)%Q ->
  (forall v, In v vs -> GaC3_P03_val_bounded v B) ->
  Qabs (GaC3_P02_path_sumR (GaC3_P02_vline_seg c T) vs) <= B * (2 * T)
  /\ Qabs (GaC3_P02_path_sumI (GaC3_P02_vline_seg c T) vs) <= B * (2 * T).
Proof.
  intros c T vs B HT HB Hv. split.
  - eapply Qle_trans;
      [ apply (GaC3_P03_path_sumR_ml _ _ B HB Hv)
      | rewrite (GaC3_P03_len1_vline c T HT); apply Qle_refl ].
  - eapply Qle_trans;
      [ apply (GaC3_P03_path_sumI_ml _ _ B HB Hv)
      | rewrite (GaC3_P03_len1_vline c T HT); apply Qle_refl ].
Qed.

(* ML instance on the horizontal path. *)
Theorem GaC3_P03_ml_hline : forall (x0 x1 T : Q) (vs : list (Q * Q)) (B : Q),
  (0 <= x1 - x0)%Q -> (0 <= B)%Q ->
  (forall v, In v vs -> GaC3_P03_val_bounded v B) ->
  Qabs (GaC3_P02_path_sumR (GaC3_P02_hline_seg x0 x1 T) vs) <= B * (x1 - x0)
  /\ Qabs (GaC3_P02_path_sumI (GaC3_P02_hline_seg x0 x1 T) vs) <= B * (x1 - x0).
Proof.
  intros x0 x1 T vs B Hdx HB Hv. split.
  - eapply Qle_trans;
      [ apply (GaC3_P03_path_sumR_ml _ _ B HB Hv)
      | rewrite (GaC3_P03_len1_hline x0 x1 T Hdx); apply Qle_refl ].
  - eapply Qle_trans;
      [ apply (GaC3_P03_path_sumI_ml _ _ B HB Hv)
      | rewrite (GaC3_P03_len1_hline x0 x1 T Hdx); apply Qle_refl ].
Qed.
