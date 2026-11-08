(* ConstructiveWorld-Main - the algebra layer of the line integral over the
   Q-polyline path carrier. *)
(** * GaC3_P02_LineIntegralAlg: path carrier and the line-integral algebra.
    Mission.  Node C3-P02, the algebra layer of the line integral over
      the Q-polyline path carrier: the path type (list of Q-endpoint
      segments), the vertical/horizontal path seeds (the AFP L c T
      transcription, finite T), the path-level line integral (zip of
      segments with constant-per-segment complex Q values), and the
      three algebra laws: complex-scalar homogeneity (linear),
      concatenation additivity (concat), and orientation reversal
      (reverse).  The reparameterisation-invariance face of the draft
      skeleton (monotone C1 covering) is a Real-level face and remains
      open: the step-level refinement face of it is carried by
      [GaC3_P01_LineIntegralDef] ([GaC3_P01_split_map_R]/
      [GaC3_P01_refine_pt_R]); the deferral is explicit.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [List].  Requires [GaC3_P01_LineIntegralDef]
      (cell/step layer, Cx bridges), [CxRealPairCore] (Cx carrier),
      [S01_BaseRing], and [S02_CauchyComplete]
      ([real_eq_of_zero_diff]) of this development.
    References.  AFP Perron_Prerequisites (Eberl 2026-06-17)
      contour_integral_rmul :447 / contour_integral_lmul :462 /
      contour_integral_divide :465 (linear three, statement-shape
      transcription; proofs rebuilt from the step layer);
      Perrons_Formula L c T := linepath (Complex c (-T)) (Complex c T)
      at :53 (vline seed shape).  Concatenation/reversal are not
      separate AFP items (path algebra implicit in HOL-Analysis),
      from-zero at the step carrier.  Card cards_C3 C3-P02; drafts_C3
      P02 statement skeleton.
    Constructivity.  Set-carried statements; zero classical choice;
      all numerics stay in Q (decidable, exact); Real embedding via
      [real_const]/[c_of_Q]; [real_eq] discharged pointwise via
      [real_eq_of_zero_diff]; [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC3_P02_LineIntegralAlg.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3] (-AllowG3 -GearForce 0
      -TempLimit 98 -LoadLimit 60 -CoreN 2). *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import GaC3_P01_LineIntegralDef.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. The path carrier: Q-polyline segments.                      *)
(* ===================================================================== *)

Definition GaC3_P02_vertex : Set := (Q * Q)%type.
Definition GaC3_P02_pseg : Set := (GaC3_P02_vertex * GaC3_P02_vertex)%type.
Definition GaC3_P02_cpath : Set := list GaC3_P02_pseg.

(* The vertical-line path (AFP L c T :53 shape, finite T truncation). *)
Definition GaC3_P02_vline_seg (c T : Q) : GaC3_P02_cpath := [((c, -T), (c, T))].

(* The horizontal-line path at height T. *)
Definition GaC3_P02_hline_seg (x0 x1 T : Q) : GaC3_P02_cpath :=
  [((x0, T), (x1, T))].

(* Zip discipline: value data matched to segments by position.  Set-level     *)
(* bearing (QltT/NatLe-family boolean reflection through the S01 Id carrier,  *)
(* S01 NatLe :88 / S02 QleT' :99 pattern): the check is a computation         *)
(* (Nat.eqb), not a Prop premise.                                             *)
Definition GaC3_P02_plen_ok (ps : GaC3_P02_cpath) (vs : list (Q * Q)) : Set :=
  Id (Nat.eqb (length ps) (length vs)) true.

(* Bridge (elim): Set bearer -> native length equality (probe0g2-verified). *)
Lemma GaC3_P02_nat_eqb_eq : forall n m : nat, Nat.eqb n m = true -> n = m.
Proof.
  induction n as [| n IH]; intros m H; destruct m as [| m'].
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - f_equal. apply IH. exact H.
Qed.

Lemma GaC3_P02_plen_ok_true : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q)),
  GaC3_P02_plen_ok ps vs -> length ps = length vs.
Proof.
  intros ps vs H. unfold GaC3_P02_plen_ok in H.
  destruct (Nat.eqb (length ps) (length vs)) eqn:E.
  - apply (GaC3_P02_nat_eqb_eq _ _ E).
  - inversion H.
Qed.

(* Bridge (intro): native length equality -> Set bearer (probe0g2-verified). *)
Lemma GaC3_P02_plen_ok_of_eq : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q)),
  length ps = length vs -> GaC3_P02_plen_ok ps vs.
Proof.
  intros ps vs H. unfold GaC3_P02_plen_ok.
  assert (Hr : forall n : nat, Nat.eqb n n = true).
  { induction n as [| n IH].
    - reflexivity.
    - exact IH. }
  rewrite H, (Hr (length vs)). apply id_refl.
Qed.

(* ===================================================================== *)
(* Section 2. Segment displacement, contribution, path sums.              *)
(* ===================================================================== *)

Definition GaC3_P02_seg_dz (s : GaC3_P02_pseg) : Q * Q :=
  ((fst (snd s) - fst (fst s))%Q, (snd (snd s) - snd (fst s))%Q).

(* Constant-value contribution of one segment: dz * v (complex Q        *)
(* product, both components).  This is the weight of one cell along the *)
(* affine parametrisation z(t) = z0 + t*(z1-z0).                         *)
Definition GaC3_P02_seg_contrib (s : GaC3_P02_pseg) (v : Q * Q) : Q * Q :=
  let (dx, dy) := GaC3_P02_seg_dz s in
  (dx * fst v - dy * snd v, dx * snd v + dy * fst v).

Fixpoint GaC3_P02_path_sumR (ps : GaC3_P02_cpath) (vs : list (Q * Q)) : Q :=
  match ps, vs with
  | nil, _ => 0
  | _, nil => 0
  | p :: ps', v :: vs' => fst (GaC3_P02_seg_contrib p v) + GaC3_P02_path_sumR ps' vs'
  end.

Fixpoint GaC3_P02_path_sumI (ps : GaC3_P02_cpath) (vs : list (Q * Q)) : Q :=
  match ps, vs with
  | nil, _ => 0
  | _, nil => 0
  | p :: ps', v :: vs' => snd (GaC3_P02_seg_contrib p v) + GaC3_P02_path_sumI ps' vs'
  end.

(* The path-level line integral (Cx carrier). *)
Definition GaC3_P02_line_integral (ps : GaC3_P02_cpath) (vs : list (Q * Q)) : Cx :=
  c_of_Q (GaC3_P02_path_sumR ps vs) (GaC3_P02_path_sumI ps vs).

(* Head-step unfoldings (definitional; named for reuse). *)
Lemma GaC3_P02_path_sumR_cons : forall (p : GaC3_P02_pseg) (ps : GaC3_P02_cpath)
  (v : Q * Q) (vs : list (Q * Q)),
  GaC3_P02_path_sumR (p :: ps) (v :: vs)
  == fst (GaC3_P02_seg_contrib p v) + GaC3_P02_path_sumR ps vs.
Proof. reflexivity. Qed.

Lemma GaC3_P02_path_sumI_cons : forall (p : GaC3_P02_pseg) (ps : GaC3_P02_cpath)
  (v : Q * Q) (vs : list (Q * Q)),
  GaC3_P02_path_sumI (p :: ps) (v :: vs)
  == snd (GaC3_P02_seg_contrib p v) + GaC3_P02_path_sumI ps vs.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(* Section 3. Cx bridges over the rational embedding.                     *)
(* ===================================================================== *)

Lemma GaC3_P02_cploQ : forall a b c d : Q,
  c_eq (c_plus (c_of_Q a b) (c_of_Q c d)) (c_of_Q (a + c) (b + d)).
Proof.
  intros a b c d. unfold c_eq. split; apply real_eq_of_zero_diff; intro n.
  - rewrite (cRe_plus_pt (c_of_Q a b) (c_of_Q c d) n).
    rewrite (cRe_of_Q_pt a b n). rewrite (cRe_of_Q_pt c d n).
    rewrite (cRe_of_Q_pt (a + c) (b + d) n). ring.
  - rewrite (cIm_plus_pt (c_of_Q a b) (c_of_Q c d) n).
    rewrite (cIm_of_Q_pt a b n). rewrite (cIm_of_Q_pt c d n).
    rewrite (cIm_of_Q_pt (a + c) (b + d) n). ring.
Qed.

Lemma GaC3_P02_coppoQ : forall a b : Q,
  c_eq (c_opp (c_of_Q a b)) (c_of_Q (- a) (- b)).
Proof.
  intros a b. unfold c_eq. split; apply real_eq_of_zero_diff; intro n.
  - rewrite (cRe_opp_pt (c_of_Q a b) n).
    rewrite (cRe_of_Q_pt a b n). rewrite (cRe_of_Q_pt (- a) (- b) n). ring.
  - rewrite (cIm_opp_pt (c_of_Q a b) n).
    rewrite (cIm_of_Q_pt a b n). rewrite (cIm_of_Q_pt (- a) (- b) n). ring.
Qed.

(* ===================================================================== *)
(* Section 4. Path seeds: nil, vline, hline (constant value).             *)
(* ===================================================================== *)

Theorem GaC3_P02_line_integral_nil : forall vs : list (Q * Q),
  c_eq (GaC3_P02_line_integral nil vs) (c_of_Q 0 0).
Proof.
  intros vs. unfold GaC3_P02_line_integral.
  cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI].
  apply GaC3_P01_cofQ_eq; ring.
Qed.

(* The vline seed at path level: integral over the vertical path equals  *)
(* (2*T)*i*v.  Shape: the AFP L c T constant-integrand face (finite T).  *)
Theorem GaC3_P02_vline_const : forall (c T : Q) (v : Q * Q),
  c_eq (GaC3_P02_line_integral (GaC3_P02_vline_seg c T) [v])
       (c_of_Q (- (2 * T) * snd v) (2 * T * fst v)).
Proof.
  intros c T v. unfold GaC3_P02_line_integral, GaC3_P02_vline_seg.
  cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz
       GaC3_P02_seg_contrib fst snd].
  apply GaC3_P01_cofQ_eq; ring.
Qed.

(* The hline seed: integral over the horizontal path equals (x1-x0)*v.  *)
Theorem GaC3_P02_hline_const : forall (x0 x1 T : Q) (v : Q * Q),
  c_eq (GaC3_P02_line_integral (GaC3_P02_hline_seg x0 x1 T) [v])
       (c_of_Q ((x1 - x0) * fst v) ((x1 - x0) * snd v)).
Proof.
  intros x0 x1 T v. unfold GaC3_P02_line_integral, GaC3_P02_hline_seg.
  cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz
       GaC3_P02_seg_contrib fst snd].
  apply GaC3_P01_cofQ_eq; ring.
Qed.

(* ===================================================================== *)
(* Section 5. Concatenation additivity.                                   *)
(* ===================================================================== *)

Theorem GaC3_P02_path_concat_R : forall (ps1 ps2 : GaC3_P02_cpath)
  (vs1 vs2 : list (Q * Q)),
  GaC3_P02_plen_ok ps1 vs1 ->
  GaC3_P02_path_sumR (ps1 ++ ps2) (vs1 ++ vs2)
  == GaC3_P02_path_sumR ps1 vs1 + GaC3_P02_path_sumR ps2 vs2.
Proof.
  intros ps1. induction ps1 as [| p ps1' IH]; intros ps2 vs1 vs2 Hlen.
  - destruct vs1 as [| v vs1'].
    + cbn [app GaC3_P02_path_sumR]. ring.
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
  - destruct vs1 as [| v vs1'].
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
    + destruct p as [[x0 y0] [x1 y1]]. destruct v as [vr vi].
      cbn [app]. rewrite GaC3_P02_path_sumR_cons, GaC3_P02_path_sumR_cons.
      rewrite IH
        by (apply GaC3_P02_plen_ok_of_eq;
            pose proof (GaC3_P02_plen_ok_true _ _ Hlen) as Hlen0;
            cbn [length] in Hlen0; injection Hlen0 as Heq; exact Heq).
      cbn [GaC3_P02_seg_contrib fst snd GaC3_P02_seg_dz]. ring.
Qed.

Theorem GaC3_P02_path_concat_I : forall (ps1 ps2 : GaC3_P02_cpath)
  (vs1 vs2 : list (Q * Q)),
  GaC3_P02_plen_ok ps1 vs1 ->
  GaC3_P02_path_sumI (ps1 ++ ps2) (vs1 ++ vs2)
  == GaC3_P02_path_sumI ps1 vs1 + GaC3_P02_path_sumI ps2 vs2.
Proof.
  intros ps1. induction ps1 as [| p ps1' IH]; intros ps2 vs1 vs2 Hlen.
  - destruct vs1 as [| v vs1'].
    + cbn [app GaC3_P02_path_sumI]. ring.
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
  - destruct vs1 as [| v vs1'].
    + unfold GaC3_P02_plen_ok in Hlen. cbn [length Nat.eqb] in Hlen. inversion Hlen.
    + destruct p as [[x0 y0] [x1 y1]]. destruct v as [vr vi].
      cbn [app]. rewrite GaC3_P02_path_sumI_cons, GaC3_P02_path_sumI_cons.
      rewrite IH
        by (apply GaC3_P02_plen_ok_of_eq;
            pose proof (GaC3_P02_plen_ok_true _ _ Hlen) as Hlen0;
            cbn [length] in Hlen0; injection Hlen0 as Heq; exact Heq).
      cbn [GaC3_P02_seg_contrib fst snd GaC3_P02_seg_dz]. ring.
Qed.

(* Cx level: concatenation additivity of the line integral. *)
Theorem GaC3_P02_line_integral_concat : forall (ps1 ps2 : GaC3_P02_cpath)
  (vs1 vs2 : list (Q * Q)),
  GaC3_P02_plen_ok ps1 vs1 ->
  c_eq (GaC3_P02_line_integral (ps1 ++ ps2) (vs1 ++ vs2))
       (c_plus (GaC3_P02_line_integral ps1 vs1)
               (GaC3_P02_line_integral ps2 vs2)).
Proof.
  intros ps1 ps2 vs1 vs2 Hlen.
  unfold GaC3_P02_line_integral.
  apply (c_eq_trans _ (c_of_Q
    (GaC3_P02_path_sumR ps1 vs1 + GaC3_P02_path_sumR ps2 vs2)
    (GaC3_P02_path_sumI ps1 vs1 + GaC3_P02_path_sumI ps2 vs2))).
  - apply GaC3_P01_cofQ_eq; [ apply GaC3_P02_path_concat_R | apply GaC3_P02_path_concat_I ];
      exact Hlen.
  - exact (GaC3_P02_cploQ (GaC3_P02_path_sumR ps1 vs1) (GaC3_P02_path_sumI ps1 vs1)
             (GaC3_P02_path_sumR ps2 vs2) (GaC3_P02_path_sumI ps2 vs2)).
Qed.

(* ===================================================================== *)
(* Section 6. Complex-scalar homogeneity (the linear law).                *)
(* ===================================================================== *)

(* Complex scalar action on value vectors (Q pairs). *)
Definition GaC3_P02_vmul (al v : Q * Q) : Q * Q :=
  (fst al * fst v - snd al * snd v, fst al * snd v + snd al * fst v).

(* Per-segment bilinearity of the contribution in the value vector        *)
(* (both components; pure Q algebra on destructed pairs). *)
Lemma GaC3_P02_contrib_vmul_R : forall (s : GaC3_P02_pseg) (v al : Q * Q),
  fst (GaC3_P02_seg_contrib s (GaC3_P02_vmul al v))
  == fst al * fst (GaC3_P02_seg_contrib s v) - snd al * snd (GaC3_P02_seg_contrib s v).
Proof.
  intros [[x0 y0] [x1 y1]] [vr vi] [ar ai].
  cbn [GaC3_P02_vmul GaC3_P02_seg_contrib GaC3_P02_seg_dz fst snd].
  ring.
Qed.

Lemma GaC3_P02_contrib_vmul_I : forall (s : GaC3_P02_pseg) (v al : Q * Q),
  snd (GaC3_P02_seg_contrib s (GaC3_P02_vmul al v))
  == fst al * snd (GaC3_P02_seg_contrib s v) + snd al * fst (GaC3_P02_seg_contrib s v).
Proof.
  intros [[x0 y0] [x1 y1]] [vr vi] [ar ai].
  cbn [GaC3_P02_vmul GaC3_P02_seg_contrib GaC3_P02_seg_dz fst snd].
  ring.
Qed.

Theorem GaC3_P02_path_sumR_vmul : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (al : Q * Q),
  GaC3_P02_path_sumR ps (map (GaC3_P02_vmul al) vs)
  == fst al * GaC3_P02_path_sumR ps vs - snd al * GaC3_P02_path_sumI ps vs.
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs al; destruct vs as [| v vs'].
  - cbn [map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
  - cbn [map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
  - cbn [map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
  - cbn [map].
    destruct p as [[x0 y0] [x1 y1]]. destruct v as [vr vi]. destruct al as [ar ai].
    rewrite GaC3_P02_path_sumR_cons, GaC3_P02_path_sumR_cons,
            GaC3_P02_path_sumI_cons, (IH vs' (ar, ai)).
    cbn [GaC3_P02_vmul GaC3_P02_seg_contrib fst snd GaC3_P02_seg_dz].
    ring.
Qed.

Theorem GaC3_P02_path_sumI_vmul : forall (ps : GaC3_P02_cpath) (vs : list (Q * Q))
  (al : Q * Q),
  GaC3_P02_path_sumI ps (map (GaC3_P02_vmul al) vs)
  == fst al * GaC3_P02_path_sumI ps vs + snd al * GaC3_P02_path_sumR ps vs.
Proof.
  intros ps. induction ps as [| p ps' IH]; intros vs al; destruct vs as [| v vs'].
  - cbn [map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
  - cbn [map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
  - cbn [map GaC3_P02_path_sumR GaC3_P02_path_sumI]. ring.
  - cbn [map].
    destruct p as [[x0 y0] [x1 y1]]. destruct v as [vr vi]. destruct al as [ar ai].
    rewrite GaC3_P02_path_sumI_cons, GaC3_P02_path_sumI_cons,
            GaC3_P02_path_sumR_cons, (IH vs' (ar, ai)).
    cbn [GaC3_P02_vmul GaC3_P02_seg_contrib fst snd GaC3_P02_seg_dz].
    ring.
Qed.

(* The linear law: pulling a complex scalar through the path integral     *)
(* (statement shape of AFP Perron_Prerequisites contour_integral_lmul     *)
(* :462, rebuilt from the step layer). *)
Theorem GaC3_P02_line_integral_linear : forall (ps : GaC3_P02_cpath)
  (vs : list (Q * Q)) (al : Q * Q),
  c_eq (GaC3_P02_line_integral ps (map (GaC3_P02_vmul al) vs))
       (c_mult (c_of_Q (fst al) (snd al)) (GaC3_P02_line_integral ps vs)).
Proof.
  intros ps vs al. unfold GaC3_P02_line_integral.
  apply (c_eq_trans _ (c_of_Q
    (fst al * GaC3_P02_path_sumR ps vs - snd al * GaC3_P02_path_sumI ps vs)
    (fst al * GaC3_P02_path_sumI ps vs + snd al * GaC3_P02_path_sumR ps vs))).
  - apply GaC3_P01_cofQ_eq;
      [ exact (GaC3_P02_path_sumR_vmul ps vs al)
      | exact (GaC3_P02_path_sumI_vmul ps vs al) ].
  - exact (GaC3_P01_cmuloQ (fst al) (snd al)
             (GaC3_P02_path_sumR ps vs) (GaC3_P02_path_sumI ps vs)).
Qed.

