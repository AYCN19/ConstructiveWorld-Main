(* ConstructiveWorld-Main - the rectangular-contour layer of the Perron chain
   over the Q-polyline path carrier (probe variant). *)
(** * GaC3_P04_CauchyRect_probe: the Cauchy-rectangle node, probe variant.
    Mission.  Node C3-P04, the rectangular-contour layer of the Perron
      chain over the P02 path carrier: the rectangle boundary polyline
      [GaC3_P04_rect_boundary] (four Q-endpoint segments, traversed
      counterclockwise), the closed-loop cancellation of the constant
      integrand around it [GaC3_P04_cauchy_rect_const] (the Cauchy-zero
      face at the step carrier), the four-edge decomposition identity
      [GaC3_P04_rect_four_edges] (the AFP contour_integral_rectpath
      expansion shape, arbitrary per-edge value data), and the
      vertical-line shift identity [GaC3_P04_vline_shift_const] that
      the contour-shift node P10 consumes.  The general holomorphic
      Cauchy-Goursat theorem (f holomorphic on the box => loop
      integral zero) is the deep-water face of this node: the carrier
      has no holomorphic predicate yet (complex differentiability
      machinery is a carrier gap, loudly recorded in the node card);
      this probe slice lands the contour algebra and the
      constant-integrand faces.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [List].  Requires [GaC3_P02_LineIntegralAlg]
      (path carrier, line integral, Cx bridges),
      [GaC3_P01_LineIntegralDef] (Cx embedding bridges),
      [CxRealPairCore], [S01_BaseRing], and [S02_CauchyComplete] of
      this development.
    References.  AFP Perrons_Formula (Eberl 2026-06-17): R = rectpath
      (Complex c (-T)) (Complex b T) at :129, Cauchy_theorem_convex_simple
      at :137, contour_integral_rectpath four-edge expansion at :145-151
      (the :143-153 window), the decomposition shape transcribed here;
      Cauchy's theorem itself is HOL-Analysis-internal there (consumed,
      not re-proved), so the tree rebuilds the contour algebra from
      zero at the step carrier.  Card cards_C3 C3-P04; drafts_C3 P04
      statement skeleton.
    Constructivity.  Set-carried statements; zero classical choice;
      all numerics stay in Q (decidable, exact); both loop identities
      reduce to pure Q algebra on constructor data; [coqchk] reports
      zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC3_P04_CauchyRect_probe.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3] (-AllowG3 -GearForce 0
      -TempLimit 98 -LoadLimit 60 -CoreN 2). *)

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
(* Section 1. The rectangle boundary polyline.                            *)
(* ===================================================================== *)

(* The rectangle boundary: bottom edge (c,-T) -> (b,-T), right edge       *)
(* (b,-T) -> (b,T), top edge (b,T) -> (c,T), left edge (c,T) -> (c,-T)   *)
(* - traversed counterclockwise, closing the loop (AFP R = rectpath       *)
(* (Complex c (-T)) (Complex b T) :129 shape).                            *)
Definition GaC3_P04_rect_boundary (c b T : Q) : GaC3_P02_cpath :=
  [((c, -T), (b, -T)); ((b, -T), (b, T)); ((b, T), (c, T)); ((c, T), (c, -T))].

(* ===================================================================== *)
(* Section 2. Constant-integrand loop cancellation (Cauchy-zero face).    *)
(* ===================================================================== *)

(* The constant integrand integrates to zero around the closed rectangle *)
(* - the displacement sums cancel componentwise.  This is the Cauchy    *)
(* zero face at the step carrier (AFP consumes Cauchy_theorem_convex_    *)
(* simple :137 from HOL-Analysis; the tree rebuilds this face here).     *)
Theorem GaC3_P04_cauchy_rect_const : forall (c b T : Q) (v : Q * Q),
  c_eq (GaC3_P02_line_integral (GaC3_P04_rect_boundary c b T) [v; v; v; v])
       (c_of_Q 0 0).
Proof.
  intros c b T v.
  unfold GaC3_P02_line_integral, GaC3_P04_rect_boundary.
  cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz
       GaC3_P02_seg_contrib fst snd].
  apply GaC3_P01_cofQ_eq; ring.
Qed.

(* ===================================================================== *)
(* Section 3. The four-edge decomposition identity.                       *)
(* ===================================================================== *)

(* The rectangle integral decomposes into the four edge integrals with   *)
(* arbitrary per-edge value data (the AFP contour_integral_rectpath      *)
(* expansion :145-151 shape; P10 consumes this identity).                *)
Theorem GaC3_P04_rect_four_edges : forall (c b T : Q) (v1 v2 v3 v4 : Q * Q),
  c_eq (GaC3_P02_line_integral (GaC3_P04_rect_boundary c b T) [v1; v2; v3; v4])
       (c_plus
         (GaC3_P02_line_integral [((c, -T), (b, -T))] [v1])
         (c_plus
           (GaC3_P02_line_integral [((b, -T), (b, T))] [v2])
           (c_plus
             (GaC3_P02_line_integral [((b, T), (c, T))] [v3])
             (GaC3_P02_line_integral [((c, T), (c, -T))] [v4])))).
Proof.
  intros c b T v1 v2 v3 v4.
  unfold GaC3_P02_line_integral, GaC3_P04_rect_boundary.
  cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz
       GaC3_P02_seg_contrib fst snd].
  repeat rewrite GaC3_P02_cploQ.
  apply GaC3_P01_cofQ_eq; ring.
Qed.

(* ===================================================================== *)
(* Section 4. The vertical-line shift identity (constant integrand).      *)
(* ===================================================================== *)

(* For a constant integrand the rectangle integral vanishes, so the      *)
(* left vertical edge equals right edge plus bottom minus top - the      *)
(* AFP :143-153 shift shape (derived there from the Cauchy zero; here    *)
(* directly at the constant face).  P10 consumes this shape.             *)
Theorem GaC3_P04_vline_shift_const : forall (c b T : Q) (v : Q * Q),
  c_eq (GaC3_P02_line_integral (GaC3_P02_vline_seg c T) [v])
       (c_plus
         (GaC3_P02_line_integral (GaC3_P02_vline_seg b T) [v])
         (c_plus
           (GaC3_P02_line_integral (GaC3_P02_hline_seg c b (-T)) [v])
           (c_opp (GaC3_P02_line_integral (GaC3_P02_hline_seg c b T) [v]))))).
Proof.
  intros c b T v.
  unfold GaC3_P02_line_integral, GaC3_P02_vline_seg, GaC3_P02_hline_seg.
  cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz
       GaC3_P02_seg_contrib fst snd].
  rewrite GaC3_P02_coppoQ.
  repeat rewrite GaC3_P02_cploQ.
  apply GaC3_P01_cofQ_eq; ring.
Qed.
