(* ConstructiveWorld-Main - the rectangular-contour layer of the Perron chain
   over the Q-polyline path carrier. *)
(** * GaC3_P04_CauchyRect: the rectangle contour and the Cauchy-zero face.
    Mission.  Node C3-P04, the rectangular-contour layer of the Perron
      chain over the P02 path carrier: the rectangle boundary polyline
      [GaC3_P04_rect_boundary] (four Q-endpoint segments, traversed
      counterclockwise), the closed-loop cancellation of the constant
      integrand around it [GaC3_P04_cauchy_rect_const] (the Cauchy-zero
      face at the step carrier), a congruence lemma for [c_plus] over
      [c_eq] [GaC3_P04_cplus_congr_r] (newly supplied, consumed by the
      decomposition proof), the four-edge decomposition identity
      [GaC3_P04_rect_four_edges] (the AFP contour_integral_rectpath
      expansion shape, arbitrary per-edge value data), and the
      vertical-line shift identity [GaC3_P04_vline_shift_const] that
      the contour-shift node P10 consumes.  The general holomorphic
      Cauchy-Goursat theorem (f holomorphic on the box => loop
      integral zero) is the deep-water face of this node: the carrier
      has no holomorphic predicate yet (complex differentiability
      machinery is a carrier gap, loudly recorded in the node card);
      this slice lands the contour algebra and the constant-integrand
      faces.
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [List].  Requires [GaC3_P02_LineIntegralAlg]
      (path carrier, line integral, concat additivity,
      [cploQ]/[coppoQ] bridges), [GaC3_P01_LineIntegralDef] (Cx
      embedding bridges), [CxRealPairCore], [S01_BaseRing], and
      [S02_CauchyComplete] of this development.
    References.  AFP Perrons_Formula (Eberl 2026-06-17): R = rectpath
      (Complex c (-T)) (Complex b T) at :129, Cauchy_theorem_convex_simple
      at :137, contour_integral_rectpath four-edge expansion at :145-151
      (the :143-153 window), the decomposition shape transcribed here;
      Cauchy's theorem itself is HOL-Analysis-internal there (consumed,
      not re-proved), so the tree rebuilds the contour algebra from
      zero at the step carrier.  Card cards_C3 C3-P04; drafts_C3 P04
      statement skeleton.  Proof-strategy note: the four-edge identity
      is assembled structurally from P02's own concat additivity (no
      ring tactic on the multi-segment goal, where the ring blowup is
      content-pinned); [GaC3_P04_cplus_congr_r] is supplied here for
      that assembly.
    Constructivity.  Set-carried statements; zero classical choice;
      all numerics stay in Q (decidable, exact); the decomposition
      chain is purely structural; [coqchk] reports zero assumed
      constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC3_P04_CauchyRect.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3] (-AllowG3 -GearForce 0 -TempLimit 98
      -LoadLimit 60 -CoreN 2). *)

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
(* Section 3. Congruence of c_plus in the second argument (new supply).   *)
(* ===================================================================== *)

(* c_plus respects c_eq componentwise on the right: at the pointwise     *)
(* level (a + b)_n - (a + c)_n = b_n - c_n, so the eventual-closeness    *)
(* witness of c_eq b c serves directly.  This is the first congruence    *)
(* lemma over c_plus/c_eq in the tree; it carries the structural         *)
(* four-edge decomposition below.                                        *)
Lemma GaC3_P04_cplus_congr_r : forall (a b c : Cx),
  c_eq b c -> c_eq (c_plus a b) (c_plus a c).
Proof.
  intros a b c Hbc. revert Hbc.
  destruct a as [ar ai]; destruct b as [br bi]; destruct c as [cr ci];
    destruct ar as [uar Har]; destruct ai as [uai Hai];
    destruct br as [ubr Hbr]; destruct bi as [ubi Hbi];
    destruct cr as [ucr Hcr]; destruct ci as [uci Hci].
  intro Hbc. unfold c_eq in Hbc. unfold c_eq. split.
  - destruct Hbc as [HbR _].
    intros eps Heps. destruct (HbR eps Heps) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn). apply QltT_to_Qlt in HN.
    destruct (proj1 (Qabs_Qlt_condition (ubr n - ucr n) eps) HN) as [Hlow0 Hhigh0].
    assert (Hd : uar n + ubr n - (uar n + ucr n) == ubr n - ucr n) by ring.
    rewrite <- Hd in Hlow0.
    rewrite <- Hd in Hhigh0.
    apply Qlt_to_QltT.
    apply (proj2 (Qabs_Qlt_condition (uar n + ubr n - (uar n + ucr n)) eps)).
    split; assumption.
  - destruct Hbc as [_ HbI].
    intros eps Heps. destruct (HbI eps Heps) as [N HN].
    exists N. intros n Hn.
    specialize (HN n Hn). apply QltT_to_Qlt in HN.
    destruct (proj1 (Qabs_Qlt_condition (ubi n - uci n) eps) HN) as [Hlow0 Hhigh0].
    assert (Hd : uai n + ubi n - (uai n + uci n) == ubi n - uci n) by ring.
    rewrite <- Hd in Hlow0.
    rewrite <- Hd in Hhigh0.
    apply Qlt_to_QltT.
    apply (proj2 (Qabs_Qlt_condition (uai n + ubi n - (uai n + uci n)) eps)).
    split; assumption.
Qed.

(* ===================================================================== *)
(* Section 4. The four-edge decomposition identity (structural).          *)
(* ===================================================================== *)

(* The rectangle integral decomposes into the four edge integrals with   *)
(* arbitrary per-edge value data (the AFP contour_integral_rectpath      *)
(* expansion :145-151 shape; P10 consumes this identity).  Proof: three  *)
(* applications of P02's concat additivity (the boundary list cuts into  *)
(* its head segment plus the rest, definitionally), lifted through the   *)
(* Section 3 congruence - no arithmetic normalization on any multi-      *)
(* segment goal.                                                         *)
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
  assert (H1 : GaC3_P02_plen_ok [((c, -T), (b, -T))] [v1]) by reflexivity.
  assert (H2 : GaC3_P02_plen_ok [((b, -T), (b, T))] [v2]) by reflexivity.
  assert (H3 : GaC3_P02_plen_ok [((b, T), (c, T))] [v3]) by reflexivity.
  unfold GaC3_P04_rect_boundary.
  (* Term-mode assembly (kernel conversion only - no tactic machinery on    *)
  (* multi-segment goals): three concat cuts lifted through the congruence. *)
  assert (Hs1 : c_eq
    (GaC3_P02_line_integral (((c, -T), (b, -T)) :: ((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v1 :: v2 :: v3 :: v4 :: nil))
    (c_plus
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (GaC3_P02_line_integral (((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v2 :: v3 :: v4 :: nil)))).
  { exact (GaC3_P02_line_integral_concat (((c, -T), (b, -T)) :: nil) (((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v1 :: nil) (v2 :: v3 :: v4 :: nil) H1). }
  assert (Hs2 : c_eq
    (c_plus
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (GaC3_P02_line_integral (((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v2 :: v3 :: v4 :: nil)))
    (c_plus
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (c_plus
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (GaC3_P02_line_integral (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v3 :: v4 :: nil))))).
  { exact (GaC3_P04_cplus_congr_r
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (GaC3_P02_line_integral (((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v2 :: v3 :: v4 :: nil))
      (c_plus
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (GaC3_P02_line_integral (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v3 :: v4 :: nil)))
      (GaC3_P02_line_integral_concat (((b, -T), (b, T)) :: nil) (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v2 :: nil) (v3 :: v4 :: nil) H2)). }
  assert (Hs3 : c_eq
    (c_plus
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (c_plus
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (GaC3_P02_line_integral (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v3 :: v4 :: nil))))
    (c_plus
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (c_plus
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (c_plus
          (GaC3_P02_line_integral (((b, T), (c, T)) :: nil) (v3 :: nil))
          (GaC3_P02_line_integral (((c, T), (c, -T)) :: nil) (v4 :: nil)))))).
  { exact (GaC3_P04_cplus_congr_r
      (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
      (c_plus
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (GaC3_P02_line_integral (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v3 :: v4 :: nil)))
      (c_plus
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (c_plus
          (GaC3_P02_line_integral (((b, T), (c, T)) :: nil) (v3 :: nil))
          (GaC3_P02_line_integral (((c, T), (c, -T)) :: nil) (v4 :: nil))))
      (GaC3_P04_cplus_congr_r
        (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
        (GaC3_P02_line_integral (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v3 :: v4 :: nil))
        (c_plus
          (GaC3_P02_line_integral (((b, T), (c, T)) :: nil) (v3 :: nil))
          (GaC3_P02_line_integral (((c, T), (c, -T)) :: nil) (v4 :: nil)))
        (GaC3_P02_line_integral_concat (((b, T), (c, T)) :: nil) (((c, T), (c, -T)) :: nil) (v3 :: nil) (v4 :: nil) H3))). }
  exact (c_eq_trans
    (GaC3_P02_line_integral (((c, -T), (b, -T)) :: ((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v1 :: v2 :: v3 :: v4 :: nil))
    (c_plus (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil)) (GaC3_P02_line_integral (((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v2 :: v3 :: v4 :: nil)))
    (c_plus (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
       (c_plus (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
          (c_plus (GaC3_P02_line_integral (((b, T), (c, T)) :: nil) (v3 :: nil)) (GaC3_P02_line_integral (((c, T), (c, -T)) :: nil) (v4 :: nil)))))
    Hs1
    (c_eq_trans
      (c_plus (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil)) (GaC3_P02_line_integral (((b, -T), (b, T)) :: ((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v2 :: v3 :: v4 :: nil)))
      (c_plus (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
         (c_plus (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil)) (GaC3_P02_line_integral (((b, T), (c, T)) :: ((c, T), (c, -T)) :: nil) (v3 :: v4 :: nil))))
      (c_plus (GaC3_P02_line_integral (((c, -T), (b, -T)) :: nil) (v1 :: nil))
         (c_plus (GaC3_P02_line_integral (((b, -T), (b, T)) :: nil) (v2 :: nil))
            (c_plus (GaC3_P02_line_integral (((b, T), (c, T)) :: nil) (v3 :: nil)) (GaC3_P02_line_integral (((c, T), (c, -T)) :: nil) (v4 :: nil)))))
      Hs2 Hs3)).
Qed.

(* ===================================================================== *)
(* Section 5. The vertical-line shift identity (constant integrand).      *)
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
           (c_opp (GaC3_P02_line_integral (GaC3_P02_hline_seg c b T) [v])))).
Proof.
  intros c b T v.
  unfold GaC3_P02_line_integral. unfold c_eq.
  split; apply real_eq_of_zero_diff; intro n.
  - (* Real component: per-segment identities (small bounded rings), then   *)
    (* structural cancellation - no ring on any multi-segment goal.         *)
    repeat rewrite cRe_plus_pt.
    repeat rewrite cRe_opp_pt.
    repeat rewrite cRe_of_Q_pt.
    assert (Hc : GaC3_P02_path_sumR (GaC3_P02_vline_seg c T) [v]
                 == - (2 * T) * snd v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    assert (Hb : GaC3_P02_path_sumR (GaC3_P02_vline_seg b T) [v]
                 == - (2 * T) * snd v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    assert (Hht : GaC3_P02_path_sumR (GaC3_P02_hline_seg c b (-T)) [v]
                  == (b - c) * fst v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    assert (Hhb : GaC3_P02_path_sumR (GaC3_P02_hline_seg c b T) [v]
                  == (b - c) * fst v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    rewrite Hc. rewrite Hb. rewrite Hht. rewrite Hhb.
    rewrite (Qplus_opp_r ((b - c) * fst v)).
    rewrite Qplus_0_r.
    ring.
  - (* Imag component: mirror. *)
    repeat rewrite cIm_plus_pt.
    repeat rewrite cIm_opp_pt.
    repeat rewrite cIm_of_Q_pt.
    assert (Ic : GaC3_P02_path_sumI (GaC3_P02_vline_seg c T) [v]
                 == 2 * T * fst v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    assert (Ib : GaC3_P02_path_sumI (GaC3_P02_vline_seg b T) [v]
                 == 2 * T * fst v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    assert (Iht : GaC3_P02_path_sumI (GaC3_P02_hline_seg c b (-T)) [v]
                  == (b - c) * snd v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    assert (Ihb : GaC3_P02_path_sumI (GaC3_P02_hline_seg c b T) [v]
                  == (b - c) * snd v)
      by (cbn [GaC3_P02_path_sumR GaC3_P02_path_sumI GaC3_P02_seg_dz GaC3_P02_seg_contrib GaC3_P02_vline_seg GaC3_P02_hline_seg fst snd]; ring).
    rewrite Ic. rewrite Ib. rewrite Iht. rewrite Ihb.
    rewrite (Qplus_opp_r ((b - c) * snd v)).
    rewrite Qplus_0_r.
    ring.
Qed.
