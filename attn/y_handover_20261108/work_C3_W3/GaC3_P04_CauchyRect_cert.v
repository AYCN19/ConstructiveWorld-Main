(* ===================================================================== *)
(* GaC3_P04_CauchyRect_cert.v                                             *)
(*                                                                       *)
(* Mission: node C3-P04 certificate face (R2 discipline): exact-Q spot    *)
(*   certificates of the rectangular-contour faces at concrete rectangle  *)
(*   data (c = 3, b = 7, T = 5): the closed-loop cancellation of the      *)
(*   constant integrand (both components zero), the four-edge            *)
(*   decomposition component values under distinct per-edge data, and    *)
(*   the vertical-line shift component values - all discharged by        *)
(*   vm_compute.  The proof-topology face (GaC3_P04_CauchyRect.v)        *)
(*   carries zero vm_compute (LINT-5 word-face split; this cert file     *)
(*   holds the computational word-face by design).  The node card marks  *)
(*   the general computational face of C3-P04 as none: these are spot    *)
(*   certificates on literal rectangle data, not closed forms.           *)
(* Dependencies: GaC3_P04_CauchyRect (stem of the same node - the        *)
(*   C3-P03 stem+cert closed-set precedent), GaC3_P02_LineIntegralAlg    *)
(*   (path carrier).  Stdlib: QArith, List.                              *)
(* Constructivity: certificate word-face only; zero Axiom, zero          *)
(*   Parameter; all data in Q (decidable, exact).                        *)
(* Build: coqc -native-compiler no -q (sandbox -Q paths), cpu_guard v3    *)
(*   wrapper (-AllowG3 -GearForce 0 -TempLimit 98 -LoadLimit 60 -CoreN 2). *)
(* References: AFP Perrons_Formula (Eberl 2026-06-17) rectpath window    *)
(*   :129-153 (the shapes transcribed in the stem); cards_C3 C3-P04      *)
(*   incl. 20261103 AFP comparison record.  Spot literals cross-checked  *)
(*   machine-outside (python -I, fractions, 20261104): constant loop     *)
(*   total (0,0); four-edge total (-28,-44); vline c (3): (-10,20).      *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P04_CauchyRect.

Local Open Scope Q_scope.
Import ListNotations.

(* ===================================================================== *)
(* Section 1. Closed-loop cancellation of a constant integrand (spot).    *)
(* ===================================================================== *)

(* Rectangle c=3, b=7, T=5, constant value v=(2,1): both component sums  *)
(* vanish (machine-outside cross-check: per-edge (8,4), (-10,20),        *)
(* (-8,-4), (10,-20); total (0,0)).                                      *)
Lemma GaC3_P04_cert_rect_const_sample_R :
  GaC3_P02_path_sumR (GaC3_P04_rect_boundary 3 7 5)
    [(2, 1); (2, 1); (2, 1); (2, 1)] == 0.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC3_P04_cert_rect_const_sample_I :
  GaC3_P02_path_sumI (GaC3_P04_rect_boundary 3 7 5)
    [(2, 1); (2, 1); (2, 1); (2, 1)] == 0.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* Section 2. Four-edge decomposition component values (distinct data).   *)
(* ===================================================================== *)

(* Distinct per-edge values v1..v4 (machine-outside cross-check: bottom  *)
(* (8,4), right (-30,0), top (4,-8), left (-10,-40); total (-28,-44)).   *)
Lemma GaC3_P04_cert_four_edges_sample_R :
  GaC3_P02_path_sumR (GaC3_P04_rect_boundary 3 7 5)
    [(2, 1); (0, 3); (-1, 2); (4, -1)] == -28.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC3_P04_cert_four_edges_sample_I :
  GaC3_P02_path_sumI (GaC3_P04_rect_boundary 3 7 5)
    [(2, 1); (0, 3); (-1, 2); (4, -1)] == -44.
Proof. vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* Section 3. Vertical-line shift component values (constant integrand).  *)
(* ===================================================================== *)

(* Shift shape at the constant face (machine-outside cross-check:        *)
(* vline at c=3 is (-10,20); vline at b=7 is (-10,20); bottom hline      *)
(* (hline_seg 3 7 5) is (8,4); top hline (hline_seg 3 7 (-5)) is (8,4);  *)
(* so LHS -10 == -10 + 8 - 8 and 20 == 20 + 4 - 4).                      *)
Lemma GaC3_P04_cert_vline_shift_sample_R :
  GaC3_P02_path_sumR (GaC3_P02_vline_seg 3 5) [(2, 1)]
  == GaC3_P02_path_sumR (GaC3_P02_vline_seg 7 5) [(2, 1)]
     + GaC3_P02_path_sumR (GaC3_P02_hline_seg 3 7 (-5)) [(2, 1)]
     - GaC3_P02_path_sumR (GaC3_P02_hline_seg 3 7 5) [(2, 1)].
Proof. vm_compute; reflexivity. Qed.

Lemma GaC3_P04_cert_vline_shift_sample_I :
  GaC3_P02_path_sumI (GaC3_P02_vline_seg 3 5) [(2, 1)]
  == GaC3_P02_path_sumI (GaC3_P02_vline_seg 7 5) [(2, 1)]
     + GaC3_P02_path_sumI (GaC3_P02_hline_seg 3 7 (-5)) [(2, 1)]
     - GaC3_P02_path_sumI (GaC3_P02_hline_seg 3 7 5) [(2, 1)].
Proof. vm_compute; reflexivity. Qed.
