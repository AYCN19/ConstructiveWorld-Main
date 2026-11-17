(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 1 of 6: n = 7..12.                            *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b1: anchor groups (b)/(c) point-wise, n = 7..12.

    Mission.  The planb4_g1_ab_def born-window anchors continued
      past n = 6: group (b) the integrality round trip
      [Qeq_bool (inject_Z (Qnum q)) q = true] over both assembled
      channels; group (c) the assembled [Qnum] values bite the
      frozen [planb3_g1_A]/[planb3_g1_B] table channels (the
      single-source table md5 f2e56ff27c667de6b077e87e7c5c7b70).
      One Example per channel per n, each an independent
      vm_compute bite; a failing anchor names its n.

    Dependencies.  planb4_g1_ab_def (planb4_abqA/planb4_abqB; its
      witness/rs_channel/laur_extract/zzm1b/calib closure compiled
      in tree); stdlib QArith, ZArith.

    References.  ZZ2020 Prop 1 (2^(-floor(5n/2)+2) L_n I_n in
      Z + Z pi); planb3_g1_calib A/B channels n = 1..40.

    Constructivity.  No non-constructive escapes; zero premise slot;
      every anchor closes by one vm_compute step.

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_calibwin_b1.v
      (Rocq 9.3.0; serial single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.
Require Export planb4_g1_calibwin_b1_seg_7_12.
