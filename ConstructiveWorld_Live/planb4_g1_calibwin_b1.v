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
From Stdlib Require Import ZArith.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.

(* ================================================================== *)
(* Group (b): both assembled channels are integer-valued rationals    *)
(* at every n of the segment (Q representation free: Qeq_bool through *)
(* the Qnum/inject_Z round trip; the ab_def statement shape, per n).  *)
(* ================================================================== *)

Example planb4_abqA_int_7 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 7))) (planb4_abqA 7) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_7 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 7))) (planb4_abqB 7) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_8 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 8))) (planb4_abqA 8) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_8 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 8))) (planb4_abqB 8) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_9 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 9))) (planb4_abqA 9) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_9 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 9))) (planb4_abqB 9) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_10 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 10))) (planb4_abqA 10) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_10 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 10))) (planb4_abqB 10) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_11 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 11))) (planb4_abqA 11) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_11 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 11))) (planb4_abqB 11) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_12 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 12))) (planb4_abqA 12) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_12 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 12))) (planb4_abqB 12) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n).                   *)
(* ================================================================== *)

Example planb4_ab_Acal_7 :
  Z.eqb (Qnum (planb4_abqA 7)) (planb3_g1_A 7) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_7 :
  Z.eqb (Qnum (planb4_abqB 7)) (planb3_g1_B 7) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_8 :
  Z.eqb (Qnum (planb4_abqA 8)) (planb3_g1_A 8) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_8 :
  Z.eqb (Qnum (planb4_abqB 8)) (planb3_g1_B 8) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_9 :
  Z.eqb (Qnum (planb4_abqA 9)) (planb3_g1_A 9) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_9 :
  Z.eqb (Qnum (planb4_abqB 9)) (planb3_g1_B 9) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_10 :
  Z.eqb (Qnum (planb4_abqA 10)) (planb3_g1_A 10) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_10 :
  Z.eqb (Qnum (planb4_abqB 10)) (planb3_g1_B 10) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_11 :
  Z.eqb (Qnum (planb4_abqA 11)) (planb3_g1_A 11) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_11 :
  Z.eqb (Qnum (planb4_abqB 11)) (planb3_g1_B 11) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_12 :
  Z.eqb (Qnum (planb4_abqA 12)) (planb3_g1_A 12) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_12 :
  Z.eqb (Qnum (planb4_abqB 12)) (planb3_g1_B 12) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_7.
Print Assumptions planb4_abqB_int_7.
Print Assumptions planb4_ab_Acal_7.
Print Assumptions planb4_ab_Bcal_7.
Print Assumptions planb4_abqA_int_8.
Print Assumptions planb4_abqB_int_8.
Print Assumptions planb4_ab_Acal_8.
Print Assumptions planb4_ab_Bcal_8.
Print Assumptions planb4_abqA_int_9.
Print Assumptions planb4_abqB_int_9.
Print Assumptions planb4_ab_Acal_9.
Print Assumptions planb4_ab_Bcal_9.
Print Assumptions planb4_abqA_int_10.
Print Assumptions planb4_abqB_int_10.
Print Assumptions planb4_ab_Acal_10.
Print Assumptions planb4_ab_Bcal_10.
Print Assumptions planb4_abqA_int_11.
Print Assumptions planb4_abqB_int_11.
Print Assumptions planb4_ab_Acal_11.
Print Assumptions planb4_ab_Bcal_11.
Print Assumptions planb4_abqA_int_12.
Print Assumptions planb4_abqB_int_12.
Print Assumptions planb4_ab_Acal_12.
Print Assumptions planb4_ab_Bcal_12.
