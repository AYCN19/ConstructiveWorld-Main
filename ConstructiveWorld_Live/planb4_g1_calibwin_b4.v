(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 4 of 6: n = 25..30.                            *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b4: anchor groups (b)/(c) point-wise, n = 25..30.

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

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_calibwin_b4.v
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

Example planb4_abqA_int_25 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 25))) (planb4_abqA 25) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_25 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 25))) (planb4_abqB 25) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_26 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 26))) (planb4_abqA 26) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_26 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 26))) (planb4_abqB 26) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_27 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 27))) (planb4_abqA 27) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_27 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 27))) (planb4_abqB 27) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_28 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 28))) (planb4_abqA 28) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_28 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 28))) (planb4_abqB 28) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_29 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 29))) (planb4_abqA 29) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_29 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 29))) (planb4_abqB 29) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_30 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 30))) (planb4_abqA 30) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_30 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 30))) (planb4_abqB 30) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n).                   *)
(* ================================================================== *)

Example planb4_ab_Acal_25 :
  Z.eqb (Qnum (planb4_abqA 25)) (planb3_g1_A 25) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_25 :
  Z.eqb (Qnum (planb4_abqB 25)) (planb3_g1_B 25) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_26 :
  Z.eqb (Qnum (planb4_abqA 26)) (planb3_g1_A 26) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_26 :
  Z.eqb (Qnum (planb4_abqB 26)) (planb3_g1_B 26) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_27 :
  Z.eqb (Qnum (planb4_abqA 27)) (planb3_g1_A 27) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_27 :
  Z.eqb (Qnum (planb4_abqB 27)) (planb3_g1_B 27) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_28 :
  Z.eqb (Qnum (planb4_abqA 28)) (planb3_g1_A 28) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_28 :
  Z.eqb (Qnum (planb4_abqB 28)) (planb3_g1_B 28) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_29 :
  Z.eqb (Qnum (planb4_abqA 29)) (planb3_g1_A 29) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_29 :
  Z.eqb (Qnum (planb4_abqB 29)) (planb3_g1_B 29) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_30 :
  Z.eqb (Qnum (planb4_abqA 30)) (planb3_g1_A 30) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_30 :
  Z.eqb (Qnum (planb4_abqB 30)) (planb3_g1_B 30) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_25.
Print Assumptions planb4_abqB_int_25.
Print Assumptions planb4_ab_Acal_25.
Print Assumptions planb4_ab_Bcal_25.
Print Assumptions planb4_abqA_int_26.
Print Assumptions planb4_abqB_int_26.
Print Assumptions planb4_ab_Acal_26.
Print Assumptions planb4_ab_Bcal_26.
Print Assumptions planb4_abqA_int_27.
Print Assumptions planb4_abqB_int_27.
Print Assumptions planb4_ab_Acal_27.
Print Assumptions planb4_ab_Bcal_27.
Print Assumptions planb4_abqA_int_28.
Print Assumptions planb4_abqB_int_28.
Print Assumptions planb4_ab_Acal_28.
Print Assumptions planb4_ab_Bcal_28.
Print Assumptions planb4_abqA_int_29.
Print Assumptions planb4_abqB_int_29.
Print Assumptions planb4_ab_Acal_29.
Print Assumptions planb4_ab_Bcal_29.
Print Assumptions planb4_abqA_int_30.
Print Assumptions planb4_abqB_int_30.
Print Assumptions planb4_ab_Acal_30.
Print Assumptions planb4_ab_Bcal_30.
