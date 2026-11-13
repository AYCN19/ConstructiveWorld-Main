(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 5 of 6: n = 31..36.                            *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b5: anchor groups (b)/(c) point-wise, n = 31..36.

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

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_calibwin_b5.v
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

Example planb4_abqA_int_31 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 31))) (planb4_abqA 31) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_31 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 31))) (planb4_abqB 31) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_32 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 32))) (planb4_abqA 32) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_32 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 32))) (planb4_abqB 32) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_33 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 33))) (planb4_abqA 33) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_33 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 33))) (planb4_abqB 33) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_34 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 34))) (planb4_abqA 34) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_34 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 34))) (planb4_abqB 34) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_35 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 35))) (planb4_abqA 35) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_35 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 35))) (planb4_abqB 35) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_36 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 36))) (planb4_abqA 36) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_36 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 36))) (planb4_abqB 36) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n).                   *)
(* ================================================================== *)

Example planb4_ab_Acal_31 :
  Z.eqb (Qnum (planb4_abqA 31)) (planb3_g1_A 31) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_31 :
  Z.eqb (Qnum (planb4_abqB 31)) (planb3_g1_B 31) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_32 :
  Z.eqb (Qnum (planb4_abqA 32)) (planb3_g1_A 32) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_32 :
  Z.eqb (Qnum (planb4_abqB 32)) (planb3_g1_B 32) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_33 :
  Z.eqb (Qnum (planb4_abqA 33)) (planb3_g1_A 33) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_33 :
  Z.eqb (Qnum (planb4_abqB 33)) (planb3_g1_B 33) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_34 :
  Z.eqb (Qnum (planb4_abqA 34)) (planb3_g1_A 34) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_34 :
  Z.eqb (Qnum (planb4_abqB 34)) (planb3_g1_B 34) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_35 :
  Z.eqb (Qnum (planb4_abqA 35)) (planb3_g1_A 35) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_35 :
  Z.eqb (Qnum (planb4_abqB 35)) (planb3_g1_B 35) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_36 :
  Z.eqb (Qnum (planb4_abqA 36)) (planb3_g1_A 36) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_36 :
  Z.eqb (Qnum (planb4_abqB 36)) (planb3_g1_B 36) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_31.
Print Assumptions planb4_abqB_int_31.
Print Assumptions planb4_ab_Acal_31.
Print Assumptions planb4_ab_Bcal_31.
Print Assumptions planb4_abqA_int_32.
Print Assumptions planb4_abqB_int_32.
Print Assumptions planb4_ab_Acal_32.
Print Assumptions planb4_ab_Bcal_32.
Print Assumptions planb4_abqA_int_33.
Print Assumptions planb4_abqB_int_33.
Print Assumptions planb4_ab_Acal_33.
Print Assumptions planb4_ab_Bcal_33.
Print Assumptions planb4_abqA_int_34.
Print Assumptions planb4_abqB_int_34.
Print Assumptions planb4_ab_Acal_34.
Print Assumptions planb4_ab_Bcal_34.
Print Assumptions planb4_abqA_int_35.
Print Assumptions planb4_abqB_int_35.
Print Assumptions planb4_ab_Acal_35.
Print Assumptions planb4_ab_Bcal_35.
Print Assumptions planb4_abqA_int_36.
Print Assumptions planb4_abqB_int_36.
Print Assumptions planb4_ab_Acal_36.
Print Assumptions planb4_ab_Bcal_36.
