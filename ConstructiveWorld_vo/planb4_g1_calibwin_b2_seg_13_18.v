(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* segment for n = 13..18 (bite anchors, leaf-ified form).               *)
(*                                                                       *)
(* Mission      : Group (b) channel-integrality bites (abqA_int/         *)
(*                abqB_int per n) and Group (c) frozen-table bites       *)
(*                (Acal/Bcal per n) for n = 13..18.  Each anchor is an   *)
(*                independent vm_compute bite; a failing anchor names    *)
(*                its n.                                                 *)
(* Dependencies : planb4_g1_ab_def (planb4_abqA/planb4_abqB);            *)
(*                planb3_g1_calib (the frozen A/B table channels);       *)
(*                stdlib QArith, ZArith.                                 *)
(* References   : ZZ2020 Prop 1 (2^(-floor(5n/2)+2) L_n I_n in Z+Z pi);  *)
(*                planb3_g1_calib A/B channels; the segment shim         *)
(*                planb4_g1_calibwin_b2 (Export form).              *)
(* Constructivity.  No non-constructive escapes; zero premise slot;      *)
(*                every anchor closes by one vm_compute step.            *)
(* Build.  coqc -native-compiler no -q -Q . ""                           *)
(*         planb4_g1_calibwin_b2_seg_13_18.v                        *)
(*         (Rocq 9.3.0; 12-lane pool segment).                           *)
(* ===================================================================== *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.

Example planb4_abqA_int_13 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 13))) (planb4_abqA 13) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_13 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 13))) (planb4_abqB 13) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_14 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 14))) (planb4_abqA 14) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_14 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 14))) (planb4_abqB 14) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_15 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 15))) (planb4_abqA 15) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_15 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 15))) (planb4_abqB 15) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_16 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 16))) (planb4_abqA 16) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_16 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 16))) (planb4_abqB 16) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_17 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 17))) (planb4_abqA 17) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_17 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 17))) (planb4_abqB 17) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_18 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 18))) (planb4_abqA 18) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_18 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 18))) (planb4_abqB 18) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_13 :
  Z.eqb (Qnum (planb4_abqA 13)) (planb3_g1_A 13) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_13 :
  Z.eqb (Qnum (planb4_abqB 13)) (planb3_g1_B 13) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_14 :
  Z.eqb (Qnum (planb4_abqA 14)) (planb3_g1_A 14) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_14 :
  Z.eqb (Qnum (planb4_abqB 14)) (planb3_g1_B 14) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_15 :
  Z.eqb (Qnum (planb4_abqA 15)) (planb3_g1_A 15) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_15 :
  Z.eqb (Qnum (planb4_abqB 15)) (planb3_g1_B 15) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_16 :
  Z.eqb (Qnum (planb4_abqA 16)) (planb3_g1_A 16) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_16 :
  Z.eqb (Qnum (planb4_abqB 16)) (planb3_g1_B 16) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_17 :
  Z.eqb (Qnum (planb4_abqA 17)) (planb3_g1_A 17) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_17 :
  Z.eqb (Qnum (planb4_abqB 17)) (planb3_g1_B 17) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_18 :
  Z.eqb (Qnum (planb4_abqA 18)) (planb3_g1_A 18) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_18 :
  Z.eqb (Qnum (planb4_abqB 18)) (planb3_g1_B 18) = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions planb4_abqA_int_13.
Print Assumptions planb4_abqB_int_13.
Print Assumptions planb4_abqA_int_14.
Print Assumptions planb4_abqB_int_14.
Print Assumptions planb4_abqA_int_15.
Print Assumptions planb4_abqB_int_15.
Print Assumptions planb4_abqA_int_16.
Print Assumptions planb4_abqB_int_16.
Print Assumptions planb4_abqA_int_17.
Print Assumptions planb4_abqB_int_17.
Print Assumptions planb4_abqA_int_18.
Print Assumptions planb4_abqB_int_18.
Print Assumptions planb4_ab_Acal_13.
Print Assumptions planb4_ab_Bcal_13.
Print Assumptions planb4_ab_Acal_14.
Print Assumptions planb4_ab_Bcal_14.
Print Assumptions planb4_ab_Acal_15.
Print Assumptions planb4_ab_Bcal_15.
Print Assumptions planb4_ab_Acal_16.
Print Assumptions planb4_ab_Bcal_16.
Print Assumptions planb4_ab_Acal_17.
Print Assumptions planb4_ab_Bcal_17.
Print Assumptions planb4_ab_Acal_18.
Print Assumptions planb4_ab_Bcal_18.
