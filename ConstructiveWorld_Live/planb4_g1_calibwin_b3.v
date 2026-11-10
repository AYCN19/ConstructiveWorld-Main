(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 3 of 6: n = 19..24.                            *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b3: anchor groups (b)/(c) point-wise, n = 19..24.

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

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_calibwin_b3.v
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

Example planb4_abqA_int_19 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 19))) (planb4_abqA 19) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_19 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 19))) (planb4_abqB 19) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_20 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 20))) (planb4_abqA 20) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_20 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 20))) (planb4_abqB 20) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_21 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 21))) (planb4_abqA 21) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_21 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 21))) (planb4_abqB 21) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_22 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 22))) (planb4_abqA 22) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_22 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 22))) (planb4_abqB 22) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_23 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 23))) (planb4_abqA 23) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_23 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 23))) (planb4_abqB 23) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_24 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 24))) (planb4_abqA 24) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_24 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 24))) (planb4_abqB 24) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n).                   *)
(* ================================================================== *)

Example planb4_ab_Acal_19 :
  Z.eqb (Qnum (planb4_abqA 19)) (planb3_g1_A 19) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_19 :
  Z.eqb (Qnum (planb4_abqB 19)) (planb3_g1_B 19) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_20 :
  Z.eqb (Qnum (planb4_abqA 20)) (planb3_g1_A 20) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_20 :
  Z.eqb (Qnum (planb4_abqB 20)) (planb3_g1_B 20) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_21 :
  Z.eqb (Qnum (planb4_abqA 21)) (planb3_g1_A 21) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_21 :
  Z.eqb (Qnum (planb4_abqB 21)) (planb3_g1_B 21) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_22 :
  Z.eqb (Qnum (planb4_abqA 22)) (planb3_g1_A 22) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_22 :
  Z.eqb (Qnum (planb4_abqB 22)) (planb3_g1_B 22) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_23 :
  Z.eqb (Qnum (planb4_abqA 23)) (planb3_g1_A 23) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_23 :
  Z.eqb (Qnum (planb4_abqB 23)) (planb3_g1_B 23) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_24 :
  Z.eqb (Qnum (planb4_abqA 24)) (planb3_g1_A 24) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_24 :
  Z.eqb (Qnum (planb4_abqB 24)) (planb3_g1_B 24) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_19.
Print Assumptions planb4_abqB_int_19.
Print Assumptions planb4_ab_Acal_19.
Print Assumptions planb4_ab_Bcal_19.
Print Assumptions planb4_abqA_int_20.
Print Assumptions planb4_abqB_int_20.
Print Assumptions planb4_ab_Acal_20.
Print Assumptions planb4_ab_Bcal_20.
Print Assumptions planb4_abqA_int_21.
Print Assumptions planb4_abqB_int_21.
Print Assumptions planb4_ab_Acal_21.
Print Assumptions planb4_ab_Bcal_21.
Print Assumptions planb4_abqA_int_22.
Print Assumptions planb4_abqB_int_22.
Print Assumptions planb4_ab_Acal_22.
Print Assumptions planb4_ab_Bcal_22.
Print Assumptions planb4_abqA_int_23.
Print Assumptions planb4_abqB_int_23.
Print Assumptions planb4_ab_Acal_23.
Print Assumptions planb4_ab_Bcal_23.
Print Assumptions planb4_abqA_int_24.
Print Assumptions planb4_abqB_int_24.
Print Assumptions planb4_ab_Acal_24.
Print Assumptions planb4_ab_Bcal_24.
