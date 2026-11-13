(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 6 of 6: n = 37..40.                            *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b6: anchor groups (b)/(c) point-wise, n = 37..40.

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

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_calibwin_b6.v
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

Example planb4_abqA_int_37 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 37))) (planb4_abqA 37) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_37 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 37))) (planb4_abqB 37) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_38 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 38))) (planb4_abqA 38) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_38 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 38))) (planb4_abqB 38) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_39 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 39))) (planb4_abqA 39) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_39 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 39))) (planb4_abqB 39) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqA_int_40 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 40))) (planb4_abqA 40) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_abqB_int_40 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 40))) (planb4_abqB 40) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n).                   *)
(* ================================================================== *)

Example planb4_ab_Acal_37 :
  Z.eqb (Qnum (planb4_abqA 37)) (planb3_g1_A 37) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_37 :
  Z.eqb (Qnum (planb4_abqB 37)) (planb3_g1_B 37) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_38 :
  Z.eqb (Qnum (planb4_abqA 38)) (planb3_g1_A 38) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_38 :
  Z.eqb (Qnum (planb4_abqB 38)) (planb3_g1_B 38) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_39 :
  Z.eqb (Qnum (planb4_abqA 39)) (planb3_g1_A 39) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_39 :
  Z.eqb (Qnum (planb4_abqB 39)) (planb3_g1_B 39) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Acal_40 :
  Z.eqb (Qnum (planb4_abqA 40)) (planb3_g1_A 40) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_ab_Bcal_40 :
  Z.eqb (Qnum (planb4_abqB 40)) (planb3_g1_B 40) = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_37.
Print Assumptions planb4_abqB_int_37.
Print Assumptions planb4_ab_Acal_37.
Print Assumptions planb4_ab_Bcal_37.
Print Assumptions planb4_abqA_int_38.
Print Assumptions planb4_abqB_int_38.
Print Assumptions planb4_ab_Acal_38.
Print Assumptions planb4_ab_Bcal_38.
Print Assumptions planb4_abqA_int_39.
Print Assumptions planb4_abqB_int_39.
Print Assumptions planb4_ab_Acal_39.
Print Assumptions planb4_ab_Bcal_39.
Print Assumptions planb4_abqA_int_40.
Print Assumptions planb4_abqB_int_40.
Print Assumptions planb4_ab_Acal_40.
Print Assumptions planb4_ab_Bcal_40.
