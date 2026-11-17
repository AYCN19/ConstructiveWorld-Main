(* Segment b1 n=7..12: bite anchors (leaf-ified form). *)

From Stdlib Require Import QArith. ZArith.
Require Import planb4_g1_ab_def. planb3_g1_calib.

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
Print Assumptions planb4_abqA_int_7.
Print Assumptions planb4_abqB_int_7.
Print Assumptions planb4_abqA_int_8.
Print Assumptions planb4_abqB_int_8.
Print Assumptions planb4_abqA_int_9.
Print Assumptions planb4_abqB_int_9.
Print Assumptions planb4_abqA_int_10.
Print Assumptions planb4_abqB_int_10.
Print Assumptions planb4_abqA_int_11.
Print Assumptions planb4_abqB_int_11.
Print Assumptions planb4_abqA_int_12.
Print Assumptions planb4_abqB_int_12.
Print Assumptions planb4_ab_Acal_7.
Print Assumptions planb4_ab_Bcal_7.
Print Assumptions planb4_ab_Acal_8.
Print Assumptions planb4_ab_Bcal_8.
Print Assumptions planb4_ab_Acal_9.
Print Assumptions planb4_ab_Bcal_9.
Print Assumptions planb4_ab_Acal_10.
Print Assumptions planb4_ab_Bcal_10.
Print Assumptions planb4_ab_Acal_11.
Print Assumptions planb4_ab_Bcal_11.
Print Assumptions planb4_ab_Acal_12.
Print Assumptions planb4_ab_Bcal_12.
