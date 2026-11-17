(* Segment b2 n=13..18: bite anchors (leaf-ified form). *)

From Stdlib Require Import QArith. ZArith.
Require Import planb4_g1_ab_def. planb3_g1_calib.

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
