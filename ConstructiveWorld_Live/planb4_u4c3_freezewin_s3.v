(* ConstructiveWorld-Main - U4-C3 segment s3: pointwise frozen-window   *)
(* bites n = 17..24 (A/B table bites and Laurent pole symmetry).      *)

(** * planb4_u4c3_freezewin_s3: pointwise bites, n = 17..24.
    Mission.  The per-point machine bites feeding the k = 40 census
      assembly in planb4_u4c3_freezewin_40.v: per n of 17..24 the
      assembled [planb4_g1_A]/[planb4_g1_B] bite the frozen table
      arms, and the antipodal Laurent readouts agree via [zz_lqeqb];
      one Example per channel per n plus one range Lemma per channel
      (fail-loud: a failing bite names its n).
    Dependencies.  planb4_u4c3_freezewin_cert (the census carriers);
      planb4_g1_rs_assembly; planb3_g1_calib; planb4_g1_laur_extract;
      zzm1b_linform_bridge (zz_lqeqb).
    References.  ZZ2020 Prop 1; planb3_g1_calib A/B tables
      n = 1..40; the pointwise discipline of rs_assembly.v:226-236.
    Constructivity.  One vm_compute step per bite; admission-free
      and postulate-free throughout.
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_s3.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import planb3_g1_calib.
Require Import zzm1b_linform_bridge.
Require Import planb4_g1_laur_extract.
Require Import planb4_g1_rs_assembly.
Require Import planb4_u4c3_freezewin_cert.

(* Section 1. Per-point bites: A/B table bites, pole symmetry. *)

Example planb4_u4c3_A_pt_17 : Z.eqb (planb4_g1_A 17%nat) (planb3_g1_A 17%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_18 : Z.eqb (planb4_g1_A 18%nat) (planb3_g1_A 18%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_19 : Z.eqb (planb4_g1_A 19%nat) (planb3_g1_A 19%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_20 : Z.eqb (planb4_g1_A 20%nat) (planb3_g1_A 20%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_21 : Z.eqb (planb4_g1_A 21%nat) (planb3_g1_A 21%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_22 : Z.eqb (planb4_g1_A 22%nat) (planb3_g1_A 22%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_23 : Z.eqb (planb4_g1_A 23%nat) (planb3_g1_A 23%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_24 : Z.eqb (planb4_g1_A 24%nat) (planb3_g1_A 24%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_17 : Z.eqb (planb4_g1_B 17%nat) (planb3_g1_B 17%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_18 : Z.eqb (planb4_g1_B 18%nat) (planb3_g1_B 18%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_19 : Z.eqb (planb4_g1_B 19%nat) (planb3_g1_B 19%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_20 : Z.eqb (planb4_g1_B 20%nat) (planb3_g1_B 20%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_21 : Z.eqb (planb4_g1_B 21%nat) (planb3_g1_B 21%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_22 : Z.eqb (planb4_g1_B 22%nat) (planb3_g1_B 22%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_23 : Z.eqb (planb4_g1_B 23%nat) (planb3_g1_B 23%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_24 : Z.eqb (planb4_g1_B 24%nat) (planb3_g1_B 24%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_17 : zz_lqeqb (planb4_g1_poleA 17%nat) (planb4_g1_poleB 17%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_18 : zz_lqeqb (planb4_g1_poleA 18%nat) (planb4_g1_poleB 18%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_19 : zz_lqeqb (planb4_g1_poleA 19%nat) (planb4_g1_poleB 19%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_20 : zz_lqeqb (planb4_g1_poleA 20%nat) (planb4_g1_poleB 20%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_21 : zz_lqeqb (planb4_g1_poleA 21%nat) (planb4_g1_poleB 21%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_22 : zz_lqeqb (planb4_g1_poleA 22%nat) (planb4_g1_poleB 22%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_23 : zz_lqeqb (planb4_g1_poleA 23%nat) (planb4_g1_poleB 23%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_24 : zz_lqeqb (planb4_g1_poleA 24%nat) (planb4_g1_poleB 24%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* Section 2. Range Lemmas: explicit enumeration, lia tail. *)

Lemma planb4_u4c3_A_rng_s3 : forall n : nat, (17 <= n <= 24)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 17%nat).
  { subst. apply planb4_u4c3_A_pt_17. }
  destruct (Nat.eq_dec n 18%nat).
  { subst. apply planb4_u4c3_A_pt_18. }
  destruct (Nat.eq_dec n 19%nat).
  { subst. apply planb4_u4c3_A_pt_19. }
  destruct (Nat.eq_dec n 20%nat).
  { subst. apply planb4_u4c3_A_pt_20. }
  destruct (Nat.eq_dec n 21%nat).
  { subst. apply planb4_u4c3_A_pt_21. }
  destruct (Nat.eq_dec n 22%nat).
  { subst. apply planb4_u4c3_A_pt_22. }
  destruct (Nat.eq_dec n 23%nat).
  { subst. apply planb4_u4c3_A_pt_23. }
  destruct (Nat.eq_dec n 24%nat).
  { subst. apply planb4_u4c3_A_pt_24. }
  lia.
Qed.

Lemma planb4_u4c3_B_rng_s3 : forall n : nat, (17 <= n <= 24)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 17%nat).
  { subst. apply planb4_u4c3_B_pt_17. }
  destruct (Nat.eq_dec n 18%nat).
  { subst. apply planb4_u4c3_B_pt_18. }
  destruct (Nat.eq_dec n 19%nat).
  { subst. apply planb4_u4c3_B_pt_19. }
  destruct (Nat.eq_dec n 20%nat).
  { subst. apply planb4_u4c3_B_pt_20. }
  destruct (Nat.eq_dec n 21%nat).
  { subst. apply planb4_u4c3_B_pt_21. }
  destruct (Nat.eq_dec n 22%nat).
  { subst. apply planb4_u4c3_B_pt_22. }
  destruct (Nat.eq_dec n 23%nat).
  { subst. apply planb4_u4c3_B_pt_23. }
  destruct (Nat.eq_dec n 24%nat).
  { subst. apply planb4_u4c3_B_pt_24. }
  lia.
Qed.

Lemma planb4_u4c3_sym_rng_s3 : forall n : nat, (17 <= n <= 24)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 17%nat).
  { subst. apply planb4_u4c3_sym_pt_17. }
  destruct (Nat.eq_dec n 18%nat).
  { subst. apply planb4_u4c3_sym_pt_18. }
  destruct (Nat.eq_dec n 19%nat).
  { subst. apply planb4_u4c3_sym_pt_19. }
  destruct (Nat.eq_dec n 20%nat).
  { subst. apply planb4_u4c3_sym_pt_20. }
  destruct (Nat.eq_dec n 21%nat).
  { subst. apply planb4_u4c3_sym_pt_21. }
  destruct (Nat.eq_dec n 22%nat).
  { subst. apply planb4_u4c3_sym_pt_22. }
  destruct (Nat.eq_dec n 23%nat).
  { subst. apply planb4_u4c3_sym_pt_23. }
  destruct (Nat.eq_dec n 24%nat).
  { subst. apply planb4_u4c3_sym_pt_24. }
  lia.
Qed.

(* Section 3. Assumption audit. *)

Print Assumptions planb4_u4c3_A_pt_17.
Print Assumptions planb4_u4c3_A_pt_18.
Print Assumptions planb4_u4c3_A_pt_19.
Print Assumptions planb4_u4c3_A_pt_20.
Print Assumptions planb4_u4c3_A_pt_21.
Print Assumptions planb4_u4c3_A_pt_22.
Print Assumptions planb4_u4c3_A_pt_23.
Print Assumptions planb4_u4c3_A_pt_24.
Print Assumptions planb4_u4c3_B_pt_17.
Print Assumptions planb4_u4c3_B_pt_18.
Print Assumptions planb4_u4c3_B_pt_19.
Print Assumptions planb4_u4c3_B_pt_20.
Print Assumptions planb4_u4c3_B_pt_21.
Print Assumptions planb4_u4c3_B_pt_22.
Print Assumptions planb4_u4c3_B_pt_23.
Print Assumptions planb4_u4c3_B_pt_24.
Print Assumptions planb4_u4c3_sym_pt_17.
Print Assumptions planb4_u4c3_sym_pt_18.
Print Assumptions planb4_u4c3_sym_pt_19.
Print Assumptions planb4_u4c3_sym_pt_20.
Print Assumptions planb4_u4c3_sym_pt_21.
Print Assumptions planb4_u4c3_sym_pt_22.
Print Assumptions planb4_u4c3_sym_pt_23.
Print Assumptions planb4_u4c3_sym_pt_24.
Print Assumptions planb4_u4c3_A_rng_s3.
Print Assumptions planb4_u4c3_B_rng_s3.
Print Assumptions planb4_u4c3_sym_rng_s3.
