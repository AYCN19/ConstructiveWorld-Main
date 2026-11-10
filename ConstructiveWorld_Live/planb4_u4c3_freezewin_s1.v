(* ConstructiveWorld-Main - U4-C3 segment s1: pointwise frozen-window   *)
(* bites n = 1..8 (A/B table bites and Laurent pole symmetry).      *)

(** * planb4_u4c3_freezewin_s1: pointwise bites, n = 1..8.
    Mission.  The per-point machine bites feeding the k = 40 census
      assembly in planb4_u4c3_freezewin_40.v: per n of 1..8 the
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
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_s1.v
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

Example planb4_u4c3_A_pt_1 : Z.eqb (planb4_g1_A 1%nat) (planb3_g1_A 1%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_2 : Z.eqb (planb4_g1_A 2%nat) (planb3_g1_A 2%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_3 : Z.eqb (planb4_g1_A 3%nat) (planb3_g1_A 3%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_4 : Z.eqb (planb4_g1_A 4%nat) (planb3_g1_A 4%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_5 : Z.eqb (planb4_g1_A 5%nat) (planb3_g1_A 5%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_6 : Z.eqb (planb4_g1_A 6%nat) (planb3_g1_A 6%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_7 : Z.eqb (planb4_g1_A 7%nat) (planb3_g1_A 7%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_8 : Z.eqb (planb4_g1_A 8%nat) (planb3_g1_A 8%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_1 : Z.eqb (planb4_g1_B 1%nat) (planb3_g1_B 1%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_2 : Z.eqb (planb4_g1_B 2%nat) (planb3_g1_B 2%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_3 : Z.eqb (planb4_g1_B 3%nat) (planb3_g1_B 3%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_4 : Z.eqb (planb4_g1_B 4%nat) (planb3_g1_B 4%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_5 : Z.eqb (planb4_g1_B 5%nat) (planb3_g1_B 5%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_6 : Z.eqb (planb4_g1_B 6%nat) (planb3_g1_B 6%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_7 : Z.eqb (planb4_g1_B 7%nat) (planb3_g1_B 7%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_8 : Z.eqb (planb4_g1_B 8%nat) (planb3_g1_B 8%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_1 : zz_lqeqb (planb4_g1_poleA 1%nat) (planb4_g1_poleB 1%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_2 : zz_lqeqb (planb4_g1_poleA 2%nat) (planb4_g1_poleB 2%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_3 : zz_lqeqb (planb4_g1_poleA 3%nat) (planb4_g1_poleB 3%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_4 : zz_lqeqb (planb4_g1_poleA 4%nat) (planb4_g1_poleB 4%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_5 : zz_lqeqb (planb4_g1_poleA 5%nat) (planb4_g1_poleB 5%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_6 : zz_lqeqb (planb4_g1_poleA 6%nat) (planb4_g1_poleB 6%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_7 : zz_lqeqb (planb4_g1_poleA 7%nat) (planb4_g1_poleB 7%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_8 : zz_lqeqb (planb4_g1_poleA 8%nat) (planb4_g1_poleB 8%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* Section 2. Range Lemmas: explicit enumeration, lia tail. *)

Lemma planb4_u4c3_A_rng_s1 : forall n : nat, (1 <= n <= 8)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 1%nat).
  { subst. apply planb4_u4c3_A_pt_1. }
  destruct (Nat.eq_dec n 2%nat).
  { subst. apply planb4_u4c3_A_pt_2. }
  destruct (Nat.eq_dec n 3%nat).
  { subst. apply planb4_u4c3_A_pt_3. }
  destruct (Nat.eq_dec n 4%nat).
  { subst. apply planb4_u4c3_A_pt_4. }
  destruct (Nat.eq_dec n 5%nat).
  { subst. apply planb4_u4c3_A_pt_5. }
  destruct (Nat.eq_dec n 6%nat).
  { subst. apply planb4_u4c3_A_pt_6. }
  destruct (Nat.eq_dec n 7%nat).
  { subst. apply planb4_u4c3_A_pt_7. }
  destruct (Nat.eq_dec n 8%nat).
  { subst. apply planb4_u4c3_A_pt_8. }
  lia.
Qed.

Lemma planb4_u4c3_B_rng_s1 : forall n : nat, (1 <= n <= 8)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 1%nat).
  { subst. apply planb4_u4c3_B_pt_1. }
  destruct (Nat.eq_dec n 2%nat).
  { subst. apply planb4_u4c3_B_pt_2. }
  destruct (Nat.eq_dec n 3%nat).
  { subst. apply planb4_u4c3_B_pt_3. }
  destruct (Nat.eq_dec n 4%nat).
  { subst. apply planb4_u4c3_B_pt_4. }
  destruct (Nat.eq_dec n 5%nat).
  { subst. apply planb4_u4c3_B_pt_5. }
  destruct (Nat.eq_dec n 6%nat).
  { subst. apply planb4_u4c3_B_pt_6. }
  destruct (Nat.eq_dec n 7%nat).
  { subst. apply planb4_u4c3_B_pt_7. }
  destruct (Nat.eq_dec n 8%nat).
  { subst. apply planb4_u4c3_B_pt_8. }
  lia.
Qed.

Lemma planb4_u4c3_sym_rng_s1 : forall n : nat, (1 <= n <= 8)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 1%nat).
  { subst. apply planb4_u4c3_sym_pt_1. }
  destruct (Nat.eq_dec n 2%nat).
  { subst. apply planb4_u4c3_sym_pt_2. }
  destruct (Nat.eq_dec n 3%nat).
  { subst. apply planb4_u4c3_sym_pt_3. }
  destruct (Nat.eq_dec n 4%nat).
  { subst. apply planb4_u4c3_sym_pt_4. }
  destruct (Nat.eq_dec n 5%nat).
  { subst. apply planb4_u4c3_sym_pt_5. }
  destruct (Nat.eq_dec n 6%nat).
  { subst. apply planb4_u4c3_sym_pt_6. }
  destruct (Nat.eq_dec n 7%nat).
  { subst. apply planb4_u4c3_sym_pt_7. }
  destruct (Nat.eq_dec n 8%nat).
  { subst. apply planb4_u4c3_sym_pt_8. }
  lia.
Qed.

(* Section 3. Assumption audit. *)

Print Assumptions planb4_u4c3_A_pt_1.
Print Assumptions planb4_u4c3_A_pt_2.
Print Assumptions planb4_u4c3_A_pt_3.
Print Assumptions planb4_u4c3_A_pt_4.
Print Assumptions planb4_u4c3_A_pt_5.
Print Assumptions planb4_u4c3_A_pt_6.
Print Assumptions planb4_u4c3_A_pt_7.
Print Assumptions planb4_u4c3_A_pt_8.
Print Assumptions planb4_u4c3_B_pt_1.
Print Assumptions planb4_u4c3_B_pt_2.
Print Assumptions planb4_u4c3_B_pt_3.
Print Assumptions planb4_u4c3_B_pt_4.
Print Assumptions planb4_u4c3_B_pt_5.
Print Assumptions planb4_u4c3_B_pt_6.
Print Assumptions planb4_u4c3_B_pt_7.
Print Assumptions planb4_u4c3_B_pt_8.
Print Assumptions planb4_u4c3_sym_pt_1.
Print Assumptions planb4_u4c3_sym_pt_2.
Print Assumptions planb4_u4c3_sym_pt_3.
Print Assumptions planb4_u4c3_sym_pt_4.
Print Assumptions planb4_u4c3_sym_pt_5.
Print Assumptions planb4_u4c3_sym_pt_6.
Print Assumptions planb4_u4c3_sym_pt_7.
Print Assumptions planb4_u4c3_sym_pt_8.
Print Assumptions planb4_u4c3_A_rng_s1.
Print Assumptions planb4_u4c3_B_rng_s1.
Print Assumptions planb4_u4c3_sym_rng_s1.
