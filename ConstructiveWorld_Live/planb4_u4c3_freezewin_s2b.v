(* ConstructiveWorld-Main - U4-C3 segment s2b: pointwise frozen-window  *)
(* bites n = 12..16 (A/B table bites and Laurent pole symmetry).      *)

(** * planb4_u4c3_freezewin_s2b: pointwise bites, n = 12..16.
    Mission.  The per-point machine bites feeding the k = 40 census
      assembly in planb4_u4c3_freezewin_40.v: per n of 12..16 the
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
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_s2b.v
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

Example planb4_u4c3_A_pt_12 : Z.eqb (planb4_g1_A 12%nat) (planb3_g1_A 12%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_13 : Z.eqb (planb4_g1_A 13%nat) (planb3_g1_A 13%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_14 : Z.eqb (planb4_g1_A 14%nat) (planb3_g1_A 14%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_15 : Z.eqb (planb4_g1_A 15%nat) (planb3_g1_A 15%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_16 : Z.eqb (planb4_g1_A 16%nat) (planb3_g1_A 16%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_12 : Z.eqb (planb4_g1_B 12%nat) (planb3_g1_B 12%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_13 : Z.eqb (planb4_g1_B 13%nat) (planb3_g1_B 13%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_14 : Z.eqb (planb4_g1_B 14%nat) (planb3_g1_B 14%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_15 : Z.eqb (planb4_g1_B 15%nat) (planb3_g1_B 15%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_16 : Z.eqb (planb4_g1_B 16%nat) (planb3_g1_B 16%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_12 : zz_lqeqb (planb4_g1_poleA 12%nat) (planb4_g1_poleB 12%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_13 : zz_lqeqb (planb4_g1_poleA 13%nat) (planb4_g1_poleB 13%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_14 : zz_lqeqb (planb4_g1_poleA 14%nat) (planb4_g1_poleB 14%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_15 : zz_lqeqb (planb4_g1_poleA 15%nat) (planb4_g1_poleB 15%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_16 : zz_lqeqb (planb4_g1_poleA 16%nat) (planb4_g1_poleB 16%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* Section 2. Range Lemmas: explicit enumeration, lia tail. *)

Lemma planb4_u4c3_A_rng_s2b : forall n : nat, (12 <= n <= 16)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 12%nat).
  { subst. apply planb4_u4c3_A_pt_12. }
  destruct (Nat.eq_dec n 13%nat).
  { subst. apply planb4_u4c3_A_pt_13. }
  destruct (Nat.eq_dec n 14%nat).
  { subst. apply planb4_u4c3_A_pt_14. }
  destruct (Nat.eq_dec n 15%nat).
  { subst. apply planb4_u4c3_A_pt_15. }
  destruct (Nat.eq_dec n 16%nat).
  { subst. apply planb4_u4c3_A_pt_16. }
  lia.
Qed.

Lemma planb4_u4c3_B_rng_s2b : forall n : nat, (12 <= n <= 16)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 12%nat).
  { subst. apply planb4_u4c3_B_pt_12. }
  destruct (Nat.eq_dec n 13%nat).
  { subst. apply planb4_u4c3_B_pt_13. }
  destruct (Nat.eq_dec n 14%nat).
  { subst. apply planb4_u4c3_B_pt_14. }
  destruct (Nat.eq_dec n 15%nat).
  { subst. apply planb4_u4c3_B_pt_15. }
  destruct (Nat.eq_dec n 16%nat).
  { subst. apply planb4_u4c3_B_pt_16. }
  lia.
Qed.

Lemma planb4_u4c3_sym_rng_s2b : forall n : nat, (12 <= n <= 16)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 12%nat).
  { subst. apply planb4_u4c3_sym_pt_12. }
  destruct (Nat.eq_dec n 13%nat).
  { subst. apply planb4_u4c3_sym_pt_13. }
  destruct (Nat.eq_dec n 14%nat).
  { subst. apply planb4_u4c3_sym_pt_14. }
  destruct (Nat.eq_dec n 15%nat).
  { subst. apply planb4_u4c3_sym_pt_15. }
  destruct (Nat.eq_dec n 16%nat).
  { subst. apply planb4_u4c3_sym_pt_16. }
  lia.
Qed.

(* Section 3. Assumption audit. *)

Print Assumptions planb4_u4c3_A_pt_12.
Print Assumptions planb4_u4c3_A_pt_13.
Print Assumptions planb4_u4c3_A_pt_14.
Print Assumptions planb4_u4c3_A_pt_15.
Print Assumptions planb4_u4c3_A_pt_16.
Print Assumptions planb4_u4c3_B_pt_12.
Print Assumptions planb4_u4c3_B_pt_13.
Print Assumptions planb4_u4c3_B_pt_14.
Print Assumptions planb4_u4c3_B_pt_15.
Print Assumptions planb4_u4c3_B_pt_16.
Print Assumptions planb4_u4c3_sym_pt_12.
Print Assumptions planb4_u4c3_sym_pt_13.
Print Assumptions planb4_u4c3_sym_pt_14.
Print Assumptions planb4_u4c3_sym_pt_15.
Print Assumptions planb4_u4c3_sym_pt_16.
Print Assumptions planb4_u4c3_A_rng_s2b.
Print Assumptions planb4_u4c3_B_rng_s2b.
Print Assumptions planb4_u4c3_sym_rng_s2b.
