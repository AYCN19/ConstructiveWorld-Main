(* ConstructiveWorld-Main - U4-C3 segment s4: pointwise frozen-window   *)
(* bites n = 25..32 (A/B table bites and Laurent pole symmetry).      *)

(** * planb4_u4c3_freezewin_s4: pointwise bites, n = 25..32.
    Mission.  The per-point machine bites feeding the k = 40 census
      assembly in planb4_u4c3_freezewin_40.v: per n of 25..32 the
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
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_s4.v
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

Example planb4_u4c3_A_pt_25 : Z.eqb (planb4_g1_A 25%nat) (planb3_g1_A 25%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_26 : Z.eqb (planb4_g1_A 26%nat) (planb3_g1_A 26%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_27 : Z.eqb (planb4_g1_A 27%nat) (planb3_g1_A 27%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_28 : Z.eqb (planb4_g1_A 28%nat) (planb3_g1_A 28%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_29 : Z.eqb (planb4_g1_A 29%nat) (planb3_g1_A 29%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_30 : Z.eqb (planb4_g1_A 30%nat) (planb3_g1_A 30%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_31 : Z.eqb (planb4_g1_A 31%nat) (planb3_g1_A 31%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_32 : Z.eqb (planb4_g1_A 32%nat) (planb3_g1_A 32%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_25 : Z.eqb (planb4_g1_B 25%nat) (planb3_g1_B 25%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_26 : Z.eqb (planb4_g1_B 26%nat) (planb3_g1_B 26%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_27 : Z.eqb (planb4_g1_B 27%nat) (planb3_g1_B 27%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_28 : Z.eqb (planb4_g1_B 28%nat) (planb3_g1_B 28%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_29 : Z.eqb (planb4_g1_B 29%nat) (planb3_g1_B 29%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_30 : Z.eqb (planb4_g1_B 30%nat) (planb3_g1_B 30%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_31 : Z.eqb (planb4_g1_B 31%nat) (planb3_g1_B 31%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_32 : Z.eqb (planb4_g1_B 32%nat) (planb3_g1_B 32%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_25 : zz_lqeqb (planb4_g1_poleA 25%nat) (planb4_g1_poleB 25%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_26 : zz_lqeqb (planb4_g1_poleA 26%nat) (planb4_g1_poleB 26%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_27 : zz_lqeqb (planb4_g1_poleA 27%nat) (planb4_g1_poleB 27%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_28 : zz_lqeqb (planb4_g1_poleA 28%nat) (planb4_g1_poleB 28%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_29 : zz_lqeqb (planb4_g1_poleA 29%nat) (planb4_g1_poleB 29%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_30 : zz_lqeqb (planb4_g1_poleA 30%nat) (planb4_g1_poleB 30%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_31 : zz_lqeqb (planb4_g1_poleA 31%nat) (planb4_g1_poleB 31%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_32 : zz_lqeqb (planb4_g1_poleA 32%nat) (planb4_g1_poleB 32%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* Section 2. Range Lemmas: explicit enumeration, lia tail. *)

Lemma planb4_u4c3_A_rng_s4 : forall n : nat, (25 <= n <= 32)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 25%nat).
  { subst. apply planb4_u4c3_A_pt_25. }
  destruct (Nat.eq_dec n 26%nat).
  { subst. apply planb4_u4c3_A_pt_26. }
  destruct (Nat.eq_dec n 27%nat).
  { subst. apply planb4_u4c3_A_pt_27. }
  destruct (Nat.eq_dec n 28%nat).
  { subst. apply planb4_u4c3_A_pt_28. }
  destruct (Nat.eq_dec n 29%nat).
  { subst. apply planb4_u4c3_A_pt_29. }
  destruct (Nat.eq_dec n 30%nat).
  { subst. apply planb4_u4c3_A_pt_30. }
  destruct (Nat.eq_dec n 31%nat).
  { subst. apply planb4_u4c3_A_pt_31. }
  destruct (Nat.eq_dec n 32%nat).
  { subst. apply planb4_u4c3_A_pt_32. }
  lia.
Qed.

Lemma planb4_u4c3_B_rng_s4 : forall n : nat, (25 <= n <= 32)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 25%nat).
  { subst. apply planb4_u4c3_B_pt_25. }
  destruct (Nat.eq_dec n 26%nat).
  { subst. apply planb4_u4c3_B_pt_26. }
  destruct (Nat.eq_dec n 27%nat).
  { subst. apply planb4_u4c3_B_pt_27. }
  destruct (Nat.eq_dec n 28%nat).
  { subst. apply planb4_u4c3_B_pt_28. }
  destruct (Nat.eq_dec n 29%nat).
  { subst. apply planb4_u4c3_B_pt_29. }
  destruct (Nat.eq_dec n 30%nat).
  { subst. apply planb4_u4c3_B_pt_30. }
  destruct (Nat.eq_dec n 31%nat).
  { subst. apply planb4_u4c3_B_pt_31. }
  destruct (Nat.eq_dec n 32%nat).
  { subst. apply planb4_u4c3_B_pt_32. }
  lia.
Qed.

Lemma planb4_u4c3_sym_rng_s4 : forall n : nat, (25 <= n <= 32)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 25%nat).
  { subst. apply planb4_u4c3_sym_pt_25. }
  destruct (Nat.eq_dec n 26%nat).
  { subst. apply planb4_u4c3_sym_pt_26. }
  destruct (Nat.eq_dec n 27%nat).
  { subst. apply planb4_u4c3_sym_pt_27. }
  destruct (Nat.eq_dec n 28%nat).
  { subst. apply planb4_u4c3_sym_pt_28. }
  destruct (Nat.eq_dec n 29%nat).
  { subst. apply planb4_u4c3_sym_pt_29. }
  destruct (Nat.eq_dec n 30%nat).
  { subst. apply planb4_u4c3_sym_pt_30. }
  destruct (Nat.eq_dec n 31%nat).
  { subst. apply planb4_u4c3_sym_pt_31. }
  destruct (Nat.eq_dec n 32%nat).
  { subst. apply planb4_u4c3_sym_pt_32. }
  lia.
Qed.

(* Section 3. Assumption audit. *)

Print Assumptions planb4_u4c3_A_pt_25.
Print Assumptions planb4_u4c3_A_pt_26.
Print Assumptions planb4_u4c3_A_pt_27.
Print Assumptions planb4_u4c3_A_pt_28.
Print Assumptions planb4_u4c3_A_pt_29.
Print Assumptions planb4_u4c3_A_pt_30.
Print Assumptions planb4_u4c3_A_pt_31.
Print Assumptions planb4_u4c3_A_pt_32.
Print Assumptions planb4_u4c3_B_pt_25.
Print Assumptions planb4_u4c3_B_pt_26.
Print Assumptions planb4_u4c3_B_pt_27.
Print Assumptions planb4_u4c3_B_pt_28.
Print Assumptions planb4_u4c3_B_pt_29.
Print Assumptions planb4_u4c3_B_pt_30.
Print Assumptions planb4_u4c3_B_pt_31.
Print Assumptions planb4_u4c3_B_pt_32.
Print Assumptions planb4_u4c3_sym_pt_25.
Print Assumptions planb4_u4c3_sym_pt_26.
Print Assumptions planb4_u4c3_sym_pt_27.
Print Assumptions planb4_u4c3_sym_pt_28.
Print Assumptions planb4_u4c3_sym_pt_29.
Print Assumptions planb4_u4c3_sym_pt_30.
Print Assumptions planb4_u4c3_sym_pt_31.
Print Assumptions planb4_u4c3_sym_pt_32.
Print Assumptions planb4_u4c3_A_rng_s4.
Print Assumptions planb4_u4c3_B_rng_s4.
Print Assumptions planb4_u4c3_sym_rng_s4.
