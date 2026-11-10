(* ConstructiveWorld-Main - U4-C3 segment s5: pointwise frozen-window   *)
(* bites n = 33..40 (A/B table bites and Laurent pole symmetry).      *)

(** * planb4_u4c3_freezewin_s5: pointwise bites, n = 33..40.
    Mission.  The per-point machine bites feeding the k = 40 census
      assembly in planb4_u4c3_freezewin_40.v: per n of 33..40 the
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
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_s5.v
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

Example planb4_u4c3_A_pt_33 : Z.eqb (planb4_g1_A 33%nat) (planb3_g1_A 33%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_34 : Z.eqb (planb4_g1_A 34%nat) (planb3_g1_A 34%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_35 : Z.eqb (planb4_g1_A 35%nat) (planb3_g1_A 35%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_36 : Z.eqb (planb4_g1_A 36%nat) (planb3_g1_A 36%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_37 : Z.eqb (planb4_g1_A 37%nat) (planb3_g1_A 37%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_38 : Z.eqb (planb4_g1_A 38%nat) (planb3_g1_A 38%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_39 : Z.eqb (planb4_g1_A 39%nat) (planb3_g1_A 39%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_A_pt_40 : Z.eqb (planb4_g1_A 40%nat) (planb3_g1_A 40%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_33 : Z.eqb (planb4_g1_B 33%nat) (planb3_g1_B 33%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_34 : Z.eqb (planb4_g1_B 34%nat) (planb3_g1_B 34%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_35 : Z.eqb (planb4_g1_B 35%nat) (planb3_g1_B 35%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_36 : Z.eqb (planb4_g1_B 36%nat) (planb3_g1_B 36%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_37 : Z.eqb (planb4_g1_B 37%nat) (planb3_g1_B 37%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_38 : Z.eqb (planb4_g1_B 38%nat) (planb3_g1_B 38%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_39 : Z.eqb (planb4_g1_B 39%nat) (planb3_g1_B 39%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_40 : Z.eqb (planb4_g1_B 40%nat) (planb3_g1_B 40%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_33 : zz_lqeqb (planb4_g1_poleA 33%nat) (planb4_g1_poleB 33%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_34 : zz_lqeqb (planb4_g1_poleA 34%nat) (planb4_g1_poleB 34%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_35 : zz_lqeqb (planb4_g1_poleA 35%nat) (planb4_g1_poleB 35%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_36 : zz_lqeqb (planb4_g1_poleA 36%nat) (planb4_g1_poleB 36%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_37 : zz_lqeqb (planb4_g1_poleA 37%nat) (planb4_g1_poleB 37%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_38 : zz_lqeqb (planb4_g1_poleA 38%nat) (planb4_g1_poleB 38%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_39 : zz_lqeqb (planb4_g1_poleA 39%nat) (planb4_g1_poleB 39%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_40 : zz_lqeqb (planb4_g1_poleA 40%nat) (planb4_g1_poleB 40%nat) = true.
Proof. vm_compute. reflexivity. Qed.

(* Section 2. Range Lemmas: explicit enumeration, lia tail. *)

Lemma planb4_u4c3_A_rng_s5 : forall n : nat, (33 <= n <= 40)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 33%nat).
  { subst. apply planb4_u4c3_A_pt_33. }
  destruct (Nat.eq_dec n 34%nat).
  { subst. apply planb4_u4c3_A_pt_34. }
  destruct (Nat.eq_dec n 35%nat).
  { subst. apply planb4_u4c3_A_pt_35. }
  destruct (Nat.eq_dec n 36%nat).
  { subst. apply planb4_u4c3_A_pt_36. }
  destruct (Nat.eq_dec n 37%nat).
  { subst. apply planb4_u4c3_A_pt_37. }
  destruct (Nat.eq_dec n 38%nat).
  { subst. apply planb4_u4c3_A_pt_38. }
  destruct (Nat.eq_dec n 39%nat).
  { subst. apply planb4_u4c3_A_pt_39. }
  destruct (Nat.eq_dec n 40%nat).
  { subst. apply planb4_u4c3_A_pt_40. }
  lia.
Qed.

Lemma planb4_u4c3_B_rng_s5 : forall n : nat, (33 <= n <= 40)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 33%nat).
  { subst. apply planb4_u4c3_B_pt_33. }
  destruct (Nat.eq_dec n 34%nat).
  { subst. apply planb4_u4c3_B_pt_34. }
  destruct (Nat.eq_dec n 35%nat).
  { subst. apply planb4_u4c3_B_pt_35. }
  destruct (Nat.eq_dec n 36%nat).
  { subst. apply planb4_u4c3_B_pt_36. }
  destruct (Nat.eq_dec n 37%nat).
  { subst. apply planb4_u4c3_B_pt_37. }
  destruct (Nat.eq_dec n 38%nat).
  { subst. apply planb4_u4c3_B_pt_38. }
  destruct (Nat.eq_dec n 39%nat).
  { subst. apply planb4_u4c3_B_pt_39. }
  destruct (Nat.eq_dec n 40%nat).
  { subst. apply planb4_u4c3_B_pt_40. }
  lia.
Qed.

Lemma planb4_u4c3_sym_rng_s5 : forall n : nat, (33 <= n <= 40)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn.
  destruct (Nat.eq_dec n 33%nat).
  { subst. apply planb4_u4c3_sym_pt_33. }
  destruct (Nat.eq_dec n 34%nat).
  { subst. apply planb4_u4c3_sym_pt_34. }
  destruct (Nat.eq_dec n 35%nat).
  { subst. apply planb4_u4c3_sym_pt_35. }
  destruct (Nat.eq_dec n 36%nat).
  { subst. apply planb4_u4c3_sym_pt_36. }
  destruct (Nat.eq_dec n 37%nat).
  { subst. apply planb4_u4c3_sym_pt_37. }
  destruct (Nat.eq_dec n 38%nat).
  { subst. apply planb4_u4c3_sym_pt_38. }
  destruct (Nat.eq_dec n 39%nat).
  { subst. apply planb4_u4c3_sym_pt_39. }
  destruct (Nat.eq_dec n 40%nat).
  { subst. apply planb4_u4c3_sym_pt_40. }
  lia.
Qed.

(* Section 3. Assumption audit. *)

Print Assumptions planb4_u4c3_A_pt_33.
Print Assumptions planb4_u4c3_A_pt_34.
Print Assumptions planb4_u4c3_A_pt_35.
Print Assumptions planb4_u4c3_A_pt_36.
Print Assumptions planb4_u4c3_A_pt_37.
Print Assumptions planb4_u4c3_A_pt_38.
Print Assumptions planb4_u4c3_A_pt_39.
Print Assumptions planb4_u4c3_A_pt_40.
Print Assumptions planb4_u4c3_B_pt_33.
Print Assumptions planb4_u4c3_B_pt_34.
Print Assumptions planb4_u4c3_B_pt_35.
Print Assumptions planb4_u4c3_B_pt_36.
Print Assumptions planb4_u4c3_B_pt_37.
Print Assumptions planb4_u4c3_B_pt_38.
Print Assumptions planb4_u4c3_B_pt_39.
Print Assumptions planb4_u4c3_B_pt_40.
Print Assumptions planb4_u4c3_sym_pt_33.
Print Assumptions planb4_u4c3_sym_pt_34.
Print Assumptions planb4_u4c3_sym_pt_35.
Print Assumptions planb4_u4c3_sym_pt_36.
Print Assumptions planb4_u4c3_sym_pt_37.
Print Assumptions planb4_u4c3_sym_pt_38.
Print Assumptions planb4_u4c3_sym_pt_39.
Print Assumptions planb4_u4c3_sym_pt_40.
Print Assumptions planb4_u4c3_A_rng_s5.
Print Assumptions planb4_u4c3_B_rng_s5.
Print Assumptions planb4_u4c3_sym_rng_s5.
