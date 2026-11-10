(* ConstructiveWorld-Main - U4-C3 micro-segment s2n12: the three        *)
(* channel bites at the single point n = 12.                             *)

(** * planb4_u4c3_freezewin_s2n12: pointwise bites at n = 12.
    Mission.  The per-point machine bites feeding the k = 40 census
      assembly in planb4_u4c3_freezewin_40.v: the assembled
      [planb4_g1_A]/[planb4_g1_B] bite the frozen table arms and the
      antipodal Laurent readouts agree via [zz_lqeqb] at n = 12,
      each an independent vm_compute bite (fail-loud: a failing bite
      names its n); the singleton range Lemmas feed the tie dispatch.
    Dependencies.  planb4_u4c3_freezewin_cert (the census carriers);
      planb4_g1_rs_assembly; planb3_g1_calib; planb4_g1_laur_extract;
      zzm1b_linform_bridge (zz_lqeqb).
    References.  ZZ2020 Prop 1; planb3_g1_calib A/B tables
      n = 1..40; the pointwise discipline of rs_assembly.v:226-236.
    Constructivity.  One vm_compute step per bite; admission-free
      and postulate-free throughout.
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_s2n12.v
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

Example planb4_u4c3_A_pt_12 : Z.eqb (planb4_g1_A 12%nat) (planb3_g1_A 12%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_B_pt_12 : Z.eqb (planb4_g1_B 12%nat) (planb3_g1_B 12%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Example planb4_u4c3_sym_pt_12 : zz_lqeqb (planb4_g1_poleA 12%nat) (planb4_g1_poleB 12%nat) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb4_u4c3_A_rng_s2n12 : forall n : nat, (12 <= n <= 12)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn. destruct (Nat.eq_dec n 12%nat).
  { subst. apply planb4_u4c3_A_pt_12. }
  lia.
Qed.

Lemma planb4_u4c3_B_rng_s2n12 : forall n : nat, (12 <= n <= 12)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn. destruct (Nat.eq_dec n 12%nat).
  { subst. apply planb4_u4c3_B_pt_12. }
  lia.
Qed.

Lemma planb4_u4c3_sym_rng_s2n12 : forall n : nat, (12 <= n <= 12)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn. destruct (Nat.eq_dec n 12%nat).
  { subst. apply planb4_u4c3_sym_pt_12. }
  lia.
Qed.

Print Assumptions planb4_u4c3_A_pt_12.
Print Assumptions planb4_u4c3_B_pt_12.
Print Assumptions planb4_u4c3_sym_pt_12.
Print Assumptions planb4_u4c3_A_rng_s2n12.
Print Assumptions planb4_u4c3_B_rng_s2n12.
Print Assumptions planb4_u4c3_sym_rng_s2n12.
