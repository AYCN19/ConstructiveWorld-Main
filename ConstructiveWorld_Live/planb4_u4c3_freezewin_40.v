(* ConstructiveWorld-Main - U4-C3 tie: the mandated k = 40 census        *)
(* anchors assembled from the s1..s5 pointwise bites.                    *)

(** * planb4_u4c3_freezewin_40: the k = 40 census anchors.
    Mission.  The mandated full-window faces: [planb4_g1_awin_40],
      [planb4_g1_bwin_40], [planb4_g1_symwin_40] (the census folds
      assembled from the s1..s5 pointwise bites through the intro
      Lemmas of the cert file) and [planb4_g1_allb_nz_40] (the
      nonzero census transferred from the table bite census and the
      frozen-table nonzero census via the mono Lemma - no
      recomputation of the B pipeline).
    Dependencies.  planb4_u4c3_freezewin_cert;
      planb4_u4c3_freezewin_s1..s5; planb3_g1_calib.
    References.  planb3_g1_calib_cert.v:36 (the frozen nonzero
      census face mirrored by the cert file's calib census Example).
    Constructivity.  Lemma application and pointwise dispatch only;
      admission-free and postulate-free throughout.
    Build.  coqc -native-compiler no -q -Q . "" planb4_u4c3_freezewin_40.v
      (Rocq 9.3.0, single lane under cpu_guard_v3). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Require Import planb3_g1_calib.
Require Import planb4_u4c3_freezewin_cert.
Require Import planb4_u4c3_freezewin_s1.
Require Import planb4_u4c3_freezewin_s2.
Require Import planb4_u4c3_freezewin_s3.
Require Import planb4_u4c3_freezewin_s4.
Require Import planb4_u4c3_freezewin_s5.

(* Section 1. The pointwise tables over the whole declared window. *)

Lemma planb4_u4c3_A_all_40 : forall n : nat, (1 <= n <= 40)%nat ->
  Z.eqb (planb4_g1_A n) (planb3_g1_A n) = true.
Proof. intros n Hn.
  destruct (Nat.leb n 8) eqn:E1.
  { apply planb4_u4c3_A_rng_s1. lia. }
  apply Nat.leb_gt in E1.
  destruct (Nat.leb n 16) eqn:E2.
  { apply planb4_u4c3_A_rng_s2. lia. }
  apply Nat.leb_gt in E2.
  destruct (Nat.leb n 24) eqn:E3.
  { apply planb4_u4c3_A_rng_s3. lia. }
  apply Nat.leb_gt in E3.
  destruct (Nat.leb n 32) eqn:E4.
  { apply planb4_u4c3_A_rng_s4. lia. }
  apply Nat.leb_gt in E4.
  apply planb4_u4c3_A_rng_s5. lia.
Qed.

Lemma planb4_u4c3_B_all_40 : forall n : nat, (1 <= n <= 40)%nat ->
  Z.eqb (planb4_g1_B n) (planb3_g1_B n) = true.
Proof. intros n Hn.
  destruct (Nat.leb n 8) eqn:E1.
  { apply planb4_u4c3_B_rng_s1. lia. }
  apply Nat.leb_gt in E1.
  destruct (Nat.leb n 16) eqn:E2.
  { apply planb4_u4c3_B_rng_s2. lia. }
  apply Nat.leb_gt in E2.
  destruct (Nat.leb n 24) eqn:E3.
  { apply planb4_u4c3_B_rng_s3. lia. }
  apply Nat.leb_gt in E3.
  destruct (Nat.leb n 32) eqn:E4.
  { apply planb4_u4c3_B_rng_s4. lia. }
  apply Nat.leb_gt in E4.
  apply planb4_u4c3_B_rng_s5. lia.
Qed.

Lemma planb4_u4c3_sym_all_40 : forall n : nat, (1 <= n <= 40)%nat ->
  zz_lqeqb (planb4_g1_poleA n) (planb4_g1_poleB n) = true.
Proof. intros n Hn.
  destruct (Nat.leb n 8) eqn:E1.
  { apply planb4_u4c3_sym_rng_s1. lia. }
  apply Nat.leb_gt in E1.
  destruct (Nat.leb n 16) eqn:E2.
  { apply planb4_u4c3_sym_rng_s2. lia. }
  apply Nat.leb_gt in E2.
  destruct (Nat.leb n 24) eqn:E3.
  { apply planb4_u4c3_sym_rng_s3. lia. }
  apply Nat.leb_gt in E3.
  destruct (Nat.leb n 32) eqn:E4.
  { apply planb4_u4c3_sym_rng_s4. lia. }
  apply Nat.leb_gt in E4.
  apply planb4_u4c3_sym_rng_s5. lia.
Qed.

(* Section 2. The mandated k = 40 census anchors. *)

Example planb4_g1_awin_40 : planb4_g1_awin 40%nat = true.
Proof. apply planb4_g1_awin_intro.
  intros n H1 H2. apply planb4_u4c3_A_all_40. lia.
Qed.

Example planb4_g1_bwin_40 : planb4_g1_bwin 40%nat = true.
Proof. apply planb4_g1_bwin_intro.
  intros n H1 H2. apply planb4_u4c3_B_all_40. lia.
Qed.

Example planb4_g1_symwin_40 : planb4_g1_symwin 40%nat = true.
Proof. apply planb4_g1_symwin_intro.
  intros n H1 H2. apply planb4_u4c3_sym_all_40. lia.
Qed.

Example planb4_g1_allb_nz_40 : planb4_g1_allb_nz 40%nat = true.
Proof. apply planb4_g1_allb_nz_mono.
  - exact planb4_g1_bwin_40.
  - exact planb4_u4c3_calib_allb_nz_40.
Qed.

(* Section 3. Assumption audit. *)

Print Assumptions planb4_u4c3_A_all_40.
Print Assumptions planb4_u4c3_B_all_40.
Print Assumptions planb4_u4c3_sym_all_40.
Print Assumptions planb4_g1_awin_40.
Print Assumptions planb4_g1_bwin_40.
Print Assumptions planb4_g1_symwin_40.
Print Assumptions planb4_g1_allb_nz_40.
