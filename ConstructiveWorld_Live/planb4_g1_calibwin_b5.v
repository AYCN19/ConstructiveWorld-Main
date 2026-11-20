(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 5 of 6: n = 31..36 (chain-tail supply form).    *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b5: anchor groups (b)/(c) point-wise, n = 31..36.

    Mission.  The planb4_g1_ab_def born-window anchors continued
      past n = 6, supplied from the small-step chain.  Group (b)
      the integrality round trip [Qeq_bool (inject_Z (Qnum q)) q =
      true]: each anchor rewrites the point's chain-tail equality
      certificate onto its integer literal, then one small bite.
      Group (c) the assembled [Qnum] values bite the frozen
      [planb3_g1_A]/[planb3_g1_B] table channels: each anchor is
      the matching host twin certificate, taken verbatim.

    Dependencies.  planb4_g1_ab_def; planb3_g1_calib;
      planb4_calib_chain_glue_qred (pb4cwin_zzId_eq);
      planb4_calib_chain_build_n31..n36 (eq-face certificates);
      planb4_calib_chain_host_n31..n36 (group-(c) twins);
      stdlib QArith, ZArith.

    References.  ZZ2020 Prop 1; planb3_g1_calib A/B channels
      n = 1..40; planb4_g1_calibwin_b1.v (segment 1, continued).

    Constructivity.  No non-constructive escapes; zero premise
      slot; every anchor carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <chain sandbox> ""
      -Q <tree ConstructiveWorld_Live> "" planb4_g1_calibwin_b5.v
      (Rocq 9.3.0; cpu_guard_v3 wrapped). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.
Require Import planb4_calib_chain_glue_qred.
Require Import planb4_calib_chain_build_n31.
Require Import planb4_calib_chain_build_n32.
Require Import planb4_calib_chain_build_n33.
Require Import planb4_calib_chain_build_n34.
Require Import planb4_calib_chain_build_n35.
Require Import planb4_calib_chain_build_n36.
Require Import planb4_calib_chain_host_n31.
Require Import planb4_calib_chain_host_n32.
Require Import planb4_calib_chain_host_n33.
Require Import planb4_calib_chain_host_n34.
Require Import planb4_calib_chain_host_n35.
Require Import planb4_calib_chain_host_n36.

(* ================================================================== *)
(* Group (b): both assembled channels are integer-valued rationals    *)
(* at every n of the segment (Q representation free: Qeq_bool through *)
(* the Qnum/inject_Z round trip; the ab_def statement shape, per n;   *)
(* each proof rewrites the build file's chain-tail equality           *)
(* certificate to the point's integer literal, then one small bite).  *)
(* ================================================================== *)

Example planb4_abqA_int_31 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 31))) (planb4_abqA 31) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n31).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_31 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 31))) (planb4_abqB 31) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n31).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_32 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 32))) (planb4_abqA 32) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n32).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_32 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 32))) (planb4_abqB 32) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n32).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_33 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 33))) (planb4_abqA 33) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n33).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_33 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 33))) (planb4_abqB 33) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n33).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_34 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 34))) (planb4_abqA 34) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n34).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_34 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 34))) (planb4_abqB 34) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n34).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_35 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 35))) (planb4_abqA 35) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n35).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_35 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 35))) (planb4_abqB 35) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n35).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_36 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 36))) (planb4_abqA 36) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n36).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_36 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 36))) (planb4_abqB 36) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n36).
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n; each proof term is *)
(* the host file's twin certificate verbatim, zero computation here). *)
(* ================================================================== *)

Example planb4_ab_Acal_31 :
  Z.eqb (Qnum (planb4_abqA 31)) (planb3_g1_A 31) = true :=
  pb4cwin_ab_Acal_n31.

Example planb4_ab_Bcal_31 :
  Z.eqb (Qnum (planb4_abqB 31)) (planb3_g1_B 31) = true :=
  pb4cwin_ab_Bcal_n31.

Example planb4_ab_Acal_32 :
  Z.eqb (Qnum (planb4_abqA 32)) (planb3_g1_A 32) = true :=
  pb4cwin_ab_Acal_n32.

Example planb4_ab_Bcal_32 :
  Z.eqb (Qnum (planb4_abqB 32)) (planb3_g1_B 32) = true :=
  pb4cwin_ab_Bcal_n32.

Example planb4_ab_Acal_33 :
  Z.eqb (Qnum (planb4_abqA 33)) (planb3_g1_A 33) = true :=
  pb4cwin_ab_Acal_n33.

Example planb4_ab_Bcal_33 :
  Z.eqb (Qnum (planb4_abqB 33)) (planb3_g1_B 33) = true :=
  pb4cwin_ab_Bcal_n33.

Example planb4_ab_Acal_34 :
  Z.eqb (Qnum (planb4_abqA 34)) (planb3_g1_A 34) = true :=
  pb4cwin_ab_Acal_n34.

Example planb4_ab_Bcal_34 :
  Z.eqb (Qnum (planb4_abqB 34)) (planb3_g1_B 34) = true :=
  pb4cwin_ab_Bcal_n34.

Example planb4_ab_Acal_35 :
  Z.eqb (Qnum (planb4_abqA 35)) (planb3_g1_A 35) = true :=
  pb4cwin_ab_Acal_n35.

Example planb4_ab_Bcal_35 :
  Z.eqb (Qnum (planb4_abqB 35)) (planb3_g1_B 35) = true :=
  pb4cwin_ab_Bcal_n35.

Example planb4_ab_Acal_36 :
  Z.eqb (Qnum (planb4_abqA 36)) (planb3_g1_A 36) = true :=
  pb4cwin_ab_Acal_n36.

Example planb4_ab_Bcal_36 :
  Z.eqb (Qnum (planb4_abqB 36)) (planb3_g1_B 36) = true :=
  pb4cwin_ab_Bcal_n36.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_31.
Print Assumptions planb4_abqB_int_31.
Print Assumptions planb4_abqA_int_32.
Print Assumptions planb4_abqB_int_32.
Print Assumptions planb4_abqA_int_33.
Print Assumptions planb4_abqB_int_33.
Print Assumptions planb4_abqA_int_34.
Print Assumptions planb4_abqB_int_34.
Print Assumptions planb4_abqA_int_35.
Print Assumptions planb4_abqB_int_35.
Print Assumptions planb4_abqA_int_36.
Print Assumptions planb4_abqB_int_36.
Print Assumptions planb4_ab_Acal_31.
Print Assumptions planb4_ab_Bcal_31.
Print Assumptions planb4_ab_Acal_32.
Print Assumptions planb4_ab_Bcal_32.
Print Assumptions planb4_ab_Acal_33.
Print Assumptions planb4_ab_Bcal_33.
Print Assumptions planb4_ab_Acal_34.
Print Assumptions planb4_ab_Bcal_34.
Print Assumptions planb4_ab_Acal_35.
Print Assumptions planb4_ab_Bcal_35.
Print Assumptions planb4_ab_Acal_36.
Print Assumptions planb4_ab_Bcal_36.
