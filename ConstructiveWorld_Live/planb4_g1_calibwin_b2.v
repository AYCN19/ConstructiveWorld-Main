(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 2 of 6: n = 13..18 (chain-tail supply form).    *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b2: anchor groups (b)/(c) point-wise, n = 13..18.

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
      planb4_calib_chain_build_n13..n18 (eq-face certificates);
      planb4_calib_chain_host_n13..n18 (group-(c) twins);
      stdlib QArith, ZArith.

    References.  ZZ2020 Prop 1; planb3_g1_calib A/B channels
      n = 1..40; planb4_g1_calibwin_b1.v (segment 1, continued).

    Constructivity.  No non-constructive escapes; zero premise
      slot; every anchor carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <chain sandbox> ""
      -Q <tree ConstructiveWorld_Live> "" planb4_g1_calibwin_b2.v
      (Rocq 9.3.0; cpu_guard_v3 wrapped). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.
Require Import planb4_calib_chain_glue_qred.
Require Import planb4_calib_chain_build_n13.
Require Import planb4_calib_chain_build_n14.
Require Import planb4_calib_chain_build_n15.
Require Import planb4_calib_chain_build_n16.
Require Import planb4_calib_chain_build_n17.
Require Import planb4_calib_chain_build_n18.
Require Import planb4_calib_chain_host_n13.
Require Import planb4_calib_chain_host_n14.
Require Import planb4_calib_chain_host_n15.
Require Import planb4_calib_chain_host_n16.
Require Import planb4_calib_chain_host_n17.
Require Import planb4_calib_chain_host_n18.

(* ================================================================== *)
(* Group (b): both assembled channels are integer-valued rationals    *)
(* at every n of the segment (Q representation free: Qeq_bool through *)
(* the Qnum/inject_Z round trip; the ab_def statement shape, per n;   *)
(* each proof rewrites the build file's chain-tail equality           *)
(* certificate to the point's integer literal, then one small bite).  *)
(* ================================================================== *)

Example planb4_abqA_int_13 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 13))) (planb4_abqA 13) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n13).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_13 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 13))) (planb4_abqB 13) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n13).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_14 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 14))) (planb4_abqA 14) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n14).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_14 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 14))) (planb4_abqB 14) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n14).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_15 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 15))) (planb4_abqA 15) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n15).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_15 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 15))) (planb4_abqB 15) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n15).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_16 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 16))) (planb4_abqA 16) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n16).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_16 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 16))) (planb4_abqB 16) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n16).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_17 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 17))) (planb4_abqA 17) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n17).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_17 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 17))) (planb4_abqB 17) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n17).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_18 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 18))) (planb4_abqA 18) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n18).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_18 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 18))) (planb4_abqB 18) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n18).
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n; each proof term is *)
(* the host file's twin certificate verbatim, zero computation here). *)
(* ================================================================== *)

Example planb4_ab_Acal_13 :
  Z.eqb (Qnum (planb4_abqA 13)) (planb3_g1_A 13) = true :=
  pb4cwin_ab_Acal_n13.

Example planb4_ab_Bcal_13 :
  Z.eqb (Qnum (planb4_abqB 13)) (planb3_g1_B 13) = true :=
  pb4cwin_ab_Bcal_n13.

Example planb4_ab_Acal_14 :
  Z.eqb (Qnum (planb4_abqA 14)) (planb3_g1_A 14) = true :=
  pb4cwin_ab_Acal_n14.

Example planb4_ab_Bcal_14 :
  Z.eqb (Qnum (planb4_abqB 14)) (planb3_g1_B 14) = true :=
  pb4cwin_ab_Bcal_n14.

Example planb4_ab_Acal_15 :
  Z.eqb (Qnum (planb4_abqA 15)) (planb3_g1_A 15) = true :=
  pb4cwin_ab_Acal_n15.

Example planb4_ab_Bcal_15 :
  Z.eqb (Qnum (planb4_abqB 15)) (planb3_g1_B 15) = true :=
  pb4cwin_ab_Bcal_n15.

Example planb4_ab_Acal_16 :
  Z.eqb (Qnum (planb4_abqA 16)) (planb3_g1_A 16) = true :=
  pb4cwin_ab_Acal_n16.

Example planb4_ab_Bcal_16 :
  Z.eqb (Qnum (planb4_abqB 16)) (planb3_g1_B 16) = true :=
  pb4cwin_ab_Bcal_n16.

Example planb4_ab_Acal_17 :
  Z.eqb (Qnum (planb4_abqA 17)) (planb3_g1_A 17) = true :=
  pb4cwin_ab_Acal_n17.

Example planb4_ab_Bcal_17 :
  Z.eqb (Qnum (planb4_abqB 17)) (planb3_g1_B 17) = true :=
  pb4cwin_ab_Bcal_n17.

Example planb4_ab_Acal_18 :
  Z.eqb (Qnum (planb4_abqA 18)) (planb3_g1_A 18) = true :=
  pb4cwin_ab_Acal_n18.

Example planb4_ab_Bcal_18 :
  Z.eqb (Qnum (planb4_abqB 18)) (planb3_g1_B 18) = true :=
  pb4cwin_ab_Bcal_n18.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_13.
Print Assumptions planb4_abqB_int_13.
Print Assumptions planb4_ab_Acal_13.
Print Assumptions planb4_ab_Bcal_13.
Print Assumptions planb4_abqA_int_14.
Print Assumptions planb4_abqB_int_14.
Print Assumptions planb4_ab_Acal_14.
Print Assumptions planb4_ab_Bcal_14.
Print Assumptions planb4_abqA_int_15.
Print Assumptions planb4_abqB_int_15.
Print Assumptions planb4_ab_Acal_15.
Print Assumptions planb4_ab_Bcal_15.
Print Assumptions planb4_abqA_int_16.
Print Assumptions planb4_abqB_int_16.
Print Assumptions planb4_ab_Acal_16.
Print Assumptions planb4_ab_Bcal_16.
Print Assumptions planb4_abqA_int_17.
Print Assumptions planb4_abqB_int_17.
Print Assumptions planb4_ab_Acal_17.
Print Assumptions planb4_ab_Bcal_17.
Print Assumptions planb4_abqA_int_18.
Print Assumptions planb4_abqB_int_18.
Print Assumptions planb4_ab_Acal_18.
Print Assumptions planb4_ab_Bcal_18.
