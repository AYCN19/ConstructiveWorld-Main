(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 4 of 6: n = 25..30 (chain-tail supply form).    *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b4: anchor groups (b)/(c) point-wise, n = 25..30.

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
      planb4_calib_chain_build_n25..n30 (eq-face certificates);
      planb4_calib_chain_host_n25..n30 (group-(c) twins);
      stdlib QArith, ZArith.

    References.  ZZ2020 Prop 1; planb3_g1_calib A/B channels
      n = 1..40; planb4_g1_calibwin_b1.v (segment 1, continued).

    Constructivity.  No non-constructive escapes; zero premise
      slot; every anchor carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <chain sandbox> ""
      -Q <tree ConstructiveWorld_Live> "" planb4_g1_calibwin_b4.v
      (Rocq 9.3.0; cpu_guard_v3 wrapped). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.
Require Import planb4_calib_chain_glue_qred.
Require Import planb4_calib_chain_build_n25.
Require Import planb4_calib_chain_build_n26.
Require Import planb4_calib_chain_build_n27.
Require Import planb4_calib_chain_build_n28.
Require Import planb4_calib_chain_build_n29.
Require Import planb4_calib_chain_build_n30.
Require Import planb4_calib_chain_host_n25.
Require Import planb4_calib_chain_host_n26.
Require Import planb4_calib_chain_host_n27.
Require Import planb4_calib_chain_host_n28.
Require Import planb4_calib_chain_host_n29.
Require Import planb4_calib_chain_host_n30.

(* ================================================================== *)
(* Group (b): both assembled channels are integer-valued rationals    *)
(* at every n of the segment (Q representation free: Qeq_bool through *)
(* the Qnum/inject_Z round trip; the ab_def statement shape, per n;   *)
(* each proof rewrites the build file's chain-tail equality           *)
(* certificate to the point's integer literal, then one small bite).  *)
(* ================================================================== *)

Example planb4_abqA_int_25 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 25))) (planb4_abqA 25) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n25).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_25 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 25))) (planb4_abqB 25) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n25).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_26 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 26))) (planb4_abqA 26) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n26).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_26 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 26))) (planb4_abqB 26) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n26).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_27 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 27))) (planb4_abqA 27) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n27).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_27 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 27))) (planb4_abqB 27) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n27).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_28 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 28))) (planb4_abqA 28) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n28).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_28 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 28))) (planb4_abqB 28) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n28).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_29 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 29))) (planb4_abqA 29) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n29).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_29 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 29))) (planb4_abqB 29) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n29).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_30 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 30))) (planb4_abqA 30) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n30).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_30 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 30))) (planb4_abqB 30) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n30).
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n; each proof term is *)
(* the host file's twin certificate verbatim, zero computation here). *)
(* ================================================================== *)

Example planb4_ab_Acal_25 :
  Z.eqb (Qnum (planb4_abqA 25)) (planb3_g1_A 25) = true :=
  pb4cwin_ab_Acal_n25.

Example planb4_ab_Bcal_25 :
  Z.eqb (Qnum (planb4_abqB 25)) (planb3_g1_B 25) = true :=
  pb4cwin_ab_Bcal_n25.

Example planb4_ab_Acal_26 :
  Z.eqb (Qnum (planb4_abqA 26)) (planb3_g1_A 26) = true :=
  pb4cwin_ab_Acal_n26.

Example planb4_ab_Bcal_26 :
  Z.eqb (Qnum (planb4_abqB 26)) (planb3_g1_B 26) = true :=
  pb4cwin_ab_Bcal_n26.

Example planb4_ab_Acal_27 :
  Z.eqb (Qnum (planb4_abqA 27)) (planb3_g1_A 27) = true :=
  pb4cwin_ab_Acal_n27.

Example planb4_ab_Bcal_27 :
  Z.eqb (Qnum (planb4_abqB 27)) (planb3_g1_B 27) = true :=
  pb4cwin_ab_Bcal_n27.

Example planb4_ab_Acal_28 :
  Z.eqb (Qnum (planb4_abqA 28)) (planb3_g1_A 28) = true :=
  pb4cwin_ab_Acal_n28.

Example planb4_ab_Bcal_28 :
  Z.eqb (Qnum (planb4_abqB 28)) (planb3_g1_B 28) = true :=
  pb4cwin_ab_Bcal_n28.

Example planb4_ab_Acal_29 :
  Z.eqb (Qnum (planb4_abqA 29)) (planb3_g1_A 29) = true :=
  pb4cwin_ab_Acal_n29.

Example planb4_ab_Bcal_29 :
  Z.eqb (Qnum (planb4_abqB 29)) (planb3_g1_B 29) = true :=
  pb4cwin_ab_Bcal_n29.

Example planb4_ab_Acal_30 :
  Z.eqb (Qnum (planb4_abqA 30)) (planb3_g1_A 30) = true :=
  pb4cwin_ab_Acal_n30.

Example planb4_ab_Bcal_30 :
  Z.eqb (Qnum (planb4_abqB 30)) (planb3_g1_B 30) = true :=
  pb4cwin_ab_Bcal_n30.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_25.
Print Assumptions planb4_abqB_int_25.
Print Assumptions planb4_abqA_int_26.
Print Assumptions planb4_abqB_int_26.
Print Assumptions planb4_abqA_int_27.
Print Assumptions planb4_abqB_int_27.
Print Assumptions planb4_abqA_int_28.
Print Assumptions planb4_abqB_int_28.
Print Assumptions planb4_abqA_int_29.
Print Assumptions planb4_abqB_int_29.
Print Assumptions planb4_abqA_int_30.
Print Assumptions planb4_abqB_int_30.
Print Assumptions planb4_ab_Acal_25.
Print Assumptions planb4_ab_Bcal_25.
Print Assumptions planb4_ab_Acal_26.
Print Assumptions planb4_ab_Bcal_26.
Print Assumptions planb4_ab_Acal_27.
Print Assumptions planb4_ab_Bcal_27.
Print Assumptions planb4_ab_Acal_28.
Print Assumptions planb4_ab_Bcal_28.
Print Assumptions planb4_ab_Acal_29.
Print Assumptions planb4_ab_Bcal_29.
Print Assumptions planb4_ab_Acal_30.
Print Assumptions planb4_ab_Bcal_30.
