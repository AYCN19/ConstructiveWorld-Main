(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: the calibration-window      *)
(* anchor sweep, segment 6 of 6: n = 37..40 (chain-tail supply form).    *)
(* ===================================================================== *)

(** * planb4_g1_calibwin_b6: anchor groups (b)/(c) point-wise, n = 37..40.

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
      planb4_calib_chain_build_n37..n40 (eq-face certificates);
      planb4_calib_chain_host_n37..n40 (group-(c) twins);
      stdlib QArith, ZArith.

    References.  ZZ2020 Prop 1; planb3_g1_calib A/B channels
      n = 1..40; planb4_g1_calibwin_b1.v (segment 1, continued).

    Constructivity.  No non-constructive escapes; zero premise
      slot; every anchor carries Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <chain sandbox> ""
      -Q <tree ConstructiveWorld_Live> "" planb4_g1_calibwin_b6.v
      (Rocq 9.3.0; cpu_guard_v3 wrapped). *)

From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.
Require Import planb4_calib_chain_glue_qred.
Require Import planb4_calib_chain_build_n37.
Require Import planb4_calib_chain_build_n38.
Require Import planb4_calib_chain_build_n39.
Require Import planb4_calib_chain_build_n40.
Require Import planb4_calib_chain_host_n37.
Require Import planb4_calib_chain_host_n38.
Require Import planb4_calib_chain_host_n39.
Require Import planb4_calib_chain_host_n40.

(* ================================================================== *)
(* Group (b): both assembled channels are integer-valued rationals    *)
(* at every n of the segment (Q representation free: Qeq_bool through *)
(* the Qnum/inject_Z round trip; the ab_def statement shape, per n;   *)
(* each proof rewrites the build file's chain-tail equality           *)
(* certificate to the point's integer literal, then one small bite).  *)
(* ================================================================== *)

Example planb4_abqA_int_37 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 37))) (planb4_abqA 37) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n37).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_37 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 37))) (planb4_abqB 37) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n37).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_38 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 38))) (planb4_abqA 38) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n38).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_38 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 38))) (planb4_abqB 38) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n38).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_39 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 39))) (planb4_abqA 39) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n39).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_39 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 39))) (planb4_abqB 39) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n39).
  vm_compute. reflexivity.
Qed.

Example planb4_abqA_int_40 :
  Qeq_bool (inject_Z (Qnum (planb4_abqA 40))) (planb4_abqA 40) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n40).
  vm_compute. reflexivity.
Qed.

Example planb4_abqB_int_40 :
  Qeq_bool (inject_Z (Qnum (planb4_abqB 40))) (planb4_abqB 40) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n40).
  vm_compute. reflexivity.
Qed.

(* ================================================================== *)
(* Group (c): the assembled Qnum values bite the frozen calibration   *)
(* tables (the exact machine verification of the assembly formula on  *)
(* the segment; the ab_def statement shape, per n; each proof term is *)
(* the host file's twin certificate verbatim, zero computation here). *)
(* ================================================================== *)

Example planb4_ab_Acal_37 :
  Z.eqb (Qnum (planb4_abqA 37)) (planb3_g1_A 37) = true :=
  pb4cwin_ab_Acal_n37.

Example planb4_ab_Bcal_37 :
  Z.eqb (Qnum (planb4_abqB 37)) (planb3_g1_B 37) = true :=
  pb4cwin_ab_Bcal_n37.

Example planb4_ab_Acal_38 :
  Z.eqb (Qnum (planb4_abqA 38)) (planb3_g1_A 38) = true :=
  pb4cwin_ab_Acal_n38.

Example planb4_ab_Bcal_38 :
  Z.eqb (Qnum (planb4_abqB 38)) (planb3_g1_B 38) = true :=
  pb4cwin_ab_Bcal_n38.

Example planb4_ab_Acal_39 :
  Z.eqb (Qnum (planb4_abqA 39)) (planb3_g1_A 39) = true :=
  pb4cwin_ab_Acal_n39.

Example planb4_ab_Bcal_39 :
  Z.eqb (Qnum (planb4_abqB 39)) (planb3_g1_B 39) = true :=
  pb4cwin_ab_Bcal_n39.

Example planb4_ab_Acal_40 :
  Z.eqb (Qnum (planb4_abqA 40)) (planb3_g1_A 40) = true :=
  pb4cwin_ab_Acal_n40.

Example planb4_ab_Bcal_40 :
  Z.eqb (Qnum (planb4_abqB 40)) (planb3_g1_B 40) = true :=
  pb4cwin_ab_Bcal_n40.

(* ================================================================== *)
(* Assumption audit over the segment anchors.                         *)
(* ================================================================== *)

Print Assumptions planb4_abqA_int_37.
Print Assumptions planb4_abqB_int_37.
Print Assumptions planb4_abqA_int_38.
Print Assumptions planb4_abqB_int_38.
Print Assumptions planb4_abqA_int_39.
Print Assumptions planb4_abqB_int_39.
Print Assumptions planb4_abqA_int_40.
Print Assumptions planb4_abqB_int_40.
Print Assumptions planb4_ab_Acal_37.
Print Assumptions planb4_ab_Bcal_37.
Print Assumptions planb4_ab_Acal_38.
Print Assumptions planb4_ab_Bcal_38.
Print Assumptions planb4_ab_Acal_39.
Print Assumptions planb4_ab_Bcal_39.
Print Assumptions planb4_ab_Acal_40.
Print Assumptions planb4_ab_Bcal_40.
