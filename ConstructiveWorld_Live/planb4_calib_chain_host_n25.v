(* ===================================================================== *)
(* ConstructiveWorld-Main - calibwin small-step chain: host anchors at the window point n = 25 *)
(** * planb4_calib_chain_host_n25: statement twins of the landed calibwin group-(c) anchors at 25, closed from the chain tail instead of a full-chain bite: each anchor is the exact landed statement face Z.eqb (Qnum (planb4_abqX 25)) (planb3_g1_X 25) = true; the proof rewrites with the chain-tail literal certificate pb4cwin_abqXeq_n25 imported from the build file and closes with one small integer comparison, so no anchor here re-triggers the Laurent chain or the fold.

    Mission.  statement twins of the landed calibwin group-(c) anchors at 25, closed from the chain tail instead of a full-chain bite: each anchor is the exact landed statement face Z.eqb (Qnum (planb4_abqX 25)) (planb3_g1_X 25) = true; the proof rewrites with the chain-tail literal certificate pb4cwin_abqXeq_n25 imported from the build file and closes with one small integer comparison, so no anchor here re-triggers the Laurent chain or the fold.

    Dependencies.  planb4_g1_ab_def (planb4_abqA, planb4_abqB); planb3_g1_calib (frozen tables); planb4_calib_chain_build_n25 (pb4cwin_abqAeq_n25, pb4cwin_abqBeq_n25); planb4_calib_chain_glue_qred (pb4cwin_zzId_eq); stdlib ZArith.

    References.  planb4_g1_calibwin_b1.v / planb4_g1_calibwin_b2.v (the landed anchor face this file twins); planb4_g1_ab_def.v:157-181 (the group-(c) anchor block).

    Constructivity.  Each proof is one rewrite from an imported certificate plus one small bite; no axioms, no admits; both anchors carry Print Assumptions.

    Build.  coqc -native-compiler no -time -q -Q <this sandbox> "" -Q <tree ConstructiveWorld_Live> "" planb4_calib_chain_host_n25.v (Rocq 9.3.0; cpu_guard_v3 wrapped; products stay in this sandbox, the module tree is read-only). *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
Require Import zzm1_gauss.
Require Import planb4_g1_ab_def.
Require Import planb3_g1_calib.
Require Import planb4_calib_chain_glue_qred.
Require Import planb4_calib_chain_build_n25.

(* A-channel anchor: the assembled value lands on the frozen table row. *)
Example pb4cwin_ab_Acal_n25 :
  Z.eqb (Qnum (planb4_abqA 25)) (planb3_g1_A 25) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqAeq_n25).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_ab_Acal_n25.

(* B-channel anchor: the s-channel twin. *)
Example pb4cwin_ab_Bcal_n25 :
  Z.eqb (Qnum (planb4_abqB 25)) (planb3_g1_B 25) = true.
Proof.
  rewrite (pb4cwin_zzId_eq pb4cwin_abqBeq_n25).
  vm_compute. reflexivity.
Qed.
Print Assumptions pb4cwin_ab_Bcal_n25.
