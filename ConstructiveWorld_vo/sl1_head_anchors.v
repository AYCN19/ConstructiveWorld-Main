(* sl1_head_anchors.v - the machine anchors of the SL1 head range.
   Ticket: SL12 ticket SL1 (psi band + Phi window construction seat).
   Mission: pin the head-range machine evidence: the lcm band at the
   integer instance B = 65 over n = 0..40 (zero violations; the
   ground-truth table confirms zero through n = 600), the L_n band at
   the tight instance b = 48 over n = 0..14 (below the pinned offset
   sl1_N0 = 15), the Phi-window band at c = 34/25 over n = 15..40,
   the offset tightness certificate (violated at n = 14: Phi 14 = 23),
   and the pairing numerics 65 / (34/25) = 1625/34 <= 48 and > 0.
   Inventory: 7 anchor Examples (vm_compute + reflexivity, Qed kept
   per the upstream anchor registration).
   Dependencies: S02_CauchyComplete; planb4_g1_witness;
   sl1_phase_faces (head-check faces, sl1_N0); stdlib QArith, ZArith,
   Qpower, List, Lia.
   References: slot statement draft SL12 sections 1.1-1.3 (instance
   pairing table); survey volume section 5 (shared decay account);
   ground-truth table tools/sl1_ground_truth.py.
   NOT claimed: the forall-n band supplies remain open debts; these
   anchors cover the head ranges the kernel evaluates directly.
   Constructivity: conversion checks over transparent informative
   definitions; zero global assumptions.
   Build: coqc -native-compiler no -q -Q world "" -Q out_sl1 ""
   sl1_head_anchors.v (E952 script form; after sl1_phase_faces). *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower List.
Require Import S02_CauchyComplete.
Require Import planb4_g1_witness.
Require Import sl1_phase_faces.

(* ==== Section 1: the integer instance pairing anchors ==== *)

(* The assembly base after the integer round-up of the psi band:
   65 / (34/25) = 1625/34, which sits strictly below the tight
   integer instance 48 and strictly above 0. *)
Example sl1_anchor_base_le48 :
  S02_CauchyComplete.QleT' ((65 # 1)%Q / (34 # 25)%Q) ((48 # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

Example sl1_anchor_base_pos :
  S02_CauchyComplete.QltT 0 ((65 # 1)%Q / (34 # 25)%Q).
Proof. vm_compute. reflexivity. Qed.

Example sl1_anchor_48_pos :
  S02_CauchyComplete.QltT 0 ((48 # 1)%Q).
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 2: the head-range anchors ==== *)

(* lcm band at B = 65 over n = 0..40 (seq 0 41): zero violations. *)
Example sl1_lcm65_head_anchor :
  sl1_lcm_head_ok ((65 # 1)%Q) 41 = true.
Proof. vm_compute. reflexivity. Qed.

(* L_n band at b = 48 over n = 0..14 (seq 0 sl1_N0): zero violations;
   together with the conditional chain theorem this covers the head
   range of the tight instance. *)
Example sl1_lzn48_head_anchor :
  sl1_lzn_head_ok ((48 # 1)%Q) sl1_N0 = true.
Proof. vm_compute. reflexivity. Qed.

(* Phi-window band at c = 34/25 over n = 15..40 (seq sl1_N0 26): the
   machine window of the offset band face. *)
Example sl1_phi_band_head_anchor :
  sl1_phi_band_head_ok ((34 # 25)%Q) sl1_N0 26 = true.
Proof. vm_compute. reflexivity. Qed.

(* ==== Section 3: the offset tightness certificate ==== *)

(* The Phi-window band at c = 34/25 is violated at n = 14 (the last
   violation index of the ground-truth table): Phi 14 = 23 and
   (34/25)^14 exceeds it. The pinned offset sl1_N0 = 15 is therefore
   tight. *)
Example sl1_phi_N0_tight :
  S02_CauchyComplete.QltT (inject_Z (planb4_Phi 14))
    (Qpower ((34 # 25)%Q) 14).
Proof. vm_compute. reflexivity. Qed.

Print Assumptions sl1_anchor_base_le48.
Print Assumptions sl1_anchor_base_pos.
Print Assumptions sl1_anchor_48_pos.
Print Assumptions sl1_lcm65_head_anchor.
Print Assumptions sl1_lzn48_head_anchor.
Print Assumptions sl1_phi_band_head_anchor.
Print Assumptions sl1_phi_N0_tight.
