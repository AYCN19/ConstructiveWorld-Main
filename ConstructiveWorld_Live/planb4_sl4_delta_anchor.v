(* ========================================================================= *)
(* ConstructiveWorld-Main - unif L4 piece: the SL4 delta table-domain        *)
(* anchors (survey volume, slice S-1; dispatch row D-SL4-1).                 *)
(* Mission      : Name the dodge determinant on the ab_def total carrier     *)
(*                (planb4_sl4_delta) and land its table-domain nonzero       *)
(*                anchors for n = 1..39.  Each anchor is discharged by       *)
(*                bite transfer: the in-tree bite examples (planb4_ab_Acal   *)
(*                /Bcal_n n = 1..12, planb4_abqA/B_int_n n = 7..40) rewrite  *)
(*                the Qnum projections to the frozen calibration channels,   *)
(*                then vm_compute closes on plain Z arithmetic - the ab_def  *)
(*                Qred chains are never evaluated, bypassing the direct      *)
(*                large-rational timeout at n >= 39 (300 s, skeleton seat).  *)
(*                Window-slot twins (frozen / ab_def) and the nlo domain-    *)
(*                exit lemma land alongside (slice S-2); the frozen-carrier  *)
(*                vacuity face at q >= 2^79 is born, honestly unproven -     *)
(*                NOT claimed.  The forall-n nonzero body stays open (SL4    *)
(*                breakthrough debt; survey sec 5).                          *)
(* Dependencies : planb3_g1_calib; planb4_g1_ab_def (n = 1..12 bites);       *)
(*                planb4_g1_calibwin_b1..b6 (bites n = 4,7..40);             *)
(*                planb1_hcage_zerotouch_prescription (planb_b_nlo).         *)
(* References   : survey volume sec 6/9 (D-SL4-1/D-SL4-2);                   *)
(*                planb4_l4_fourslots.v:101-109 (SL4 slot);                  *)
(*                planb5_hesc18_assembly.v:1587-1643 (consumers);            *)
(*                planb3_g1_calib.v:79/:261 (out-of-domain fallback).        *)
(* Constructivity: Z-carried statements (Z.eqb_eq rewrites, vm_compute,     *)
(*                lia); postulate-free; no Parameter, no Conjecture,         *)
(*                no Abort.                                                  *)
(* Build        : coqc -q -native-compiler no -Q <Live> ""                   *)
(*                planb4_sl4_delta_anchor.v (Rocq 9.3.0, E952 script form).  *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.
Require Import planb4_g1_calibwin_b1.
Require Import planb4_g1_calibwin_b2.
Require Import planb4_g1_calibwin_b3.
Require Import planb4_g1_calibwin_b4.
Require Import planb4_g1_calibwin_b5.
Require Import planb4_g1_calibwin_b6.
Require Import planb1_hcage_zerotouch_prescription.

(* ================================================================== *)
(* Section 1. The dodge determinant on the total carrier (named       *)
(*            definition; survey slice S-1).                          *)
(* ================================================================== *)

Definition planb4_sl4_delta (n : nat) : Z :=
  (planb4_g1_A n * planb4_g1_B (S n)
   - planb4_g1_A (S n) * planb4_g1_B n)%Z.

(* ================================================================== *)
(* Section 2. Table-domain nonzero anchors, n = 1..39 (bite           *)
(*            transfer; the frozen channels are machine values, the   *)
(*            ab_def Qred chains are never evaluated).                *)
(* ================================================================== *)

Example planb4_sl4_delta_nz_1 : planb4_sl4_delta 1 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_1).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_2).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_2).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_1).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_2 : planb4_sl4_delta 2 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_2).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_3).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_3).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_2).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_3 : planb4_sl4_delta 3 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_3).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_4).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_4).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_3).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_4 : planb4_sl4_delta 4 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_4).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_5).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_5).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_4).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_5 : planb4_sl4_delta 5 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_5).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_6).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_6).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_5).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_6 : planb4_sl4_delta 6 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_6).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_7).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_7).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_6).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_7 : planb4_sl4_delta 7 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_7).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_8).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_8).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_7).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_8 : planb4_sl4_delta 8 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_8).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_9).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_9).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_8).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_9 : planb4_sl4_delta 9 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_9).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_10).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_10).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_9).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_10 : planb4_sl4_delta 10 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_10).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_11).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_11).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_10).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_11 : planb4_sl4_delta 11 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_11).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_12).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_12).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_11).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_12 : planb4_sl4_delta 12 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Acal_12).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_13).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_13).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_ab_Bcal_12).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_13 : planb4_sl4_delta 13 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_13).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_14).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_14).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_13).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_14 : planb4_sl4_delta 14 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_14).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_15).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_15).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_14).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_15 : planb4_sl4_delta 15 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_15).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_16).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_16).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_15).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_16 : planb4_sl4_delta 16 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_16).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_17).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_17).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_16).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_17 : planb4_sl4_delta 17 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_17).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_18).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_18).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_17).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_18 : planb4_sl4_delta 18 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_18).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_19).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_19).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_18).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_19 : planb4_sl4_delta 19 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_19).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_20).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_20).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_19).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_20 : planb4_sl4_delta 20 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_20).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_21).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_21).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_20).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_21 : planb4_sl4_delta 21 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_21).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_22).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_22).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_21).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_22 : planb4_sl4_delta 22 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_22).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_23).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_23).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_22).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_23 : planb4_sl4_delta 23 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_23).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_24).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_24).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_23).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_24 : planb4_sl4_delta 24 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_24).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_25).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_25).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_24).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_25 : planb4_sl4_delta 25 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_25).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_26).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_26).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_25).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_26 : planb4_sl4_delta 26 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_26).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_27).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_27).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_26).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_27 : planb4_sl4_delta 27 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_27).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_28).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_28).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_27).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_28 : planb4_sl4_delta 28 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_28).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_29).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_29).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_28).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_29 : planb4_sl4_delta 29 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_29).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_30).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_30).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_29).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_30 : planb4_sl4_delta 30 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_30).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_31).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_31).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_30).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_31 : planb4_sl4_delta 31 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_31).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_32).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_32).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_31).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_32 : planb4_sl4_delta 32 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_32).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_33).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_33).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_32).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_33 : planb4_sl4_delta 33 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_33).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_34).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_34).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_33).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_34 : planb4_sl4_delta 34 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_34).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_35).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_35).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_34).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_35 : planb4_sl4_delta 35 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_35).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_36).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_36).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_35).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_36 : planb4_sl4_delta 36 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_36).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_37).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_37).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_36).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_37 : planb4_sl4_delta 37 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_37).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_38).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_38).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_37).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_38 : planb4_sl4_delta 38 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_38).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_39).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_39).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_38).
  vm_compute. lia.
Qed.

Example planb4_sl4_delta_nz_39 : planb4_sl4_delta 39 <> 0%Z.
Proof.
  unfold planb4_sl4_delta, planb4_g1_A, planb4_g1_B.
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_39).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_40).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqA_int_40).
  rewrite (proj2 (Z.eqb_eq _ _) planb4_abqB_int_39).
  vm_compute. lia.
Qed.

(* ================================================================== *)
(* Section 3. The window-slot twins (survey slice S-2 material; the   *)
(*            frozen twin is the consumption shape at                 *)
(*            planb5_hesc18_assembly.v:1587-1643, the ab_def twin is  *)
(*            the swap target with the total carrier).                *)
(* ================================================================== *)

Definition planb4_sl4_window_slot_frozen (nlo : nat -> nat) : Prop :=
  forall q : nat, (1 <= q)%nat ->
    (planb3_g1_A (nlo q) * planb3_g1_B (S (nlo q))
     - planb3_g1_A (S (nlo q)) * planb3_g1_B (nlo q) <> 0)%Z.

Definition planb4_sl4_window_slot_abdef (nlo : nat -> nat) : Prop :=
  forall q : nat, (1 <= q)%nat -> planb4_sl4_delta (nlo q) <> 0%Z.

(* The domain-exit bound: at q >= 2^79 the window index reaches the    *)
(* table edge (planb_b_nlo = div2(log2 q + 2) stepped, so 2^79 <= q    *)
(* forces log2 q >= 79 and div2(79 + 2) = 40).                         *)
Lemma planb4_sl4_nlo_ge_40 : forall q : nat, (2 ^ 79 <= q)%nat ->
  (40 <= planb_b_nlo q)%nat.
Proof.
  intros q Hq.
  assert (Hl : (79 <= Nat.log2 q)%nat).
  { destruct (Nat.le_gt_cases 79 (Nat.log2 q)) as [H | H]; [ exact H | ].
    apply Nat.log2_lt_pow2 in H; [ lia | lia ]. }
  unfold planb_b_nlo.
  assert (Hd : (40 <= Nat.div2 (Nat.log2 q + 2))%nat).
  { apply Nat.div2_le_mono. lia. }
  destruct (2 ^ (2 * Nat.div2 (Nat.log2 q + 2)) <? 2 * q)%nat; lia.
Qed.

(* The frozen-carrier vacuity face at q >= 2^79 - the formal statement *)
(* of the survey finding (the fallback returns 0 at the table edge, so *)
(* the frozen twin reads 0 there).  Born statement, honestly unproven  *)
(* - NOT claimed here; near-mechanical once dispatched (the lemma      *)
(* above pins the index, the table fallback does the rest).            *)
Definition planb4_sl4_frozen_delta_vacuity : Prop :=
  forall q : nat, (2 ^ 79 <= q)%nat ->
    (planb3_g1_A (planb_b_nlo q) * planb3_g1_B (S (planb_b_nlo q))
     - planb3_g1_A (S (planb_b_nlo q)) * planb3_g1_B (planb_b_nlo q))%Z
    = 0%Z.

(* ================================================================== *)
(* Section 4. Assumption audit (tail).                                *)
(* ================================================================== *)

Print Assumptions planb4_sl4_delta.
Print Assumptions planb4_sl4_nlo_ge_40.
Print Assumptions planb4_sl4_window_slot_frozen.
Print Assumptions planb4_sl4_window_slot_abdef.
Print Assumptions planb4_sl4_frozen_delta_vacuity.
