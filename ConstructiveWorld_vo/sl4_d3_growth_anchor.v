(* ========================================================================= *)
(* ConstructiveWorld-Main - unif L4 growth account: the SL4 B-side table-    *)
(* domain pin-6 anchors (dispatch row D-SL4-3, ticket sl4_d3_growth).        *)
(* Mission      : Ticket No. D-SL4-3 (growth account, breakthrough half 1).  *)
(*                Faces minted here: twelve machine anchors                *)
(*                planb4_sl4_bgrow_1..12, each proving (2 ^ Z.of_nat         *)
(*                (6 * (n - 1)) <= Z.abs (planb4_g1_B n))%Z on the total     *)
(*                ab_def carrier, plus the table-domain forall face          *)
(*                planb4_sl4_bgrowth_table over 1 <= n <= 12.  Registered    *)
(*                remainder, NOT claimed here: the n = 13..40 window (bite   *)
(*                cost beyond the single-anchor compute budget; re-anchor    *)
(*                debt; born forall-n face: skeleton Section 3, unproven).   *)
(* Dependencies : planb3_g1_calib (frozen B channel, fallback 0 above n=40); *)
(*                planb4_g1_ab_def (carrier + value bites 1..6);             *)
(*                planb4_g1_calibwin_b1   (bites 7..12; verbatim Main-Live  *)
(*                sources, md5-copied, rebuilt over the fresh sandbox        *)
(*                calib/ab_def generation; package base snapshots plus       *)
(*                closure deps only - source routing).                       *)
(* References   : survey volume sec 9 row D-SL4-3; skeleton Sections 3/7     *)
(*                (born face and ledger row); delta_anchor bite-transfer     *)
(*                craft; survey sec 3 (bit growth behind pin 6).             *)
(* Constructivity: each anchor = one value-bite rewrite (Z.eqb_eq) then one  *)
(*                vm_compute step on plain Z - the ab_def Qred chains are    *)
(*                never evaluated here.  Table face = 19-case dispatch;      *)
(*                lia only for out-of-range bookkeeping (n = 0, n >= 13).    *)
(*                Z-carried statements; postulate-free: no Parameter, no     *)
(*                Conjecture, no Abort, no admission commands, no Unset GC.  *)
(* Build        : coqc -native-compiler no -q -Q <sandbox root> ""           *)
(*                sl4_d3_growth_anchor.v (Rocq 9.3.0; products sandboxed).   *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.
Require Import planb4_g1_calibwin_b1.

(* ================================================================== *)
(* Section 1. Per-n anchors: the pin-6 lower bound on the B channel,  *)
(*            n = 1..12, discharged by bite transfer (the frozen      *)
(*            channels are machine values; the Qred chains of the     *)
(*            total carrier are never evaluated here).                *)
(* ================================================================== *)

(* n = 1: |B 1| >= 2^(6(1-1)); bite planb4_ab_Bcal_1 (planb4_g1_ab_def). *)
Example planb4_sl4_bgrow_1 :
  (2 ^ Z.of_nat ((6 * (1 - 1))%nat)
   <= Z.abs (planb4_g1_B 1))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_1).
  vm_compute. discriminate.
Qed.

(* n = 2: |B 2| >= 2^(6(2-1)); bite planb4_ab_Bcal_2 (planb4_g1_ab_def). *)
Example planb4_sl4_bgrow_2 :
  (2 ^ Z.of_nat ((6 * (2 - 1))%nat)
   <= Z.abs (planb4_g1_B 2))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_2).
  vm_compute. discriminate.
Qed.

(* n = 3: |B 3| >= 2^(6(3-1)); bite planb4_ab_Bcal_3 (planb4_g1_ab_def). *)
Example planb4_sl4_bgrow_3 :
  (2 ^ Z.of_nat ((6 * (3 - 1))%nat)
   <= Z.abs (planb4_g1_B 3))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_3).
  vm_compute. discriminate.
Qed.

(* n = 4: |B 4| >= 2^(6(4-1)); bite planb4_ab_Bcal_4 (planb4_g1_ab_def). *)
Example planb4_sl4_bgrow_4 :
  (2 ^ Z.of_nat ((6 * (4 - 1))%nat)
   <= Z.abs (planb4_g1_B 4))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_4).
  vm_compute. discriminate.
Qed.

(* n = 5: |B 5| >= 2^(6(5-1)); bite planb4_ab_Bcal_5 (planb4_g1_ab_def). *)
Example planb4_sl4_bgrow_5 :
  (2 ^ Z.of_nat ((6 * (5 - 1))%nat)
   <= Z.abs (planb4_g1_B 5))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_5).
  vm_compute. discriminate.
Qed.

(* n = 6: |B 6| >= 2^(6(6-1)); bite planb4_ab_Bcal_6 (planb4_g1_ab_def). *)
Example planb4_sl4_bgrow_6 :
  (2 ^ Z.of_nat ((6 * (6 - 1))%nat)
   <= Z.abs (planb4_g1_B 6))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_6).
  vm_compute. discriminate.
Qed.

(* n = 7: |B 7| >= 2^(6(7-1)); bite planb4_ab_Bcal_7 (planb4_g1_calibwin_b1). *)
Example planb4_sl4_bgrow_7 :
  (2 ^ Z.of_nat ((6 * (7 - 1))%nat)
   <= Z.abs (planb4_g1_B 7))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_7).
  vm_compute. discriminate.
Qed.

(* n = 8: |B 8| >= 2^(6(8-1)); bite planb4_ab_Bcal_8 (planb4_g1_calibwin_b1). *)
Example planb4_sl4_bgrow_8 :
  (2 ^ Z.of_nat ((6 * (8 - 1))%nat)
   <= Z.abs (planb4_g1_B 8))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_8).
  vm_compute. discriminate.
Qed.

(* n = 9: |B 9| >= 2^(6(9-1)); bite planb4_ab_Bcal_9 (planb4_g1_calibwin_b1). *)
Example planb4_sl4_bgrow_9 :
  (2 ^ Z.of_nat ((6 * (9 - 1))%nat)
   <= Z.abs (planb4_g1_B 9))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_9).
  vm_compute. discriminate.
Qed.

(* n = 10: |B 10| >= 2^(6(10-1)); bite planb4_ab_Bcal_10 (planb4_g1_calibwin_b1). *)
Example planb4_sl4_bgrow_10 :
  (2 ^ Z.of_nat ((6 * (10 - 1))%nat)
   <= Z.abs (planb4_g1_B 10))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_10).
  vm_compute. discriminate.
Qed.

(* n = 11: |B 11| >= 2^(6(11-1)); bite planb4_ab_Bcal_11 (planb4_g1_calibwin_b1). *)
Example planb4_sl4_bgrow_11 :
  (2 ^ Z.of_nat ((6 * (11 - 1))%nat)
   <= Z.abs (planb4_g1_B 11))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_11).
  vm_compute. discriminate.
Qed.

(* n = 12: |B 12| >= 2^(6(12-1)); bite planb4_ab_Bcal_12 (planb4_g1_calibwin_b1). *)
Example planb4_sl4_bgrow_12 :
  (2 ^ Z.of_nat ((6 * (12 - 1))%nat)
   <= Z.abs (planb4_g1_B 12))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_12).
  vm_compute. discriminate.
Qed.


(* ================================================================== *)
(* Section 2. The table-domain forall face over the anchored window:  *)
(*            the pin-6 bound holds for every 1 <= n <= 12.  This is  *)
(*            a proven fragment of the born face planb4_sl4_bgrowth   *)
(*            (skeleton Section 3); the window 13..40 and the         *)
(*            forall-n body stay registered debt - NOT claimed here.  *)
(* ================================================================== *)

Example planb4_sl4_bgrowth_table :
  forall n : nat, (1 <= n)%nat -> (n <= 12)%nat ->
    (2 ^ Z.of_nat ((6 * (n - 1))%nat)
     <= Z.abs (planb4_g1_B n))%Z.
Proof.
  intros n H1 H2.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]].
  - lia. (* n = 0 contradicts H1 *)
  - apply planb4_sl4_bgrow_1.
  - apply planb4_sl4_bgrow_2.
  - apply planb4_sl4_bgrow_3.
  - apply planb4_sl4_bgrow_4.
  - apply planb4_sl4_bgrow_5.
  - apply planb4_sl4_bgrow_6.
  - apply planb4_sl4_bgrow_7.
  - apply planb4_sl4_bgrow_8.
  - apply planb4_sl4_bgrow_9.
  - apply planb4_sl4_bgrow_10.
  - apply planb4_sl4_bgrow_11.
  - apply planb4_sl4_bgrow_12.
  - lia. (* n >= 13 contradicts H2 *)
Qed.

(* ================================================================== *)
(* Section 3. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_sl4_bgrow_1.
Print Assumptions planb4_sl4_bgrow_2.
Print Assumptions planb4_sl4_bgrow_3.
Print Assumptions planb4_sl4_bgrow_4.
Print Assumptions planb4_sl4_bgrow_5.
Print Assumptions planb4_sl4_bgrow_6.
Print Assumptions planb4_sl4_bgrow_7.
Print Assumptions planb4_sl4_bgrow_8.
Print Assumptions planb4_sl4_bgrow_9.
Print Assumptions planb4_sl4_bgrow_10.
Print Assumptions planb4_sl4_bgrow_11.
Print Assumptions planb4_sl4_bgrow_12.
Print Assumptions planb4_sl4_bgrowth_table.

(* = end of the D-SL4-3 growth anchors (window 1..12) = *)
