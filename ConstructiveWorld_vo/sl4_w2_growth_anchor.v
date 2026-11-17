(* ========================================================================= *)
(* ConstructiveWorld-Main continuation - SL4 debt row D-SL4-3: the B-side   *)
(* growth window extension (n = 13..18) and certified window face (1..18).  *)
(* Ticket        : D-SL4-3 remainder (survey volume SL4, section 9 ledger);  *)
(*                 continuation of sl4_d3_growth_anchor (window 1..12)     *)
(*                 over the bite segment planb4_g1_calibwin_b2.            *)
(* Statement list: planb4_sl4_bgrow_13 .. _18 (6 point anchors, pin 6:      *)
(*                 (2 ^ (6*(n-1)))%Z <= |B n| on the total ab_def carrier); *)
(*                 planb4_sl4_bgrowth_table_18 (window face over 1..18,     *)
(*                 consuming the twelve anchors of sl4_d3_growth_anchor by  *)
(*                 name); a Check line re-typechecking the born face        *)
(*                 planb4_sl4_bgrowth (skeleton section 3).  Nothing else   *)
(*                 is named.                                                *)
(* Mission       : complete the machine-certified domain of the pin-6       *)
(*                 B-channel growth account over the frozen table window.  *)
(* Dependencies  : planb3_g1_calib; planb4_g1_ab_def; planb4_g1_calibwin_b2; *)
(*                 planb4_sl4_skeleton (born face, consumed by name).      *)
(* References    : survey volume SL4 sections 2/3/9 (row D-SL4-3); skeleton *)
(*                 sections 3/7; survey section 7 leverage list.           *)
(* Source routing: closure sources extracted byte-exact from origin/main    *)
(*                 ConstructiveWorld_Live (git show); the md5 ledger lives  *)
(*                 in the delivery receipt, not in this file.              *)
(* Build         : coqc -native-compiler no -q -Q <sandbox root> ""        *)
(*                 sl4_w2_growth_anchor.v (Rocq 9.3.0, scripted form).     *)
(* Constructivity: Z-carried statements; each anchor = one value-bite       *)
(*                 rewrite (Z.eqb_eq) then one vm_compute step on plain Z   *)
(*                 (the ab_def Qred chains are never evaluated); lia only   *)
(*                 for out-of-range bookkeeping bullets; postulate-free.   *)
(* Related registrations: see the trailing registration ledger of this file. *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.
Require Import planb4_g1_calibwin_b2.
Require Import sl4_d3_growth_anchor.
Require Import planb4_sl4_skeleton.

(* ================================================================== *)
(* Section 1. Point anchors n = 13..18: the pin-6 lower bound on the  *)
(*            B channel, discharged by bite transfer over the         *)
(*            frozen machine values (the ab_def Qred chains are       *)
(*            never evaluated here).                                  *)
(* ================================================================== *)

(* n = 13: |B 13| >= 2^(6(13-1)); bite planb4_ab_Bcal_13 (planb4_g1_calibwin_b2). *)
Example planb4_sl4_bgrow_13 :
  (2 ^ Z.of_nat ((6 * (13 - 1))%nat)
   <= Z.abs (planb4_g1_B 13))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_13).
  vm_compute. discriminate.
Qed.

(* n = 14: |B 14| >= 2^(6(14-1)); bite planb4_ab_Bcal_14 (planb4_g1_calibwin_b2). *)
Example planb4_sl4_bgrow_14 :
  (2 ^ Z.of_nat ((6 * (14 - 1))%nat)
   <= Z.abs (planb4_g1_B 14))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_14).
  vm_compute. discriminate.
Qed.

(* n = 15: |B 15| >= 2^(6(15-1)); bite planb4_ab_Bcal_15 (planb4_g1_calibwin_b2). *)
Example planb4_sl4_bgrow_15 :
  (2 ^ Z.of_nat ((6 * (15 - 1))%nat)
   <= Z.abs (planb4_g1_B 15))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_15).
  vm_compute. discriminate.
Qed.

(* n = 16: |B 16| >= 2^(6(16-1)); bite planb4_ab_Bcal_16 (planb4_g1_calibwin_b2). *)
Example planb4_sl4_bgrow_16 :
  (2 ^ Z.of_nat ((6 * (16 - 1))%nat)
   <= Z.abs (planb4_g1_B 16))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_16).
  vm_compute. discriminate.
Qed.

(* n = 17: |B 17| >= 2^(6(17-1)); bite planb4_ab_Bcal_17 (planb4_g1_calibwin_b2). *)
Example planb4_sl4_bgrow_17 :
  (2 ^ Z.of_nat ((6 * (17 - 1))%nat)
   <= Z.abs (planb4_g1_B 17))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_17).
  vm_compute. discriminate.
Qed.

(* n = 18: |B 18| >= 2^(6(18-1)); bite planb4_ab_Bcal_18 (planb4_g1_calibwin_b2). *)
Example planb4_sl4_bgrow_18 :
  (2 ^ Z.of_nat ((6 * (18 - 1))%nat)
   <= Z.abs (planb4_g1_B 18))%Z.
Proof.
  unfold planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_18).
  vm_compute. discriminate.
Qed.


(* ================================================================== *)
(* Section 2. The full window face: the pin-6 bound holds for every   *)
(*            1 <= n <= 18.  Cases 1..12 consume the twelve anchors   *)
(*            of sl4_d3_growth_anchor by name; cases 13..18 consume   *)
(*            Section 1; the range guards are bookkeeping only.       *)
(* ================================================================== *)

Example planb4_sl4_bgrowth_table_18 :
  forall n : nat, (1 <= n)%nat -> (n <= 18)%nat ->
    (2 ^ Z.of_nat ((6 * (n - 1))%nat)
     <= Z.abs (planb4_g1_B n))%Z.
Proof.
  intros n H1 H2.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]]]]]].
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
  - apply planb4_sl4_bgrow_13.
  - apply planb4_sl4_bgrow_14.
  - apply planb4_sl4_bgrow_15.
  - apply planb4_sl4_bgrow_16.
  - apply planb4_sl4_bgrow_17.
  - apply planb4_sl4_bgrow_18.
  - lia. (* n >= 19 contradicts H2 *)
Qed.

(* ================================================================== *)
(* Section 3. Born-face consumption and honest registration.          *)
(*            The forall-n body is NOT claimed here.  The born face   *)
(*            below is re-typechecked by name (skeleton section 3);   *)
(*            the machine-certified domain is the frozen-table window *)
(*            1..18.  Beyond n = 18 the total carrier still computes, *)
(*            but neither machine anchors nor certificates exist      *)
(*            there; the forall-n proof needs the general-n Laurent   *)
(*            product structure (the P6 debt) or a decay-coupled      *)
(*            route (survey section 2), both outside this file's      *)
(*            reach.                                                  *)
(* ================================================================== *)

Check planb4_sl4_bgrowth.

(* ================================================================== *)
(* Section 4. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_sl4_bgrow_13.
Print Assumptions planb4_sl4_bgrow_14.
Print Assumptions planb4_sl4_bgrow_15.
Print Assumptions planb4_sl4_bgrow_16.
Print Assumptions planb4_sl4_bgrow_17.
Print Assumptions planb4_sl4_bgrow_18.
Print Assumptions planb4_sl4_bgrowth_table_18.

(* ==================== registration ledger (comments only) =============== *)
(* Born-face registration: the forall-n face planb4_sl4_bgrowth stays       *)
(* honestly unproven (skeleton section 3); the machine-certified window     *)
(* after this file is exactly 1..18.                                        *)
(* Window-completion debt (machine-time, not mathematical): the bite        *)
(* segments planb4_g1_calibwin_b3..b6 carry the n = 19..40 machine facts    *)
(* and none has ever completed a machine build on this host - aborted stub  *)
(* products sit beside their sources in the main tree Live directory, the   *)
(* predecessor collection note in sl4_d4_denom_anchors records the segments *)
(* as still compiling at collection time, and the predecessor sandbox holds *)
(* b1 and b2 only.  Segment cost is hours-to-days scale per segment (the    *)
(* predecessor b2 vo landed about eight hours after its b1 vo); when an     *)
(* idle machine window completes b3..b6, the same anchor generator re-emits *)
(* the 19..40 block unchanged.                                              *)
(* Forall-n route re-inventory against the current tree: the SL1 band       *)
(* supplies remain open debts (sl1_head_anchors header); the SL3 universal  *)
(* N2c sharp face is premise-carried (sl3_d4_chain header: the universal    *)
(* pole domination stays open); the Laurent r/s general-n face is the P6    *)
(* debt.  Registered review conditions for the forall-n body: T1 re-estimate *)
(* of the pole structure; the ZZ2020 v2 forall-n structure; a Gantumur-type *)
(* oracle analogue for the growth account.                                  *)
(* = end of the D-SL4-3 window extension (13..18) and certified window face = *)
