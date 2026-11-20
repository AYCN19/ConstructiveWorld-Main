(* ========================================================================= *)
(* ConstructiveWorld-Main continuation - SL4 debt row D-SL4-4: reduced-     *)
(* denominator window extension (13..18), face (1..18), gcd account.        *)
(* Ticket        : D-SL4-4 remainder (survey volume SL4, section 9 ledger);  *)
(* continuation of sl4_d4_denom_anchors (window 1..12) over segment         *)
(* planb4_g1_calibwin_b2 (n = 13..18).                                      *)
(* Statement list: planb4_sl4_d4_denom_anchor_13 .. _18;                    *)
(* planb4_sl4_d4_denom_table_18 (full direct window face over 1..18,        *)
(* consuming the twelve anchors of sl4_d4_denom_anchors by name);           *)
(* planb4_sl4_d4_gcdub_5 .. _18 (14 point anchors of the reduction gcd      *)
(* premise); planb4_sl4_d4_gcdub_3_pin_over / _4_pin_over (the gcd pin      *)
(* 2^((7n-11)/2) is overshoot at n = 3, 4);                                 *)
(* planb4_sl4_d4_denom_via_accounts_table (reduction route face over        *)
(* 5..18 through planb4_sl4_d4_denom_transfer).  Nothing else is named.     *)
(* Mission       : machine-discharge the reduction skeleton gcd premise     *)
(* on its true certified domain (5..18) and extend the direct anchors.      *)
(* Dependencies  : planb3_g1_calib; planb4_g1_ab_def; planb4_sl4_skeleton;  *)
(* planb4_g1_calibwin_b1/b2; sl4_d3_growth_anchor; sl4_d4_denom_anchors;    *)
(* sl4_d4_denom_skeleton; sl4_w2_growth_anchor.                             *)
(* References    : survey volume SL4 sections 2/3/9 (rows D-SL4-3/4);       *)
(* skeleton sections 3/4/7; sl4_d4_denom_skeleton (arithmetic spine).       *)
(* Source routing: closure sources byte-exact from origin/main              *)
(* ConstructiveWorld_Live (git show); the md5 ledger lives in the receipt.  *)
(* Build         : coqc -native-compiler no -q -Q <sandbox root> ""         *)
(* sl4_w2_growth_d4_denom_anchor.v (Rocq 9.3.0, scripted form; compile      *)
(* after sl4_w2_growth_anchor).                                             *)
(* Constructivity: decidable Z comparisons only (Z.leb = true or false,     *)
(* closed by vm_compute and reflexivity); bite transfer; lia bookkeeping.   *)
(* Related registrations: see the trailing registration ledger of this file.*)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith ZArith.ZArith Arith.Arith Lia.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.
Require Import planb4_sl4_skeleton.
Require Import planb4_g1_calibwin_b1.
Require Import planb4_g1_calibwin_b2.
Require Import sl4_d3_growth_anchor.
Require Import sl4_d4_denom_anchors.
Require Import sl4_d4_denom_skeleton.
Require Import sl4_w2_growth_anchor.

(* ================================================================== *)
(* Section 1. Point anchors n = 13..18 for the reduced denominator    *)
(*            bound (decidable Z.leb = true form; bite transfer, the  *)
(*            ab_def Qred chains never evaluated).                    *)
(* ================================================================== *)

Example planb4_sl4_d4_denom_anchor_13 :
  Z.leb (2 ^ ((Z.of_nat 13 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 13) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_13).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_13).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_14 :
  Z.leb (2 ^ ((Z.of_nat 14 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 14) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_14).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_14).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_15 :
  Z.leb (2 ^ ((Z.of_nat 15 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 15) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_15).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_15).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_16 :
  Z.leb (2 ^ ((Z.of_nat 16 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 16) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_16).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_16).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_17 :
  Z.leb (2 ^ ((Z.of_nat 17 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 17) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_17).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_17).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_18 :
  Z.leb (2 ^ ((Z.of_nat 18 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 18) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_18).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_18).
  vm_compute.
  reflexivity.
Qed.


(* ================================================================== *)
(* Section 2. The full direct window face over 1 <= n <= 18: cases    *)
(*            1..12 consume the twelve anchors of sl4_d4_denom_anchors *)
(*            by name; cases 13..18 consume Section 1.                *)
(* ================================================================== *)

Example planb4_sl4_d4_denom_table_18 :
  forall n : nat, (1 <= n)%nat -> (n <= 18)%nat ->
    Z.leb (2 ^ ((Z.of_nat n * 5 - 1) / 2))
          (planb4_sl4_denom_reduced n) = true.
Proof.
  intros n H1 H2.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]]]]]].
  - lia. (* n = 0 contradicts H1 *)
  - apply planb4_sl4_d4_denom_anchor_1.
  - apply planb4_sl4_d4_denom_anchor_2.
  - apply planb4_sl4_d4_denom_anchor_3.
  - apply planb4_sl4_d4_denom_anchor_4.
  - apply planb4_sl4_d4_denom_anchor_5.
  - apply planb4_sl4_d4_denom_anchor_6.
  - apply planb4_sl4_d4_denom_anchor_7.
  - apply planb4_sl4_d4_denom_anchor_8.
  - apply planb4_sl4_d4_denom_anchor_9.
  - apply planb4_sl4_d4_denom_anchor_10.
  - apply planb4_sl4_d4_denom_anchor_11.
  - apply planb4_sl4_d4_denom_anchor_12.
  - apply planb4_sl4_d4_denom_anchor_13.
  - apply planb4_sl4_d4_denom_anchor_14.
  - apply planb4_sl4_d4_denom_anchor_15.
  - apply planb4_sl4_d4_denom_anchor_16.
  - apply planb4_sl4_d4_denom_anchor_17.
  - apply planb4_sl4_d4_denom_anchor_18.
  - lia. (* n >= 19 contradicts H2 *)
Qed.

(* ================================================================== *)
(* Section 3. The reduction gcd account on the certified domain.      *)
(*            The d4 reduction skeleton needs, per n, the gcd upper   *)
(*            bound gcd(|A n|, |B n|) <= 2^((7n-11)/2).  Machine      *)
(*            truth over the frozen table: the pin holds for n =      *)
(*            5..40 with growing margin, and is overshoot at n = 3    *)
(*            (gcd 2240 vs 32) and n = 4 (gcd 352 vs 256) - both      *)
(*            overshoot facts are minted below as decidable machine   *)
(*            anchors, so the via-accounts face starts at n = 5 and   *)
(*            the n = 1..4 slices stay covered by the direct anchors. *)
(* ================================================================== *)

(* pin overshoot at n = 3 (machine fact, decidable form). *)
Example planb4_sl4_d4_gcdub_3_pin_over :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 3)) (Z.abs (planb4_g1_B 3)))
        (2 ^ ((Z.of_nat 3 * 7 - 11) / 2)) = false.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_3).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_3).
  vm_compute.
  reflexivity.
Qed.

(* pin overshoot at n = 4 (machine fact, decidable form). *)
Example planb4_sl4_d4_gcdub_4_pin_over :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 4)) (Z.abs (planb4_g1_B 4)))
        (2 ^ ((Z.of_nat 4 * 7 - 11) / 2)) = false.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_4).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_4).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_5 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 5)) (Z.abs (planb4_g1_B 5)))
        (2 ^ ((Z.of_nat 5 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_5).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_5).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_6 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 6)) (Z.abs (planb4_g1_B 6)))
        (2 ^ ((Z.of_nat 6 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_6).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_6).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_7 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 7)) (Z.abs (planb4_g1_B 7)))
        (2 ^ ((Z.of_nat 7 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_7).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_7).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_8 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 8)) (Z.abs (planb4_g1_B 8)))
        (2 ^ ((Z.of_nat 8 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_8).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_8).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_9 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 9)) (Z.abs (planb4_g1_B 9)))
        (2 ^ ((Z.of_nat 9 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_9).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_9).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_10 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 10)) (Z.abs (planb4_g1_B 10)))
        (2 ^ ((Z.of_nat 10 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_10).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_10).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_11 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 11)) (Z.abs (planb4_g1_B 11)))
        (2 ^ ((Z.of_nat 11 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_11).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_11).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_12 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 12)) (Z.abs (planb4_g1_B 12)))
        (2 ^ ((Z.of_nat 12 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_12).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_12).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_13 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 13)) (Z.abs (planb4_g1_B 13)))
        (2 ^ ((Z.of_nat 13 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_13).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_13).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_14 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 14)) (Z.abs (planb4_g1_B 14)))
        (2 ^ ((Z.of_nat 14 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_14).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_14).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_15 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 15)) (Z.abs (planb4_g1_B 15)))
        (2 ^ ((Z.of_nat 15 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_15).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_15).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_16 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 16)) (Z.abs (planb4_g1_B 16)))
        (2 ^ ((Z.of_nat 16 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_16).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_16).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_17 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 17)) (Z.abs (planb4_g1_B 17)))
        (2 ^ ((Z.of_nat 17 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_17).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_17).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_gcdub_18 :
  Z.leb (Z.gcd (Z.abs (planb4_g1_A 18)) (Z.abs (planb4_g1_B 18)))
        (2 ^ ((Z.of_nat 18 * 7 - 11) / 2)) = true.
Proof.
  unfold planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_18).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_18).
  vm_compute.
  reflexivity.
Qed.


(* ================================================================== *)
(* Section 4. The via-accounts window face over 5 <= n <= 18: the     *)
(*            reduction skeleton route, now with both per-n accounts  *)
(*            machine-discharged (growth from the twelve anchors of   *)
(*            sl4_d3_growth_anchor and the six anchors of             *)
(*            sl4_w2_growth_anchor, gcd from Section 3).  This        *)
(*            cross-checks the direct window face of Section 2        *)
(*            through the reduction machinery on the whole shared     *)
(*            domain.                                                 *)
(* ================================================================== *)

Example planb4_sl4_d4_denom_via_accounts_table :
  forall n : nat, (5 <= n)%nat -> (n <= 18)%nat ->
    (2 ^ ((Z.of_nat n * 5 - 1) / 2)
     <= planb4_sl4_denom_reduced n)%Z.
Proof.
  intros n H5 Hhi.
  assert (H3 : (3 <= n)%nat) by lia.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]]]]]].
  - lia. (* n = 0 contradicts H5 *)
  - lia. (* n = 1 contradicts H5 *)
  - lia. (* n = 2 contradicts H5 *)
  - lia. (* n = 3 contradicts H5 *)
  - lia. (* n = 4 contradicts H5 *)
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_5.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_5.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_6.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_6.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_7.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_7.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_8.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_8.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_9.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_9.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_10.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_10.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_11.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_11.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_12.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_12.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_13.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_13.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_14.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_14.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_15.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_15.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_16.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_16.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_17.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_17.
  - apply (planb4_sl4_d4_denom_transfer _ H3).
    + apply planb4_sl4_bgrow_18.
    + apply Z.leb_le. apply planb4_sl4_d4_gcdub_18.
  - lia. (* n >= 19 contradicts Hhi *)
Qed.

(* ================================================================== *)
(* Section 5. Born-face consumption and honest registration.          *)
(*            The forall-n body is NOT claimed here.  The born face   *)
(*            below is re-typechecked by name (skeleton section 4);   *)
(*            the machine-certified domain is the frozen-table window *)
(*            1..18 (direct) plus the reduction route on 5..18; the   *)
(*            forall-n proof needs the general-n growth account (the  *)
(*            P6 debt, D-SL4-3 born face) and a forall-n gcd upper    *)
(*            bound over the N2c chain - both outside this file's     *)
(*            reach (survey sections 2 and 9).                        *)
(* ================================================================== *)

Check planb4_sl4_denom_bound.

(* ================================================================== *)
(* Section 6. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb4_sl4_d4_denom_anchor_13.
Print Assumptions planb4_sl4_d4_denom_anchor_14.
Print Assumptions planb4_sl4_d4_denom_anchor_15.
Print Assumptions planb4_sl4_d4_denom_anchor_16.
Print Assumptions planb4_sl4_d4_denom_anchor_17.
Print Assumptions planb4_sl4_d4_denom_anchor_18.
Print Assumptions planb4_sl4_d4_gcdub_3_pin_over.
Print Assumptions planb4_sl4_d4_gcdub_4_pin_over.
Print Assumptions planb4_sl4_d4_gcdub_5.
Print Assumptions planb4_sl4_d4_gcdub_6.
Print Assumptions planb4_sl4_d4_gcdub_7.
Print Assumptions planb4_sl4_d4_gcdub_8.
Print Assumptions planb4_sl4_d4_gcdub_9.
Print Assumptions planb4_sl4_d4_gcdub_10.
Print Assumptions planb4_sl4_d4_gcdub_11.
Print Assumptions planb4_sl4_d4_gcdub_12.
Print Assumptions planb4_sl4_d4_gcdub_13.
Print Assumptions planb4_sl4_d4_gcdub_14.
Print Assumptions planb4_sl4_d4_gcdub_15.
Print Assumptions planb4_sl4_d4_gcdub_16.
Print Assumptions planb4_sl4_d4_gcdub_17.
Print Assumptions planb4_sl4_d4_gcdub_18.
Print Assumptions planb4_sl4_d4_denom_table_18.
Print Assumptions planb4_sl4_d4_denom_via_accounts_table.

(* ==================== registration ledger (comments only) =============== *)
(* Born-face registration: the forall-n face planb4_sl4_denom_bound stays   *)
(* honestly unproven (skeleton section 4); the forall-n proof needs the     *)
(* general-n growth account (the P6 debt, D-SL4-3 born face) and a          *)
(* forall-n gcd upper bound over the N2c chain.                             *)
(* Gcd-pin domain registration: the reduction pin 2^((7n-11)/2) is machine- *)
(* true over 5..40 on the frozen table with growing margin, and machine-    *)
(* false at n = 3 (gcd 2240 vs 32) and n = 4 (gcd 352 vs 256); the two      *)
(* overshoot facts are minted above, so the via-accounts face starts at     *)
(* n = 5 and the n = 1..4 slices stay covered by the direct anchors.        *)
(* Window-completion debt (machine-time, not mathematical): the bite        *)
(* segments planb4_g1_calibwin_b3..b6 carry the n = 19..40 machine facts;   *)
(* their status and the generator re-emit plan are registered in the        *)
(* trailing ledger of sl4_w2_growth_anchor.                                 *)
(* Registered review conditions for the forall-n gcd account: the N2c chain *)
(* landing; the ZZ2020 v2 forall-n structure; a Gantumur-type oracle        *)
(* analogue.                                                                *)
(* = end of the D-SL4-4 window extension, certified window face, and gcd account = *)
