(* ========================================================================= *)
(* ConstructiveWorld-Main outbound package - SL4 debt row D-SL4-4, the      *)
(* table-domain anchors of the reduced-denominator bound (n = 1..12).       *)
(* Mission      : Dispatch row D-SL4-4 (survey volume SL4, section 9): the  *)
(*                reduced-denominator bound d_n >= 2^((5n-1)/2) on the      *)
(*                total carrier, where d_n is planb4_sl4_denom_reduced      *)
(*                (skeleton Section 4).  Point anchors for n = 1..12 (segments beyond pending), *)
(*                each discharged by transfer over the in-tree table-bite   *)
(*                facts; the complete forall-n face is NOT claimed here     *)
(*                (sl4_d4_denom_skeleton.v carries the reduction the open   *)
(*                accounts plug into).                                      *)
(* Statements   : planb4_sl4_d4_denom_anchor_1 .. _12 (one Example per n,   *)
(*                decidable Z.leb = true form; nothing else is named).      *)
(* Dependencies : planb3_g1_calib; planb4_g1_ab_def (carrier + bites        *)
(*                n = 1..6); planb4_g1_calibwin_b1..b1 (bites n = 7..12; segments b2..b6 pending, see the coverage ledger);   *)
(*                planb4_sl4_skeleton (consumed by name); Stdlib QArith,    *)
(*                ZArith.  Source routing: kept in the delivery receipt per *)
(*                the comment law, nothing written here.                    *)
(* References   : survey volume SL4 sections 2/3/9 (row D-SL4-4); skeleton  *)
(*                Section 4 (threshold pin 2^((5n-1)/2), criterion (i));    *)
(*                planb3_g1_g2_design.v:170-180 (N2c chain registration).   *)
(* Constructivity: decidable Z comparisons only (Z.leb = true, closed by    *)
(*                vm_compute and reflexivity); postulate-free; no           *)
(*                Parameter, no Conjecture, no Abort; the named results are *)
(*                proof items carrying no data, so no extraction surface.   *)
(* Build        : coqc -native-compiler no -q -Q <sandbox root> ""          *)
(*                sl4_d4_denom_anchors.v  (Rocq 9.3.0, scripted form;      *)
(*                compile after planb4_g1_calibwin_b1..b6).                *)
(* ========================================================================= *)
From Stdlib Require Import QArith.QArith ZArith.ZArith.
Require Import planb3_g1_calib.
Require Import planb4_g1_ab_def.
Require Import planb4_sl4_skeleton.
Require Import planb4_g1_calibwin_b1.


(* ================================================================== *)
(* Section 1. What the anchors certify.                               *)
(* ================================================================== *)

(* For each n the anchor states Z.leb 2^((5n-1)/2) d_n = true with      *)
(* d_n = planb4_sl4_denom_reduced n = |B n| / gcd(|A n|, |B n|) on the   *)
(* total carrier.  Z.div here is exact at every anchor (the gcd divides  *)
(* the numerator), so the machine value is the true reduced denominator. *)
(* Proof craft, per anchor: the in-tree table-bite facts                *)
(* planb4_ab_Acal_n / planb4_ab_Bcal_n (n = 1..6 in planb4_g1_ab_def,    *)
(* n = 7..40 in the six calibration window segments) rewrite the Qnum    *)
(* projections of the assembled channels to the frozen planb3_g1_A /     *)
(* planb3_g1_B table entries, and vm_compute then closes on plain Z      *)
(* arithmetic - the assembled Q-reduction chains are never evaluated,    *)
(* which keeps every anchor fast even at the top of the range.  The      *)
(* bound is stated in the decidable carrier Z.leb = true, so the         *)
(* certified comparison result is a bool value, not a bare relation.    *)
(* The Z equality is read off each bite with proj1 (Z.eqb_eq _ _); the  *)
(* direction is pinned by the anchor-form probe on Rocq 9.3.0.          *)

(* ================================================================== *)
(* Section 2. Point anchors, n = 1..12.                                *)
(* ================================================================== *)

(* n = 1..6: bites from planb4_g1_ab_def. *)
Example planb4_sl4_d4_denom_anchor_1 :
  Z.leb (2 ^ ((Z.of_nat 1 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 1) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_1).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_1).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_2 :
  Z.leb (2 ^ ((Z.of_nat 2 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 2) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_2).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_2).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_3 :
  Z.leb (2 ^ ((Z.of_nat 3 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 3) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_3).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_3).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_4 :
  Z.leb (2 ^ ((Z.of_nat 4 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 4) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_4).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_4).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_5 :
  Z.leb (2 ^ ((Z.of_nat 5 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 5) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_5).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_5).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_6 :
  Z.leb (2 ^ ((Z.of_nat 6 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 6) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_6).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_6).
  vm_compute.
  reflexivity.
Qed.

(* n = 7..12: bites from planb4_g1_calibwin_b1. *)

Example planb4_sl4_d4_denom_anchor_7 :
  Z.leb (2 ^ ((Z.of_nat 7 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 7) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_7).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_7).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_8 :
  Z.leb (2 ^ ((Z.of_nat 8 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 8) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_8).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_8).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_9 :
  Z.leb (2 ^ ((Z.of_nat 9 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 9) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_9).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_9).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_10 :
  Z.leb (2 ^ ((Z.of_nat 10 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 10) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_10).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_10).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_11 :
  Z.leb (2 ^ ((Z.of_nat 11 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 11) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_11).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_11).
  vm_compute.
  reflexivity.
Qed.

Example planb4_sl4_d4_denom_anchor_12 :
  Z.leb (2 ^ ((Z.of_nat 12 * 5 - 1) / 2))
        (planb4_sl4_denom_reduced 12) = true.
Proof.
  unfold planb4_sl4_denom_reduced, planb4_g1_A, planb4_g1_B.
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Bcal_12).
  rewrite (proj1 (Z.eqb_eq _ _) planb4_ab_Acal_12).
  vm_compute.
  reflexivity.
Qed.

(* ================================================================== *)
(* Section 3. Assumption audit (every anchor must print Closed).       *)
(* ================================================================== *)

Print Assumptions planb4_sl4_d4_denom_anchor_1.
Print Assumptions planb4_sl4_d4_denom_anchor_2.
Print Assumptions planb4_sl4_d4_denom_anchor_3.
Print Assumptions planb4_sl4_d4_denom_anchor_4.
Print Assumptions planb4_sl4_d4_denom_anchor_5.
Print Assumptions planb4_sl4_d4_denom_anchor_6.
Print Assumptions planb4_sl4_d4_denom_anchor_7.
Print Assumptions planb4_sl4_d4_denom_anchor_8.
Print Assumptions planb4_sl4_d4_denom_anchor_9.
Print Assumptions planb4_sl4_d4_denom_anchor_10.
Print Assumptions planb4_sl4_d4_denom_anchor_11.
Print Assumptions planb4_sl4_d4_denom_anchor_12.

(* Coverage ledger: anchors n = 13..40 are NOT in this file; their   *)
(* segment bites (planb4_g1_calibwin_b2..b6) were still compiling    *)
(* at collection time.  Continuation: rerun the generator without    *)
(* the range tag once those segments are compiled, then recompile    *)
(* and re-run the gates.  The per-n bound over the pending range is  *)
(* machine-checked independently by the mirror instrument log.       *)

(* ================== end of table-domain anchors ================= *)
