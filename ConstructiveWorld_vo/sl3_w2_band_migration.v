(* ================================================================== *)
(* Ticket: D-SL3-7 - the B-arm band-swap migration unit.               *)
(* Statement list, proven: sl3_w2_band_zlet_to_qpow_pointwise and      *)
(*   sl3_w2_band_qpow_to_zlet_pointwise (the ZleT / QleT' dialect      *)
(*   conversion pair at the point level); sl3_w2_band_b_slot_to_       *)
(*   qpow_arm and sl3_w2_band_b_qpow_to_slot_arm (the pair at the      *)
(*   arm level); sl3_w2_band_b_qpow18_of_planb17,                      *)
(*   sl3_w2_band_b_slot18_of_planb17, sl3_w2_band_b_qpow18_of_slot17   *)
(*   (the composed band-17-to-18 migrations off the joint faces).      *)
(* Mission: move a B-arm band contract across the two slot dialects    *)
(*   and compose the upward band lift with the projection and the      *)
(*   dialect bridges, giving the B-only route its full machine path    *)
(*   from the P4-era joint face to the QleT' arm at the band-18 pin.   *)
(* Dependencies: Stdlib QArith, ZArith, Arith, Lia, Qpower; units      *)
(*   piu_mu_criterion, S02_CauchyComplete,                             *)
(*   planb1_hcage_zerotouch_prescription, sl3_d1_sigma_lift, and the   *)
(*   companion unit sl3_w2_band_b_arm.                                 *)
(* References: the upstream joint slot face and its agreement bites;   *)
(*   the Q-power form conversion certificate of the calibration line;  *)
(*   the QleT' bridge pair of the Cauchy carrier unit.                 *)
(* Constructivity: every named statement Set-carried; all proofs are   *)
(*   real derivation chains (constructor re-seating, rewrite chains    *)
(*   over the power-form certificate, multi-lemma composition); zero   *)
(*   assumption surfaces, zero proof surrender, no solver finish;      *)
(*   proven statements close transparent (Defined).                    *)
(* Build: coqc -native-compiler no -q -Q <live-closure-root> "" -Q     *)
(*   <sandbox-out> "" -o <sandbox-out>/sl3_w2_band_migration.vo        *)
(*   this file (full command line and source routing: the receipt's    *)
(*   external provenance ledger).                                      *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Qpower.
Require Import piu_mu_criterion.
Require Import S02_CauchyComplete.
Require Import planb1_hcage_zerotouch_prescription.
Require Import sl3_d1_sigma_lift.
Require Import sl3_w2_band_b_arm.

(* ================================================================ *)
(* Section 1. The dialect conversion pair (point level).              *)
(* ================================================================ *)

(* The ZleT-to-QleT' conversion: an integer-magnitude bound against  *)
(* the dyadic carrier yields the QleT' certificate between the       *)
(* injected magnitude and the Q-power form.  Engine: unpack the      *)
(* constructor, rewrite the Q-power form onto the integer power      *)
(* (the power-form certificate over the natural-exponent side), then *)
(* read the rational comparison of the unit-denominator fractions    *)
(* back to the integer comparison (multiplication by the unit        *)
(* denominator cancelled by rewriting, no solver step).              *)
Lemma sl3_w2_band_zlet_to_qpow_pointwise :
  forall (x : Z) (k : nat),
    piu_mu_ZleT x (2 ^ Z.of_nat k)%Z ->
    S02_CauchyComplete.QleT' (inject_Z x)
      (Qpower (inject_Z 2) (Z.of_nat k)).
Proof.
  intros x k H.
  destruct H as [Hle].
  apply Qle_to_QleT'.
  assert (Hform : Qpower (inject_Z 2) (Z.of_nat k) == inject_Z (2 ^ Z.of_nat k)).
  { apply Qeq_sym. apply Zpower_Qpower. apply Nat2Z.is_nonneg. }
  rewrite Hform.
  unfold Qle, inject_Z.
  cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  exact Hle.
Defined.

(* The reverse conversion: the QleT' certificate between the         *)
(* injected magnitude and the Q-power form yields the integer        *)
(* bound.  Engine: certify with the Qle bridge, move the Q-power     *)
(* onto the integer power form, and read the unit-denominator        *)
(* fraction comparison back to the integer comparison.               *)
Lemma sl3_w2_band_qpow_to_zlet_pointwise :
  forall (x : Z) (k : nat),
    S02_CauchyComplete.QleT' (inject_Z x)
      (Qpower (inject_Z 2) (Z.of_nat k)) ->
    piu_mu_ZleT x (2 ^ Z.of_nat k)%Z.
Proof.
  intros x k H.
  apply piu_mu_ZleT_i.
  pose proof (QleT'_to_Qle (inject_Z x)
              (Qpower (inject_Z 2) (Z.of_nat k)) H) as HQ.
  assert (Hform : Qpower (inject_Z 2) (Z.of_nat k) == inject_Z (2 ^ Z.of_nat k)).
  { apply Qeq_sym. apply Zpower_Qpower. apply Nat2Z.is_nonneg. }
  rewrite Hform in HQ.
  unfold Qle, inject_Z in HQ.
  cbn [Qnum Qden] in HQ.
  rewrite !Z.mul_1_r in HQ.
  exact HQ.
Defined.

(* ================================================================ *)
(* Section 2. The dialect conversion pair (arm level).               *)
(* ================================================================ *)

(* Arm-level ZleT-to-QleT': the B arm contracts across the dialects  *)
(* pointwise.                                                        *)
Theorem sl3_w2_band_b_slot_to_qpow_arm :
  forall (B : nat -> Z) (s : nat),
    sl3_w2_band_b_slot_arm B s -> sl3_w2_band_b_qpow_arm B s.
Proof.
  intros B s H.
  unfold sl3_w2_band_b_qpow_arm.
  intros n.
  unfold sl3_w2_band_b_slot_arm in H.
  apply sl3_w2_band_zlet_to_qpow_pointwise.
  apply (H n).
Defined.

(* Arm-level QleT'-to-ZleT: the reverse direction pointwise.         *)
Theorem sl3_w2_band_b_qpow_to_slot_arm :
  forall (B : nat -> Z) (s : nat),
    sl3_w2_band_b_qpow_arm B s -> sl3_w2_band_b_slot_arm B s.
Proof.
  intros B s H.
  unfold sl3_w2_band_b_slot_arm.
  intros n.
  unfold sl3_w2_band_b_qpow_arm in H.
  apply sl3_w2_band_qpow_to_zlet_pointwise.
  apply (H n).
Defined.

(* ================================================================ *)
(* Section 3. The composed band-17-to-18 migrations.                 *)
(* ================================================================ *)

(* Band-direction honesty: only the upward band is composed here.    *)
(* The downward direction is false in general and no downward path   *)
(* is cast or claimed.                                               *)

(* The full B-only machine path off the P4-era joint face: the       *)
(* joint ZleT face at 17 collapses to the B arm (the projection      *)
(* through the agreement bite), crosses into the QleT' dialect, and  *)
(* lifts upward onto the band-18 target pin.  Engine chain: upward   *)
(* lift, dialect bridge, projection, agreement bite, the consumed    *)
(* premise.                                                          *)
Theorem sl3_w2_band_b_qpow18_of_planb17 :
  forall (A B : nat -> Z),
    planb_b_hcoef17 A B -> sl3_w2_band_b_qpow_arm B 18.
Proof.
  intros A B H.
  apply (sl3_w2_band_b_qpow_arm_lift B 17 18).
  - apply Nat.le_succ_diag_r.
  - apply sl3_w2_band_b_slot_to_qpow_arm.
    apply (sl3_w2_band_b_of_slot_face A B 17).
    rewrite <- (sl3_w2_band_planb17_agrees_slot17 A B).
    exact H.
Defined.

(* The same path within the ZleT dialect: the P4-era joint face at   *)
(* 17 yields the standalone B arm at the band-18 target pin.         *)
Theorem sl3_w2_band_b_slot18_of_planb17 :
  forall (A B : nat -> Z),
    planb_b_hcoef17 A B -> sl3_w2_band_b_slot_arm B 18.
Proof.
  intros A B H.
  apply (sl3_w2_band_b_slot_arm_lift B 17 18).
  - apply Nat.le_succ_diag_r.
  - apply (sl3_w2_band_b_of_slot_face A B 17).
    rewrite <- (sl3_w2_band_planb17_agrees_slot17 A B).
    exact H.
Defined.

(* The migration off the carried joint face: the upstream joint      *)
(* slot face at 17 yields the B arm in the QleT' dialect at the      *)
(* band-18 target pin (the carried-band consumer path).              *)
Theorem sl3_w2_band_b_qpow18_of_slot17 :
  forall (A B : nat -> Z),
    sl3_hcoef_slot_face A B 17 -> sl3_w2_band_b_qpow_arm B 18.
Proof.
  intros A B H.
  apply (sl3_w2_band_b_qpow_arm_lift B 17 18).
  - apply Nat.le_succ_diag_r.
  - apply sl3_w2_band_b_slot_to_qpow_arm.
    exact (sl3_w2_band_b_of_slot_face A B 17 H).
Defined.

(* ================================================================ *)
(* Section 4. Assumption audit.                                      *)
(* ================================================================ *)

Print Assumptions sl3_w2_band_zlet_to_qpow_pointwise.
Print Assumptions sl3_w2_band_qpow_to_zlet_pointwise.
Print Assumptions sl3_w2_band_b_slot_to_qpow_arm.
Print Assumptions sl3_w2_band_b_qpow_to_slot_arm.
Print Assumptions sl3_w2_band_b_qpow18_of_planb17.
Print Assumptions sl3_w2_band_b_slot18_of_planb17.
Print Assumptions sl3_w2_band_b_qpow18_of_slot17.

(* ================================================================ *)
(* Section 5. Supply-honesty ledger (comment face only - zero        *)
(* statement change).                                                *)
(* ================================================================ *)

(* SUPPLY-HONESTY LEDGER:                                            *)
(*   The embedding direction (a bare B arm into the joint slot       *)
(*   face) is NOT cast in this file: it would require an A-arm       *)
(*   supply, and no A-arm supply is claimed here.  The A-arm         *)
(*   premise drops at the sole destruct position of the upstream     *)
(*   criterion, which is why the B-only route runs through the       *)
(*   projection instead.                                             *)
(*   The universal B-side supply is the N5/N6' construction scope    *)
(*   (registered in the upstream decay unit and in the survey        *)
(*   volume); nothing in this file discharges it.  The companion     *)
(*   interface unit carries the born contract faces; this unit       *)
(*   carries only proven bridges and migrations over existing        *)
(*   supplies.                                                       *)
(*   Band direction: upward only (s <= s').  The downward direction  *)
(*   is false in general; no downward bridge or migration is cast    *)
(*   or claimed.  The pinned values 17 and 18 appear only in named   *)
(*   upward instances composed off the landed upstream pattern; the   *)
(*   contract faces themselves stay sigma-parameterized.             *)
