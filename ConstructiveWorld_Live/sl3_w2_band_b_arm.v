(* ================================================================== *)
(* Ticket: D-SL3-7 - the B-arm band-swap interface unit.               *)
(* Statement list: sl3_w2_band_b_slot_arm, sl3_w2_band_b_qpow_arm      *)
(*   (born Set contract faces, sigma-parameterized, ZleT / QleT');     *)
(*   the bites b17_qpow_agrees_tree, planb17_agrees_slot17; the lifts  *)
(*   b_slot_arm_lift, b_qpow_arm_lift; the instances b_slot_17_to_18,  *)
(*   b_qpow_17_to_18; the projection b_of_slot_face; the census flag   *)
(*   b_fit_flag with anchors fit17_dom40, fit18_dom40,                 *)
(*   sigma12_falsified (short names; full names at the statements).    *)
(* Mission: the standalone B-arm contracts at a carried band argument, *)
(*   their upward lifts and named band-17-to-18 instances in both      *)
(*   slot dialects, the B-arm projection out of the joint slot face,   *)
(*   and the table-domain fit certificates for the B channel.          *)
(* Dependencies: Stdlib QArith, ZArith, Arith, Lia, Qpower; units      *)
(*   piu_mu_criterion, S02_CauchyComplete, piu_zz_sigma_decay,         *)
(*   planb1_hcage_zerotouch_prescription, planb3_g1_calib, and the     *)
(*   landed upstream unit sl3_d1_sigma_lift.                           *)
(* References: the upstream b1 slot faces and their parameterized      *)
(*   isomorphs; the joint slot face of the upstream lift unit; the     *)
(*   P4-era joint face; the calibration table and its fit certificate. *)
(* Constructivity: every named statement Set-carried; the two contract *)
(*   faces are born and honestly unproven (their universal supply is   *)
(*   the N5/N6' construction product); all proofs are real derivation  *)
(*   chains or computation certificates; zero assumption surfaces,     *)
(*   zero proof surrender, no solver finish; proven statements close   *)
(*   transparent (Defined).                                            *)
(* Build: coqc -native-compiler no -q -Q <live-closure-root> "" -Q     *)
(*   <sandbox-out> "" -o <sandbox-out>/sl3_w2_band_b_arm.vo this file  *)
(*   (full command line and source routing: receipt provenance ledger).*)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Qpower.
Require Import piu_mu_criterion.
Require Import S02_CauchyComplete.
Require Import piu_zz_sigma_decay.
Require Import planb1_hcage_zerotouch_prescription.
Require Import planb3_g1_calib.
Require Import sl3_d1_sigma_lift.

(* ================================================================ *)
(* Section 1. The born contract faces (sigma-parameterized).         *)
(* ================================================================ *)

(* The standalone B arm of the slot dialect at the band argument s:  *)
(* the sigma-carried contract for the B-side growth account alone.   *)
(* This is the interface the B-only reduction consumes (the upstream *)
(* criterion binds its B premise through this arm shape after its    *)
(* A-arm premise drops at the sole destruct position).  Born         *)
(* statement - honestly unproven: its universal supply is the N5/N6' *)
(* construction product registered in the upstream decay unit, not   *)
(* this ticket.                                                      *)
Definition sl3_w2_band_b_slot_arm (B : nat -> Z) (s : nat) : Set :=
  forall n : nat,
    piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (s * n))%Z.

(* The QleT'-dialect B arm at the band argument s: the isomorph of   *)
(* the upstream b1 B-face with the band carried as an explicit       *)
(* argument.  Born statement - honestly unproven for the same        *)
(* supply reason.                                                    *)
Definition sl3_w2_band_b_qpow_arm (B : nat -> Z) (s : nat) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (inject_Z (Z.abs (B n)))
      (Qpower (inject_Z 2) (Z.of_nat (s * n))).

(* ================================================================ *)
(* Section 2. Agreement bites (definitional unfoldings).             *)
(* ================================================================ *)

(* At band 17 the parameterized QleT' B arm unfolds exactly to the   *)
(* upstream b1 B-face applied at its own carrier: the parameterized  *)
(* face IS the tree face at that instance (the bite closes by        *)
(* definitional unfolding - the upstream agreement-bite precedent).  *)
Lemma sl3_w2_band_b17_qpow_agrees_tree :
  forall B : nat -> Z,
    piu_zz_n2b_hcoef17_B B = sl3_w2_band_b_qpow_arm B 17.
Proof. reflexivity. Defined.

(* The P4-era joint face at 17 unfolds exactly to the upstream       *)
(* parameterized joint slot face at 17: the pinned face is the       *)
(* band-17 instance of the carried face (bite by definitional        *)
(* unfolding; the projection below consumes the carried form).       *)
Lemma sl3_w2_band_planb17_agrees_slot17 :
  forall (A B : nat -> Z),
    planb_b_hcoef17 A B = sl3_hcoef_slot_face A B 17.
Proof. reflexivity. Defined.

(* ================================================================ *)
(* Section 3. The upward band lifts and the named instances.         *)
(* ================================================================ *)

(* Band-direction honesty: only the upward band (s <= s') is cast    *)
(* in this file.  The downward band (a supply at s' > s against a    *)
(* contract at s) is false in general - no downward bridge is cast   *)
(* or claimed.  No full-table band-17 A-arm face is cast either: the *)
(* machine-checked tension certificate at n = 5 refutes that form    *)
(* upstream and stays an asset.                                      *)
(* The ZleT-dialect upward lift: a B-arm supply at s discharges the  *)
(* B arm at s' >= s.  Engine: s <= s' gives s * n <= s' * n, hence   *)
(* 2^(s*n) <= 2^(s'*n) by the Z exponent monotonicity, and the arm   *)
(* re-seats under its constructor over the transitivity chain.       *)
Theorem sl3_w2_band_b_slot_arm_lift :
  forall (B : nat -> Z) (s s' : nat), (s <= s')%nat ->
    sl3_w2_band_b_slot_arm B s -> sl3_w2_band_b_slot_arm B s'.
Proof.
  intros B s s' Hs H.
  unfold sl3_w2_band_b_slot_arm in H |- *.
  intros n.
  destruct (H n) as [HB].
  assert (Hmono : (2 ^ Z.of_nat (s * n) <= 2 ^ Z.of_nat (s' * n))%Z).
  { apply (Z.pow_le_mono_r 2%Z (Z.of_nat (s * n)) (Z.of_nat (s' * n))).
    - lia.
    - apply (proj1 (Nat2Z.inj_le (s * n) (s' * n))).
      apply Nat.mul_le_mono_r. exact Hs. }
  apply piu_mu_ZleT_i.
  exact (Z.le_trans _ _ _ HB Hmono).
Defined.

(* The QleT'-dialect upward lift: a B-arm supply at s discharges the *)
(* B arm at s' >= s.  Engine: unpack the QleT' certificate into Qle,  *)
(* chain the dyadic exponent bound (the upstream engine lemma),       *)
(* re-certify with the Qle bridge.                                    *)
Theorem sl3_w2_band_b_qpow_arm_lift :
  forall (B : nat -> Z) (s s' : nat), (s <= s')%nat ->
    sl3_w2_band_b_qpow_arm B s -> sl3_w2_band_b_qpow_arm B s'.
Proof.
  intros B s s' Hs H.
  unfold sl3_w2_band_b_qpow_arm in H |- *.
  intros n.
  apply Qle_to_QleT'.
  apply (Qle_trans (inject_Z (Z.abs (B n)))
                   (Qpower (inject_Z 2) (Z.of_nat (s * n)))
                   (Qpower (inject_Z 2) (Z.of_nat (s' * n)))).
  - exact (QleT'_to_Qle _ _ (H n)).
  - assert (Hmn : (s * n <= s' * n)%nat)
      by (apply Nat.mul_le_mono_r; exact Hs).
    destruct (sl3_qpow2_le_mono_natT (s * n) (s' * n) Hmn) as [Hle].
    exact Hle.
Defined.

(* The named ZleT-dialect instance: the B arm lifts from band 17 to  *)
(* band 18 (the successor leg of the upward lift; the pinned values  *)
(* appear only in this named instance shape, mirroring the upstream  *)
(* named-instance pattern).                                          *)
Theorem sl3_w2_band_b_slot_17_to_18 :
  forall B : nat -> Z,
    sl3_w2_band_b_slot_arm B 17 -> sl3_w2_band_b_slot_arm B 18.
Proof.
  intros B H.
  apply (sl3_w2_band_b_slot_arm_lift B 17 18).
  - apply Nat.le_succ_diag_r.
  - exact H.
Defined.

(* The named QleT'-dialect instance: the B arm lifts from band 17 to *)
(* band 18 through the same upward engine.                           *)
Theorem sl3_w2_band_b_qpow_17_to_18 :
  forall B : nat -> Z,
    sl3_w2_band_b_qpow_arm B 17 -> sl3_w2_band_b_qpow_arm B 18.
Proof.
  intros B H.
  apply (sl3_w2_band_b_qpow_arm_lift B 17 18).
  - apply Nat.le_succ_diag_r.
  - exact H.
Defined.

(* ================================================================ *)
(* Section 4. The B-arm projection (the B-only route machine face).  *)
(* ================================================================ *)

(* From the joint slot face at any carried band, the B arm alone is  *)
(* recoverable: the joint face is the paired conjunction and its     *)
(* second component is exactly the standalone B arm.  This is the    *)
(* machine face of the B-only reduction: after the upstream          *)
(* criterion drops its A-arm premise at the sole destruct position,  *)
(* the surviving obligation is the B arm in this shape.  The         *)
(* reverse embedding (a bare B arm into the joint face) is NOT       *)
(* provable without an A-arm supply and is not cast.                 *)
Theorem sl3_w2_band_b_of_slot_face :
  forall (A B : nat -> Z) (s : nat),
    sl3_hcoef_slot_face A B s -> sl3_w2_band_b_slot_arm B s.
Proof.
  intros A B s H.
  unfold sl3_hcoef_slot_face in H.
  unfold sl3_w2_band_b_slot_arm.
  intros n.
  destruct (H n) as [_ HB].
  exact HB.
Defined.

(* ================================================================ *)
(* Section 5. The table-domain fit census (machine certificates).    *)
(* ================================================================ *)

(* The B-channel fit census over the calibration table domain: the   *)
(* flag scans n = 1..k and compares the B table magnitude against    *)
(* the dyadic carrier at the carried band.  The flag is a boolean    *)
(* certificate carrier; the anchors below pin it at bands 17 and 18  *)
(* over the full calibration domain n = 1..40.  These are TABLE-     *)
(* DOMAIN certificates, not the universal supply: the B table is a   *)
(* frozen calibration object on n = 1..40 (the out-of-domain value   *)
(* is zero), and the universal B-side account remains the N5/N6'     *)
(* construction product.                                             *)
Fixpoint sl3_w2_band_b_fit_flag (s k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      andb (Z.leb (Z.abs (planb3_g1_B (S k')))
                  (2 ^ Z.of_nat (s * S k')))
           (sl3_w2_band_b_fit_flag s k')
  end.

(* The band-17 whole-table fit census for the B channel: every       *)
(* calibration row satisfies |B n| <= 2^(17 n) on n = 1..40 (the     *)
(* upstream certificate pins only the n = 5 row; this census covers  *)
(* the whole domain machine-side).                                   *)
Example sl3_w2_band_b_fit17_dom40 : sl3_w2_band_b_fit_flag 17 40 = true.
Proof. vm_compute. reflexivity. Defined.

(* The band-18 whole-table fit census for the B channel: every       *)
(* calibration row satisfies |B n| <= 2^(18 n) on n = 1..40 (the     *)
(* head-side certificate for the band-18 target pin's B side).       *)
Example sl3_w2_band_b_fit18_dom40 : sl3_w2_band_b_fit_flag 18 40 = true.
Proof. vm_compute. reflexivity. Defined.

(* The band-12 position is machine-refuted for the B side: the       *)
(* first calibration row already exceeds the carrier, 7176 > 2^12    *)
(* (the upstream A-side refutation precedent, mirrored here for B;   *)
(* the supply side can never discharge the band-12 slot).            *)
Example sl3_w2_band_b_sigma12_falsified :
  (2 ^ 12 < Z.abs (planb3_g1_B 1))%Z.
Proof. vm_compute. reflexivity. Defined.

(* ================================================================ *)
(* Section 6. Assumption audit.                                      *)
(* ================================================================ *)

Print Assumptions sl3_w2_band_b_slot_arm.
Print Assumptions sl3_w2_band_b_qpow_arm.
Print Assumptions sl3_w2_band_b17_qpow_agrees_tree.
Print Assumptions sl3_w2_band_planb17_agrees_slot17.
Print Assumptions sl3_w2_band_b_slot_arm_lift.
Print Assumptions sl3_w2_band_b_qpow_arm_lift.
Print Assumptions sl3_w2_band_b_slot_17_to_18.
Print Assumptions sl3_w2_band_b_qpow_17_to_18.
Print Assumptions sl3_w2_band_b_of_slot_face.
Print Assumptions sl3_w2_band_b_fit_flag.
Print Assumptions sl3_w2_band_b_fit17_dom40.
Print Assumptions sl3_w2_band_b_fit18_dom40.
Print Assumptions sl3_w2_band_b_sigma12_falsified.

(* ================================================================ *)
(* Section 7. Supply-honesty ledger (comment face only - zero        *)
(* statement change).                                                *)
(* ================================================================ *)

(* SUPPLY-HONESTY LEDGER:                                            *)
(*   The two contract faces in Section 1 are born and honestly       *)
(*   unproven: their universal supply is the B-side growth account   *)
(*   of the N5/N6' construction scope, registered in the upstream    *)
(*   decay unit and in the survey volume, not discharged here.       *)
(*   The delivery is sigma-parameterized: the band argument is       *)
(*   carried on both faces and on both lifts; the pinned values 17   *)
(*   and 18 appear only in the named upward instances (Section 3)    *)
(*   and in the table-domain certificates (Section 5) - no pinned-   *)
(*   value universal supply face is cast.                            *)
(*   Band direction: upward only.  The downward direction is false   *)
(*   in general; no downward bridge is cast or claimed in this       *)
(*   file.  The band-12 position is machine-refuted for the B side   *)
(*   (the Section 5 anchor) and is not delivered.                    *)
(*   No full-table band-17 A-arm face exists here or upstream: the   *)
(*   machine-checked tension certificate at n = 5 refutes that form  *)
(*   and is an asset, not bypassed by any statement in this file.    *)
(*   The Section 5 census is table-domain only (n = 1..40 over the   *)
(*   frozen calibration table); it is a head-side certificate, not   *)
(*   a universal claim.                                              *)
(*   Consumption path: the projection (Section 4) plus the           *)
(*   agreement bites (Section 2) wire the P4-era joint face into     *)
(*   the standalone B arm; the companion migration unit lifts the    *)
(*   B arm across the dialects and onto the band-18 target pin.      *)
