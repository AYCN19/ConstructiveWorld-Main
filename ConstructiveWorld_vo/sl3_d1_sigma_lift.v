(* ================================================================== *)
(* Ticket: D-SL3-1 - the sigma band-lift bridge and the slot           *)
(*   isomorphism face.                                                 *)
(* Statement list: sl3_hcoef_slot_face (Set contract face - the        *)
(*   sigma-carried isomorph of the fourslots Hcoef slot);              *)
(*   sl3_hcoef_sigma_lift (theorem, proven - upward lift, ZleT         *)
(*   dialect); sl3_n2b_hcoefA_at (Set contract face - the sigma-       *)
(*   carried A arm, QleT' dialect); sl3_n2b_hcoefA_lift (theorem,      *)
(*   proven - upward lift, QleT' dialect); sl3_n2b_hcoef_17_to_18      *)
(*   (theorem, proven - named instance bridge);                        *)
(*   sl3_qpow2_le_mono_natT (auxiliary lemma).                         *)
(* Source routing: faces follow section 2 of the SL3 slot-statement    *)
(*   draft and its survey volume in the outbound package; exact        *)
(*   document paths live in the external provenance ledger attached    *)
(*   to the delivery receipt, not in this file.                        *)
(* Build: coqc -native-compiler no -q -Q <vo-closure-root> ""          *)
(*   sl3_d1_sigma_lift.v (full line in the provenance ledger).         *)
(* Related registrations: the pin-unification ledger at the end is     *)
(*   comment-level only (zero statement change); the sigma-12 slot is  *)
(*   NOT delivered here (see the ledger and the Section 3 note).       *)
(* Mission: the upward sigma lifts of the Hcoef slot face plus the     *)
(*   named 17-to-18 instance bridge (upward direction only).           *)
(* Dependencies: Stdlib QArith, ZArith, Arith, Lia, Qpower; project    *)
(*   units piu_mu_criterion and S02_CauchyComplete only.               *)
(* References: the fourslots Hcoef slot face and the N2b b1 A-arm      *)
(*   face (the two slot dialects carried explicitly here).             *)
(* Constructivity: all six named statements Set-carried; zero          *)
(*   assumption surfaces and zero proof surrender; no solver finish    *)
(*   on the lift theorems; theorems close Defined (transparent).       *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Qpower.
Require Import piu_mu_criterion.
Require Import S02_CauchyComplete.

(* ================================================================ *)
(* Section 1. The slot faces (sigma-carried, Set-typed).             *)
(* ================================================================ *)

(* The Hcoef slot face at the sigma argument s: the                 *)
(* sigma-carried isomorph of the fourslots ledger slot face, with    *)
(* the pin carried as an explicit argument instead of a fixed        *)
(* constant.  Born statement - the contract face for the supply      *)
(* side; the supply that discharges it is the N2c chain debt, not    *)
(* this ticket.                                                      *)
Definition sl3_hcoef_slot_face (A B : nat -> Z) (s : nat) : Set :=
  forall n : nat,
    piu_mu_and2
      (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (s * n))%Z)
      (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (s * n))%Z).

(* The QleT'-dialect slot face at the sigma argument s: the N2b     *)
(* b1-face isomorph with the band carried as an explicit argument.   *)
(* Only the A arm is constrained - the B-side mapping belongs to the *)
(* N5/N6' construction scope, and B is bound for slot-shape          *)
(* parallelism.  Born statement - the contract face.                 *)
Definition sl3_n2b_hcoefA_at (s : nat) : Set :=
  forall (A B : nat -> Z) (n : nat),
    QleT' (inject_Z (Z.abs (A n)))
          (Qpower (inject_Z 2) (Z.of_nat (s * n))).

(* ================================================================ *)
(* Section 2. Q-power exponent monotonicity at base two.             *)
(* ================================================================ *)

(* The arithmetic engine under both lifts: for nat exponents        *)
(* a <= b the dyadic carrier 2^a is bounded by 2^b over Q.  Engine:  *)
(* split b = a + d, expand 2^(a+d) = 2^a * 2^d over Q (the base two  *)
(* is nonzero), then 2^a <= 2^a * 2^d holds because 1 <= 2^d and     *)
(* 0 <= 2^a.                                                         *)
Lemma sl3_qpow2_le_mono_natT :
  forall (a b : nat), (a <= b)%nat ->
    piu_mu_QleT (Qpower (inject_Z 2) (Z.of_nat a))
                (Qpower (inject_Z 2) (Z.of_nat b)).
Proof.
  intros a b Hab.
  replace b with (a + (b - a))%nat by lia.
  assert (H2nz : ~ (inject_Z 2 == 0)%Q).
  { intros H2. unfold Qeq, inject_Z in H2. cbn in H2. discriminate. }
  (* the core bound lives entirely in the stdlib Qle context: the    *)
  (* Qeq-stated expansions rewrite only under registered morphism    *)
  (* contexts, so the wrapper constructor is applied at the very end *)
  assert (Hcore : (Qpower (inject_Z 2) (Z.of_nat a)
                <= Qpower (inject_Z 2) (Z.of_nat (a + (b - a))))%Q).
  { rewrite Nat2Z.inj_add.
    rewrite (Qpower_plus (inject_Z 2) (Z.of_nat a) (Z.of_nat (b - a)) H2nz).
    assert (Hge : (1 <= Qpower (inject_Z 2) (Z.of_nat (b - a)))%Q).
    { apply (Qpower_1_le (inject_Z 2) (Z.of_nat (b - a))).
      - unfold Qle, inject_Z. cbn. lia.
      - lia. }
    assert (Hpos : (0 <= Qpower (inject_Z 2) (Z.of_nat a))%Q).
    { apply (Qpower_0_le (inject_Z 2) (Z.of_nat a)).
      unfold Qle, inject_Z. cbn. lia. }
    pose proof (Qmult_le_compat_r 1 (Qpower (inject_Z 2) (Z.of_nat (b - a)))
                (Qpower (inject_Z 2) (Z.of_nat a)) Hge Hpos) as Hm.
    rewrite Qmult_1_l in Hm.
    rewrite (Qmult_comm (Qpower (inject_Z 2) (Z.of_nat (b - a)))
                        (Qpower (inject_Z 2) (Z.of_nat a))) in Hm.
    exact Hm. }
  apply piu_mu_QleT_i.
  exact Hcore.
Defined.

(* ================================================================ *)
(* Section 3. The upward sigma lift bridges (both dialects).         *)
(* ================================================================ *)

(* Band-direction honesty: only the upward band (s <= s') is cast   *)
(* here.  The downward band (a supply at s' > s against a slot at   *)
(* s) is false in general - no downward bridge is cast or claimed.  *)
(* No full-table sigma-17 A-arm face is cast either: the machine-    *)
(* checked tension face at n = 5 refutes that form, and that tension *)
(* face is an asset - it is not bypassed by any supply statement.    *)
(* The sigma-12 slot position is not delivered through this file;    *)
(* its unification re-pin is a pre-L4 convergence debt reserved for  *)
(* main-session adjudication (the Section 6 ledger records it).      *)

(* The sigma lift bridge (piu_mu_ZleT dialect): upward re-pin is    *)
(* monotone - a supply at s discharges the slot at s' >= s.  Engine: *)
(* s <= s' gives s * n <= s' * n, hence 2^(s*n) <= 2^(s'*n) by Z     *)
(* exponent monotonicity, and each arm re-seats under its            *)
(* constructor.  The reverse direction is false in general and no    *)
(* downward bridge is cast (survey volume, section 2.2).             *)
Theorem sl3_hcoef_sigma_lift :
  forall (A B : nat -> Z) (s s' : nat), (s <= s')%nat ->
    sl3_hcoef_slot_face A B s -> sl3_hcoef_slot_face A B s'.
Proof.
  intros A B s s' Hs H.
  unfold sl3_hcoef_slot_face in H |- *.
  intros n. destruct (H n) as [HA HB].
  assert (Hmono : (2 ^ Z.of_nat (s * n) <= 2 ^ Z.of_nat (s' * n))%Z).
  { apply (Z.pow_le_mono_r 2%Z (Z.of_nat (s * n)) (Z.of_nat (s' * n))).
    - lia.
    - apply (proj1 (Nat2Z.inj_le (s * n) (s' * n))).
      apply Nat.mul_le_mono_r. exact Hs. }
  apply piu_mu_and2_i.
  - destruct HA as [HA]. apply piu_mu_ZleT_i.
    exact (Z.le_trans _ _ _ HA Hmono).
  - destruct HB as [HB]. apply piu_mu_ZleT_i.
    exact (Z.le_trans _ _ _ HB Hmono).
Defined.

(* The sigma lift bridge (QleT' dialect): the A-arm slot face at s  *)
(* lifts to s' >= s.  Engine: unpack the QleT' certificate into Qle  *)
(* (QleT'_to_Qle), chain the dyadic exponent bound                  *)
(* (sl3_qpow2_le_mono_natT), re-certify with Qle_to_QleT'.           *)
Theorem sl3_n2b_hcoefA_lift :
  forall (s s' : nat), (s <= s')%nat ->
    sl3_n2b_hcoefA_at s -> sl3_n2b_hcoefA_at s'.
Proof.
  intros s s' Hs H.
  unfold sl3_n2b_hcoefA_at in H |- *.
  intros A B n.
  apply Qle_to_QleT'.
  apply (Qle_trans (inject_Z (Z.abs (A n)))
                   (Qpower (inject_Z 2) (Z.of_nat (s * n)))
                   (Qpower (inject_Z 2) (Z.of_nat (s' * n)))).
  - exact (QleT'_to_Qle _ _ (H A B n)).
  - assert (Hmn : (s * n <= s' * n)%nat)
      by (apply Nat.mul_le_mono_r; exact Hs).
    destruct (sl3_qpow2_le_mono_natT (s * n) (s' * n) Hmn) as [Hle].
    exact Hle.
Defined.

(* ================================================================ *)
(* Section 4. The named instance bridge: band 17 lifts to 18.        *)
(* ================================================================ *)

(* The 17 -> 18 instance bridge (the named re-pin that the sigma-18 *)
(* landing left open).  Both arms lift by the dyadic exponent       *)
(* engine; the pair is carried by piu_mu_and2, the Set conjunction  *)
(* carrier of the slot dialect (the draft's Prop conjunction form   *)
(* is re-cast here to keep the embedded-Prop channel at zero).  The *)
(* B arm consumes the same supply shape for B; the B-side supply    *)
(* mapping itself is the N5/N6' construction scope, registered, not *)
(* claimed here.                                                     *)
Theorem sl3_n2b_hcoef_17_to_18 :
  forall (A B : nat -> Z),
    (forall n : nat,
       QleT' (inject_Z (Z.abs (A n)))
             (Qpower (inject_Z 2) (Z.of_nat (17 * n)))) ->
    (forall n : nat,
       QleT' (inject_Z (Z.abs (B n)))
             (Qpower (inject_Z 2) (Z.of_nat (17 * n)))) ->
    piu_mu_and2
      (forall n : nat,
         QleT' (inject_Z (Z.abs (A n)))
               (Qpower (inject_Z 2) (Z.of_nat (18 * n))))
      (forall n : nat,
         QleT' (inject_Z (Z.abs (B n)))
               (Qpower (inject_Z 2) (Z.of_nat (18 * n)))).
Proof.
  intros A B HA17 HB17.
  apply piu_mu_and2_i.
  - intros n.
    assert (Hmn : (17 * n <= 18 * n)%nat) by lia.
    destruct (sl3_qpow2_le_mono_natT (17 * n) (18 * n) Hmn) as [Hle].
    apply Qle_to_QleT'.
    exact (Qle_trans (inject_Z (Z.abs (A n)))
                     (Qpower (inject_Z 2) (Z.of_nat (17 * n)))
                     (Qpower (inject_Z 2) (Z.of_nat (18 * n)))
                     (QleT'_to_Qle _ _ (HA17 n)) Hle).
  - intros n.
    assert (Hmn : (17 * n <= 18 * n)%nat) by lia.
    destruct (sl3_qpow2_le_mono_natT (17 * n) (18 * n) Hmn) as [Hle].
    apply Qle_to_QleT'.
    exact (Qle_trans (inject_Z (Z.abs (B n)))
                     (Qpower (inject_Z 2) (Z.of_nat (17 * n)))
                     (Qpower (inject_Z 2) (Z.of_nat (18 * n)))
                     (QleT'_to_Qle _ _ (HB17 n)) Hle).
Defined.

(* ================================================================ *)
(* Section 5. Kernel audit prints.                                   *)
(* ================================================================ *)

Print Assumptions sl3_hcoef_slot_face.
Print Assumptions sl3_n2b_hcoefA_at.
Print Assumptions sl3_qpow2_le_mono_natT.
Print Assumptions sl3_hcoef_sigma_lift.
Print Assumptions sl3_n2b_hcoefA_lift.
Print Assumptions sl3_n2b_hcoef_17_to_18.

(* ================================================================ *)
(* Section 6. Pin-unification ledger (comment face only - zero       *)
(* statement change).                                                *)
(* ================================================================ *)

(* PIN-UNIFICATION LEDGER: three pins coexist in the package data   *)
(* plane (the registered state this ledger records):                 *)
(*   pin 12: piu_zz_ec_sigma = 12 (piu_zz_e_carrier.v, the six-tau   *)
(*     lock piu_zz_ec_sigma = 6 * piu_zz_ec_tau intact) - the        *)
(*     fourslots Hcoef slot face is pinned at this constant          *)
(*     (planb4_l4_fourslots.v, the coefficient-growth slot).         *)
(*   pin 17: hardcoded 17 - the P4-era five-premise faces            *)
(*     (planb1_hcage_zerotouch_prescription.v: the hcoef17 face and  *)
(*     the MuBound 17 2 conclusion).                                 *)
(*   pin 18: planb_b_sigma = 18 (the A3 re-pin; zero external        *)
(*     consumers of the pin itself, internal span/E/slot derivation  *)
(*     only).                                                        *)
(* sigma = 12 is machine-refuted for the ZZ family: the sigma-12     *)
(* falsified certificate holds 2^24 < |A_{2,0}| = 37324672, and the  *)
(* calibration side holds |B_1| = 7176 > 2^12 - the supply side can  *)
(* never discharge the slot at 12, so the slot must be re-pinned     *)
(* first.  The unification re-pin (12 -> 18, with the six-tau lock   *)
(* break and the span 14 -> 20 / E 10 / slot 11 contrast faces       *)
(* already landed in the prescription unit) is a pre-L4 convergence  *)
(* debt reserved for main-session adjudication: this file records    *)
(* the coexisting pins and casts no re-pin and touches no tree.      *)
(* The lift bridges above serve the 17 -> 18 leg once the supply     *)
(* face lands.                                                       *)
