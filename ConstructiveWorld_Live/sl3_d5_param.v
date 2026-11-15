(* ================================================================== *)
(* Ticket: D-SL3-5 - the sigma-parameterized supply recast plus the    *)
(*   three-pin annotation face.                                        *)
(* Statement list: sl3_aj_allj_pow_bound_face (Set contract face,      *)
(*   born); sl3_qpow2_form_natT (auxiliary lemma, proven);             *)
(*   sl3_aj_supply_at_37 (theorem, proven - coarse-band instance);     *)
(*   sl3_aj_allj_pow_bound_lift (theorem, proven - upward lift);       *)
(*   sl3_supply17_agrees_allj17, sl3_slot17_agrees_b1_A/B (bites);     *)
(*   sl3_slot18_from_slot17 (theorem, proven - band-18 instance).      *)
(* Source routing: follows the SL3 slot-statement draft and its survey *)
(*   volume; exact paths live in the delivery-receipt provenance ledger. *)
(* Build: coqc -native-compiler no -q -Q <vo-closure-root> "" -Q       *)
(*   <sandbox-upstream-vo-dir> "" sl3_d5_param.v (full line in the    *)
(*   provenance ledger).                                               *)
(* Related registrations: the pin ledger and tension-face asset note   *)
(*   at the end are comment-level only; band 12 is NOT delivered; no   *)
(*   full-table band-17 A-arm face is cast here.                       *)
(* Mission: one parameterized supply face, three pin instantiations -  *)
(*   band 17 tree instance, 18 target pin via lift, 12 recorded only.  *)
(* Dependencies: Stdlib QArith, ZArith, Arith, Qpower, Qabs; project   *)
(*   units S02_CauchyComplete, piu_zz_kernel_sum, piu_zz_sigma_decay,  *)
(*   sl3_d1_sigma_lift.                                                *)
(* References: the b1 slot faces and the b2 all-j face (bite targets); *)
(*   the crude band-37 theorem and the b0 bridge; the fourslots        *)
(*   Hcoef slot face.                                                  *)
(* Constructivity: data-carrying statements Set-carried; proven        *)
(*   statements close Defined (transparent); zero assumption surfaces, *)
(*   zero proof surrender, no solver finish; the born face is          *)
(*   honestly unproven (universal proof = N2c chain product).          *)
(* ================================================================== *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Qpower.
From Stdlib Require Import QArith.Qabs.
Require Import S02_CauchyComplete.
Require Import piu_zz_kernel_sum.
Require Import piu_zz_sigma_decay.
Require Import sl3_d1_sigma_lift.

(* ================================================================ *)
(* Section 1. The sigma-parameterized supply face (born).            *)
(* ================================================================ *)

(* The all-j coefficient envelope of the kernel-sum coefficients at  *)
(* the band argument s: the sigma-carried recast of the N2b all-j    *)
(* consumption face.  At s = 17 this face IS the tree acceptance     *)
(* interface; at s = 19 it is the retained fallback margin tier      *)
(* registered in the N2c assembly unit.  Born statement - honestly   *)
(* unproven: its universal proof consumes the N2c chain product (the *)
(* GF decomposition supply); only the band argument is new here.     *)
(* The witness-side wiring from this envelope to the Hcoef slot face *)
(* is a different account and is NOT claimed in this file.           *)
Definition sl3_aj_allj_pow_bound_face (s : nat) : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    QleT' (Qabs (piu_zz_Aj n j))
          (Qpower (inject_Z 2) (Z.of_nat (s * n))).

(* ================================================================ *)
(* Section 2. The power-form conversion engine at base two.          *)
(* ================================================================ *)

(* The dyadic carrier in Qpower form equals the integer-power        *)
(* fraction form, for every nat exponent.  The tree declines the     *)
(* symbolic-n conversion in the N2c assembly unit (its form witness  *)
(* is concrete-n only); this engine supplies it.  Engine: induction  *)
(* on the exponent; the successor step splits the Qpower argument by *)
(* the Qpower additivity over Z (the base is nonzero) and multiplies *)
(* the integer-power fraction by the inject_Z image of two, with the *)
(* nat-side successor law for the power.                             *)
Lemma sl3_qpow2_form_natT :
  forall k : nat, Qpower (inject_Z 2) (Z.of_nat k) == ((Z.of_nat (2 ^ k)) # 1)%Q.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r'.
    rewrite Nat2Z.inj_succ.
    change (Z.succ (Z.of_nat k)) with (Z.of_nat k + 1)%Z.
    assert (H2nz : ~ (inject_Z 2 == 0)%Q).
    { intros H2. unfold Qeq, inject_Z in H2. cbn in H2. discriminate. }
    rewrite (Qpower_plus (inject_Z 2) (Z.of_nat k) 1%Z H2nz).
    replace (Qpower (inject_Z 2) 1%Z) with (inject_Z 2)%Q by reflexivity.
    rewrite IH.
    rewrite Nat2Z.inj_mul.
    unfold Qeq, inject_Z.
    cbn [Qnum Qden Qmult Z.of_nat].
    rewrite !Z.mul_1_r.
    apply Z.mul_comm.
Qed.

(* ================================================================ *)
(* Section 3. The proven coarse-band instance of the supply face.    *)
(* ================================================================ *)

(* The supply face is inhabited at the crude band 37: the crude      *)
(* band-37 theorem of the kernel-sum unit (local qleT dialect)       *)
(* enters the QleT' world through the b0 bridge, and the band-form   *)
(* witness above moves the carrier into the Qpower form.  This       *)
(* instance does NOT step toward the target bands: the downward      *)
(* band direction is false in general and no downward bridge exists. *)
Theorem sl3_aj_supply_at_37 : sl3_aj_allj_pow_bound_face 37.
Proof.
  unfold sl3_aj_allj_pow_bound_face.
  intros n j Hj.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (piu_zz_Aj n j))
                   ((Z.of_nat (2 ^ (37 * n)) # 1)%Q)
                   (Qpower (inject_Z 2) (Z.of_nat (37 * n)))).
  - exact (QleT'_to_Qle _ _
            (piu_zz_n2b_qleT_to_QleT' _ _ (piu_zz_crude_size n j Hj))).
  - exact (qeq_imp_qle _ _ (Qeq_sym _ _ (sl3_qpow2_form_natT (37 * n)))).
Defined.

(* The upward supply lift: a supply at s discharges the same face at *)
(* s' >= s.  Same engine as the upstream slot lift - the band        *)
(* product is monotone in the multiplier, then the dyadic carrier    *)
(* bound applies.  The downward direction is false in general and no *)
(* downward lift is cast.                                            *)
Theorem sl3_aj_allj_pow_bound_lift :
  forall (s s' : nat), (s <= s')%nat ->
    sl3_aj_allj_pow_bound_face s -> sl3_aj_allj_pow_bound_face s'.
Proof.
  intros s s' Hs H.
  unfold sl3_aj_allj_pow_bound_face in H |- *.
  intros n j Hj.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qabs (piu_zz_Aj n j))
                   (Qpower (inject_Z 2) (Z.of_nat (s * n)))
                   (Qpower (inject_Z 2) (Z.of_nat (s' * n)))).
  - exact (QleT'_to_Qle _ _ (H n j Hj)).
  - assert (Hmn : (s * n <= s' * n)%nat)
      by (apply Nat.mul_le_mono_r; exact Hs).
    destruct (sl3_qpow2_le_mono_natT (s * n) (s' * n) Hmn) as [Hle].
    exact Hle.
Defined.

(* ================================================================ *)
(* Section 4. The three-instantiation contract.                      *)
(* ================================================================ *)

(* INST-17 (the tree instance): at band 17 the parameterized supply  *)
(* face agrees definitionally with the tree all-j acceptance face,   *)
(* and the parameterized slot face (upstream) agrees with both b1    *)
(* arms at the whole-statement level.  The tree b1 faces are         *)
(* minimally generalized by their Section (each binds only its       *)
(* constrained arm); the bites attest that the upstream slot face at *)
(* 17 unfolds exactly to each arm statement universally quantified - *)
(* the second arm carries no constraint, which is the upstream       *)
(* slot-shape parallelism note attested machine-side.  The face body *)
(* names its first binder, so the A bite reads the A arm at that     *)
(* binder and the B bite attests the very same unfolding against the *)
(* B arm statement.  Closed by definitional unfolding - the tree     *)
(* precedent is the sharp-face agreement bite in the N2c assembly    *)
(* unit.                                                             *)
Lemma sl3_supply17_agrees_allj17 :
  piu_zz_n2b_A_allj_le17_face = sl3_aj_allj_pow_bound_face 17.
Proof. reflexivity. Defined.

Lemma sl3_slot17_agrees_b1_A :
  sl3_n2b_hcoefA_at 17 = forall A B : nat -> Z, piu_zz_n2b_hcoef17_A A.
Proof. reflexivity. Defined.

Lemma sl3_slot17_agrees_b1_B :
  sl3_n2b_hcoefA_at 17 = forall A B : nat -> Z, piu_zz_n2b_hcoef17_B A.
Proof. reflexivity. Defined.

(* INST-18 (the target pin): a supply at band 17 discharges the      *)
(* parameterized slot face at band 18 through the upstream upward    *)
(* lift.  The joint two-arm form is the upstream named-instance      *)
(* bridge; this file does not duplicate it.                          *)
Theorem sl3_slot18_from_slot17 :
  sl3_n2b_hcoefA_at 17 -> sl3_n2b_hcoefA_at 18.
Proof.
  intro H17.
  exact (sl3_n2b_hcoefA_lift 17 18 (Nat.le_succ_diag_r 17) H17).
Defined.

(* INST-12 (the blocked position): NOT delivered here.  See the      *)
(* pin ledger in Section 6.                                          *)

(* ================================================================ *)
(* Section 5. Kernel audit prints.                                   *)
(* ================================================================ *)

Print Assumptions sl3_aj_allj_pow_bound_face.
Print Assumptions sl3_qpow2_form_natT.
Print Assumptions sl3_aj_supply_at_37.
Print Assumptions sl3_aj_allj_pow_bound_lift.
Print Assumptions sl3_supply17_agrees_allj17.
Print Assumptions sl3_slot17_agrees_b1_A.
Print Assumptions sl3_slot17_agrees_b1_B.
Print Assumptions sl3_slot18_from_slot17.

(* ================================================================ *)
(* Section 6. Pin ledger and tension-face asset note (comment face   *)
(* only - zero statement change).                                    *)
(* ================================================================ *)

(* THREE-PIN LEDGER: three pins coexist in the package data plane    *)
(* (the registered state this ledger records):                       *)
(*   pin 12: piu_zz_ec_sigma = 12 (the e-carrier unit, the six-tau   *)
(*     lock intact) - the fourslots Hcoef slot face is pinned at     *)
(*     this constant.  The slot carries 12, NOT 18: the fourslots    *)
(*     slot position and the band-18 prescription pin are two        *)
(*     different positions and must not be conflated.                *)
(*   pin 17: hardcoded 17 - the P4-era five-premise faces in the     *)
(*     prescription unit (the hcoef17 face and the MuBound 17 2      *)
(*     conclusion).                                                  *)
(*   pin 18: planb_b_sigma = 18 (the re-pin; zero external consumers *)
(*     of the pin itself, internal span/E/slot derivation only).     *)
(* sigma = 12 is machine-refuted for the ZZ family: the sigma-12     *)
(* falsified certificate holds 2^24 < |A_{2,0}| = 37324672, so the   *)
(* supply side can never discharge the slot at 12 - the slot must be *)
(* re-pinned first.  The three-pin unification is one open           *)
(* convergence item reserved for main-session adjudication: this     *)
(* file records the coexistence and casts no re-pin and touches no   *)
(* tree.  The unification prerequisites (the six-tau lock break and  *)
(* the span/E/slot contrast faces) are already landed in the         *)
(* prescription unit.  The lift statements above serve the 17 -> 18  *)
(* leg once the supply face is discharged.                           *)
(*                                                                   *)
(* TENSION-FACE ASSET NOTE: the machine-checked calibration tension  *)
(* face 2^85 < |A 5| (the planb3 calibration certificate) is an      *)
(* ASSET, not a debt: it machine-refutes the full-table band-17      *)
(* A-arm form of the supply, and no supply statement bypasses or     *)
(* supersedes it.  Three legal supply forms only: the                *)
(* sigma-parameterized face (Section 1), a band-18 pin, or the       *)
(* B-only reduction (the A-arm premise drops at its sole destruct    *)
(* position in the criterion unit).  Accordingly NO full-table       *)
(* band-17 A-arm face is cast in this file: band 17 is reached only  *)
(* as an instance of the parameterized face, and its universal       *)
(* proof stays the N2c chain product (an open registered debt).      *)
(*                                                                   *)
(* THE THREE INSTANTIATIONS of the one parameterized supply:         *)
(*   INST-17: the tree N2b instance - the agreement bites in         *)
(*     Section 4; the witness-side wiring from the all-j envelope    *)
(*     (over the kernel-sum coefficients) to the witness slot face   *)
(*     is NOT claimed in this file: it is the general-n witness      *)
(*     formula debt, outside this ticket's base.                     *)
(*   INST-18: reached by the upward lift only (Section 4 theorem,    *)
(*     plus the upstream named-instance bridge for the joint arms).  *)
(*   INST-12: NOT deliverable - the band is machine-refuted for the  *)
(*     ZZ family; no face is cast at 12 and no supply claim is made  *)
(*     there.                                                        *)
(*                                                                   *)
(* FALLBACK TIER: at s = 19 the parameterized face is the retained   *)
(* fallback margin tier of the N2c assembly; the proven coarse-band  *)
(* instance here sits at s = 37 (the crude skeleton band) and does   *)
(* not step toward the target bands - the downward direction is      *)
(* false in general and no downward bridge exists.                   *)
