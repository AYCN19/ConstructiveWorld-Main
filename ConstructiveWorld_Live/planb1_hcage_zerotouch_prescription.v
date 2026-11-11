(* ConstructiveWorld-Main - Hcage zero-touch prescription piece: (B)-branch pins, escape faces and the five-premise consumption face. *)

(* Mission. In-tree internalization of the KB41m 6.2 (B)-branch prescription:
   the exponent chain pinned at sigma = 17 with tau = 2 alive, span 19,
   rate-slot exponent E = ceil(19/2) = 10 (was 7), slot 11 (was 8),
   kappa/c0 unchanged; E3_nat re-derived at sigma = 17 over the unchanged
   nesc witness (2^(34n) <= kappa^2 q^19); the square-root dance and the
   abstract slot-11 distance face (7 -> 10, 8 -> 11, isomorphic to
   e_carrier.v:469-527) live in the companion certificate unit
   planb1_hcage_zerotouch_prescription_cert; the Hcage ZERO-TOUCH face
   consumes the five-premise criterion with Hval supplied DIRECTLY as an
   explicit premise - no falsified (3/20)^n cage premise exists (KB41m 5.3).
Dependencies. Stdlib QArith, ZArith, Arith, Lia, Qpower; S02_CauchyComplete
   (QleT'/QeqT); piu_mu_criterion (QleT/ZleT/and2/and3/epos/MuBound, the
   five-premise criterion, Qinv nonnegativity). One-way layering: no
   e_carrier, no bridge_real, no real-layer units - the (B) pins are
   re-pinned locally (nescD.v:57-63 precedent).
References. KB41m 6.2 (B) redirect + 5.3 NEGATIVE (cage falsified at n=5);
   KB41h 5.2 (B)-row (exponent 7 -> 10, slot 8 -> 11) and 5.1 (E3_nat
   sigma=17 chain); e_carrier.v:54-94 (old pinning), :105-154 (nesc
   bounds + E1/E3), :613-679 (Section EC premises, ec_hval); nescD.v
   (witness + Q bridges); bracket.v:164-175 (slope certificate).
Constructivity. Every named statement is Set-carried (piu_mu_QleT/ZleT/
   and2/and3, sigT, S02 QleT'); propositional reasoning only inside proofs;
   definitions transparent; postulate-free, admission-free; every statement
   closes under the global context; Path-A: zero new-cast Prop surface,
   information-bit faces informative-sorted (QleT'/QleT/ZleT/sigT forms).
Build. coqc -q -native-compiler no -Q . "" -Q <green9 cache> "" (Rocq 9.3.0),
   serial single lane under cpu_guard_v3 (-AllowG3); coqchk MUST carry
   -bytecode-compiler yes. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.

(* ================================================================== *)
(* Section 1. The (B) pin block: sigma 12 -> 17, tau = 2 alive,       *)
(*            E = ceil(span/tau) = 10, slot 11, kappa/c0 unchanged.   *)
(* ================================================================== *)

Definition planb_b_tau : nat := 2%nat.
Definition planb_b_sigma : nat := 17%nat.
Definition planb_b_kappa : Q := (35831808 # 1)%Q.
Definition planb_b_span : nat := (planb_b_sigma + planb_b_tau)%nat.
Definition planb_b_E : nat := Nat.div (S planb_b_span) 2%nat.
Definition planb_b_slot : nat := S planb_b_E.
Definition planb_b_c0 : Q := (1 # 1) / (2 * planb_b_kappa)%Q.

Example planb_b_tau_pin : planb_b_tau = 2%nat.
Proof. reflexivity. Qed.

Example planb_b_sigma_pin : planb_b_sigma = 17%nat.
Proof. reflexivity. Qed.

(* C1: the span moves 14 -> 19 (sigma 12 -> 17 with tau = 2 alive). *)
Example planb_b_span_19 : planb_b_span = 19%nat.
Proof. reflexivity. Qed.

(* C2: the rate-slot exponent E = ceil(span/tau) = ceil(19/2) = 10 *)
(* (was the exact division 14/2 = 7 - the 7 -> 10 replacement).    *)
Example planb_b_E_10 : planb_b_E = 10%nat.
Proof. reflexivity. Qed.

Example planb_b_E_is_ceil_span :
  planb_b_E = Nat.div (planb_b_span + 1) 2%nat.
Proof. reflexivity. Qed.

(* the slot moves 8 -> 11 (1 + E). *)
Example planb_b_slot_11 : planb_b_slot = 11%nat.
Proof. reflexivity. Qed.

(* kappa unchanged: 35831808 = 12^7 = 2^14 * 3^7. *)
Example planb_b_kappa_pin : planb_b_kappa = (35831808 # 1)%Q.
Proof. reflexivity. Qed.

(* The kappa power pins and the c0 decomposition ground faces live in  *)
(* the companion certificate unit (certificate-separation rule).        *)

(* The old-chain contrast faces (the e_carrier.v:62-77 pinning being    *)
(* replaced): sigma = 12, span 14, exact division 7, slot 8.            *)
Example planb_b_old_sigma : (12 + 2)%nat = 14%nat.
Proof. reflexivity. Qed.

Example planb_b_old_exp : Nat.div (12 + 2) 2 = 7%nat.
Proof. reflexivity. Qed.

Example planb_b_old_slot : (1 + Nat.div (12 + 2) 2)%nat = 8%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Section 2. Calibration anchors (KB41h 5.1 numeric faces, EXACT):   *)
(*            the reduction-closed ground faces live in the companion *)
(*            certificate unit; these Z-carried twins stay here since *)
(*            the nat-side E3 anchors below consume them.             *)
(* ================================================================== *)

(* E3 re-derivation anchors: 2^6 <= 3^14 and 2^21 <= 3^14. Z-carried   *)
(* with binary-Z numeral replacements closed by reflexivity; the nat   *)
(* forms are transported via Nat2Z.inj_le + Nat2Z.inj_pow for the      *)
(* nat-side E3 chain.                                                  *)
Example planb_b_anchor_E3_lo_z : (2 ^ 6 <= 3 ^ 14)%Z.
Proof.
  replace (2 ^ 6)%Z with 64%Z by reflexivity.
  replace (3 ^ 14)%Z with 4782969%Z by reflexivity.
  lia.
Qed.

Example planb_b_anchor_E3_mid_z : (2 ^ 21 <= 3 ^ 14)%Z.
Proof.
  replace (2 ^ 21)%Z with 2097152%Z by reflexivity.
  replace (3 ^ 14)%Z with 4782969%Z by reflexivity.
  lia.
Qed.

Example planb_b_anchor_E3_lo : (2 ^ 6 <= 3 ^ 14)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le (2 ^ 6) (3 ^ 14))).
  rewrite !Nat2Z.inj_pow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  replace (Z.of_nat 6) with 6%Z by reflexivity.
  replace (Z.of_nat 3) with 3%Z by reflexivity.
  replace (Z.of_nat 14) with 14%Z by reflexivity.
  exact planb_b_anchor_E3_lo_z.
Qed.

Example planb_b_anchor_E3_mid : (2 ^ 21 <= 3 ^ 14)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le (2 ^ 21) (3 ^ 14))).
  rewrite !Nat2Z.inj_pow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  replace (Z.of_nat 21) with 21%Z by reflexivity.
  replace (Z.of_nat 3) with 3%Z by reflexivity.
  replace (Z.of_nat 14) with 14%Z by reflexivity.
  exact planb_b_anchor_E3_mid_z.
Qed.

(* ================================================================== *)
(* Section 3. The unchanged nesc witness and the sigma = 17 escape    *)
(*            faces (E1 alive, E3_nat re-derived).                    *)
(* ================================================================== *)

(* The escape witness re-pinned locally (e_carrier.v:102-103 verbatim  *)
(* form; the (B) migration keeps the witness, KB41h 5.1).              *)
Definition planb_b_nesc (q : nat) : nat :=
  Datatypes.S (Nat.div2 (Datatypes.S (Nat.log2 q))).

Lemma planb_b_nesc_bounds : forall q : nat,
  (Nat.log2 q + 2 <= 2 * planb_b_nesc q <= Nat.log2 q + 3)%nat.
Proof.
  intros q. unfold planb_b_nesc.
  set (m := Nat.log2 q) in *.
  assert (Hd : (Datatypes.S m
                = 2 * Nat.div2 (Datatypes.S m)
                + Nat.b2n (Nat.odd (Datatypes.S m)))%nat)
    by apply Nat.div2_odd.
  assert (Hb : (Nat.b2n (Nat.odd (Datatypes.S m)) <= 1)%nat).
  { destruct (Nat.odd (Datatypes.S m)); cbn; lia. }
  lia.
Qed.

(* E1 window limb (tau = 2 alive, unchanged by the sigma move). *)
Lemma planb_b_esc_E1_nat : forall q : nat, (1 <= q)%nat ->
  (2 * q < 2 ^ (2 * planb_b_nesc q))%nat.
Proof.
  intros q Hq.
  destruct (Nat.log2_spec (2 * q)) as [_ Hlt]; [lia |].
  rewrite (Nat.log2_double q) in Hlt by lia.
  apply (Nat.lt_le_trans _ (2 ^ (Datatypes.S (Datatypes.S (Nat.log2 q))))).
  - exact Hlt.
  - apply Nat.pow_le_mono_r; [lia |].
    replace (Datatypes.S (Datatypes.S (Nat.log2 q)))%nat
      with (Nat.log2 q + 2)%nat by lia.
    apply (proj1 (planb_b_nesc_bounds q)).
Qed.

(* E3_nat re-derivation at sigma = 17 (the (B) chain:                   *)
(* 2^(sigma*tau*n) = 2^(34n) <= kappa^2 * q^(sigma+tau) =               *)
(* 2^28 * 3^14 * q^19). Chain: 2*nesc <= log2 q + 3 gives               *)
(* 34*nesc <= 17*log2 q + 51; at q >= 2 the 2^51 excess is absorbed by  *)
(* q^2 (anchor 2^21 <= 3^14); at q = 1 the witness is 1 and             *)
(* 2^34 = 2^28 * 2^6 <= 2^28 * 3^14 (anchor 2^6 <= 3^14). Isomorphic    *)
(* to e_carrier.v:133-154 at the (B) pinning.                           *)
Lemma planb_b_esc_E3_nat : forall q : nat, (1 <= q)%nat ->
  (2 ^ (34 * planb_b_nesc q) <= 2 ^ 28 * 3 ^ 14 * q ^ 19)%nat.
Proof.
  intros q Hq.
  destruct (Nat.eq_dec q 1) as [H1 | Hne].
  - (* base: q = 1, witness nesc 1 = 1 *)
    rewrite H1.
    replace (planb_b_nesc 1) with 1%nat by reflexivity.
    replace (34 * 1)%nat with (28 + 6)%nat by lia.
    rewrite Nat.pow_add_r.
    replace (1 ^ 19)%nat with 1%nat by reflexivity.
    assert (H614 : (2 ^ 6 <= 3 ^ 14)%nat) by exact planb_b_anchor_E3_lo.
    rewrite Nat.mul_1_r. apply Nat.mul_le_mono_l. exact H614.
  - (* step: q >= 2 *)
    assert (Hq2 : (2 <= q)%nat) by lia.
    destruct (Nat.log2_spec q) as [Hge _]; [lia |].
    pose proof (proj2 (planb_b_nesc_bounds q)) as Htw.
    assert (H34 : (34 * planb_b_nesc q <= 17 * Nat.log2 q + 51)%nat).
    { assert (Hz : (34 * planb_b_nesc q = 17 * (2 * planb_b_nesc q))%nat) by lia.
      rewrite Hz. lia. }
    apply (Nat.le_trans _ (2 ^ (17 * Nat.log2 q + 51))).
    + apply Nat.pow_le_mono_r; lia.
    + rewrite Nat.pow_add_r.
      replace (17 * Nat.log2 q)%nat with (Nat.log2 q * 17)%nat by lia.
      rewrite Nat.pow_mul_r.
      apply (Nat.le_trans _ (q ^ 17 * 2 ^ 51)).
      * apply Nat.mul_le_mono.
        { apply Nat.pow_le_mono_l. exact Hge. }
        { apply Nat.le_refl. }
      * assert (Hq22 : (2 * 2 <= q * q)%nat) by (apply Nat.mul_le_mono; lia).
        assert (Hkey : (2 ^ 51 <= 2 ^ 28 * 3 ^ 14 * (q * q))%nat).
        { replace 51%nat with (28 + 23)%nat by lia.
          rewrite Nat.pow_add_r.
          replace 23%nat with (21 + 2)%nat by lia.
          rewrite Nat.pow_add_r.
          replace (2 ^ 2)%nat with 4%nat by reflexivity.
          assert (Hstep1 : (2 ^ 21 * 4 <= 3 ^ 14 * 4)%nat)
            by (apply Nat.mul_le_mono_r; exact planb_b_anchor_E3_mid).
          assert (Hstep2 : (3 ^ 14 * 4 <= 3 ^ 14 * (q * q))%nat)
            by (apply Nat.mul_le_mono_l; exact Hq22).
          apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * 4))).
          { apply Nat.mul_le_mono_l. exact Hstep1. }
          apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (q * q)))).
          { apply Nat.mul_le_mono_l. exact Hstep2. }
          rewrite Nat.mul_assoc. apply Nat.le_refl. }
        replace (q ^ 19)%nat with (q ^ 2 * q ^ 17)%nat
          by (rewrite <- (Nat.pow_add_r q 2 17); f_equal; lia).
        assert (Hrq : (q ^ 17 * (2 ^ 28 * 3 ^ 14 * (q * q))
                       = 2 ^ 28 * 3 ^ 14 * (q ^ 2 * q ^ 17))%nat).
        { (* explicit comm/assoc reorder: nat ring with big literal powers
             explodes (fail-loud shot 16/17 record) - lemma-chain only. *)
          replace (q ^ 2)%nat with (q * q)%nat
            by (change (q ^ 2)%nat with (q ^ (1 + 1))%nat;
                rewrite Nat.pow_add_r; rewrite !Nat.pow_1_r; reflexivity).
          rewrite Nat.mul_assoc.
          rewrite (Nat.mul_comm (q ^ 17) (2 ^ 28 * 3 ^ 14)).
          rewrite <- Nat.mul_assoc.
          rewrite (Nat.mul_comm (q ^ 17) (q * q)).
          reflexivity. }
        apply (Nat.le_trans _ (q ^ 17 * (2 ^ 28 * 3 ^ 14 * (q * q)))).
        { apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hkey]. }
        rewrite Hrq. apply Nat.le_refl.
Qed.

(* ================================================================== *)
(* Section 4. The Hcage ZERO-TOUCH consumption face: the five         *)
(*            premises explicit, the cage absent.                     *)
(* ================================================================== *)

(* The (B) value-slot: Hval DIRECT (the cage-derived ec_hval of        *)
(* e_carrier.v:653-679 is replaced by an explicit premise - this is    *)
(* the whole of the zero-touch semantics: no (3/20)^n cage premise     *)
(* exists anywhere in the (B) consumption bundle).                     *)
Definition planb_b_hval_direct (A B : nat -> Z) (dval : Z -> Z -> Q) : Set :=
  forall n : nat,
    piu_mu_QleT (dval (A n) (B n) * piu_mu_epos (2 * n)) (1 # 1)%Q.

(* the coefficient-growth slot at sigma = 17 (e_carrier.v:627-630      *)
(* isomorph with the pin moved 12 -> 17).                              *)
Definition planb_b_hcoef17 (A B : nat -> Z) : Set :=
  forall n : nat,
    piu_mu_and2
      (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (17 * n))%Z)
      (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (17 * n))%Z).

(* the escape slot at (sigma, tau) = (17, 2) (e_carrier.v:633-642      *)
(* isomorph: 2q <= 2^(2n), the nonvanishing limb verbatim,             *)
(* 2^(34n) <= kappa^2 * q^19).                                         *)
Definition planb_b_hesc17 (A B : nat -> Z) (dval : Z -> Z -> Q) : Set :=
  forall (p : Z) (q : nat), (1 <= q)%nat ->
    sigT (fun n : nat => piu_mu_and3
      (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)))
      (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
      (piu_mu_QleT (Qpower (piu_mu_epos (17 * n)) (Z.of_nat 2))
        (Qpower (35831808 # 1)%Q (Z.of_nat 2)
         * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q)).

(* THE ZERO-TOUCH FACE: the five-premise criterion closes to MuBound   *)
(* at the (B) pins with Hp/Hcoef17/Hval-direct/Htri/Hesc17 all         *)
(* explicit. The cage premise is bypassed wholesale - the conclusion   *)
(* is the same MuBound shape the old chain reached THROUGH the cage,   *)
(* here reached without it (the KB41m 6.2 (B) equivalence face).       *)
Theorem planb_b_mubound_zerotouch :
  forall (A B : nat -> Z) (dval : Z -> Z -> Q),
  (forall a b : Z, piu_mu_QleT 0 (dval a b)) ->
  planb_b_hcoef17 A B ->
  planb_b_hval_direct A B dval ->
  (forall (a b p : Z) (q : nat), (1 <= q)%nat ->
    piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
      ((inject_Z (Z.of_nat q) * dval a b
        + inject_Z (Z.abs b) * dval (- p)%Z (Z.of_nat q))%Q)) ->
  planb_b_hesc17 A B dval ->
  piu_mu_MuBound 17%nat 2%nat dval (35831808 # 1)%Q (1 # 2)%Q.
Proof.
  intros A B dval Hp Hc Hv Ht He.
  apply (piu_mu_criterion 17%nat 2%nat dval A B (35831808 # 1)%Q).
  - apply piu_mu_NleT_i. lia.
  - apply piu_mu_QltT_i. unfold Qlt. cbn. lia.
  - exact Hp.
  - exact Hc.
  - exact Hv.
  - exact Ht.
  - exact He.
Qed.

(* ================================================================== *)
(* Section 5. Module documentation: performance / effectiveness lines *)
(*            (4d extraction-ladder preparation).                     *)
(* ================================================================== *)

(* PERFORMANCE: the unit pulls only stdlib + S02_CauchyComplete +
   piu_mu_criterion plus its certificate companion; single-lane compile,
   no real-layer closure (the (B) pins are re-pinned locally, the
   nescD.v:57-63 precedent). The reduction-closed numeric ground faces
   live in the certificate unit with binary-Z operands at most 2^34 ~
   1.7e10; the E3 re-derivation is a pure nat lemma chain (pow_le_mono /
   mul_le_mono), no solver runs on powers; the square-root dance (now in
   the certificate unit) is proof-term-only. Expected compile cost: well
   under one cpu_guard_v3 shot budget.

   EFFECTIVENESS: planb_b_rate_c0_E10 (certificate unit) is the
   exponent-10 first-power face feeding planb_b_rate_dist_slot11, the
   (B)-migrated counterpart of the ck_alpha c0 8 q height-form slot
   (e_carrier.v:684); every downstream consumer replaces its 8-slot
   instantiations by 11. planb_b_esc_E3_nat is the sigma = 17 E3 face
   consumed by the Hesc17 premise discharge; with planb_b_esc_E1_nat
   (tau = 2 alive) it is the escape-supply anchor of the (B) chain.
   planb_b_mubound_zerotouch is the cage-free consumption face: the 4d
   extraction ladder never traverses the falsified (3/20)^n cage (KB41m
   5.3 NEGATIVE), because no cage premise exists in the bundle; the Hval
   slot enters as a direct premise (the ec_hval replacement).
   Statement-face audit: all conclusion faces are informative-sorted
   (QleT'/QleT/ZleT/and2/and3/sigT); the only Prop occurrences are
   inside proof bodies (path-A compliant; no proof-only bridge is
   exported, so no proof-bridge registry entry arises from this unit). *)

(* ================================================================== *)
(* Section 6. Assumption audit.                                       *)
(* ================================================================== *)

(* The rate-dance and bridge faces are audited in the certificate unit. *)

Print Assumptions planb_b_esc_E1_nat.
Print Assumptions planb_b_esc_E3_nat.
Print Assumptions planb_b_mubound_zerotouch.
Print Assumptions planb_b_nesc_bounds.
