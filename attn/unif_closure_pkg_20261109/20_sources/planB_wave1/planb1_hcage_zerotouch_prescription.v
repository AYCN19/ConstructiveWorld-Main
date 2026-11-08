(* ========================================================================= *)
(* Mission      : planB wave-1 piece (1/3) - the Hcage ZERO-TOUCH            *)
(*                prescription piece: in-tree internalization of the KB41m   *)
(*                6.2 (B)-branch prescription (true locus: receipt-KB41m-    *)
(*                beta0-presurvey-20261028.md:88-90 + receipt-KB41h-        *)
(*                chufang-yukan-20261028.md 3.0/3.1/3.2/4/5; the ask-       *)
(*                cited docs/04 file does NOT carry the prescription -      *)
(*                census registered out-of-file per the provenance rule).   *)
(*                Core steps cast one by one: (a) the exponent-chain pin    *)
(*                sigma 12 -> 17 with tau = 2 alive, span 14 -> 19,         *)
(*                rate-slot exponent E = ceil(19/2) = 10 (was 7), slot      *)
(*                1 + E = 11 (was 8), kappa and c0 unchanged; (b) the       *)
(*                E3_nat re-derivation at sigma = 17 over the unchanged     *)
(*                nesc witness (2^(34n) <= kappa^2 * q^19 chain); (c) the   *)
(*                square-root dance re-cast at the E = 10 exponent (the     *)
(*                7 -> 10 replacement, isomorphic to e_carrier.v:469-527);  *)
(*                (d) the abstract slot-11 distance face (the 8 -> 11       *)
(*                mechanical-migration core); (e) the Hcage ZERO-TOUCH      *)
(*                semantics: the five-premise criterion is consumed with    *)
(*                Hval supplied DIRECTLY as an explicit premise, so the     *)
(*                cage premise is bypassed wholesale - the equivalent       *)
(*                conclusion face of the old chain with the falsified       *)
(*                (3/20)^n cage (KB41m 5.3, x3.655 at n=5) never entered.   *)
(*                Module documentation with performance / effectiveness     *)
(*                lines is Section 7 (4d extraction-ladder preparation).    *)
(* Dependencies : S02_CauchyComplete (QleT'/QeqT), piu_mu_criterion         *)
(*                (piu_mu_QleT/ZleT/and2/and3/epos/MuBound + the five-      *)
(*                premise criterion + piu_mu_Qinv_nonneg), stdlib QArith,   *)
(*                ZArith, Arith, Lia, Qpower. One-way layering: no          *)
(*                e_carrier, no bridge_real, no real-layer units - the (B)  *)
(*                pins are re-pinned locally (nescD.v:57-63 precedent).     *)
(* References   : KB41m 6.2 (B) redirect + 5.3 NEGATIVE (the (3/20)^n cage  *)
(*                EXACT-falsified at n=5, |R5|_hi > (3/20)^5 x 3.655);      *)
(*                KB41h 5.2 (B)-row (rate_c0 exponent 7 -> 10, E3_nat       *)
(*                re-derivation, slot 8 -> 11, ~35-line mechanical face)    *)
(*                and 5.1 (E3_nat sigma=17 chain 2^34 <= kappa^2 q^19);     *)
(*                e_carrier.v:54-94 (old pinning + span/div/slot faces),    *)
(*                :105-154 (nesc bounds + E1/E3), :466-527 (the square-    *)
(*                root dance), :613-650 (Section EC premises), :653-679    *)
(*                (ec_hval - the cage-derived value face the (B) chain      *)
(*                replaces by a direct premise); nescD.v (witness + Q       *)
(*                bridges; this file copies its inject/pow_pos shapes);     *)
(*                bracket.v:164-175 (slope certificate, q=1 anchor).        *)
(* Constructivity: every named statement is Set-carried (piu_mu_QleT/ZleT/ *)
(*                and2/and3, sigT, S02 QleT'); propositional reasoning only *)
(*                inside proofs; definitions transparent; no Axiom, no      *)
(*                Parameter, no Admitted, no Abort; every named statement   *)
(*                closes under the global context. Path-A: zero new-cast    *)
(*                Prop surface; information-bit faces are informative-      *)
(*                sorted (QleT'/QleT/ZleT/sigT forms).                      *)
(* Build        : coqc -native-compiler no -q -Q . "" -Q <green9 cache> ""  *)
(*                planb1_hcage_zerotouch_prescription.v, Rocq 9.3.0, serial *)
(*                single lane under cpu_guard_v3 (-TempLimit 98 -AllowG3),  *)
(*                shot spacing >= 120 s; coqchk MUST carry                  *)
(*                -bytecode-compiler yes.                                   *)
(* ========================================================================= *)

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

Example planb_b_kappa_pow12 : (12 ^ 7 = 35831808)%Z.
Proof. vm_compute; reflexivity. Qed.

Example planb_b_kappa_decomp : (2 ^ 14 * 3 ^ 7 = 35831808)%Z.
Proof. vm_compute; reflexivity. Qed.

(* c0 unchanged: c0 = 1/(2*kappa) = 1/71663616 (the bridge_real:63      *)
(* decomposition re-check, EXACT).                                      *)
Example planb_b_c0_bool :
  Qeq_bool planb_b_c0 (1 # 71663616)%Q = true.
Proof. vm_compute; reflexivity. Qed.

Example planb_b_c0_half_kappa_inv :
  Qeq_bool planb_b_c0 ((1 # 2) / planb_b_kappa)%Q = true.
Proof. vm_compute; reflexivity. Qed.

(* The old-chain contrast faces (the e_carrier.v:62-77 pinning being    *)
(* replaced): sigma = 12, span 14, exact division 7, slot 8.            *)
Example planb_b_old_sigma : (12 + 2)%nat = 14%nat.
Proof. reflexivity. Qed.

Example planb_b_old_exp : Nat.div (12 + 2) 2 = 7%nat.
Proof. reflexivity. Qed.

Example planb_b_old_slot : (1 + Nat.div (12 + 2) 2)%nat = 8%nat.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Section 2. Calibration anchors (KB41h 5.1 numeric faces, EXACT).   *)
(* ================================================================== *)

(* (D)-calibration pair: the slope certificate and its minimality twin. *)
(* Z-carried (binary) exactly as the bracket.v:164 slope-certificate    *)
(* precedent - the unary-nat vm_compute of 20^7 overflows the stack     *)
(* (fail-loud shot 6 record); the integer comparison IS the anchor.     *)
Example planb_b_anchor_A1 : (2 ^ 17 * 3 ^ 7 <= 20 ^ 7)%Z.
Proof. vm_compute; discriminate. Qed.

Example planb_b_anchor_A2_min : (20 ^ 6 < 2 ^ 17 * 3 ^ 6)%Z.
Proof. vm_compute; reflexivity. Qed.

(* (B) q = 1 anchors: 2^34 <= kappa^2 and 2^17 <= kappa. *)
Example planb_b_anchor_kappa_sq :
  (35831808 * 35831808 = 1283918464548864)%Z.
Proof. vm_compute; reflexivity. Qed.

Example planb_b_anchor_C3 : (2 ^ 34 <= 35831808 * 35831808)%Z.
Proof. vm_compute; discriminate. Qed.

Example planb_b_anchor_C4 : (2 ^ 17 <= 35831808)%Z.
Proof. vm_compute; discriminate. Qed.

(* the q = 1 double-limb anchor: 2*1*3 <= 20 (small nat, unary-safe). *)
Example planb_b_anchor_D1 : (2 * 1 * 3 <= 20)%nat.
Proof. vm_compute; lia. Qed.

(* E3 re-derivation anchors: 2^6 <= 3^14 and 2^21 <= 3^14. Z-carried   *)
(* EXACT, with the nat forms transported back via Nat2Z.inj_le for the *)
(* nat-side E3 chain.                                                  *)
Example planb_b_anchor_E3_lo_z : (2 ^ 6 <= 3 ^ 14)%Z.
Proof. vm_compute; discriminate. Qed.

Example planb_b_anchor_E3_mid_z : (2 ^ 21 <= 3 ^ 14)%Z.
Proof. vm_compute; discriminate. Qed.

Example planb_b_anchor_E3_lo : (2 ^ 6 <= 3 ^ 14)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le (2 ^ 6) (3 ^ 14))).
  vm_compute; discriminate.
Qed.

Example planb_b_anchor_E3_mid : (2 ^ 21 <= 3 ^ 14)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le (2 ^ 21) (3 ^ 14))).
  vm_compute; discriminate.
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
    replace (planb_b_nesc 1) with 1%nat by (vm_compute; reflexivity).
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
(* Section 4. Local Q bridges (nescD.v shapes re-pinned; the one-way- *)
(*            layering price of not pulling the escwin unit).         *)
(* ================================================================== *)

Lemma planb_b_pow_pos_lt : forall (x : Q) (n : nat),
  (0 < x)%Q -> (0 < Qpower x (Z.of_nat n))%Q.
Proof.
  intros x n Hx. induction n as [|n IH].
  - cbn [Z.of_nat]. rewrite Qpower_0_r. unfold Qlt. cbn. lia.
  - assert (Hne : ~ (x == 0)%Q).
    { intro Hc. unfold Qeq in Hc. cbn in Hc. unfold Qlt in Hx. cbn in Hx. lia. }
    assert (Hs : (Z.of_nat (Datatypes.S n) = Z.of_nat n + 1)%Z) by lia.
    rewrite Hs.
    rewrite (Qpower_plus x (Z.of_nat n) (Z.of_nat 1) Hne).
    replace (Qpower x 1) with x by reflexivity.
    rewrite Qmult_comm.
    exact (Qmult_lt_0_compat _ _ Hx IH).
Qed.

Lemma planb_b_qpow2_mul : forall x : Q, ~ (x == 0)%Q ->
  Qpower x (Z.of_nat 2) == x * x.
Proof.
  intros x Hne.
  replace (Z.of_nat 2) with (Z.of_nat 1 + Z.of_nat 1)%Z by reflexivity.
  rewrite (Qpower_plus x (Z.of_nat 1) (Z.of_nat 1) Hne).
  rewrite Qpower_1_r. reflexivity.
Qed.

(* left-multiplied monotonicity is not a stdlib Q lemma: the right-     *)
(* multiplied forms commute into it (smoke_api_probe pin).              *)
Lemma planb_b_qmult_le_compat_l : forall x y z : Q,
  (x <= y)%Q -> (0 <= z)%Q -> (z * x <= z * y)%Q.
Proof.
  intros x y z H1 H2.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_le_compat_r; assumption.
Qed.

(* inverse nonnegativity (the piu_mu_criterion face, QleT form read out *)
(* to plain Qle; e_carrier.v:413-424 isomorph kept local).              *)
Lemma planb_b_qinv_nneg : forall y : Q, (0 < y)%Q -> (0 <= / y)%Q.
Proof.
  intros y Hy. destruct (piu_mu_Qinv_nonneg y Hy) as [H]. exact H.
Qed.

(* left-multiplied strict monotonicity (comm + the right-multiplied
   stdlib form; Qmult_lt_compat_l does not exist in this stdlib). *)
Lemma planb_b_qmult_lt_compat_l : forall x y z : Q,
  (0 < z)%Q -> (x < y)%Q -> (z * x < z * y)%Q.
Proof.
  intros x y z H1 H2.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply Qmult_lt_compat_r; assumption.
Qed.

(* order-reflecting squares on the positive domain (the dance engine). *)
Lemma planb_b_qsq_ord_reflect : forall x y : Q,
  (0 < x)%Q -> (0 < y)%Q -> (x * x <= y * y)%Q -> (x <= y)%Q.
Proof.
  intros x y Hx Hy Hsq.
  destruct (Qlt_le_dec y x) as [Hyx | Hle].
  - exfalso.
    assert (H1 : (y * y < y * x)%Q)
      by (apply planb_b_qmult_lt_compat_l; [exact Hy | exact Hyx]).
    assert (H2 : (y * x < x * x)%Q) by (apply Qmult_lt_compat_r; assumption).
    assert (H3 : (y * y < x * x)%Q) by (apply (Qlt_trans _ (y * x)); assumption).
    exact (Qlt_irrefl (y * y) (Qlt_le_trans _ _ _ H3 Hsq)).
  - exact Hle.
Qed.

(* ================================================================== *)
(* Section 5. The rate-slot dance re-cast at E = 10 (the exponent     *)
(*            7 -> 10 replacement) and the abstract slot-11 face.     *)
(* ================================================================== *)

(* The (B) first-power rate face: MuBound at (sigma, tau) = (17, 2)     *)
(* unwinds to c0 <= dval * q^10 (e_carrier.v:469-527 isomorph with the  *)
(* half-integer span absorbed by bQ <= bQ^2 inside the square).         *)
Lemma planb_b_rate_c0_E10 :
  forall (dval : Z -> Z -> Q) (p0 : Z) (q0 : nat),
  (1 <= q0)%nat -> (0 <= dval (Z.of_nat q0) (- p0)%Z)%Q ->
  piu_mu_MuBound 17%nat 2%nat dval (35831808 # 1)%Q (1 # 2)%Q ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * (35831808 # 1))%Q)
    (dval (Z.of_nat q0) (- p0)%Z
     * Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 10))%Q.
Proof.
  intros dval p0 q0 Hq0 Hnn Hmb.
  pose proof (Hmb p0 q0 Hq0) as Hm0. destruct Hm0 as [Hm0].
  remember (dval (Z.of_nat q0) (- p0)%Z) as W eqn:HW in *.
  remember (inject_Z (Z.of_nat q0)) as bQ eqn:HQb in *.
  remember (35831808 # 1)%Q as kq eqn:HKq in *.
  assert (Hbne : ~ (bQ == 0)%Q).
  { rewrite HQb. intro Hc. unfold inject_Z, Qeq in Hc. cbn [Qnum Qden] in Hc.
    lia. }
  assert (Hbpos : (0 < bQ)%Q).
  { rewrite HQb. unfold inject_Z, Qlt. cbn. lia. }
  assert (Hbge : (1 <= bQ)%Q).
  { rewrite HQb. unfold inject_Z, Qle. cbn. lia. }
  assert (HWne : ~ (W == 0)%Q).
  { intro Hc. rewrite Hc in Hm0.
    assert (Hz : Qpower 0%Q (Z.of_nat 2) == 0%Q) by reflexivity.
    rewrite Hz in Hm0. rewrite Qmult_0_r in Hm0. rewrite Qmult_0_l in Hm0.
    unfold Qle in Hm0. cbn in Hm0. lia. }
  assert (HWpos : (0 < W)%Q).
  { destruct (Qlt_le_dec 0 W) as [HL | HR]; [exact HL | exfalso].
    apply HWne. apply Qle_antisym; [exact HR | exact Hnn]. }
  assert (Hne12 : ~ ((1 # 2) == 0)%Q) by (unfold Qeq; cbn; lia).
  assert (HneK : ~ (kq == 0)%Q).
  { rewrite HKq. unfold Qeq. cbn. lia. }
  assert (HB9ne : ~ (Qpower bQ (Z.of_nat 9) == 0)%Q).
  { pose proof (planb_b_pow_pos_lt bQ 9 Hbpos) as HP.
    intro Hc. rewrite Hc in HP. unfold Qlt in HP. cbn in HP. lia. }
  (* bQ^18 = (bQ^9)^2 and bQ^19 = bQ^18 * bQ *)
  assert (H18 : Qpower bQ (Z.of_nat 18)
                == Qpower (Qpower bQ (Z.of_nat 9)) (Z.of_nat 2)).
  { replace (Z.of_nat 18) with (Z.of_nat 9 + Z.of_nat 9)%Z by reflexivity.
    rewrite (Qpower_plus bQ (Z.of_nat 9) (Z.of_nat 9) Hbne).
    rewrite <- (planb_b_qpow2_mul (Qpower bQ (Z.of_nat 9)) HB9ne).
    reflexivity. }
  assert (H19split : Qpower bQ (Z.of_nat (17 + 2))
                     == Qpower bQ (Z.of_nat 18) * bQ).
  { replace (Z.of_nat (17 + 2)) with (Z.of_nat 18 + 1)%Z by reflexivity.
    rewrite (Qpower_plus bQ (Z.of_nat 18) (Z.of_nat 1) Hbne).
    rewrite Qpower_1_r. reflexivity. }
  (* unpack the squares into multiplied form *)
  rewrite (planb_b_qpow2_mul (1 # 2)%Q Hne12) in Hm0.
  rewrite (planb_b_qpow2_mul kq HneK) in Hm0.
  rewrite (planb_b_qpow2_mul W HWne) in Hm0.
  rewrite H19split, H18 in Hm0.
  rewrite (planb_b_qpow2_mul (Qpower bQ (Z.of_nat 9)) HB9ne) in Hm0.
  (* Hm0 : (1/2)*(1/2) <= kq*kq*(W*W)*((bQ9*bQ9)*bQ)                    *)
  (* pack: = (kq*W*bQ9) * (kq*W*bQ9) * bQ = Y*Y*bQ                      *)
  (* (Q ring proves Qeq, not Eq - the replace side-goal is Eq, so the   *)
  (* reorders are carried as Qeq asserts + setoid rewrites.)            *)
  assert (Hpack : (kq * kq * (W * W)
                   * (Qpower bQ (Z.of_nat 9) * Qpower bQ (Z.of_nat 9) * bQ))%Q
                  == (kq * W * Qpower bQ (Z.of_nat 9)
                      * (kq * W * Qpower bQ (Z.of_nat 9)) * bQ)%Q)
    by ring.
  rewrite Hpack in Hm0.
  assert (HYpos : (0 < kq * W * Qpower bQ (Z.of_nat 9))%Q).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; [rewrite HKq; unfold Qlt; cbn; lia | exact HWpos].
    - apply (planb_b_pow_pos_lt bQ 9 Hbpos). }
  assert (Hbgrow : (bQ <= bQ * bQ)%Q).
  { pose proof (planb_b_qmult_le_compat_l (1 # 1)%Q bQ bQ Hbge
                  ltac:(rewrite HQb; unfold inject_Z, Qle; cbn; lia)) as Hb0.
    rewrite Qmult_1_r in Hb0. exact Hb0. }
  (* grow the lone bQ into the square: Y*Y*bQ <= Y*Y*(bQ*bQ) = (Y*bQ)^2 *)
  assert (Hgrow2 : ((kq * W * Qpower bQ (Z.of_nat 9))
                    * (kq * W * Qpower bQ (Z.of_nat 9)) * bQ
                    <= (kq * W * Qpower bQ (Z.of_nat 9))
                       * (kq * W * Qpower bQ (Z.of_nat 9))
                       * (bQ * bQ))%Q).
  { apply planb_b_qmult_le_compat_l.
    - exact Hbgrow.
    - apply Qmult_le_0_compat.
      + apply Qmult_le_0_compat.
        * apply Qmult_le_0_compat.
          { rewrite HKq; unfold Qle; cbn; lia. }
          { apply Qlt_le_weak. exact HWpos. }
        * apply Qlt_le_weak. apply (planb_b_pow_pos_lt bQ 9 Hbpos).
      + apply Qmult_le_0_compat.
        * apply Qmult_le_0_compat.
          { rewrite HKq; unfold Qle; cbn; lia. }
          { apply Qlt_le_weak. exact HWpos. }
        * apply Qlt_le_weak. apply (planb_b_pow_pos_lt bQ 9 Hbpos). }
  assert (Hrepack : ((kq * W * Qpower bQ (Z.of_nat 9))
                     * (kq * W * Qpower bQ (Z.of_nat 9)) * (bQ * bQ))%Q
                    == ((kq * W * Qpower bQ (Z.of_nat 9) * bQ)
                        * (kq * W * Qpower bQ (Z.of_nat 9) * bQ))%Q)
    by ring.
  rewrite Hrepack in Hgrow2.
  assert (Hsq : ((1 # 2) * (1 # 2)
                 <= (kq * W * Qpower bQ (Z.of_nat 9) * bQ)
                    * (kq * W * Qpower bQ (Z.of_nat 9) * bQ))%Q).
  { apply (Qle_trans _ ((kq * W * Qpower bQ (Z.of_nat 9))
                        * (kq * W * Qpower bQ (Z.of_nat 9)) * bQ)).
    - exact Hm0.
    - exact Hgrow2. }
  assert (Hhalf : ((1 # 2)
                   <= kq * W * Qpower bQ (Z.of_nat 9) * bQ)%Q).
  { apply (planb_b_qsq_ord_reflect (1 # 2)%Q
             (kq * W * Qpower bQ (Z.of_nat 9) * bQ)).
    - unfold Qlt. cbn. lia.
    - apply Qmult_lt_0_compat.
      + exact HYpos.
      + rewrite HQb. unfold inject_Z, Qlt. cbn. lia.
    - exact Hsq. }
  (* bridge to the exponent-10 face: Y*bQ = kq*W*bQ^10 *)
  assert (HB10 : Qpower bQ (Z.of_nat 10) == Qpower bQ (Z.of_nat 9) * bQ).
  { replace (Z.of_nat 10) with (Z.of_nat 9 + 1)%Z by reflexivity.
    rewrite (Qpower_plus bQ (Z.of_nat 9) (Z.of_nat 1) Hbne).
    rewrite Qpower_1_r. reflexivity. }
  assert (HhalfK : ((1 # 2)
                    <= kq * W * Qpower bQ (Z.of_nat 10))%Q).
  { rewrite HB10.
    assert (Hbr : (kq * W * (Qpower bQ (Z.of_nat 9) * bQ))%Q
                  == (kq * W * Qpower bQ (Z.of_nat 9) * bQ)%Q)
      by ring.
    rewrite Hbr. exact Hhalf. }
  (* cancel kappa: c0 = (1/2)/kq <= W * bQ^10 *)
  apply S02_CauchyComplete.Qle_to_QleT'.
  assert (Hc0split : ((1 # 1) / (2 * kq)%Q
                      == (1 # 2) * / kq)%Q).
  { rewrite HKq. unfold Qdiv, Qmult; cbn; ring. }
  rewrite Hc0split.
  apply (Qle_trans _ ((W * Qpower bQ (Z.of_nat 10)) * kq * / kq)%Q).
  - apply Qmult_le_compat_r.
    + rewrite (Qmult_comm (W * Qpower bQ (Z.of_nat 10)) kq).
      assert (Has1 : (kq * (W * Qpower bQ (Z.of_nat 10)))%Q
                     == (kq * W * Qpower bQ (Z.of_nat 10))%Q)
        by ring.
      rewrite Has1. exact HhalfK.
    + exact (planb_b_qinv_nneg kq ltac:(rewrite HKq; unfold Qlt; cbn; lia)).
  - rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r kq HneK).
    rewrite Qmult_1_r. apply Qle_refl.
Qed.

(* The abstract slot-11 distance face: the first-power face at exponent *)
(* 10 plus the mirror premise yields the point distance bound           *)
(* c0 / q^11 <= |xk - r| (the piu_zz_ec_rate_dist isomorph with the     *)
(* 7 -> 10 and 8 -> 11 replacements; the point xk is an abstract Q so   *)
(* the face stays out of the real-layer dependency closure).            *)
Lemma planb_b_rate_dist_slot11 :
  forall (dval : Z -> Z -> Q) (r xk : Q) (p0 : Z) (q0 : nat),
  S02_CauchyComplete.QeqT (inject_Z (Z.of_nat q0) * r) (inject_Z p0) ->
  (1 <= q0)%nat ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * (35831808 # 1))%Q)
    (dval (Z.of_nat q0) (- p0)%Z
     * Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 10))%Q ->
  S02_CauchyComplete.QleT' (dval (Z.of_nat q0) (- p0)%Z)
    (Qabs (inject_Z (Z.of_nat q0) * xk - inject_Z p0)) ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * (35831808 # 1))%Q
      / Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 11))%Q
    (Qabs (xk - r)).
Proof.
  intros dval r xk p0 q0 Hred Hq0 Hc0 Hx.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hc0) as H1.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hx) as H2.
  remember (dval (Z.of_nat q0) (- p0)%Z) as W eqn:HW in *.
  remember (inject_Z (Z.of_nat q0)) as bQ eqn:HQb in *.
  remember (Qpower bQ (Z.of_nat 10)) as B10 eqn:HQ10 in *.
  remember (Qpower bQ (Z.of_nat 11)) as B11 eqn:HQ11 in *.
  assert (Hbpos : (0 < bQ)%Q).
  { rewrite HQb. unfold inject_Z, Qlt. cbn. lia. }
  assert (HB10pos : (0 < B10)%Q)
    by (rewrite HQ10; apply (planb_b_pow_pos_lt bQ 10 Hbpos)).
  assert (HB11pos : (0 < B11)%Q)
    by (rewrite HQ11; apply (planb_b_pow_pos_lt bQ 11 Hbpos)).
  assert (HB11eq : (B11 == bQ * B10)%Q).
  { rewrite HQ11, HQ10.
    replace (Z.of_nat 11)%Z with (Z.of_nat 1 + Z.of_nat 10)%Z by reflexivity.
    rewrite (Qpower_plus bQ (Z.of_nat 1) (Z.of_nat 10)
               ltac:(intro Hc; exfalso; rewrite HQb in Hc;
                     unfold inject_Z, Qeq in Hc; cbn in Hc; lia)).
    rewrite Qpower_1_r. reflexivity. }
  assert (Habs : (Qabs (bQ * xk - inject_Z p0) == bQ * Qabs (xk - r))%Q).
  { rewrite <- (qeqT_imp_qeq _ _ Hred).
    assert (Hsp : (bQ * xk - bQ * r == bQ * (xk - r))%Q) by ring.
    rewrite Hsp, Qabs_Qmult, (Qabs_pos bQ (Qlt_le_weak 0 bQ Hbpos)).
    reflexivity. }
  assert (H3 : ((1 # 1) / (2 * (35831808 # 1))%Q <= Qabs (xk - r) * B11)%Q).
  { apply (Qle_trans _ (W * B10)).
    - exact H1.
    - apply (Qle_trans _ (Qabs (bQ * xk - inject_Z p0) * B10)).
      + apply Qmult_le_compat_r; [exact H2 | apply Qlt_le_weak; exact HB10pos].
      + rewrite Habs, (Qmult_comm bQ (Qabs (xk - r))), <- Qmult_assoc,
          <- HB11eq.
        apply Qle_refl. }
  apply S02_CauchyComplete.Qle_to_QleT'. unfold Qdiv.
  apply (Qle_trans _ (Qabs (xk - r) * B11 * / B11)).
  - apply Qmult_le_compat_r; [exact H3 | apply (planb_b_qinv_nneg B11 HB11pos)].
  - rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r
      by (intro Hc; exfalso; unfold Qeq in Hc; cbn in Hc;
          unfold Qlt in HB11pos; cbn in HB11pos; lia).
    rewrite Qmult_1_r. apply Qle_refl.
Qed.

(* ================================================================== *)
(* Section 6. The Hcage ZERO-TOUCH consumption face: the five         *)
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
        + inject_Z (Z.abs b) * dval (Z.of_nat q) (- p)%Z)%Q)) ->
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
(* Section 7. Module documentation: performance / effectiveness lines *)
(*            (4d extraction-ladder preparation).                     *)
(* ================================================================== *)

(* PERFORMANCE LINES -------------------------------------------------
   - Zero heavy Requires: this unit pulls only stdlib + S02_CauchyComplete
     + piu_mu_criterion. Single-file compile; no real-layer, no
     bridge_real/poincare/mu_assembly closure is loaded (the (B) pins are
     re-pinned locally, the nescD.v:57-63 precedent).
   - Every numeric anchor is a vm_compute-closed ground face; the largest
     vm_compute operands in this file are 2^34 ~ 1.7e10 and 3^14 ~ 4.8e6
     (sub-millisecond on the reference box).
   - The E3 re-derivation and the slot-11 merge are pure nat/Q lemma
     chains (pow_le_mono / mul_le_mono / Qmult compat); no solver runs on
     powers; the square-root dance is proof-term-only.
   - Expected compile cost: well under one cpu_guard_v3 shot budget.

   EFFECTIVENESS LINES (4d extraction-ladder preparation) ------------
   - planb_b_rate_c0_E10 is the exponent-10 first-power face; it feeds
     planb_b_rate_dist_slot11, the (B)-migrated counterpart of the
     ck_alpha c0 8 q height-form slot (e_carrier.v:684). The 4d ladder's
     rate-slot consumption point is therefore the slot-11 face: every
     downstream consumer replaces its 8-slot instantiations by 11.
   - planb_b_esc_E3_nat is the sigma = 17 E3 face consumed by the Hesc17
     premise discharge in the bridge_rateslot migration (the KB41h 4.1
     measured 20-line face); together with planb_b_esc_E1_nat (tau = 2
     alive) it is the escape-supply anchor of the (B) chain.
   - planb_b_mubound_zerotouch is the Hcage-free consumption face: the
     4d extraction ladder never traverses the falsified (3/20)^n cage
     (KB41m 5.3 NEGATIVE), because no cage premise exists in the bundle;
     the Hval slot enters as a direct premise (the ec_hval replacement).
   - Statement-face audit: all conclusion faces are informative-sorted
     (QleT'/QleT/ZleT/and2/and3/sigT); the only Prop occurrences are
     inside proof bodies (path-A compliant; no proof-only bridge is
     exported, so no proof-bridge registry entry arises from this unit). *)

(* ================================================================== *)
(* Section 8. Assumption audit.                                       *)
(* ================================================================== *)

Print Assumptions planb_b_esc_E1_nat.
Print Assumptions planb_b_esc_E3_nat.
Print Assumptions planb_b_rate_c0_E10.
Print Assumptions planb_b_rate_dist_slot11.
Print Assumptions planb_b_mubound_zerotouch.
Print Assumptions planb_b_qsq_ord_reflect.
Print Assumptions planb_b_nesc_bounds.
Print Assumptions planb_b_qinv_nneg.
