(* ConstructiveWorld-Main - Hcage zero-touch prescription piece: (B)-branch pins, escape faces and the five-premise consumption face. *)

(* Mission. In-tree internalization of the KB41m 6.2 (B)-branch prescription:
   the exponent chain pinned at sigma = 18 with tau = 2 alive, span 20,
   rate-slot exponent E = span/tau = 10 (exact division; was ceil(19/2)
   at sigma = 17), slot 11, kappa/c0 unchanged; E3_nat re-derived at
   sigma = 18 over the lower-edge window witness planb_b_nlo
   (2^(36n) <= kappa^2 q^20; the stock nesc witness leaves the sigma = 18
   window at the lone point q = 2, measured up to q = 2^20); the
   square-root dance and the abstract slot-11 distance face (E = 10,
   slot 11, isomorphic to e_carrier.v:469-527) live in the companion
   certificate unit
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
(* Section 1. The (B) pin block: sigma 12 -> 18, tau = 2 alive,       *)
(*            E = span/tau = 10 exact, slot 11, kappa/c0 unchanged.   *)
(* ================================================================== *)

Definition planb_b_tau : nat := 2%nat.
Definition planb_b_sigma : nat := 18%nat.
Definition planb_b_kappa : Q := (35831808 # 1)%Q.
Definition planb_b_span : nat := (planb_b_sigma + planb_b_tau)%nat.
Definition planb_b_E : nat := Nat.div (S planb_b_span) 2%nat.
Definition planb_b_slot : nat := S planb_b_E.
Definition planb_b_c0 : Q := (1 # 1) / (2 * planb_b_kappa)%Q.

Example planb_b_tau_pin : planb_b_tau = 2%nat.
Proof. reflexivity. Qed.

Example planb_b_sigma_pin : planb_b_sigma = 18%nat.
Proof. reflexivity. Qed.

(* C1: the span moves 14 -> 20 (sigma 12 -> 18 with tau = 2 alive). *)
Example planb_b_span_20 : planb_b_span = 20%nat.
Proof. reflexivity. Qed.

(* C2: the rate-slot exponent E = span/tau = 20/2 = 10, exact      *)
(* division restored (at sigma = 17 the odd span 19 forced the      *)
(* ceiling ceil(19/2) = 10 with a half-integer remainder absorbed   *)
(* inside the rate dance; the 7 -> 10 replacement stands).          *)
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

(* E3 re-derivation anchors at sigma = 18: 2^8 <= 3^14 (the q = 1 base, *)
(* 36 = 28 + 8) and 2^21 <= 3^14 (the corrected-branch excess at        *)
(* m >= 2); the lone corrected point q = 3 carries its own exact anchor *)
(* below. Z-carried with binary-Z numeral replacements closed by        *)
(* reflexivity; the nat forms are transported via Nat2Z.inj_le +        *)
(* Nat2Z.inj_pow for the nat-side E3 chain.                             *)
Example planb_b_anchor_E3_lo_z : (2 ^ 8 <= 3 ^ 14)%Z.
Proof.
  replace (2 ^ 8)%Z with 256%Z by reflexivity.
  replace (3 ^ 14)%Z with 4782969%Z by reflexivity.
  lia.
Qed.

Example planb_b_anchor_E3_mid_z : (2 ^ 21 <= 3 ^ 14)%Z.
Proof.
  replace (2 ^ 21)%Z with 2097152%Z by reflexivity.
  replace (3 ^ 14)%Z with 4782969%Z by reflexivity.
  lia.
Qed.

Example planb_b_anchor_E3_lo : (2 ^ 8 <= 3 ^ 14)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le (2 ^ 8) (3 ^ 14))).
  rewrite !Nat2Z.inj_pow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  replace (Z.of_nat 8) with 8%Z by reflexivity.
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

(* the lone corrected point q = 3 (the m = 1 corrected case of the nlo  *)
(* witness at sigma = 18): exact Z-carried ground face with binary-Z    *)
(* numerals (the certificate-unit (D)-calibration style); the nat form  *)
(* is transported via Nat2Z.inj_le + Nat2Z.inj_mul + Nat2Z.inj_pow.     *)
Example planb_b_anchor_E3_q3_z : (2 ^ 72 <= 2 ^ 28 * 3 ^ 14 * 3 ^ 20)%Z.
Proof. vm_compute; discriminate. Qed.

Example planb_b_anchor_E3_q3 : (2 ^ 72 <= 2 ^ 28 * 3 ^ 14 * 3 ^ 20)%nat.
Proof.
  apply (proj2 (Nat2Z.inj_le (2 ^ 72) (2 ^ 28 * 3 ^ 14 * 3 ^ 20))).
  rewrite !Nat2Z.inj_mul.
  rewrite !Nat2Z.inj_pow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  replace (Z.of_nat 72) with 72%Z by reflexivity.
  replace (Z.of_nat 28) with 28%Z by reflexivity.
  replace (Z.of_nat 14) with 14%Z by reflexivity.
  replace (Z.of_nat 3) with 3%Z by reflexivity.
  replace (Z.of_nat 20) with 20%Z by reflexivity.
  exact planb_b_anchor_E3_q3_z.
Qed.

(* ================================================================== *)
(* Section 3. The nesc and nlo window witnesses and the sigma = 18    *)
(*            escape faces (E1 alive at both witnesses, E3_nat        *)
(*            re-derived at the lower-edge witness nlo).              *)
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

(* Lower-edge window witness for the sigma = 18 escape face (the        *)
(* witness repair of the stock nesc witness, which leaves the           *)
(* sigma = 18 window at the lone point q = 2). nlo q is the minimal n   *)
(* with 2*q <= 2^(2*n): the div2 half of log2 q + 2, stepped by one     *)
(* exactly when the half falls short of the growth limb (the decidable  *)
(* nat comparison below). Measured at sigma = 18 over q <= 2^20: nlo    *)
(* meets both escape limbs everywhere on the range and equals the true  *)
(* window lower edge (n_lo) on it.                                      *)
Definition planb_b_nlo (q : nat) : nat :=
  let m := Nat.div2 (Nat.log2 q + 2) in
  if Nat.ltb (2 ^ (2 * m)) (2 * q) then S m else m.

(* the repair point: the stock nesc candidate 2 sits one above the      *)
(* sigma = 18 window at q = 2 (whose only admissible witness is 1);     *)
(* nlo 2 = 1 lands inside.                                              *)
Example planb_b_nlo_pin_q2 : planb_b_nlo 2 = 1%nat.
Proof. reflexivity. Qed.

(* the growth limb at the lower-edge witness: 2q <= 2^(2*nlo q). The    *)
(* non-strict face matches the escape-slot growth premise (QleT form);  *)
(* the strict stock face planb_b_esc_E1_nat stays for the sigma = 17    *)
(* consumption instance (kept in this unit).                            *)
Lemma planb_b_esc_E1_lo_nat : forall q : nat, (1 <= q)%nat ->
  (2 * q <= 2 ^ (2 * planb_b_nlo q))%nat.
Proof.
  intros q Hq.
  destruct (Nat.log2_spec q) as [Hge Hlt]; [lia |].
  assert (Hd : (Nat.log2 q + 2
                = 2 * Nat.div2 (Nat.log2 q + 2)
                + Nat.b2n (Nat.odd (Nat.log2 q + 2)))%nat)
    by apply Nat.div2_odd.
  assert (Hb : (Nat.b2n (Nat.odd (Nat.log2 q + 2)) <= 1)%nat).
  { destruct (Nat.odd (Nat.log2 q + 2)); cbn; lia. }
  assert (Hmlb : (Nat.log2 q + 1 <= 2 * Nat.div2 (Nat.log2 q + 2))%nat)
    by lia.
  unfold planb_b_nlo.
  destruct (Nat.ltb (2 ^ (2 * Nat.div2 (Nat.log2 q + 2))) (2 * q))
    eqn:Hc; cbn;
    remember (Nat.div2 (Nat.log2 q + 2)) as m eqn:Hmdef.
  - (* corrected branch: witness S m, with 2m >= l+1 lifting the limb *)
    assert (Hbigger : (2 ^ (Nat.log2 q + 2) <= 2 ^ (2 * S m))%nat).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hq2 : (2 * q < 2 ^ (Nat.log2 q + 2))%nat).
    { assert (Hlt1 : (q < 2 ^ (Nat.log2 q + 1))%nat).
      { replace (Nat.log2 q + 1)%nat with (S (Nat.log2 q))%nat by lia.
        exact Hlt. }
      replace (Nat.log2 q + 2)%nat with (S (Nat.log2 q + 1))%nat by lia.
      rewrite Nat.pow_succ_r'.
      lia. }
    assert (Hchain : (2 * q < 2 ^ (2 * S m))%nat).
    { apply (Nat.lt_le_trans _ (2 ^ (Nat.log2 q + 2)));
        [exact Hq2 | exact Hbigger]. }
    exact (Nat.lt_le_incl _ _ Hchain).
  - (* uncorrected branch: witness m, the ltb negation is the face *)
    exact (proj1 (Nat.ltb_ge _ _) Hc).
Qed.

(* E3_nat re-derivation at sigma = 18 (the (B) chain:                    *)
(* 2^(sigma*tau*n) = 2^(36n) <= kappa^2 * q^(sigma+tau) =                *)
(* 2^28 * 3^14 * q^20), re-derived over the lower-edge window witness    *)
(* planb_b_nlo (the stock nesc witness leaves the sigma = 18 window at   *)
(* the lone point q = 2, measured up to q = 2^20). Chain, uniform at     *)
(* q = 1: 36*nlo <= 18*log2 q + 36 gives 2^(36*nlo) <= q^18 * 2^36 with  *)
(* 36 = 28 + 8 covered by the anchor 2^8 <= 3^14 (the q = 1 base). In    *)
(* the corrected branch at m = div2 (log2 q + 2) >= 2 the split re-forms:*)
(* 2^(2m-1) < q puts (2^(2m-1))^20 inside q^20 and 36*(m+1) <=           *)
(* 20*(2m-1) + 49 with 49 = 28 + 21 covered by the anchor 2^21 <= 3^14.  *)
(* The lone corrected point with m = 1 is q = 3, carried by the exact    *)
(* anchor 2^72 <= 2^28 * 3^14 * 3^20. Isomorphic to e_carrier.v:133-154  *)
(* at the (B) sigma = 18 pinning.                                        *)
Lemma planb_b_esc_E3_nat : forall q : nat, (1 <= q)%nat ->
  (2 ^ (36 * planb_b_nlo q) <= 2 ^ 28 * 3 ^ 14 * q ^ 20)%nat.
Proof.
  intros q Hq.
  destruct (Nat.eq_dec q 3) as [Hq3 | Hne3].
  - (* q = 3: the lone corrected point at m = 1 - exact anchor *)
    rewrite Hq3.
    replace (planb_b_nlo 3) with 2%nat by reflexivity.
    replace (36 * 2)%nat with 72%nat by lia.
    exact planb_b_anchor_E3_q3.
  - (* general chain over the two witness branches *)
    destruct (Nat.log2_spec q) as [Hge Hlt]; [lia |].
    assert (Hd : (Nat.log2 q + 2
                  = 2 * Nat.div2 (Nat.log2 q + 2)
                  + Nat.b2n (Nat.odd (Nat.log2 q + 2)))%nat)
      by apply Nat.div2_odd.
    assert (Hb : (Nat.b2n (Nat.odd (Nat.log2 q + 2)) <= 1)%nat).
    { destruct (Nat.odd (Nat.log2 q + 2)); cbn; lia. }
    assert (Hmub : (2 * Nat.div2 (Nat.log2 q + 2)
                    <= Nat.log2 q + 2)%nat) by lia.
    assert (Hmlb : (Nat.log2 q + 1
                    <= 2 * Nat.div2 (Nat.log2 q + 2))%nat) by lia.
    (* witness form, stated as a premise BEFORE the case split: the     *)
    (* destruct then resolves the if inside Hnl per branch, so each branch *)
    (* rewrites the witness by Hnl alone - no goal-side cbn (cbn on the    *)
    (* literal-heavy RHS would normalize 2^28 * 3^14 into unary - the      *)
    (* fail-loud r3 blow-up record).                                       *)
    assert (Hnl : planb_b_nlo q
                  = (if Nat.ltb (2 ^ (2 * Nat.div2 (Nat.log2 q + 2)))
                                 (2 * q)
                     then S (Nat.div2 (Nat.log2 q + 2))
                     else Nat.div2 (Nat.log2 q + 2))%nat)
      by reflexivity.
    destruct (Nat.ltb (2 ^ (2 * Nat.div2 (Nat.log2 q + 2))) (2 * q))
      eqn:Hc;
      remember (Nat.div2 (Nat.log2 q + 2)) as m eqn:Hmdef.
    + (* corrected branch: witness S m, and 2^(2m) < 2q *)
      rewrite Hnl.
      apply Nat.ltb_lt in Hc.
      (* q <> 3 rules out the m = 1 corrected point, so log2 q >= 2 *)
      assert (Hl2 : (2 <= Nat.log2 q)%nat).
      { destruct (Nat.le_gt_cases (Nat.log2 q) 1) as [Hl1 | Hl2x]; [|lia].
        exfalso. apply Hne3.
        (* the destruct below abstracts Nat.log2 q in the hypotheses too *)
        destruct (Nat.log2 q) as [|l'] eqn:Hlq.
        - cbn in Hmdef, Hlt.
          rewrite Hmdef in Hc. cbn in Hc. lia.
        - assert (Hl0 : l' = 0%nat) by lia.
          rewrite Hl0 in Hmdef, Hlt. cbn in Hmdef, Hlt.
          rewrite Hmdef in Hc. cbn in Hc. lia. }
      assert (Hmge : (2 <= m)%nat) by lia.
      assert (Hqgt : (2 ^ (2 * m - 1) < q)%nat).
      { assert (Hpow : (2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1))%nat).
        { rewrite <- (Nat.pow_succ_r' 2 (2 * m - 1)).
          f_equal. lia. }
        lia. }
      assert (Hkq : (2 ^ (2 * m - 1) <= q)%nat) by lia.
      assert (Hexp1 : (36 * S m <= 20 * (2 * m - 1) + 49)%nat) by lia.
      apply (Nat.le_trans _ (2 ^ (20 * (2 * m - 1) + 49))).
      { apply Nat.pow_le_mono_r; lia. }
      rewrite Nat.pow_add_r.
      replace (20 * (2 * m - 1))%nat with ((2 * m - 1) * 20)%nat by lia.
      rewrite Nat.pow_mul_r.
      assert (Hk20 : ((2 ^ (2 * m - 1)) ^ 20 <= q ^ 20)%nat).
      { apply Nat.pow_le_mono_l. exact Hkq. }
      apply (Nat.le_trans _ (q ^ 20 * 2 ^ 49)).
      { apply Nat.mul_le_mono; [exact Hk20 | apply Nat.le_refl]. }
      assert (Hmid : (2 ^ 49 <= 2 ^ 28 * 3 ^ 14)%nat).
      { replace 49%nat with (28 + 21)%nat by lia.
        rewrite Nat.pow_add_r.
        apply Nat.mul_le_mono; [apply Nat.le_refl |].
        exact planb_b_anchor_E3_mid. }
      apply (Nat.le_trans _ (q ^ 20 * (2 ^ 28 * 3 ^ 14))).
      { apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hmid]. }
      rewrite (Nat.mul_comm (q ^ 20) (2 ^ 28 * 3 ^ 14)).
      apply Nat.le_refl.
    + (* uncorrected branch: witness m = div2 (log2 q + 2) *)
      rewrite Hnl.
      assert (Hexp2 : (36 * m <= 18 * Nat.log2 q + 36)%nat) by lia.
      apply (Nat.le_trans _ (2 ^ (18 * Nat.log2 q + 36))).
      { apply Nat.pow_le_mono_r; lia. }
      rewrite Nat.pow_add_r.
      replace (18 * Nat.log2 q)%nat with (Nat.log2 q * 18)%nat by lia.
      rewrite Nat.pow_mul_r.
      assert (Hq18 : ((2 ^ Nat.log2 q) ^ 18 <= q ^ 18)%nat).
      { apply Nat.pow_le_mono_l. exact Hge. }
      apply (Nat.le_trans _ (q ^ 18 * 2 ^ 36)).
      { apply Nat.mul_le_mono; [exact Hq18 | apply Nat.le_refl]. }
      assert (Hlo36 : (2 ^ 36 <= 2 ^ 28 * 3 ^ 14)%nat).
      { replace 36%nat with (28 + 8)%nat by lia.
        rewrite Nat.pow_add_r.
        apply Nat.mul_le_mono; [apply Nat.le_refl |].
        exact planb_b_anchor_E3_lo. }
      apply (Nat.le_trans _ (q ^ 18 * (2 ^ 28 * 3 ^ 14))).
      { apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hlo36]. }
      rewrite (Nat.mul_comm (q ^ 18) (2 ^ 28 * 3 ^ 14)).
      apply Nat.mul_le_mono; [apply Nat.le_refl |].
      apply Nat.pow_le_mono_r; lia.
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
   1.7e10 (the planb1-side q = 3 exact anchor reaches 2^72 * 3^20 ~
   4.5e24); the E3 re-derivation is a pure nat lemma chain (pow_le_mono /
   mul_le_mono), no solver runs on powers; the square-root dance (now in
   the certificate unit) is proof-term-only. Expected compile cost: well
   under one cpu_guard_v3 shot budget.

   EFFECTIVENESS: planb_b_rate_c0_E10 (certificate unit) is the
   exponent-10 first-power face feeding planb_b_rate_dist_slot11, the
   (B)-migrated counterpart of the ck_alpha c0 8 q height-form slot
   (e_carrier.v:684); every downstream consumer replaces its 8-slot
   instantiations by 11. planb_b_esc_E3_nat is the sigma = 18 E3 face
   at the lower-edge window witness planb_b_nlo; with
   planb_b_esc_E1_lo_nat (the growth limb at the same witness) it is
   the escape-supply pair of the sigma = 18 chain. The stock
   sigma = 17 faces planb_b_esc_E1_nat / planb_b_nesc stay for the
   sigma = 17 consumption face planb_b_hesc17 (kept at the sigma = 17
   instance in this unit; the sigma = 18 counterpart and the downstream
   discharge are the landing-wave surface).
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
Print Assumptions planb_b_esc_E1_lo_nat.
Print Assumptions planb_b_esc_E3_nat.
Print Assumptions planb_b_mubound_zerotouch.
Print Assumptions planb_b_nesc_bounds.
