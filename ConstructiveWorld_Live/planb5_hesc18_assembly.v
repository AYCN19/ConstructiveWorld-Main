(* ConstructiveWorld-Main - planB wave-5 assembly: the Hesc18 limb-2     *)
(* escape chain - two layers and two routes over the full modulus range. *)

(** * planb5_hesc18_assembly: the two-layer four-piece Hesc18 limb-2 face.

    Mission.  The limb-2 assembly of the planB wave-5 chain, delivered at
      the calibration pair (planb3_g1_A, planb3_g1_B) as two layers and
      two routes.  (a) Tier 1, planb5_esc18_reduce: the same-index
      selection function planb5_esc18_pick with
      m = if Z.eqb (A n * Z.of_nat q + B n * p) 0 then S n else n reduces
      the window faces held at the consecutive indices n and S n to the
      full three-limb escape body at the pick index, sigT-carried.
      (b) Tier 2, planb5_esc18_dodge_upgrade: the Delta n nonzero
      contrapositive upgrade of the dodge pair - at q >= 1 at least one
      of the two indicators is nonzero.  (c) Route F,
      planb5_esc18_forced: the forced band route over 1 <= q <= 558240,
      zero premises beyond the range bound, zero use of the dodge
      determinant.  (d) Route W, planb5_esc18_window_route: the window
      supply face above the forced band, with the dodge-determinant slot
      as an explicit positional premise.  (e) planb5_esc18_global: the
      dispatch - q within the forced band goes to Route F, q above it
      goes to Route W.
    Debt ledger.  Three lines, honest states:
      (D1) DELIVERED as an explicit slot: the dodge determinant
        Delta (nlo q) <> 0 at the window witness - carried verbatim as
        the positional premise of planb5_esc18_window_route and
        planb5_esc18_global; a premise slot only, never discharged,
        never a global axiom.
      (D2) NOT DELIVERED (registered fail-loud): the window-face
        finalization - the escape-window faces of this file are recast
        at the sigma = 18 pins (the P4 re-pin) and stay a sandbox
        finalization candidate until the A3 shore-landing (the WF-2
        merge) lands; promotion to final is out of this unit's scope.
      (D3) NOT DELIVERED (registered fail-loud): the shore-landing face -
        the assembly is delivered as a sandbox handoff only; the landing
        into the in-tree world is a later unit.
    SIGMA-18 RECAST - FINALIZATION CANDIDATE, NOT FINAL: the window
      faces in this file are recast at the sigma = 18 pins of the P4
      prescription (window q <= 2^20 zero holes; band minimum
      L = 20..3000 with n_hi - n_lo >= 1; forced set 84081 with
      max 558240 and witnesses n <= 11 in table; |A_n|, |B_n| <=
      2^(18n) with the n = 5 tension resolved; rate face E = 10 exact
      division).  The file must not be promoted to final before the
      A3 shore-landing (the WF-2 merge) lands.  The retired v1 window
      statement face (the log2-threshold same-window form) is not
      restored here.
    Dependencies.  Stdlib QArith.QArith, ZArith, Arith.Arith, Lia,
      Qpower; piu_mu_criterion; planb1_hcage_zerotouch_prescription
      (the sigma = 18 unit: the lower-edge window witness planb_b_nlo,
      the growth limb planb_b_esc_E1_lo_nat, the re-derived
      planb_b_esc_E3_nat at 2^(36n) <= 2^28 * 3^14 * q^20, and the
      anchor 2^21 <= 3^14); planb3_g1_calib.  Z-domain Lia at auxiliary
      bookkeeping steps only.  One-way layering: the assembly consumes
      the in-tree base units and adds no Require edge into them.
    References.  The two-indicator dodge prescription with the Z.eqb
      selection reading and the sigT carrier (M1:434 segment 1); the
      sigma = 18 escape faces planb_b_esc_E1_lo_nat and
      planb_b_esc_E3_nat at the lower-edge witness planb_b_nlo
      (planb1 Section 3); the Nat2Z monotone lift pattern (the planb1
      anchor transports); the calibration tables (planb3_g1_calib.v);
      the local Q-bridge craft (piu_zz_ec_escwin_nescD.v:103-124 and
      328-345); the coprime engine is the stdlib Gauss theorem
      (Z.gauss); the sigma = 18 window measurement (forced set 84081,
      max 558240, witnesses n <= 11).
    Constructivity.  The delivered route faces are sigT-carried over
      piu_mu_and3 of piu_mu_QleT and piu_mu_ZleT (Set carriers) with the
      dodge-determinant slot as the only premise of the global face.
      All numeric ground faces are boolean certificates proven by
      vm_compute (informative carriers).  The Prop-sorted helper
      statements (the dodge pair, the Tier-2 upgrade, the reflection
      bridges, the Qeq inject bridges) are consumed at proof positions
      only and are registered with their consumption sites in the merged
      consumption census delivered alongside this file.
      Admission-free, assumption-free; every statement closes under the
      global context (Print Assumptions = Closed); definitions
      transparent.
    Build.  coqc -native-compiler no -q -Q . "" -Q vo_base ""
      planb5_hesc18_assembly.v, run from the sandbox root (Rocq 9.3.0,
      serial single lane; the sandbox-local vo_base copy is the seated
      trust cache of this box - the bundled vo_closure_base cache is
      superseded here, see the base-seat provenance ledger; the
      sigma = 18 planb1 unit is compiled in this sandbox from the
      sigma = 18 recast source). *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
From Stdlib Require Import List.
Import ListNotations.
Require Import piu_mu_criterion.
Require Import planb1_hcage_zerotouch_prescription.
Require Import planb3_g1_calib.


(* ------------------------------------------------------------------ *)
(* Merged fragment 1 of 4 (planb5_frag_dodge.v): the statements and   *)
(* proofs below are carried verbatim from the cast fragment; the       *)
(* Section banners are renumbered for the merged file.                 *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(* Section 1. The dodge identity: both indicators zero force          *)
(*            q * Delta n = 0.                                        *)
(* ================================================================== *)

(* The two indicator relations read A n * q + B n * p = 0 and          *)
(* A (S n) * q + B (S n) * p = 0 with the modulus q embedded from      *)
(* nat into Z; Delta n is the determinant                              *)
(* A n * B (S n) - A (S n) * B n.                                      *)

Lemma planb5_dodge_qΔ :
  forall (A B : nat -> Z) (p : Z) (q n : nat),
  (A n * Z.of_nat q + B n * p = 0)%Z ->
  (A (S n) * Z.of_nat q + B (S n) * p = 0)%Z ->
  (Z.of_nat q * (A n * B (S n) - A (S n) * B n) = 0)%Z.
Proof.
  intros A B p q n H1 H2.
  (* identity recast: the dodged product equals the B (S n)-scaled    *)
  (* first relation minus the B n-scaled second relation - a ring    *)
  (* identity on the Z commutative-ring face.                        *)
  assert (Hid : (Z.of_nat q * (A n * B (S n) - A (S n) * B n)
                 = B (S n) * (A n * Z.of_nat q + B n * p)
                   - B n * (A (S n) * Z.of_nat q + B (S n) * p))%Z)
    by ring.
  (* both indicator hypotheses annihilate the two scaled relations   *)
  rewrite Hid, H1, H2.
  ring.
Qed.

(* ================================================================== *)
(* Section 2. The contrapositive: Delta n nonzero and the first       *)
(*            indicator zero force the second indicator nonzero.      *)
(* ================================================================== *)

(* With q >= 1 the modulus embedding Z.of_nat q is nonzero, so once    *)
(* the first indicator vanishes the second cannot: the dodge identity  *)
(* makes the product Z.of_nat q * Delta n vanish, Z.mul_eq_0 splits    *)
(* that product, and both splits are contradictory (lia against        *)
(* 1 <= q, or the explicit Delta n nonzero premise).                   *)

Lemma planb5_dodge_contra :
  forall (A B : nat -> Z) (p : Z) (q n : nat),
  (1 <= q)%nat ->
  (A n * B (S n) - A (S n) * B n <> 0)%Z ->
  (A n * Z.of_nat q + B n * p = 0)%Z ->
  (A (S n) * Z.of_nat q + B (S n) * p <> 0)%Z.
Proof.
  intros A B p q n Hq Hdelta H1.
  (* decidable split on the second indicator (Z.eq_dec)              *)
  destruct (Z.eq_dec (A (S n) * Z.of_nat q + B (S n) * p) 0)
    as [H2 | H2].
  - (* second indicator zero: the dodge identity annihilates, and     *)
    (* Z.mul_eq_0 leaves two splits, each contradictory               *)
    exfalso.
    pose proof (planb5_dodge_qΔ A B p q n H1 H2) as Hz.
    apply Z.mul_eq_0 in Hz.
    destruct Hz as [Hqz | Hdz].
    + (* Z.of_nat q = 0 contradicts 1 <= q *) lia.
    + (* Delta n = 0 contradicts the explicit premise *)
      exact (Hdelta Hdz).
  - (* second indicator nonzero: the goal holds directly              *)
    exact H2.
Qed.


(* ------------------------------------------------------------------ *)
(* Merged fragment 2 of 4 (planb5_frag_adapters.v): the statements and *)
(* proofs below are carried from the cast fragment and recast at the   *)
(* sigma = 18 pins; the Section banners are renumbered for the merged  *)
(* file.                                                               *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(* Section 3. Local Q bridges (the inject/pow craft cloned from the   *)
(*            escwin-nescD Section-2 forms, planb5-prefixed).         *)
(* ================================================================== *)

(* inject_Z is multiplicative up to the Q setoid equality. *)
Lemma planb5_adapt_inj_mul_eq : forall x y : Z,
  inject_Z (x * y) == inject_Z x * inject_Z y.
Proof.
  intros x y. unfold inject_Z, Qmult, Qeq. cbn. ring.
Qed.

(* the square of an inject form: the Qpower face at exponent 2 is the   *)
(* inject face of the squared integer (no nonzero side condition is     *)
(* needed at the fixed exponent 2).                                     *)
Lemma planb5_adapt_inj_sq_eq : forall z : Z,
  Qpower (inject_Z z) (Z.of_nat 2) == inject_Z (z * z).
Proof.
  intros z. unfold inject_Z, Qpower, Qeq. cbn. ring.
Qed.

(* inject_Z commutes with nat-indexed powers on positive bases. *)
Lemma planb5_adapt_inj_pow_eq : forall (z : Z) (k : nat),
  (0 < z)%Z ->
  inject_Z (z ^ Z.of_nat k) == Qpower (inject_Z z) (Z.of_nat k).
Proof.
  intros z k Hz. induction k as [|k IH].
  - cbn [Z.of_nat]. rewrite Z.pow_0_r, Qpower_0_r. reflexivity.
  - assert (Hne : ~ (inject_Z z == 0)%Q).
    { intro Hc. unfold inject_Z, Qeq in Hc. cbn [Qnum Qden] in Hc. lia. }
    assert (Hs : (Z.of_nat (Datatypes.S k) = Z.of_nat k + 1)%Z) by lia.
    rewrite Hs.
    rewrite Qpower_plus by exact Hne.
    replace (Qpower (inject_Z z) 1) with (inject_Z z) by reflexivity.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
    rewrite (planb5_adapt_inj_mul_eq (z ^ Z.of_nat k) z).
    rewrite IH. reflexivity.
Qed.

(* ================================================================== *)
(* Section 4. The kappa-square ground pin: (35831808 # 1)^2 is         *)
(*            2^28 * 3^14 (35831808 = 2^14 * 3^7).                    *)
(* ================================================================== *)

Example planb5_adapt_kappa2_pin : (35831808 ^ 2 = 2 ^ 28 * 3 ^ 14)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 5. Adapter 1: the E1_lo window face into the Hesc18        *)
(*            limb-1 slot (non-strict nat face, non-strict Q face).   *)
(* ================================================================== *)

(* Source end: planb_b_esc_E1_lo_nat (planb1 Section 3) - the           *)
(* non-strict nat face 2*q <= 2^(2*nlo q) at the lower-edge witness.    *)
(* Target end: the limb-1 slot of the Hesc18 body at n = planb_b_nlo q  *)
(* - the non-strict Q face inject_Z (2*q) <= epos (2*n).  Lift: the     *)
(* Nat2Z monotone bridge (the planb1 anchor-transport pattern) carries  *)
(* the face to Z and piu_mu_Zle_Qle carries it to Q.                    *)
Lemma planb5_adapt_E1_limb1 : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
              (piu_mu_epos (2 * planb_b_nlo q)).
Proof.
  intros q Hq.
  pose proof (planb_b_esc_E1_lo_nat q Hq) as H1.
  (* Nat2Z monotone lift, the planb1 anchor-transport pattern *)
  pose proof (proj1 (Nat2Z.inj_le _ _) H1) as Hz0.
  rewrite Nat2Z.inj_pow in Hz0.
  change (Z.of_nat 2) with 2%Z in Hz0.
  (* Z monotone bridge into the Q carrier at the limb-1 slot *)
  exact (piu_mu_Zle_Qle (Z.of_nat (2 * q))
           (2 ^ Z.of_nat (2 * planb_b_nlo q)) Hz0).
Qed.

(* ================================================================== *)
(* Section 6. Adapter 2: the E3_nat growth face into the Hesc18       *)
(*            limb-3 slot (squared faces, kappa^2 = 2^28 * 3^14).     *)
(* ================================================================== *)

(* Source end: planb_b_esc_E3_nat (planb1 Section 3, sigma = 18) -      *)
(* the nat face 2^(36*nlo q) <= 2^28 * 3^14 * q^20 at the lower-edge    *)
(* witness.  Target end: the limb-3 slot of the Hesc18 body at          *)
(* n = planb_b_nlo q - the squared Q face epos (18*n)^2 <=              *)
(* (35831808 # 1)^2 * q^20, where (35831808 # 1)^2 = 2^28 * 3^14 by the *)
(* Section-4 pin.  Both faces are rewritten into inject_Z form by the   *)
(* Section-3 bridges, and the resulting Z ordering is the planb1 Nat2Z  *)
(* lift of the nat face.                                                *)
Lemma planb5_adapt_E3_limb3 : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (Qpower (piu_mu_epos (18 * planb_b_nlo q)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q.
Proof.
  intros q Hq.
  (* Nat2Z monotone lift of the nat face, the planb1 anchor-transport    *)
  (* pattern *)
  pose proof (proj1 (Nat2Z.inj_le _ _) (planb_b_esc_E3_nat q Hq)) as HZ.
  repeat rewrite Nat2Z.inj_mul in HZ.
  repeat rewrite Nat2Z.inj_pow in HZ.
  (* literal repair: keep the numerals folded (cbn would half-reduce     *)
  (* Z.of_nat 2 into a Pos.of_succ_nat shape and break the pin rewrite)  *)
  change (Z.of_nat 2) with 2%Z in HZ.
  change (Z.of_nat 28) with 28%Z in HZ.
  change (Z.of_nat 3) with 3%Z in HZ.
  change (Z.of_nat 14) with 14%Z in HZ.
  (* 36 * nlo = 18 * nlo + 18 * nlo, then the square reads off *)
  assert (Hz36 : (Z.of_nat (36 * planb_b_nlo q)
                  = Z.of_nat (18 * planb_b_nlo q)
                    + Z.of_nat (18 * planb_b_nlo q))%Z).
  { replace (36 * planb_b_nlo q)%nat
      with ((18 * planb_b_nlo q) + (18 * planb_b_nlo q))%nat by lia.
    apply Nat2Z.inj_add. }
  rewrite Hz36 in HZ.
  rewrite Z.pow_add_r in HZ by lia.
  (* kappa^2 = 2^28 * 3^14 (the Section-4 pin, read right-to-left) *)
  rewrite <- planb5_adapt_kappa2_pin in HZ.
  (* the raw Q face at the limb-3 slot *)
  apply piu_mu_QleT_i.
  unfold piu_mu_epos.
  change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
  rewrite (planb5_adapt_inj_sq_eq (2 ^ Z.of_nat (18 * planb_b_nlo q))%Z).
  change (Qpower (35831808 # 1)%Q (Z.of_nat 2))
    with (inject_Z (35831808 ^ 2)%Z).
  rewrite <- (planb5_adapt_inj_pow_eq (Z.of_nat q) 20%nat ltac:(lia)).
  rewrite <- (planb5_adapt_inj_mul_eq (35831808 ^ 2)%Z
                ((Z.of_nat q) ^ Z.of_nat 20)%Z).
  destruct (piu_mu_Zle_Qle _ _ HZ) as [HQ].
  exact HQ.
Qed.

(* ================================================================== *)
(* Assembly glue: modulus-bound bridges for the large decimal bounds.  *)
(*                                                                    *)
(* Decimal nat numerals above 5000 are parsed as symbolic              *)
(* Init.Nat.of_num_uint applications, which lia treats as opaque      *)
(* atoms, so the small-bound faces are bridged once here: the          *)
(* successor equations are boolean vm certificates, and the plain      *)
(* 1 <= q face follows by transitivity through the S-form.             *)
(* ================================================================== *)

Example planb5_esc18_e558241 : (558241 =? S 558240)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example planb5_esc18_e46038 : (46038 =? S 46037)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example planb5_esc18_e160313 : (160313 =? S 160312)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example planb5_esc18_e13221 : (13221 =? S 13220)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb5_esc18_bound1 : forall q : nat, (558241 <= q)%nat -> (1 <= q)%nat.
Proof.
  intros q Hq.
  apply (Nat.le_trans 1%nat 558241%nat q%nat).
  - rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc18_e558241).
    apply (le_n_S 0%nat 558240%nat).
    apply Nat.le_0_l.
  - exact Hq.
Qed.


(* ------------------------------------------------------------------ *)
(* Merged fragment 3 of 4 (planb5_frag_window.v): the statements and  *)
(* proofs below are carried from the cast fragment and recast at the  *)
(* sigma = 18 pins; the Section banners are renumbered for the merged  *)
(* file.                                                              *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(* Section 7. The limb-1 face at the shifted witness S (nlo q):       *)
(*            the non-strict E1_lo limb lifted one step by pow        *)
(*            monotonicity.                                           *)
(* ================================================================== *)

(* The E1_lo limb is non-strict at the witness (2 * q <= 2 ^ (2 * nlo   *)
(* q)); the shifted face needs only the same non-strict form one        *)
(* exponent step up, since 2 * nlo q <= 2 * S (nlo q).                  *)

Lemma planb5_esc_E1p_nat : forall q : nat, (1 <= q)%nat ->
  (2 * q <= 2 ^ (2 * S (planb_b_nlo q)))%nat.
Proof.
  intros q Hq.
  pose proof (planb_b_esc_E1_lo_nat q Hq) as He1.
  apply (Nat.le_trans _ (2 ^ (2 * planb_b_nlo q))).
  - (* the non-strict E1_lo limb gives the first hop *)
    exact He1.
  - (* the exponent grows by exactly two under the witness shift *)
    apply Nat.pow_le_mono_r; lia.
Qed.

(* ================================================================== *)
(* Section 8. The binary-Z threshold adjudication literals at         *)
(*            q = 558241 / q = 558240 (vm_compute, exact).            *)
(* ================================================================== *)

(* Reach side: the tight difference at the threshold is a 118-digit     *)
(* positive numeral, carried verbatim; binary-Z evaluation keeps the    *)
(* nat side free of unary blowup.                                       *)

Example planb5_esc_E3p_diff_z :
  (3 ^ 14 * 558241 ^ 20 - 2 ^ 404)%Z
  = 1324215486919340883998652641212999504656683129697344240072442297383674950759829516550371797744109912635043423515356153%Z.
Proof. vm_compute. reflexivity. Qed.

(* Non-reach side: at q = 558240 the growth face fails at witness       *)
(* S (nlo q) = 12, so the threshold 558241 is tight.                    *)

Example planb5_esc_E3p_noreach_z :
  Z.leb (2 ^ 404) (3 ^ 14 * 558240 ^ 20) = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 9. The nat-side reach face at the threshold, transported   *)
(*            from the binary-Z literal (the Nat2Z craft of planb1).  *)
(* ================================================================== *)

(* The Z-carried difference literal is nonnegative, so the reach order *)
(* holds in Z; Nat2Z.inj_le with inj_mul / inj_pow transports it to    *)
(* nat without evaluating any nat-side power.                          *)

Lemma planb5_esc_E3p_reach :
  (2 ^ 404 <= 3 ^ 14 * 558241 ^ 20)%nat.
Proof.
  assert (Hz : (2 ^ 404 <= 3 ^ 14 * 558241 ^ 20)%Z)
    by (pose proof planb5_esc_E3p_diff_z; lia).
  apply (proj2 (Nat2Z.inj_le (2 ^ 404) (3 ^ 14 * 558241 ^ 20))).
  rewrite Nat2Z.inj_mul, Nat2Z.inj_pow, Nat2Z.inj_pow, Nat2Z.inj_pow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  replace (Z.of_nat 404) with 404%Z by reflexivity.
  replace (Z.of_nat 3) with 3%Z by reflexivity.
  replace (Z.of_nat 14) with 14%Z by reflexivity.
  replace (Z.of_nat 558241) with 558241%Z by reflexivity.
  replace (Z.of_nat 20) with 20%Z by reflexivity.
  exact Hz.
Qed.

(* ================================================================== *)
(* Section 10. The limb-3 face at the shifted witness:                 *)
(*            planb5_esc_E3p_nat (threshold 558241).                  *)
(* ================================================================== *)

(* Case below 2 ^ 20: the shifted witness is at most 12 (nlo q <= 11    *)
(* when log2 q <= 19), so the left side is at most 2 ^ 432 =            *)
(* 2 ^ 28 * 2 ^ 404, and the threshold reach plus pow monotonicity of   *)
(* q ^ 20 carries the right side.  Case from 2 ^ 20: the planb1 E3      *)
(* craft applies with a parity split on log2 q - the exponent excess    *)
(* 72 = 28 + 44 (even log2, where the nlo correction never fires and    *)
(* S (nlo q) = log2 q / 2 + 2) or 90 = 28 + 62 (odd log2) is absorbed   *)
(* by q ^ 2 at the 2 ^ 20 / 2 ^ 21 floor (the anchor 2 ^ 21 <= 3 ^ 14   *)
(* covers 2 ^ 4 <= 3 ^ 14 and 2 ^ 20 <= 3 ^ 14 alike).                  *)

Lemma planb5_esc_E3p_nat : forall q : nat, (558241 <= q)%nat ->
  (2 ^ (36 * S (planb_b_nlo q)) <= 2 ^ 28 * 3 ^ 14 * q ^ 20)%nat.
Proof.
  intros q Hq.
  pose proof (planb5_esc18_bound1 q Hq) as Hq1.
  assert (Hr2 : (2 ^ 404 <= 3 ^ 14 * q ^ 20)%nat).
  { apply (Nat.le_trans _ (3 ^ 14 * 558241 ^ 20)).
    - exact planb5_esc_E3p_reach.
    - apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l; lia. }
  (* witness bound from the nlo definition shape: nlo q <= S (div2      *)
  (* (log2 q + 2)), both branches of the decidable step alike *)
  assert (Hnl : (planb_b_nlo q <= S (Nat.div2 (Nat.log2 q + 2)))%nat).
  { unfold planb_b_nlo. cbv zeta.
    destruct (Nat.ltb (2 ^ (2 * Nat.div2 (Nat.log2 q + 2))) (2 * q));
      cbn; lia. }
  destruct (le_lt_dec (2 ^ 20) q) as [Hbig | Hsmall].
  - (* case from 2 ^ 20: the E3 craft with the q ^ 2 absorption *)
    destruct (Nat.log2_spec q) as [Hge Hlt]; [exact Hq1 |].
    assert (Hnlt : ~ (Nat.log2 q < 20)%nat).
    { intro Hc.
      destruct (Nat.log2_lt_pow2 q 20 Hq1) as [_ Hf].
      apply Hf in Hc. lia. }
    assert (Hl20 : (20 <= Nat.log2 q)%nat) by lia.
    destruct (Nat.Even_or_Odd (Nat.log2 q)) as [[k Hk] | [k Hk]].
    + (* even log2 q = 2*k: the nlo correction never fires, so        *)
      (* nlo q = k + 1 and the exponent excess is 72 *)
      assert (Hnlok : planb_b_nlo q = S (Nat.div2 (Nat.log2 q))%nat).
      { assert (Hd2 : (Nat.div2 (Nat.log2 q + 2)
                       = S (Nat.div2 (Nat.log2 q)))%nat).
        { replace (Nat.log2 q + 2)%nat with (S (S (Nat.log2 q)))%nat by lia.
          reflexivity. }
        unfold planb_b_nlo. cbv zeta. rewrite Hd2.
        destruct (Nat.ltb (2 ^ (2 * S (Nat.div2 (Nat.log2 q)))) (2 * q))
          eqn:Hc.
        - exfalso. apply Nat.ltb_lt in Hc.
          rewrite Hk in Hc, Hlt. rewrite Nat.div2_double in Hc.
          assert (H2q : (2 * q < 2 ^ (2 * S k))%nat).
          { replace (2 * S k)%nat with (S (S (2 * k)))%nat by lia.
            rewrite Nat.pow_succ_r'.
            apply (proj1 (Nat.mul_lt_mono_pos_l 2 q (2 ^ S (2 * k))
                            (Nat.lt_0_succ 1))).
            exact Hlt. }
          lia.
        - reflexivity. }
      rewrite Hk in Hnlok. rewrite Nat.div2_double in Hnlok.
      assert (Hexp : (36 * S (planb_b_nlo q)
                      <= 18 * Nat.log2 q + 72)%nat) by lia.
      apply (Nat.le_trans _ (2 ^ (18 * Nat.log2 q + 72))).
      * apply Nat.pow_le_mono_r; lia.
      * rewrite Nat.pow_add_r.
        replace (18 * Nat.log2 q)%nat with (Nat.log2 q * 18)%nat by lia.
        rewrite Nat.pow_mul_r.
        assert (Hq18 : ((2 ^ Nat.log2 q) ^ 18 <= q ^ 18)%nat).
        { apply Nat.pow_le_mono_l. exact Hge. }
        apply (Nat.le_trans _ (q ^ 18 * 2 ^ 72)).
        { apply Nat.mul_le_mono; [exact Hq18 | apply Nat.le_refl]. }
        assert (Hq20 : (2 ^ 20 <= q)%nat).
          { apply (Nat.le_trans _ (2 ^ Nat.log2 q)).
            { apply Nat.pow_le_mono_r; lia. }
            exact Hge. }
          assert (Hqq : (2 ^ 20 * 2 ^ 20 <= q * q)%nat)
            by (apply Nat.mul_le_mono; exact Hq20).
          assert (Hkey : (2 ^ 72 <= 2 ^ 28 * 3 ^ 14 * (q * q))%nat).
          { replace 72%nat with (28 + 44)%nat by (vm_compute; reflexivity).
            rewrite Nat.pow_add_r.
            replace 44%nat with (4 + 40)%nat by (vm_compute; reflexivity).
            rewrite Nat.pow_add_r.
            assert (H4 : (2 ^ 4 <= 2 ^ 21)%nat) by (apply Nat.pow_le_mono_r; lia).
            assert (Hstep0 : (2 ^ 4 * 2 ^ 40 <= 2 ^ 21 * 2 ^ 40)%nat)
              by (apply Nat.mul_le_mono; [exact H4 | apply Nat.le_refl]).
            assert (Hstep1 : (2 ^ 21 * 2 ^ 40 <= 3 ^ 14 * (2 ^ 20 * 2 ^ 20))%nat).
            { apply Nat.mul_le_mono.
              - exact planb_b_anchor_E3_mid.
              - replace 40%nat with (20 + 20)%nat by (vm_compute; reflexivity).
                rewrite Nat.pow_add_r. apply Nat.le_refl. }
            assert (Hstep2 : (3 ^ 14 * (2 ^ 20 * 2 ^ 20) <= 3 ^ 14 * (q * q))%nat)
              by (apply Nat.mul_le_mono_l; exact Hqq).
            apply (Nat.le_trans _ (2 ^ 28 * (2 ^ 21 * 2 ^ 40))).
            { apply Nat.mul_le_mono_l. exact Hstep0. }
            apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (2 ^ 20 * 2 ^ 20)))).
            { apply Nat.mul_le_mono_l. exact Hstep1. }
            apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (q * q)))).
            { apply Nat.mul_le_mono_l. exact Hstep2. }
            rewrite Nat.mul_assoc. apply Nat.le_refl. }
          replace (q ^ 20)%nat with (q ^ 2 * q ^ 18)%nat
            by (rewrite <- (Nat.pow_add_r q 2 18); f_equal;
                vm_compute; reflexivity).
          assert (Hrq : (q ^ 18 * (2 ^ 28 * 3 ^ 14 * (q * q))
                         = 2 ^ 28 * 3 ^ 14 * (q ^ 2 * q ^ 18))%nat).
          { replace (q ^ 2)%nat with (q * q)%nat
              by (change (q ^ 2)%nat with (q ^ (1 + 1))%nat;
                  rewrite Nat.pow_add_r; rewrite !Nat.pow_1_r; reflexivity).
            rewrite Nat.mul_assoc.
            rewrite (Nat.mul_comm (q ^ 18) (2 ^ 28 * 3 ^ 14)).
            rewrite <- Nat.mul_assoc.
            rewrite (Nat.mul_comm (q ^ 18) (q * q)).
            reflexivity. }
          apply (Nat.le_trans _ (q ^ 18 * (2 ^ 28 * 3 ^ 14 * (q * q)))).
          { apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hkey]. }
          rewrite Hrq. apply Nat.le_refl.
    + (* odd log2 q = 2*k+1: the witness is at most k + 2 and the      *)
      (* exponent excess is 90 *)
      assert (Hd : (Nat.log2 q + 2
                    = 2 * Nat.div2 (Nat.log2 q + 2)
                    + Nat.b2n (Nat.odd (Nat.log2 q + 2)))%nat)
        by apply Nat.div2_odd.
      assert (Hb : (Nat.b2n (Nat.odd (Nat.log2 q + 2)) <= 1)%nat).
      { destruct (Nat.odd (Nat.log2 q + 2)); cbn; lia. }
      assert (Hexp : (36 * S (planb_b_nlo q)
                      <= 18 * Nat.log2 q + 90)%nat) by lia.
      apply (Nat.le_trans _ (2 ^ (18 * Nat.log2 q + 90))).
      { apply Nat.pow_le_mono_r; lia. }
      rewrite Nat.pow_add_r.
      replace (18 * Nat.log2 q)%nat with (Nat.log2 q * 18)%nat by lia.
      rewrite Nat.pow_mul_r.
      assert (Hq18 : ((2 ^ Nat.log2 q) ^ 18 <= q ^ 18)%nat).
      { apply Nat.pow_le_mono_l. exact Hge. }
      apply (Nat.le_trans _ (q ^ 18 * 2 ^ 90)).
      { apply Nat.mul_le_mono; [exact Hq18 | apply Nat.le_refl]. }
      assert (Hq21 : (2 ^ 21 <= q)%nat).
      { apply (Nat.le_trans _ (2 ^ Nat.log2 q)).
        { apply Nat.pow_le_mono_r; lia. }
        exact Hge. }
      assert (Hqq : (2 ^ 21 * 2 ^ 21 <= q * q)%nat)
        by (apply Nat.mul_le_mono; exact Hq21).
      assert (Hkey : (2 ^ 90 <= 2 ^ 28 * 3 ^ 14 * (q * q))%nat).
      { replace 90%nat with (28 + 62)%nat by (vm_compute; reflexivity).
        rewrite Nat.pow_add_r.
        replace 62%nat with (20 + 42)%nat by (vm_compute; reflexivity).
        rewrite Nat.pow_add_r.
        assert (H20 : (2 ^ 20 <= 2 ^ 21)%nat) by (apply Nat.pow_le_mono_r; lia).
        assert (Hstep0 : (2 ^ 20 * 2 ^ 42 <= 2 ^ 21 * 2 ^ 42)%nat)
          by (apply Nat.mul_le_mono; [exact H20 | apply Nat.le_refl]).
        assert (Hstep1 : (2 ^ 21 * 2 ^ 42 <= 3 ^ 14 * (2 ^ 21 * 2 ^ 21))%nat).
        { apply Nat.mul_le_mono.
          - exact planb_b_anchor_E3_mid.
          - replace 42%nat with (21 + 21)%nat by (vm_compute; reflexivity).
            rewrite Nat.pow_add_r. apply Nat.le_refl. }
        assert (Hstep2 : (3 ^ 14 * (2 ^ 21 * 2 ^ 21) <= 3 ^ 14 * (q * q))%nat)
          by (apply Nat.mul_le_mono_l; exact Hqq).
        apply (Nat.le_trans _ (2 ^ 28 * (2 ^ 21 * 2 ^ 42))).
        { apply Nat.mul_le_mono_l. exact Hstep0. }
        apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (2 ^ 21 * 2 ^ 21)))).
        { apply Nat.mul_le_mono_l. exact Hstep1. }
        apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (q * q)))).
        { apply Nat.mul_le_mono_l. exact Hstep2. }
        rewrite Nat.mul_assoc. apply Nat.le_refl. }
      replace (q ^ 20)%nat with (q ^ 2 * q ^ 18)%nat
        by (rewrite <- (Nat.pow_add_r q 2 18); f_equal;
            vm_compute; reflexivity).
      assert (Hrq : (q ^ 18 * (2 ^ 28 * 3 ^ 14 * (q * q))
                     = 2 ^ 28 * 3 ^ 14 * (q ^ 2 * q ^ 18))%nat).
      { replace (q ^ 2)%nat with (q * q)%nat
          by (change (q ^ 2)%nat with (q ^ (1 + 1))%nat;
              rewrite Nat.pow_add_r; rewrite !Nat.pow_1_r; reflexivity).
        rewrite Nat.mul_assoc.
        rewrite (Nat.mul_comm (q ^ 18) (2 ^ 28 * 3 ^ 14)).
        rewrite <- Nat.mul_assoc.
        rewrite (Nat.mul_comm (q ^ 18) (q * q)).
        reflexivity. }
      apply (Nat.le_trans _ (q ^ 18 * (2 ^ 28 * 3 ^ 14 * (q * q)))).
      { apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hkey]. }
      rewrite Hrq. apply Nat.le_refl.
  - (* case below 2 ^ 20: the shifted witness is at most 12 *)
    assert (Hl19 : (Nat.log2 q < 20)%nat).
    { destruct (Nat.log2_lt_pow2 q 20 Hq1) as [Hiff _].
      apply Hiff. exact Hsmall. }
    assert (Hd : (Nat.log2 q + 2
                  = 2 * Nat.div2 (Nat.log2 q + 2)
                  + Nat.b2n (Nat.odd (Nat.log2 q + 2)))%nat)
      by apply Nat.div2_odd.
    assert (Hb : (Nat.b2n (Nat.odd (Nat.log2 q + 2)) <= 1)%nat).
    { destruct (Nat.odd (Nat.log2 q + 2)); cbn; lia. }
    assert (Hs12 : (S (planb_b_nlo q) <= 12)%nat) by lia.
    apply (Nat.le_trans _ (2 ^ 432)).
    + apply Nat.pow_le_mono_r; lia.
    + replace 432%nat with (28 + 404)%nat by (vm_compute; reflexivity).
      rewrite Nat.pow_add_r.
      (* re-associate the right side first: the flat product form defeats  *)
      (* the unifier here (stack overflow at the deep numerals)            *)
      rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hr2].
Qed.


(* ------------------------------------------------------------------ *)
(* Merged fragment 4 of 4 (planb5_frag_forced.v): the statements and  *)
(* proofs below are carried from the cast fragment and recast at the  *)
(* sigma = 18 pins; the Section banners are renumbered for the merged  *)
(* file.                                                              *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(* Section 11. Local Q bridges (the inject craft cloned from the       *)
(*            escwin-nescD Section-2 forms, planb5-forced prefix).    *)
(* ================================================================== *)

(* inject_Z is multiplicative up to the Q setoid equality. *)
Lemma planb5_forced_inj_mul_eq : forall x y : Z,
  inject_Z (x * y) == inject_Z x * inject_Z y.
Proof.
  intros x y. unfold inject_Z, Qmult, Qeq. cbn. ring.
Qed.

(* the square of an inject form: at the fixed exponent 2 the Qpower     *)
(* face is the inject face of the squared integer, with no nonzero      *)
(* side condition.                                                      *)
Lemma planb5_forced_inj_sq_eq : forall z : Z,
  Qpower (inject_Z z) (Z.of_nat 2) == inject_Z (z * z).
Proof.
  intros z. unfold inject_Z, Qpower, Qeq. cbn. ring.
Qed.

(* inject_Z commutes with nat-indexed powers on positive bases. *)
Lemma planb5_forced_inj_pow_eq : forall (z : Z) (k : nat),
  (0 < z)%Z ->
  inject_Z (z ^ Z.of_nat k) == Qpower (inject_Z z) (Z.of_nat k).
Proof.
  intros z k Hz. induction k as [|k IH].
  - cbn [Z.of_nat]. rewrite Z.pow_0_r, Qpower_0_r. reflexivity.
  - assert (Hne : ~ (inject_Z z == 0)%Q).
    { intro Hc. unfold inject_Z, Qeq in Hc. cbn [Qnum Qden] in Hc. lia. }
    assert (Hs : (Z.of_nat (Datatypes.S k) = Z.of_nat k + 1)%Z) by lia.
    rewrite Hs.
    rewrite Qpower_plus by exact Hne.
    replace (Qpower (inject_Z z) 1) with (inject_Z z) by reflexivity.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
    rewrite (planb5_forced_inj_mul_eq (z ^ Z.of_nat k) z).
    rewrite IH. reflexivity.
Qed.

(* ================================================================== *)
(* Section 12. The prescribed band tables and the verbatim endpoint    *)
(*            criterion (item a: eleven band endpoint pairs, checked   *)
(*            by a boolean vm_compute face).                           *)
(* ================================================================== *)

(* The prescribed band lower endpoints lo_k, k = 1..11; outside the     *)
(* table domain the function returns 0 and no claim is made.            *)
Definition planb5_forced_blo : nat -> nat :=
  fun k =>
    match k with
    | S k' => nth k' [1%nat; 3%nat; 9%nat; 33%nat; 129%nat; 513%nat;
                      2049%nat; 8193%nat; 32769%nat; 131073%nat;
                      524289%nat] 0%nat
    | _ => 0%nat
    end.

(* The prescribed band upper endpoints hi_k, k = 1..11.                 *)
Definition planb5_forced_bhi : nat -> nat :=
  fun k =>
    match k with
    | S k' => nth k' [2%nat; 7%nat; 25%nat; 89%nat; 313%nat; 1090%nat;
                      3796%nat; 13220%nat; 46037%nat; 160312%nat;
                      558240%nat] 0%nat
    | _ => 0%nat
    end.

(* The q3min table k = 1..12: the least q with 3^14 * q^20 >=           *)
(* 2^(36*k - 28), the limb-3 floor of the F-extended interval k; the    *)
(* entry q3min(12) = 558241 closes the top of the range [1, 558240].    *)
Definition planb5_forced_q3m : nat -> nat :=
  fun k =>
    match k with
    | S k' => nth k' [1%nat; 3%nat; 8%nat; 26%nat; 90%nat; 314%nat;
                      1091%nat; 3797%nat; 13221%nat; 46038%nat;
                      160313%nat; 558241%nat] 0%nat
    | _ => 0%nat
    end.

(* Item (a) header criterion: the eleven band endpoint pairs verbatim,  *)
(* as a boolean certificate over the tables.                            *)
Definition planb5_forced_band_endpoints_check : bool :=
  (Nat.eqb (planb5_forced_blo 1) 1) && (Nat.eqb (planb5_forced_bhi 1) 2) &&
  (Nat.eqb (planb5_forced_blo 2) 3) && (Nat.eqb (planb5_forced_bhi 2) 7) &&
  (Nat.eqb (planb5_forced_blo 3) 9) && (Nat.eqb (planb5_forced_bhi 3) 25) &&
  (Nat.eqb (planb5_forced_blo 4) 33) && (Nat.eqb (planb5_forced_bhi 4) 89) &&
  (Nat.eqb (planb5_forced_blo 5) 129) && (Nat.eqb (planb5_forced_bhi 5) 313) &&
  (Nat.eqb (planb5_forced_blo 6) 513) && (Nat.eqb (planb5_forced_bhi 6) 1090) &&
  (Nat.eqb (planb5_forced_blo 7) 2049) && (Nat.eqb (planb5_forced_bhi 7) 3796) &&
  (Nat.eqb (planb5_forced_blo 8) 8193) && (Nat.eqb (planb5_forced_bhi 8) 13220) &&
  (Nat.eqb (planb5_forced_blo 9) 32769) && (Nat.eqb (planb5_forced_bhi 9) 46037) &&
  (Nat.eqb (planb5_forced_blo 10) 131073) && (Nat.eqb (planb5_forced_bhi 10) 160312) &&
  (Nat.eqb (planb5_forced_blo 11) 524289) && (Nat.eqb (planb5_forced_bhi 11) 558240).

Example planb5_forced_band_endpoints_ok : planb5_forced_band_endpoints_check = true.
Proof. vm_compute. reflexivity. Qed.

(* The ten adjacencies of the F-extension tiling: the extended          *)
(* interval k+1 starts exactly one step after the band top hi_k,        *)
(* q3min(k+1) = hi_k + 1 for k = 1..10 (boolean certificate).           *)
Definition planb5_forced_adj_check : bool :=
  (Nat.eqb (planb5_forced_q3m 2) (planb5_forced_bhi 1 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 3) (planb5_forced_bhi 2 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 4) (planb5_forced_bhi 3 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 5) (planb5_forced_bhi 4 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 6) (planb5_forced_bhi 5 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 7) (planb5_forced_bhi 6 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 8) (planb5_forced_bhi 7 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 9) (planb5_forced_bhi 8 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 10) (planb5_forced_bhi 9 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 11) (planb5_forced_bhi 10 + 1)).

Example planb5_forced_adj_ok : planb5_forced_adj_check = true.
Proof. vm_compute. reflexivity. Qed.

(* The top entry of the q3min table: 558241, one step past the range    *)
(* end 558240 (the limb-3 face at n = 12 needs q >= 558241, so the      *)
(* forced route ends exactly at the prescribed top).                    *)
Example planb5_forced_q3m_top : Nat.eqb (planb5_forced_q3m 12) 558241 = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 13. The coprime forced lemma (item c: gcd = 1, b nonzero,   *)
(*            1 <= q < |b| force the limb-2 face for every p).        *)
(* ================================================================== *)

(* The chain: if the linear form vanished, then b divides a*q (the      *)
(* relation a*q = (-p)*b), the Gauss theorem with gcd a b = 1 gives     *)
(* b | q, hence |b| <= q, contradicting q < |b|.  The conclusion holds  *)
(* for every p; the prescribed nonzero-p face is the main instance.     *)
Lemma planb5_forced_limb2 : forall (a b : Z) (q : nat) (p : Z),
  (Z.gcd a b = 1)%Z ->
  (b <> 0)%Z ->
  (1 <= q)%nat ->
  (Z.of_nat q < Z.abs b)%Z ->
  (1 <= Z.abs (a * Z.of_nat q + b * p))%Z.
Proof.
  intros a b q p Hcop Hb Hq Hlt.
  rewrite Z.gcd_comm in Hcop.
  destruct (Z.eq_dec (a * Z.of_nat q + b * p) 0) as [H0 | Hne].
  - (* the vanishing case is impossible: the divisibility chain *)
    assert (Hdiv : Z.divide b (a * Z.of_nat q)).
    { exists (-p)%Z.
      assert (Haux : (b * p + (-p) * b = 0)%Z) by ring.
      lia. }
    destruct (Z.gauss b a (Z.of_nat q) Hdiv Hcop) as [z Hz].
    (* z is nonzero: q = z * b with q >= 1 *)
    assert (Hz0 : (z <> 0)%Z).
    { intro Hzz. rewrite Hzz in Hz. rewrite Z.mul_0_l in Hz. lia. }
    assert (Habsz : (1 <= Z.abs z)%Z).
    { destruct (Z.le_gt_cases 0 z) as [Hpos | Hneg].
      - rewrite Z.abs_eq by lia. lia.
      - rewrite Z.abs_neq by lia. lia. }
    assert (Habsb : (1 <= Z.abs b)%Z).
    { destruct (Z.le_gt_cases 0 b) as [Hpos | Hneg].
      - rewrite Z.abs_eq by lia. lia.
      - rewrite Z.abs_neq by lia. lia. }
    assert (Habsq : (Z.abs (Z.of_nat q) = Z.abs z * Z.abs b)%Z).
    { rewrite <- Z.abs_mul. rewrite Hz. reflexivity. }
    pose proof (Z.abs_eq (Z.of_nat q) ltac:(lia)) as Hqpos.
    pose proof (Z.mul_le_mono_nonneg 1 (Z.abs z) (Z.abs b) (Z.abs b)
                  ltac:(lia) ltac:(lia)
                  ltac:(apply Z.abs_nonneg) ltac:(lia)) as Hge.
    rewrite Z.mul_1_l in Hge.
    rewrite <- Hqpos in Hlt.
    rewrite Habsq in Hlt.
    lia.
  - (* the nonvanishing case: the absolute value is at least 1 *)
    destruct (Z.le_gt_cases 0 (a * Z.of_nat q + b * p)) as [Hpos | Hneg].
    + rewrite Z.abs_eq by lia. lia.
    + rewrite Z.abs_neq by lia. lia.
Qed.

(* ================================================================== *)
(* Section 14. The per-band reduced pairs and their certificates       *)
(*            (item d: d_k / g_k / h_k, verified per band).           *)
(* ================================================================== *)

(* The per-band gcd d_k = gcd(|A_k|, |B_k|), k = 1..11.                 *)
Definition planb5_forced_dk : nat -> Z :=
  fun k =>
    match k with
    | S k' => nth k' [8%Z; 32%Z; 2240%Z; 352%Z; 2688%Z; 32%Z; 160%Z;
                      17600%Z; 30464%Z; 512%Z; 128%Z] 0%Z
    | _ => 0%Z
    end.

(* The reduced numerator pair g_k = A_k / d_k (signed), k = 1..11.      *)
Definition planb5_forced_gk : nat -> Z :=
  fun k =>
    match k with
    | S k' => nth k' [2818%Z; 96188954%Z; 202909760012%Z;
                      11363042315305984%Z; 16454631467853697072832%Z;
                      7210732800456956809618314752%Z;
                      8419827893461487859350600476672%Z;
                      3869345558286928574831731815957397504%Z;
                      8806829371930926381963609226384365961216%Z;
                      2644791314655510283632140858092780624217325568%Z;
                      13880603067623515419652591507363337279452871413465088%Z] 0%Z
    | _ => 0%Z
    end.

(* The reduced denominator pair h_k = B_k / d_k (signed), k = 1..11;    *)
(* the M1-style size value is |h_k| = |B_k| / gcd(|A_k|,|B_k|).         *)
Definition planb5_forced_hk : nat -> Z :=
  fun k =>
    match k with
    | S k' => nth k' [(-897)%Z; (-30617895)%Z; (-64588182615)%Z;
                      (-3616968706086645)%Z; (-5237671869728730747315)%Z;
                      (-2295247537015180093651920615)%Z;
                      (-2680114458454832168671987059975)%Z;
                      (-1231650944264068208514063627819193845)%Z;
                      (-2803300855019397860902949284200418731975)%Z;
                      (-841863222347873579452565675390633469475782825)%Z;
                      (-4418333182617616843296580418075545009457503490032575)%Z] 0%Z
    | _ => 0%Z
    end.

(* The per-band reduced-pair certificate: the signed splits             *)
(* A_k = d_k * g_k and B_k = d_k * h_k, the coprimality                 *)
(* gcd(g_k, h_k) = 1 of the reduced pair, the size criterion            *)
(* hi_k < |h_k| (the reduced size value dominates the band top), and    *)
(* the positivity of d_k.                                               *)
Definition planb5_forced_band_ok (k : nat) : bool :=
  (Z.eqb (planb3_g1_A k) (planb5_forced_dk k * planb5_forced_gk k)) &&
  (Z.eqb (planb3_g1_B k) (planb5_forced_dk k * planb5_forced_hk k)) &&
  (Z.eqb (Z.gcd (planb5_forced_gk k) (planb5_forced_hk k)) 1) &&
  (Z.ltb (Z.of_nat (planb5_forced_bhi k)) (Z.abs (planb5_forced_hk k))) &&
  (Z.ltb 0 (planb5_forced_dk k)).

(* The per-band extractor: the certificate holds at every band          *)
(* index 1..11 (one vm_compute case per concrete index).                *)
Lemma planb5_forced_band_ok_at : forall k : nat,
  (1 <= k <= 11)%nat -> planb5_forced_band_ok k = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The all-bands certificate: the eleven per-band checks concatenated.  *)
Example planb5_forced_band_ok_all :
  (planb5_forced_band_ok 1 && planb5_forced_band_ok 2 &&
   planb5_forced_band_ok 3 && planb5_forced_band_ok 4 &&
   planb5_forced_band_ok 5 && planb5_forced_band_ok 6 &&
   planb5_forced_band_ok 7 && planb5_forced_band_ok 8 &&
   planb5_forced_band_ok 9 && planb5_forced_band_ok 10 &&
   planb5_forced_band_ok 11)%bool = true.
Proof. vm_compute. reflexivity. Qed.

(* Reflection bridges from the boolean certificate to the Prop faces    *)
(* consumed by the forced escape theorem (proof positions only).        *)
Lemma planb5_forced_split_AB : forall k : nat,
  planb5_forced_band_ok k = true ->
  (planb3_g1_A k = planb5_forced_dk k * planb5_forced_gk k)%Z /\
  (planb3_g1_B k = planb5_forced_dk k * planb5_forced_hk k)%Z.
Proof.
  intros k Hok. unfold planb5_forced_band_ok in Hok.
  repeat rewrite andb_true_iff in Hok.
  (* the repeated rewrite leaves a LEFT-nested conjunction on 9.3:        *)
  (* (((a /\ b) /\ c) /\ d) /\ e - peel from the outside in           *)
  destruct Hok as [H12 Hok].
  destruct H12 as [H123 H4].
  destruct H123 as [H12b H3].
  destruct H12b as [H1 H2].
  split; apply (proj1 (Z.eqb_eq _ _)); assumption.
Qed.

Lemma planb5_forced_coprime_gk_hk : forall k : nat,
  planb5_forced_band_ok k = true ->
  (Z.gcd (planb5_forced_gk k) (planb5_forced_hk k) = 1)%Z.
Proof.
  intros k Hok. unfold planb5_forced_band_ok in Hok.
  repeat rewrite andb_true_iff in Hok.
  destruct Hok as [H12 Hok].
  destruct H12 as [H123 H4].
  destruct H123 as [H12b H3].
  apply (proj1 (Z.eqb_eq _ _)). exact H3.
Qed.

Lemma planb5_forced_hk_abs_gt_hi : forall k : nat,
  planb5_forced_band_ok k = true ->
  (Z.of_nat (planb5_forced_bhi k) < Z.abs (planb5_forced_hk k))%Z.
Proof.
  intros k Hok. unfold planb5_forced_band_ok in Hok.
  repeat rewrite andb_true_iff in Hok.
  destruct Hok as [H12 Hok].
  destruct H12 as [H123 H4].
  apply (proj1 (Z.ltb_lt _ _)). exact H4.
Qed.

Lemma planb5_forced_dk_pos : forall k : nat,
  planb5_forced_band_ok k = true -> (0 < planb5_forced_dk k)%Z.
Proof.
  intros k Hok. unfold planb5_forced_band_ok in Hok.
  repeat rewrite andb_true_iff in Hok.
  destruct Hok as [H12 Hok].
  apply (proj1 (Z.ltb_lt _ _)). exact Hok.
Qed.

(* ================================================================== *)
(* Section 15. The window-end N1 faces at the band endpoints (item b:  *)
(*            limb 1 at hi_k and limb 3 at lo_k, eleven bands).       *)
(* ================================================================== *)

(* The band-top Z face for limb 1: 2*hi_k <= 2^(2*k), boolean form.     *)
Lemma planb5_forced_limb1Z_ok : forall k : nat,
  (1 <= k <= 11)%nat ->
  (Z.of_nat (2 * planb5_forced_bhi k) <=? 2 ^ Z.of_nat (2 * k))%Z = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The band-bottom Z face for limb 3 at the q3min floor:                *)
(* 2^(18*k) * 2^(18*k) <= 2^28 * 3^14 * q3min(k)^20, boolean form.      *)
Lemma planb5_forced_limb3Z_ok : forall k : nat,
  (1 <= k <= 11)%nat ->
  ((2 ^ Z.of_nat (18 * k) * 2 ^ Z.of_nat (18 * k) <=?
    35831808 ^ 2 * Z.of_nat (planb5_forced_q3m k) ^ Z.of_nat 20)%Z) = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The prescribed-bottom Z face for limb 3 at lo_k: the same face at    *)
(* the band lower endpoint, boolean form (consumed by the N1 faces).    *)
Lemma planb5_forced_limb3Zlo_ok : forall k : nat,
  (1 <= k <= 11)%nat ->
  ((2 ^ Z.of_nat (18 * k) * 2 ^ Z.of_nat (18 * k) <=?
    35831808 ^ 2 * Z.of_nat (planb5_forced_blo k) ^ Z.of_nat 20)%Z) = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The eleven window-end N1 faces: the limb-1 slot face at the band     *)
(* top hi_k and the limb-3 slot face at the band bottom lo_k, per       *)
(* band, all literals, piu_mu_and2-carried.                             *)

Example planb5_forced_N1_1 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 2))) (piu_mu_epos (2 * 1)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 1)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 1)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_1 = 2 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_1 = 1 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 1))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 1) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 1) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 1) * 2 ^ Z.of_nat (18 * 1))%Z
                (35831808 ^ 2 * (Z.of_nat 1) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_2 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 7))) (piu_mu_epos (2 * 2)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 2)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 3)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_2 = 7 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_2 = 3 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 2))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 3) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 3) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 2) * 2 ^ Z.of_nat (18 * 2))%Z
                (35831808 ^ 2 * (Z.of_nat 3) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_3 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 25))) (piu_mu_epos (2 * 3)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 3)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 9)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_3 = 25 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_3 = 9 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 3))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 9) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 9) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 3) * 2 ^ Z.of_nat (18 * 3))%Z
                (35831808 ^ 2 * (Z.of_nat 9) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_4 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 89))) (piu_mu_epos (2 * 4)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 4)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 33)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_4 = 89 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_4 = 33 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 4))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 33) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 33) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 4) * 2 ^ Z.of_nat (18 * 4))%Z
                (35831808 ^ 2 * (Z.of_nat 33) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_5 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 313))) (piu_mu_epos (2 * 5)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 5)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 129)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_5 = 313 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_5 = 129 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 5))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 129) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 129) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 5) * 2 ^ Z.of_nat (18 * 5))%Z
                (35831808 ^ 2 * (Z.of_nat 129) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_6 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 1090))) (piu_mu_epos (2 * 6)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 6)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 513)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_6 = 1090 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_6 = 513 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 6))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 513) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 513) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 6) * 2 ^ Z.of_nat (18 * 6))%Z
                (35831808 ^ 2 * (Z.of_nat 513) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_7 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 3796))) (piu_mu_epos (2 * 7)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 7)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 2049)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_7 = 3796 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_7 = 2049 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 7))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 2049) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 2049) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 7) * 2 ^ Z.of_nat (18 * 7))%Z
                (35831808 ^ 2 * (Z.of_nat 2049) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_8 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 13220))) (piu_mu_epos (2 * 8)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 8)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 8193)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_8 = 13220 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_8 = 8193 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 8))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 8193) 20%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 8193) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 8) * 2 ^ Z.of_nat (18 * 8))%Z
                (35831808 ^ 2 * (Z.of_nat 8193) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_9 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 46037))) (piu_mu_epos (2 * 9)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 9)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 32769)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_9 = 46037 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_9 = 32769 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 9))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 32769) 20%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 32769) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 9) * 2 ^ Z.of_nat (18 * 9))%Z
                (35831808 ^ 2 * (Z.of_nat 32769) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_10 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 160312))) (piu_mu_epos (2 * 10)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 10)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 131073)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_10 = 160312 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_10 = 131073 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 10))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 131073) 20%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 131073) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 10) * 2 ^ Z.of_nat (18 * 10))%Z
                (35831808 ^ 2 * (Z.of_nat 131073) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_11 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 558240))) (piu_mu_epos (2 * 11)))
  (piu_mu_QleT (Qpower (piu_mu_epos (18 * 11)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 524289)) (Z.of_nat (18 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_11 = 558240 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_11 = 524289 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * 11))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 524289) 20%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 524289) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * 11) * 2 ^ Z.of_nat (18 * 11))%Z
                (35831808 ^ 2 * (Z.of_nat 524289) ^ Z.of_nat 20)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

(* ================================================================== *)
(* Section 16. The F-extension tiling and the forced escape theorem    *)
(*            (item e: the eleven extended intervals [q3min(k), hi_k] *)
(*            tile [1, 558240]; zero premises, zero dodge).           *)
(* ================================================================== *)

(* The generic interval witness: at band index k with the table values  *)
(* vlo = q3min(k) and vhi = hi_k, every q with vlo <= q <= vhi admits   *)
(* the full three-limb witness n = k.  Limb 1 comes from the band-top    *)
(* face and q <= vhi; limb 2 from the coprime forced lemma at the       *)
(* reduced pair (g_k, h_k), scaled by d_k; limb 3 from the q3min floor   *)
(* face and the pow monotonicity vlo^20 <= q^20.                        *)
Lemma planb5_forced_witness : forall (k vlo vhi : nat) (p : Z) (q : nat),
  (1 <= k <= 11)%nat ->
  (1 <= q)%nat ->
  planb5_forced_band_ok k = true ->
  planb5_forced_q3m k = vlo%nat ->
  planb5_forced_bhi k = vhi%nat ->
  (vlo <= q)%nat ->
  (q <= vhi)%nat ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A n * Z.of_nat q + planb3_g1_B n * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (18 * n)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q)).
Proof.
  intros k vlo vhi p q Hk Hq1 Hok Hqlo Hbhi Hlo Hhi.
  exists k.
  apply piu_mu_and3_i.
  - (* limb 1: 2*q <= 2^(2*k), from the band-top face and q <= vhi *)
    pose proof (proj1 (Z.leb_le _ _) (planb5_forced_limb1Z_ok k ltac:(lia))) as H1.
    rewrite Hbhi in H1.
    unfold piu_mu_epos. apply piu_mu_Zle_Qle. lia.
  - (* limb 2: the coprime forced lemma at the reduced pair, scaled    *)
    (* by d_k through the signed splits.                              *)
    pose proof (planb5_forced_split_AB k Hok) as [HsA HsB].
    pose proof (planb5_forced_coprime_gk_hk k Hok) as Hcop.
    pose proof (planb5_forced_hk_abs_gt_hi k Hok) as Hsize.
    pose proof (planb5_forced_dk_pos k Hok) as Hdp.
    rewrite Hbhi in Hsize.
    assert (Hhne : (planb5_forced_hk k <> 0)%Z).
    { intro Hzz.
      assert (Habs0 : (Z.abs (planb5_forced_hk k) = 0)%Z)
        by (rewrite Hzz; reflexivity).
      rewrite Habs0 in Hsize. lia. }
    apply piu_mu_ZleT_i.
    assert (Hfact : (planb3_g1_A k * Z.of_nat q + planb3_g1_B k * p
                     = planb5_forced_dk k * (planb5_forced_gk k * Z.of_nat q
                        + planb5_forced_hk k * p))%Z)
      by (rewrite HsA, HsB; ring).
    rewrite Hfact, Z.abs_mul.
    rewrite (Z.abs_eq (planb5_forced_dk k)) by lia.
    pose proof (planb5_forced_limb2 (planb5_forced_gk k) (planb5_forced_hk k) q p
                  Hcop Hhne ltac:(lia) ltac:(lia)) as Hl2.
    assert (Hfin : (1 <= planb5_forced_dk k
                     * Z.abs (planb5_forced_gk k * Z.of_nat q
                        + planb5_forced_hk k * p))%Z).
    { pose proof (Z.mul_le_mono_nonneg 1
                    (Z.abs (planb5_forced_gk k * Z.of_nat q
                       + planb5_forced_hk k * p))
                    (planb5_forced_dk k) (planb5_forced_dk k)
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hm.
      rewrite Z.mul_1_l in Hm.
      rewrite (Z.mul_comm (Z.abs (planb5_forced_gk k * Z.of_nat q
                  + planb5_forced_hk k * p)) (planb5_forced_dk k)) in Hm.
      lia. }
    exact Hfin.
  - (* limb 3: the q3min floor face and the pow monotonicity to q *)
    pose proof (proj1 (Z.leb_le _ _) (planb5_forced_limb3Z_ok k ltac:(lia))) as H3c.
    rewrite Hqlo in H3c.
    pose proof (Nat.pow_le_mono_l vlo q 20%nat ltac:(lia)) as Hmono.
    pose proof (proj1 (Nat2Z.inj_le _ _) Hmono) as HmonoZ.
    rewrite !Nat2Z.inj_pow in HmonoZ.
    pose proof (Z.mul_le_mono_nonneg (35831808 ^ 2)%Z (35831808 ^ 2)%Z
                  (Z.of_nat vlo ^ Z.of_nat 20) (Z.of_nat q ^ Z.of_nat 20)
                  ltac:(apply Z.pow_nonneg; lia) ltac:(lia)
                  ltac:(apply Z.pow_nonneg; lia) ltac:(exact HmonoZ)) as HmonoM.
    assert (HZ : (2 ^ Z.of_nat (18 * k) * 2 ^ Z.of_nat (18 * k)
                  <= 35831808 ^ 2 * Z.of_nat q ^ Z.of_nat 20)%Z) by lia.
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (18 * k))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat q) 20%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat q) ^ Z.of_nat 20)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (18 * k) * 2 ^ Z.of_nat (18 * k))%Z
                (35831808 ^ 2 * (Z.of_nat q) ^ Z.of_nat 20)%Z HZ) as [HQ].
    exact HQ.
Qed.

(* The mission theorem: the forced route over the whole bounded range.  *)
(* The eleven extended intervals [q3min(k), hi_k] tile [1, 558240] by   *)
(* the ten adjacencies (q3min(k+1) = hi_k + 1, Section 12); q is        *)
(* dispatched by one le_lt_dec cut per boundary and each branch         *)
(* instantiates the interval witness at its band index.  Zero premises  *)
(* beyond the range bound; the dodge determinant is never used.         *)
Theorem planb5_esc18_forced : forall (p : Z) (q : nat),
  (1 <= q)%nat -> (q <= 558240)%nat ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A n * Z.of_nat q + planb3_g1_B n * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (18 * n)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q)).
Proof.
  intros p q Hq1 Hq2.
  destruct (le_lt_dec q 2) as [Hc1 | Hc1].
  - (* interval 1: [1, 2], witness n = 1 *)
    exact (planb5_forced_witness 1%nat 1%nat 2%nat p q
             ltac:(lia) ltac:(lia)
             (planb5_forced_band_ok_at 1%nat ltac:(lia))
             ltac:(reflexivity) ltac:(reflexivity)
             ltac:(lia) ltac:(lia)).
  - destruct (le_lt_dec q 7) as [Hc2 | Hc2].
    { (* interval 2: [3, 7], witness n = 2 *)
      exact (planb5_forced_witness 2%nat 3%nat 7%nat p q
               ltac:(lia) ltac:(lia)
               (planb5_forced_band_ok_at 2%nat ltac:(lia))
               ltac:(reflexivity) ltac:(reflexivity)
               ltac:(lia) ltac:(lia)). }
    { destruct (le_lt_dec q 25) as [Hc3 | Hc3].
      { (* interval 3: [8, 25], witness n = 3 *)
        exact (planb5_forced_witness 3%nat 8%nat 25%nat p q
                 ltac:(lia) ltac:(lia)
                 (planb5_forced_band_ok_at 3%nat ltac:(lia))
                 ltac:(reflexivity) ltac:(reflexivity)
                 ltac:(lia) ltac:(lia)). }
      { destruct (le_lt_dec q 89) as [Hc4 | Hc4].
        { (* interval 4: [26, 89], witness n = 4 *)
          exact (planb5_forced_witness 4%nat 26%nat 89%nat p q
                   ltac:(lia) ltac:(lia)
                   (planb5_forced_band_ok_at 4%nat ltac:(lia))
                   ltac:(reflexivity) ltac:(reflexivity)
                   ltac:(lia) ltac:(lia)). }
        { destruct (le_lt_dec q 313) as [Hc5 | Hc5].
          { (* interval 5: [90, 313], witness n = 5 *)
            exact (planb5_forced_witness 5%nat 90%nat 313%nat p q
                     ltac:(lia) ltac:(lia)
                     (planb5_forced_band_ok_at 5%nat ltac:(lia))
                     ltac:(reflexivity) ltac:(reflexivity)
                     ltac:(lia) ltac:(lia)). }
          { destruct (le_lt_dec q 1090) as [Hc6 | Hc6].
            { (* interval 6: [314, 1090], witness n = 6 *)
              exact (planb5_forced_witness 6%nat 314%nat 1090%nat p q
                       ltac:(lia) ltac:(lia)
                       (planb5_forced_band_ok_at 6%nat ltac:(lia))
                       ltac:(reflexivity) ltac:(reflexivity)
                       ltac:(lia) ltac:(lia)). }
            { destruct (le_lt_dec q 3796) as [Hc7 | Hc7].
              { (* interval 7: [1091, 3796], witness n = 7 *)
                exact (planb5_forced_witness 7%nat 1091%nat 3796%nat p q
                         ltac:(lia) ltac:(lia)
                         (planb5_forced_band_ok_at 7%nat ltac:(lia))
                         ltac:(reflexivity) ltac:(reflexivity)
                         ltac:(lia) ltac:(lia)). }
              { destruct (le_lt_dec q 13220) as [Hc8 | Hc8].
                { (* interval 8: [3797, 13220], witness n = 8 *)
                  exact (planb5_forced_witness 8%nat 3797%nat 13220%nat p q
                           ltac:(lia) ltac:(lia)
                           (planb5_forced_band_ok_at 8%nat ltac:(lia))
                           ltac:(reflexivity) ltac:(reflexivity)
                           ltac:(lia) ltac:(lia)). }
                { destruct (le_lt_dec q 46037) as [Hc9 | Hc9].
                  { (* interval 9: [13221, 46037], witness n = 9 *)
                    exact (planb5_forced_witness 9%nat 13221%nat 46037%nat p q
                             ltac:(lia) ltac:(lia)
                             (planb5_forced_band_ok_at 9%nat ltac:(lia))
                             ltac:(reflexivity) ltac:(reflexivity)
                             ltac:(rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc18_e13221); exact Hc8)
                             ltac:(lia)). }
                  { destruct (le_lt_dec q 160312) as [Hc10 | Hc10].
                    { (* interval 10: [46038, 160312], witness n = 10 *)
                      exact (planb5_forced_witness 10%nat 46038%nat 160312%nat p q
                               ltac:(lia) ltac:(lia)
                               (planb5_forced_band_ok_at 10%nat ltac:(lia))
                               ltac:(reflexivity) ltac:(reflexivity)
                               ltac:(rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc18_e46038); exact Hc9)
                               ltac:(lia)). }
                    { (* interval 11: [160313, 558240], witness n = 11 *)
                      exact (planb5_forced_witness 11%nat 160313%nat 558240%nat p q
                               ltac:(lia) ltac:(lia)
                               (planb5_forced_band_ok_at 11%nat ltac:(lia))
                               ltac:(reflexivity) ltac:(reflexivity)
                               ltac:(rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc18_e160313); exact Hc10)
                               ltac:(lia)). } } } } } } } } }
Qed.

(* ================================================================== *)
(* Section 17. The two-layer dodge chain: the Z.eqb selection          *)
(*             function, the Tier-2 contrapositive upgrade, and the    *)
(*             Tier-1 same-index reduction to the sigT witness.        *)
(* ================================================================== *)

(* The same-index selection function m = if Z.eqb (A n * Z.of_nat q +   *)
(* B n * p) 0 then S n else n: when the first indicator vanishes at n   *)
(* the pick steps to S n, otherwise it keeps n.  Transparent by         *)
(* construction.                                                        *)

Definition planb5_esc18_pick (A B : nat -> Z) (p : Z) (q n : nat) : nat :=
  if Z.eqb (A n * Z.of_nat q + B n * p) 0 then S n else n.

(* Tier 2.  The Delta n nonzero contrapositive upgrade of the dodge     *)
(* pair: at q >= 1 the two indicators cannot vanish together, so at     *)
(* least one of them is nonzero.  The Delta slot is an explicit         *)
(* positional premise here and stays one everywhere below - never       *)
(* discharged, never a global axiom.                                    *)

Lemma planb5_esc18_dodge_upgrade :
  forall (A B : nat -> Z) (p : Z) (q n : nat),
  (1 <= q)%nat ->
  (A n * B (S n) - A (S n) * B n <> 0)%Z ->
  (A n * Z.of_nat q + B n * p <> 0 \/
   A (S n) * Z.of_nat q + B (S n) * p <> 0)%Z.
Proof.
  intros A B p q n Hq Hdelta.
  destruct (Z.eq_dec (A n * Z.of_nat q + B n * p) 0) as [Hz | Hnz].
  - (* first indicator zero: the dodge contrapositive forces the second  *)
    right. exact (planb5_dodge_contra A B p q n Hq Hdelta Hz).
  - (* first indicator nonzero *)
    left. exact Hnz.
Qed.

(* Tier 1.  The same-index reduction: with the window faces held at     *)
(* both n and S n, the pick index carries the full three-limb escape    *)
(* body - limb 1 at the pick index, the nonzero limb 2 at the pick      *)
(* index via the Tier-2 upgrade, limb 3 at the pick index - sigT        *)
(* carried.                                                             *)

Lemma planb5_esc18_reduce :
  forall (A B : nat -> Z) (p : Z) (q n : nat),
  (1 <= q)%nat ->
  (A n * B (S n) - A (S n) * B n <> 0)%Z ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)) ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * S n)) ->
  piu_mu_QleT (Qpower (piu_mu_epos (18 * n)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q ->
  piu_mu_QleT (Qpower (piu_mu_epos (18 * S n)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q ->
  sigT (fun m : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * m)))
    (piu_mu_ZleT 1 (Z.abs (A m * Z.of_nat q + B m * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (18 * m)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q)).
Proof.
  intros A B p q n Hq Hdelta Hl1n Hl1sn Hl3n Hl3sn.
  pose proof (planb5_esc18_dodge_upgrade A B p q n Hq Hdelta) as Hup.
  destruct (Z.eqb_spec (A n * Z.of_nat q + B n * p) 0) as [Hz | Hnz].
  - (* first indicator zero at n: the pick selects S n *)
    exists (planb5_esc18_pick A B p q n).
    assert (Hpick : planb5_esc18_pick A B p q n = S n).
    { unfold planb5_esc18_pick.
      rewrite (proj2 (Z.eqb_eq _ _) Hz). reflexivity. }
    rewrite Hpick.
    apply piu_mu_and3_i.
    + (* limb 1 at the shifted index S n *)
      exact Hl1sn.
    + (* limb 2 at the shifted index S n, via the Tier-2 upgrade *)
      apply piu_mu_ZleT_i.
      destruct Hup as [Hup1 | Hup2].
      * exfalso. exact (Hup1 Hz).
      * destruct (Z.le_gt_cases 0 (A (S n) * Z.of_nat q + B (S n) * p))
          as [Hp | Hn].
        -- rewrite Z.abs_eq by lia. lia.
        -- rewrite Z.abs_neq by lia. lia.
    + (* limb 3 at the shifted index S n *)
      exact Hl3sn.
  - (* first indicator nonzero at n: the pick keeps n *)
    exists (planb5_esc18_pick A B p q n).
    assert (Hpick : planb5_esc18_pick A B p q n = n).
    { unfold planb5_esc18_pick.
      rewrite (proj2 (Z.eqb_neq _ _) Hnz). reflexivity. }
    rewrite Hpick.
    apply piu_mu_and3_i.
    + (* limb 1 at the index n *)
      exact Hl1n.
    + (* limb 2 at the index n: the first indicator is nonzero *)
      apply piu_mu_ZleT_i.
      destruct (Z.le_gt_cases 0 (A n * Z.of_nat q + B n * p)) as [Hp | Hn].
      * rewrite Z.abs_eq by lia. lia.
      * rewrite Z.abs_neq by lia. lia.
    + (* limb 3 at the index n *)
      exact Hl3n.
Qed.

(* ================================================================== *)
(* Section 18. The route faces: the Q-face bridges at the shifted      *)
(*             witness, Route W with the explicit Delta slot, and the  *)
(*             global dispatch over the full modulus range.            *)
(* ================================================================== *)

(* The limb-1 Q face at the shifted witness S (nlo q): the non-strict   *)
(* E1_lo limb lifted one witness step (Section 7) carried to the        *)
(* non-strict Q face by the Nat2Z monotone lift and the Z-to-Q bridge.  *)

Lemma planb5_esc18_E1p_Q : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
              (piu_mu_epos (2 * S (planb_b_nlo q))).
Proof.
  intros q Hq.
  pose proof (planb5_esc_E1p_nat q Hq) as He.
  pose proof (proj1 (Nat2Z.inj_le _ _) He) as Hz.
  rewrite Nat2Z.inj_pow in Hz.
  change (Z.of_nat 2) with 2%Z in Hz.
  exact (piu_mu_Zle_Qle (Z.of_nat (2 * q))
           (2 ^ Z.of_nat (2 * S (planb_b_nlo q))) Hz).
Qed.

(* The limb-3 squared Q face at the shifted witness S (nlo q): the     *)
(* E3p growth face (Section 10) carried to the squared Q face by the    *)
(* same craft as the Section 6 adapter, with the kappa-square pin.      *)

Lemma planb5_esc18_E3p_Q : forall q : nat, (558241 <= q)%nat ->
  piu_mu_QleT (Qpower (piu_mu_epos (18 * S (planb_b_nlo q))) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q.
Proof.
  intros q Hq.
  pose proof (planb5_esc18_bound1 q Hq) as Hq1.
  pose proof (proj1 (Nat2Z.inj_le _ _) (planb5_esc_E3p_nat q Hq)) as HZ.
  repeat rewrite Nat2Z.inj_mul in HZ.
  repeat rewrite Nat2Z.inj_pow in HZ.
  (* literal repair: keep the numerals folded, as in the Section 6 fix   *)
  change (Z.of_nat 2) with 2%Z in HZ.
  change (Z.of_nat 28) with 28%Z in HZ.
  change (Z.of_nat 3) with 3%Z in HZ.
  change (Z.of_nat 14) with 14%Z in HZ.
  assert (Hz36 : (Z.of_nat (36 * S (planb_b_nlo q))
                  = Z.of_nat (18 * S (planb_b_nlo q))
                    + Z.of_nat (18 * S (planb_b_nlo q)))%Z).
  { replace (36 * S (planb_b_nlo q))%nat
      with ((18 * S (planb_b_nlo q)) + (18 * S (planb_b_nlo q)))%nat
      by lia.
    apply Nat2Z.inj_add. }
  rewrite Hz36 in HZ.
  rewrite Z.pow_add_r in HZ by lia.
  rewrite <- planb5_adapt_kappa2_pin in HZ.
  apply piu_mu_QleT_i.
  unfold piu_mu_epos.
  change (Z.of_nat (18 + 2)) with (Z.of_nat 20).
  rewrite (planb5_adapt_inj_sq_eq (2 ^ Z.of_nat (18 * S (planb_b_nlo q)))%Z).
  change (Qpower (35831808 # 1)%Q (Z.of_nat 2))
    with (inject_Z (35831808 ^ 2)%Z).
  rewrite <- (planb5_adapt_inj_pow_eq (Z.of_nat q) 20%nat ltac:(lia)).
  rewrite <- (planb5_adapt_inj_mul_eq (35831808 ^ 2)%Z
                ((Z.of_nat q) ^ Z.of_nat 20)%Z).
  destruct (piu_mu_Zle_Qle
              (2 ^ Z.of_nat (18 * S (planb_b_nlo q))
               * 2 ^ Z.of_nat (18 * S (planb_b_nlo q)))%Z
              (35831808 ^ 2 * (Z.of_nat q) ^ Z.of_nat 20)%Z HZ) as [HQ].
  exact HQ.
Qed.

(* Route W.  The window supply face with the Delta slot explicit: for   *)
(* every q above the forced-band top, the Hesc18 escape body at the     *)
(* calibration pair is constructed at the pick index of the window      *)
(* witness pair (nlo q, S (nlo q)).  The dodge determinant slot         *)
(* Delta (nlo q) <> 0 enters as an explicit positional premise - it is  *)
(* a premise of this face and of the global dispatch below, never       *)
(* discharged, never a global axiom.                                    *)

Lemma planb5_esc18_window_route :
  forall (p : Z) (q : nat),
  (558241 <= q)%nat ->
  (planb3_g1_A (planb_b_nlo q) * planb3_g1_B (S (planb_b_nlo q))
   - planb3_g1_A (S (planb_b_nlo q)) * planb3_g1_B (planb_b_nlo q)
   <> 0)%Z ->
  sigT (fun m : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * m)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A m * Z.of_nat q + planb3_g1_B m * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (18 * m)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q)).
Proof.
  intros p q Hq Hdelta.
  pose proof (planb5_esc18_bound1 q Hq) as Hq1.
  apply (planb5_esc18_reduce planb3_g1_A planb3_g1_B p q (planb_b_nlo q)).
  - (* the modulus bound, via the glue bridge *)
    exact Hq1.
  - (* the Delta slot, passed verbatim *)
    exact Hdelta.
  - (* limb 1 at the window witness nlo q *)
    exact (planb5_adapt_E1_limb1 q ltac:(exact Hq1)).
  - (* limb 1 at the shifted witness S (nlo q) *)
    exact (planb5_esc18_E1p_Q q ltac:(exact Hq1)).
  - (* limb 3 at the window witness nlo q *)
    exact (planb5_adapt_E3_limb3 q ltac:(exact Hq1)).
  - (* limb 3 at the shifted witness S (nlo q) *)
    exact (planb5_esc18_E3p_Q q ltac:(exact Hq)).
Qed.

(* The global dispatch: q within the forced band goes to Route F (the   *)
(* zero-premise closed face, Section 16), q above the band goes to      *)
(* Route W with the Delta slot explicit.  The slot stays a premise of   *)
(* the global face itself - never discharged, never a global axiom.     *)

Theorem planb5_esc18_global :
  forall (p : Z) (q : nat),
  (1 <= q)%nat ->
  (planb3_g1_A (planb_b_nlo q) * planb3_g1_B (S (planb_b_nlo q))
   - planb3_g1_A (S (planb_b_nlo q)) * planb3_g1_B (planb_b_nlo q)
   <> 0)%Z ->
  sigT (fun m : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * m)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A m * Z.of_nat q + planb3_g1_B m * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (18 * m)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (18 + 2)))%Q)).
Proof.
  intros p q Hq Hdelta.
  destruct (le_lt_dec q 558240) as [Hlow | Hhigh].
  - (* forced band route: zero premises beyond the range bound *)
    exact (planb5_esc18_forced p q Hq Hlow).
  - (* window route above the forced band, the Delta slot explicit *)
    assert (Hq6 : (558241 <= q)%nat)
      by (rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc18_e558241); exact Hhigh).
    exact (planb5_esc18_window_route p q Hq6 Hdelta).
Qed.

(* ================================================================== *)
(* Section 19. Assumption audit over every delivered statement.        *)
(* ================================================================== *)

Print Assumptions planb5_dodge_qΔ.
Print Assumptions planb5_dodge_contra.
Print Assumptions planb5_adapt_inj_mul_eq.
Print Assumptions planb5_adapt_inj_sq_eq.
Print Assumptions planb5_adapt_inj_pow_eq.
Print Assumptions planb5_adapt_kappa2_pin.
Print Assumptions planb5_adapt_E1_limb1.
Print Assumptions planb5_adapt_E3_limb3.
Print Assumptions planb5_esc18_e558241.
Print Assumptions planb5_esc18_e46038.
Print Assumptions planb5_esc18_e160313.
Print Assumptions planb5_esc18_e13221.
Print Assumptions planb5_esc18_bound1.
Print Assumptions planb5_esc_E1p_nat.
Print Assumptions planb5_esc_E3p_diff_z.
Print Assumptions planb5_esc_E3p_noreach_z.
Print Assumptions planb5_esc_E3p_reach.
Print Assumptions planb5_esc_E3p_nat.
Print Assumptions planb5_forced_inj_mul_eq.
Print Assumptions planb5_forced_inj_sq_eq.
Print Assumptions planb5_forced_inj_pow_eq.
Print Assumptions planb5_forced_blo.
Print Assumptions planb5_forced_bhi.
Print Assumptions planb5_forced_q3m.
Print Assumptions planb5_forced_band_endpoints_check.
Print Assumptions planb5_forced_band_endpoints_ok.
Print Assumptions planb5_forced_adj_check.
Print Assumptions planb5_forced_adj_ok.
Print Assumptions planb5_forced_q3m_top.
Print Assumptions planb5_forced_limb2.
Print Assumptions planb5_forced_dk.
Print Assumptions planb5_forced_gk.
Print Assumptions planb5_forced_hk.
Print Assumptions planb5_forced_band_ok.
Print Assumptions planb5_forced_band_ok_at.
Print Assumptions planb5_forced_band_ok_all.
Print Assumptions planb5_forced_split_AB.
Print Assumptions planb5_forced_coprime_gk_hk.
Print Assumptions planb5_forced_hk_abs_gt_hi.
Print Assumptions planb5_forced_dk_pos.
Print Assumptions planb5_forced_limb1Z_ok.
Print Assumptions planb5_forced_limb3Z_ok.
Print Assumptions planb5_forced_limb3Zlo_ok.
Print Assumptions planb5_forced_N1_1.
Print Assumptions planb5_forced_N1_2.
Print Assumptions planb5_forced_N1_3.
Print Assumptions planb5_forced_N1_4.
Print Assumptions planb5_forced_N1_5.
Print Assumptions planb5_forced_N1_6.
Print Assumptions planb5_forced_N1_7.
Print Assumptions planb5_forced_N1_8.
Print Assumptions planb5_forced_N1_9.
Print Assumptions planb5_forced_N1_10.
Print Assumptions planb5_forced_N1_11.
Print Assumptions planb5_forced_witness.
Print Assumptions planb5_esc18_forced.
Print Assumptions planb5_esc18_pick.
Print Assumptions planb5_esc18_dodge_upgrade.
Print Assumptions planb5_esc18_reduce.
Print Assumptions planb5_esc18_E1p_Q.
Print Assumptions planb5_esc18_E3p_Q.
Print Assumptions planb5_esc18_window_route.
Print Assumptions planb5_esc18_global.
