(* ConstructiveWorld-Main - planB wave-5 assembly: the Hesc17 limb-2     *)
(* escape chain - two layers and two routes over the full modulus range. *)

(** * planb5_hesc17_assembly: the two-layer four-piece Hesc17 limb-2 face.

    Mission.  The limb-2 assembly of the planB wave-5 chain, delivered at
      the calibration pair (planb3_g1_A, planb3_g1_B) as two layers and
      two routes.  (a) Tier 1, planb5_esc17_reduce: the same-index
      selection function planb5_esc17_pick with
      m = if Z.eqb (A n * Z.of_nat q + B n * p) 0 then S n else n reduces
      the window faces held at the consecutive indices n and S n to the
      full three-limb escape body at the pick index, sigT-carried.
      (b) Tier 2, planb5_esc17_dodge_upgrade: the Delta n nonzero
      contrapositive upgrade of the dodge pair - at q >= 1 at least one
      of the two indicators is nonzero.  (c) Route F,
      planb5_esc17_forced: the forced band route over 1 <= q <= 135005,
      zero premises beyond the range bound, zero use of the dodge
      determinant.  (d) Route W, planb5_esc17_window_route: the window
      supply face above the forced band, with the dodge-determinant slot
      as an explicit positional premise.  (e) planb5_esc17_global: the
      dispatch - q within the forced band goes to Route F, q above it
      goes to Route W.
    Debt ledger.  Three lines, honest states:
      (D1) DELIVERED as an explicit slot: the dodge determinant
        Delta (nesc q) <> 0 at the window witness - carried verbatim as
        the positional premise of planb5_esc17_window_route and
        planb5_esc17_global; a premise slot only, never discharged,
        never a global axiom.
      (D2) NOT DELIVERED (registered fail-loud): the window-face
        finalization - the escape-window faces of this file are cast at
        the sigma = 17 draft pins and stay a draft until the sigma = 18
        re-pin lands; finalization is out of this unit's scope.
      (D3) NOT DELIVERED (registered fail-loud): the shore-landing face -
        the assembly is delivered as a sandbox handoff only; the landing
        into the in-tree world is a later unit.
    SIGMA-17 DRAFT - NOT FINAL, PENDING P4: the window faces in this
      file are draft shapes at the sigma = 17 pins; the file must not be
      declared final before the sigma = 18 re-pin lands.  The retired v1
      window statement face (the log2-threshold same-window form) is not
      restored here.
    Dependencies.  Stdlib QArith.QArith, ZArith, Arith.Arith, Lia,
      Qpower; piu_mu_criterion; planb1_hcage_zerotouch_prescription;
      planb3_g1_calib.  Z-domain Lia at auxiliary bookkeeping steps
      only.  One-way layering: the assembly consumes the in-tree base
      units and adds no Require edge into them.
    References.  The two-indicator dodge prescription with the Z.eqb
      selection reading and the sigT carrier (M1:434 segment 1); the
      hesc17 slot faces (planb1_hcage_zerotouch_prescription.v:273-280);
      the E-chain faces planb_b_esc_E1_nat and planb_b_esc_E3_nat
      (planb1:164-247); the Nat2Z monotone lift pattern (planb1:117-137);
      the calibration tables (planb3_g1_calib.v); the local Q-bridge
      craft (piu_zz_ec_escwin_nescD.v:103-124 and 328-345); the coprime
      engine is the stdlib Gauss theorem (Z.gauss).
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
      planb5_hesc17_assembly.v, run from the sandbox root (Rocq 9.3.0,
      single lane under the local cpu_guard channel; the sandbox-local
      vo_base copy is the seated trust cache of this box - the bundled
      vo_closure_base cache is superseded here, see the base-seat
      provenance ledger). *)

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
(* proofs below are carried verbatim from the cast fragment; the       *)
(* Section banners are renumbered for the merged file.                 *)
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
(* Section 5. Adapter 1: the E1_nat window face into the Hesc17       *)
(*            limb-1 slot (strict nat face, non-strict Q face).       *)
(* ================================================================== *)

(* Source end: planb_b_esc_E1_nat (planb1:164) - strict nat face        *)
(* 2*q < 2^(2*nesc q).  Target end: the limb-1 slot of planb_b_hesc17   *)
(* (planb1:276) at n = planb_b_nesc q - the non-strict Q face           *)
(* inject_Z (2*q) <= epos (2*n).  Lift: strictness is weakened on the   *)
(* nat side, then the planb1 Nat2Z monotone bridge (planb1:117-137      *)
(* pattern) carries the face to Z and piu_mu_Zle_Qle carries it to Q.   *)
Lemma planb5_adapt_E1_limb1 : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
              (piu_mu_epos (2 * planb_b_nesc q)).
Proof.
  intros q Hq.
  pose proof (planb_b_esc_E1_nat q Hq) as H1.
  (* strict nat face -> non-strict nat face *)
  pose proof (Nat.lt_le_incl _ _ H1) as Hle.
  (* Nat2Z monotone lift, the planb1:117-137 anchor pattern *)
  pose proof (proj1 (Nat2Z.inj_le _ _) Hle) as Hz0.
  rewrite Nat2Z.inj_pow in Hz0.
  change (Z.of_nat 2) with 2%Z in Hz0.
  (* Z monotone bridge into the Q carrier at the limb-1 slot *)
  exact (piu_mu_Zle_Qle (Z.of_nat (2 * q))
           (2 ^ Z.of_nat (2 * planb_b_nesc q)) Hz0).
Qed.

(* ================================================================== *)
(* Section 6. Adapter 2: the E3_nat growth face into the Hesc17       *)
(*            limb-3 slot (squared faces, kappa^2 = 2^28 * 3^14).     *)
(* ================================================================== *)

(* Source end: planb_b_esc_E3_nat (planb1:185) - the nat face           *)
(* 2^(34*nesc q) <= 2^28 * 3^14 * q^19.  Target end: the limb-3 slot of *)
(* planb_b_hesc17 (planb1:278-280) at n = planb_b_nesc q - the squared  *)
(* Q face epos (17*n)^2 <= (35831808 # 1)^2 * q^19, where               *)
(* (35831808 # 1)^2 = 2^28 * 3^14 by the Section-4 pin.  Both faces are *)
(* rewritten into inject_Z form by the Section-3 bridges, and the       *)
(* resulting Z ordering is the planb1 Nat2Z lift of the nat face.       *)
Lemma planb5_adapt_E3_limb3 : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (Qpower (piu_mu_epos (17 * planb_b_nesc q)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q.
Proof.
  intros q Hq.
  (* Nat2Z monotone lift of the nat face, the planb1:117-137 pattern *)
  pose proof (proj1 (Nat2Z.inj_le _ _) (planb_b_esc_E3_nat q Hq)) as HZ.
  repeat rewrite Nat2Z.inj_mul in HZ.
  repeat rewrite Nat2Z.inj_pow in HZ.
  (* literal repair: keep the numerals folded (cbn would half-reduce     *)
  (* Z.of_nat 2 into a Pos.of_succ_nat shape and break the pin rewrite)  *)
  change (Z.of_nat 2) with 2%Z in HZ.
  change (Z.of_nat 28) with 28%Z in HZ.
  change (Z.of_nat 3) with 3%Z in HZ.
  change (Z.of_nat 14) with 14%Z in HZ.
  (* 34 * nesc = 17 * nesc + 17 * nesc, then the square reads off *)
  assert (Hz34 : (Z.of_nat (34 * planb_b_nesc q)
                  = Z.of_nat (17 * planb_b_nesc q)
                    + Z.of_nat (17 * planb_b_nesc q))%Z).
  { replace (34 * planb_b_nesc q)%nat
      with ((17 * planb_b_nesc q) + (17 * planb_b_nesc q))%nat by lia.
    apply Nat2Z.inj_add. }
  rewrite Hz34 in HZ.
  rewrite Z.pow_add_r in HZ by lia.
  (* kappa^2 = 2^28 * 3^14 (the Section-4 pin, read right-to-left) *)
  rewrite <- planb5_adapt_kappa2_pin in HZ.
  (* the raw Q face at the limb-3 slot *)
  apply piu_mu_QleT_i.
  unfold piu_mu_epos.
  change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
  rewrite (planb5_adapt_inj_sq_eq (2 ^ Z.of_nat (17 * planb_b_nesc q))%Z).
  change (Qpower (35831808 # 1)%Q (Z.of_nat 2))
    with (inject_Z (35831808 ^ 2)%Z).
  rewrite <- (planb5_adapt_inj_pow_eq (Z.of_nat q) 19 ltac:(lia)).
  rewrite <- (planb5_adapt_inj_mul_eq (35831808 ^ 2)%Z
                ((Z.of_nat q) ^ Z.of_nat 19)%Z).
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

Example planb5_esc17_e135006 : (135006 =? S 135005)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example planb5_esc17_e39055 : (39055 =? S 39054)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example planb5_esc17_e11298 : (11298 =? S 11297)%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma planb5_esc17_bound1 : forall q : nat, (135006 <= q)%nat -> (1 <= q)%nat.
Proof.
  intros q Hq.
  apply (Nat.le_trans 1%nat 135006%nat q%nat).
  - rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc17_e135006).
    apply (le_n_S 0%nat 135005%nat).
    apply Nat.le_0_l.
  - exact Hq.
Qed.

(* ------------------------------------------------------------------ *)
(* Merged fragment 3 of 4 (planb5_frag_window.v): the statements and  *)
(* proofs below are carried verbatim from the cast fragment; the       *)
(* Section banners are renumbered for the merged file.                 *)
(* ------------------------------------------------------------------ *)

(* ================================================================== *)
(* Section 7. The limb-1 face at the shifted witness S (nesc q):      *)
(*            the strict E1 limb lifted one step by pow monotonicity. *)
(* ================================================================== *)

(* The E1 limb is strict at the witness (2 * q < 2 ^ (2 * nesc q));    *)
(* the shifted face needs only the non-strict form one exponent step   *)
(* up, since 2 * nesc q <= 2 * S (nesc q).                             *)

Lemma planb5_esc_E1p_nat : forall q : nat, (1 <= q)%nat ->
  (2 * q <= 2 ^ (2 * S (planb_b_nesc q)))%nat.
Proof.
  intros q Hq.
  pose proof (planb_b_esc_E1_nat q Hq) as He1.
  pose proof (Nat.lt_le_incl _ _ He1) as Hle1.
  apply (Nat.le_trans _ (2 ^ (2 * planb_b_nesc q))).
  - (* the strict E1 limb gives the first hop, read non-strict *)
    exact Hle1.
  - (* the exponent grows by exactly two under the witness shift *)
    apply Nat.pow_le_mono_r; lia.
Qed.

(* ================================================================== *)
(* Section 8. The binary-Z threshold adjudication literals at         *)
(*            q = 135006 / q = 135005 (vm_compute, exact).            *)
(* ================================================================== *)

(* Reach side: the tight difference at the threshold is a 100-digit    *)
(* positive numeral, carried verbatim; binary-Z evaluation keeps the   *)
(* nat side free of unary blowup.                                      *)

Example planb5_esc_E3p_diff_z :
  (3 ^ 14 * 135006 ^ 19 - 2 ^ 346)%Z
  = 9043017437553511866547048756406586174708779629375924615155971488466718084007784298234252365028392960%Z.
Proof. vm_compute. reflexivity. Qed.

(* Non-reach side: at q = 135005 the growth face fails, so the         *)
(* threshold 135006 is tight.                                          *)

Example planb5_esc_E3p_noreach_z :
  Z.leb (2 ^ 346) (3 ^ 14 * 135005 ^ 19) = false.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 9. The nat-side reach face at the threshold, transported   *)
(*            from the binary-Z literal (the Nat2Z craft of planb1).  *)
(* ================================================================== *)

(* The Z-carried difference literal is nonnegative, so the reach order *)
(* holds in Z; Nat2Z.inj_le with inj_mul / inj_pow transports it to    *)
(* nat without evaluating any nat-side power.                          *)

Lemma planb5_esc_E3p_reach :
  (2 ^ 346 <= 3 ^ 14 * 135006 ^ 19)%nat.
Proof.
  assert (Hz : (2 ^ 346 <= 3 ^ 14 * 135006 ^ 19)%Z)
    by (pose proof planb5_esc_E3p_diff_z; lia).
  apply (proj2 (Nat2Z.inj_le (2 ^ 346) (3 ^ 14 * 135006 ^ 19))).
  rewrite Nat2Z.inj_mul, Nat2Z.inj_pow, Nat2Z.inj_pow, Nat2Z.inj_pow.
  replace (Z.of_nat 2) with 2%Z by reflexivity.
  replace (Z.of_nat 346) with 346%Z by reflexivity.
  replace (Z.of_nat 3) with 3%Z by reflexivity.
  replace (Z.of_nat 14) with 14%Z by reflexivity.
  replace (Z.of_nat 135006) with 135006%Z by reflexivity.
  replace (Z.of_nat 19) with 19%Z by reflexivity.
  exact Hz.
Qed.

(* ================================================================== *)
(* Section 10. The limb-3 face at the shifted witness:                 *)
(*            planb5_esc_E3p_nat (two cases, threshold 135006).       *)
(* ================================================================== *)

(* Case below 2 ^ 19: the shifted witness is at most 11 (the nesc      *)
(* upper bound with log2 q <= 18), so the left side is at most         *)
(* 2 ^ 374 = 2 ^ 28 * 2 ^ 346, and the threshold reach plus pow        *)
(* monotonicity of q ^ 19 carries the right side.  Case from 2 ^ 19:   *)
(* the planb1 E3_nat craft applies - the exponent excess 85 = 28 + 57  *)
(* with 57 = 21 + 38 is absorbed by q ^ 2 at the 2 ^ 19 floor          *)
(* (anchor 2 ^ 21 <= 3 ^ 14).                                          *)

Lemma planb5_esc_E3p_nat : forall q : nat, (135006 <= q)%nat ->
  (2 ^ (34 * S (planb_b_nesc q)) <= 2 ^ 28 * 3 ^ 14 * q ^ 19)%nat.
Proof.
  intros q Hq.
  pose proof (planb5_esc17_bound1 q Hq) as Hq1.
  pose proof (proj2 (planb_b_nesc_bounds q)) as Htw.
  assert (Hr2 : (2 ^ 346 <= 3 ^ 14 * q ^ 19)%nat).
  { apply (Nat.le_trans _ (3 ^ 14 * 135006 ^ 19)).
    - exact planb5_esc_E3p_reach.
    - apply Nat.mul_le_mono_l. apply Nat.pow_le_mono_l; lia. }
  destruct (le_lt_dec (2 ^ 19) q) as [Hbig | Hsmall].
  - (* case from 2 ^ 19: the E3_nat craft with the q ^ 2 absorption *)
    destruct (Nat.log2_spec q) as [Hge _]; [exact Hq1 |].
    assert (H34 : (34 * S (planb_b_nesc q) <= 17 * Nat.log2 q + 85)%nat)
      by lia.
    apply (Nat.le_trans _ (2 ^ (17 * Nat.log2 q + 85))).
    + apply Nat.pow_le_mono_r; lia.
    + rewrite Nat.pow_add_r.
      replace (17 * Nat.log2 q)%nat with (Nat.log2 q * 17)%nat by lia.
      rewrite Nat.pow_mul_r.
      apply (Nat.le_trans _ (q ^ 17 * 2 ^ 85)).
      * apply Nat.mul_le_mono.
        { apply Nat.pow_le_mono_l. exact Hge. }
        { apply Nat.le_refl. }
      * assert (Hq38 : (2 ^ 19 * 2 ^ 19 <= q * q)%nat)
          by (apply Nat.mul_le_mono; lia).
        assert (Hkey : (2 ^ 85 <= 2 ^ 28 * 3 ^ 14 * (q * q))%nat).
        { replace 85%nat with (28 + 57)%nat by (vm_compute; reflexivity).
          rewrite Nat.pow_add_r.
          (* 57 = 19 + 38: the fragment cast carried 21 + 38 here, which   *)
          (* sums to 59 - a false ground equation the solver rightly       *)
          (* refused; the exponent split is repaired to the true one.      *)
          replace 57%nat with (19 + 38)%nat by (vm_compute; reflexivity).
          rewrite Nat.pow_add_r.
          assert (H19 : (2 ^ 19 <= 2 ^ 21)%nat) by (apply Nat.pow_le_mono_r; lia).
          assert (Hstep0 : (2 ^ 19 * 2 ^ 38 <= 2 ^ 21 * 2 ^ 38)%nat)
            by (apply Nat.mul_le_mono; [exact H19 | apply Nat.le_refl]).
          assert (Hstep1 : (2 ^ 21 * 2 ^ 38 <= 3 ^ 14 * (2 ^ 19 * 2 ^ 19))%nat).
          { apply Nat.mul_le_mono.
            - exact planb_b_anchor_E3_mid.
            - replace 38%nat with (19 + 19)%nat by (vm_compute; reflexivity).
              rewrite Nat.pow_add_r. apply Nat.le_refl. }
          assert (Hstep2 : (3 ^ 14 * (2 ^ 19 * 2 ^ 19) <= 3 ^ 14 * (q * q))%nat)
            by (apply Nat.mul_le_mono_l; exact Hq38).
          apply (Nat.le_trans _ (2 ^ 28 * (2 ^ 21 * 2 ^ 38))).
          { apply Nat.mul_le_mono_l. exact Hstep0. }
          apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (2 ^ 19 * 2 ^ 19)))).
          { apply Nat.mul_le_mono_l. exact Hstep1. }
          apply (Nat.le_trans _ (2 ^ 28 * (3 ^ 14 * (q * q)))).
          { apply Nat.mul_le_mono_l. exact Hstep2. }
          rewrite Nat.mul_assoc. apply Nat.le_refl. }
        replace (q ^ 19)%nat with (q ^ 2 * q ^ 17)%nat
          by (rewrite <- (Nat.pow_add_r q 2 17); f_equal; vm_compute; reflexivity).
        assert (Hrq : (q ^ 17 * (2 ^ 28 * 3 ^ 14 * (q * q))
                       = 2 ^ 28 * 3 ^ 14 * (q ^ 2 * q ^ 17))%nat).
        { (* explicit comm/assoc reorder: nat ring with big literal powers
             explodes - lemma-chain only (the planb1 E3_nat craft). *)
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
  - (* case below 2 ^ 19: the shifted witness is at most 11 *)
    destruct (Nat.log2_spec q) as [Hge _]; [exact Hq1 |].
    assert (Hlog : (Nat.log2 q <= 18)%nat).
    { assert (Hcontra : ~ (19 <= Nat.log2 q)%nat).
      { intro H19.
        assert (Hp : (2 ^ 19 <= 2 ^ Nat.log2 q)%nat)
          by (apply Nat.pow_le_mono_r; lia).
        lia. }
      lia. }
    assert (Hsn : (S (planb_b_nesc q) <= 11)%nat) by lia.
    apply (Nat.le_trans _ (2 ^ 374)).
    + apply Nat.pow_le_mono_r; lia.
    + replace 374%nat with (28 + 346)%nat by (vm_compute; reflexivity).
      rewrite Nat.pow_add_r.
      (* re-associate the right side first: the flat product form defeats  *)
      (* the unifier here (stack overflow at the deep numerals)            *)
      rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono; [apply Nat.le_refl | exact Hr2].
Qed.


(* ------------------------------------------------------------------ *)
(* Merged fragment 4 of 4 (planb5_frag_forced.v): the statements and  *)
(* proofs below are carried verbatim from the cast fragment; the       *)
(* Section banners are renumbered for the merged file.                 *)
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
(*            criterion (item a: ten band endpoint pairs, checked by  *)
(*            a boolean vm_compute face).                             *)
(* ================================================================== *)

(* The prescribed band lower endpoints lo_k, k = 1..10; outside the     *)
(* table domain the function returns 0 and no claim is made.            *)
Definition planb5_forced_blo : nat -> nat :=
  fun k =>
    match k with
    | S k' => nth k' [1%nat; 3%nat; 9%nat; 33%nat; 129%nat; 513%nat;
                      2049%nat; 8193%nat; 32769%nat; 131073%nat] 0%nat
    | _ => 0%nat
    end.

(* The prescribed band upper endpoints hi_k, k = 1..10.                 *)
Definition planb5_forced_bhi : nat -> nat :=
  fun k =>
    match k with
    | S k' => nth k' [1%nat; 6%nat; 22%nat; 79%nat; 273%nat; 945%nat;
                      3268%nat; 11297%nat; 39054%nat; 135005%nat] 0%nat
    | _ => 0%nat
    end.

(* The q3min table k = 1..11: the least q with 3^14 * q^19 >=           *)
(* 2^(34*k - 28), the limb-3 floor of the F-extended interval k; the    *)
(* entry q3min(11) = 135006 closes the top of the range [1, 135005].    *)
Definition planb5_forced_q3m : nat -> nat :=
  fun k =>
    match k with
    | S k' => nth k' [1%nat; 2%nat; 7%nat; 23%nat; 80%nat; 274%nat;
                      946%nat; 3269%nat; 11298%nat; 39055%nat; 135006%nat] 0%nat
    | _ => 0%nat
    end.

(* Item (a) header criterion: the ten band endpoint pairs verbatim,     *)
(* as a boolean certificate over the tables.                            *)
Definition planb5_forced_band_endpoints_check : bool :=
  (Nat.eqb (planb5_forced_blo 1) 1) && (Nat.eqb (planb5_forced_bhi 1) 1) &&
  (Nat.eqb (planb5_forced_blo 2) 3) && (Nat.eqb (planb5_forced_bhi 2) 6) &&
  (Nat.eqb (planb5_forced_blo 3) 9) && (Nat.eqb (planb5_forced_bhi 3) 22) &&
  (Nat.eqb (planb5_forced_blo 4) 33) && (Nat.eqb (planb5_forced_bhi 4) 79) &&
  (Nat.eqb (planb5_forced_blo 5) 129) && (Nat.eqb (planb5_forced_bhi 5) 273) &&
  (Nat.eqb (planb5_forced_blo 6) 513) && (Nat.eqb (planb5_forced_bhi 6) 945) &&
  (Nat.eqb (planb5_forced_blo 7) 2049) && (Nat.eqb (planb5_forced_bhi 7) 3268) &&
  (Nat.eqb (planb5_forced_blo 8) 8193) && (Nat.eqb (planb5_forced_bhi 8) 11297) &&
  (Nat.eqb (planb5_forced_blo 9) 32769) && (Nat.eqb (planb5_forced_bhi 9) 39054) &&
  (Nat.eqb (planb5_forced_blo 10) 131073) && (Nat.eqb (planb5_forced_bhi 10) 135005).

Example planb5_forced_band_endpoints_ok : planb5_forced_band_endpoints_check = true.
Proof. vm_compute. reflexivity. Qed.

(* The nine adjacencies of the F-extension tiling: the extended         *)
(* interval k+1 starts exactly one step after the band top hi_k,        *)
(* q3min(k+1) = hi_k + 1 for k = 1..9 (boolean certificate).            *)
Definition planb5_forced_adj_check : bool :=
  (Nat.eqb (planb5_forced_q3m 2) (planb5_forced_bhi 1 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 3) (planb5_forced_bhi 2 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 4) (planb5_forced_bhi 3 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 5) (planb5_forced_bhi 4 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 6) (planb5_forced_bhi 5 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 7) (planb5_forced_bhi 6 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 8) (planb5_forced_bhi 7 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 9) (planb5_forced_bhi 8 + 1)) &&
  (Nat.eqb (planb5_forced_q3m 10) (planb5_forced_bhi 9 + 1)).

Example planb5_forced_adj_ok : planb5_forced_adj_check = true.
Proof. vm_compute. reflexivity. Qed.

(* The top entry of the q3min table: 135006, one step past the range    *)
(* end 135005 (the limb-3 face at n = 11 needs q >= 135006, so the      *)
(* forced route ends exactly at the prescribed top).                    *)
Example planb5_forced_q3m_top : Nat.eqb (planb5_forced_q3m 11) 135006 = true.
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

(* The per-band gcd d_k = gcd(|A_k|, |B_k|), k = 1..10.                 *)
Definition planb5_forced_dk : nat -> Z :=
  fun k =>
    match k with
    | S k' => nth k' [8%Z; 32%Z; 2240%Z; 352%Z; 2688%Z; 32%Z; 160%Z;
                      17600%Z; 30464%Z; 512%Z] 0%Z
    | _ => 0%Z
    end.

(* The reduced numerator pair g_k = A_k / d_k (signed), k = 1..10.      *)
Definition planb5_forced_gk : nat -> Z :=
  fun k =>
    match k with
    | S k' => nth k' [2818%Z; 96188954%Z; 202909760012%Z;
                      11363042315305984%Z; 16454631467853697072832%Z;
                      7210732800456956809618314752%Z;
                      8419827893461487859350600476672%Z;
                      3869345558286928574831731815957397504%Z;
                      8806829371930926381963609226384365961216%Z;
                      2644791314655510283632140858092780624217325568%Z] 0%Z
    | _ => 0%Z
    end.

(* The reduced denominator pair h_k = B_k / d_k (signed), k = 1..10;    *)
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
                      (-841863222347873579452565675390633469475782825)%Z] 0%Z
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
(* index 1..10 (one vm_compute case per concrete index).                *)
Lemma planb5_forced_band_ok_at : forall k : nat,
  (1 <= k <= 10)%nat -> planb5_forced_band_ok k = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The all-bands certificate: the ten per-band checks concatenated.     *)
Example planb5_forced_band_ok_all :
  (planb5_forced_band_ok 1 && planb5_forced_band_ok 2 &&
   planb5_forced_band_ok 3 && planb5_forced_band_ok 4 &&
   planb5_forced_band_ok 5 && planb5_forced_band_ok 6 &&
   planb5_forced_band_ok 7 && planb5_forced_band_ok 8 &&
   planb5_forced_band_ok 9 && planb5_forced_band_ok 10)%bool = true.
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
(*            limb 1 at hi_k and limb 3 at lo_k, ten bands).          *)
(* ================================================================== *)

(* The band-top Z face for limb 1: 2*hi_k <= 2^(2*k), boolean form.     *)
Lemma planb5_forced_limb1Z_ok : forall k : nat,
  (1 <= k <= 10)%nat ->
  (Z.of_nat (2 * planb5_forced_bhi k) <=? 2 ^ Z.of_nat (2 * k))%Z = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The band-bottom Z face for limb 3 at the q3min floor:                *)
(* 2^(17*k) * 2^(17*k) <= 2^28 * 3^14 * q3min(k)^19, boolean form.      *)
Lemma planb5_forced_limb3Z_ok : forall k : nat,
  (1 <= k <= 10)%nat ->
  ((2 ^ Z.of_nat (17 * k) * 2 ^ Z.of_nat (17 * k) <=?
    35831808 ^ 2 * Z.of_nat (planb5_forced_q3m k) ^ Z.of_nat 19)%Z) = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The prescribed-bottom Z face for limb 3 at lo_k: the same face at    *)
(* the band lower endpoint, boolean form (consumed by the N1 faces).    *)
Lemma planb5_forced_limb3Zlo_ok : forall k : nat,
  (1 <= k <= 10)%nat ->
  ((2 ^ Z.of_nat (17 * k) * 2 ^ Z.of_nat (17 * k) <=?
    35831808 ^ 2 * Z.of_nat (planb5_forced_blo k) ^ Z.of_nat 19)%Z) = true.
Proof.
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]; try lia;
    vm_compute; reflexivity.
Qed.

(* The ten window-end N1 faces: the limb-1 slot face at the band top    *)
(* hi_k and the limb-3 slot face at the band bottom lo_k, per band,     *)
(* all literals, piu_mu_and2-carried.                                   *)

Example planb5_forced_N1_1 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 1))) (piu_mu_epos (2 * 1)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 1)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 1)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_1 = 1 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_1 = 1 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 1))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 1) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 1) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 1) * 2 ^ Z.of_nat (17 * 1))%Z
                (35831808 ^ 2 * (Z.of_nat 1) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_2 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 6))) (piu_mu_epos (2 * 2)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 2)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 3)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_2 = 6 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_2 = 3 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 2))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 3) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 3) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 2) * 2 ^ Z.of_nat (17 * 2))%Z
                (35831808 ^ 2 * (Z.of_nat 3) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_3 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 22))) (piu_mu_epos (2 * 3)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 3)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 9)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_3 = 22 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_3 = 9 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 3))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 9) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 9) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 3) * 2 ^ Z.of_nat (17 * 3))%Z
                (35831808 ^ 2 * (Z.of_nat 9) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_4 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 79))) (piu_mu_epos (2 * 4)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 4)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 33)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_4 = 79 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_4 = 33 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 4))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 33) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 33) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 4) * 2 ^ Z.of_nat (17 * 4))%Z
                (35831808 ^ 2 * (Z.of_nat 33) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_5 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 273))) (piu_mu_epos (2 * 5)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 5)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 129)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_5 = 273 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_5 = 129 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 5))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 129) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 129) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 5) * 2 ^ Z.of_nat (17 * 5))%Z
                (35831808 ^ 2 * (Z.of_nat 129) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_6 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 945))) (piu_mu_epos (2 * 6)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 6)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 513)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_6 = 945 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_6 = 513 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 6))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 513) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 513) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 6) * 2 ^ Z.of_nat (17 * 6))%Z
                (35831808 ^ 2 * (Z.of_nat 513) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_7 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 3268))) (piu_mu_epos (2 * 7)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 7)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 2049)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_7 = 3268 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_7 = 2049 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 7))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 2049) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 2049) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 7) * 2 ^ Z.of_nat (17 * 7))%Z
                (35831808 ^ 2 * (Z.of_nat 2049) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_8 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 11297))) (piu_mu_epos (2 * 8)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 8)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 8193)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_8 = 11297 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_8 = 8193 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 8))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 8193) 19%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 8193) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 8) * 2 ^ Z.of_nat (17 * 8))%Z
                (35831808 ^ 2 * (Z.of_nat 8193) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_9 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 39054))) (piu_mu_epos (2 * 9)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 9)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 32769)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_9 = 39054 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_9 = 32769 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 9))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 32769) 19%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 32769) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 9) * 2 ^ Z.of_nat (17 * 9))%Z
                (35831808 ^ 2 * (Z.of_nat 32769) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

Example planb5_forced_N1_10 : piu_mu_and2
  (piu_mu_QleT (inject_Z (Z.of_nat (2 * 135005))) (piu_mu_epos (2 * 10)))
  (piu_mu_QleT (Qpower (piu_mu_epos (17 * 10)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat 131073)) (Z.of_nat (17 + 2)))%Q).
Proof.
  apply piu_mu_and2_i.
  - (* limb 1 at the band top hi_10 = 135005 *)
    unfold piu_mu_epos. apply piu_mu_Zle_Qle.
    vm_compute. easy.
  - (* limb 3 at the band bottom lo_10 = 131073 *)
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * 10))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat 131073) 19%nat ltac:(vm_compute; reflexivity)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat 131073) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * 10) * 2 ^ Z.of_nat (17 * 10))%Z
                (35831808 ^ 2 * (Z.of_nat 131073) ^ Z.of_nat 19)%Z
                ltac:(vm_compute; easy)) as [HQ].
    exact HQ.
Qed.

(* ================================================================== *)
(* Section 16. The F-extension tiling and the forced escape theorem    *)
(*            (item e: the ten extended intervals [q3min(k), hi_k]    *)
(*            tile [1, 135005]; zero premises, zero dodge).           *)
(* ================================================================== *)

(* The generic interval witness: at band index k with the table values  *)
(* vlo = q3min(k) and vhi = hi_k, every q with vlo <= q <= vhi admits   *)
(* the full three-limb witness n = k.  Limb 1 comes from the band-top    *)
(* face and q <= vhi; limb 2 from the coprime forced lemma at the       *)
(* reduced pair (g_k, h_k), scaled by d_k; limb 3 from the q3min floor   *)
(* face and the pow monotonicity vlo^19 <= q^19.                        *)
Lemma planb5_forced_witness : forall (k vlo vhi : nat) (p : Z) (q : nat),
  (1 <= k <= 10)%nat ->
  (1 <= q)%nat ->
  planb5_forced_band_ok k = true ->
  planb5_forced_q3m k = vlo%nat ->
  planb5_forced_bhi k = vhi%nat ->
  (vlo <= q)%nat ->
  (q <= vhi)%nat ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A n * Z.of_nat q + planb3_g1_B n * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (17 * n)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q)).
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
    pose proof (Nat.pow_le_mono_l vlo q 19%nat ltac:(lia)) as Hmono.
    pose proof (proj1 (Nat2Z.inj_le _ _) Hmono) as HmonoZ.
    rewrite !Nat2Z.inj_pow in HmonoZ.
    pose proof (Z.mul_le_mono_nonneg (35831808 ^ 2)%Z (35831808 ^ 2)%Z
                  (Z.of_nat vlo ^ Z.of_nat 19) (Z.of_nat q ^ Z.of_nat 19)
                  ltac:(apply Z.pow_nonneg; lia) ltac:(lia)
                  ltac:(apply Z.pow_nonneg; lia) ltac:(exact HmonoZ)) as HmonoM.
    assert (HZ : (2 ^ Z.of_nat (17 * k) * 2 ^ Z.of_nat (17 * k)
                  <= 35831808 ^ 2 * Z.of_nat q ^ Z.of_nat 19)%Z) by lia.
    apply piu_mu_QleT_i. unfold piu_mu_epos.
    change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
    rewrite (planb5_forced_inj_sq_eq (2 ^ Z.of_nat (17 * k))%Z).
    change (Qpower (35831808 # 1)%Q (Z.of_nat 2)) with (inject_Z (35831808 ^ 2)%Z).
    rewrite <- (planb5_forced_inj_pow_eq (Z.of_nat q) 19%nat ltac:(lia)).
    rewrite <- (planb5_forced_inj_mul_eq (35831808 ^ 2)%Z ((Z.of_nat q) ^ Z.of_nat 19)%Z).
    destruct (piu_mu_Zle_Qle
                (2 ^ Z.of_nat (17 * k) * 2 ^ Z.of_nat (17 * k))%Z
                (35831808 ^ 2 * (Z.of_nat q) ^ Z.of_nat 19)%Z HZ) as [HQ].
    exact HQ.
Qed.

(* The mission theorem: the forced route over the whole bounded range.  *)
(* The ten extended intervals [q3min(k), hi_k] tile [1, 135005] by the  *)
(* nine adjacencies (q3min(k+1) = hi_k + 1, Section 12); q is dispatched *)
(* by one le_lt_dec cut per boundary and each branch instantiates the   *)
(* interval witness at its band index.  Zero premises beyond the range  *)
(* bound; the dodge determinant is never used.                          *)
Theorem planb5_esc17_forced : forall (p : Z) (q : nat),
  (1 <= q)%nat -> (q <= 135005)%nat ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A n * Z.of_nat q + planb3_g1_B n * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (17 * n)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q)).
Proof.
  intros p q Hq1 Hq2.
  destruct (le_lt_dec q 1) as [Hc1 | Hc1].
  - (* interval 1: [1, 1], witness n = 1 *)
    exact (planb5_forced_witness 1%nat 1%nat 1%nat p q
             ltac:(lia) ltac:(lia)
             (planb5_forced_band_ok_at 1%nat ltac:(lia))
             ltac:(reflexivity) ltac:(reflexivity)
             ltac:(lia) ltac:(lia)).
  - destruct (le_lt_dec q 6) as [Hc2 | Hc2].
    { (* interval 2: [2, 6], witness n = 2 *)
      exact (planb5_forced_witness 2%nat 2%nat 6%nat p q
               ltac:(lia) ltac:(lia)
               (planb5_forced_band_ok_at 2%nat ltac:(lia))
               ltac:(reflexivity) ltac:(reflexivity)
               ltac:(lia) ltac:(lia)). }
    { destruct (le_lt_dec q 22) as [Hc3 | Hc3].
      { (* interval 3: [7, 22], witness n = 3 *)
        exact (planb5_forced_witness 3%nat 7%nat 22%nat p q
                 ltac:(lia) ltac:(lia)
                 (planb5_forced_band_ok_at 3%nat ltac:(lia))
                 ltac:(reflexivity) ltac:(reflexivity)
                 ltac:(lia) ltac:(lia)). }
      { destruct (le_lt_dec q 79) as [Hc4 | Hc4].
        { (* interval 4: [23, 79], witness n = 4 *)
          exact (planb5_forced_witness 4%nat 23%nat 79%nat p q
                   ltac:(lia) ltac:(lia)
                   (planb5_forced_band_ok_at 4%nat ltac:(lia))
                   ltac:(reflexivity) ltac:(reflexivity)
                   ltac:(lia) ltac:(lia)). }
        { destruct (le_lt_dec q 273) as [Hc5 | Hc5].
          { (* interval 5: [80, 273], witness n = 5 *)
            exact (planb5_forced_witness 5%nat 80%nat 273%nat p q
                     ltac:(lia) ltac:(lia)
                     (planb5_forced_band_ok_at 5%nat ltac:(lia))
                     ltac:(reflexivity) ltac:(reflexivity)
                     ltac:(lia) ltac:(lia)). }
          { destruct (le_lt_dec q 945) as [Hc6 | Hc6].
            { (* interval 6: [274, 945], witness n = 6 *)
              exact (planb5_forced_witness 6%nat 274%nat 945%nat p q
                       ltac:(lia) ltac:(lia)
                       (planb5_forced_band_ok_at 6%nat ltac:(lia))
                       ltac:(reflexivity) ltac:(reflexivity)
                       ltac:(lia) ltac:(lia)). }
            { destruct (le_lt_dec q 3268) as [Hc7 | Hc7].
              { (* interval 7: [946, 3268], witness n = 7 *)
                exact (planb5_forced_witness 7%nat 946%nat 3268%nat p q
                         ltac:(lia) ltac:(lia)
                         (planb5_forced_band_ok_at 7%nat ltac:(lia))
                         ltac:(reflexivity) ltac:(reflexivity)
                         ltac:(lia) ltac:(lia)). }
              { destruct (le_lt_dec q 11297) as [Hc8 | Hc8].
                { (* interval 8: [3269, 11297], witness n = 8 *)
                  exact (planb5_forced_witness 8%nat 3269%nat 11297%nat p q
                           ltac:(lia) ltac:(lia)
                           (planb5_forced_band_ok_at 8%nat ltac:(lia))
                           ltac:(reflexivity) ltac:(reflexivity)
                           ltac:(lia) ltac:(lia)). }
                { destruct (le_lt_dec q 39054) as [Hc9 | Hc9].
                  { (* interval 9: [11298, 39054], witness n = 9 *)
                    exact (planb5_forced_witness 9%nat 11298%nat 39054%nat p q
                             ltac:(lia) ltac:(lia)
                             (planb5_forced_band_ok_at 9%nat ltac:(lia))
                             ltac:(reflexivity) ltac:(reflexivity)
                             ltac:(rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc17_e11298); exact Hc8)
                             ltac:(lia)). }
                  { (* interval 10: [39055, 135005], witness n = 10 *)
                    exact (planb5_forced_witness 10%nat 39055%nat 135005%nat p q
                             ltac:(lia) ltac:(lia)
                             (planb5_forced_band_ok_at 10%nat ltac:(lia))
                             ltac:(reflexivity) ltac:(reflexivity)
                             ltac:(rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc17_e39055); exact Hc9)
                             ltac:(lia)). } } } } } } } }
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

Definition planb5_esc17_pick (A B : nat -> Z) (p : Z) (q n : nat) : nat :=
  if Z.eqb (A n * Z.of_nat q + B n * p) 0 then S n else n.

(* Tier 2.  The Delta n nonzero contrapositive upgrade of the dodge     *)
(* pair: at q >= 1 the two indicators cannot vanish together, so at     *)
(* least one of them is nonzero.  The Delta slot is an explicit         *)
(* positional premise here and stays one everywhere below - never       *)
(* discharged, never a global axiom.                                    *)

Lemma planb5_esc17_dodge_upgrade :
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

Lemma planb5_esc17_reduce :
  forall (A B : nat -> Z) (p : Z) (q n : nat),
  (1 <= q)%nat ->
  (A n * B (S n) - A (S n) * B n <> 0)%Z ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * n)) ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * S n)) ->
  piu_mu_QleT (Qpower (piu_mu_epos (17 * n)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q ->
  piu_mu_QleT (Qpower (piu_mu_epos (17 * S n)) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q ->
  sigT (fun m : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * m)))
    (piu_mu_ZleT 1 (Z.abs (A m * Z.of_nat q + B m * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (17 * m)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q)).
Proof.
  intros A B p q n Hq Hdelta Hl1n Hl1sn Hl3n Hl3sn.
  pose proof (planb5_esc17_dodge_upgrade A B p q n Hq Hdelta) as Hup.
  destruct (Z.eqb_spec (A n * Z.of_nat q + B n * p) 0) as [Hz | Hnz].
  - (* first indicator zero at n: the pick selects S n *)
    exists (planb5_esc17_pick A B p q n).
    assert (Hpick : planb5_esc17_pick A B p q n = S n).
    { unfold planb5_esc17_pick.
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
    exists (planb5_esc17_pick A B p q n).
    assert (Hpick : planb5_esc17_pick A B p q n = n).
    { unfold planb5_esc17_pick.
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

(* The limb-1 Q face at the shifted witness S (nesc q): the strict E1   *)
(* limb lifted one witness step (Section 7) carried to the non-strict   *)
(* Q face by the Nat2Z monotone lift and the Z-to-Q bridge.             *)

Lemma planb5_esc17_E1p_Q : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
              (piu_mu_epos (2 * S (planb_b_nesc q))).
Proof.
  intros q Hq.
  pose proof (planb5_esc_E1p_nat q Hq) as He.
  pose proof (proj1 (Nat2Z.inj_le _ _) He) as Hz.
  rewrite Nat2Z.inj_pow in Hz.
  change (Z.of_nat 2) with 2%Z in Hz.
  exact (piu_mu_Zle_Qle (Z.of_nat (2 * q))
           (2 ^ Z.of_nat (2 * S (planb_b_nesc q))) Hz).
Qed.

(* The limb-3 squared Q face at the shifted witness S (nesc q): the     *)
(* E3p growth face (Section 10) carried to the squared Q face by the    *)
(* same craft as the Section 6 adapter, with the kappa-square pin.      *)

Lemma planb5_esc17_E3p_Q : forall q : nat, (135006 <= q)%nat ->
  piu_mu_QleT (Qpower (piu_mu_epos (17 * S (planb_b_nesc q))) (Z.of_nat 2))
    (Qpower (35831808 # 1)%Q (Z.of_nat 2)
     * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q.
Proof.
  intros q Hq.
  pose proof (planb5_esc17_bound1 q Hq) as Hq1.
  pose proof (proj1 (Nat2Z.inj_le _ _) (planb5_esc_E3p_nat q Hq)) as HZ.
  repeat rewrite Nat2Z.inj_mul in HZ.
  repeat rewrite Nat2Z.inj_pow in HZ.
  (* literal repair: keep the numerals folded, as in the Section 6 fix   *)
  change (Z.of_nat 2) with 2%Z in HZ.
  change (Z.of_nat 28) with 28%Z in HZ.
  change (Z.of_nat 3) with 3%Z in HZ.
  change (Z.of_nat 14) with 14%Z in HZ.
  assert (Hz34 : (Z.of_nat (34 * S (planb_b_nesc q))
                  = Z.of_nat (17 * S (planb_b_nesc q))
                    + Z.of_nat (17 * S (planb_b_nesc q)))%Z).
  { replace (34 * S (planb_b_nesc q))%nat
      with ((17 * S (planb_b_nesc q)) + (17 * S (planb_b_nesc q)))%nat
      by lia.
    apply Nat2Z.inj_add. }
  rewrite Hz34 in HZ.
  rewrite Z.pow_add_r in HZ by lia.
  rewrite <- planb5_adapt_kappa2_pin in HZ.
  apply piu_mu_QleT_i.
  unfold piu_mu_epos.
  change (Z.of_nat (17 + 2)) with (Z.of_nat 19).
  rewrite (planb5_adapt_inj_sq_eq (2 ^ Z.of_nat (17 * S (planb_b_nesc q)))%Z).
  change (Qpower (35831808 # 1)%Q (Z.of_nat 2))
    with (inject_Z (35831808 ^ 2)%Z).
  rewrite <- (planb5_adapt_inj_pow_eq (Z.of_nat q) 19%nat ltac:(lia)).
  rewrite <- (planb5_adapt_inj_mul_eq (35831808 ^ 2)%Z
                ((Z.of_nat q) ^ Z.of_nat 19)%Z).
  destruct (piu_mu_Zle_Qle
              (2 ^ Z.of_nat (17 * S (planb_b_nesc q))
               * 2 ^ Z.of_nat (17 * S (planb_b_nesc q)))%Z
              (35831808 ^ 2 * (Z.of_nat q) ^ Z.of_nat 19)%Z HZ) as [HQ].
  exact HQ.
Qed.

(* Route W.  The window supply face with the Delta slot explicit: for   *)
(* every q above the forced-band top, the Hesc17 escape body at the     *)
(* calibration pair is constructed at the pick index of the window      *)
(* witness pair (nesc q, S (nesc q)).  The dodge determinant slot       *)
(* Delta (nesc q) <> 0 enters as an explicit positional premise - it is *)
(* a premise of this face and of the global dispatch below, never       *)
(* discharged, never a global axiom.                                    *)

Lemma planb5_esc17_window_route :
  forall (p : Z) (q : nat),
  (135006 <= q)%nat ->
  (planb3_g1_A (planb_b_nesc q) * planb3_g1_B (S (planb_b_nesc q))
   - planb3_g1_A (S (planb_b_nesc q)) * planb3_g1_B (planb_b_nesc q)
   <> 0)%Z ->
  sigT (fun m : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * m)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A m * Z.of_nat q + planb3_g1_B m * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (17 * m)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q)).
Proof.
  intros p q Hq Hdelta.
  pose proof (planb5_esc17_bound1 q Hq) as Hq1.
  apply (planb5_esc17_reduce planb3_g1_A planb3_g1_B p q (planb_b_nesc q)).
  - (* the modulus bound, via the glue bridge *)
    exact Hq1.
  - (* the Delta slot, passed verbatim *)
    exact Hdelta.
  - (* limb 1 at the window witness nesc q *)
    exact (planb5_adapt_E1_limb1 q ltac:(exact Hq1)).
  - (* limb 1 at the shifted witness S (nesc q) *)
    exact (planb5_esc17_E1p_Q q ltac:(exact Hq1)).
  - (* limb 3 at the window witness nesc q *)
    exact (planb5_adapt_E3_limb3 q ltac:(exact Hq1)).
  - (* limb 3 at the shifted witness S (nesc q) *)
    exact (planb5_esc17_E3p_Q q ltac:(exact Hq)).
Qed.

(* The global dispatch: q within the forced band goes to Route F (the   *)
(* zero-premise closed face, Section 16), q above the band goes to      *)
(* Route W with the Delta slot explicit.  The slot stays a premise of   *)
(* the global face itself - never discharged, never a global axiom.     *)

Theorem planb5_esc17_global :
  forall (p : Z) (q : nat),
  (1 <= q)%nat ->
  (planb3_g1_A (planb_b_nesc q) * planb3_g1_B (S (planb_b_nesc q))
   - planb3_g1_A (S (planb_b_nesc q)) * planb3_g1_B (planb_b_nesc q)
   <> 0)%Z ->
  sigT (fun m : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q))) (piu_mu_epos (2 * m)))
    (piu_mu_ZleT 1 (Z.abs (planb3_g1_A m * Z.of_nat q + planb3_g1_B m * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (17 * m)) (Z.of_nat 2))
      (Qpower (35831808 # 1)%Q (Z.of_nat 2)
       * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat (17 + 2)))%Q)).
Proof.
  intros p q Hq Hdelta.
  destruct (le_lt_dec q 135005) as [Hlow | Hhigh].
  - (* forced band route: zero premises beyond the range bound *)
    exact (planb5_esc17_forced p q Hq Hlow).
  - (* window route above the forced band, the Delta slot explicit *)
    assert (Hq6 : (135006 <= q)%nat)
      by (rewrite (proj1 (Nat.eqb_eq _ _) planb5_esc17_e135006); exact Hhigh).
    exact (planb5_esc17_window_route p q Hq6 Hdelta).
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
Print Assumptions planb5_esc17_e135006.
Print Assumptions planb5_esc17_e39055.
Print Assumptions planb5_esc17_e11298.
Print Assumptions planb5_esc17_bound1.
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
Print Assumptions planb5_forced_witness.
Print Assumptions planb5_esc17_forced.
Print Assumptions planb5_esc17_pick.
Print Assumptions planb5_esc17_dodge_upgrade.
Print Assumptions planb5_esc17_reduce.
Print Assumptions planb5_esc17_E1p_Q.
Print Assumptions planb5_esc17_E3p_Q.
Print Assumptions planb5_esc17_window_route.
Print Assumptions planb5_esc17_global.
