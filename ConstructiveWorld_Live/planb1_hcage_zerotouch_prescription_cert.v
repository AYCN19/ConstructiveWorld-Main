(* ConstructiveWorld-Main - Certificate unit of the Hcage zero-touch prescription piece: numeric ground faces and the Q-layer rate dance. *)

(* Mission. Companion certificate unit of the Hcage zero-touch prescription
   piece (KB41m 6.2 (B) branch): it hosts (i) the reduction-closed numeric
   ground faces - the kappa power pins, the c0 exact decomposition checks,
   the (D)-calibration anchor pair, the q = 1 anchors, and the double-limb
   anchor - and (ii) the local Q bridges (power positivity, square packing,
   two-sided monotonicity, inverse nonnegativity, order reflection on
   squares) together with the rate-slot dance re-cast at exponent E = 10
   and the abstract slot-11 distance face. The split keeps reduction
   tactics out of the proof-surface unit and keeps both units inside the
   line budget (certificate-separation rule). *)
(* Dependencies. Stdlib QArith, Qabs, ZArith, Arith, Lia, Qpower;
   S02_CauchyComplete (QleT'/QeqT and the two-way Qle gates);
   piu_mu_criterion (inverse-non negativity face); the proof-surface unit
   planb1_hcage_zerotouch_prescription for the pinned constants kappa and
   c0 (one-way upward Require). *)
(* References. KB41m 6.2 (B) redirect and 5.3 NEGATIVE; KB41h 5.2 (B)-row
   and 5.1 (E3 chain anchors); e_carrier.v (pinning faces, nesc bounds,
   the square-root dance :466-527, Section EC premises); nescD.v (Q
   bridges, inject/pow_pos shapes); bracket.v:164 slope certificate. *)
(* Constructivity. Every named statement is Set-carried or a decidable
   ground proposition; the Q bridges are transparent definitions over
   stdlib Q lemmas; postulate-free, admission-free; every named statement
   closes under the global context. *)
(* Build. coqc -q -native-compiler no -Q . "" (Rocq 9.3.0) after the
   proof-surface unit, serial single lane under the cpu_guard wrapped
   chain; coqchk must carry -bytecode-compiler yes. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import planb1_hcage_zerotouch_prescription.

(* ================================================================== *)
(* Section 1. Numeric ground faces (reduction-closed anchors).        *)
(* ================================================================== *)

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

(* (D)-calibration pair: the slope certificate and its minimality twin. *)
(* Z-carried (binary) exactly as the bracket.v:164 slope-certificate    *)
(* precedent - the unary-nat computation of 20^7 overflows the stack    *)
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

(* ================================================================== *)
(* Section 2. Local Q bridges (nescD.v shapes re-pinned; the one-way- *)
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
(* Section 3. The rate-slot dance re-cast at E = 10 (the exponent     *)
(*            7 -> 10 replacement) and the abstract slot-11 face.     *)
(* ================================================================== *)

(* The (B) first-power rate face: MuBound at (sigma, tau) = (17, 2)     *)
(* unwinds to c0 <= dval * q^10 (e_carrier.v:469-527 isomorph with the  *)
(* half-integer span absorbed by bQ <= bQ^2 inside the square).         *)
Lemma planb_b_rate_c0_E10 :
  forall (dval : Z -> Z -> Q) (p0 : Z) (q0 : nat),
  (1 <= q0)%nat -> (0 <= dval (- p0)%Z (Z.of_nat q0))%Q ->
  piu_mu_MuBound 17%nat 2%nat dval (35831808 # 1)%Q (1 # 2)%Q ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * (35831808 # 1))%Q)
    (dval (- p0)%Z (Z.of_nat q0)
     * Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 10))%Q.
Proof.
  intros dval p0 q0 Hq0 Hnn Hmb.
  pose proof (Hmb p0 q0 Hq0) as Hm0. destruct Hm0 as [Hm0].
  remember (dval (- p0)%Z (Z.of_nat q0)) as W eqn:HW in *.
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
    (dval (- p0)%Z (Z.of_nat q0)
     * Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 10))%Q ->
  S02_CauchyComplete.QleT' (dval (- p0)%Z (Z.of_nat q0))
    (Qabs (inject_Z (Z.of_nat q0) * xk - inject_Z p0)) ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * (35831808 # 1))%Q
      / Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 11))%Q
    (Qabs (xk - r)).
Proof.
  intros dval r xk p0 q0 Hred Hq0 Hc0 Hx.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hc0) as H1.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hx) as H2.
  remember (dval (- p0)%Z (Z.of_nat q0)) as W eqn:HW in *.
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

(* Assumption audit for the certificate-local faces. *)

Print Assumptions planb_b_pow_pos_lt.
Print Assumptions planb_b_qpow2_mul.
Print Assumptions planb_b_qmult_le_compat_l.
Print Assumptions planb_b_qinv_nneg.
Print Assumptions planb_b_qmult_lt_compat_l.
Print Assumptions planb_b_qsq_ord_reflect.
Print Assumptions planb_b_rate_c0_E10.
Print Assumptions planb_b_rate_dist_slot11.
