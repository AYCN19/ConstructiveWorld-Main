(* ========================================================================= *)
(* Mission      : E-side carrier and the conditional mu-certificate chain    *)
(*                for the pi irrationality rate slot.  The linear-form pair  *)
(*                (A, B) and the residual mirror dv are carried as explicit  *)
(*                section parameters; the cage and escape inputs enter as    *)
(*                explicit premises.  The main theorem closes the chain      *)
(*                from the explicit premise group to the rate-form           *)
(*                real-layer certificate real_lt (real_const (ck_alpha c0 8  *)
(*                q)) (pi distance q), with the corrected exponent pinning   *)
(*                sigma = 6*tau = 12, tau = 2, kappa = 35831808, and         *)
(*                c0 = 1/71663616.                                           *)
(* Dependencies : piu_mu_criterion, piu_zz_bridge_real, piu_zz_poincare_     *)
(*                engine, piu_zz_padic_clearing, piu_zz_tau_enclosure_base,  *)
(*                piu_zz_mu_assembly, plus the S01-S10 real layer,           *)
(*                LW0MLicBridge, LW1PiMeasure, Local.LW0LeibSeparation.      *)
(* References   : piu_mu_criterion (five-premise criterion); piu_zz_tau_     *)
(*                enclosure_base (tau face, eventual_le); piu_zz_mu_         *)
(*                assembly (dist_pt to real_lt adapter); Zeilberger-        *)
(*                Zudilin, Moscow J. Comb. Number Theory 9 (2020) 407-419.   *)
(* Constructivity: every named statement is carried in Set (piu_mu_QleT,     *)
(*                QleT', QltT, QeqT, sigT, and2, and3, NatLe); premises are  *)
(*                section-level explicit parameters in discharged shape      *)
(*                after End; no global assumptions; definitions transparent; *)
(*                lia and lra appear only as auxiliary linear-algebra steps  *)
(*                inside proof bodies (piu1904 and piu_mu_criterion          *)
(*                precedent).                                                *)
(* Build        : full-literal COQLIB/ROCQLIB export, then coqc              *)
(*                -native-compiler no -q with the certified vo tree, Local,  *)
(*                the adapter world and this directory as -Q roots, under    *)
(*                the thermal guard (Rocq 9.1.0).                            *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.
Require Import Local.LW0LeibSeparation.
Require Import piu1932_tight_bound_instantiated.
Require Import piu_mu_criterion.
Require Import piu_zz_bridge_real.
Require Import piu_zz_poincare_engine.
Require Import piu_zz_padic_clearing.
Require Import piu_zz_tau_enclosure_base.
Require Import piu_zz_mu_assembly.

(* ==== Section 1. Criterion data pins (corrected exponent pairing) ==== *)

(* The criterion MuBound yields |q*x - p| >= c0 * q^-(sigma+tau)/tau, so the
   point-distance exponent is 1 + (sigma+tau)/tau.  The rate slot threshold
   ck_alpha c0 8 q is the height-form exponent 8, which requires
   (sigma+tau)/tau = 7, i.e. sigma = 6*tau.  With tau = 2 this pins
   sigma = 12 while kappa = 35831808 and c0 = 1/71663616 are unchanged. *)
Definition piu_zz_ec_tau : nat := 2%nat.
Definition piu_zz_ec_sigma : nat := 12%nat.
Definition piu_zz_ec_kappa : Q := (35831808 # 1)%Q.

Lemma piu_zz_ec_sigma_six_tau : piu_zz_ec_sigma = (6 * piu_zz_ec_tau)%nat.
Proof. reflexivity. Qed.

Lemma piu_zz_ec_span : (piu_zz_ec_sigma + piu_zz_ec_tau = 14)%nat.
Proof. reflexivity. Qed.

Example piu_zz_ec_exp_int :
  Nat.div (piu_zz_ec_sigma + piu_zz_ec_tau) piu_zz_ec_tau = 7%nat.
Proof. reflexivity. Qed.

Example piu_zz_ec_exp_point :
  (1 + Nat.div (piu_zz_ec_sigma + piu_zz_ec_tau) piu_zz_ec_tau = 8)%nat.
Proof. reflexivity. Qed.

Lemma piu_zz_ec_kappa_pos : piu_mu_QltT 0 piu_zz_ec_kappa.
Proof. apply piu_mu_QltT_i. unfold piu_zz_ec_kappa, Qlt. cbn. lia. Qed.

Example piu_zz_ec_kappa_c0_bool :
  Qeq_bool ((2 # 1) * (piu_zz_ec_kappa * piu_zz_c0_criterion)%Q)%Q (1 # 1)%Q = true.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_ec_kappa_c0 :
  S02_CauchyComplete.QeqT
    ((2 # 1) * (piu_zz_ec_kappa * piu_zz_c0_criterion)%Q)%Q (1 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma piu_zz_ec_c0_inv :
  S02_CauchyComplete.QeqT
    ((1 # 1) / (2 * piu_zz_ec_kappa)%Q)%Q piu_zz_c0_criterion.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ==== Section 2. Escape window (unconditional arithmetic face) ==== *)

(* Escape index candidate: the escape premise of the criterion needs an
   index n with 2*q <= 2^(tau*n) and (2^(sigma*n))^tau <= kappa^tau *
   q^(sigma+tau).  With tau = 2 and sigma = 12 the window is nonempty for
   every q >= 1; the explicit candidate below lands inside it. *)
Definition piu_zz_ec_nesc (q : nat) : nat :=
  Datatypes.S (Nat.div2 (Datatypes.S (Nat.log2 q))).

Lemma piu_zz_ec_nesc_bounds : forall q : nat,
  (Nat.log2 q + 2 <= 2 * piu_zz_ec_nesc q <= Nat.log2 q + 3)%nat.
Proof.
  intros q. unfold piu_zz_ec_nesc.
  set (m := Nat.log2 q) in *.
  assert (Hd : (Datatypes.S m
                = 2 * Nat.div2 (Datatypes.S m)
                + Nat.b2n (Nat.odd (Datatypes.S m)))%nat)
    by apply Nat.div2_odd.
  assert (Hb : (Nat.b2n (Nat.odd (Datatypes.S m)) <= 1)%nat).
  { destruct (Nat.odd (Datatypes.S m)); cbn; lia. }
  lia.
Qed.

Lemma piu_zz_ec_escape_E1_nat : forall q : nat, (1 <= q)%nat ->
  (2 * q < 2 ^ (2 * piu_zz_ec_nesc q))%nat.
Proof.
  intros q Hq.
  destruct (Nat.log2_spec (2 * q)) as [_ Hlt]; [lia |].
  rewrite (Nat.log2_double q) in Hlt by lia.
  apply (Nat.lt_le_trans _ (2 ^ (Datatypes.S (Datatypes.S (Nat.log2 q))))).
  - exact Hlt.
  - apply Nat.pow_le_mono_r; [lia |].
    replace (Datatypes.S (Datatypes.S (Nat.log2 q)))%nat
      with (Nat.log2 q + 2)%nat by lia.
    apply (proj1 (piu_zz_ec_nesc_bounds q)).
Qed.

Lemma piu_zz_ec_escape_E3_nat : forall q : nat, (1 <= q)%nat ->
  (2 ^ (24 * piu_zz_ec_nesc q) <= 2 ^ 50 * q ^ 14)%nat.
Proof.
  intros q Hq.
  assert (Hhi : (2 * piu_zz_ec_nesc q <= Nat.log2 q + 3)%nat)
    by apply piu_zz_ec_nesc_bounds.
  destruct (Nat.log2_spec q) as [Hge _]; [lia |].
  assert (H12 : (2 ^ (12 * Nat.log2 q) <= q ^ 12)%nat).
  { replace (12 * Nat.log2 q)%nat with (Nat.log2 q * 12)%nat by lia.
    rewrite Nat.pow_mul_r.
    apply Nat.pow_le_mono_l. exact Hge. }
  apply (Nat.le_trans _ (2 ^ (12 * Nat.log2 q + 36))).
  - apply Nat.pow_le_mono_r; [lia | lia].
  - rewrite Nat.pow_add_r.
    apply (Nat.le_trans _ (q ^ 12 * 2 ^ 36)).
    + apply Nat.mul_le_mono; [exact H12 | apply Nat.le_refl].
    + apply (Nat.le_trans _ (q ^ 14 * 2 ^ 36)).
      * apply Nat.mul_le_mono; [apply Nat.pow_le_mono_r; lia | apply Nat.le_refl].
      * replace (q ^ 14 * 2 ^ 36)%nat with (2 ^ 36 * q ^ 14)%nat
          by (apply Nat.mul_comm).
        apply Nat.mul_le_mono_r. apply Nat.pow_le_mono_r; lia.
Qed.

(* Q-layer bridges: Z-cast multiplication, two-powers, casted powers *)
Lemma piu_zz_ec_inject_mul : forall x y : Z,
  S02_CauchyComplete.QeqT (inject_Z (x * y)) (inject_Z x * inject_Z y)%Q.
Proof.
  intros x y. apply qeq_imp_qeqT.
  unfold inject_Z, Qmult, Qeq. cbn. ring.
Qed.

Lemma piu_zz_ec_Qpower2 : forall x : Q, (0 < x)%Q ->
  S02_CauchyComplete.QeqT (Qpower x (Z.of_nat 2)) (x * x)%Q.
Proof.
  intros x Hx. apply qeq_imp_qeqT.
  cbn [Z.of_nat Pos.of_nat Qpower Qpower_pos].
  unfold Qeq. cbn. ring.
Qed.

Lemma piu_zz_ec_inject_pow : forall (z : Z) (k : nat),
  (0 < z)%Z ->
  S02_CauchyComplete.QeqT (Qpower (inject_Z z) (Z.of_nat k))
    (inject_Z (z ^ Z.of_nat k))%Q.
Proof.
  intros z k Hz. induction k as [|k IH].
  - apply qeq_imp_qeqT. cbn [Z.of_nat].
    rewrite Qpower_0_r, Z.pow_0_r. reflexivity.
  - apply qeq_imp_qeqT.
    assert (Hne : ~ (inject_Z z == 0)%Q).
    { intro Hc.
      assert (Hz0 : (z = 0)%Z).
      { unfold inject_Z, Qeq in Hc. cbn [Qnum Qden] in Hc. lia. }
      lia. }
    assert (Hs : (Z.of_nat (Datatypes.S k) = Z.of_nat k + 1)%Z) by lia.
    rewrite Hs.
    rewrite Qpower_plus by exact Hne.
    replace (Qpower (inject_Z z) 1) with (inject_Z z) by reflexivity.
    rewrite Z.pow_add_r by lia. rewrite Z.pow_1_r.
    pose proof (qeqT_imp_qeq _ _ (piu_zz_ec_inject_mul (z ^ Z.of_nat k) z)) as E.
    rewrite E.
    pose proof (qeqT_imp_qeq _ _ IH) as IHr. rewrite IHr.
    reflexivity.
Qed.

Lemma piu_zz_ec_qpow_cast : forall m n : nat,
  S02_CauchyComplete.QeqT (piu_zz_qpow (Z.of_nat m # 1)%Q n)
    (inject_Z (Z.of_nat (m ^ n)))%Q.
Proof.
  intros m n. induction n as [|n IH].
  - apply qeq_imp_qeqT. cbn [piu_zz_qpow]. rewrite Nat.pow_0_r.
    unfold inject_Z. cbn. reflexivity.
  - apply qeq_imp_qeqT. cbn [piu_zz_qpow].
    rewrite (Nat.pow_succ_r m n) by lia. rewrite Nat2Z.inj_mul.
    pose proof (qeqT_imp_qeq _ _
      (piu_zz_ec_inject_mul (Z.of_nat m) (Z.of_nat (m ^ n)))) as E.
    rewrite E.
    pose proof (qeqT_imp_qeq _ _ IH) as IHr. rewrite IHr.
    reflexivity.
Qed.

Lemma piu_zz_ec_qpow_Qpower : forall (x : Q) (n : nat), (0 < x)%Q ->
  S02_CauchyComplete.QeqT (q_pow x n) (Qpower x (Z.of_nat n))%Q.
Proof.
  intros x n Hx. induction n as [|n IH].
  - apply qeq_imp_qeqT. cbn [q_pow Z.of_nat]. rewrite Qpower_0_r. reflexivity.
  - apply qeq_imp_qeqT. cbn [q_pow].
    assert (Hs : (Z.of_nat (Datatypes.S n) = Z.of_nat n + 1)%Z) by lia.
    rewrite Hs at 1. rewrite Qpower_plus by (intro Hc; exfalso; lra).
    rewrite Qpower_1_r. pose proof (qeqT_imp_qeq _ _ IH) as IHr. rewrite IHr.
    apply Qmult_comm.
Qed.

Lemma piu_zz_ec_qpow_one : forall n : nat,
  S02_CauchyComplete.QeqT (piu_zz_qpow 1%Q n) 1%Q.
Proof.
  intros n. induction n as [|n IH].
  - apply qeq_imp_qeqT. cbn [piu_zz_qpow]. reflexivity.
  - apply qeq_imp_qeqT. cbn [piu_zz_qpow].
    pose proof (qeqT_imp_qeq _ _ IH) as IHr. rewrite IHr. reflexivity.
Qed.

Lemma piu_zz_ec_epos_pos : forall k : nat, (0 <= piu_mu_epos k)%Q.
Proof.
  intros k. unfold piu_mu_epos. unfold Qle, inject_Z. cbn.
  assert (Hp : (0 < 2 ^ Z.of_nat k)%Z)
    by (apply Z.pow_pos_nonneg; lia).
  lia.
Qed.

Lemma piu_zz_ec_escape_E1 : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
    (piu_mu_epos (2 * piu_zz_ec_nesc q)).
Proof.
  intros q Hq. apply piu_mu_Zle_Qle.
  pose proof (piu_zz_ec_escape_E1_nat q Hq) as Hnat.
  apply (Nat.lt_le_incl) in Hnat.
  replace (2 ^ Z.of_nat (2 * piu_zz_ec_nesc q))%Z
    with (Z.of_nat (2 ^ (2 * piu_zz_ec_nesc q)))%Z
    by (rewrite Nat2Z.inj_pow; reflexivity).
  apply Nat2Z.inj_le. exact Hnat.
Qed.

Lemma piu_zz_ec_escape_E3 : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (piu_mu_epos (12 * piu_zz_ec_nesc q) ^ Z.of_nat 2)
    (piu_zz_ec_kappa ^ Z.of_nat 2
     * inject_Z (Z.of_nat q) ^ Z.of_nat 14)%Q.
Proof.
  intros q Hq.
  pose proof (piu_zz_ec_escape_E3_nat q Hq) as Hnat.
  assert (HposE : (0 < inject_Z (2 ^ Z.of_nat (12 * piu_zz_ec_nesc q)))%Q).
  { unfold inject_Z, Qlt. cbn [Qnum Qden].
    replace (2 ^ Z.of_nat (12 * piu_zz_ec_nesc q))%Z
      with (Z.of_nat (2 ^ (12 * piu_zz_ec_nesc q)))%Z
      by (rewrite Nat2Z.inj_pow; reflexivity).
    assert (2 ^ (12 * piu_zz_ec_nesc q) > 0)%nat
      by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    lia. }
  (* HL : the left side equals inject_Z of the nat power *)
  assert (HL : S02_CauchyComplete.QeqT
                 (piu_mu_epos (12 * piu_zz_ec_nesc q) ^ Z.of_nat 2)
                 (inject_Z (Z.of_nat (2 ^ (24 * piu_zz_ec_nesc q))))%Q).
  { unfold piu_mu_epos. apply qeq_imp_qeqT.
    pose proof (qeqT_imp_qeq _ _
      (piu_zz_ec_Qpower2 (inject_Z (2 ^ Z.of_nat (12 * piu_zz_ec_nesc q)))
        HposE)) as E1.
    rewrite E1.
    pose proof (qeqT_imp_qeq _ _
      (piu_zz_ec_inject_mul (2 ^ Z.of_nat (12 * piu_zz_ec_nesc q))
        (2 ^ Z.of_nat (12 * piu_zz_ec_nesc q)))) as E2.
    rewrite <- E2.
    replace (2 ^ Z.of_nat (12 * piu_zz_ec_nesc q) *
             2 ^ Z.of_nat (12 * piu_zz_ec_nesc q))%Z
      with (2 ^ (Z.of_nat (12 * piu_zz_ec_nesc q) + Z.of_nat (12 * piu_zz_ec_nesc q)))%Z
      by (rewrite <- Z.pow_add_r by lia; reflexivity).
    replace (Z.of_nat (12 * piu_zz_ec_nesc q) + Z.of_nat (12 * piu_zz_ec_nesc q))%Z
      with (Z.of_nat (24 * piu_zz_ec_nesc q))%Z by lia.
    replace (2 ^ Z.of_nat (24 * piu_zz_ec_nesc q))%Z
      with (Z.of_nat (2 ^ (24 * piu_zz_ec_nesc q)))%Z
      by (rewrite Nat2Z.inj_pow; reflexivity).
    reflexivity. }
  apply piu_mu_QleT_i.
  pose proof (qeqT_imp_qeq _ _ HL) as HLr. rewrite HLr.
  (* step A: nat fact to inject_Z of 2^50 * q^14 *)
  apply (Qle_trans _ (inject_Z (Z.of_nat (2 ^ 50 * q ^ 14)))).
  - apply piu_mu_Zle_Qle. apply Nat2Z.inj_le. exact Hnat.
  - (* step B: split the product, dominate the 2^50 factor in the binary Q layer *)
    assert (Es : S02_CauchyComplete.QeqT
                   (inject_Z (Z.of_nat (2 ^ 50 * q ^ 14)))
                   (inject_Z (Z.of_nat (2 ^ 50))
                    * inject_Z (Z.of_nat (q ^ 14)))%Q).
    { rewrite Nat2Z.inj_mul. apply piu_zz_ec_inject_mul. }
    pose proof (qeqT_imp_qeq _ _ Es) as Esr. rewrite Esr.
    assert (Hk50 : (inject_Z (Z.of_nat (2 ^ 50))
                    <= piu_zz_ec_kappa ^ Z.of_nat 2)%Q).
    { assert (Hkap0 : (0 < piu_zz_ec_kappa)%Q)
        by (unfold piu_zz_ec_kappa, Qlt; cbn; lia).
      pose proof (qeqT_imp_qeq _ _
        (piu_zz_ec_Qpower2 piu_zz_ec_kappa Hkap0)) as Ek2.
      apply (Qle_trans _ (inject_Z (2 ^ Z.of_nat 25)
                          * inject_Z (2 ^ Z.of_nat 25))%Q).
      - assert (HZ : (Z.of_nat (2 ^ 50)
                      = 2 ^ Z.of_nat 25 * 2 ^ Z.of_nat 25)%Z).
        { rewrite (Nat2Z.inj_pow 2 50).
          replace (Z.of_nat 2)%Z with 2%Z by reflexivity.
          rewrite <- Z.pow_add_r by lia. f_equal; lia. }
        unfold Qle, inject_Z, Qmult. cbn [Qnum Qden Z.mul].
        rewrite HZ. lia.
      - apply (Qle_trans _ (inject_Z (2 ^ Z.of_nat 25)
                              * inject_Z 35831808)%Q).
        + apply (Qmult_le_compat_r (inject_Z (2 ^ Z.of_nat 25))
                   (inject_Z 35831808) (inject_Z (2 ^ Z.of_nat 25))).
          * apply piu_mu_Zle_Qle. cbn. lia.
          * unfold Qle, inject_Z. cbn. lia.
        + apply (Qle_trans _ (inject_Z 35831808 * inject_Z 35831808)%Q).
          * apply (Qmult_le_compat_r (inject_Z (2 ^ Z.of_nat 25))
                     (inject_Z 35831808) (inject_Z 35831808)).
            -- apply piu_mu_Zle_Qle. cbn. lia.
            -- unfold Qle, inject_Z. cbn. lia.
          * rewrite Ek2. apply Qle_refl. }
    rewrite (Nat2Z.inj_pow q 14).
    rewrite (qeqT_imp_qeq _ _
      (piu_zz_ec_inject_pow (Z.of_nat q) 14 ltac:(lia))).
    apply Qmult_le_compat_r.
    + exact Hk50.
    + apply piu_mu_Zle_Qle. apply Z.lt_le_incl. apply Z.pow_pos_nonneg; lia.
Qed.

(* ==== Section 3. Rate account: MuBound to the point-distance rate ==== *)

Lemma piu_zz_ec_tau_ge1 : piu_mu_NleT 1 piu_zz_ec_tau.
Proof. apply piu_mu_NleT_i. unfold piu_zz_ec_tau. lia. Qed.

Lemma piu_zz_ec_inv_nneg : forall x : Q, (0 < x)%Q -> (0 <= / x)%Q.
Proof.
  intros x Hx. destruct (Qlt_le_dec 0 (/ x)) as [HL | HR].
  - apply Qlt_le_weak. exact HL.
  - exfalso.
    assert (Hle : (/ x * x <= 0 * x)%Q).
    { apply Qmult_le_compat_r; [exact HR | apply Qlt_le_weak; exact Hx]. }
    rewrite (Qmult_comm (/ x) x) in Hle.
    rewrite Qmult_inv_r in Hle by (intro Hc; exfalso; lra).
    assert (Hz : (0 * x == 0)%Q) by ring.
    rewrite Hz in Hle. lra.
Qed.

Lemma piu_zz_ec_pow_pos : forall (x : Q) (n : nat),
  (0 < x)%Q -> (0 < Qpower x (Z.of_nat n))%Q.
Proof.
  intros x n Hx. induction n as [|k IH].
  - rewrite Nat2Z.inj_0, Qpower_0_r. unfold Qlt. cbn. lia.
  - assert (Hs : (Z.of_nat (Datatypes.S k) = Z.of_nat k + 1)%Z) by lia.
    rewrite Hs, (Qpower_plus x (Z.of_nat k) 1 ltac:(intro Hc; exfalso; lra)),
      (Qpower_1_r x).
    apply Qmult_lt_0_compat; assumption.
Qed.

Lemma piu_zz_ec_pow_le_one : forall (x : Q) (n : nat),
  (0 < x)%Q -> (x <= 1)%Q -> (Qpower x (Z.of_nat n) <= 1)%Q.
Proof.
  intros x n Hx Hx1. induction n as [|k IH].
  - rewrite Nat2Z.inj_0, Qpower_0_r. apply Qle_refl.
  - assert (Hs : (Z.of_nat (Datatypes.S k) = Z.of_nat k + 1)%Z) by lia.
    rewrite Hs, (Qpower_plus x (Z.of_nat k) 1 ltac:(intro Hc; exfalso; lra)),
      (Qpower_1_r x).
    apply (Qle_trans _ (x * Qpower x (Z.of_nat k))).
    + rewrite (Qmult_comm (Qpower x (Z.of_nat k)) x). apply Qle_refl.
    + apply (Qle_trans _ (1 * Qpower x (Z.of_nat k))).
      * apply Qmult_le_compat_r; [exact Hx1 |
          apply Qlt_le_weak; apply (piu_zz_ec_pow_pos x k Hx)].
      * rewrite Qmult_1_l. exact IH.
Qed.

Lemma piu_zz_ec_pow_lt : forall (x y : Q), (0 < x)%Q -> (x < y)%Q ->
  forall n : nat, (1 <= n)%nat ->
  (Qpower x (Z.of_nat n) < Qpower y (Z.of_nat n))%Q.
Proof.
  intros x y Hx Hxy n Hn. revert Hn.
  induction n as [|k IH]; intros Hn.
  - exfalso. lia.
  - destruct k as [|j].
    + cbn [Z.of_nat]. rewrite (Qpower_1_r x), (Qpower_1_r y). exact Hxy.
    + assert (Hs : (Z.of_nat (Datatypes.S (Datatypes.S j))
                    = Z.of_nat (Datatypes.S j) + 1)%Z) by lia.
      rewrite Hs,
        (Qpower_plus x (Z.of_nat (Datatypes.S j)) 1 ltac:(intro Hc; exfalso; lra)),
        (Qpower_plus y (Z.of_nat (Datatypes.S j)) 1 ltac:(intro Hc; exfalso; lra)),
        (Qpower_1_r x), (Qpower_1_r y).
      rewrite (Qmult_comm (Qpower x (Z.of_nat (Datatypes.S j))) x).
      assert (Hxyk : (Qpower x (Z.of_nat (Datatypes.S j))
                      < Qpower y (Z.of_nat (Datatypes.S j)))%Q)
        by (apply IH; lia).
      apply (Qlt_le_trans _ (y * Qpower x (Z.of_nat (Datatypes.S j)))).
      * apply Qmult_lt_compat_r;
          [apply piu_zz_ec_pow_pos; exact Hx | exact Hxy].
      * rewrite (Qmult_comm y (Qpower x (Z.of_nat (Datatypes.S j)))).
        apply Qmult_le_compat_r;
          [apply Qlt_le_weak; exact Hxyk
          | apply Qlt_le_weak; apply (Qlt_trans 0 x y Hx Hxy)].
Qed.

Lemma piu_zz_ec_inv_pos : forall x : Q, (0 < x)%Q -> (0 < / x)%Q.
Proof.
  intros x Hx. destruct (Qlt_le_dec 0 (/ x)) as [HL | HR].
  - exact HL.
  - exfalso.
    assert (Hle : (/ x * x <= 0 * x)%Q).
    { apply Qmult_le_compat_r; [exact HR | apply Qlt_le_weak; exact Hx]. }
    rewrite (Qmult_comm (/ x) x) in Hle.
    rewrite Qmult_inv_r in Hle by (intro Hc; exfalso; lra).
    assert (Hz : (0 * x == 0)%Q) by ring.
    rewrite Hz in Hle. lra.
Qed.

Lemma piu_zz_ec_inv_lt : forall x y : Q,
  (0 < x)%Q -> (x < y)%Q -> (/ y < / x)%Q.
Proof.
  intros x y Hx Hxy.
  assert (Hypos : (0 < / y)%Q)
    by (apply piu_zz_ec_inv_pos; apply (Qlt_trans 0 x y Hx Hxy)).
  assert (Hxpos : (0 < / x)%Q) by (apply piu_zz_ec_inv_pos; exact Hx).
  assert (Heq2 : (x * / x == 1)%Q) by (apply Qmult_inv_r; intro Hc; exfalso; lra).
  assert (Hsimpl : (y * (x * / y) == x)%Q).
  { rewrite Qmult_assoc, (Qmult_comm y x), <- Qmult_assoc.
    rewrite Qmult_inv_r by (intro Hc; exfalso; lra).
    rewrite Qmult_1_r. reflexivity. }
  destruct (Qlt_le_dec (/ y) (/ x)) as [HL | HR].
  - exact HL.
  - exfalso.
    assert (H1 : (x * / x <= x * / y)%Q).
    { rewrite <- (Qmult_comm (/ x) x), <- (Qmult_comm (/ y) x).
      apply Qmult_le_compat_r; [exact HR | apply Qlt_le_weak; exact Hx]. }
    rewrite Heq2 in H1.
    assert (H2 : (y * 1 <= y * (x * / y))%Q).
    { apply (Qle_trans _ ((x * / y) * y)%Q).
      - rewrite <- (Qmult_comm 1 y).
        apply Qmult_le_compat_r;
          [exact H1 | apply Qlt_le_weak; apply (Qlt_trans 0 x y Hx Hxy)].
      - rewrite (Qmult_comm (x * / y) y). apply Qle_refl. }
    rewrite Hsimpl in H2. rewrite Qmult_1_r in H2. lra.
Qed.

Lemma piu_zz_ec_red_eq : forall q : Q,
  S02_CauchyComplete.QeqT
    (inject_Z (Z.of_nat (Pos.to_nat (Qden (Qred q)))) * q)
    (inject_Z (Qnum (Qred q)))%Q.
Proof.
  intros q. apply qeq_imp_qeqT.
  unfold Qmult, inject_Z, Qeq. cbn [Qnum Qden].
  rewrite Znat.positive_nat_Z. cbn [Pos.mul].
  pose proof (Qred_correct q) as Hr. unfold Qeq in Hr.
  rewrite Hr. rewrite Z.mul_1_r. apply Z.mul_comm.
Qed.

(* The first-power rate face: the MuBound conclusion unwinds to the
   first-power inequality c0 <= dval(q0,-p0) * q0^7 (square-root step via
   order-reflecting powers on the positive domain). *)
Lemma piu_zz_ec_rate_c0 : forall (dv : Z -> Z -> Q) (p0 : Z) (q0 : nat),
  (1 <= q0)%nat -> (0 <= dv (Z.of_nat q0) (- p0)%Z)%Q ->
  piu_mu_MuBound piu_zz_ec_sigma piu_zz_ec_tau dv piu_zz_ec_kappa
    (1 # 2)%Q ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * piu_zz_ec_kappa)%Q)
    (dv (Z.of_nat q0) (- p0)%Z
     * Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 7))%Q.
Proof.
  intros dv p0 q0 Hq0 Hnn Hmb.
  pose proof (Hmb p0 q0 Hq0) as Hm. destruct Hm as [Hm].
  unfold piu_zz_ec_sigma, piu_zz_ec_tau in Hm. cbn [Z.of_nat] in Hm.
  remember (dv (Z.of_nat q0) (- p0)%Z) as W eqn:HW.
  remember (inject_Z (Z.of_nat q0)) as bQ eqn:HQb.
  remember (Qpower bQ (Z.of_nat 7)) as B7 eqn:HQ7.
  destruct piu_zz_ec_kappa_pos as [Hk].
  assert (Hbpos : (0 < bQ)%Q).
  { rewrite HQb. unfold inject_Z, Qlt. cbn. lia. }
  assert (HB7pos : (0 < B7)%Q) by (rewrite HQ7; apply piu_zz_ec_pow_pos; exact Hbpos).
  assert (Hdv : (0 < W)%Q).
  { destruct (Qlt_le_dec 0 W) as [HL | HR].
    - exact HL.
    - exfalso. destruct (Qeq_dec W 0%Q) as [He | Hne].
      + rewrite He in Hm. cbn in Hm. lra.
      + lra. }
  assert (HWB : (Qpower W (Z.of_nat 2) * Qpower bQ (Z.of_nat 14)
                == Qpower (W * B7)%Q (Z.of_nat 2))%Q).
  { rewrite HQ7.
    rewrite <- (Qmult_power W (Qpower bQ (Z.of_nat 7)) (Z.of_nat 2)).
    reflexivity. }
  assert (Hsq : S02_CauchyComplete.QleT' (Qpower (1 # 2)%Q (Z.of_nat 2))
                  (Qpower (piu_zz_ec_kappa * W * B7)%Q (Z.of_nat 2))).
  { apply piu1932_qle_to_qleT'.
    rewrite <- Qmult_assoc.
    rewrite (Qmult_power piu_zz_ec_kappa (W * B7) (Z.of_nat 2)), <- HWB.
    rewrite <- Qmult_assoc in Hm. exact Hm. }
  assert (HkapW : (0 < piu_zz_ec_kappa * W * B7)%Q).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; assumption.
    - exact HB7pos. }
  pose proof (piu_zz_mu_qpow_inject 2%nat (1 # 2)%Q
    (piu_zz_ec_kappa * W * B7)%Q ltac:(lia) ltac:(unfold Qlt; cbn; lia)
    HkapW Hsq) as Hfirst.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hfirst) as Hf.
  rewrite <- (Qmult_assoc piu_zz_ec_kappa W B7) in Hf.
  rewrite (Qmult_comm piu_zz_ec_kappa (W * B7)) in Hf.
  assert (Hc0split : ((1 # 1) / (2 * piu_zz_ec_kappa)
                      == (1 # 2) * / piu_zz_ec_kappa)%Q)
    by (unfold Qdiv, Qmult; cbn; ring).
  apply piu1932_qle_to_qleT'.
  rewrite Hc0split.
  assert (Hcancel : ((W * B7) * piu_zz_ec_kappa * / piu_zz_ec_kappa
                     == W * B7)%Q).
  { rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r by (intro Hc; exfalso; lra).
    rewrite Qmult_1_r. reflexivity. }
  rewrite <- Hcancel.
  apply Qmult_le_compat_r; [exact Hf | apply piu_zz_ec_inv_nneg;
    apply piu_zz_ec_kappa_pos].
Qed.

(* The distance-rate face: the first-power inequality plus the mirror
   premise dval(q0,-p0) <= |q0*xL-p0| yields the point distance bound
   |xL(k)-r| >= c0/q0^8 at the reduced height coordinate. *)
Lemma piu_zz_ec_rate_dist : forall (dv : Z -> Z -> Q) (r : Q) (p0 : Z)
    (q0 : nat) (k : nat),
  S02_CauchyComplete.QeqT (inject_Z (Z.of_nat q0) * r) (inject_Z p0) ->
  (1 <= q0)%nat ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * piu_zz_ec_kappa)%Q)
    (dv (Z.of_nat q0) (- p0)%Z
     * Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 7))%Q ->
  S02_CauchyComplete.QleT' (dv (Z.of_nat q0) (- p0)%Z)
    (Qabs (inject_Z (Z.of_nat q0) * lw0m_xL k - inject_Z p0)) ->
  S02_CauchyComplete.QleT' ((1 # 1) / (2 * piu_zz_ec_kappa)%Q
          / Qpower (inject_Z (Z.of_nat q0)) (Z.of_nat 8))%Q
    (Qabs (lw0m_xL k - r)).
Proof.
  intros dv r p0 q0 k Hred Hq0 Hc0 Hx.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hc0) as H1.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hx) as H2.
  remember (dv (Z.of_nat q0) (- p0)%Z) as W eqn:HW.
  remember (inject_Z (Z.of_nat q0)) as bQ eqn:HQb.
  remember (Qpower bQ (Z.of_nat 7)) as B7 eqn:HQ7.
  remember (Qpower bQ (Z.of_nat 8)) as B8 eqn:HQ8.
  remember (Qabs (lw0m_xL k - r)) as X eqn:HX.
  assert (Hbpos : (0 < bQ)%Q).
  { rewrite HQb. unfold inject_Z, Qlt. cbn. lia. }
  assert (HB7pos : (0 < B7)%Q) by (rewrite HQ7; apply piu_zz_ec_pow_pos; exact Hbpos).
  assert (HB8pos : (0 < B8)%Q) by (rewrite HQ8; apply piu_zz_ec_pow_pos; exact Hbpos).
  assert (HB8eq : (B8 == bQ * B7)%Q).
  { rewrite HQ8, HQ7.
    replace (Z.of_nat 8)%Z with (Z.of_nat 1 + Z.of_nat 7)%Z by reflexivity.
    rewrite (Qpower_plus bQ (Z.of_nat 1) (Z.of_nat 7)
      ltac:(intro Hc; exfalso; lra)), (Qpower_1_r bQ). reflexivity. }
  (* merge: c0 <= X * B8 *)
  rewrite HX.
  assert (Habs : (Qabs (bQ * lw0m_xL k - inject_Z p0) == bQ * Qabs (lw0m_xL k - r))%Q).
  { rewrite <- (qeqT_imp_qeq _ _ Hred).
    assert (Hsp : (bQ * lw0m_xL k - bQ * r == bQ * (lw0m_xL k - r))%Q) by ring.
    rewrite Hsp, Qabs_Qmult, (Qabs_pos bQ (Qlt_le_weak 0 bQ Hbpos)).
    reflexivity. }
  assert (H3 : ((1 # 1) / (2 * piu_zz_ec_kappa) <= X * B8)%Q).
  { apply (Qle_trans _ (W * B7)).
    - exact H1.
    - apply (Qle_trans _ (Qabs (bQ * lw0m_xL k - inject_Z p0) * B7)).
      + apply Qmult_le_compat_r. exact H2.
        apply Qlt_le_weak. exact HB7pos.
      + rewrite Habs, (Qmult_comm bQ (Qabs (lw0m_xL k - r))), <- Qmult_assoc,
          <- HB8eq, <- HX.
        apply Qle_refl. }
  apply piu1932_qle_to_qleT'. unfold Qdiv.
  apply (Qle_trans _ (X * B8 * / B8)).
  - apply Qmult_le_compat_r; [exact H3 | apply (piu_zz_ec_inv_nneg B8 HB8pos)].
  - rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r by (intro Hc; exfalso; lra).
    rewrite Qmult_1_r, <- HX. apply Qle_refl.
Qed.

(* the margin step: with v < u and c positive, the halfway margin keeps
   the strict inequality (the irrationality-rate face) *)
Lemma piu_zz_ec_margin_lt : forall (c u v ab : Q),
  (0 < c)%Q -> (v < u)%Q -> (c * u <= ab)%Q ->
  (c * v + (1 # 2) * (c * (u - v)) < ab)%Q.
Proof.
  intros c u v ab Hc Hvu Hcu.
  assert (Hh1 : ((1 # 2) * (c * v) < (1 # 2) * (c * u))%Q).
  { rewrite (Qmult_comm (1 # 2) (c * v)), (Qmult_comm (1 # 2) (c * u)).
    apply (Qmult_lt_compat_r (c * v)%Q (c * u)%Q (1 # 2)%Q).
    - unfold Qlt. cbn. lia.
    - rewrite <- (Qmult_comm v c), <- (Qmult_comm u c).
      apply (Qmult_lt_compat_r v u c); [exact Hc | exact Hvu]. }
  assert (Heq : (c * v + (1 # 2) * (c * (u - v))
                 == (1 # 2) * (c * v) + (1 # 2) * (c * u))%Q)
    by ring.
  rewrite Heq.
  apply (Qlt_le_trans _ ((1 # 2) * (c * u) + (1 # 2) * (c * u))).
  - apply (Qplus_lt_le_compat ((1 # 2) * (c * v))%Q ((1 # 2) * (c * u))%Q
      ((1 # 2) * (c * u))%Q ((1 # 2) * (c * u))%Q).
    + exact Hh1.
    + apply Qle_refl.
  - assert (Hy : ((1 # 2) * (c * u) + (1 # 2) * (c * u) == c * u)%Q)
      by ring.
    rewrite Hy. exact Hcu.
Qed.

(* ==== Section 4. E-side carrier and the conditional chain ==== *)

Section EC.
Variable A B : nat -> Z.
Variable dv : Z -> Z -> Q.

(* positivity of the residual mirror *)
Hypothesis Hp : forall a b : Z, piu_mu_QleT 0 (dv a b).
(* triangular mirror consistency *)
Hypothesis Htri : forall (a b p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
    ((inject_Z (Z.of_nat q) * dv a b
      + inject_Z (Z.abs b) * dv (Z.of_nat q) (- p))%Q).
(* coefficient growth at the corrected pinning sigma = 12 *)
Hypothesis Hcoef : forall n : nat,
  piu_mu_and2
    (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n))%Z)
    (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n))%Z).
(* escape supply (the nonvanishing limb is the p-adic clearing gap,
   carried explicitly) *)
Hypothesis Hesc : forall (p : Z) (q : nat), (1 <= q)%nat ->
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
       (piu_mu_epos (piu_zz_ec_tau * n)))
    (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
    (piu_mu_QleT (Qpower (piu_mu_epos (piu_zz_ec_sigma * n))
                         (Z.of_nat piu_zz_ec_tau))
      (Qpower piu_zz_ec_kappa (Z.of_nat piu_zz_ec_tau)
       * Qpower (inject_Z (Z.of_nat q))
          (Z.of_nat (piu_zz_ec_sigma + piu_zz_ec_tau)))%Q)).
(* the cage: the carrier magnitude is exponentially bounded for all n *)
Hypothesis Hcage : forall n : nat,
  S02_CauchyComplete.QleT' (dv (A n) (B n)) (Qpower (13 # 400)%Q (Z.of_nat n)).
(* the exit mirror: dval(b,-a) is eventually bounded by |b*xL(k)-a| *)
Hypothesis Hexit : forall a b : Z, (1 <= b)%Z ->
  sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
    S02_CauchyComplete.QleT' (dv b (- a)%Z)
      (Qabs (inject_Z b * lw0m_xL k - inject_Z a))).

(* the value face derived from the cage: dval * 2^(tau*n) <= 1 *)
Lemma ec_hval : forall n : nat,
  piu_mu_QleT (dv (A n) (B n) * piu_mu_epos (piu_zz_ec_tau * n)) (1 # 1).
Proof.
  intros n. pose proof (Hcage n) as Hc.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ Hc) as HD.
  unfold piu_mu_epos, piu_zz_ec_tau.
  apply piu_mu_QleT_i.
  rewrite <- (qeqT_imp_qeq _ _ (piu_zz_ec_inject_pow 2 (2 * n)%nat ltac:(lia))).
  assert (Hs2 : (Z.of_nat (2 * n) = Z.of_nat n + Z.of_nat n)%Z) by lia.
  rewrite Hs2, (Qpower_plus (inject_Z 2) (Z.of_nat n) (Z.of_nat n)
    ltac:(intro Hc0; exfalso; unfold inject_Z, Qeq in Hc0; cbn in Hc0; lia)).
  apply (Qle_trans _ (Qpower (13 # 400)%Q (Z.of_nat n)
                      * (Qpower (inject_Z 2) (Z.of_nat n)
                         * Qpower (inject_Z 2) (Z.of_nat n)))).
  - apply Qmult_le_compat_r; [exact HD |].
    apply Qmult_le_0_compat;
      [apply Qlt_le_weak; apply (piu_zz_ec_pow_pos (inject_Z 2) n
         ltac:(unfold inject_Z, Qlt; cbn; lia))
      | apply Qlt_le_weak; apply (piu_zz_ec_pow_pos (inject_Z 2) n
         ltac:(unfold inject_Z, Qlt; cbn; lia))].
  - rewrite <- (Qmult_power (inject_Z 2) (inject_Z 2) (Z.of_nat n)).
    replace ((inject_Z 2) * (inject_Z 2))%Q with ((4 # 1)%Q) by reflexivity.
    rewrite <- (Qmult_power (13 # 400)%Q (4 # 1)%Q (Z.of_nat n)).
    exact (piu_zz_ec_pow_le_one ((13 # 400)%Q * (4 # 1)%Q) n
      ltac:(unfold Qlt, Qmult, Qnum, Qden; cbn; lia)
      ltac:(unfold Qle, Qmult, Qnum, Qden; cbn; lia)).
Qed.

(* the main conditional chain (route C): cage + mirrors to the
   rate-form certificate *)
Theorem piu_zz_ec_mu_cond : forall q : Q, (0 < q)%Q ->
  real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros q Hq.
  remember (Pos.to_nat (Qden (Qred q))) as q0 eqn:HQ0.
  remember (Qnum (Qred q)) as p0 eqn:HP0.
  assert (Hq0 : (1 <= q0)%nat).
  { rewrite HQ0.
    destruct (Nat.eq_dec (Pos.to_nat (Qden (Qred q))) 0%nat) as [He | Hne].
    - exfalso. pose proof (Znat.positive_nat_Z (Qden (Qred q))) as Hz.
      rewrite He in Hz. cbn [Z.of_nat] in Hz. discriminate Hz.
    - lia. }
  assert (HbQ : (0 < inject_Z (Z.of_nat q0))%Q)
    by (unfold inject_Z, Qlt; cbn; lia).
  pose proof (NatLe_drop _ _ (lw1m_height_ge2 q)) as Hge2.
  apply (piu_zz_Hmu_rateslot_of_distpt q Hq).
  pose proof (piu_mu_criterion piu_zz_ec_sigma piu_zz_ec_tau dv A B
    piu_zz_ec_kappa piu_zz_ec_tau_ge1 piu_zz_ec_kappa_pos Hp Hcoef
    ec_hval Htri Hesc) as HMBd.
  pose proof (Hp (Z.of_nat q0) (- p0)%Z) as Hnn0. destruct Hnn0 as [Hnn0].
  pose proof (piu_zz_ec_rate_c0 dv p0 q0 Hq0 Hnn0 HMBd) as Hc0.
  destruct (Hexit p0 (Z.of_nat q0) ltac:(unfold inject_Z; cbn; lia)) as [K HK].
  remember (inject_Z (Z.of_nat q0)) as bQ eqn:HQb.
  rewrite HQb in Hc0, HK.
  remember (Qpower bQ (Z.of_nat 8)) as B8 eqn:HQ8.
  remember ((Z.of_nat (lw1m_height q) # 1)%Q) as hQ eqn:HQh.
  remember (Qpower hQ (Z.of_nat 8)) as H8 eqn:HQ8h.
  assert (HhQ : (0 < hQ)%Q) by (rewrite HQh; unfold Qlt; cbn; lia).
  assert (HB8pos : (0 < B8)%Q)
    by (rewrite HQ8; apply piu_zz_ec_pow_pos; exact HbQ).
  assert (HH8pos : (0 < H8)%Q)
    by (rewrite HQ8h; apply (piu_zz_ec_pow_pos hQ 8 HhQ)).
  assert (Hbhlt : (bQ < hQ)%Q).
  { rewrite HQb, HQh. unfold inject_Z, Qlt. cbn [Z.of_nat].
    assert (Hh : lw1m_height q = Datatypes.S (Pos.to_nat (Qden (Qred q))))
      by reflexivity.
    rewrite Hh, <- HQ0. cbn. lia. }
  assert (HB8lt : (B8 < H8)%Q).
  { rewrite HQ8, HQ8h. apply (piu_zz_ec_pow_lt bQ hQ HbQ Hbhlt 8 ltac:(lia)). }
  assert (HUV2 : (/ H8 < / B8)%Q)
    by (apply (piu_zz_ec_inv_lt B8 H8 HB8pos HB8lt)).
  assert (Hc0pos : (0 < piu_zz_c0_criterion)%Q)
    by (unfold piu_zz_c0_criterion, Qlt; cbn; lia).
  pose proof (piu_zz_ec_red_eq q) as Hred0.
  rewrite <- HQ0, <- HP0 in Hred0.
  assert (HrdQ : forall k : nat, (K <= k)%nat ->
    S02_CauchyComplete.QleT'
      ((1 # 1) / (2 * piu_zz_ec_kappa)%Q / B8)%Q
      (Qabs (lw0m_xL k - q))).
  { intros k Hk.
    pose proof (piu_zz_ec_rate_dist dv q p0 q0 k Hred0 Hq0 Hc0 (HK k Hk)) as Hrd.
    rewrite <- HQb, <- HQ8 in Hrd. exact Hrd. }
  exists ((1 # 4) * (piu_zz_c0_criterion * (/ B8 - / H8)))%Q.
  split.
  - apply Qlt_to_QltT. unfold piu_zz_c0_criterion. lra.
  - unfold lw1m_dist_pt. exists K. intros k HkN.
    pose proof (NatLe_drop K k HkN) as Hk.
    apply Qlt_to_QltT.
    unfold piu1932_ck_alpha.
    rewrite <- HQh.
    rewrite (qeqT_imp_qeq _ _ (piu_zz_ec_qpow_Qpower hQ 8 HhQ)), <- HQ8h.
    unfold Qdiv.
    assert (Hth : (piu_zz_c0_criterion * / H8
                   + (2 # 1) * ((1 # 4) * (piu_zz_c0_criterion * (/ B8 - / H8)))
                   == piu_zz_c0_criterion * / H8
                      + (1 # 2) * (piu_zz_c0_criterion * (/ B8 - / H8)))%Q)
      by ring.
    rewrite Hth.
    apply (piu_zz_ec_margin_lt piu_zz_c0_criterion (/ B8)%Q (/ H8)%Q
      (Qabs (lw0m_xL k - q))).
    + exact Hc0pos.
    + exact HUV2.
    + pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (HrdQ k Hk)) as Hle.
      pose proof (qeqT_imp_qeq _ _ piu_zz_ec_c0_inv) as Ec0.
      rewrite Ec0 in Hle. unfold Qdiv in Hle. exact Hle.
Qed.

End EC.
