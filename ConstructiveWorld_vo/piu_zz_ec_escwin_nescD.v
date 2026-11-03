(* ========================================================================= *)
(* Mission      : N5 escape-window turnkey integration (gammaP1 head-ledger  *)
(*                W4 batch). The (D)-window witness index is re-armed with   *)
(*                the closed form nescD(q) = ceil((2L+1)/5), L = floor       *)
(*                (log2 (2q)) = S (Nat.log2 q), replacing the structurally   *)
(*                incompatible slope-1/2 old witness (65330/65565 grid       *)
(*                failures, 100 percent E3-overshoot, KB41j 4.1). This file  *)
(*                compiles the KB41j statement draft into born proofs: the   *)
(*                two nat-window limbs E1D (2*q*3^n <= 20^n) and E3D         *)
(*                (2^(17n) <= kappa*q^7) hold for every q >= 1 at            *)
(*                n = nescD(q) (full-spectrum certificate: step anchors      *)
(*                400 >= 288 and 2187 >= 2048 plus the 5-band induction),   *)
(*                the Q-face window supply (sigT, piu_mu_and2 limbs 1 and 3) *)
(*                and its QleT' variant are derived, the (D) HescD premise   *)
(*                slot is stated as an explicit Set face with its supply     *)
(*                contract (limbs 1+3 from this file, limb 2 = p-adic       *)
(*                clearing gap instantiated at the same witness), and the    *)
(*                dual-engine acceptor discrimination is mirrored Coq-side   *)
(*                by exact rejection faces for the retired old witness and   *)
(*                the near-miss W25 = ceil(2(L+1)/5) form.                   *)
(* Dependencies : piu_zz_nail_mu (N6'-a main-nail pins: sigma=17, E=7,       *)
(*                rho=(3/20), N0=1348 - interface bite W4/N6'-a);            *)
(*                piu_mu_criterion (piu_mu_QleT/ZleT/and2/and3/epos,         *)
(*                piu_mu_Zle_Qle, piu_mu_mult_le_r_inv); S02_CauchyComplete  *)
(*                (QleT' :99, Qle_to_QleT' :115); stdlib QArith, ZArith,     *)
(*                Lia, Wf_nat.                                               *)
(* References   : KB41j receipt 3.1-3.2/4.3/5.1 (full-spectrum certificate,  *)
(*                replacement ammo, statement draft); KB41h 3.1 (anchor      *)
(*                (20/3)^2 >= 2^5); KB41k bank row 7 (E=7 criterion);        *)
(*                KB41g 4-1 (window shape, slope certificate); GEDAN-v2      *)
(*                workorder node N5.                                         *)
(* Constructivity: every named statement is Set-carried (piu_mu_QleT,        *)
(*                piu_mu_ZleT, piu_mu_and2/and3, sigT, S02 QleT', sum);      *)
(*                propositional reasoning occurs only inside proofs;         *)
(*                definitions transparent; 无公理依赖、无未证假设; no Abort; *)
(*                every named statement closes under the global context.     *)
(* Build        : rocq c -native-compiler no -q -time -Q . ""                *)
(*                -Q <kb46 sandbox> "" -Q <ConstructiveWorld_vo> ""          *)
(*                piu_zz_ec_escwin_nescD.v, under cpu_guard_v3               *)
(*                (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce 0),       *)
(*                Rocq 9.1.0.                                                *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith Arith.Arith Lia.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_nail_mu.

(* ================================================================== *)
(* Section 1. Pins and the closed-form witness (escwin re-arm).       *)
(* ================================================================== *)

(* kappa pin, same value as e_carrier:61-63 (35831808 = 2^14 * 3^7);   *)
(* re-pinned locally so this unit does not pull the full e_carrier     *)
(* dependency closure; identity to the nail face is anchored below.    *)
Definition piu_zz_ec_kappaD : Q := (35831808 # 1)%Q.

Example piu_zz_ec_kappaD_decomp :
  (2 ^ 14 * 3 ^ 7)%Z = 35831808%Z.
Proof. vm_compute. reflexivity. Qed.

(* Interface bite W4/N6'-a: sigma, E, rho, N0 are consumed from the    *)
(* N6'-a nail unit (not re-pinned here).                               *)
Example piu_zz_ec_nail_sigma_face : piu_zz_nail_sigma = 17%nat.
Proof. reflexivity. Qed.

Example piu_zz_ec_nail_E_face : piu_zz_nail_E = 7%nat.
Proof. reflexivity. Qed.

Example piu_zz_ec_nail_rho_face : piu_zz_nail_rho = (3 # 20)%Q.
Proof. reflexivity. Qed.

(* The replacement witness: nescD q = (2L+5)/5 floored = ceil((2L+1)/5) *)
(* with L = S (Nat.log2 q) = floor (log2 (2q)) for q >= 1 (KB41j 3.0).  *)
Definition piu_zz_ec_nescD (q : nat) : nat :=
  Nat.div (2 * S (Nat.log2 q) + 5) 5.

(* L-band form: at band index L the witness is (2L+5)/5 floored. *)
Definition piu_zz_ec_nescD_at (L : nat) : nat := Nat.div (2 * L + 5) 5.

Lemma piu_zz_ec_nescD_at_eq :
  forall q : nat, piu_zz_ec_nescD q = piu_zz_ec_nescD_at (S (Nat.log2 q)).
Proof. intros q. reflexivity. Qed.

(* band step: nescD_at (L+5) = nescD_at L + 2 (KB41j 3.1 identity). *)
Lemma piu_zz_ec_nescD_at_step5 :
  forall L : nat, piu_zz_ec_nescD_at (L + 5) = (piu_zz_ec_nescD_at L + 2)%nat.
Proof.
  intros L. unfold piu_zz_ec_nescD_at.
  replace (2 * (L + 5) + 5)%nat with (2 * 5 + (2 * L + 5))%nat by lia.
  rewrite Nat.div_add_l by discriminate.
  lia.
Qed.

(* ================================================================== *)
(* Section 2. Local Q bridges (cloned inject_pow / mul / pos faces).  *)
(* ================================================================== *)

Lemma piu_zz_ec_inj_mul_eq : forall x y : Z,
  inject_Z (x * y) == inject_Z x * inject_Z y.
Proof.
  intros x y. unfold inject_Z, Qmult, Qeq. cbn. ring.
Qed.

Lemma piu_zz_ec_inj_pow_eq : forall (z : Z) (k : nat),
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
    rewrite (piu_zz_ec_inj_mul_eq (z ^ Z.of_nat k) z).
    rewrite IH. reflexivity.
Qed.

Lemma piu_zz_ec_pow_pos_lt : forall (x : Q) (n : nat),
  (0 < x)%Q -> (0 < Qpower x (Z.of_nat n))%Q.
Proof.
  intros x n Hx. induction n as [|n IH].
  - cbn [Z.of_nat]. rewrite Qpower_0_r. unfold Qlt. cbn. lia.
  - assert (Hne : ~ (x == 0)%Q).
    { intro Hc. rewrite Hc in Hx. unfold Qlt in Hx. cbn in Hx. lia. }
    assert (Hs : (Z.of_nat (Datatypes.S n) = Z.of_nat n + 1)%Z) by lia.
    rewrite Hs.
    rewrite Qpower_plus by exact Hne.
    replace (Qpower x 1) with x by reflexivity.
    rewrite Qmult_comm.
    exact (Qmult_lt_0_compat _ _ Hx IH).
Qed.

(* the product identity behind limb 1: q * (3/20)^n * 20^n == q*3^n    *)
Lemma piu_zz_ec_limb1_mult : forall (q n : nat),
  (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n))
    * Qpower (inject_Z 20%Z) (Z.of_nat n)
    == inject_Z (Z.of_nat q * 3 ^ Z.of_nat n).
Proof.
  intros q n.
  rewrite <- Qmult_assoc.
  rewrite <- Qmult_power.
  assert (Em : ((3 # 20)%Q * inject_Z 20%Z) == (3 # 1)%Q)
    by (unfold inject_Z, Qmult, Qeq; cbn; lia).
  rewrite Em.
  rewrite <- (piu_zz_ec_inj_pow_eq 3%Z n ltac:(cbn; lia)).
  rewrite (piu_zz_ec_inj_mul_eq (Z.of_nat q) (3 ^ Z.of_nat n)).
  reflexivity.
Qed.

(* doubling bridge in the inject vocabulary *)
Lemma piu_zz_ec_inj_double : forall m : Z,
  inject_Z (2 * m) == inject_Z m * (2 # 1)%Q.
Proof.
  intros m.
  replace (2 * m)%Z with (m * 2)%Z by ring.
  rewrite piu_zz_ec_inj_mul_eq.
  reflexivity.
Qed.

(* Z.of_nat distribution for the E1D canonical form *)
Lemma piu_zz_ec_znat_mul_distr : forall (q n : nat),
  (2 * (Z.of_nat q * 3 ^ Z.of_nat n))%Z = Z.of_nat (2 * q * 3 ^ n).
Proof.
  intros q n.
  rewrite Nat2Z.inj_mul, Nat2Z.inj_mul, Nat2Z.inj_pow.
  change (Z.of_nat 2) with 2%Z. change (Z.of_nat 3) with 3%Z.
  ring.
Qed.

(* ================================================================== *)
(* Section 3. The two nat-window limbs (full-spectrum CERT face).     *)
(* ================================================================== *)

(* Limb 1 nat face (E1D): 2*q*3^n <= 20^n at n = nescD q, i.e. the     *)
(* (D)-window lower edge q*(3/20)^n <= 1/2 (KB41j 3.1 E1' chain).      *)
(* Band lemma: band-end hardest point, step-5 induction, bases L=1..7  *)
(* vm_compute, step closes via 288 <= 400 (the (20/3)^2 >= 2^5 anchor) *)
(* and the L >= 3 slack 112*2^(L-4) >= 782.                            *)
Lemma piu_zz_ec_escwin_E1D_band :
  forall L : nat, (1 <= L)%nat ->
  ((2 ^ (S L) - 2) * 3 ^ (piu_zz_ec_nescD_at L)
    <= 20 ^ (piu_zz_ec_nescD_at L))%nat.
Proof.
  intro L. pattern L. apply lt_wf_ind. clear L.
  intros L IH HL.
  destruct (le_lt_dec 8 L) as [Hbig | Hsmall].
  - (* step: L >= 8, reduce to L-5 >= 3 *)
    assert (HL5 : (1 <= L - 5)%nat) by lia.
    replace L with (L - 5 + 5)%nat by lia.
    rewrite piu_zz_ec_nescD_at_step5.
    specialize (IH (L - 5)%nat (ltac:(lia)) HL5).
    replace (piu_zz_ec_nescD_at (L - 5) + 2)%nat
      with (S (S (piu_zz_ec_nescD_at (L - 5))))%nat by lia.
    rewrite (Nat.pow_succ_r' 3 (S (piu_zz_ec_nescD_at (L - 5)))).
    rewrite (Nat.pow_succ_r' 3 (piu_zz_ec_nescD_at (L - 5))).
    rewrite (Nat.pow_succ_r' 20 (S (piu_zz_ec_nescD_at (L - 5)))).
    rewrite (Nat.pow_succ_r' 20 (piu_zz_ec_nescD_at (L - 5))).
    replace (S (L - 5 + 5)) with (S (L - 5) + 5)%nat by lia.
    rewrite Nat.pow_add_r.
    replace (2 ^ 5)%nat with 32%nat by reflexivity.
    remember (piu_zz_ec_nescD_at (L - 5)) as n eqn:Hn.
    remember (3 ^ n)%nat as A eqn:HA.
    remember (20 ^ n)%nat as B eqn:HB.
    assert (Hx : (16 <= 2 ^ S (L - 5))%nat)
      by (change (2 ^ 4 <= 2 ^ S (L - 5))%nat; apply Nat.pow_le_mono_r; lia).
    remember (2 ^ S (L - 5))%nat as X eqn:HX.
    remember (X * 32 - 2)%nat as P eqn:HP.
    remember (X - 2)%nat as Q eqn:HQ.
    (* IH : Q*A <= B; goal : P*(A*3*3) <= B*20*20; Hx : 16 <= X *)
    assert (Hstep : (P * 9 <= 400 * Q)%nat) by lia.
    assert (Hs1 : (P * (3 * (3 * A)) = P * 9 * A)%nat) by nia.
    assert (Hs2 : (20 * (20 * B) = B * 400)%nat) by nia.
    rewrite Hs1, Hs2.
    apply (Nat.le_trans _ (400 * Q * A)%nat).
    + apply Nat.mul_le_mono; [exact Hstep | apply Nat.le_refl].
    + rewrite (Nat.mul_comm B 400). rewrite <- Nat.mul_assoc.
      apply Nat.mul_le_mono; [apply Nat.le_refl | exact IH].
  - (* bases L = 0..7 (0 impossible; 1..7 vm_compute; >=8 contradictory) *)
    destruct L as [|[|[|[|[|[|[|[|L8]]]]]]]]; try lia; vm_compute; lia.
Qed.

Lemma piu_zz_ec_escwin_E1D_nat : forall q : nat, (1 <= q)%nat ->
  (2 * q * 3 ^ piu_zz_ec_nescD q <= 20 ^ piu_zz_ec_nescD q)%nat.
Proof.
  intros q Hq.
  assert (HLt : (q < 2 ^ S (Nat.log2 q))%nat).
  { destruct (Nat.log2_spec q) as [_ Hlt]; [lia | exact Hlt]. }
  assert (Hq2 : (2 * q + 2 <= 2 ^ (S (S (Nat.log2 q))))%nat).
  { replace (S (S (Nat.log2 q))) with (S (Nat.log2 q) + 1)%nat by lia.
    rewrite Nat.pow_add_r.
    replace (2 ^ 1)%nat with 2%nat by reflexivity.
    replace (2 * q + 2)%nat with ((q + 1) * 2)%nat by lia.
    apply Nat.mul_le_mono.
    - lia.
    - apply Nat.le_refl. }
  rewrite piu_zz_ec_nescD_at_eq.
  apply (Nat.le_trans _ ((2 ^ (S (S (Nat.log2 q))) - 2)
                          * 3 ^ piu_zz_ec_nescD_at (S (Nat.log2 q)))%nat).
  - apply Nat.mul_le_mono; [lia | apply Nat.le_refl].
  - apply piu_zz_ec_escwin_E1D_band. lia.
Qed.

(* Limb 3 nat face (E3D): 2^(17n) <= kappa*q^7 at n = nescD q.  Chain:  *)
(* 5n <= 2L+5 (div bound) => 85n <= 34L+85 <= 35L+90 = 5*(7L+18) =>     *)
(* 17n <= 7L+18; then 2^(17n) <= 2^(7log2q+25) = 2^11 * 2^14 * (2^L)^7  *)
(* <= 3^7 * q^7 <= kappa * q^7 (anchor 2048 <= 2187).                   *)
Lemma piu_zz_ec_escwin_E3D_nat : forall q : nat, (1 <= q)%nat ->
  (2 ^ (17 * piu_zz_ec_nescD q) <= 35831808 * q ^ 7)%nat.
Proof.
  intros q Hq.
  unfold piu_zz_ec_nescD.
  set (L := S (Nat.log2 q)) in *.
  assert (Hq1 : (0 < q)%nat) by lia.
  assert (Hd : (2 * L + 5 = 5 * Nat.div (2 * L + 5) 5 + (2 * L + 5) mod 5)%nat)
    by (apply Nat.div_mod; discriminate).
  assert (Hm : ((2 * L + 5) mod 5 < 5)%nat)
    by (apply Nat.mod_upper_bound; discriminate).
  assert (H5n : (5 * Nat.div (2 * L + 5) 5 <= 2 * L + 5)%nat) by lia.
  assert (H2 : (5 * (17 * Nat.div (2 * L + 5) 5) <= 5 * (7 * L + 18))%nat) by lia.
  pose proof (proj2 (Nat.mul_le_mono_pos_l _ _ 5%nat ltac:(lia)) H2) as Hlin.
  assert (Hge : (2 ^ Nat.log2 q <= q)%nat).
  { destruct (Nat.log2_spec q) as [Hge _]; [lia | exact Hge]. }
  apply (Nat.le_trans _ (2 ^ (7 * Nat.log2 q + 25))%nat).
  - apply Nat.pow_le_mono_r; lia.
  - replace (7 * L + 18)%nat with (7 * Nat.log2 q + 25)%nat by lia.
    rewrite Nat.pow_add_r.
    replace (7 * Nat.log2 q)%nat with (Nat.log2 q * 7)%nat by lia.
    rewrite Nat.pow_mul_r by lia.
    rewrite (Nat.mul_comm ((2 ^ Nat.log2 q) ^ 7) (2 ^ 25)).
    apply (Nat.le_trans _ (2 ^ 25 * q ^ 7)%nat).
    + apply Nat.mul_le_mono.
      * apply Nat.le_refl.
      * apply Nat.pow_le_mono_l. exact Hge.
    + apply Nat.mul_le_mono.
      * assert (Hz : (Z.of_nat (2 ^ 25) <= Z.of_nat 35831808)%Z)
          by (vm_compute; discriminate).
        apply (proj2 (Nat2Z.inj_le (2 ^ 25) 35831808)). exact Hz.
      * apply Nat.le_refl.
Qed.

(* ================================================================== *)
(* Section 4. Q-face window supply (sigT, limbs 1 and 3).             *)
(* ================================================================== *)

Lemma piu_zz_ec_escwin_limb1_Q : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat (piu_zz_ec_nescD q)))
              (1 # 2)%Q.
Proof.
  intros q Hq.
  pose proof (piu_zz_ec_pow_pos_lt (inject_Z 20%Z) (piu_zz_ec_nescD q)
    ltac:(unfold inject_Z, Qlt; cbn; lia)) as Hp.
  apply (piu_mu_mult_le_r_inv
          (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat (piu_zz_ec_nescD q)))
          (1 # 2)%Q
          (Qpower (inject_Z 20%Z) (Z.of_nat (piu_zz_ec_nescD q))) Hp).
  - (* X * z <= Y * z *)
    rewrite piu_zz_ec_limb1_mult.
    rewrite <- (piu_zz_ec_inj_pow_eq 20%Z (piu_zz_ec_nescD q) ltac:(cbn; lia)).
    (* inject(q*3^n) <= (1/2) * inject(20^n); multiply by 2 *)
    apply (piu_mu_mult_le_r_inv
            (inject_Z (Z.of_nat q * 3 ^ Z.of_nat (piu_zz_ec_nescD q)))
            ((1 # 2) * inject_Z (20 ^ Z.of_nat (piu_zz_ec_nescD q)))%Q
            (2 # 1)%Q ltac:(unfold Qlt; cbn; lia)).
    + rewrite <- piu_zz_ec_inj_double.
      replace (2 * (Z.of_nat q * 3 ^ Z.of_nat (piu_zz_ec_nescD q)))%Z
        with (Z.of_nat (2 * q * 3 ^ piu_zz_ec_nescD q))
        by (symmetry; apply piu_zz_ec_znat_mul_distr).
      assert (E2 : (((1 # 2) * inject_Z (20 ^ Z.of_nat (piu_zz_ec_nescD q)))
                     * (2 # 1))%Q
                   == inject_Z (20 ^ Z.of_nat (piu_zz_ec_nescD q))) by ring.
      rewrite E2.
      pose proof (proj1 (Nat2Z.inj_le _ _)
        (piu_zz_ec_escwin_E1D_nat q Hq)) as HZ.
      destruct (piu_mu_Zle_Qle _ _ HZ) as [HQ].
      rewrite Nat2Z.inj_pow in HQ.
      cbn [Z.of_nat] in HQ.
      exact HQ.
Qed.

Lemma piu_zz_ec_escwin_limb3_Q : forall q : nat, (1 <= q)%nat ->
  piu_mu_QleT (piu_mu_epos (17 * piu_zz_ec_nescD q))
              (piu_zz_ec_kappaD * Qpower (inject_Z (Z.of_nat q))
                 (Z.of_nat piu_zz_nail_E))%Q.
Proof.
  intros q Hq.
  unfold piu_zz_ec_kappaD, piu_mu_epos, piu_zz_nail_E.
  apply piu_mu_QleT_i.
  rewrite <- (piu_zz_ec_inj_pow_eq (Z.of_nat q) 7 ltac:(unfold inject_Z, Qlt; cbn; lia)).
  rewrite <- (piu_zz_ec_inj_mul_eq 35831808%Z ((Z.of_nat q) ^ Z.of_nat 7)%Z).
  pose proof (proj1 (Nat2Z.inj_le _ _) (piu_zz_ec_escwin_E3D_nat q Hq)) as HZ.
  change (Z.of_nat 35831808) with (2 ^ 14 * 3 ^ 7)%Z in HZ.
  repeat rewrite Nat2Z.inj_mul in HZ.
  repeat rewrite Nat2Z.inj_pow in HZ.
  cbn [Z.of_nat] in HZ.
  destruct (piu_mu_Zle_Qle _ _ HZ) as [HQ].
  exact HQ.
Qed.

(* The (D)-window supply: witness n = nescD q with limbs 1 and 3 in    *)
(* piu_mu_and2 form (sigT carried; the HescD limb-2 slot is supplied   *)
(* separately at the same witness, see the contract theorem below).    *)
Theorem piu_zz_ec_escwin_nescD_Q : forall q : nat, (1 <= q)%nat ->
  sigT (fun n : nat => piu_mu_and2
    (piu_mu_QleT (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n))
                  (1 # 2)%Q)
    (piu_mu_QleT (piu_mu_epos (17 * n))
      (piu_zz_ec_kappaD * Qpower (inject_Z (Z.of_nat q)) (Z.of_nat 7))%Q)).
Proof.
  intros q Hq. exists (piu_zz_ec_nescD q).
  apply piu_mu_and2_i.
  - exact (piu_zz_ec_escwin_limb1_Q q Hq).
  - exact (piu_zz_ec_escwin_limb3_Q q Hq).
Qed.

(* QleT'-carried variant of the window limb 1 (vm_compute-decidable    *)
(* face; S02 bridge one step, KB41j 5.1 item 3). *)
Theorem piu_zz_ec_escwin_nescD_QleT' : forall q : nat, (1 <= q)%nat ->
  sigT (fun n : nat => S02_CauchyComplete.QleT'
          (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n)) (1 # 2)%Q).
Proof.
  intros q Hq.
  destruct (piu_zz_ec_escwin_nescD_Q q Hq) as [n [H1 _]].
  exists n. apply S02_CauchyComplete.Qle_to_QleT'.
  destruct H1 as [H1]. exact H1.
Qed.

(* ================================================================== *)
(* Section 5. The (D) HescD premise slot: face + supply contract.     *)
(* ================================================================== *)

(* The reshaped (D) escape premise (Section EC Hesc slot isomorph at    *)
(* sigma = 17, E = 7; limb 1 = q*(3/20)^n <= 1/2, limb 2 verbatim,      *)
(* limb 3 = 2^(17n) <= kappa*q^7). A : nat -> Z and B : nat -> Z are    *)
(* the ZZ linear-form coefficient families (Section EC variables); the  *)
(* Hcoef supply side is the N1/N2b territory, not re-declared here.     *)
Section ESCWIN_HESCD.

Context (A B : nat -> Z).

Definition piu_zz_ec_HescD_face (p : Z) (q : nat) : Set :=
  sigT (fun n : nat => piu_mu_and3
    (piu_mu_QleT (inject_Z (Z.of_nat q) * Qpower (3 # 20)%Q (Z.of_nat n))
                  (1 # 2)%Q)
    (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
    (piu_mu_QleT (piu_mu_epos (17 * n))
      (piu_zz_ec_kappaD * Qpower (inject_Z (Z.of_nat q))
         (Z.of_nat 7))%Q)).

(* Supply contract: limbs 1+3 come from the nescD window of this file; *)
(* limb 2 (the nonvanishing limb) is the p-adic clearing gap premise   *)
(* instantiated at the same witness (KB41f P3 debt, architecture       *)
(* unchanged, KB41j 5.1 item 4).                                       *)
Theorem piu_zz_ec_HescD_of_window :
  forall (p : Z) (q : nat), (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_zz_ec_HescD_face p q.
Proof.
  intros p q Hq H2.
  exists (piu_zz_ec_nescD q). apply piu_mu_and3_i.
  - exact (piu_zz_ec_escwin_limb1_Q q Hq).
  - exact H2.
  - exact (piu_zz_ec_escwin_limb3_Q q Hq).
Qed.

End ESCWIN_HESCD.

(* ================================================================== *)
(* Section 6. Acceptor wiring: three-form discrimination faces.       *)
(* ================================================================== *)

(* Machine-side regression gate: kb41j_acceptor.py run recorded in the  *)
(* kb84 sandbox (2 5 1 -> CERT-FULLSPECTRUM-PASS; 2 5 2 and 1 2 1 ->    *)
(* FAIL). The two lemmas below mirror the FAIL verdicts as exact nat    *)
(* faces so the Coq side carries the discrimination, not only the log.  *)

(* The retired old witness S (div2 (S (log2 q))) violates the upper    *)
(* edge at q = 2^10 (slope anchor 17 <= 14 fails structurally,         *)
(* KB41j 3.2 form-table row 3). *)
Lemma piu_zz_ec_nescD_rejects_old :
  (2 ^ (Z.of_nat (17 * S (Nat.div2 (S 10))))
    > 35831808 * (2 ^ 10) ^ 7)%Z.
Proof. vm_compute; reflexivity. Qed.

(* The near-miss W25 = ceil(2(L+1)/5) form violates the upper edge at  *)
(* q = 2 (8 grid bad points, L = 2 mod 5 band heads; KB41j 3.3 N-j1).  *)
Definition piu_zz_ec_nescW25 (q : nat) : nat :=
  Nat.div (2 * S (Nat.log2 q) + 6) 5.

Lemma piu_zz_ec_nescD_rejects_W25 :
  (2 ^ (Z.of_nat (17 * piu_zz_ec_nescW25 2)) > 35831808 * 2 ^ 7)%Z.
Proof. vm_compute; reflexivity. Qed.

(* And the armed form passes both limbs at the same probe points       *)
(* (q = 2 and q = 1; the acceptor's PASS direction, spot anchors).     *)
Lemma piu_zz_ec_nescD_accepts_q2 :
  (2 * 2 * 3 ^ piu_zz_ec_nescD 2 <= 20 ^ piu_zz_ec_nescD 2)%nat
  /\ (2 ^ (Z.of_nat (17 * piu_zz_ec_nescD 2)) <= 35831808 * 2 ^ 7)%Z.
Proof.
  split.
  - vm_compute; lia.
  - vm_compute; discriminate.
Qed.

Lemma piu_zz_ec_nescD_accepts_q1 :
  (2 * 1 * 3 ^ piu_zz_ec_nescD 1 <= 20 ^ piu_zz_ec_nescD 1)%nat
  /\ (2 ^ (Z.of_nat (17 * piu_zz_ec_nescD 1)) <= 35831808 * 1 ^ 7)%Z.
Proof.
  split.
  - vm_compute; lia.
  - vm_compute; discriminate.
Qed.

(* Step anchors as standalone example faces (400 >= 288 = (20/3)^2 >=  *)
(* 2^5, the KB41h anchor; 2187 >= 2048 = 3^7 >= 2^11). *)
Example piu_zz_ec_escwin_anchor_step1 : (400 >= 288)%nat.
Proof. vm_compute; lia. Qed.

Example piu_zz_ec_escwin_anchor_step3 : (3 ^ 7 >= 2 ^ 11)%nat.
Proof. vm_compute; lia. Qed.

Print Assumptions piu_zz_ec_escwin_E1D_nat.
Print Assumptions piu_zz_ec_escwin_E3D_nat.
Print Assumptions piu_zz_ec_escwin_nescD_Q.
Print Assumptions piu_zz_ec_escwin_nescD_QleT'.
Print Assumptions piu_zz_ec_HescD_of_window.
Print Assumptions piu_zz_ec_nescD_rejects_old.
Print Assumptions piu_zz_ec_nescD_rejects_W25.
Print Assumptions piu_zz_ec_nescD_accepts_q2.
Print Assumptions piu_zz_ec_nescD_accepts_q1.
