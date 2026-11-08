(* ========================================================================= *)
(* Mission      : W5 hcage-glue construction (the residue N6'-b registered   *)
(*                as "W5 owns instantiation or retirement"): the U-shape     *)
(*                absorption account C_asm*n <= (375/373)^n for all n >= 1   *)
(*                from the admissibility premise C_asm <= C* (the anchor     *)
(*                C* * 187 == (375/373)^187, exact), its composition with    *)
(*                the Hasm band dvf n <= C_asm*n*(373/2500)^n into the       *)
(*                head-coverage faces dvf n <= (3/20)^n (all-n, head, tail   *)
(*                - the N6'-b draft trio), the tail absorption account       *)
(*                n*(373/2500)^n <= (375/2500)^n for n >= 1348, and the      *)
(*                N0-boundary face inhabited from the N2a born bank pair.    *)
(*                All carriers stay abstract (dvf, Casm); the Hasm           *)
(*                instantiation for the concrete supply object remains the   *)
(*                registered open bridge (KB41m NEGATIVE precedent).         *)
(* Dependencies : S02_CauchyComplete (QleT'/QltT/QeqT), piu_mu_criterion     *)
(*                (and2), piu_zz_ec_escwin_nescD (positivity helper),        *)
(*                piu_zz_ec_escwin_bracket (draft trio + N0 face),           *)
(*                piu_zz_cage_constants (C* admissibility + bank pair);      *)
(*                stdlib QArith, ZArith, Lia, Lqa, Qring, Qpower, Setoid.    *)
(* References   : KB41g 4-2 four-piece method; KB76 refactor context;        *)
(*                N6'-b construction skeleton steps (1)-(5) pre-verified in  *)
(*                the kb84 scratch; piu_zz_ec_mu_cond ec_hval technique.     *)
(* Constructivity: every named statement is Set-carried (QleT', QltT, QeqT, *)
(*                sigT, piu_mu_and2); premises explicit (Casm <= C*, the     *)
(*                Hasm band); no Axiom, no Abort, no admit; lia/nia only as  *)
(*                auxiliary linear steps inside proofs.                      *)
(* Build        : rocq c -native-compiler no -q -Q . "" -Q kb84 "" -Q kb45   *)
(*                "" -Q kb46 "" -Q vo "" piu_zz_hcage_glue.v, under          *)
(*                cpu_guard_v3 (-LoadLimit 60 -TempLimit 98 -AllowG3         *)
(*                -GearForce 0 -CoreN 2 -MaxWaitSec 7200), Rocq 9.1.0.       *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
From Stdlib Require Import Extraction.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import piu_zz_ec_escwin_nescD.
Require Import piu_zz_ec_escwin_bracket.
Require Import piu_zz_cage_constants.

(* ==== Section 1. The U-shape anchor and the two branches ==== *)

(* Anchor: C* * 187 is exactly (375/373)^187, so the admissibility *)
(* premise lands the absorption account on the anchor point. *)
Lemma piu_zz_hcg_casm_anchor : forall Casm : Q,
  piu_zz_c7_Casm_admissible Casm ->
  S02_CauchyComplete.QleT'
    (Casm * inject_Z 187)%Q (Qpower (375 # 373)%Q 187%Z).
Proof.
  intros Casm HC.
  pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ HC) as HCle.
  apply S02_CauchyComplete.Qle_to_QleT'.
  assert (Eanch : (piu_zz_c7_Casm_bound_v187 * inject_Z 187
                   == Qpower (375 # 373)%Q 187%Z)%Q)
    by (vm_compute; reflexivity).
  rewrite <- Eanch.
  apply Qmult_le_compat_r; [exact HCle |].
  unfold Qle, inject_Z. cbn [Qnum Qden]. lia.
Qed.

(* Shared U-shape facts on the anchor constant. *)
Definition piu_zz_hcg_A : Q := (375 # 373)%Q.

Lemma piu_zz_hcg_A_nonzero : ~ (piu_zz_hcg_A == 0)%Q.
Proof.
  intro H0.
  pose proof (Qeq_eq_bool piu_zz_hcg_A 0%Q H0) as Hb.
  vm_compute in Hb. discriminate Hb.
Qed.

(* Nonvanishing of the two band constants (Qpower_plus side slots). *)
Lemma piu_zz_hcg_rt_nonzero : ~ ((373 # 2500)%Q == 0)%Q.
Proof.
  intro H0.
  pose proof (Qeq_eq_bool (373 # 2500)%Q 0%Q H0) as Hb.
  vm_compute in Hb. discriminate Hb.
Qed.

Lemma piu_zz_hcg_rm_nonzero : ~ ((375 # 2500)%Q == 0)%Q.
Proof.
  intro H0.
  pose proof (Qeq_eq_bool (375 # 2500)%Q 0%Q H0) as Hb.
  vm_compute in Hb. discriminate Hb.
Qed.

Lemma piu_zz_hcg_A_pow_S : forall n : nat,
  (Qpower piu_zz_hcg_A (Z.of_nat (S n))
   == Qpower piu_zz_hcg_A (Z.of_nat n) * piu_zz_hcg_A)%Q.
Proof.
  intros n.
  assert (Hs : (Z.of_nat (S n) = Z.of_nat n + 1)%Z) by lia.
  rewrite Hs at 1.
  rewrite Qpower_plus by exact piu_zz_hcg_A_nonzero.
  replace (Qpower piu_zz_hcg_A 1%Z) with piu_zz_hcg_A by reflexivity.
  reflexivity.
Qed.

Lemma piu_zz_hcg_A_pow_pos : forall n : nat,
  (0 < Qpower piu_zz_hcg_A (Z.of_nat n))%Q.
Proof.
  intros n. exact (piu_zz_ec_pow_pos_lt piu_zz_hcg_A n
    ltac:(unfold piu_zz_hcg_A, Qlt; cbn; lia)).
Qed.

(* Downward branch of the U-shape: n in [1, 187], sliding from 187. *)
Lemma piu_zz_hcg_ushape_dn : forall Casm : Q,
  piu_zz_c7_Casm_admissible Casm ->
  forall n : nat, (1 <= n)%nat -> (n <= 187)%nat ->
  S02_CauchyComplete.QleT'
    (Casm * inject_Z (Z.of_nat n))%Q
    (Qpower piu_zz_hcg_A (Z.of_nat n)).
Proof.
  intros Casm HC n H1 H2.
  remember (187 - n)%nat as d eqn:Hd.
  revert n H1 H2 Hd.
  induction d as [|d IH]; intros n H1 H2 Hd.
  - replace n with 187%nat by lia. exact (piu_zz_hcg_casm_anchor Casm HC).
  - assert (HS1 : (1 <= S n)%nat) by lia.
    assert (HS2 : (S n <= 187)%nat) by lia.
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _
      (IH (S n) HS1 HS2 (ltac:(lia)))) as HSn.
    apply S02_CauchyComplete.Qle_to_QleT'.
    assert (Hnz : (0 < inject_Z (Z.of_nat n))%Q)
      by (unfold inject_Z, Qlt; cbn; lia).
    assert (Hsnz : (0 < inject_Z (Z.of_nat (S n)))%Q)
      by (unfold inject_Z, Qlt; cbn; lia).
    assert (HApowpos : (0 <= Qpower piu_zz_hcg_A (Z.of_nat n))%Q).
    { apply Qlt_le_weak. exact (piu_zz_hcg_A_pow_pos n). }
    pose proof (piu_zz_hcg_A_pow_S n) as Hpow.
    assert (Hstep : (piu_zz_hcg_A * inject_Z (Z.of_nat n)
                     <= inject_Z (Z.of_nat (S n)))%Q).
    { assert (Hz : (Z.of_nat n <= 186)%Z) by lia.
      unfold piu_zz_hcg_A, Qle, inject_Z. cbn [Qmult Qnum Qden]. nia. }
    assert (E1 : (Casm * inject_Z (Z.of_nat n) * inject_Z (Z.of_nat (S n))
                  == Casm * inject_Z (Z.of_nat (S n)) * inject_Z (Z.of_nat n))%Q)
      by ring.
    assert (E2 : (Qpower piu_zz_hcg_A (Z.of_nat (S n)) * inject_Z (Z.of_nat n)
                  == Qpower piu_zz_hcg_A (Z.of_nat n)
                     * (piu_zz_hcg_A * inject_Z (Z.of_nat n)))%Q)
      by (rewrite Hpow; ring).
    apply (proj1 (Qmult_le_r (Casm * inject_Z (Z.of_nat n))%Q
                    (Qpower piu_zz_hcg_A (Z.of_nat n))
                    (inject_Z (Z.of_nat (S n))) Hsnz)).
    apply (Qle_trans _ (Qpower piu_zz_hcg_A (Z.of_nat (S n))
                          * inject_Z (Z.of_nat n))%Q).
    + rewrite E1. apply Qmult_le_compat_r;
        [exact HSn | apply Qlt_le_weak; exact Hnz].
    + rewrite E2.
      apply (Qle_trans _ (Qpower piu_zz_hcg_A (Z.of_nat n)
                            * inject_Z (Z.of_nat (S n)))%Q).
      * rewrite (Qmult_comm (Qpower piu_zz_hcg_A (Z.of_nat n))
                  (piu_zz_hcg_A * inject_Z (Z.of_nat n))).
        rewrite (Qmult_comm (Qpower piu_zz_hcg_A (Z.of_nat n))
                  (inject_Z (Z.of_nat (S n)))).
        apply Qmult_le_compat_r; [exact Hstep | exact HApowpos].
      * apply Qle_refl.
Qed.

(* Upward branch of the U-shape: n >= 187. *)
Lemma piu_zz_hcg_ushape_up : forall Casm : Q,
  piu_zz_c7_Casm_admissible Casm ->
  forall n : nat, (187 <= n)%nat ->
  S02_CauchyComplete.QleT'
    (Casm * inject_Z (Z.of_nat n))%Q
    (Qpower piu_zz_hcg_A (Z.of_nat n)).
Proof.
  intros Casm HC n.
  remember (n - 187)%nat as d eqn:Hd.
  revert n Hd.
  induction d as [|d IH]; intros n Hge Hd.
  - replace n with 187%nat by lia. exact (piu_zz_hcg_casm_anchor Casm HC).
  - destruct n as [|n0]; [lia |].
    assert (Hge0 : (187 <= n0)%nat) by lia.
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _
      (IH n0 (ltac:(lia)) Hge0)) as Hn0.
    apply S02_CauchyComplete.Qle_to_QleT'.
    assert (Hn0z : (0 < inject_Z (Z.of_nat n0))%Q)
      by (unfold inject_Z, Qlt; cbn; lia).
    assert (HSnz : (0 <= inject_Z (Z.of_nat (S n0)))%Q)
      by (unfold Qle, inject_Z; cbn [Qnum Qden]; lia).
    assert (HApowpos : (0 <= Qpower piu_zz_hcg_A (Z.of_nat n0))%Q).
    { apply Qlt_le_weak. exact (piu_zz_hcg_A_pow_pos n0). }
    pose proof (piu_zz_hcg_A_pow_S n0) as Hpow.
    assert (Hstep : (inject_Z (Z.of_nat (S n0))
                     <= piu_zz_hcg_A * inject_Z (Z.of_nat n0))%Q).
    { assert (Hz : (187 <= Z.of_nat n0)%Z) by lia.
      unfold piu_zz_hcg_A, Qle, inject_Z. cbn [Qmult Qnum Qden]. nia. }
    assert (E1 : (Casm * inject_Z (Z.of_nat (S n0)) * inject_Z (Z.of_nat n0)
                  == Casm * inject_Z (Z.of_nat n0) * inject_Z (Z.of_nat (S n0)))%Q)
      by ring.
    assert (E3 : (Qpower piu_zz_hcg_A (Z.of_nat n0) * (piu_zz_hcg_A * inject_Z (Z.of_nat n0))
                  == (Qpower piu_zz_hcg_A (Z.of_nat n0) * piu_zz_hcg_A)
                     * inject_Z (Z.of_nat n0))%Q)
      by ring.
    apply (proj1 (Qmult_le_r (Casm * inject_Z (Z.of_nat (S n0)))%Q
                    (Qpower piu_zz_hcg_A (Z.of_nat (S n0)))
                    (inject_Z (Z.of_nat n0)) Hn0z)).
    apply (Qle_trans _ (Qpower piu_zz_hcg_A (Z.of_nat n0)
                          * inject_Z (Z.of_nat (S n0)))%Q).
    + rewrite E1. apply Qmult_le_compat_r; [exact Hn0 | exact HSnz].
    + apply (Qle_trans _ (Qpower piu_zz_hcg_A (Z.of_nat n0)
                            * (piu_zz_hcg_A * inject_Z (Z.of_nat n0)))%Q).
      * rewrite (Qmult_comm (Qpower piu_zz_hcg_A (Z.of_nat n0))
                  (inject_Z (Z.of_nat (S n0)))).
        rewrite (Qmult_comm (Qpower piu_zz_hcg_A (Z.of_nat n0))
                  (piu_zz_hcg_A * inject_Z (Z.of_nat n0))).
        apply Qmult_le_compat_r; [exact Hstep | exact HApowpos].
      * rewrite E3. rewrite <- Hpow. apply Qle_refl.
Qed.

(* The U-shape account on the whole positive domain. *)
Lemma piu_zz_hcg_casm_ushape : forall Casm : Q,
  piu_zz_c7_Casm_admissible Casm ->
  forall n : nat, (1 <= n)%nat ->
  S02_CauchyComplete.QleT'
    (Casm * inject_Z (Z.of_nat n))%Q
    (Qpower piu_zz_hcg_A (Z.of_nat n)).
Proof.
  intros Casm HC n Hn.
  destruct (le_lt_dec 187 n) as [Hbig | Hsmall].
  - exact (piu_zz_hcg_ushape_up Casm HC n Hbig).
  - apply (piu_zz_hcg_ushape_dn Casm HC n Hn). lia.
Qed.

(* ==== Section 2. Head-coverage glue (the N6'-b draft trio) ==== *)

(* All-n face: the Hasm band composed with the U-shape account gives     *)
(* dvf n <= (3/20)^n for every n (n = 0 via the degenerate band; the     *)
(* anchor constant pair 375*373/(373*2500) = 3/20 exact). *)
Lemma piu_zz_hcg_hcage_all_glue : forall (dvf : nat -> Q) (Casm : Q),
  (forall n : nat,
     S02_CauchyComplete.QleT' (dvf n)
       (Casm * inject_Z (Z.of_nat n)
          * Qpower (373 # 2500)%Q (Z.of_nat n))%Q) ->
  piu_zz_c7_Casm_admissible Casm ->
  piu_zz_ec_hcage_all_face dvf.
Proof.
  intros dvf Casm Hasm HC.
  unfold piu_zz_ec_hcage_all_face. intros n.
  destruct (Nat.eq_dec n 0%nat) as [H0 | Hpos].
  - rewrite H0. apply S02_CauchyComplete.Qle_to_QleT'.
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hasm 0%nat)) as Hd0.
    assert (E0 : (Casm * inject_Z 0%Z * Qpower (373 # 2500)%Q (Z.of_nat 0)
                  == 0)%Q).
    { rewrite Qpower_0_r. unfold inject_Z. ring. }
    rewrite E0 in Hd0.
    rewrite Qpower_0_r.
    apply (Qle_trans _ 0%Q); [exact Hd0 |].
    unfold Qle. cbn [Qnum Qden]. lia.
  - assert (Hpos1 : (1 <= n)%nat) by lia.
    apply S02_CauchyComplete.Qle_to_QleT'.
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _ (Hasm n)) as Hd.
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _
      (piu_zz_hcg_casm_ushape Casm HC n Hpos1)) as Hu.
    assert (Hrt : (0 <= Qpower (373 # 2500)%Q (Z.of_nat n))%Q).
    { pose proof (piu_zz_ec_pow_pos_lt (373 # 2500)%Q n
        ltac:(unfold Qlt; cbn; lia)) as Hp.
      apply Qlt_le_weak. exact Hp. }
    assert (H1 : (Casm * inject_Z (Z.of_nat n)
                    * Qpower (373 # 2500)%Q (Z.of_nat n)
                  <= Qpower piu_zz_hcg_A (Z.of_nat n)
                     * Qpower (373 # 2500)%Q (Z.of_nat n))%Q).
    { apply Qmult_le_compat_r; [exact Hu | exact Hrt]. }
    assert (Ecomp : (Qpower piu_zz_hcg_A (Z.of_nat n)
                       * Qpower (373 # 2500)%Q (Z.of_nat n)
                     == Qpower (3 # 20)%Q (Z.of_nat n))%Q).
    { assert (Ebase : (piu_zz_hcg_A * (373 # 2500)%Q == (3 # 20)%Q)%Q)
        by (unfold piu_zz_hcg_A; vm_compute; reflexivity).
      rewrite <- Ebase. symmetry. apply Qmult_power. }
    apply (Qle_trans _ (Qpower piu_zz_hcg_A (Z.of_nat n)
                          * Qpower (373 # 2500)%Q (Z.of_nat n))%Q).
    + apply (Qle_trans _ (Casm * inject_Z (Z.of_nat n)
                            * Qpower (373 # 2500)%Q (Z.of_nat n))%Q);
        [exact Hd | exact H1].
    + rewrite Ecomp. apply Qle_refl.
Qed.

(* Head face (n < 1348) and tail face (1348 <= n): restrictions of the   *)
(* all-n glue on the two draft domains. *)
Lemma piu_zz_hcg_hcage_head_glue : forall (dvf : nat -> Q) (Casm : Q),
  (forall n : nat,
     S02_CauchyComplete.QleT' (dvf n)
       (Casm * inject_Z (Z.of_nat n)
          * Qpower (373 # 2500)%Q (Z.of_nat n))%Q) ->
  piu_zz_c7_Casm_admissible Casm ->
  piu_zz_ec_hcage_head_face dvf.
Proof.
  intros dvf Casm Hasm HC.
  unfold piu_zz_ec_hcage_head_face. intros n _.
  exact (piu_zz_hcg_hcage_all_glue dvf Casm Hasm HC n).
Qed.

Lemma piu_zz_hcg_hcage_tail_glue : forall (dvf : nat -> Q) (Casm : Q),
  (forall n : nat,
     S02_CauchyComplete.QleT' (dvf n)
       (Casm * inject_Z (Z.of_nat n)
          * Qpower (373 # 2500)%Q (Z.of_nat n))%Q) ->
  piu_zz_c7_Casm_admissible Casm ->
  piu_zz_ec_hcage_tail_face dvf.
Proof.
  intros dvf Casm Hasm HC.
  unfold piu_zz_ec_hcage_tail_face. intros n _.
  exact (piu_zz_hcg_hcage_all_glue dvf Casm Hasm HC n).
Qed.

(* ==== Section 3. Tail absorption account and the N0 boundary pair ==== *)

(* Tail absorption: n*(373/2500)^n <= (375/2500)^n for n >= 1348;        *)
(* base 1348 exact (the N2a born anchor), step needs 373 <= 2*n. *)
Lemma piu_zz_hcg_tail_absorb : forall n : nat, (1348 <= n)%nat ->
  S02_CauchyComplete.QleT'
    (inject_Z (Z.of_nat n) * Qpower (373 # 2500)%Q (Z.of_nat n))%Q
    (Qpower (375 # 2500)%Q (Z.of_nat n)).
Proof.
  intros n Hn.
  remember (n - 1348)%nat as d eqn:Hd.
  revert n Hn Hd.
  induction d as [|d IH]; intros n Hn Hd.
  - replace n with 1348%nat by lia. exact piu_zz_c7_tail_base_1348.
  - destruct n as [|n0]; [lia |].
    assert (Hn0 : (1348 <= n0)%nat) by lia.
    pose proof (S02_CauchyComplete.QleT'_to_Qle _ _
      (IH n0 Hn0 (ltac:(lia)))) as Hn0le.
    apply S02_CauchyComplete.Qle_to_QleT'.
    assert (Hlin : (inject_Z (Z.of_nat (S n0)) * (373 # 2500)%Q
                    <= inject_Z (Z.of_nat n0) * (375 # 2500)%Q)%Q).
    { assert (Hz : (187 <= Z.of_nat n0)%Z) by lia.
      unfold Qle, inject_Z. cbn [Qmult Qnum Qden]. nia. }
    assert (Hrt : (0 <= Qpower (373 # 2500)%Q (Z.of_nat n0))%Q).
    { pose proof (piu_zz_ec_pow_pos_lt (373 # 2500)%Q n0
        ltac:(unfold Qlt; cbn; lia)) as Hp.
      apply Qlt_le_weak. exact Hp. }
    assert (Hs : (Z.of_nat (S n0) = Z.of_nat n0 + 1)%Z) by lia.
    assert (E1 : (inject_Z (Z.of_nat (S n0))
                    * Qpower (373 # 2500)%Q (Z.of_nat (S n0))
                  == inject_Z (Z.of_nat (S n0)) * (373 # 2500)%Q
                     * Qpower (373 # 2500)%Q (Z.of_nat n0))%Q).
    { rewrite Hs at 2.
      rewrite Qpower_plus by exact piu_zz_hcg_rt_nonzero.
      replace (Qpower (373 # 2500)%Q 1%Z) with (373 # 2500)%Q by reflexivity.
      ring. }
    assert (E4 : (inject_Z (Z.of_nat n0) * (375 # 2500)%Q
                    * Qpower (373 # 2500)%Q (Z.of_nat n0)
                  == (inject_Z (Z.of_nat n0)
                      * Qpower (373 # 2500)%Q (Z.of_nat n0))
                     * (375 # 2500)%Q)%Q)
      by ring.
    assert (Es : (Qpower (375 # 2500)%Q (Z.of_nat (S n0))
                  == Qpower (375 # 2500)%Q (Z.of_nat n0) * (375 # 2500)%Q)%Q).
    { rewrite Hs at 1.
      rewrite Qpower_plus by exact piu_zz_hcg_rm_nonzero.
      replace (Qpower (375 # 2500)%Q 1%Z) with (375 # 2500)%Q by reflexivity.
      ring. }
    assert (Hrm0 : (0 <= (375 # 2500)%Q)%Q)
      by (unfold Qle; cbn [Qnum Qden]; lia).
    apply (Qle_trans _ (inject_Z (Z.of_nat n0) * (375 # 2500)%Q
                          * Qpower (373 # 2500)%Q (Z.of_nat n0))%Q).
    + rewrite E1. apply Qmult_le_compat_r; [exact Hlin | exact Hrt].
    + rewrite E4, Es.
      apply Qmult_le_compat_r; [exact Hn0le | exact Hrm0].
Qed.

(* The N0-boundary face inhabited from the N2a born bank pair (the       *)
(* N6'-b draft boundary certificate countersigned by N2a). *)
Lemma piu_zz_hcg_hcage_n0_of_bank : piu_zz_ec_hcage_N0_face.
Proof.
  unfold piu_zz_ec_hcage_N0_face. apply piu_mu_and2_i.
  - exact piu_zz_c7_tail_base_1348.
  - exact piu_zz_c7_tail_prev_violation_1347.
Qed.

(* ==== Section 4. Audit ==== *)

Print Assumptions piu_zz_hcg_A_nonzero.
Print Assumptions piu_zz_hcg_rt_nonzero.
Print Assumptions piu_zz_hcg_rm_nonzero.
Print Assumptions piu_zz_hcg_A_pow_pos.
Print Assumptions piu_zz_hcg_casm_anchor.
Print Assumptions piu_zz_hcg_ushape_dn.
Print Assumptions piu_zz_hcg_ushape_up.
Print Assumptions piu_zz_hcg_casm_ushape.
Print Assumptions piu_zz_hcg_hcage_all_glue.
Print Assumptions piu_zz_hcg_hcage_head_glue.
Print Assumptions piu_zz_hcg_hcage_tail_glue.
Print Assumptions piu_zz_hcg_tail_absorb.
Print Assumptions piu_zz_hcg_hcage_n0_of_bank.

(* Extraction witness list: the glue statements compile to OCaml with   *)
(* no Obj.magic and no lost names. *)
Extraction "piu_zz_hcage_glue_ext" piu_zz_hcg_casm_ushape piu_zz_hcg_hcage_all_glue
  piu_zz_hcg_hcage_head_glue piu_zz_hcg_hcage_tail_glue
  piu_zz_hcg_tail_absorb piu_zz_hcg_hcage_n0_of_bank.
