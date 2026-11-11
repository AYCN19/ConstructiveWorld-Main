(* ========================================================================= *)
(* Mission      : W5 Hmu-assembly supply face for the pi uniform-strength    *)
(*                irrationality endpoint chain.  Delivers the pointwise-     *)
(*                distance supply in the exact landed rateslot target shape  *)
(*                forall q > 0, exists ee > 0, lw1m_dist_pt q                *)
(*                (ck_alpha c0 8 q + 2*ee) from the six-premise conditional  *)
(*                chain piu_zz_ec_mu_cond, via the reverse adapter           *)
(*                (rate-form real_lt certificate -> dist_pt certificate at   *)
(*                the half-margin transport), the converse direction of the  *)
(*                landed piu_zz_realcert_of_distpt; re-anchors the criterion *)
(*                data pins (kappa = 35831808 = 2^14*3^7, sigma span 14,     *)
(*                2*kappa*c0 = 1) and the tau-power cancellation use-faces   *)
(*                (t = 2 and t = 8); registers the W4/first-wave interface   *)
(*                bites (N4 combined face, N5 nescD window, N6'-b q1         *)
(*                landing, N1 s1-length relay, N2a Pell chain, N2c bank).    *)
(* Dependencies : S01-S03, S10, PiEnvelope, LW0MLicBridge, LW1PiMeasure,     *)
(*                Local.LW0LeibSeparation, piu1932_tight_bound_instantiated, *)
(*                piu_mu_criterion, piu_zz_bridge_real, piu_zz_e_carrier     *)
(*                (six-premise chain), piu_zz_mu_assembly (adapter+pins),    *)
(*                piu_zz_s2_headledger, piu_zz_ec_escwin_nescD,              *)
(*                piu_zz_ec_escwin_bracket, piu_zz_n1_linform,               *)
(*                piu_zz_n2c_sigma_assembly, piu_zz_cage_constants,          *)
(*                piu_zz_sigma_decay, piu_zz_nail_mu.                        *)
(* References   : Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9        *)
(*                (2020) 407-419, Lemma 2; KB27 gap map sec.4/7 (down-seat   *)
(*                supply contract); leibsep_metric_pi_transport (Local/      *)
(*                LW0LeibSeparation); GEDAN-v2 workorder node W5.            *)
(* Constructivity: every named statement is Set-carried (QltT, QltT', QleT',*)
(*                QeqT, sigT; supply statement shape matches the landed      *)
(*                adapter verbatim); the six chain premises stay explicit    *)
(*                (honest interface; the concrete Hcage-all bridge stays     *)
(*                open per the workorder risk register); no non-constructive *)
(*                escapes and no unfinished-proof markers; lia/lra only as   *)
(*                auxiliary linear steps inside proofs (piu1904 and          *)
(*                piu_zz_mu_assembly precedent).                             *)
(* Build        : rocq c -native-compiler no -q -Q . "" -Q kb72/born3 ""     *)
(*                -Q kb86 "" -Q kb84 "" -Q kb45 "" -Q kb46 "" -Q vo ""       *)
(*                piu_zz_hmu_distpt_supply.v, under cpu_guard_v3             *)
(*                (-LoadLimit 60 -TempLimit 98 -AllowG3 -GearForce 0         *)
(*                -CoreN 2 -MaxWaitSec 7200), Rocq 9.1.0.                    *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Qring.
From Stdlib Require Import Lqa.
From Stdlib Require Import Qpower.
From Stdlib Require Import Extraction.
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
Require Import piu_zz_kernel_sum.
Require Import piu_zz_bridge_real.
Require Import piu_zz_e_carrier.
Require Import piu_zz_mu_assembly.
Require Import piu_zz_s2_headledger.
Require Import piu_zz_ec_escwin_nescD.
Require Import piu_zz_ec_escwin_bracket.
Require Import piu_zz_n1_linform.
Require Import piu_zz_n2c_sigma_assembly.
Require Import piu_zz_cage_constants.
Require Import piu_zz_sigma_decay.
Require Import piu_zz_nail_mu.

(* ==== Section 1. Criterion data pins (kappa, sigma span, tau) ==== *)

(* kappa decomposition and identity of the two landed kappa pins. *)
Example piu_zz_hmu_kappa_decomp :
  (2 ^ 14 * 3 ^ 7)%Z = 35831808%Z.
Proof. vm_compute. reflexivity. Qed.

Example piu_zz_hmu_kappa_pin :
  piu_zz_ec_kappa == piu_zz_mu_kappa.
Proof. reflexivity. Qed.

(* sigma = 14 pin (the 7*tau face of piu_zz_mu_assembly) and the span *)
(* reconciliation: the chain pins sigma = 12 at tau = 2, so the single *)
(* span sigma + tau = 14 carries both conventions. *)
Example piu_zz_hmu_sigma14_pin : piu_zz_mu_sigma = 14%nat.
Proof. reflexivity. Qed.

Example piu_zz_hmu_tau2_pin : piu_zz_mu_tau = 2%nat.
Proof. reflexivity. Qed.

Lemma piu_zz_hmu_span14 :
  (piu_zz_ec_sigma + piu_zz_ec_tau)%nat = piu_zz_mu_sigma.
Proof. reflexivity. Qed.

(* 2 * kappa * c0 = 1, vm_compute pinned (data level), in both the    *)
(* bool-reflection and the QeqT carrier of the registered pins. *)
Example piu_zz_hmu_kappa_c0_bool :
  Qeq_bool ((2 # 1) * (piu_zz_mu_kappa * piu_zz_c0_criterion)%Q)%Q
           (1 # 1)%Q = true.
Proof. vm_compute. reflexivity. Qed.

Lemma piu_zz_hmu_kappa_c0 :
  S02_CauchyComplete.QeqT
    ((2 # 1) * (piu_zz_mu_kappa * piu_zz_c0_criterion)%Q)%Q (1 # 1)%Q.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

Lemma piu_zz_hmu_c0_inv :
  S02_CauchyComplete.QeqT
    ((1 # 1) / (2 * piu_zz_mu_kappa)%Q)%Q piu_zz_c0_criterion.
Proof. apply qeq_imp_qeqT. vm_compute. reflexivity. Qed.

(* ==== Section 2. Tau-power cancellation use-faces (t = 2, t = 8) ==== *)

(* The alpha = 8 instance: the first-power exit of the rate-slot height *)
(* exponent, exactly the tau-power-form to h^8 first-power step of the *)
(* KB27 down-seat contract. *)
Example piu_zz_hmu_qpow_inject_alpha8 : forall x y : Q,
  (0 < x)%Q -> (0 < y)%Q ->
  S02_CauchyComplete.QleT' (Qpower x (Z.of_nat 8)) (Qpower y (Z.of_nat 8))
    -> S02_CauchyComplete.QleT' x y.
Proof.
  intros x y Hx Hy H.
  assert (Ht : (1 <= 8)%nat) by lia.
  exact (piu_zz_mu_qpow_inject 8%nat x y Ht Hx Hy H).
Qed.

(* The tau = 2 instance: the chain tau value. *)
Example piu_zz_hmu_qpow_inject_tau2 : forall x y : Q,
  (0 < x)%Q -> (0 < y)%Q ->
  S02_CauchyComplete.QleT' (Qpower x (Z.of_nat 2)) (Qpower y (Z.of_nat 2))
    -> S02_CauchyComplete.QleT' x y.
Proof.
  intros x y Hx Hy H.
  assert (Ht : (1 <= 2)%nat) by lia.
  exact (piu_zz_mu_qpow_inject 2%nat x y Ht Hx Hy H).
Qed.

(* ==== Section 3. The dist_pt supply face (W5 headline) ==== *)

(* Reverse adapter: a rate-form certificate at threshold d delivers the *)
(* pointwise certificate at the doubled threshold d + 2*ee, with the    *)
(* transport margin halved so a quarter of eps survives as ee.  This is *)
(* the converse direction of piu_zz_realcert_of_distpt. *)
Lemma piu_zz_hmu_distpt_of_realcert : forall (q d : Q),
  real_lt (real_const d) (real_metric real_pi_geom (real_const q)) ->
  sigT (fun ee : Q => And (S02_CauchyComplete.QltT 0 ee)
    (lw1m_dist_pt q ((d + (2 # 1) * ee)%Q))).
Proof.
  intros q d [eps [Heps [N HN]]].
  assert (Heps2 : S02_CauchyComplete.QltT 0 ((1 # 2) * eps)%Q).
  { apply Qlt_to_QltT.
    pose proof (QltT_to_Qlt _ _ Heps) as Hlt. lra. }
  destruct (leibsep_metric_pi_transport q ((1 # 2) * eps)%Q Heps2) as [Nr HNr].
  exists ((1 # 4) * eps)%Q.
  split.
  - apply Qlt_to_QltT.
    pose proof (QltT_to_Qlt _ _ Heps) as Hlt. lra.
  - exists (Nat.max N Nr). intros k Hk.
    assert (HkN : NatLe N k).
    { apply NatLe_lift.
      pose proof (NatLe_drop (Nat.max N Nr) k Hk) as Hmax.
      apply (Nat.le_trans N (Nat.max N Nr) k (Nat.le_max_l N Nr) Hmax). }
    assert (HkNr : NatLe Nr k).
    { apply NatLe_lift.
      pose proof (NatLe_drop (Nat.max N Nr) k Hk) as Hmax.
      apply (Nat.le_trans Nr (Nat.max N Nr) k (Nat.le_max_r N Nr) Hmax). }
    pose proof (HN k HkN) as Hlow.
    cbn [projT1 real_const] in Hlow.
    pose proof (HNr k HkNr) as Htr.
    apply Qlt_to_QltT'.
    set (P := projT1 (real_metric real_pi_geom (real_const q)) k) in *.
    set (X := Qabs ((lw0m_xL k - q)%Q)) in *.
    pose proof (QltT_to_Qlt _ _ Hlow) as HlowQ.
    pose proof (QltT_to_Qlt _ _ Htr) as HtrQ.
    (* HlowQ : eps < P - d ;  HtrQ : Qabs (P - X) < eps/2 ;  goal : d + eps/2 < X *)
    (* the Qabs band condition: -(eps/2) <= P - X <= eps/2 *)
    pose proof (proj1 (Qabs_Qle_condition (P - X)%Q ((1 # 2) * eps)%Q)
                  (Qlt_le_weak _ _ HtrQ)) as Hband.
    lra.
Qed.

(* The W5 supply headline: the six-premise conditional chain drives the *)
(* exact landed rateslot target shape. *)
Theorem piu_zz_hmu_distpt_supply :
  forall (A B : nat -> Z) (dv : Z -> Z -> Q),
  (forall a b : Z, piu_mu_QleT 0 (dv a b)) ->
  (forall (a b p : Z) (q : nat), (1 <= q)%nat ->
     piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
       (inject_Z (Z.of_nat q) * dv a b
         + inject_Z (Z.abs b) * dv (- p)%Z (Z.of_nat q))) ->
  (forall n : nat,
     piu_mu_and2
       (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n)))
       (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n)))) ->
  (forall (p : Z) (q : nat), (1 <= q)%nat ->
     sigT (fun n : nat => piu_mu_and3
       (piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
          (piu_mu_epos (piu_zz_ec_tau * n)))
       (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
       (piu_mu_QleT (piu_mu_epos (piu_zz_ec_sigma * n) ^ Z.of_nat piu_zz_ec_tau)
          (piu_zz_ec_kappa ^ Z.of_nat piu_zz_ec_tau
            * inject_Z (Z.of_nat q)
              ^ Z.of_nat (piu_zz_ec_sigma + piu_zz_ec_tau))))) ->
  (forall n : nat,
     S02_CauchyComplete.QleT' (dv (A n) (B n)) ((13 # 400) ^ Z.of_nat n)) ->
  (forall a b : Z, (1 <= b)%Z ->
     sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
       S02_CauchyComplete.QleT' (dv (- a)%Z b)
         (Qabs (inject_Z b * lw0m_xL k - inject_Z a)))) ->
  forall q : Q, (0 < q)%Q ->
  sigT (fun ee : Q => And (S02_CauchyComplete.QltT 0 ee)
    (lw1m_dist_pt q ((piu1932_ck_alpha piu_zz_c0_criterion 8 q
                      + (2 # 1) * ee)%Q))).
Proof.
  intros A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq.
  apply (piu_zz_hmu_distpt_of_realcert q).
  exact (piu_zz_ec_mu_cond A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq).
Qed.

(* Full-chain corollary: the supply reassembles to the rate-form slot   *)
(* certificate through the landed adapter, closing the two-form circuit *)
(* inside one statement. *)
Theorem piu_zz_hmu_realcert_of_chain :
  forall (A B : nat -> Z) (dv : Z -> Z -> Q),
  (forall a b : Z, piu_mu_QleT 0 (dv a b)) ->
  (forall (a b p : Z) (q : nat), (1 <= q)%nat ->
     piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
       (inject_Z (Z.of_nat q) * dv a b
         + inject_Z (Z.abs b) * dv (- p)%Z (Z.of_nat q))) ->
  (forall n : nat,
     piu_mu_and2
       (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n)))
       (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n)))) ->
  (forall (p : Z) (q : nat), (1 <= q)%nat ->
     sigT (fun n : nat => piu_mu_and3
       (piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
          (piu_mu_epos (piu_zz_ec_tau * n)))
       (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
       (piu_mu_QleT (piu_mu_epos (piu_zz_ec_sigma * n) ^ Z.of_nat piu_zz_ec_tau)
          (piu_zz_ec_kappa ^ Z.of_nat piu_zz_ec_tau
            * inject_Z (Z.of_nat q)
              ^ Z.of_nat (piu_zz_ec_sigma + piu_zz_ec_tau))))) ->
  (forall n : nat,
     S02_CauchyComplete.QleT' (dv (A n) (B n)) ((13 # 400) ^ Z.of_nat n)) ->
  (forall a b : Z, (1 <= b)%Z ->
     sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
       S02_CauchyComplete.QleT' (dv (- a)%Z b)
         (Qabs (inject_Z b * lw0m_xL k - inject_Z a)))) ->
  forall q : Q, (0 < q)%Q ->
  real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq.
  apply piu_zz_Hmu_rateslot_of_distpt.
  - exact Hq.
  - exact (piu_zz_hmu_distpt_supply A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq).
Qed.

(* ==== Section 4. Interface bites (first-wave and W4 meshing) ==== *)

(* Bite W5/N5: a born spot anchor at q = 3 beyond the N5 q = 1 and      *)
(* q = 2 faces, on the same closed-form witness. *)
Lemma piu_zz_hmu_n5_nescD3_limbs :
  (2 * 3 * 3 ^ piu_zz_ec_nescD 3 <= 20 ^ piu_zz_ec_nescD 3)%nat
  /\ (2 ^ (Z.of_nat (17 * piu_zz_ec_nescD 3)) <= 35831808 * 3 ^ 7)%Z.
Proof. split; vm_compute; [lia | discriminate]. Qed.

(* Bite W5/N5: the HescD supply contract instantiated at an abstract    *)
(* coefficient pair (limb 2 slot stays explicit, the p-adic clearing    *)
(* gap per the N5 registration). *)
Lemma piu_zz_hmu_n5_hescd_contract : forall (A B : nat -> Z) (p : Z) (q : nat),
  (1 <= q)%nat ->
  piu_mu_ZleT 1 (Z.abs (A (piu_zz_ec_nescD q) * Z.of_nat q
                          + B (piu_zz_ec_nescD q) * p)) ->
  piu_zz_ec_HescD_face A B p q.
Proof.
  intros A B p q Hq H2.
  exact (piu_zz_ec_HescD_of_window A B p q Hq H2).
Qed.

(* Bite W5/N6'-b: the q = 1 witness landing composed with the q = 1     *)
(* forcing anchor (the N5 witness closes the N6'-b anchor band). *)
Lemma piu_zz_hmu_n6b_q1_landing :
  piu_zz_ec_nescD 1 = 1%nat /\ (2 ^ 17 <= 35831808 < 2 ^ 34)%Z.
Proof.
  split.
  - vm_compute. reflexivity.
  - exact piu_zz_ec_q1_anchor.
Qed.

(* Bite W5/N4: the W4 combined face plus the C1-branch account assembles *)
(* into the max-form head headline - the premise bundle the W5 assembly *)
(* carries forward. *)
Lemma piu_zz_hmu_n4_maxform_of_combined : forall (A B : nat -> Z) (s2f : nat -> Q),
  piu_zz_s2_head_combined_face A B s2f ->
  (forall n : nat,
     S02_CauchyComplete.QleT' (inject_Z 41%Z) (inject_Z (Z.of_nat n)) ->
     S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2 ->
     S02_CauchyComplete.QleT' (Qpower (s2f n) 4%Z)
       (Qpower piu_zz_s2_C1ln_hi 4%Z * inject_Z (Z.of_nat (n * n * n)))%Q) ->
  forall n : nat, (41 <= n)%nat ->
  sum (S02_CauchyComplete.QleT' (s2f n)
         (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q)
      (S02_CauchyComplete.QleT' (Qpower (s2f n) 4%Z)
         (Qpower piu_zz_s2_C1ln_hi 4%Z
            * inject_Z (Z.of_nat (n * n * n)))%Q).
Proof.
  intros A B s2f [HA [H1 H2 H3]] HC1 n Hn.
  apply (piu_zz_s2_head_maxform s2f H1 H2 H3 HC1 n Hn).
Qed.

(* Bite W5/N1: the s1-length calibration relayed on the S02 carrier. *)
Lemma piu_zz_hmu_n1_s1len_relay : forall n j : nat, (18 <= n)%nat ->
  QleT' ((Z.of_nat (length (zz_Mj n j))) # 1)
        ((Z.of_nat (2 ^ (2 * n))) # 1).
Proof.
  intros n j Hn.
  exact (zz_s1_len_QleT' n j Hn).
Qed.

(* Bite W5/N2a: the Pell sqrt3 chain and the argmin/N0 column gap on    *)
(* one face (Set-carried product of the two born faces). *)
Lemma piu_zz_hmu_n2a_chain :
  (S02_CauchyComplete.QltT (3 # 1)%Q ((1351 # 780)%Q * (1351 # 780)%Q)
   * S02_CauchyComplete.QltT (inject_Z 187) (inject_Z 1348))%type.
Proof.
  split.
  - exact piu_zz_c2_pell_sqrt3_lt_1351_780.
  - exact piu_zz_c7_argmin_lt_N0.
Qed.

(* Bite W5/N2c: the numeric-bank kappa and 2*kappa*c0 anchors on one    *)
(* face (Set-carried product), matching the Section 1 pins. *)
Lemma piu_zz_hmu_n2c_bank_pair :
  (S02_CauchyComplete.QeqT (inject_Z 35831808)%Q
     (inject_Z (2 ^ 14 * 3 ^ 7))%Q
   * S02_CauchyComplete.QeqT
       ((2 # 1)%Q * (35831808 # 1)%Q * (1 # 71663616)%Q)%Q (1 # 1)%Q)%type.
Proof.
  split.
  - exact piu_zz_n2c_bank_kappa.
  - exact piu_zz_n2c_bank_c0.
Qed.

(* Bite W5/N2b: the coefficient-side band slot (hcoef17 face) is the     *)
(* first component of the W4 combined face - this relay assembles the    *)
(* N2b supply with the three noise-piece slots into the combined face    *)
(* the W5 assembly carries forward. *)
Lemma piu_zz_hmu_n2b_hcoef17_relay : forall (A B : nat -> Z) (s2f : nat -> Q),
  piu_zz_n2b_hcoef17_A A ->
  (forall n : nat,
     S02_CauchyComplete.QleT' piu_zz_s2_w1 (inject_Z (Z.of_nat n)) ->
     S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w2 ->
     S02_CauchyComplete.QleT' (s2f n)
       (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q) ->
  (forall n : nat,
     S02_CauchyComplete.QleT' piu_zz_s2_w2 (inject_Z (Z.of_nat n)) ->
     S02_CauchyComplete.QleT' (inject_Z (Z.of_nat n)) piu_zz_s2_w3 ->
     S02_CauchyComplete.QleT' (s2f n)
       (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q) ->
  (forall n : nat,
     S02_CauchyComplete.QleT' piu_zz_s2_w3 (inject_Z (Z.of_nat n)) ->
     S02_CauchyComplete.QleT' (s2f n)
       (piu_zz_s2_C2ln_hi * inject_Z (Z.of_nat n))%Q) ->
  piu_zz_s2_head_combined_face A B s2f.
Proof.
  intros A B s2f HA H1 H2 H3.
  apply piu_mu_and2_i.
  - exact HA.
  - apply piu_mu_and3_i.
    + exact H1.
    + exact H2.
    + exact H3.
Qed.

(* ==== Section 5. Audit ==== *)

Print Assumptions piu_zz_hmu_kappa_decomp.
Print Assumptions piu_zz_hmu_kappa_pin.
Print Assumptions piu_zz_hmu_sigma14_pin.
Print Assumptions piu_zz_hmu_tau2_pin.
Print Assumptions piu_zz_hmu_span14.
Print Assumptions piu_zz_hmu_kappa_c0_bool.
Print Assumptions piu_zz_hmu_kappa_c0.
Print Assumptions piu_zz_hmu_c0_inv.
Print Assumptions piu_zz_hmu_qpow_inject_alpha8.
Print Assumptions piu_zz_hmu_qpow_inject_tau2.
Print Assumptions piu_zz_hmu_distpt_of_realcert.
Print Assumptions piu_zz_hmu_distpt_supply.
Print Assumptions piu_zz_hmu_realcert_of_chain.
Print Assumptions piu_zz_hmu_n5_nescD3_limbs.
Print Assumptions piu_zz_hmu_n5_hescd_contract.
Print Assumptions piu_zz_hmu_n6b_q1_landing.
Print Assumptions piu_zz_hmu_n4_maxform_of_combined.
Print Assumptions piu_zz_hmu_n1_s1len_relay.
Print Assumptions piu_zz_hmu_n2a_chain.
Print Assumptions piu_zz_hmu_n2c_bank_pair.
Print Assumptions piu_zz_hmu_n2b_hcoef17_relay.

(* Extraction differential: the named values and Set-carried statements *)
(* compile to OCaml with no Obj.magic and no lost names. *)
Extraction "piu_zz_hmu_distpt_supply_ext" piu_zz_hmu_kappa_c0 piu_zz_hmu_c0_inv
  piu_zz_hmu_qpow_inject_alpha8 piu_zz_hmu_qpow_inject_tau2
  piu_zz_hmu_distpt_of_realcert piu_zz_hmu_distpt_supply
  piu_zz_hmu_realcert_of_chain piu_zz_hmu_n5_hescd_contract
  piu_zz_hmu_n4_maxform_of_combined.
