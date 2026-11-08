(* ========================================================================= *)
(* Mission      : Hmu certificate assembly for the pi uniform-strength       *)
(*                irrationality endpoint chain.  The rate-form mu            *)
(*                certificate real_lt (real_const (piu1932_ck_alpha          *)
(*                piu_zz_c0_criterion 8 q)) (real_metric real_pi_geom        *)
(*                (real_const q)) is assembled from the dist_pt supply       *)
(*                witness of the six-premise conditional chain: the          *)
(*                existential margin ee is selected from the witness sigT,   *)
(*                its positivity face QltT 0 ee (hence 2*ee > 0) is kept,    *)
(*                and the rate form is closed through the landed             *)
(*                distance-monotone transport piu_zz_Hmu_rateslot_of_distpt  *)
(*                (a pointwise distance certificate at the doubled           *)
(*                threshold d + 2*ee delivers the rate certificate at d).    *)
(*                The six chain premises (Hp/Htri/Hcoef/Hesc/Hcage/Hexit)    *)
(*                remain the explicit honest interface, exactly as in the    *)
(*                registered top piece piu1932_uncond_zz; the premise-free   *)
(*                form of the mu certificate is the registered open slot     *)
(*                piu_zz_Hmu_criterion and is not closed here.  A threshold  *)
(*                relaxation step additionally lands the same certificate    *)
(*                at the halving-anchor constant C0 = 1/10^9 (the workorder  *)
(*                face piu1932_ck_alpha piu_zz_C0 8 q).                      *)
(* Dependencies : S01-S03, S10, PiEnvelope, LW0MLicBridge, LW1PiMeasure,     *)
(*                piu1932_tight_bound_instantiated, piu_mu_criterion,        *)
(*                piu_zz_bridge_real, piu_zz_e_carrier, piu_zz_mu_assembly,  *)
(*                the registered top piece piu1932_uncond_zz, the W5 supply  *)
(*                piece piu_zz_hmu_distpt_supply; stdlib QArith, ZArith,     *)
(*                Lia, Lqa.                                                  *)
(* References   : Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9        *)
(*                (2020) 407-419, Lemma 2; piu_zz_mu_assembly (pointwise     *)
(*                distance to rate-form adapter); piu_zz_hmu_distpt_supply   *)
(*                (W5 supply headline and six-premise interface).            *)
(* Constructivity: every named statement is Set-carried (real_lt, QleT',     *)
(*                QltT, QltT', sigT, NatLe, piu_mu_* carriers); the six      *)
(*                chain premises are explicit arguments (honest interface);  *)
(*                no Axiom, no Parameter, no Conjecture, no Abort, no        *)
(*                Admitted; lia/lra appear only as auxiliary linear steps    *)
(*                inside proofs (piu1904 and piu_mu_criterion precedent).    *)
(* Build        : coqc -native-compiler no -q -Q . "" -Q <certified vo tree> *)
(*                "" piu_zz_hmu_certificate_assembly.v, Rocq 9.3.0, under    *)
(*                cpu_guard v3 (-TempLimit 98 -AllowG3), serial single lane. *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.
Require Import piu1932_tight_bound_instantiated.
Require Import piu_mu_criterion.
Require Import piu_zz_bridge_real.
Require Import piu_zz_e_carrier.
Require Import piu_zz_mu_assembly.
Require Import piu1932_uncond_zz.
Require Import piu_zz_hmu_distpt_supply.

(* ==== Section 1. Threshold relaxation on the rate-form certificate ==== *)

(* Threshold down-relaxation: a rate certificate at the larger threshold d2 *)
(* delivers the rate certificate at the smaller threshold d1, with the      *)
(* margin widened by the threshold gap d2 - d1. *)
Lemma piu_zz_hmu_thresh_dn : forall d1 d2 : Q,
  QleT' d1 d2 ->
  forall q : Q,
  real_lt (real_const d2) (real_metric real_pi_geom (real_const q)) ->
  real_lt (real_const d1) (real_metric real_pi_geom (real_const q)).
Proof.
  intros d1 d2 Hdle q Hcert.
  destruct Hcert as [eps [Heps [N HN]]].
  exists ((eps + (d2 - d1))%Q). split.
  - apply Qlt_to_QltT.
    pose proof (QltT_to_Qlt _ _ Heps) as HepsQ.
    pose proof (QleT'_to_Qle _ _ Hdle) as HdleQ.
    lra.
  - exists N. intros n Hn.
    pose proof (HN n Hn) as Hlow.
    cbn [projT1 real_const] in Hlow.
    cbn [projT1 real_const].
    set (P := projT1 (real_metric real_pi_geom (real_const q)) n) in *.
    pose proof (QltT_to_Qlt _ _ Hlow) as HlowQ.
    pose proof (QleT'_to_Qle _ _ Hdle) as HdleQ.
    apply Qlt_to_QltT.
    lra.
Qed.

(* The halving anchor C0 sits below the criterion constant on the shared   *)
(* height power, so the ck_alpha thresholds are ordered the same way. *)
Lemma piu_zz_hmu_ck_alpha_C0_le : forall q : Q,
  QleT' (piu1932_ck_alpha piu_zz_C0 8 q)
        (piu1932_ck_alpha piu_zz_c0_criterion 8 q).
Proof.
  intros q. apply piu1932_qle_to_qleT'.
  unfold piu1932_ck_alpha.
  pose proof (qeqT_imp_qeq _ _ (piu_zz_nat_hpow_qpow q 8)) as Hnp.
  rewrite <- Hnp.
  unfold Qdiv.
  apply Qmult_le_compat_r.
  - apply Qlt_le_weak.
    pose proof (QltT_to_Qlt _ _ piu_zz_halving_chain) as Hhc.
    pose proof (QltT_to_Qlt _ _ piu_zz_C0_pos) as Hpos.
    apply (Qlt_trans piu_zz_C0 ((2 # 1) * piu_zz_C0)%Q piu_zz_c0_criterion).
    + lra.
    + exact Hhc.
  - pose proof (piu_zz_hpow_ge1 q 8) as Hh.
    apply Nat.leb_le in Hh.
    pose proof (piu_zz_znat1_pos (lw1m_hpow q 8) Hh) as Hden.
    pose proof (QltT'_to_Qlt _ _ Hden) as HdenQ.
    destruct (piu_mu_Qinv_nonneg ((Z.of_nat (lw1m_hpow q 8) # 1)%Q) HdenQ)
      as [Hnn].
    exact Hnn.
Qed.

(* ==== Section 2. The Hmu assembly lemma (dist_pt witness extraction) ==== *)

(* The six-premise conditional chain delivers the pointwise distance       *)
(* certificate at the doubled threshold; the assembly extracts the margin  *)
(* and closes the rate form at the criterion constant. *)
Theorem piu_zz_hmu_certificate_assembly :
  forall (A B : nat -> Z) (dv : Z -> Z -> Q),
  (forall a b : Z, piu_mu_QleT 0 (dv a b)) ->
  (forall (a b p : Z) (q : nat), (1 <= q)%nat ->
     piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
       (inject_Z (Z.of_nat q) * dv a b
         + inject_Z (Z.abs b) * dv (Z.of_nat q) (- p)%Z)) ->
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
     QleT' (dv (A n) (B n)) ((13 # 400) ^ Z.of_nat n)) ->
  (forall a b : Z, (1 <= b)%Z ->
     sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
       QleT' (dv b (- a)%Z) (Qabs (inject_Z b * lw0m_xL k - inject_Z a)))) ->
  forall q : Q, (0 < q)%Q ->
  real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq.
  (* Step 1: select the existential margin ee from the dist_pt supply     *)
  (* witness at the doubled threshold. *)
  pose proof (piu_zz_hmu_distpt_supply
                A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq) as Hwit.
  destruct Hwit as [ee [Hee Hdist]].
  (* Step 2: the margin face QltT 0 ee carries the 2*ee > 0 account.      *)
  (* Step 3: the distance-monotone transport closes the rate form at the  *)
  (* undoubled threshold from the certificate at d + 2*ee. *)
  apply (piu_zz_Hmu_rateslot_of_distpt q Hq).
  exists ee. split.
  - exact Hee.
  - exact Hdist.
Qed.

(* ==== Section 3. The C0-face corollary (the halving-anchor form) ==== *)

(* The same assembly, landed at the halving anchor C0 = 1/10^9 through the *)
(* threshold relaxation of Section 1. *)
Theorem piu_zz_hmu_certificate_assembly_C0 :
  forall (A B : nat -> Z) (dv : Z -> Z -> Q),
  (forall a b : Z, piu_mu_QleT 0 (dv a b)) ->
  (forall (a b p : Z) (q : nat), (1 <= q)%nat ->
     piu_mu_QleT (inject_Z (Z.abs (a * Z.of_nat q + b * p)))
       (inject_Z (Z.of_nat q) * dv a b
         + inject_Z (Z.abs b) * dv (Z.of_nat q) (- p)%Z)) ->
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
     QleT' (dv (A n) (B n)) ((13 # 400) ^ Z.of_nat n)) ->
  (forall a b : Z, (1 <= b)%Z ->
     sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
       QleT' (dv b (- a)%Z) (Qabs (inject_Z b * lw0m_xL k - inject_Z a)))) ->
  forall q : Q, (0 < q)%Q ->
  real_lt (real_const (piu1932_ck_alpha piu_zz_C0 8 q))
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq.
  apply (piu_zz_hmu_thresh_dn
          (piu1932_ck_alpha piu_zz_C0 8 q)
          (piu1932_ck_alpha piu_zz_c0_criterion 8 q)).
  - exact (piu_zz_hmu_ck_alpha_C0_le q).
  - exact (piu_zz_hmu_certificate_assembly
             A B dv Hp Htri Hcoef Hesc Hcage Hexit q Hq).
Qed.

(* ==== Section 4. Assumption audit ==== *)

Print Assumptions piu_zz_hmu_thresh_dn.
Print Assumptions piu_zz_hmu_ck_alpha_C0_le.
Print Assumptions piu_zz_hmu_certificate_assembly.
Print Assumptions piu_zz_hmu_certificate_assembly_C0.
