(* ========================================================================= *)
(* Mission      : Rate-slot nsep corollary of the pi uniform-strength        *)
(*                irrationality endpoint chain: NatLe (tlw1448_nsep_rebase   *)
(*                tlw1448_ck q) (S (tlw1703_unif_bpow_c piu_zz_C0 8          *)
(*                (lw1m_height q))), closed through the registered           *)
(*                signature-stability twin piu1932_uncond_zz_rateloaded of   *)
(*                the top piece piu1932_uncond_zz composed with the Hmu      *)
(*                assembly lemma piu_zz_hmu_certificate_assembly (the       *)
(*                rate-form mu certificate assembled from the dist_pt        *)
(*                supply witness).  The six chain premises                   *)
(*                (Hp/Htri/Hcoef/Hesc/Hcage/Hexit) are carried as the        *)
(*                explicit honest interface, matching the registered form    *)
(*                of the top piece; the premise-free form of this            *)
(*                corollary requires closing the registered open slot        *)
(*                piu_zz_Hmu_criterion (the concrete supply of the           *)
(*                six-premise chain) and is not claimed here.                *)
(* Dependencies : S01_BaseRing, S02_CauchyComplete, LW0MLicBridge,           *)
(*                LW1PiMeasure, tlw1448_rebase, tlw1448_transfer,            *)
(*                tlw1703_unif_tight_instantiation, piu_mu_criterion,        *)
(*                piu_zz_bridge_real, piu_zz_e_carrier, the registered top   *)
(*                piece piu1932_uncond_zz, the assembly piece                *)
(*                piu_zz_hmu_certificate_assembly; stdlib QArith, ZArith.    *)
(* References   : Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9        *)
(*                (2020) 407-419, Lemma 2; tlw1703_unif_rebase_le_Sbpowc     *)
(*                (four-slot rate-slot derivation); piu1932_uncond_zz        *)
(*                (top piece, rateloaded twin).                              *)
(* Constructivity: the named statement is Set-carried (NatLe, sigT faces in  *)
(*                the premise group); the six chain premises are explicit    *)
(*                arguments (honest interface); no Axiom, no Parameter, no   *)
(*                Conjecture, no Abort, no Admitted; the proof body is the   *)
(*                two-line composition of the twin with the assembly lemma.  *)
(* Build        : coqc -native-compiler no -q -Q . "" -Q <certified vo tree> *)
(*                "" piu1932_uncond_zz_final.v, Rocq 9.3.0, under cpu_guard  *)
(*                v3 (-TempLimit 98 -AllowG3), serial single lane.           *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1703_unif_tight_instantiation.
Require Import piu_mu_criterion.
Require Import piu_zz_bridge_real.
Require Import piu_zz_e_carrier.
Require Import piu1932_uncond_zz.
Require Import piu_zz_hmu_certificate_assembly.

(* ==== Section 1. The rate-slot corollary through the assembly lemma ==== *)

Theorem piu1932_uncond_zz_final :
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
  forall q : Q,
    NatLe (tlw1448_nsep_rebase tlw1448_ck q)
          (Datatypes.S (tlw1703_unif_bpow_c piu_zz_C0 8 (lw1m_height q))).
Proof.
  intros A B dv Hp Htri Hcoef Hesc Hcage Hexit q.
  exact (piu1932_uncond_zz_rateloaded
          (piu_zz_hmu_certificate_assembly
             A B dv Hp Htri Hcoef Hesc Hcage Hexit) q).
Qed.

(* ==== Section 2. Assumption audit ==== *)

Print Assumptions piu1932_uncond_zz_final.
