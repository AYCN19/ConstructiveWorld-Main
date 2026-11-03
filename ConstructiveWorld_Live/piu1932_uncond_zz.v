(* ========================================================================= *)
(* Mission      : Route B assembly piece, W5 four-slot direct-supply form     *)
(*                (same-name replacement candidate of the registered unit).  *)
(*                The rate-slot nsep bound NatLe (tlw1448_nsep_rebase ck q)  *)
(*                (S (bpow_c C0 8 (height q))) is derived with all four      *)
(*                slots of tlw1703_unif_rebase_le_Sbpowc supplied directly:  *)
(*                slots 1/2/4 from the pool (C0 positivity, threshold        *)
(*                positivity, ck_alpha reflexivity) and slot 3 from the      *)
(*                six-premise conditional chain piu_zz_ec_mu_cond through    *)
(*                the v2 rate-slot bridge, so no rate-form certificate is    *)
(*                taken as an abstract premise any more; the premise group   *)
(*                (Hp/Htri/Hcoef/Hesc/Hcage/Hexit) is the explicit honest    *)
(*                interface.  The previous rate-loaded signature is kept as  *)
(*                a twin theorem (signature-stability migration ledger).     *)
(*                C0 = 1/10^9 (halving anchor 2*C0 < c0 = 1/71663616),       *)
(*                alpha = 8 (ZZ mu = 1 + sigma/tau = 7.1032... < 8).          *)
(* Dependencies : S01-S03, S10, PiEnvelope, LW0MLicBridge, LW1PiMeasure,     *)
(*                tlw1448_rebase, tlw1448_transfer, tlw1703_unif_tight_       *)
(*                instantiation, piu1932_tight_bound_instantiated,           *)
(*                piu_zz_bridge_real, piu_zz_bridge_rateslot,                *)
(*                piu_zz_constants, piu_zz_e_carrier (six-premise chain).    *)
(* References   : Zeilberger-Zudilin, Moscow J. Comb. Number Theory 9        *)
(*                (2020) 407-419; K01 transport precedent; E01 sec.2.0 Route *)
(*                B ruling (cwin dead slot HC0_valid retired); W5 workorder.  *)
(* Constructivity: every named statement is Set-carried (NatLe, QltT',      *)
(*                zzQltT, real_lt, sigT); the six chain premises are         *)
(*                explicit arguments (honest interface); 无公理依赖、        *)
(*                无未证假设, no Parameter, no Conjecture, no Abort.          *)
(* Build        : rocq c -native-compiler no -q -Q . "" -Q vo ""              *)
(*                piu1932_uncond_zz.v under cpu_guard_v3 (-LoadLimit 60      *)
(*                -TempLimit 98 -AllowG3 -GearForce 0 -CoreN 2), Rocq 9.1.0. *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1703_unif_tight_instantiation.
Require Import piu1932_tight_bound_instantiated.
Require Import piu_mu_criterion.
Require Import piu_zz_bridge_real.
Require Import piu_zz_bridge_rateslot.
Require Import piu_zz_constants.
Require Import piu_zz_e_carrier.

(* Pre-flight vernacular check against the pinned pool statement. *)
Check tlw1703_unif_rebase_le_Sbpowc.

(* ==== Section 1. Four-slot direct supply from the six-premise chain ==== *)

Section Piu1932Instantiation.

(** The W5 endpoint form: the four slots are supplied directly, slot 3
    through piu_zz_ec_mu_cond composed with the v2 rate-slot bridge. *)
Theorem piu1932_uncond_zz :
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
  apply (tlw1703_unif_rebase_le_Sbpowc piu_zz_C0 8 (piu1932_ck_alpha piu_zz_C0 8)).
  - (* slot 1, HC0_pos: QltT' 0 piu_zz_C0 from the pool *)
    exact piu_zz_C0_pos.
  - (* slot 2, Hcrt_pos: the threshold ck_alpha C0 8 q' is positive *)
    intros q'. apply piu1932_div_pos.
    + exact (QltT_to_Qlt _ _ piu_zz_C0_pos).
    + apply Qlt_to_QltT'. apply tlw1703_unif_qpow_pos.
      exact (QltT_to_Qlt _ _
               (lw1m_snq_pos (Pos.to_nat (Qden (Qred q'))))).
  - (* slot 3, Hcrt_dist: the pointwise distance certificate, supplied   *)
    (* directly by the six-premise chain through the v2 rate-slot bridge *)
    intros q'.
    exact (piu_zz_bridge_full_v2
             (piu_zz_ec_mu_cond A B dv Hp Htri Hcoef Hesc Hcage Hexit) q').
  - (* slot 4, Hcert_pow: crt := ck_alpha, reflexive (Route B beta unused) *)
    intros q'. apply piu1932_qleT'_refl.
Qed.

(** Signature-stability twin: the previous rate-loaded form, kept verbatim
    so any consumer of the old signature keeps a target. *)
Theorem piu1932_uncond_zz_rateloaded :
  (forall q : Q, (0 < q)%Q ->
     real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
             (real_metric real_pi_geom (real_const q))) ->
  forall q : Q,
    NatLe (tlw1448_nsep_rebase tlw1448_ck q)
          (Datatypes.S (tlw1703_unif_bpow_c piu_zz_C0 8 (lw1m_height q))).
Proof.
  intros Hmu q.
  apply (tlw1703_unif_rebase_le_Sbpowc piu_zz_C0 8 (piu1932_ck_alpha piu_zz_C0 8)).
  - exact piu_zz_C0_pos.
  - intros q'. apply piu1932_div_pos.
    + exact (QltT_to_Qlt _ _ piu_zz_C0_pos).
    + apply Qlt_to_QltT'. apply tlw1703_unif_qpow_pos.
      exact (QltT_to_Qlt _ _
               (lw1m_snq_pos (Pos.to_nat (Qden (Qred q'))))).
  - intros q'. exact (piu_zz_bridge_full_v2 Hmu q').
  - intros q'. apply piu1932_qleT'_refl.
Qed.

End Piu1932Instantiation.

(* ==== Section 2. Assumption audit ==== *)

Print Assumptions piu1932_uncond_zz.
Print Assumptions piu1932_uncond_zz_rateloaded.
Print Assumptions piu_zz_ec_mu_cond.
Print Assumptions piu_zz_bridge_full_v2.
Print Assumptions piu_zz_bridge_nonpos.
Print Assumptions piu_zz_C0_pos.
Print Assumptions tlw1703_unif_rebase_le_Sbpowc.

(* ==== Section 3. Stop-point shape and numeric cross-checks ==== *)

(* Stop-point expansion: the bound ceiling is the exact integer account    *)
(* 8/C0 = 8 * 10^9 (zero rounding); the universal shape is checked by      *)
(* conversion, the sample points on the binary Z carrier of Qceiling.      *)
Example piu1932_uncond_zz_stop_shape : forall h : nat,
  Datatypes.S (tlw1703_unif_bpow_c piu_zz_C0 8 h) =
  Datatypes.S (Datatypes.S
    (Z.to_nat (Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat h # 1) 8)%Q)))).
Proof. reflexivity. Qed.

Example piu1932_uncond_zz_stop_h2  :
  Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat 2 # 1) 8)%Q) = 2048000000000%Z.
Proof. vm_compute. reflexivity. Qed.
Example piu1932_uncond_zz_stop_h3  :
  Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat 3 # 1) 8)%Q) = 52488000000000%Z.
Proof. vm_compute. reflexivity. Qed.
Example piu1932_uncond_zz_stop_h10 :
  Qceiling ((8 / piu_zz_C0 * q_pow (Z.of_nat 10 # 1) 8)%Q) = 800000000000000000%Z.
Proof. vm_compute. reflexivity. Qed.

(* Exponent compatibility: the ZZ upper measure 7.103205334138 < 8, the    *)
(* instantiated exponent (only the exponent, never the certificate). *)
Example piu1932_uncond_zz_alpha_guard :
  zzQltT piu_zzc_mu_zz_upper (8 # 1)%Q.
Proof. vm_compute. exact tt. Qed.

(* Halving cross-check: 2 * C0 = 2e-9 < c0 = 1.3954e-8. *)
Example piu1932_uncond_zz_halving_view :
  zzQltT ((2 # 1) * piu_zz_C0)%Q piu_zz_c0_criterion.
Proof. vm_compute. exact tt. Qed.

(* ==== Section 4. Extraction witness list ==== *)

Extraction "piu1932_uncond_zz_ext" piu1932_uncond_zz piu1932_uncond_zz_rateloaded
  tlw1703_unif_bpow_c piu_zz_bridge_full_v2.
