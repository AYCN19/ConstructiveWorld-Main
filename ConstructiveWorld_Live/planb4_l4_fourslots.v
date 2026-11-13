(* ========================================================================= *)
(* ConstructiveWorld-Main - unif L4 piece: the four-slot interface form.     *)
(*                                                                           *)
(* Mission      : W-L3 slot-landing ticket (route volume, section on the     *)
(*                four-slot ladder).  The six-premise interface of           *)
(*                piu1932_uncond_zz converges here: limbs Hp and Htri are    *)
(*                CLOSED in the tree (l2_dv_hp / l2_dv_htri, born proofs    *)
(*                in planb3_g1_g2_design re-exported by planb4_l2_dv_cast),  *)
(*                so the four-slot twin consumes them from the pool and      *)
(*                keeps the four remaining premises as explicitly named      *)
(*                slot faces.  The four slot faces are born Set-typed        *)
(*                statements in the verbatim consumption shapes of           *)
(*                piu1932_uncond_zz at the cast carrier dv := l2_dv; none    *)
(*                of them is claimed here.  The six-premise original is      *)
(*                kept untouched as the signature-stability twin target      *)
(*                (the piu1932_uncond_zz_rateloaded precedent, kept in the   *)
(*                same file).                                                *)
(*                Slot ledger (supply-line mapping per the route volume,     *)
(*                R8 rows; final refinement belongs to the SL12 joint        *)
(*                survey, per the no-pricing-before-survey law):             *)
(*                  planb4_l4_hcoef_slot <- SL1 (ln L_n bound;               *)
(*                    Chebyshev-Sylvester certificate scheme; Gantumur       *)
(*                    arXiv:2512.02466 constants pending full-text) and      *)
(*                    SL3 (coefficient-sum N2c chain; see the Hcoef@17      *)
(*                    registration planb3_g1_g2_design.v:170-180);          *)
(*                  planb4_l4_hesc_slot  <- SL4 (Delta_n <> 0 witness        *)
(*                    newness feeding the escape construction; the          *)
(*                    n = 1..3 machine-false note in u5_carrier_align is     *)
(*                    the recorded depth warning);                          *)
(*                  planb4_l4_hcage_slot <- SL2 (the |I_n| measure bound;    *)
(*                    polygonal-contour or real-integral recast);           *)
(*                  planb4_l4_hexit_slot <- the L6 ledger exit debt          *)
(*                    (ZZ2020 dual-pairing general anchor or carrier         *)
(*                    rebinding; planb3_g1_g2_design.v:132-137); the        *)
(*                    orientation is the consumption-verbatim form,         *)
(*                    l2_dv (-a) b (the l3 exit slot face stores the         *)
(*                    carrier-symmetric form l2_dv b (-a); the carrier is   *)
(*                    the absolute value of a sum, so the two faces agree   *)
(*                    pointwise - a bridge lemma belongs to the supply       *)
(*                    ticket, not to this file).                            *)
(*                Interface-change ledger: this file only ADDS a twin and    *)
(*                born faces; the certified six-premise signature, the       *)
(*                gate8 vacuity-sentinel probes, and every existing          *)
(*                consumer are untouched, so the non-emptiness evidence      *)
(*                chain is preserved by construction.                       *)
(* Dependencies : S01_BaseRing (NatLe); S02_CauchyComplete;                 *)
(*                piu_mu_criterion; LW0MLicBridge; piu_zz_constants;         *)
(*                piu_zz_e_carrier (the ec_sigma/tau/kappa names);           *)
(*                piu_zz_bridge_real (piu_zz_C0); piu1932_uncond_zz (the     *)
(*                six-premise original); planb4_l2_dv_cast (the cast         *)
(*                carrier and the two closed limbs); tlw1448_rebase;         *)
(*                tlw1448_transfer (tlw1448_ck);                             *)
(*                tlw1703_unif_tight_instantiation; LW1PiMeasure.            *)
(* References   : piu1932_uncond_zz.v:62-108 (the six-premise form and the   *)
(*                four-slot direct-supply pattern); planb4_l2_dv_cast.v      *)
(*                (the cast carrier, closed limbs, exit face);               *)
(*                planb4_l3_limbs_discharge.v (the limbs envelope precedent  *)
(*                and the exit slot wall registration);                      *)
(*                planb3_g1_g2_design.v:122-180 (the G2 debts and the        *)
(*                Hcoef@17 registration); the route volume (the four-slot    *)
(*                ladder and the R8 slot rows).                              *)
(* Constructivity: every new statement is Set-carried (piu_mu_QleT,          *)
(*                piu_mu_ZleT, piu_mu_and2, piu_mu_and3, sigT, QleT');       *)
(*                the twin proof body is a single application composing      *)
(*                the closed limbs with the four slots; postulate-free;      *)
(*                no Parameter, no Conjecture, no Abort anywhere.            *)
(* Build        : coqc -q -native-compiler no -Q <Live> ""                   *)
(*                planb4_l4_fourslots.v (Rocq 9.3.0, E952 script form).      *)
(* ========================================================================= *)

From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import piu_mu_criterion.
Require Import LW0MLicBridge.
Require Import piu_zz_constants.
Require Import piu_zz_e_carrier.
Require Import piu_zz_bridge_real.
Require Import piu1932_uncond_zz.
Require Import planb4_l2_dv_cast.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1703_unif_tight_instantiation.
Require Import LW1PiMeasure.

(* ================================================================== *)
(* Section 1. The four slot faces (born statements, honestly          *)
(*            unproven; verbatim consumption shapes of                *)
(*            piu1932_uncond_zz at the cast carrier dv := l2_dv).     *)
(* ================================================================== *)

(* Slot SL1 ledger face (the coefficient-growth premise Hcoef).       *)
Definition planb4_l4_hcoef_slot (A B : nat -> Z) : Set :=
  forall n : nat,
    piu_mu_and2
      (piu_mu_ZleT (Z.abs (A n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n)))
      (piu_mu_ZleT (Z.abs (B n)) (2 ^ Z.of_nat (piu_zz_ec_sigma * n))).

(* Slot SL4 ledger face (the escape premise Hesc; the witness-newness *)
(* determinant Delta_n <> 0 feeds its supply construction).           *)
Definition planb4_l4_hesc_slot (A B : nat -> Z) : Set :=
  forall (p : Z) (q : nat), (1 <= q)%nat ->
    sigT (fun n : nat => piu_mu_and3
      (piu_mu_QleT (inject_Z (Z.of_nat (2 * q)))
         (piu_mu_epos (piu_zz_ec_tau * n)))
      (piu_mu_ZleT 1 (Z.abs (A n * Z.of_nat q + B n * p)))
      (piu_mu_QleT (piu_mu_epos (piu_zz_ec_sigma * n) ^ Z.of_nat piu_zz_ec_tau)
         (piu_zz_ec_kappa ^ Z.of_nat piu_zz_ec_tau
           * inject_Z (Z.of_nat q) ^ Z.of_nat (piu_zz_ec_sigma + piu_zz_ec_tau)))).

(* Slot SL2 ledger face (the cage premise Hcage; the |I_n| measure     *)
(* bound is its supply line).                                         *)
Definition planb4_l4_hcage_slot (A B : nat -> Z) : Set :=
  forall n : nat,
    S02_CauchyComplete.QleT' (l2_dv (A n) (B n))
      ((13 # 400) ^ Z.of_nat n).

(* Slot SL4/exit ledger face (the exit premise Hexit; the L6 ledger    *)
(* debt ZZ2020 dual-pairing general anchor).  Orientation: the         *)
(* consumption-verbatim l2_dv (-a) b.                                  *)
Definition planb4_l4_hexit_slot : Set :=
  forall (a b : Z), (1 <= b)%Z ->
    sigT (fun K : nat => forall k : nat, (K <= k)%nat ->
      S02_CauchyComplete.QleT' (l2_dv (- a)%Z b)
        (Qabs (inject_Z b * lw0m_xL k - inject_Z a))).

(* ================================================================== *)
(* Section 2. The four-slot twin (signature convergence 6 -> 4):      *)
(*            the closed limbs come from the pool, the four slots     *)
(*            remain the explicit honest interface.  The proof body   *)
(*            is a single application; no new mathematics.            *)
(* ================================================================== *)

Theorem piu1932_uncond_zz_fourslots :
  forall (A B : nat -> Z),
  planb4_l4_hcoef_slot A B ->
  planb4_l4_hesc_slot A B ->
  planb4_l4_hcage_slot A B ->
  planb4_l4_hexit_slot ->
  forall q : Q,
    NatLe (tlw1448_nsep_rebase tlw1448_ck q)
          (Datatypes.S (tlw1703_unif_bpow_c piu_zz_C0 8 (lw1m_height q))).
Proof.
  intros A B Hcoef Hesc Hcage Hexit q.
  exact (piu1932_uncond_zz A B l2_dv l2_dv_hp l2_dv_htri
           Hcoef Hesc Hcage Hexit q).
Qed.

(* ================================================================== *)
(* Section 3. Assumption audit (per-statement, tail).                 *)
(* ================================================================== *)

Print Assumptions planb4_l4_hcoef_slot.
Print Assumptions planb4_l4_hesc_slot.
Print Assumptions planb4_l4_hcage_slot.
Print Assumptions planb4_l4_hexit_slot.
Print Assumptions piu1932_uncond_zz_fourslots.
