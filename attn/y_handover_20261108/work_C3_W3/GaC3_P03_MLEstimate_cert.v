(* ===================================================================== *)
(* GaC3_P03_MLEstimate_cert.v                                             *)
(*                                                                       *)
(* Mission: node C3-P03 certificate face (R2 discipline): exact-Q spot    *)
(*   checks of the L1 path-length closed forms and one ML-instance       *)
(*   sample, discharged by vm_compute (the proof-topology face carries   *)
(*   zero vm_compute - LINT-5 word-face split; this cert file holds the  *)
(*   computational word-face by design).                                 *)
(* Dependencies: GaC3_P03_MLEstimate (stem), GaC3_P02_LineIntegralAlg    *)
(*   (path carrier).  Stdlib: QArith.                                    *)
(* Constructivity: certificate word-face only; zero Axiom, zero          *)
(*   Parameter.                                                          *)
(* Build: coqc -native-compiler no -q (sandbox -Q paths), cpu_guard v3    *)
(*   wrapper (-AllowG3 -GearForce 0 -TempLimit 98 -LoadLimit 60 -CoreN 2). *)
(* ===================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import List.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P03_MLEstimate.

Local Open Scope Q_scope.
Import ListNotations.

(* L1 closed forms: |dz| sums evaluated exactly. *)
Lemma GaC3_P03_cert_len1_vline : GaC3_P03_path_len1 (GaC3_P02_vline_seg 1 10) == 20.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC3_P03_cert_len1_hline : GaC3_P03_path_len1 (GaC3_P02_hline_seg 2 5 3) == 3.
Proof. vm_compute; reflexivity. Qed.

(* ML instance sample: vline length 20, value (3,4) bounded by B = 5,    *)
(* real component -80, |−80| = 80 <= 100.                                *)
Lemma GaC3_P03_cert_ml_vline_sample :
  Qle_bool (Qabs (GaC3_P02_path_sumR (GaC3_P02_vline_seg 1 10) [(3, 4)])) (5 * 20) = true.
Proof. vm_compute; reflexivity. Qed.
