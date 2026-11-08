(* ConstructiveWorld-Main - certificate face of node C3-P03: exact-Q spot
   checks for the L1 lengths and one ML instance. *)
(** * GaC3_P03_MLEstimate_cert: certificates for the ML-estimate node.
    Mission.  Node C3-P03 certificate face: exact-Q spot checks of the
      L1 path-length closed forms and one ML-instance sample,
      discharged by vm_compute (the proof-topology face carries zero
      vm_compute; this cert file holds the computational word-face by
      design).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [List].  Requires [GaC3_P02_LineIntegralAlg]
      (path carrier) and [GaC3_P03_MLEstimate] (stem) of this
      development.
    References.  The proof face [GaC3_P03_MLEstimate], whose L1
      closed forms and ML bound this certificate samples.
    Constructivity.  Certificate word-face only; the lemmas close by
      vm_compute + reflexivity over literal data; [coqchk] reports
      zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC3_P03_MLEstimate_cert.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3] (-AllowG3 -GearForce 0
      -TempLimit 98 -LoadLimit 60 -CoreN 2). *)

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
