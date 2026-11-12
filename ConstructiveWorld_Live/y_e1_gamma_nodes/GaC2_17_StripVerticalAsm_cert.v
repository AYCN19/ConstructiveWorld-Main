(** * GaC2_17_StripVerticalAsm_cert: certificate face of node C2-17.

    Mission.  Certificate face of node C2-17: the delta sample
      points of the draft certificate line (delta in {1/10, 1/4})
      and the decidable skeletons the strip face feeds on (the band
      inventory in the Notes block).  Honest scope: these bands
      certify the rational corridor forms and the decidable
      skeletons only; the Real-line corridor inequality and the
      uniform bound live on the statement face and bind when the
      mother chain lands.

    Dependencies.  Stdlib [QArith.QArith] only (the face is
      base-standalone: the proof-to-cert direction stays one-way, no
      statement-face require).

    References.  drafts_C2.md C2.17 certificate line (the delta
      sample points and the literal lower bounds); cards_C2.md C2.17
      the computable face row; gamma_module_spec.md section 4.2 the
      certificate-face shape.

    Constructivity.  Set-sorted rational identities and boolean
      skeletons; zero assumed constants, zero abandoned proofs; the
      bands close by the compute tactic under the global context.

    Build.  [coqc -native-compiler no -q -Q . ""
      GaC2_17_StripVerticalAsm_cert.v] from the flat build
      directory; the face is base-standalone (Stdlib only). *)

From Stdlib Require Import QArith.QArith.
(** Notes.  Band inventory.

    (1) The lower-bound literals [GaC2_17_lb_delta1] = 1/16 and
    [GaC2_17_lb_delta2] = 1/8 claimed for the corridor 2^delta - 1
    at the two sample deltas (both claims true on the real line:
    2^{1/10} - 1 > 1/16 and 2^{1/4} - 1 > 1/8; their Real-line
    verification faces land with the mother chain).
    (2) The uniform-bound corridor form [GaC2_17_ub_corridor] =
    2 * inverse lb (the division-free form of the card bound
    2 / (2^delta - 1)), sampled at the two literals and closing at
    32 and 16.
    (3) The literal positivity skeletons of the two bounds.
    (4) The decidable band skeleton [GaC2_17_sigma_band] =
    0 <= sigma <= 1 - delta of the (a) band membership, sampled
    one-in one-out (sigma = 1/2 in at delta = 1/4; sigma = 7/8
    out). *)


Local Open Scope Q_scope.

(* ---- Band 1: the lower-bound literals ---- *)

(* The claimed lower-bound literals for 2^delta - 1 at the sample        *)
(* deltas (delta = 1/10 and delta = 1/4).                                *)
Definition GaC2_17_lb_delta1 : Q := (1#16).
Definition GaC2_17_lb_delta2 : Q := (1#8).

(* ---- Band 2: the uniform-bound corridor form ---- *)

(* The card bound 2 / (2^delta - 1) in the division-free form            *)
(* 2 * inverse lb over the lower-bound literal.                          *)
Definition GaC2_17_ub_corridor (lb : Q) : Q := 2 * Qinv lb.

Lemma GaC2_17_cert_ub_sample1 :
  Qeq_bool (GaC2_17_ub_corridor GaC2_17_lb_delta1) 32 = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC2_17_cert_ub_sample2 :
  Qeq_bool (GaC2_17_ub_corridor GaC2_17_lb_delta2) 16 = true.
Proof. vm_compute; reflexivity. Qed.

(* ---- Band 3: the literal positivity skeletons ---- *)

(* Strict positivity as the decidable pair: non-negative and nonzero     *)
(* (the stdlib QArith of this tree carries no boolean strict-order face; *)
(* the pair form is the honest decidable substitute).                    *)
Definition GaC2_17_lb_pos (lb : Q) : bool :=
  andb (Qle_bool 0 lb) (negb (Qeq_bool lb 0)).

Lemma GaC2_17_cert_lb_pos1 : GaC2_17_lb_pos GaC2_17_lb_delta1 = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC2_17_cert_lb_pos2 : GaC2_17_lb_pos GaC2_17_lb_delta2 = true.
Proof. vm_compute; reflexivity. Qed.

(* ---- Band 4: the decidable band skeleton ---- *)

(* The (a) band membership skeleton: 0 <= sigma <= 1 - delta as the      *)
(* boolean pair.                                                         *)
Definition GaC2_17_sigma_band (sigma delta : Q) : bool :=
  andb (Qle_bool 0 sigma) (Qle_bool sigma (1 - delta)).

Lemma GaC2_17_cert_band_in : GaC2_17_sigma_band (1#2) (1#4) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC2_17_cert_band_out : GaC2_17_sigma_band (7#8) (1#4) = false.
Proof. vm_compute; reflexivity. Qed.
