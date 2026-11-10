(* ConstructiveWorld-Main - certificate face of the Perron cutoff node.    *)

(** * GaC3_P08_PerronCutoff_cert: certificate face of node C3-P08.

    Mission.  Certificate face of node C3-P08: literal certificates for
    the decidable skeleton of the Perron cutoff face and Q-level ML
    samples.  Bands: (1) the two-case log-distance branch selections of
    [GaC3_P08_ln_dist] at x = 12, n = 7 (then branch) and x = 3, n = 9
    (else branch); (2) the truncated weight sum skeleton
    [GaC3_P08_perron_sum] at N = 2 and the half-weight carrier
    [GaC3_P08_psi_half] at k = 5 (premise-generic over the Real-line
    premises, the fold witnesses the canonical [NatLe_one_S] forms);
    (3) the Q-level ML samples of [GaC3_P08_vline_ml] at c = 3, T = 8,
    value (2,1), B = 4 (both components: -16 and 32 against the
    corridor B * 2T = 64), discharged by vm_compute.  Honest scope: the
    Real-line bounds live on the proof faces with the GAPASUME premise
    family; these literals certify the decidable skeleton and the
    rational ML corridor, not the Real-line inequalities.  The Q band
    closes with vm_compute (the R2 word-face lives here by design), the
    skeleton bands with bounded cbn reduction since Real-term internals
    are not Q-computable.

    Dependencies.  [GaC3_P08_PerronCutoff] (leaf a),
    [GaC3_P08_PerronCutoff_b] (leaf b), [S01_BaseRing] (selective
    [NatLe]), [S02_CauchyComplete], [S07_RealSetoidExpLog],
    [GaC2_Iface_DS] ([NatLe_one_S] via [GaC2_01_DirichletPartialSum]),
    [GaC3_P02_LineIntegralAlg], [GaC3_P03_MLEstimate],
    [GaC3_Z01_LogDerivSeries] ([z01_mansum], [z01_lam]); Stdlib
    [QArith], [List].

    References.  drafts_C3.md C3-P08 card (certificate band, the
    min-form and harmonic-form two-form registration); AFP
    Perrons_Formula perron_bound :1019-1020; tree precedents
    [GaC3_P03_MLEstimate_cert] (Q-level vm_compute band) and
    [GaC3_Z01_LogDerivSeries_cert] (premise-generic literal band).

    Constructivity.  Set-sorted boolean and Q identities; zero assumed
    constants, zero abandoned proofs; the Q band closes with vm_compute
    and the skeleton bands with bounded cbn reduction, all under the
    global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_P08_PerronCutoff_cert.v] compiles cleanly (exit 0) from the
    work directory (sandbox pair), single compile lane under the
    cpu_guard v3 wrapper. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import GaC2_Iface_DS.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P03_MLEstimate.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_P08_PerronCutoff.
Require Import GaC3_P08_PerronCutoff_b.

Local Open Scope Q_scope.
Import ListNotations.

(* ---- Band 1: the log-distance branch selections ---- *)

Lemma GaC3_P08_cert_ln_dist_then :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (Hx : NatLe 1 12) (Hn : NatLe 1 7),
    real_eq (GaC3_P08_ln_dist Hnpos 12 Hx 7 Hn)
            (real_plus (GaC3_P08_lnR Hnpos 12 Hx)
                       (real_opp (GaC3_P08_lnR Hnpos 7 Hn))).
Proof.
  intros Hnpos Hx Hn.
  assert (Hb : Nat.leb 7 12 = true) by reflexivity.
  unfold GaC3_P08_ln_dist. rewrite Hb. apply real_eq_refl.
Qed.

Lemma GaC3_P08_cert_ln_dist_else :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (Hx : NatLe 1 3) (Hn : NatLe 1 9),
    real_eq (GaC3_P08_ln_dist Hnpos 3 Hx 9 Hn)
            (real_plus (GaC3_P08_lnR Hnpos 9 Hn)
                       (real_opp (GaC3_P08_lnR Hnpos 3 Hx))).
Proof.
  intros Hnpos Hx Hn.
  assert (Hb : Nat.leb 9 3 = false) by reflexivity.
  unfold GaC3_P08_ln_dist. rewrite Hb. apply real_eq_refl.
Qed.

(* ---- Band 2: the fold and endpoint skeletons (premise-generic) ---- *)

Lemma GaC3_P08_cert_perron_sum_unfold :
  forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
         (xk : nat) (Hxk1 : NatLe 1 xk) (c T : Real)
         (HT0 : real_lt real_zero T),
    real_eq (GaC3_P08_perron_sum Hnpos xk Hxk1 c T HT0 2)
            (real_plus
               (real_plus real_zero
                          (GaC3_P08_pw Hnpos xk Hxk1 c T HT0 1 (NatLe_one_S 0)))
               (GaC3_P08_pw Hnpos xk Hxk1 c T HT0 2 (NatLe_one_S 1))).
Proof.
  intros Hnpos xk Hxk1 c T HT0.
  cbn [GaC3_P08_perron_sum]. apply real_eq_refl.
Qed.

Lemma GaC3_P08_cert_psi_half_unfold :
  forall (h : Real) (Hk : NatLe 1 5),
    real_eq (GaC3_P08_psi_half h 5 Hk)
            (real_plus (z01_mansum 4) (real_mult h (z01_lam 5))).
Proof.
  intros h Hk. cbn [GaC3_P08_psi_half Nat.pred]. apply real_eq_refl.
Qed.

(* ---- Band 3: the Q-level ML corridor samples ---- *)

Lemma GaC3_P08_cert_ml_vline_sample :
  Qle_bool (Qabs (GaC3_P02_path_sumR (GaC3_P02_vline_seg 3 8) [(2, 1)]))
           (4 * (2 * 8)) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma GaC3_P08_cert_ml_vline_sampleI :
  Qle_bool (Qabs (GaC3_P02_path_sumI (GaC3_P02_vline_seg 3 8) [(2, 1)]))
           (4 * (2 * 8)) = true.
Proof. vm_compute; reflexivity. Qed.
