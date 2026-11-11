(* ConstructiveWorld-Main - certificate face of the Phragmen-Lindelof
   indicator node. *)

(** * GaC2_14_PhragmenLindelof_cert: certificate face of node C2-14.

    Mission.  Certificate face of node C2-14: literal certificates for
    the decidable skeleton of the selector carriers and Q-level
    samples.  Bands: (1) the definitional unfold faces of [max_sq],
    [grow_bound], and [pl_selector_ok] (premise-generic, delta
    transparent); (2) the Q-level literal samples of the carrier
    sequences: the squared unit at (3,2), the rational maximum pick
    max(1,2) = 2 at index 7, the truncation algebra sample
    eps * (x^2 - y^2) = (1/4) * ((1/2)^2 - 3^2) = -35/16 at index 6,
    and the edge-factor corridor |exp_partial(3, 1/4) - 1| < 1;
    (3) the composite selector-sample list [zz_pl_selector_samples]
    (drafts_C2.md C2.14 REPL band), discharged by vm_compute.
    Honest scope: the Real-line inequalities live on the proof faces
    of [GaC2_14_PhragmenLindelof] with the GAPASUME consumer premise;
    these literals certify the decidable Q skeleton and the literal
    corridor, not the Real-line order facts, and the compile gate of
    both faces is deferred until the W-wave mothers land.

    Dependencies.  [GaC2_14_PhragmenLindelof] (the statement face);
      [S03_QExp] ([cauchy_real_exp], [real_abs]);
      [S07_RealSetoidExpLog] ([real_max]);
      [CxRealPairCore] ([Cx], [cRe], [cIm]); Stdlib [QArith], [List].

    References.  drafts_C2.md C2.14 certificate band (the selector
    samples at three target points times two accuracy tiers, the
    [zz_pl_selector_samples] REPL face); the certificate-face
    precedent [GaC3_P08_PerronCutoff_cert].

    Constructivity.  Set-sorted boolean and Q identities; zero
    assumed constants, zero abandoned proofs; the Q bands close with
    vm_compute, the unfold bands with definitional transparency, all
    under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_14_PhragmenLindelof_cert.v] from the
    flat build directory under the thermal-guard wrapper; compile
    deferred with the statement face. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import GaC2_14_PhragmenLindelof.

Local Open Scope Q_scope.
Import ListNotations.

(* ---- Band 1: the definitional unfold faces (premise-generic) ---- *)

Lemma pl_cert_max_sq_unfold :
  forall M0 M1 : Real,
    max_sq M0 M1 = real_max (sq M0) (sq M1).
Proof. intros M0 M1. reflexivity. Qed.

Lemma pl_cert_grow_bound_unfold :
  forall (A B : Real) (rho : Q) (y : Real),
    grow_bound A B rho y =
    real_mult (sq A)
      (cauchy_real_exp
         (real_mult (real_const (2#1))
            (real_mult B
               (r_pow rho (real_max (real_abs y) real_one)
                       (pl_cap_pos y))))).
Proof. intros A B rho y. reflexivity. Qed.

Lemma pl_cert_selector_unfold :
  forall (f : Cx -> Cx) (M0 M1 A B : Real) (rho : Q) (z : Cx) (eps T : Real),
    pl_selector_ok f M0 M1 A B rho z eps T =
    S01_BaseRing.And (real_lt (cIm z) T)
    (S01_BaseRing.And (real_lt (real_opp (cIm z)) T)
    (S01_BaseRing.And (real_lt real_zero eps)
    (S01_BaseRing.And (real_lt real_zero T)
         (real_le (grow_bound A B rho T) (max_sq M0 M1))))).
Proof. intros f M0 M1 A B rho z eps T. reflexivity. Qed.

(* ---- Band 2: the Q-level literal samples ---- *)

Lemma pl_cert_sq_sample :
  projT1 (sq  (real_const (3#2))) 5%nat == (9#4).
Proof. vm_compute. reflexivity. Qed.

Lemma pl_cert_max_sq_sample :
  projT1 (max_sq  (real_const (1#1))  (real_const (2#1))) 7%nat == (4#1).
Proof. vm_compute. reflexivity. Qed.

Lemma pl_cert_trunc_arg_sample :
  projT1 (real_mult (real_const (1#4))
                    (real_plus
                       (sq (cRe (real_const (1#2), real_const (3#1))))
                       (real_opp
                          (sq (cIm (real_const (1#2), real_const (3#1)))))))
          6%nat == ((-35)#16).
Proof. vm_compute. reflexivity. Qed.

Lemma pl_cert_edge_factor_sample :
  Qlt_bool (Qabs (projT1 (pl_edge_factor (real_const (1#4))) 3%nat
                     - projT1 real_one 3%nat))
            (1#1) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- Band 3: the composite selector-sample list ---- *)

Definition zz_pl_selector_samples : list bool :=
  (Qeq_bool
   (projT1 (max_sq (real_const (1#1)) (real_const (2#1))) 7%nat)
            (4#1))
  :: (Qeq_bool (projT1 (sq (real_const (3#2))) 5%nat) (9#4))
  :: (Qlt_bool (Qabs (projT1 (pl_edge_factor (real_const (1#4))) 3%nat
                         - projT1 real_one 3%nat))
                (1#1))
  :: nil.

Lemma zz_pl_selector_samples_true :
  zz_pl_selector_samples = true :: true :: true :: nil.
Proof. vm_compute. reflexivity. Qed.
