(** * GaC2_12_CauchyCoeffEst_g: the annulus ring-bound kit.
    Mission.  Node C2-12 glue piece g.  The parameterized ring-bound
      constant [gaC12_Bk] (Cn^2 k * (M/R^k)^2 in squared carrier, the
      target form of the stem statement cauchy_est_n) with two algebra
      faces: [gaC12_Bk_zero] (the zeroth ring equals the squared
      boundary bound M^2) and [gaC12_Bk1_eq] (the first ring equals
      (2M/R)^2 in the est_n1 consumption form).  Set-carried; zero
      Sections; zero admitted goals.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [CxRealPairCore], [CxRealPairExpLog],
      [GaC1_Iface_Cx], [GaC1_Iface_Real], [GaC2_11_MaxModulusDisk],
      [GaC2_11_MaxModulusDisk_a], [GaC2_11_MaxModulusDisk_b]; pieces
      a, c, d, f of this cluster.

    References.  drafts_C2.md C2.12 card (the annulus recursion with
      explicit constant loss; the stem cauchy_est_n1 consumption
      form).  Registered gap-carrier discipline: pure algebra faces
      over the [gaC12_rdiv]/[gaC12_Cn] constant kit.  Ahlfors Ch.2
      the classical coefficient bound (statement architecture only).

    Constructivity.  All statements are Set-sorted; no Section
      wrappers, zero assumed constants, zero admitted goals; every
      proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_g.v] from the flat
      build directory. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_12_CauchyCoeffEst_a.
Require Import GaC2_12_CauchyCoeffEst_c.
Require Import GaC2_12_CauchyCoeffEst_d.
Require Import GaC2_12_CauchyCoeffEst_f.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* The k-th ring bound in the target form of cauchy_est_n:
   Cn_k^2 * (M / R^k)^2, parameterized over the boundary pair. *)
Definition gaC12_Bk (M R : Real) (HR : real_lt real_zero R) (k : nat) : Real :=
  real_mult (gaC12_Cn_sq k)
    (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (gaC12_rnatpow_pos R k HR))).

Lemma gaC12_inv_one : real_eq (real_inv_pos real_one gaC12_real_one_pos)
                               real_one.
Proof.
  apply (real_eq_trans
           (real_inv_pos real_one gaC12_real_one_pos)
           (real_mult (real_inv_pos real_one gaC12_real_one_pos) real_one)
           real_one).
  - apply real_eq_sym. exact (real_mult_one
           (real_inv_pos real_one gaC12_real_one_pos)).
  - apply (real_eq_trans
             (real_mult (real_inv_pos real_one gaC12_real_one_pos) real_one)
             (real_mult real_one (real_inv_pos real_one gaC12_real_one_pos))
             real_one).
    + exact (real_eq_sym _ _ (real_mult_comm real_one
                 (real_inv_pos real_one gaC12_real_one_pos))).
    + exact (real_inv_pos_correct real_one gaC12_real_one_pos).
Qed.

Lemma gaC12_Bk_zero : forall (M R : Real) (HR : real_lt real_zero R),
  real_eq (gaC12_Bk M R HR 0%nat) (gaC12_sq M).
Proof.
  intros M R HR.
  unfold gaC12_Bk. cbn [gaC12_Cn_sq gaC12_Cn gaC12_rnatpow gaC12_rdiv].
  assert (Hinv1 : real_eq (real_inv_pos real_one (gaC12_rnatpow_pos R 0%nat HR))
                          real_one)
    by exact (real_eq_trans _ _ _ (gaC12_inv_wd real_one real_one
                (gaC12_rnatpow_pos R 0%nat HR) gaC12_real_one_pos
                (real_eq_refl real_one))
                gaC12_inv_one).
  assert (HY : real_eq (gaC12_sq (real_mult M (real_inv_pos real_one
                                   (gaC12_rnatpow_pos R 0%nat HR))))
                       (gaC12_sq (real_mult M real_one)))
    by exact (RealSetoid.real_eq_mult_compat_adapt
                (real_mult M (real_inv_pos real_one
                   (gaC12_rnatpow_pos R 0%nat HR)))
                (real_mult M real_one)
                (real_mult M (real_inv_pos real_one
                   (gaC12_rnatpow_pos R 0%nat HR)))
                (real_mult M real_one)
                (RealSetoid.real_eq_mult_compat_adapt M M
                   (real_inv_pos real_one (gaC12_rnatpow_pos R 0%nat HR))
                   real_one
                   (real_eq_refl M) Hinv1)
                (RealSetoid.real_eq_mult_compat_adapt M M
                   (real_inv_pos real_one (gaC12_rnatpow_pos R 0%nat HR))
                   real_one
                   (real_eq_refl M) Hinv1)).
  apply (real_eq_trans
           (real_mult (gaC12_sq real_one)
              (gaC12_sq (real_mult M (real_inv_pos real_one
                          (gaC12_rnatpow_pos R 0%nat HR)))))
           (gaC12_sq (real_mult M real_one)) (gaC12_sq M)).
  - exact (real_eq_trans _ _ _
              (RealSetoid.real_eq_mult_compat_adapt (gaC12_sq real_one) real_one
                 (gaC12_sq (real_mult M (real_inv_pos real_one
                              (gaC12_rnatpow_pos R 0%nat HR))))
                 (gaC12_sq (real_mult M real_one))
                 (real_mult_one real_one) HY)
              (real_eq_trans _ _ _
                 (real_mult_comm real_one (gaC12_sq (real_mult M real_one)))
                 (real_mult_one (gaC12_sq (real_mult M real_one))))).
  - exact (RealSetoid.real_eq_mult_compat_adapt (real_mult M real_one) M
              (real_mult M real_one) M
              (real_mult_one M) (real_mult_one M)).
Qed.

Lemma gaC12_Bk1_eq : forall (M R : Real) (HR : real_lt real_zero R),
  real_eq (gaC12_Bk M R HR 1%nat)
          (gaC12_sq (real_mult (real_const (2#1)%Q) (gaC12_rdiv M R HR))).
Proof.
  intros M R HR.
  unfold gaC12_Bk.
  apply (real_eq_trans
             (real_mult (gaC12_Cn_sq 1%nat)
                (gaC12_sq (gaC12_rdiv M
                   (gaC12_rnatpow R 1%nat) (gaC12_rnatpow_pos R 1%nat HR))))
             (real_mult (gaC12_Cn_sq 1%nat)
                (gaC12_sq (gaC12_rdiv M R HR)))
             (gaC12_sq (real_mult (real_const (2#1)%Q)
                          (gaC12_rdiv M R HR)))).
    * apply RealSetoid.real_eq_mult_compat_adapt.
      -- apply real_eq_refl.
      -- exact (RealSetoid.real_eq_mult_compat
             (gaC12_rdiv M (gaC12_rnatpow R 1%nat)
                (gaC12_rnatpow_pos R 1%nat HR))
             (gaC12_rdiv M (gaC12_rnatpow R 1%nat)
                (gaC12_rnatpow_pos R 1%nat HR))
             (gaC12_rdiv M R HR)
             (gaC12_rdiv M R HR)
             (RealSetoid.real_eq_mult_compat_adapt M M
                (real_inv_pos (gaC12_rnatpow R 1%nat)
                   (gaC12_rnatpow_pos R 1%nat HR))
                (real_inv_pos R HR)
                (real_eq_refl M)
                (gaC12_inv_wd (gaC12_rnatpow R 1%nat) R
                   (gaC12_rnatpow_pos R 1%nat HR) HR
                   (gaC12_rnatpow_one R)))
             (RealSetoid.real_eq_mult_compat_adapt M M
                (real_inv_pos (gaC12_rnatpow R 1%nat)
                   (gaC12_rnatpow_pos R 1%nat HR))
                (real_inv_pos R HR)
                (real_eq_refl M)
                (gaC12_inv_wd (gaC12_rnatpow R 1%nat) R
                   (gaC12_rnatpow_pos R 1%nat HR) HR
                   (gaC12_rnatpow_one R)))).
    * apply (real_eq_trans
                 (real_mult (gaC12_Cn_sq 1%nat)
                    (gaC12_sq (gaC12_rdiv M R HR)))
                 (real_mult (gaC12_sq (real_const (2#1)%Q))
                    (gaC12_sq (gaC12_rdiv M R HR)))
                 (gaC12_sq (real_mult (real_const (2#1)%Q)
                              (gaC12_rdiv M R HR)))).
      -- unfold gaC12_Cn_sq.
         apply RealSetoid.real_eq_mult_compat_adapt.
         ++ exact (real_eq_sym _ _ (gaC12_cert_cn1)).
         ++ apply real_eq_refl.
      -- exact (real_eq_sym _ _
                  (gaC12_sq_prod (real_const (2#1)%Q)
                     (gaC12_rdiv M R HR))).
Qed.
