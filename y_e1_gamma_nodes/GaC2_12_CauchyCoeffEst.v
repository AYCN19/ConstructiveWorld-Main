(* ConstructiveWorld-Main - the Cauchy coefficient estimate stem. *)
(** * GaC2_12_CauchyCoeffEst: the Cauchy coefficient estimate stem.

    Mission.  Node C2-12 (segment C2, slot W3), statement stem.  Two statements: [cauchy_est_n1], |f'(z0)|^2 <=
      (2M/R)^2 in squared carrier, and [cauchy_est_n], |a_n|^2 <= Cn^2 (M/R^n)^2 with the explicit constant
      [gaC12_Cn] of 2^n shape.  The coefficient carriers are the projectors [gaC12_deriv1]/[gaC12_nth_coeff] over
      the sequence carrier [gaC12_local_exp_seq] (the L14 same-source face; detailed in Notes).  Three
      gap-carrier premise slots ([Hnn]/[Hmod_gate]/[Hchain]) are carried explicitly - honest interface
      disclosure, all Set-carried, monotonically shrinkable; full statements in the Notes block after the
      first Require.  [cauchy_chain] builds the k-th quotient ring (the annulus iteration, circle bound
      [cauchy_Bk k] = Cn^2 (M/R^k)^2 by induction); both statements close through [Hmod_gate] at the ring center.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires [S01_BaseRing] (Require, not Import), [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC1_Iface_Real],
      [GaC2_11_MaxModulusDisk], [GaC2_11_MaxModulusDisk_b] (the [mm_*] kit faces [mm_norm_self_opp]/[mm_norm_wd]), and
      the machine cluster [GaC2_12_CauchyCoeffEst_a] through [GaC2_12_CauchyCoeffEst_g].

    References.  drafts_C2.md C2.12 statement sketch (cauchy_est_n1 and cauchy_est_n verbatim; obligation L16 the Cn
      closed form and the rpow R n carrier) and cards_C2.md C2.12 card (the difference-quotient route: g = (f -
      f(z0))/(z - z0) circle bound 2M/R pushed through the strict modulus gate; the general annulus recursion with
      explicit constant loss).  Ahlfors Ch.2 the classical Cauchy coefficient estimate (statement architecture
      only; no proof object transcribed).

    Constructivity.  Every named construction is carried by [Set]; the three gap-carrier premises are discharged as
      explicit arguments at the section close (gap-carrier form, monotonically shrinkable); zero assumed constants;
      every proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> "" -Q <build dir> "" GaC2_12_CauchyCoeffEst.v] from the flat build
      directory; acceptance via 50_toolkit/accept_node.py (six-chain gate), thermal-guard wrapped. *)

Require S01_BaseRing.

(** Notes.  Disclosure carried here to keep the header within budget.  (1) The three gap-carrier
    premise slots of the section: [Hnn] : forall v : Cx, real_le real_zero (c_norm_sq v) - the
    complex-norm nonnegativity face, the pending Cx-norm geometry machine, the same registered
    machine as the C2-11 Hrevtri slot and the GaC2_12_CauchyCoeffEst_d Hnn parameters.
    [Hmod_gate] : forall (g : Cx -> Cx) (B : Real), boundary_bounded g z0 R B ->
    real_le (c_norm_sq (g z0)) B - the strict maximum-modulus gate: a circle bound B on g gives
    the center value bound B at z0; the strict strengthening of the C2-11 delta-squared margin
    form.  [Hchain] : for an expandable g it yields the punctured-disk difference quotient g1
    with its own expansion, the punctured difference-quotient formula, and the full coefficient
    shift a_n(g1) = a_{S n}(g) - the power-series quotient re-expansion face registered as the
    C1.4 dependency of the C2-12 card; the vacuous step machine GaC2_12_CauchyCoeffEst_e is its
    registered placeholder.  (2) The L14 same-source face in detail: the C2-11 three-slot carrier
    is the truncation of the sequence carrier via [gaC12_slots_of_seq], and
    [cauchy_deriv1_align_c211] fixes the agreement of [gaC12_deriv1] with the C2-11 [deriv1]. *)
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_12_CauchyCoeffEst_a.
Require Import GaC2_12_CauchyCoeffEst_b.
Require Import GaC2_12_CauchyCoeffEst_c.
Require Import GaC2_12_CauchyCoeffEst_d.
Require Import GaC2_12_CauchyCoeffEst_e.
Require Import GaC2_12_CauchyCoeffEst_f.
Require Import GaC2_12_CauchyCoeffEst_g.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

Section CauchyCoeffEst.

Variable f : Cx -> Cx.
Variable z0 : Cx.
Variable R : Real.
Hypothesis HR : real_lt real_zero R.
Variable Hloc : gaC12_local_exp_seq f z0 R.
Variable M : Real.
Hypothesis HM : boundary_bounded f z0 R (gaC12_sq M).

(* Gap-carrier slot 1: the complex-norm nonnegativity face (the
   pending Cx-norm geometry machine; same registered machine as the
   GaC2_12_CauchyCoeffEst_d Hnn parameters). *)
Hypothesis Hnn : forall v : Cx, real_le real_zero (c_norm_sq v).

(* Gap-carrier slot 2: the strict maximum-modulus gate - a circle
   bound B on g gives the center value bound B at z0.  The strict
   strengthening of the C2-11 delta-squared margin form. *)
Hypothesis Hmod_gate : forall (g : Cx -> Cx) (B : Real),
  boundary_bounded g z0 R B -> real_le (c_norm_sq (g z0)) B.

(* Gap-carrier slot 3: the extended difference-quotient machine - the
   power-series quotient re-expansion face (the C1.4 dependency of
   the C2-12 card; the vacuous GaC2_12_CauchyCoeffEst_e step machine
   is its registered placeholder). *)
Definition cauchy_Hz0 : gaC12_closed_disk z0 z0 R :=
  real_le_trans (c_norm_sq (c_plus z0 (c_opp z0))) real_zero (real_mult R R)
    (RealSetoid.real_eq_le (c_norm_sq (c_plus z0 (c_opp z0))) real_zero
       (mm_norm_self_opp z0))
    (real_lt_le_iff real_zero (real_mult R R)
       (inl (real_mult_positive R R HR HR))).
Hypothesis Hchain : forall (g : Cx -> Cx)
                      (Hg : gaC12_local_exp_seq g z0 R),
  sigT (fun g1 : Cx -> Cx => sigT (fun Hg1 : gaC12_local_exp_seq g1 z0 R =>
    S01_BaseRing.And
      (forall (q : Cx)
         (Hq : real_lt real_zero (c_norm_sq (c_plus q (c_opp z0)))),
         c_eq (g1 q) (gaC12_cx_dquot g z0 q Hq))
      (forall (n : nat),
         c_eq (gaC12_nth_coeff n g1 z0 z0 R Hg1 cauchy_Hz0)
              (gaC12_nth_coeff (S n) g z0 z0 R Hg cauchy_Hz0)))).

(* ===================================================================== *)
(* Section 1. The standing data of the section.                          *)
(* ===================================================================== *)

Definition cauchy_Hz011 : closed_disk z0 z0 R :=
  real_le_trans (c_norm_sq (c_plus z0 (c_opp z0))) real_zero (real_mult R R)
    (RealSetoid.real_eq_le (c_norm_sq (c_plus z0 (c_opp z0))) real_zero
       (mm_norm_self_opp z0))
    (real_lt_le_iff real_zero (real_mult R R)
       (inl (real_mult_positive R R HR HR))).

Definition cauchy_HRsq : real_lt real_zero (gaC12_sq R) :=
  real_mult_positive R R HR HR.

Definition cauchy_HRk (k : nat) : real_lt real_zero (gaC12_rnatpow R k) :=
  gaC12_rnatpow_pos R k HR.

(* The k-th ring bound, stated directly in the target form of
   cauchy_est_n: Cn_k^2 * (M / R^k)^2. *)
Definition cauchy_Bk (k : nat) : Real := gaC12_Bk M R HR k.



Lemma cauchy_Bk_step : forall k : nat,
  real_eq (cauchy_Bk (S k))
          (real_mult (real_const 4)
             (real_mult (cauchy_Bk k)
                (real_inv_pos (gaC12_sq R) cauchy_HRsq))).
Proof.
  intro k.
  apply (real_eq_trans
           (cauchy_Bk (S k))
           (real_mult (gaC12_sq (gaC12_Cn (S k)))
              (gaC12_sq (real_mult
                 (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                 (real_inv_pos R HR))))
           (real_mult (real_const 4)
              (real_mult (cauchy_Bk k)
                 (real_inv_pos (gaC12_sq R) cauchy_HRsq)))).
  - unfold cauchy_Bk. cbn [gaC12_rnatpow].
    exact (RealSetoid.real_eq_mult_compat_adapt
              (gaC12_Cn_sq (S k)) (gaC12_sq (gaC12_Cn (S k)))
              (gaC12_sq (gaC12_rdiv M
                 (real_mult (gaC12_rnatpow R k) R)
                 (cauchy_HRk (S k))))
              (gaC12_sq (real_mult
                 (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                 (real_inv_pos R HR)))
              (real_eq_refl (gaC12_sq (gaC12_Cn (S k))))
              (RealSetoid.real_eq_mult_compat_adapt
                 (gaC12_rdiv M (real_mult (gaC12_rnatpow R k) R)
                    (cauchy_HRk (S k)))
                 (real_mult (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                    (real_inv_pos R HR))
                 (gaC12_rdiv M (real_mult (gaC12_rnatpow R k) R)
                    (cauchy_HRk (S k)))
                 (real_mult (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                    (real_inv_pos R HR))
                 (gaC12_rdiv_S k M R HR (cauchy_HRk k) (cauchy_HRk (S k)))
                 (gaC12_rdiv_S k M R HR (cauchy_HRk k) (cauchy_HRk (S k))))).
  - apply (real_eq_trans
             (real_mult (gaC12_sq (gaC12_Cn (S k)))
                (gaC12_sq (real_mult
                   (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                   (real_inv_pos R HR))))
             (real_mult (real_mult (real_const 4) (gaC12_sq (gaC12_Cn k)))
                (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                   (gaC12_sq (real_inv_pos R HR))))
             (real_mult (real_const 4)
                (real_mult (cauchy_Bk k)
                   (real_inv_pos (gaC12_sq R) cauchy_HRsq)))).
    + exact (RealSetoid.real_eq_mult_compat_adapt
                (gaC12_sq (gaC12_Cn (S k)))
                (real_mult (real_const 4) (gaC12_sq (gaC12_Cn k)))
                (gaC12_sq (real_mult
                   (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                   (real_inv_pos R HR)))
                (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                   (gaC12_sq (real_inv_pos R HR)))
                (gaC12_Cn_S_sq k)
                (gaC12_sq_prod (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))
                   (real_inv_pos R HR))).
    + apply (real_eq_trans
                 (real_mult (real_mult (real_const 4) (gaC12_sq (gaC12_Cn k)))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_mult (real_inv_pos R HR) (real_inv_pos R HR))))
                 (real_mult (real_const 4)
                    (real_mult (gaC12_sq (gaC12_Cn k))
                       (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                          (real_mult (real_inv_pos R HR) (real_inv_pos R HR)))))
                 (real_mult (real_const 4)
                    (real_mult (cauchy_Bk k)
                       (real_inv_pos (gaC12_sq R) cauchy_HRsq)))).
      * exact (real_eq_sym _ _ (real_mult_assoc (real_const 4) (gaC12_sq (gaC12_Cn k))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_mult (real_inv_pos R HR) (real_inv_pos R HR))))).
      * exact (real_eq_trans _ _ _
              (RealSetoid.real_eq_mult_compat_adapt (real_const 4) (real_const 4)
                 (real_mult (gaC12_sq (gaC12_Cn k))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_mult (real_inv_pos R HR) (real_inv_pos R HR))))
                 (real_mult (gaC12_sq (gaC12_Cn k))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_inv_pos (gaC12_sq R) cauchy_HRsq)))
                 (real_eq_refl (real_const 4))
                 (RealSetoid.real_eq_mult_compat_adapt
                    (gaC12_sq (gaC12_Cn k)) (gaC12_sq (gaC12_Cn k))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_mult (real_inv_pos R HR) (real_inv_pos R HR)))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_inv_pos (gaC12_sq R) cauchy_HRsq))
                    (real_eq_refl (gaC12_sq (gaC12_Cn k)))
                    (RealSetoid.real_eq_mult_compat_adapt
                       (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_mult (real_inv_pos R HR) (real_inv_pos R HR))
                       (real_inv_pos (gaC12_sq R) cauchy_HRsq)
                       (real_eq_refl (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))))
                       (gaC12_inv_sq R HR))))
              (RealSetoid.real_eq_mult_compat_adapt (real_const 4) (real_const 4)
                 (real_mult (gaC12_sq (gaC12_Cn k))
                    (real_mult (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                       (real_inv_pos (gaC12_sq R) cauchy_HRsq)))
                 (real_mult (real_mult (gaC12_sq (gaC12_Cn k))
                    (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k))))
                    (real_inv_pos (gaC12_sq R) cauchy_HRsq))
                 (real_eq_refl (real_const 4))
                 (real_mult_assoc (gaC12_sq (gaC12_Cn k))
                    (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R k) (cauchy_HRk k)))
                    (real_inv_pos (gaC12_sq R) cauchy_HRsq)))).

Qed.

(* ===================================================================== *)
(* Section 2. The annulus chain: the k-th quotient ring.                 *)
(* ===================================================================== *)

Lemma cauchy_chain : forall k : nat,
  sigT (fun gk : Cx -> Cx => sigT (fun Hgk : gaC12_local_exp_seq gk z0 R =>
    S01_BaseRing.And (boundary_bounded gk z0 R (cauchy_Bk k))
      (forall (n : nat),
         c_eq (gaC12_nth_coeff n gk z0 z0 R Hgk cauchy_Hz0)
              (gaC12_nth_coeff (n + k)%nat f z0 z0 R Hloc cauchy_Hz0)))).
Proof.
  intro k. induction k as [| k IH].
  - exists f. exists Hloc. split.
    + intro q. intro Hbq.
      apply (real_le_trans (c_norm_sq (f q)) (gaC12_sq M) (cauchy_Bk 0%nat)).
      * exact (HM q Hbq).
      * apply RealSetoid.real_eq_le.
        exact (real_eq_sym _ _ (gaC12_Bk_zero M R HR)).
    + intro n. rewrite <- plus_n_O. apply c_eq_refl.
  - destruct IH as [gk [Hgk [HBk Hshift]]].
    destruct (Hchain gk Hgk) as [g1 [Hg1 [Hdiff Hshift1]]].
    exists g1. exists Hg1. split.
    + intro q. intro Hbq.
      assert (HG0k : real_le (c_norm_sq (gk z0)) (cauchy_Bk k))
        by exact (Hmod_gate gk (cauchy_Bk k) HBk).
      pose proof (gaC12_step_circle_bound gk g1 z0 R (cauchy_Bk k)
                    HR Hnn HBk HG0k Hdiff) as Hstep.
      apply (real_le_trans (c_norm_sq (g1 q))
               (real_mult (real_const 4)
                  (real_mult (cauchy_Bk k)
                     (real_inv_pos (gaC12_sq R) cauchy_HRsq)))
               (cauchy_Bk (S k))).
      * exact (Hstep q Hbq).
      * apply RealSetoid.real_eq_le. exact (real_eq_sym _ _ (cauchy_Bk_step k)).
    + intro n.
      apply (c_eq_trans
                 (gaC12_nth_coeff n g1 z0 z0 R Hg1 cauchy_Hz0)
                 (gaC12_nth_coeff (S n) gk z0 z0 R Hgk cauchy_Hz0)
                 (gaC12_nth_coeff (n + S k)%nat f z0 z0 R Hloc cauchy_Hz0)).
      * exact (Hshift1 n).
      * rewrite <- (plus_n_Sm n k).
        exact (Hshift (S n)).
Qed.

(* ===================================================================== *)
(* Section 3. The two statements of the sketch roster.                   *)
(* ===================================================================== *)

Lemma cauchy_est_n : forall (n : nat), (1 <= n)%nat ->
  real_le (c_norm_sq (gaC12_nth_coeff n f z0 z0 R Hloc cauchy_Hz0))
          (real_mult (gaC12_Cn_sq n)
             (gaC12_sq (gaC12_rdiv M (gaC12_rnatpow R n) (cauchy_HRk n)))).
Proof.
  intros n Hn.
  destruct (cauchy_chain n) as [gn [Hgn [HBgn Hshift]]].
  assert (Ha0 : c_eq (gaC12_nth_coeff 0%nat gn z0 z0 R Hgn cauchy_Hz0)
                     (gaC12_nth_coeff n f z0 z0 R Hloc cauchy_Hz0))
    by exact (Hshift 0%nat).
  assert (Hval : c_eq (gaC12_nth_coeff 0%nat gn z0 z0 R Hgn cauchy_Hz0)
                      (gn z0))
    by exact (gaC12_nth_coeff_zero_value gn z0 z0 R Hgn cauchy_Hz0).
  apply (real_le_trans
           (c_norm_sq (gaC12_nth_coeff n f z0 z0 R Hloc cauchy_Hz0))
           (c_norm_sq (gn z0))
           (cauchy_Bk n)).
  - apply RealSetoid.real_eq_le.
    exact (mm_norm_wd (gaC12_nth_coeff n f z0 z0 R Hloc cauchy_Hz0) (gn z0)
             (c_eq_trans _ _ _ (c_eq_sym _ _ Ha0) Hval)).
  - exact (Hmod_gate gn (cauchy_Bk n) HBgn).
Qed.

Lemma cauchy_est_n1 :
  real_le (c_norm_sq (gaC12_deriv1 f z0 z0 R Hloc cauchy_Hz0))
          (gaC12_sq (real_mult (real_const (2#1)%Q)
                       (gaC12_rdiv M R HR))).
Proof.
  assert (Hbase : real_le (c_norm_sq (gaC12_deriv1 f z0 z0 R Hloc cauchy_Hz0))
                     (cauchy_Bk 1%nat))
    by exact (cauchy_est_n 1%nat (le_n 1%nat)).
  apply (real_le_trans
           (c_norm_sq (gaC12_deriv1 f z0 z0 R Hloc cauchy_Hz0))
           (cauchy_Bk 1%nat)
           (gaC12_sq (real_mult (real_const (2#1)%Q) (gaC12_rdiv M R HR)))).
  - exact Hbase.
  - apply RealSetoid.real_eq_le.
    exact (gaC12_Bk1_eq M R HR).
Qed.

(* ===================================================================== *)
(* Section 4. The L14 same-source alignment face.                        *)
(* ===================================================================== *)

Definition cauchy_Hslots11 : local_exp_disk f z0 R :=
  fun (p : Cx) (Hp : closed_disk p z0 R) =>
    gaC12_slots_of_seq f z0 R Hloc p Hp.

Lemma cauchy_deriv1_align_c211 :
  c_eq (gaC12_deriv1 f z0 z0 R Hloc cauchy_Hz0)
       (deriv1 f z0 z0 R cauchy_Hslots11 cauchy_Hz011).
Proof.
  change (gaC12_deriv1 f z0 z0 R Hloc cauchy_Hz0)
    with (gaC12_deriv1 f z0 z0 R Hloc cauchy_Hz011).
  unfold cauchy_Hslots11, deriv1, gaC12_deriv1, gaC12_nth_coeff,
    gaC12_slots_of_seq.
  cbv beta.
  destruct (Hloc z0 cauchy_Hz011) as [a [T2 [Ha0 [HT2 Hrem]]]].
  cbn [projT1 projT2].
  apply c_eq_refl.
Qed.

End CauchyCoeffEst.
