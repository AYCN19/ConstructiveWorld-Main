(** * GaC2_12_CauchyCoeffEst_d: the step-decomposition geometry kit.
    Mission.  Node C2-12 machine cluster, piece d.  Geometry and
      reciprocal faces for the iterated difference-quotient step
      machine (piece e): the geometry faces
      [gaC12_parallelogram]/[gaC12_opp_cnsq_le_zero]/
      [gaC12_sq_le_2sum] (carrying the pending premise [Hnn], see
      Notes), the reciprocal faces [gaC12_inv_mult]/[gaC12_sq_prod],
      the scaled-norm face [gaC12_norm_scale_inv] and the value face
      [gaC12_dquot_value_at].  Set-carried; zero Sections.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [CxRealPairCore], [CxRealPairExpLog],
      [GaC1_Iface_Cx], [GaC1_Iface_Real], [GaC2_11_MaxModulusDisk_a],
      [GaC2_11_MaxModulusDisk_b] (the [mm_*] algebra kit); pieces
      a, b, c of this cluster.

    References.  drafts_C2.md C2.12 card, general-n route
      (difference/annulus iteration recursion, C_n of 2^n shape,
      explicit constant loss).  Ahlfors Ch.2 the classical quotient
      iteration (statement architecture only; no proof object transcribed).

    Constructivity.  All statements are Set-sorted; the ring faces are
      coordinate-level polynomial identities ([real_eq_of_zero_diff] +
      [ring]); no Section wrappers, zero assumed constants, zero
      admitted goals; every proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_d.v] from the flat
      build directory. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_12_CauchyCoeffEst_a.
Require Import GaC2_12_CauchyCoeffEst_b.
Require Import GaC2_12_CauchyCoeffEst_c.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(** Notes.  Pending-premise disclosure: the two-sum square bound
    [gaC12_sq_le_2sum] carries the complex-norm nonnegativity face
    as an explicit premise [Hnn] (GAPASUME premise).  [Hnn] is the
    first output face of the pending Cx-norm geometry machine, the
    same registered pending machine whose reverse-triangle slot is
    carried by GaC2_11_MaxModulusDisk.v lines 22-28 (the [Hrevtri]
    interface premise); the premise shrinks monotonically when that
    machine lands.  Order faces in this piece propagate through
    monotone faces only.  Residency: [mm_mult_cancel_eq] and
    [mm_inv_mul_one] are resident in GaC2_11_MaxModulusDisk_a,
    [mm_norm_scale] is resident in GaC2_11_MaxModulusDisk_b.
    Deviation disclosure: the cluster contains no four-sum square
    bound statement [gaC12_sq_le_4sum]; the two-sum bound
    [gaC12_sq_le_2sum] is the only square bound cast in this piece. *)

(* ===================================================================== *)
(* Section 1. The complex parallelogram identity and the opposite        *)
(* bridge.                                                               *)
(* ===================================================================== *)

Lemma gaC12_parallelogram : forall x y : Cx,
  real_eq (real_plus (c_norm_sq (c_plus x y))
                     (c_norm_sq (c_plus x (c_opp y))))
          (real_mult (real_const 2) (real_plus (c_norm_sq x) (c_norm_sq y))).
Proof.
  intros [xr xi] [yr yi].
  destruct xr as [xrq xrqc]. destruct xi as [xiq xiqc].
  destruct yr as [yrq yrqc]. destruct yi as [yiq yiqc].
  apply real_eq_of_zero_diff; intro n;
    cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const
         c_plus c_opp c_mult c_norm_sq cRe cIm fst snd]; ring.
Qed.

Lemma gaC12_opp_cnsq_le_zero : forall (v : Cx)
    (Hnn : forall w : Cx, real_le real_zero (c_norm_sq w)),
  real_le (real_opp (c_norm_sq v)) real_zero.
Proof.
  intros v H.
  assert (Hoz : real_eq (real_opp real_zero) real_zero).
  { apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_opp real_zero]. ring. }
  destruct (H v) as [Hlt | Heq].
  - exact (real_lt_le_iff (real_opp (c_norm_sq v)) real_zero
             (inl (real_lt_zero_opp (c_norm_sq v) Hlt))).
  - apply RealSetoid.real_eq_le.
    exact (real_eq_trans (real_opp (c_norm_sq v)) (real_opp real_zero) real_zero
             (real_eq_sym _ _ (RealSetoid.real_eq_opp_compat real_zero (c_norm_sq v) Heq))
             Hoz).
Qed.

(* ===================================================================== *)
(* Section 2. The square bounds over the pending nonnegativity face.     *)
(* ===================================================================== *)

Lemma gaC12_sq_le_2sum : forall
    (Hnn : forall v : Cx, real_le real_zero (c_norm_sq v)) (x y : Cx),
  real_le (c_norm_sq (c_plus x y))
          (real_mult (real_const 2) (real_plus (c_norm_sq x) (c_norm_sq y))).
Proof.
  intros Hnn x y.
  assert (HnnD : real_le real_zero (c_norm_sq (c_plus x (c_opp y))))
    by exact (Hnn (c_plus x (c_opp y))).
  assert (Hpar : real_eq (real_plus (c_norm_sq (c_plus x y))
                                    (c_norm_sq (c_plus x (c_opp y))))
                   (real_mult (real_const 2)
                      (real_plus (c_norm_sq x) (c_norm_sq y)))).
  { apply real_eq_of_zero_diff. intro n.
    destruct x as [xr xi]; destruct y as [yr yi].
    destruct xr as [xrq xrqc0]; destruct xi as [xiq xiqc0].
    destruct yr as [yrq yrqc0]; destruct yi as [yiq yiqc0].
    cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const
         c_plus c_opp c_norm_sq cRe cIm fst snd]. ring. }
  assert (Hopp : real_le (real_opp (c_norm_sq (c_plus x (c_opp y)))) real_zero)
    by exact (gaC12_opp_cnsq_le_zero (c_plus x (c_opp y)) Hnn).
  assert (Hleg0 : real_le (c_norm_sq (c_plus x y))
                    (real_plus (c_norm_sq (c_plus x y)) real_zero)).
  { apply RealSetoid.real_eq_le.
    exact (real_eq_sym _ _ (real_plus_zero (c_norm_sq (c_plus x y)))). }
  assert (Hleg1 : real_le (real_plus (c_norm_sq (c_plus x y)) real_zero)
                    (real_plus (c_norm_sq (c_plus x y))
                               (c_norm_sq (c_plus x (c_opp y)))))
    by exact (real_le_plus_compat _ _ _ _ (real_le_refl (c_norm_sq (c_plus x y))) HnnD).
  assert (Hleg2 : real_le (real_plus (c_norm_sq (c_plus x y))
                                     (c_norm_sq (c_plus x (c_opp y))))
                     (real_mult (real_const 2)
                        (real_plus (c_norm_sq x) (c_norm_sq y))))
    by exact (RealSetoid.real_eq_le _ _ Hpar).
  exact (real_le_trans _ _ _ (real_le_trans _ _ _ Hleg0 Hleg1) Hleg2).
Qed.

(* ===================================================================== *)
(* Section 3. The real reciprocal and square product faces.              *)
(* ===================================================================== *)

Lemma gaC12_sq_prod : forall x y : Real,
  real_eq (real_mult (real_mult x y) (real_mult x y))
          (real_mult (real_mult x x) (real_mult y y)).
Proof.
  intros x y. apply real_eq_of_zero_diff. intro n.
  destruct x as [u Hu]; destruct y as [v Hv].
  cbn [projT1 real_mult]. ring.
Qed.

Lemma gaC12_inv_mult : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb))
          (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb)).
Proof.
  intros a b Ha Hb.
  assert (Hcancel : real_eq
                      (real_mult (real_inv_pos (real_mult a b)
                                   (real_mult_positive a b Ha Hb))
                              (real_mult a b))
                      (real_mult (real_mult (real_inv_pos a Ha)
                                  (real_inv_pos b Hb))
                                 (real_mult a b))).
  { apply (real_eq_trans
             (real_mult (real_inv_pos (real_mult a b)
                        (real_mult_positive a b Ha Hb)) (real_mult a b))
             real_one
             (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                        (real_mult a b))).
    - apply (real_eq_trans
               (real_mult (real_inv_pos (real_mult a b)
                          (real_mult_positive a b Ha Hb)) (real_mult a b))
               (real_mult (real_mult a b)
                  (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb)))).
      + exact (real_mult_comm (real_inv_pos (real_mult a b)
                  (real_mult_positive a b Ha Hb)) (real_mult a b)).
      + exact (real_inv_pos_correct (real_mult a b)
                 (real_mult_positive a b Ha Hb)).
    - apply (real_eq_trans real_one
               (real_mult (real_mult (real_inv_pos a Ha) a)
                  (real_mult (real_inv_pos b Hb) b))
               (real_mult (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
                  (real_mult a b))).
      + exact (RealSetoid.real_eq_mult_compat real_one real_one
                 (real_mult (real_inv_pos a Ha) a)
                 (real_mult (real_inv_pos b Hb) b)
                 (real_eq_sym _ _ (mm_inv_mul_one a Ha))
                 (real_eq_sym _ _ (mm_inv_mul_one b Hb))).
      + apply real_eq_of_zero_diff. intro n.
        destruct (real_inv_pos a Ha) as [ia Hia].
        destruct (real_inv_pos b Hb) as [ib Hib].
        destruct a as [ua Hua]; destruct b as [ub Hub].
        cbn [projT1 real_mult real_inv_pos]. ring. }
  exact (mm_mult_cancel_eq
           (real_inv_pos (real_mult a b) (real_mult_positive a b Ha Hb))
           (real_mult (real_inv_pos a Ha) (real_inv_pos b Hb))
           (real_mult a b) (real_mult_positive a b Ha Hb) Hcancel).
Qed.

(* ===================================================================== *)
(* Section 4. The scaled-norm face and the value-at face.                *)
(* ===================================================================== *)

Lemma gaC12_norm_scale_inv : forall (v : Cx) (s : Real)
    (Hs : real_lt real_zero s),
  real_eq (c_norm_sq (c_scale (real_inv_pos s Hs) v))
          (real_mult (real_inv_pos s Hs) (real_mult (real_inv_pos s Hs) (c_norm_sq v))).
Proof.
  intros v s Hs.
  apply (real_eq_trans
           (c_norm_sq (c_scale (real_inv_pos s Hs) v))
           (real_mult (real_mult (real_inv_pos s Hs) (real_inv_pos s Hs))
              (c_norm_sq v))).
  - exact (mm_norm_scale (real_inv_pos s Hs) v).
  - exact (real_eq_sym _ _
             (real_mult_assoc (real_inv_pos s Hs) (real_inv_pos s Hs)
                (c_norm_sq v))).
Qed.

Lemma gaC12_dquot_value_at : forall (f : Cx -> Cx) (z0 p : Cx)
    (Hq_p : real_lt real_zero (c_norm_sq (c_plus p (c_opp z0)))),
  c_eq (gaC12_cx_dquot f z0 p Hq_p)
       (c_mult (c_plus (f p) (c_opp (f z0)))
          (c_scale (real_inv_pos (c_norm_sq (c_plus p (c_opp z0))) Hq_p)
                   (c_conj (c_plus p (c_opp z0))))).
Proof.
  intros f z0 p Hq_p. apply c_eq_refl.
Qed.
