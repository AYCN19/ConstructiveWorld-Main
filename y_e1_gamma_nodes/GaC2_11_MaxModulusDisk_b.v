(* ConstructiveWorld-Main - the complex-norm algebra cluster of the
   maximum-modulus disk node. *)

(** * GaC2_11_MaxModulusDisk_b: complex-norm algebra.

    Mission.  Node C2-11 (segment C2, slot W2), machine piece.  The
      complex-norm algebra consumed by the maximum-modulus
      statements: the squared-norm faces of the scale, self-difference
      and conjugate-product forms ([mm_norm_scale],
      [mm_norm_self_opp], [mm_norm_wd], [mm_norm_conj_mul],
      [mm_re_conj_self], [mm_re_scale]), the pointwise cancellation
      face ([mm_norm_plus_cancel]), the squared-modulus embedding
      ([mm_sq_embed]), and the scaled-addition algebra
      ([mm_c_mult_scale], [mm_c_scale_scale], [mm_c_scale_one_mult],
      [mm_c_eq_scale_wd], [mm_c_scale_wd]).  All identities are
      pointwise rational-algebra routes on the pair carrier.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import), [S02_CauchyComplete]
      (order kit, [real_eq_of_zero_diff] ring route, ring laws),
      [S03_QExp] ([real_inv_pos] and its faces), [S07_RealSetoidExpLog]
      ([real_mult_positive], [RealSetoid.real_eq_mult_compat]),
      [CxRealPairCore] + [CxRealPairExpLog] (pair carrier,
      [c_scale]), [GaC1_Iface_Cx] (complex slice), [GaC1_Iface_Real]
      (C1-04 rational bridge, C1-05 square root faces) of this
      development.

    References.  drafts_C2.md C2.11 statement sketch (the squared
      modulus carrier and the explicit first-order increment
      algebra); Ahlfors Ch.2 the first-order growth direction
      argument mirrored at the squared-carrier level.

    Constructivity.  Every named construction is carried by [Set];
      the order predicates are the Set-sorted [real_lt] /
      [real_le]; zero assumed constants; every proof closes under
      the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_11_MaxModulusDisk_b.v] from the flat
      build directory, thermal guard wrapper. *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

Lemma mm_norm_scale : forall (t : Real) (z : Cx),
  real_eq (c_norm_sq (c_scale t z)) (real_mult (real_mult t t) (c_norm_sq z)).
Proof.
  intros t [p q]. destruct t as [ra Ha].
  destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_scale cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma mm_norm_self_opp : forall z : Cx,
  real_eq (c_norm_sq (c_plus z (c_opp z))) real_zero.
Proof.
  intros [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero
       c_plus c_opp cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma mm_norm_wd : forall z w : Cx,
  c_eq z w -> real_eq (c_norm_sq z) (c_norm_sq w).
Proof.
  intros z w Hz. unfold c_eq in Hz. destruct Hz as [Hr Hi].
  apply (real_eq_trans (c_norm_sq z)
           (real_plus (real_mult (cRe z) (cRe z)) (real_mult (cIm z) (cIm z)))
           (c_norm_sq w)).
  - apply real_eq_refl.
  - apply (real_eq_trans _
           (real_plus (real_mult (cRe w) (cRe w)) (real_mult (cIm w) (cIm w)))).
    + apply RealSetoid.real_eq_plus_compat.
      * apply RealSetoid.real_eq_mult_compat. exact Hr. exact Hr.
      * apply RealSetoid.real_eq_mult_compat. exact Hi. exact Hi.
    + apply real_eq_refl.
Qed.

Lemma mm_norm_plus_cancel : forall (X Y : Cx),
  c_eq (c_plus X (c_plus Y (c_opp X))) Y.
Proof.
  intros [a b] [p q].
  destruct a as [ua Ha]. destruct b as [ub Hb].
  destruct p as [uc Hc]. destruct q as [ud Hd].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_opp real_zero
         c_plus c_opp cRe cIm fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_opp real_zero
         c_plus c_opp cRe cIm fst snd]. ring.
Qed.

Lemma mm_sq_embed : forall z : Cx,
  c_eq (c_mult z (c_conj z)) (c_scale (c_norm_sq z) c_one).
Proof.
  intros [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_mult c_conj c_scale c_one cRe cIm c_norm_sq fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_mult c_conj c_scale c_one cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma mm_re_conj_self : forall z : Cx,
  real_eq (cRe (c_mult (c_conj z) z)) (c_norm_sq z).
Proof.
  intros [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_mult c_conj cRe cIm c_norm_sq fst snd]. ring.
Qed.

Lemma mm_c_mult_scale : forall (z : Cx) (t : Real) (u : Cx),
  c_eq (c_mult z (c_scale t u)) (c_scale t (c_mult z u)).
Proof.
  intros [a b] t [p q].
  destruct a as [ua Ha]. destruct b as [ub Hb].
  destruct t as [ra Ha2]. destruct p as [uc Hc]. destruct q as [ud Hd].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero
         c_mult c_scale cRe cIm fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero
         c_mult c_scale cRe cIm fst snd]. ring.
Qed.

Lemma mm_c_scale_scale : forall (t s : Real) (z : Cx),
  c_eq (c_scale t (c_scale s z)) (c_scale (real_mult t s) z).
Proof.
  intros t s [p q].
  destruct t as [ra Ha]. destruct s as [ra2 Ha2].
  destruct p as [u Hu]. destruct q as [v Hv].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero
         c_scale cRe cIm fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero
         c_scale cRe cIm fst snd]. ring.
Qed.

Lemma mm_c_scale_one_mult : forall (t : Real) (z : Cx),
  c_eq (c_mult (c_scale t c_one) z) (c_scale t z).
Proof.
  intros t [p q].
  destruct t as [ra Ha]. destruct p as [u Hu]. destruct q as [v Hv].
  unfold c_eq. split.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_scale c_one c_mult cRe cIm fst snd]. ring.
  - apply real_eq_of_zero_diff. intro n.
    cbn [projT1 real_plus real_mult real_opp real_zero real_one
         c_scale c_one c_mult cRe cIm fst snd]. ring.
Qed.

Lemma mm_c_eq_scale_wd : forall (t s : Real) (z : Cx),
  real_eq t s -> c_eq (c_scale t z) (c_scale s z).
Proof.
  intros t s z Hts. unfold c_eq. split.
  - apply RealSetoid.real_eq_mult_compat.
    * exact Hts.
    * apply real_eq_refl.
  - apply RealSetoid.real_eq_mult_compat.
    * exact Hts.
    * apply real_eq_refl.
Qed.

Lemma mm_c_scale_wd : forall (t : Real) (z w : Cx),
  c_eq z w -> c_eq (c_scale t z) (c_scale t w).
Proof.
  intros t z w H. unfold c_eq in H. destruct H as [Hr Hi].
  unfold c_eq. split.
  - apply RealSetoid.real_eq_mult_compat.
    ++ apply real_eq_refl.
    ++ exact Hr.
  - apply RealSetoid.real_eq_mult_compat.
    ++ apply real_eq_refl.
    ++ exact Hi.
Qed.

Lemma mm_re_scale : forall (t : Real) (z : Cx),
  real_eq (cRe (c_scale t z)) (real_mult t (cRe z)).
Proof.
  intros t [p q]. destruct t as [ra Ha].
  destruct p as [u Hu]. destruct q as [v Hv].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_opp real_zero real_one
       c_scale cRe cIm fst snd]. ring.
Qed.

Lemma mm_norm_conj_mul : forall z w : Cx,
  real_eq (c_norm_sq (c_mult (c_conj z) w))
          (real_mult (c_norm_sq z) (c_norm_sq w)).
Proof.
  intros z w.
  apply (real_eq_trans (c_norm_sq (c_mult (c_conj z) w))
           (real_mult (c_norm_sq (c_conj z)) (c_norm_sq w))).
  - exact (c_norm_sq_mul (c_conj z) w).
  - apply RealSetoid.real_eq_mult_compat.
    + exact (c_norm_sq_conj z).
    + apply real_eq_refl.
Qed.
