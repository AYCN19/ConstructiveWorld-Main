(* ConstructiveWorld-Main - the radius and remainder kernel faces
   of the maximum-modulus disk node. *)

(** * GaC2_11_MaxModulusDisk_d: radius and remainder kernels.

    Mission.  Node C2-11 (segment C2, slot W2), machine piece.  The
      radius and remainder kernel faces consumed by the growth
      statement: the half-sum identity ([mm_half_plus]), the
      expanded-square transport ([mm_sq_expand]), the radius faces
      ([mm_rho_faces]: positivity, the quarter cap, the half cap),
      the unit-direction normalization ([mm_w_norm_faces]: the
      squared norm of the conjugate-aligned direction and of its
      radius-scaled copy), the alignment face ([mm_align_face]),
      the remainder cap ([mm_rem_cap]), and the disk-membership face
      of the scaled direction ([mm_w_in_disk]).  Every kernel takes
      its data as explicit arguments, so the pointwise
      rational-algebra routes proceed on freshly introduced
      components only.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import), [S02_CauchyComplete]
      (order kit, [real_eq_of_zero_diff] ring route, ring laws),
      [S03_QExp] ([real_inv_pos] and its faces), [S07_RealSetoidExpLog]
      ([real_mult_positive], [real_lt_mult_compat],
      [RealSetoid.real_eq_mult_compat], [real_lt_le_iff]),
      [CxRealPairCore] + [CxRealPairExpLog] (pair carrier,
      [c_scale]), [GaC1_Iface_Cx] (complex slice), [GaC1_Iface_Real]
      (C1-04 rational bridge, C1-05 square root faces), and the
      machine clusters [GaC2_11_MaxModulusDisk_a],
      [GaC2_11_MaxModulusDisk_b], [GaC2_11_MaxModulusDisk_c] of this
      node.

    References.  drafts_C2.md C2.11 statement sketch (the adaptive
      radius and the first-order gain direction); Ahlfors Ch.2 the
      first-order growth direction argument mirrored at the
      squared-carrier level.

    Constructivity.  Every named construction is carried by [Set];
      the order predicates are the Set-sorted [real_lt] /
      [real_le]; zero assumed constants; every proof closes under
      the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_11_MaxModulusDisk_d.v] from the flat
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
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_11_MaxModulusDisk_c.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* The half-sum: (1/2)t + (1/2)t == t. *)
Lemma mm_half_plus : forall t : Real,
  real_eq (real_plus (real_mult (real_const (1#2)%Q) t)
                     (real_mult (real_const (1#2)%Q) t)) t.
Proof.
  intro t. apply real_eq_of_zero_diff. intro n.
  destruct t as [u Hu].
  cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const]. ring.
Qed.

(* The adaptive-theta kit: with th = tau*e and ivt the reciprocal of
   1 + th, all five comparison faces used by the radius route. *)

(* The expanded square against m0: (a+b)^2 == m0 + 2ab + b^2 when
   a*a == m0. *)
Lemma mm_sq_expand : forall (a b m0 : Real)
    (Ha0 : real_eq (real_mult a a) m0),
  real_eq (real_mult (real_plus a b) (real_plus a b))
          (real_plus m0
             (real_plus (real_mult (real_const (2#1)%Q) (real_mult a b))
                        (real_mult b b))).
Proof.
  intros a b m0 Ha0.
  apply (real_eq_trans (real_mult (real_plus a b) (real_plus a b))
           (real_plus (real_mult a a)
              (real_plus (real_mult (real_const (2#1)%Q) (real_mult a b))
                         (real_mult b b)))
           (real_plus m0
              (real_plus (real_mult (real_const (2#1)%Q) (real_mult a b))
                         (real_mult b b)))).
  - exact (mm_sq_plus a b).
  - apply RealSetoid.real_eq_plus_compat.
    + exact Ha0.
    + apply real_eq_refl.
Qed.

(* The radius faces: r = r4*(th*ivt) is positive, bounded by r4,
   and r4 < r2 <= hold with r4 = R/4, r2 = R/2 and R > 0. *)
Lemma mm_rho_faces : forall (R r4 r2 th ivt r : Real)
                       (HR : real_lt real_zero R)
                       (Hr4p : real_lt real_zero r4)
                       (Htu : real_lt (real_mult th ivt) real_one)
                       (Hthp : real_lt real_zero th)
                       (Hivtp : real_lt real_zero ivt)
                       (Hr4E : real_eq r4 (real_mult (real_const (1#4)%Q) R))
                       (Hr2E : real_eq r2 (real_mult (real_const (1#2)%Q) R))
                       (HrE : real_eq r (real_mult r4 (real_mult th ivt))),
  S01_BaseRing.And (real_lt real_zero r)
    (S01_BaseRing.And (real_lt r r4)
      (S01_BaseRing.And (real_lt r4 r2) (real_le r r2))).
Proof.
  intros R r4 r2 th ivt r HR Hr4p Htu Hthp Hivtp Hr4E Hr2E HrE.
  assert (Hr : real_lt real_zero r).
  { exact (real_lt_eq_lt real_zero (real_mult r4 (real_mult th ivt)) r
             (real_mult_positive r4 (real_mult th ivt) Hr4p
                (real_mult_positive th ivt Hthp Hivtp)) (real_eq_sym _ _ HrE)). }
  assert (Hrlt4 : real_lt r r4).
  { apply (real_eq_lt_lt r (real_mult r4 (real_mult th ivt)) r4).
    - exact HrE.
    - exact (real_lt_eq_lt (real_mult r4 (real_mult th ivt)) (real_mult r4 real_one) r4
               (real_lt_mult_compat (real_mult th ivt) real_one r4 Hr4p Htu)
               (real_mult_one r4)). }
  assert (Hq42 : QltT (1#4)%Q (1#2)%Q) by reflexivity.
  assert (Hr4ltr2 : real_lt r4 r2).
  { apply (real_eq_lt_lt r4 (real_mult R (real_const (1#4)%Q)) r2).
    - exact (real_eq_trans r4 (real_mult (real_const (1#4)%Q) R)
               (real_mult R (real_const (1#4)%Q)) Hr4E
               (real_mult_comm (real_const (1#4)%Q) R)).
    - apply (real_lt_eq_lt (real_mult R (real_const (1#4)%Q))
               (real_mult R (real_const (1#2)%Q)) r2).
      + exact (real_lt_mult_compat (real_const (1#4)%Q) (real_const (1#2)%Q) R HR
                   (gaC1_04_qlt_const_lt (1#4)%Q (1#2)%Q Hq42)).
      + exact (real_eq_trans (real_mult R (real_const (1#2)%Q))
                 (real_mult (real_const (1#2)%Q) R)
                 r2 (real_mult_comm R (real_const (1#2)%Q))
                 (real_eq_sym _ _ Hr2E)). }
  exact (pair Hr (pair Hrlt4 (pair Hr4ltr2
           (real_lt_le_iff r r2 (inl (real_lt_trans r r4 r2 Hrlt4 Hr4ltr2)))))).
Qed.

(* The unit-direction faces: ud carries the conjugate-product
   alignment; its squared norm is one, and the radius-scaled copy
   t*ud has squared norm t*t. *)
Lemma mm_w_norm_faces : forall (z w : Cx) (t s0 s1 m0 m1 : Real)
    (Hss : real_lt real_zero (real_mult s0 s1))
    (Hsq0 : real_eq (real_mult s0 s0) m0)
    (Hsq1 : real_eq (real_mult s1 s1) m1)
    (Hm0 : real_eq m0 (c_norm_sq w))
    (Hm1 : real_eq m1 (c_norm_sq z)),
  S01_BaseRing.And
    (real_eq (c_norm_sq (c_scale (real_inv_pos (real_mult s0 s1) Hss)
                             (c_mult (c_conj z) w))) real_one)
    (real_eq (c_norm_sq (c_scale t (c_scale (real_inv_pos (real_mult s0 s1) Hss)
                             (c_mult (c_conj z) w)))) (real_mult t t)).
Proof.
  intros z w t s0 s1 m0 m1 Hss Hsq0 Hsq1 Hm0 Hm1.
  set (iv := real_inv_pos (real_mult s0 s1) Hss).
  set (ud := c_scale iv (c_mult (c_conj z) w)).
  assert (Hncm : real_eq (c_norm_sq (c_mult (c_conj z) w)) (real_mult m1 m0)).
  { apply (real_eq_trans (c_norm_sq (c_mult (c_conj z) w))
             (real_mult (c_norm_sq z) (c_norm_sq w)) (real_mult m1 m0)).
    - exact (mm_norm_conj_mul z w).
    - apply RealSetoid.real_eq_mult_compat.
      + exact (real_eq_sym _ _ Hm1).
      + exact (real_eq_sym _ _ Hm0). }
  assert (HB2 : real_eq (real_mult m1 m0)
                   (real_mult (real_mult s0 s1) (real_mult s0 s1))).
  { apply (real_eq_trans (real_mult m1 m0)
             (real_mult (real_mult s1 s1) (real_mult s0 s0))
             (real_mult (real_mult s0 s1) (real_mult s0 s1))).
    - apply RealSetoid.real_eq_mult_compat.
      + exact (real_eq_sym _ _ Hsq1).
      + exact (real_eq_sym _ _ Hsq0).
    - apply (real_eq_trans (real_mult (real_mult s1 s1) (real_mult s0 s0))
               (real_mult (real_mult s0 s0) (real_mult s1 s1))
               (real_mult (real_mult s0 s1) (real_mult s0 s1))).
      + exact (real_mult_comm (real_mult s1 s1) (real_mult s0 s0)).
      + exact (mm_ABAB s0 s1). }
  assert (Hudone : real_eq (c_norm_sq ud) real_one).
  { apply (real_eq_trans (c_norm_sq ud)
             (real_mult (real_mult iv iv) (c_norm_sq (c_mult (c_conj z) w))) real_one).
    - exact (mm_norm_scale iv (c_mult (c_conj z) w)).
    - apply (real_eq_trans
               (real_mult (real_mult iv iv) (c_norm_sq (c_mult (c_conj z) w)))
               (real_mult (real_mult iv iv)
                  (real_mult (real_mult s0 s1) (real_mult s0 s1)))
               real_one).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact (real_eq_trans (c_norm_sq (c_mult (c_conj z) w))
                   (real_mult m1 m0)
                   (real_mult (real_mult s0 s1) (real_mult s0 s1)) Hncm HB2).
      + apply (real_eq_trans
                 (real_mult (real_mult iv iv)
                    (real_mult (real_mult s0 s1) (real_mult s0 s1)))
                 (real_mult (real_mult iv (real_mult s0 s1))
                    (real_mult iv (real_mult s0 s1)))
                 real_one).
        * exact (mm_ABAB iv (real_mult s0 s1)).
        * apply (real_eq_trans
                   (real_mult (real_mult iv (real_mult s0 s1))
                      (real_mult iv (real_mult s0 s1)))
                   (real_mult real_one real_one) real_one).
          -- apply RealSetoid.real_eq_mult_compat.
             ++ exact (mm_inv_mul_one (real_mult s0 s1) Hss).
             ++ exact (mm_inv_mul_one (real_mult s0 s1) Hss).
          -- apply real_eq_of_zero_diff. intro n.
             cbn [projT1 real_plus real_mult real_opp real_zero real_one]. ring. }
  assert (Hwnorm : real_eq (c_norm_sq (c_scale t ud)) (real_mult t t)).
  { apply (real_eq_trans (c_norm_sq (c_scale t ud))
             (real_mult (real_mult t t) (c_norm_sq ud)) (real_mult t t)).
    - exact (mm_norm_scale t ud).
    - apply (real_eq_trans (real_mult (real_mult t t) (c_norm_sq ud))
               (real_mult (real_mult t t) real_one) (real_mult t t)).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact Hudone.
      + assert (Hsq1t : real_eq (real_mult (real_mult t t) real_one)
                           (real_mult t t)).
        { apply real_eq_of_zero_diff. intro n.
          destruct t as [tq Htq].
          cbn [projT1 real_plus real_mult real_opp real_zero real_one]. ring. }
        exact Hsq1t. }
  exact (pair Hudone Hwnorm).
Qed.

(* The alignment face: the conjugate-aligned increment collapses to
   the real gain applied to the base value. *)
Lemma mm_align_face : forall (z u : Cx) (t s m1 : Real)
    (Hm1z : real_eq m1 (c_norm_sq z)),
  c_eq (c_mult z (c_scale t (c_scale s (c_mult (c_conj z) u))))
       (c_scale (real_mult t (real_mult s m1)) u).
Proof.
  intros z u t s m1 Hm1z.
  apply (c_eq_trans (c_mult z (c_scale t (c_scale s (c_mult (c_conj z) u))))
           (c_scale (real_mult t (real_mult s (c_norm_sq z))) u)
           (c_scale (real_mult t (real_mult s m1)) u)).
  - exact (mm_align_kappa z u t s).
  - apply mm_c_eq_scale_wd.
    apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact (real_eq_sym _ _ Hm1z).
Qed.
(* The remainder cap: |delta|^2 <= (|w|^2*|w|^2)*T transports to
   the square of r*r*sq when |w|^2 == r*r and sq*sq == T. *)
Lemma mm_rem_cap : forall (delta w : Cx) (T r sq : Real)
    (Hwnorm : real_eq (c_norm_sq w) (real_mult r r))
    (Hrem : real_le (c_norm_sq delta)
               (real_mult (real_mult (c_norm_sq w) (c_norm_sq w)) T))
    (HsqT : real_eq (real_mult sq sq) T),
  real_le (c_norm_sq delta)
          (real_mult (real_mult (real_mult r r) sq)
                     (real_mult (real_mult r r) sq)).
Proof.
  intros delta w T r sq Hwnorm Hrem HsqT.
  apply (mm_le_eq_r (c_norm_sq delta)
           (real_mult (real_mult (c_norm_sq w) (c_norm_sq w)) T)
           (real_mult (real_mult (real_mult r r) sq)
                      (real_mult (real_mult r r) sq)) Hrem).
  apply (real_eq_trans (real_mult (real_mult (c_norm_sq w) (c_norm_sq w)) T)
           (real_mult (real_mult (real_mult r r) (real_mult r r)) T)
           (real_mult (real_mult (real_mult r r) sq)
                      (real_mult (real_mult r r) sq))).
  - apply RealSetoid.real_eq_mult_compat.
    + apply RealSetoid.real_eq_mult_compat.
      * exact Hwnorm.
      * exact Hwnorm.
    + apply real_eq_refl.
  - apply (real_eq_trans (real_mult (real_mult (real_mult r r) (real_mult r r)) T)
             (real_mult (real_mult (real_mult r r) (real_mult r r)) (real_mult sq sq))
             (real_mult (real_mult (real_mult r r) sq)
                        (real_mult (real_mult r r) sq))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact (real_eq_sym _ _ HsqT).
    + exact (mm_ABAB (real_mult r r) sq).
Qed.

(* The scaled direction stays inside the disk: wn = r*r with
   r < r2 = R/2 gives wn < R*R. *)
Lemma mm_w_in_disk : forall (wn r r2 R : Real)
                       (HR : real_lt real_zero R)
                       (Hr2E : real_eq r2 (real_mult (real_const (1#2)%Q) R))
                       (Hrp : real_lt real_zero r)
                       (Hrlt : real_lt r r2)
                       (HwnE : real_eq wn (real_mult r r)),
  real_lt wn (real_mult R R).
Proof.
  intros wn r r2 R HR Hr2E Hrp Hrlt HwnE.
  assert (Hq21 : QltT (1#2)%Q 1%Q) by reflexivity.
  assert (HR2R : real_lt r2 R).
  { apply (real_eq_lt_lt r2 (real_mult R (real_const (1#2)%Q)) R).
    - exact (real_eq_trans r2 (real_mult (real_const (1#2)%Q) R)
               (real_mult R (real_const (1#2)%Q)) Hr2E
               (real_mult_comm (real_const (1#2)%Q) R)).
    - exact (real_lt_eq_lt (real_mult R (real_const (1#2)%Q))
               (real_mult R real_one) R
               (real_lt_mult_compat (real_const (1#2)%Q) real_one R HR
                  (gaC1_04_qlt_const_lt (1#2)%Q 1%Q Hq21))
               (real_mult_one R)). }
  assert (Hr2p : real_lt real_zero r2)
    by exact (real_lt_trans real_zero r r2 Hrp Hrlt).
  exact (real_eq_lt_lt wn (real_mult r r) (real_mult R R) HwnE
           (real_lt_trans (real_mult r r) (real_mult r2 r2) (real_mult R R)
              (mm_sq_strict_mono r r2
                 (real_lt_le_iff real_zero r (inl Hrp)) Hrlt)
              (mm_sq_strict_mono r2 R
                 (real_lt_le_iff real_zero r2 (inl Hr2p)) HR2R))).
Qed.

(* The first-order norm transport: the squared modulus of the base
   plus its aligned increment, in the expanded closed form. *)
Lemma mm_X0_norm : forall (a0 aw : Cx) (kap m0 : Real)
    (Hal : c_eq aw (c_scale kap a0))
    (Hm : real_eq (c_norm_sq a0) m0),
  real_eq (c_norm_sq (c_plus a0 aw))
          (real_plus m0
             (real_plus (real_mult (real_const (2#1)%Q) (real_mult kap m0))
                        (real_mult (real_mult kap kap) m0))).
Proof.
  intros a0 aw kap m0 Hal Hm.
  apply (real_eq_trans (c_norm_sq (c_plus a0 aw))
           (c_norm_sq (c_plus a0 (c_scale kap a0)))
           (real_plus m0
              (real_plus (real_mult (real_const (2#1)%Q) (real_mult kap m0))
                         (real_mult (real_mult kap kap) m0)))).
  - apply mm_norm_wd.
    + apply c_plus_congr.
      * apply c_eq_refl.
      * exact Hal.
  - exact (mm_first_order_norm a0 kap m0 Hm).
Qed.

(* The domination face: the recombined complex sum carries the
   squared modulus of the function value. *)
Lemma mm_dom_face : forall (fz a0 aw : Cx) (ssq : Real)
    (Hrev : real_le (real_mult ssq ssq)
               (c_norm_sq (c_plus (c_plus a0 aw)
                            (c_plus (c_plus fz (c_opp a0)) (c_opp aw))))),
  real_le (real_mult ssq ssq) (c_norm_sq fz).
Proof.
  intros fz a0 aw ssq Hrev.
  exact (mm_le_eq_r (real_mult ssq ssq)
           (c_norm_sq (c_plus (c_plus a0 aw)
                         (c_plus (c_plus fz (c_opp a0)) (c_opp aw))))
           (c_norm_sq fz) Hrev
           (mm_norm_wd (c_plus (c_plus a0 aw)
                          (c_plus (c_plus fz (c_opp a0)) (c_opp aw))) fz
              (mm_c_recombine a0 aw fz))).
Qed.

(* The closed-form positivity: 0 < m0 + (2km + k*k*m) from the two
   gain positivities, with the doubled term derived internally. *)
Lemma mm_X0_pos : forall (k m0 : Real)
    (Hk : real_lt real_zero k) (Hm0 : real_lt real_zero m0),
  real_lt real_zero
     (real_plus m0
        (real_plus (real_mult (real_const (2#1)%Q) (real_mult k m0))
                   (real_mult (real_mult k k) m0))).
Proof.
  intros k m0 Hk Hm0.
  assert (Hkm : real_lt real_zero (real_mult k m0))
    by exact (real_mult_positive k m0 Hk Hm0).
  assert (Hq2p : QltT 0 (2#1)%Q) by reflexivity.
  assert (Hk2 : real_lt real_zero (real_mult (real_mult k k) m0))
    by exact (real_mult_positive (real_mult k k) m0
                (real_mult_positive k k Hk Hk) Hm0).
  exact (mm_three_pos m0 (real_mult (real_const (2#1)%Q) (real_mult k m0))
           (real_mult (real_mult k k) m0) Hm0
           (real_mult_positive (real_const (2#1)%Q) (real_mult k m0)
              (gaC1_04_qlt_const_lt 0 (2#1)%Q Hq2p) Hkm) Hk2).
Qed.
