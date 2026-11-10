(* ConstructiveWorld-Main - the theta, cap, and gain-split kernel
   faces of the maximum-modulus disk node. *)

(** * GaC2_11_MaxModulusDisk_e: theta and gain-split kernels.

    Mission.  Node C2-11 (segment C2, slot W2), machine piece.  The
      theta and gain-split kernel faces consumed by the growth
      statement: the adaptive-theta reciprocal kit ([mm_theta_kit]:
      the witness pair of the theta factor and its unit reciprocal
      with the defining equation and the five comparison faces),
      the two-term comparison shift ([mm_HT_shift]), the gain-split
      identity ([mm_G_eq]), the reciprocal-reassociation face
      ([mm_mul_inv_assoc]), the half-tau cap of the
      radius-square-root product ([mm_rsq_lt_half]), and the
      half-gain domination ([mm_A_le_G]).  Every kernel takes its
      data as explicit arguments, so the pointwise
      rational-algebra routes proceed on freshly introduced
      components only.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing] (selective [NatLe] import), [S02_CauchyComplete]
      (order kit, [real_eq_of_zero_diff] ring route, ring laws),
      [S03_QExp] ([real_inv_pos] and its faces), [S07_RealSetoidExpLog]
      ([real_mult_positive], [real_lt_mult_compat],
      [real_lt_plus_compat_lt_le], [RealSetoid.real_eq_mult_compat],
      [real_lt_le_iff]), [CxRealPairCore] + [CxRealPairExpLog] (pair
      carrier, [c_scale]), [GaC1_Iface_Cx] (complex slice),
      [GaC1_Iface_Real] (C1-04 rational bridge, C1-05 square root
      faces), and the machine clusters [GaC2_11_MaxModulusDisk_a],
      [GaC2_11_MaxModulusDisk_b], [GaC2_11_MaxModulusDisk_c],
      [GaC2_11_MaxModulusDisk_d] of this node.

    References.  drafts_C2.md C2.11 statement sketch (the adaptive
      radius and the first-order gain direction); Ahlfors Ch.2 the
      first-order growth direction argument mirrored at the
      squared-carrier level.

    Constructivity.  Every named construction is carried by [Set];
      the order predicates are the Set-sorted [real_lt] /
      [real_le]; zero assumed constants; every proof closes under
      the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_11_MaxModulusDisk_e.v] from the flat
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
Require Import GaC2_11_MaxModulusDisk_d.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.
Lemma mm_theta_inv_kit : forall (tau e th one_t ivt : Real)
                           (Htau : real_lt real_zero tau)
                           (He : real_lt real_zero e)
                           (Hth : real_eq th (real_mult tau e))
                           (H1t : real_lt real_zero one_t)
                           (Hone : real_eq one_t (real_plus real_one th))
                           (Hivt : real_eq ivt (real_inv_pos one_t H1t)),
  S01_BaseRing.And (real_lt real_zero th)
    (S01_BaseRing.And (real_lt real_zero ivt)
      (S01_BaseRing.And (real_lt (real_mult th ivt) real_one)
        (S01_BaseRing.And (real_lt ivt real_one)
                          (real_le (real_mult th ivt) th)))).
Proof.
  intros tau e th one_t ivt Htau He Hth H1t Hone Hivt.
  assert (Hthp : real_lt real_zero th).
  { exact (real_lt_eq_lt real_zero (real_mult tau e) th
             (real_mult_positive tau e Htau He) (real_eq_sym _ _ Hth)). }
  assert (Hivtp : real_lt real_zero ivt).
  { exact (real_lt_eq_lt real_zero (real_inv_pos one_t H1t) ivt
             (real_inv_pos_pos one_t H1t) (real_eq_sym _ _ Hivt)). }
  assert (Htlt : real_lt real_one one_t).
  { exact (real_lt_eq_lt real_one (real_plus real_one th) one_t
             (mm_lt_plus_r real_one th Hthp) (real_eq_sym _ _ Hone)). }
  assert (Htlt2 : real_lt th one_t).
  { apply (real_eq_lt_lt th (real_plus real_zero th) one_t).
    - apply real_eq_sym. exact (g1_plus_zero_l th).
    - exact (real_lt_eq_lt (real_plus real_zero th) (real_plus real_one th) one_t
               (real_lt_plus_compat_lt_le real_zero real_one th th
                  real_lt_zero_one (real_le_refl th))
               (real_eq_sym _ _ Hone)). }
  assert (Htu : real_lt (real_mult th ivt) real_one).
  { assert (H1 : real_lt (real_mult ivt th) (real_mult ivt one_t))
      by exact (real_lt_mult_compat th one_t ivt Hivtp Htlt2).
    assert (H2 : real_eq (real_mult ivt one_t) real_one).
    { exact (real_eq_trans (real_mult ivt one_t)
               (real_mult (real_inv_pos one_t H1t) one_t) real_one
               (RealSetoid.real_eq_mult_compat ivt one_t
                  (real_inv_pos one_t H1t) one_t Hivt (real_eq_refl one_t))
               (mm_inv_mul_one one_t H1t)). }
    exact (real_eq_lt_lt (real_mult th ivt) (real_mult ivt th) real_one
             (real_mult_comm th ivt)
             (real_lt_eq_lt (real_mult ivt th) (real_mult ivt one_t) real_one
                H1 H2)). }
  assert (Hivone : real_eq (real_inv_pos real_one real_lt_zero_one) real_one).
  { apply (real_eq_trans (real_inv_pos real_one real_lt_zero_one)
             (real_mult real_one (real_inv_pos real_one real_lt_zero_one)) real_one).
    - apply real_eq_sym. exact (mm_mult_one_l (real_inv_pos real_one real_lt_zero_one)).
    - exact (real_inv_pos_correct real_one real_lt_zero_one). }
  assert (Hivt1 : real_lt ivt real_one).
  { exact (real_eq_lt_lt ivt (real_inv_pos one_t H1t) real_one
             Hivt
             (real_lt_eq_lt (real_inv_pos one_t H1t)
                (real_inv_pos real_one real_lt_zero_one) real_one
                (mm_inv_anti_lt real_one one_t real_lt_zero_one H1t Htlt)
                Hivone)). }
  assert (Htule : real_le (real_mult th ivt) th).
  { apply (mm_le_eq_l (real_mult ivt th) (real_mult th ivt) th
             (real_mult_comm th ivt)
             (mm_le_eq_r (real_mult ivt th) (real_mult real_one th) th
                (real_le_mult_compat_weak ivt real_one th
                   (real_lt_le_iff real_zero th (inl Hthp))
                   (real_lt_le_iff ivt real_one (inl Hivt1)))
                (mm_mult_one_l th))). }
  exact (pair Hthp (pair Hivtp (pair Htu (pair Hivt1 Htule)))).
Qed.

(* The adaptive-theta witness: the theta factor th = tau*e together
   with its unit reciprocal ivt, with the defining equation and the
   five comparison faces used by the radius route. *)
Lemma mm_theta_kit : forall (tau e : Real)
                       (Htau : real_lt real_zero tau)
                       (He : real_lt real_zero e),
  sigT (fun th : Real => sigT (fun ivt : Real =>
    S01_BaseRing.And (real_eq th (real_mult tau e))
      (S01_BaseRing.And (real_lt real_zero th)
        (S01_BaseRing.And (real_lt real_zero ivt)
          (S01_BaseRing.And (real_lt (real_mult th ivt) real_one)
            (S01_BaseRing.And (real_lt ivt real_one)
                              (real_le (real_mult th ivt) th))))))).
Proof.
  intros tau e Htau He.
  set (th := real_mult tau e).
  assert (Hthp : real_lt real_zero th) by exact (real_mult_positive tau e Htau He).
  assert (H1t : real_lt real_zero (real_plus real_one th)).
  { apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
                                  (real_plus real_one th)).
    - apply real_eq_of_zero_diff. intro n.
      cbn [projT1 real_plus real_zero]. ring.
    - exact (real_lt_plus_compat real_zero real_one real_zero th
               real_lt_zero_one Hthp). }
  set (ivt := real_inv_pos (real_plus real_one th) H1t).
  destruct (mm_theta_inv_kit tau e th (real_plus real_one th) ivt Htau He
              (real_eq_refl th) H1t
              (real_eq_refl (real_plus real_one th)) (real_eq_refl ivt))
    as [Hthp' [Hivtp [Htu [Hivt1 Htule]]]].
  exists th. exists ivt.
  exact (pair (real_eq_refl th)
            (pair Hthp (pair Hivtp (pair Htu (pair Hivt1 Htule))))).
Qed.

(* The two-term comparison shift: with a, r positive and t < u,
   a*(r*t) < r*(a*u).  The pointwise algebra routes run on the
   freshly introduced components. *)
Lemma mm_HT_shift : forall (a r t u : Real)
                      (Ha : real_lt real_zero a)
                      (Hr : real_lt real_zero r)
                      (Htu : real_lt t u),
  real_lt (real_mult a (real_mult r t)) (real_mult r (real_mult a u)).
Proof.
  intros a r t u Ha Hr Htu.
  assert (Hprod : real_lt real_zero (real_mult a r))
    by exact (real_mult_positive a r Ha Hr).
  assert (Heq1 : real_eq (real_mult a (real_mult r t))
                         (real_mult (real_mult a r) t)).
  { apply real_eq_of_zero_diff. intro n.
    destruct a as [aq Haq]. destruct r as [rq Hrq]. destruct t as [tq Htq].
    cbn [projT1 real_plus real_mult real_opp real_zero real_one]. ring. }
  assert (Heq2 : real_eq (real_mult (real_mult a r) u)
                         (real_mult r (real_mult a u))).
  { apply real_eq_of_zero_diff. intro n.
    destruct a as [aq Haq]. destruct r as [rq Hrq]. destruct u as [uq Huq].
    cbn [projT1 real_plus real_mult real_opp real_zero real_one]. ring. }
  exact (real_eq_lt_lt (real_mult a (real_mult r t))
           (real_mult (real_mult a r) t) (real_mult r (real_mult a u))
           Heq1
           (real_lt_eq_lt (real_mult (real_mult a r) t)
              (real_mult (real_mult a r) u) (real_mult r (real_mult a u))
              (real_lt_mult_compat t u (real_mult a r) Hprod Htu) Heq2)).
Qed.

(* The gain split: s0 + r*(t - r*q) equals (s0 + r*t) - (r*r)*q. *)
Lemma mm_G_eq : forall (s0 r t q : Real),
  real_eq (real_plus s0 (real_mult r (real_plus t (real_opp (real_mult r q)))))
          (real_plus (real_plus s0 (real_mult r t))
                     (real_opp (real_mult (real_mult r r) q))).
Proof.
  intros s0 r t q. apply real_eq_of_zero_diff. intro n.
  destruct s0 as [a Ha]. destruct r as [b Hb]. destruct t as [c Hc].
  destruct q as [d Hd].
  cbn [projT1 real_plus real_mult real_opp real_zero real_one]. ring.
Qed.

(* Reassociation through the reciprocal: (x * inv y) * y == x. *)
Lemma mm_mul_inv_assoc : forall (x y : Real) (Hy : real_lt real_zero y),
  real_eq (real_mult (real_mult x (real_inv_pos y Hy)) y) x.
Proof.
  intros x y Hy.
  apply (real_eq_trans (real_mult (real_mult x (real_inv_pos y Hy)) y)
           (real_mult x (real_mult (real_inv_pos y Hy) y)) x).
  - exact (real_eq_sym _ _ (real_mult_assoc x (real_inv_pos y Hy) y)).
  - apply (real_eq_trans (real_mult x (real_mult (real_inv_pos y Hy) y))
             (real_mult x real_one) x).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact (mm_inv_mul_one y Hy).
    + exact (real_mult_one x).
Qed.

(* The half-tau cap: with r = r4*(th*ivt), ivt < 1 and
   tau = th*(4*(r4*sqT)), the product r*sqT stays below (1/2)*tau. *)
Lemma mm_rsq_lt_half : forall (r r4 th ivt sqT tau : Real)
    (Hthp : real_lt real_zero th)
    (Hivt1 : real_lt ivt real_one)
    (Hr4p : real_lt real_zero r4)
    (HsqTp : real_lt real_zero sqT)
    (Htaup : real_lt real_zero tau)
    (HpY : real_lt real_zero
             (real_mult (real_const (4#1)%Q) (real_mult r4 sqT)))
    (HrE : real_eq r (real_mult r4 (real_mult th ivt)))
    (HthE : real_eq th
              (real_mult tau
                 (real_inv_pos (real_mult (real_const (4#1)%Q)
                    (real_mult r4 sqT)) HpY))),
  real_lt (real_mult r sqT) (real_mult (real_const (1#2)%Q) tau).
Proof.
  intros r r4 th ivt sqT tau Hthp Hivt1 Hr4p HsqTp Htaup HpY HrE HthE.
  assert (HtauE : real_eq tau
                    (real_mult th
                       (real_mult (real_const (4#1)%Q) (real_mult r4 sqT)))).
  { exact (real_eq_sym _ _
             (real_eq_trans
                (real_mult th
                   (real_mult (real_const (4#1)%Q) (real_mult r4 sqT)))
                (real_mult
                   (real_mult tau
                      (real_inv_pos (real_mult (real_const (4#1)%Q)
                         (real_mult r4 sqT)) HpY))
                   (real_mult (real_const (4#1)%Q) (real_mult r4 sqT)))
                tau
                (RealSetoid.real_eq_mult_compat th
                   (real_mult (real_const (4#1)%Q) (real_mult r4 sqT))
                   (real_mult tau
                      (real_inv_pos (real_mult (real_const (4#1)%Q)
                         (real_mult r4 sqT)) HpY))
                   (real_mult (real_const (4#1)%Q) (real_mult r4 sqT))
                   HthE (real_eq_refl _))
                (mm_mul_inv_assoc tau
                   (real_mult (real_const (4#1)%Q) (real_mult r4 sqT)) HpY))). }
  assert (HU : real_lt real_zero (real_mult th (real_mult r4 sqT)))
    by exact (real_mult_positive th (real_mult r4 sqT) Hthp
                (real_mult_positive r4 sqT Hr4p HsqTp)).
  assert (HivtU : real_lt (real_mult ivt (real_mult th (real_mult r4 sqT)))
                          (real_mult th (real_mult r4 sqT))).
  { assert (HU' : real_lt (real_mult (real_mult th (real_mult r4 sqT)) ivt)
                          (real_mult (real_mult th (real_mult r4 sqT)) real_one))
      by exact (real_lt_mult_compat ivt real_one (real_mult th (real_mult r4 sqT))
                  HU Hivt1).
    exact (real_lt_eq_lt (real_mult ivt (real_mult th (real_mult r4 sqT)))
             (real_mult (real_mult th (real_mult r4 sqT)) real_one)
             (real_mult th (real_mult r4 sqT))
             (real_eq_lt_lt (real_mult ivt (real_mult th (real_mult r4 sqT)))
                (real_mult (real_mult th (real_mult r4 sqT)) ivt)
                (real_mult (real_mult th (real_mult r4 sqT)) real_one)
                (real_mult_comm ivt (real_mult th (real_mult r4 sqT))) HU')
             (real_mult_one (real_mult th (real_mult r4 sqT)))). }
  assert (HUeq : real_eq (real_mult th (real_mult r4 sqT))
                         (real_mult (real_const (1#4)%Q) tau)).
  { apply (real_eq_trans (real_mult th (real_mult r4 sqT))
             (real_mult (real_const (1#4)%Q)
                (real_mult th (real_mult (real_const (4#1)%Q)
                   (real_mult r4 sqT))))
             (real_mult (real_const (1#4)%Q) tau)).
    - apply real_eq_of_zero_diff. intro n.
      destruct th as [t1 Ht1]. destruct r4 as [u1 Hu1]. destruct sqT as [v1 Hv1].
      cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const]. ring.
    - apply RealSetoid.real_eq_mult_compat.
      + apply real_eq_refl.
      + exact (real_eq_sym _ _ HtauE). }
  assert (Hq42 : QltT (1#4)%Q (1#2)%Q) by reflexivity.
  assert (Hquarter : real_lt (real_mult (real_const (1#4)%Q) tau)
                             (real_mult (real_const (1#2)%Q) tau)).
  { exact (real_eq_lt_lt (real_mult (real_const (1#4)%Q) tau)
             (real_mult tau (real_const (1#4)%Q))
             (real_mult (real_const (1#2)%Q) tau)
             (real_mult_comm (real_const (1#4)%Q) tau)
             (real_lt_eq_lt (real_mult tau (real_const (1#4)%Q))
                (real_mult tau (real_const (1#2)%Q))
                (real_mult (real_const (1#2)%Q) tau)
                (real_lt_mult_compat (real_const (1#4)%Q) (real_const (1#2)%Q) tau
                   Htaup (gaC1_04_qlt_const_lt (1#4)%Q (1#2)%Q Hq42))
                (real_mult_comm tau (real_const (1#2)%Q)))). }
  assert (HrEq : real_eq (real_mult r sqT)
                         (real_mult ivt (real_mult th (real_mult r4 sqT)))).
  { apply (real_eq_trans (real_mult r sqT)
             (real_mult (real_mult r4 (real_mult th ivt)) sqT)
             (real_mult ivt (real_mult th (real_mult r4 sqT)))).
    - apply RealSetoid.real_eq_mult_compat.
      + exact HrE.
      + apply real_eq_refl.
    - apply real_eq_of_zero_diff. intro n.
      destruct ivt as [q1 Hq1]. destruct th as [t1 Ht1].
      destruct r4 as [u1 Hu1]. destruct sqT as [v1 Hv1].
      cbn [projT1 real_plus real_mult real_opp real_zero real_one]. ring. }
  exact (real_lt_trans (real_mult r sqT)
           (real_mult th (real_mult r4 sqT))
           (real_mult (real_const (1#2)%Q) tau)
           (real_eq_lt_lt (real_mult r sqT)
              (real_mult ivt (real_mult th (real_mult r4 sqT)))
              (real_mult th (real_mult r4 sqT))
              HrEq HivtU)
           (real_eq_lt_lt (real_mult th (real_mult r4 sqT))
              (real_mult (real_const (1#4)%Q) tau)
              (real_mult (real_const (1#2)%Q) tau)
              HUeq Hquarter)).
Qed.

(* The half-gain domination: with r positive and r*q < (1/2)*t,
   s0 + (1/2)*(r*t) <= s0 + r*(t - r*q). *)
Lemma mm_A_le_G : forall (s0 r t q : Real)
    (Hrp : real_lt real_zero r)
    (Hrsq : real_lt (real_mult r q) (real_mult (real_const (1#2)%Q) t)),
  real_le (real_plus s0 (real_mult (real_const (1#2)%Q) (real_mult r t)))
          (real_plus s0 (real_mult r (real_plus t (real_opp (real_mult r q))))).
Proof.
  intros s0 r t q Hrp Hrsq.
  assert (HeqL : real_eq (real_mult (real_const (1#2)%Q) (real_mult r t))
                         (real_mult r (real_mult (real_const (1#2)%Q) t))).
  { apply real_eq_of_zero_diff. intro n.
    destruct r as [p1 Hp1]. destruct t as [q1 Hq1].
    cbn [projT1 real_plus real_mult real_opp real_zero real_one real_const]. ring. }
  assert (Hhalf2 : real_eq (real_plus (real_mult (real_const (1#2)%Q) t)
                                      (real_mult (real_const (1#2)%Q) t)) t)
    by exact (mm_half_plus t).
  assert (Hsum2 : real_lt (real_plus (real_mult (real_const (1#2)%Q) t)
                                     (real_mult r q))
                          (real_plus (real_mult (real_const (1#2)%Q) t)
                                     (real_mult (real_const (1#2)%Q) t)))
    by exact (real_lt_plus_compat_le_lt (real_mult (real_const (1#2)%Q) t)
               (real_mult (real_const (1#2)%Q) t) (real_mult r q)
               (real_mult (real_const (1#2)%Q) t)
               (real_le_refl (real_mult (real_const (1#2)%Q) t)) Hrsq).
  assert (Hhalfsum : real_lt (real_plus (real_mult (real_const (1#2)%Q) t)
                                        (real_mult r q)) t).
  { exact (real_lt_eq_lt (real_plus (real_mult (real_const (1#2)%Q) t) (real_mult r q))
             (real_plus (real_mult (real_const (1#2)%Q) t)
                        (real_mult (real_const (1#2)%Q) t)) t
             Hsum2 Hhalf2). }
  assert (Hhalf : real_lt (real_mult (real_const (1#2)%Q) t)
                          (real_plus t (real_opp (real_mult r q)))).
  { exact (mm_lt_minus_r (real_mult (real_const (1#2)%Q) t) (real_mult r q) t
             Hhalfsum). }
  assert (HhalfLE : real_le (real_mult (real_const (1#2)%Q) t)
                            (real_plus t (real_opp (real_mult r q))))
    by exact (real_lt_le_iff _ _ (inl Hhalf)).
  assert (Hscaled : real_le (real_mult (real_mult (real_const (1#2)%Q) t) r)
                            (real_mult (real_plus t (real_opp (real_mult r q))) r))
    by exact (real_le_mult_compat_weak (real_mult (real_const (1#2)%Q) t)
               (real_plus t (real_opp (real_mult r q))) r
               (real_lt_le_iff real_zero r (inl Hrp)) HhalfLE).
  assert (HcommL : real_le (real_mult r (real_mult (real_const (1#2)%Q) t))
                           (real_mult (real_plus t (real_opp (real_mult r q))) r))
    by exact (mm_le_eq_l (real_mult (real_mult (real_const (1#2)%Q) t) r)
               (real_mult r (real_mult (real_const (1#2)%Q) t))
               (real_mult (real_plus t (real_opp (real_mult r q))) r)
               (real_mult_comm r (real_mult (real_const (1#2)%Q) t)) Hscaled).
  assert (HcommR : real_le (real_mult r (real_mult (real_const (1#2)%Q) t))
                           (real_mult r (real_plus t (real_opp (real_mult r q)))))
    by exact (mm_le_eq_r (real_mult r (real_mult (real_const (1#2)%Q) t))
               (real_mult (real_plus t (real_opp (real_mult r q))) r)
               (real_mult r (real_plus t (real_opp (real_mult r q))))
               HcommL
               (real_mult_comm (real_plus t (real_opp (real_mult r q))) r)).
  exact (mm_le_plus_compat s0 s0
           (real_mult (real_const (1#2)%Q) (real_mult r t))
           (real_mult r (real_plus t (real_opp (real_mult r q))))
           (real_le_refl s0)
           (mm_le_eq_l (real_mult r (real_mult (real_const (1#2)%Q) t))
              (real_mult (real_const (1#2)%Q) (real_mult r t))
              (real_mult r (real_plus t (real_opp (real_mult r q))))
              HeqL HcommR)).
Qed.
