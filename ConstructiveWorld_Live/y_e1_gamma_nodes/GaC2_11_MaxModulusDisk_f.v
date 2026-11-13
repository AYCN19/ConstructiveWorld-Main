(* ConstructiveWorld-Main, GaC2_11_MaxModulusDisk_f (node C2-11,
   segment C2, slot W2, machine piece): bridge and leaf kernel faces.
   Mission.  The bridge and leaf kernel faces consumed by the
     growth statement (mm_kappa_bridge: the kappa-cancellation
     bridge; mm_A2_lt_X0: the squared-base domination; mm_leaf4:
     the growth leaf); every kernel takes explicit data arguments,
     so the pointwise rational-algebra routes proceed on freshly
     introduced components only.
   Dependencies.  Stdlib QArith.QArith, Lia.  Requires S01_BaseRing
     (selective NatLe import), S02_CauchyComplete (order kit,
     real_eq_of_zero_diff ring route, ring laws), S03_QExp
     (real_inv_pos and its faces), S07_RealSetoidExpLog
     (real_mult_positive, real_lt_mult_compat, real_lt_plus_compat,
     real_lt_plus_compat_lt_le, RealSetoid.real_eq_mult_compat,
     real_lt_le_iff), CxRealPairCore + CxRealPairExpLog (pair
     carrier), GaC1_Iface_Cx (complex slice), GaC1_Iface_Real
     (C1-04 rational bridge, C1-05 square root faces), machine
     clusters GaC2_11_MaxModulusDisk_a, GaC2_11_MaxModulusDisk_b,
     GaC2_11_MaxModulusDisk_c, GaC2_11_MaxModulusDisk_d, and
     GaC2_11_MaxModulusDisk_e of this node.
   References.  drafts_C2.md C2.11 statement sketch (the adaptive
     radius and the first-order gain direction); Ahlfors Ch.2, the
     growth-direction argument mirrored at the squared-carrier level.
   Constructivity.  Every named construction is carried by Set; the
     order predicates are the Set-sorted real_lt / real_le; zero
     assumed constants; every proof closes under the global context.
   Build.  coqc -native-compiler no -q -Q <certified vo tree> ""
     -Q <build dir> "" GaC2_11_MaxModulusDisk_f.v, from the flat
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
Require Import GaC2_11_MaxModulusDisk_e.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* The kappa-cancellation bridge: for k = r*(iv*m1) with
   iv = inv(s0*s1), the gain-times-modulus face k*m0 and the
   squared-gain face (k*k)*m0 transport against the radius faces
   r*(s0*s1) and (r*r)*m1. *)
Lemma mm_kappa_bridge : forall (k r iv m1 m0 s0 s1 : Real)
    (Hss : real_lt real_zero (real_mult s0 s1))
    (HkE : real_eq k (real_mult r (real_mult iv m1)))
    (HivE : real_eq iv (real_inv_pos (real_mult s0 s1) Hss))
    (Hsq0 : real_eq (real_mult s0 s0) m0)
    (Hsq1 : real_eq (real_mult s1 s1) m1),
  S01_BaseRing.And (real_eq (real_mult k m0)
                            (real_mult r (real_mult s0 s1)))
    (real_eq (real_mult (real_mult k k) m0)
             (real_mult (real_mult r r) m1)).
Proof.
  intros k r iv m1 m0 s0 s1 Hss HkE HivE Hsq0 Hsq1.
  assert (Hm1m0 : real_eq (real_mult m1 m0)
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
  assert (H1 : real_eq (real_mult iv (real_mult s0 s1)) real_one)
    by exact (real_eq_trans (real_mult iv (real_mult s0 s1))
                (real_mult (real_inv_pos (real_mult s0 s1) Hss)
                   (real_mult s0 s1)) real_one
                (RealSetoid.real_eq_mult_compat iv (real_mult s0 s1)
                   (real_inv_pos (real_mult s0 s1) Hss) (real_mult s0 s1)
                   HivE (real_eq_refl _))
                (mm_inv_mul_one (real_mult s0 s1) Hss)).
  assert (H2 : real_eq (real_mult iv (real_mult m1 (real_mult s0 s1))) m1).
  { apply (real_eq_trans (real_mult iv (real_mult m1 (real_mult s0 s1)))
             (real_mult iv (real_mult (real_mult s0 s1) m1)) m1).
    - apply RealSetoid.real_eq_mult_compat.
      + apply real_eq_refl.
      + exact (real_mult_comm m1 (real_mult s0 s1)).
    - apply (real_eq_trans (real_mult iv (real_mult (real_mult s0 s1) m1))
               (real_mult (real_mult iv (real_mult s0 s1)) m1) m1).
      + exact (real_mult_assoc iv (real_mult s0 s1) m1).
      + apply (real_eq_trans (real_mult (real_mult iv (real_mult s0 s1)) m1)
                 (real_mult real_one m1) m1).
        * exact (RealSetoid.real_eq_mult_compat
                   (real_mult iv (real_mult s0 s1)) m1 real_one m1
                   H1 (real_eq_refl m1)).
        * exact (mm_mult_one_l m1). }
  assert (H3 : real_eq (real_mult (real_mult iv m1) m0) (real_mult s0 s1)).
  { apply (real_eq_trans (real_mult (real_mult iv m1) m0)
             (real_mult iv (real_mult m1 m0)) (real_mult s0 s1)).
    - exact (real_eq_sym _ _ (real_mult_assoc iv m1 m0)).
    - apply (real_eq_trans (real_mult iv (real_mult m1 m0))
               (real_mult iv (real_mult (real_mult s0 s1) (real_mult s0 s1)))
               (real_mult s0 s1)).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact Hm1m0.
      + apply (real_eq_trans
                 (real_mult iv (real_mult (real_mult s0 s1) (real_mult s0 s1)))
                 (real_mult (real_mult iv (real_mult s0 s1)) (real_mult s0 s1))
                 (real_mult s0 s1)).
        * exact (real_mult_assoc iv (real_mult s0 s1) (real_mult s0 s1)).
        * apply (real_eq_trans
                   (real_mult (real_mult iv (real_mult s0 s1)) (real_mult s0 s1))
                   (real_mult real_one (real_mult s0 s1)) (real_mult s0 s1)).
          -- apply RealSetoid.real_eq_mult_compat.
             ++ exact H1.
             ++ apply real_eq_refl.
          -- exact (mm_mult_one_l (real_mult s0 s1)). }
  assert (HB1 : real_eq (real_mult k m0) (real_mult r (real_mult s0 s1))).
  { apply (real_eq_trans (real_mult k m0)
             (real_mult (real_mult r (real_mult iv m1)) m0)
             (real_mult r (real_mult s0 s1))).
    - apply RealSetoid.real_eq_mult_compat.
      + exact HkE.
      + apply real_eq_refl.
    - apply (real_eq_trans (real_mult (real_mult r (real_mult iv m1)) m0)
               (real_mult r (real_mult (real_mult iv m1) m0))
               (real_mult r (real_mult s0 s1))).
      + exact (real_eq_sym _ _ (real_mult_assoc r (real_mult iv m1) m0)).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact H3. }
  assert (H4 : real_eq (real_mult k (real_mult s0 s1)) (real_mult r m1)).
  { apply (real_eq_trans (real_mult k (real_mult s0 s1))
             (real_mult (real_mult r (real_mult iv m1)) (real_mult s0 s1))
             (real_mult r m1)).
    - apply RealSetoid.real_eq_mult_compat.
      + exact HkE.
      + apply real_eq_refl.
    - apply (real_eq_trans
               (real_mult (real_mult r (real_mult iv m1)) (real_mult s0 s1))
               (real_mult r (real_mult (real_mult iv m1) (real_mult s0 s1)))
               (real_mult r m1)).
      + exact (real_eq_sym _ _ (real_mult_assoc r (real_mult iv m1) (real_mult s0 s1))).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact (real_eq_trans (real_mult (real_mult iv m1) (real_mult s0 s1))
                   (real_mult iv (real_mult m1 (real_mult s0 s1))) m1
                   (real_eq_sym _ _ (real_mult_assoc iv m1 (real_mult s0 s1))) H2). }
  assert (HB2 : real_eq (real_mult (real_mult k k) m0)
                        (real_mult (real_mult r r) m1)).
  { apply (real_eq_trans (real_mult (real_mult k k) m0)
             (real_mult k (real_mult k m0))
             (real_mult (real_mult r r) m1)).
    - exact (real_eq_sym _ _ (real_mult_assoc k k m0)).
    - apply (real_eq_trans (real_mult k (real_mult k m0))
               (real_mult k (real_mult r (real_mult s0 s1)))
               (real_mult (real_mult r r) m1)).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact HB1.
      + apply (real_eq_trans (real_mult k (real_mult r (real_mult s0 s1)))
                 (real_mult (real_mult k r) (real_mult s0 s1))
                 (real_mult (real_mult r r) m1)).
        * exact (real_mult_assoc k r (real_mult s0 s1)).
        * apply (real_eq_trans (real_mult (real_mult k r) (real_mult s0 s1))
                   (real_mult (real_mult r k) (real_mult s0 s1))
                   (real_mult (real_mult r r) m1)).
          -- apply RealSetoid.real_eq_mult_compat.
             ++ exact (real_mult_comm k r).
             ++ apply real_eq_refl.
          -- apply (real_eq_trans
                       (real_mult (real_mult r k) (real_mult s0 s1))
                       (real_mult r (real_mult k (real_mult s0 s1)))
                       (real_mult (real_mult r r) m1)).
             ** exact (real_eq_sym _ _ (real_mult_assoc r k (real_mult s0 s1))).
             ** apply (real_eq_trans
                          (real_mult r (real_mult k (real_mult s0 s1)))
                          (real_mult r (real_mult r m1))
                          (real_mult (real_mult r r) m1)).
                --- apply RealSetoid.real_eq_mult_compat.
                    +++ apply real_eq_refl.
                    +++ exact H4.
                --- exact (real_mult_assoc r r m1). }
  exact (pair HB1 HB2).
Qed.

(* The squared-base domination: with the base square expanded
   against m0 and the closed form of the squared modulus, the two
   term-wise comparisons give the domination. *)
Lemma mm_A2_lt_X0 : forall (aa m0 k1 k2 i1 i2 x0n : Real)
    (Haa : real_eq aa (real_plus m0 (real_plus i1 i2)))
    (Hx0 : real_eq x0n (real_plus m0 (real_plus k1 k2)))
    (Hi1k1 : real_lt i1 k1)
    (Hi2k2 : real_lt i2 k2),
  real_lt aa x0n.
Proof.
  intros aa m0 k1 k2 i1 i2 x0n Haa Hx0 Hi1k1 Hi2k2.
  apply (real_eq_lt_lt aa (real_plus m0 (real_plus i1 i2)) x0n Haa).
  exact (real_lt_eq_lt (real_plus m0 (real_plus i1 i2))
           (real_plus m0 (real_plus k1 k2)) x0n
           (real_lt_plus_compat_le_lt m0 m0 (real_plus i1 i2)
              (real_plus k1 k2) (real_le_refl m0)
              (real_lt_plus_compat i1 k1 i2 k2 Hi1k1 Hi2k2))
           (real_eq_sym _ _ Hx0)).
Qed.

(* The growth leaf: the half-gain base square is dominated by the
   boundary-reduced remainder face. *)
Lemma mm_leaf4 : forall (s0 r tau sq su fq : Real)
    (Hrhop : real_lt real_zero r)
    (Hs0p : real_lt real_zero s0)
    (Htaup : real_lt real_zero tau)
    (Hrsq : real_lt (real_mult r sq) (real_mult (real_const (1#2)%Q) tau))
    (HAp : real_lt real_zero (real_mult r tau))
    (HAlt : real_lt (real_plus s0 (real_mult r tau)) su)
    (Hdom : real_le (real_mult
                       (real_plus su
                          (real_opp (real_mult (real_mult r r) sq)))
                       (real_plus su
                          (real_opp (real_mult (real_mult r r) sq)))) fq),
  real_le (real_mult (real_plus s0
                        (real_mult (real_const (1#2)%Q) (real_mult r tau)))
                     (real_plus s0
                        (real_mult (real_const (1#2)%Q) (real_mult r tau))))
          fq.
Proof.
  intros s0 r tau sq su fq Hrhop Hs0p Htaup Hrsq HAp HAlt Hdom.
  assert (Hqhp : QltT 0 (1#2)%Q) by reflexivity.
  assert (Hqhppos : real_lt real_zero (real_const (1#2)%Q))
    by exact (gaC1_04_qlt_const_lt 0 (1#2)%Q Hqhp).
  assert (Hhalfpos : real_lt real_zero (real_mult (real_const (1#2)%Q) tau))
    by exact (real_mult_positive (real_const (1#2)%Q) tau Hqhppos Htaup).
  set (Al := real_plus s0 (real_mult (real_const (1#2)%Q) (real_mult r tau))).
  set (G := real_plus s0
              (real_mult r (real_plus tau (real_opp (real_mult r sq))))).
  set (SV := real_mult (real_mult r r) sq).
  assert (Hhalftau : real_lt (real_mult (real_const (1#2)%Q) tau) tau).
  { exact (real_lt_eq_lt (real_mult (real_const (1#2)%Q) tau)
             (real_plus (real_mult (real_const (1#2)%Q) tau)
                        (real_mult (real_const (1#2)%Q) tau)) tau
             (mm_lt_plus_r (real_mult (real_const (1#2)%Q) tau)
                (real_mult (real_const (1#2)%Q) tau) Hhalfpos)
             (mm_half_plus tau)). }
  assert (HGs : real_lt real_zero (real_plus tau (real_opp (real_mult r sq))))
    by exact (mm_lt_sub_r (real_mult r sq) tau
                (real_lt_trans (real_mult r sq)
                   (real_mult (real_const (1#2)%Q) tau) tau Hrsq Hhalftau)).
  assert (HGE : real_eq G (real_plus (real_plus s0 (real_mult r tau))
                                   (real_opp SV)))
    by exact (mm_G_eq s0 r tau sq).
  assert (HGlt : real_lt G (real_plus su (real_opp SV))).
  { exact (real_eq_lt_lt G
             (real_plus (real_plus s0 (real_mult r tau)) (real_opp SV))
             (real_plus su (real_opp SV)) HGE
             (real_lt_plus_compat_lt_le (real_plus s0 (real_mult r tau)) su
                (real_opp SV) (real_opp SV)
                HAlt (real_le_refl (real_opp SV)))). }
  assert (HG0 : real_lt real_zero G).
  { exact (real_lt_trans real_zero s0 G Hs0p
              (mm_lt_plus_r s0
                 (real_mult r (real_plus tau (real_opp (real_mult r sq))))
                 (real_mult_positive r
                    (real_plus tau (real_opp (real_mult r sq))) Hrhop HGs))). }
  assert (Hfin : real_lt (real_mult G G) fq).
  { exact (real_lt_le_trans (real_mult G G)
             (real_mult (real_plus su (real_opp SV)) (real_plus su (real_opp SV)))
             fq
             (mm_sq_strict_mono G (real_plus su (real_opp SV))
                (real_lt_le_iff real_zero G (inl HG0)) HGlt)
             Hdom). }
  assert (HAG : real_le Al G) by exact (mm_A_le_G s0 r tau sq Hrhop Hrsq).
  assert (HAlpos : real_lt real_zero Al).
  { exact (real_lt_trans real_zero s0 Al Hs0p
              (mm_lt_plus_r s0
                 (real_mult (real_const (1#2)%Q) (real_mult r tau))
                 (real_mult_positive (real_const (1#2)%Q) (real_mult r tau)
                    Hqhppos HAp))). }
  assert (HAGsq : real_le (real_mult Al Al) (real_mult G G)).
  { assert (Hstep1 : real_le (real_mult Al Al) (real_mult G Al))
      by exact (real_le_mult_compat_weak Al G Al
                  (real_lt_le_iff real_zero Al (inl HAlpos)) HAG).
    assert (Hstep2 : real_le (real_mult Al G) (real_mult G G))
      by exact (real_le_mult_compat_weak Al G G
                  (real_lt_le_iff real_zero G (inl HG0)) HAG).
    exact (real_le_trans (real_mult Al Al) (real_mult G Al) (real_mult G G)
             Hstep1
             (mm_le_eq_l (real_mult Al G) (real_mult G Al) (real_mult G G)
                (real_mult_comm G Al) Hstep2)). }
  exact (real_lt_le_iff (real_mult Al Al) fq
           (inl (mm_le_lt_trans (real_mult Al Al) (real_mult G G) fq
                   HAGsq Hfin))).
Qed.
