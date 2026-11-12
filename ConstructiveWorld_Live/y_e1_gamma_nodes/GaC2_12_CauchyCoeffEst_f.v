(** * GaC2_12_CauchyCoeffEst_f: the annulus-step glue kit.
    Mission.  Node C2-12 glue piece f.  Pure algebra faces consumed by the stem
      GaC2_12_CauchyCoeffEst: complex norm faces [gaC12_norm_mult]/
      [gaC12_scale_norm]/[gaC12_norm_conj_sq]/[gaC12_norm_opp_sq]; reciprocal
      faces [gaC12_inv_wd]/[gaC12_inv_sq]; the boundary positivity face
      [gaC12_boundary_dpos]; the difference-quotient modulus face
      [gaC12_dquot_norm_sq]; the annulus step face [gaC12_step_circle_bound];
      the scalar order face [gaC12_le_mult_compat]; the constant faces
      [gaC12_Cn_S_sq]/[gaC12_two_add_four]/[gaC12_rdiv_S]; the Cn sample
      certificates for n in {1,2,4}.  Set-carried; zero Sections; zero
      admitted goals.
    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC1_Iface_Real],
      [GaC2_11_MaxModulusDisk] with subpieces [GaC2_11_MaxModulusDisk_a]/
      [GaC2_11_MaxModulusDisk_b] (the [mm_*] algebra kit), and this cluster's
      pieces a through d.
    References.  drafts_C2.md C2.12 card (the difference-quotient circle bound
      2M/R route and the annulus recursion with explicit constant loss);
      Ahlfors Ch.2 the classical quotient iteration (statement only).
    Constructivity.  All statements are Set-sorted; no Section wrappers, no
      premise slots, zero assumed constants, zero admitted goals; every proof
      closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_f.v] from the flat build
      directory. *)

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
Require Import GaC2_12_CauchyCoeffEst_b.
Require Import GaC2_12_CauchyCoeffEst_c.
Require Import GaC2_12_CauchyCoeffEst_d.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* == Section 1. The complex-norm algebra faces.== *)
Lemma gaC12_norm_mult : forall x y : Cx,
  real_eq (c_norm_sq (c_mult x y))
          (real_mult (c_norm_sq x) (c_norm_sq y)).
Proof.
  intros [xr xi] [yr yi].
  destruct xr as [xrq xrc]; destruct xi as [xiq xic].
  destruct yr as [yrq yrc]; destruct yi as [yiq yic].
  apply real_eq_of_zero_diff; intro n.
  cbn [projT1 c_mult c_norm_sq cRe cIm fst snd real_mult real_plus real_opp].
  ring.
Qed.
Lemma gaC12_scale_norm : forall (s : Real) (v : Cx),
  real_eq (c_norm_sq (c_scale s v))
          (real_mult (real_mult s s) (c_norm_sq v)).
Proof.
  intros s [xr xi].
  destruct xr as [xrq xrc]; destruct xi as [xiq xic].
  destruct s as [sq sqc].
  apply real_eq_of_zero_diff; intro n.
  cbn [projT1 c_scale c_norm_sq cRe cIm fst snd real_mult real_plus].
  ring.
Qed.
Lemma gaC12_norm_conj_sq : forall v : Cx,
  real_eq (c_norm_sq (c_conj v)) (c_norm_sq v).
Proof.
  intros [xr xi].
  destruct xr as [xrq xrc]; destruct xi as [xiq xic].
  apply real_eq_of_zero_diff; intro n.
  cbn [projT1 c_conj c_norm_sq cRe cIm fst snd real_mult real_plus real_opp].
  ring.
Qed.
Lemma gaC12_norm_opp_sq : forall v : Cx,
  real_eq (c_norm_sq (c_opp v)) (c_norm_sq v).
Proof.
  intros [xr xi].
  destruct xr as [xrq xrc]; destruct xi as [xiq xic].
  apply real_eq_of_zero_diff; intro n.
  cbn [projT1 c_opp c_norm_sq cRe cIm fst snd real_mult real_plus real_opp].
  ring.
Qed.
Lemma gaC12_inv_wd : forall (a b : Real)
    (Ha : real_lt real_zero a) (Hb : real_lt real_zero b),
  real_eq a b ->
  real_eq (real_inv_pos a Ha) (real_inv_pos b Hb).
Proof.
  intros a b Ha Hb Hab.
  assert (HL : real_eq (real_mult (real_inv_pos a Ha) (real_mult a b)) b).
  { apply (real_eq_trans
              (real_mult (real_inv_pos a Ha) (real_mult a b))
              (real_mult real_one b)
              b).
    - apply (real_eq_trans
               (real_mult (real_inv_pos a Ha) (real_mult a b))
               (real_mult (real_mult (real_inv_pos a Ha) a) b)
               (real_mult real_one b)).
      + exact (real_mult_assoc (real_inv_pos a Ha) a b).
      + exact (RealSetoid.real_eq_mult_compat_adapt
                  (real_mult (real_inv_pos a Ha) a) real_one b b
                  (mm_inv_mul_one a Ha) (real_eq_refl b)).
    - exact (mm_mult_one_l b). }
  assert (HRt : real_eq (real_mult (real_inv_pos b Hb) (real_mult a b)) a).
  { apply (real_eq_trans
              (real_mult (real_inv_pos b Hb) (real_mult a b))
              (real_mult real_one a)
              a).
    - apply (real_eq_trans
               (real_mult (real_inv_pos b Hb) (real_mult a b))
               (real_mult (real_mult (real_inv_pos b Hb) b) a)
               (real_mult real_one a)).
      + exact (real_eq_trans
                  (real_mult (real_inv_pos b Hb) (real_mult a b))
                  (real_mult (real_inv_pos b Hb) (real_mult b a))
                  (real_mult (real_mult (real_inv_pos b Hb) b) a)
                  (RealSetoid.real_eq_mult_compat_adapt (real_inv_pos b Hb)
                     (real_inv_pos b Hb) (real_mult a b) (real_mult b a)
                     (real_eq_refl (real_inv_pos b Hb))
                     (real_mult_comm a b))
                  (real_mult_assoc (real_inv_pos b Hb) b a)).
      + exact (RealSetoid.real_eq_mult_compat_adapt
                  (real_mult (real_inv_pos b Hb) b) real_one a a
                  (mm_inv_mul_one b Hb) (real_eq_refl a)).
    - exact (mm_mult_one_l a). }
  apply (mm_mult_cancel_eq (real_inv_pos a Ha) (real_inv_pos b Hb)
           (real_mult a b) (real_mult_positive a b Ha Hb)).
  apply (real_eq_trans (real_mult (real_inv_pos a Ha) (real_mult a b)) b
           (real_mult (real_inv_pos b Hb) (real_mult a b))).
  - exact HL.
  - exact (real_eq_trans b a (real_mult (real_inv_pos b Hb) (real_mult a b))
             (real_eq_sym a b Hab) (real_eq_sym _ _ HRt)).
Qed.
Lemma gaC12_inv_sq : forall (R : Real) (HR : real_lt real_zero R),
  real_eq (real_mult (real_inv_pos R HR) (real_inv_pos R HR))
          (real_inv_pos (real_mult R R) (real_mult_positive R R HR HR)).
Proof.
  intros R HR.
  exact (real_eq_sym _ _ (gaC12_inv_mult R R HR HR)).
Qed.

(* == Section 2. The boundary and difference-quotient modulus faces.== *)
Lemma gaC12_boundary_dpos : forall (q c : Cx) (R : Real)
    (Hb : boundary q c R) (HR : real_lt real_zero R),
  real_lt real_zero (c_norm_sq (c_plus q (c_opp c))).
Proof.
  intros q c R Hb HR.
  apply (real_lt_eq_lt real_zero (real_mult R R)
           (c_norm_sq (c_plus q (c_opp c)))).
  - exact (real_mult_positive R R HR HR).
  - exact (real_eq_sym _ _ Hb).
Qed.
Lemma gaC12_dquot_norm_sq : forall (g : Cx -> Cx) (z0 q : Cx)
    (Hq : real_lt real_zero (c_norm_sq (c_plus q (c_opp z0)))),
  real_eq (c_norm_sq (gaC12_cx_dquot g z0 q Hq))
          (real_mult (c_norm_sq (c_plus (g q) (c_opp (g z0))))
                     (real_inv_pos (c_norm_sq (c_plus q (c_opp z0))) Hq)).
Proof.
  intros g z0 q Hq.
  unfold gaC12_cx_dquot.
  set (d := c_plus q (c_opp z0)) in *.
  set (K := real_inv_pos (c_norm_sq d) Hq) in *.
  set (num := c_plus (g q) (c_opp (g z0))) in *.
  set (nsq := c_norm_sq num) in *.
  set (dsq := c_norm_sq d) in *.
  apply (real_eq_trans
             (c_norm_sq (c_mult num (c_scale K (c_conj d))))
             (real_mult nsq (real_mult (real_mult K K) dsq))
             (real_mult nsq K)).
  - apply (real_eq_trans
               (c_norm_sq (c_mult num (c_scale K (c_conj d))))
               (real_mult nsq (c_norm_sq (c_scale K (c_conj d))))
               (real_mult nsq (real_mult (real_mult K K) dsq))).
    + exact (gaC12_norm_mult num (c_scale K (c_conj d))).
    + apply (real_eq_trans
                 (real_mult nsq (c_norm_sq (c_scale K (c_conj d))))
                 (real_mult nsq
                    (real_mult (real_mult K K) (c_norm_sq (c_conj d))))
                 (real_mult nsq (real_mult (real_mult K K) dsq))).
      * exact (RealSetoid.real_eq_mult_compat_adapt nsq nsq
                    (c_norm_sq (c_scale K (c_conj d)))
                    (real_mult (real_mult K K) (c_norm_sq (c_conj d)))
                    (real_eq_refl nsq)
                    (gaC12_scale_norm K (c_conj d))).
      * exact (RealSetoid.real_eq_mult_compat_adapt nsq nsq
                    (real_mult (real_mult K K) (c_norm_sq (c_conj d)))
                    (real_mult (real_mult K K) dsq)
                    (real_eq_refl nsq)
                    (RealSetoid.real_eq_mult_compat_adapt (real_mult K K) (real_mult K K)
                       (c_norm_sq (c_conj d)) dsq
                       (real_eq_refl (real_mult K K))
                       (gaC12_norm_conj_sq d))).
  - apply (real_eq_trans
               (real_mult nsq (real_mult (real_mult K K) dsq))
               (real_mult nsq (real_mult K real_one))
               (real_mult nsq K)).
    + apply (real_eq_trans
                 (real_mult nsq (real_mult (real_mult K K) dsq))
                 (real_mult nsq (real_mult K (real_mult K dsq)))
                 (real_mult nsq (real_mult K real_one))).
      * exact (RealSetoid.real_eq_mult_compat_adapt nsq nsq
                    (real_mult (real_mult K K) dsq)
                    (real_mult K (real_mult K dsq))
                    (real_eq_refl nsq)
                    (real_eq_sym _ _ (real_mult_assoc K K dsq))).
      * exact (RealSetoid.real_eq_mult_compat_adapt nsq nsq
                    (real_mult K (real_mult K dsq))
                    (real_mult K real_one)
                    (real_eq_refl nsq)
                    (RealSetoid.real_eq_mult_compat_adapt K K (real_mult K dsq) real_one
                       (real_eq_refl K)
                       (mm_inv_mul_one dsq Hq))).
    + exact (RealSetoid.real_eq_mult_compat_adapt nsq nsq (real_mult K real_one) K
                (real_eq_refl nsq) (real_mult_one K)).
Qed.

(* == Section 3. The annulus step face.== *)
Lemma gaC12_le_mult_compat : forall (c x y : Real)
    (Hc : real_lt real_zero c),
  real_le x y -> real_le (real_mult c x) (real_mult c y).
Proof.
  intros c x y Hc Hxy. unfold real_le in Hxy.
  destruct Hxy as [Hlt | Heq].
  - apply (real_lt_le_iff (real_mult c x) (real_mult c y)). left.
    exact (real_lt_mult_compat x y c Hc Hlt).
  - right. exact (RealSetoid.real_eq_mult_compat_adapt c c x y (real_eq_refl c) Heq).
Qed.
Lemma gaC12_two_add_four : forall B : Real,
  real_eq (real_mult (real_const 2) (real_plus B B))
          (real_mult (real_const 4) B).
Proof.
  intro B. apply real_eq_of_zero_diff. intro n.
  destruct B as [bq Hbq].
  cbn [projT1 real_mult real_plus real_const]. ring.
Qed.
Lemma gaC12_step_circle_bound :
  forall (g g1 : Cx -> Cx) (z0 : Cx) (R B : Real)
    (HR : real_lt real_zero R)
    (Hnn : forall v : Cx, real_le real_zero (c_norm_sq v))
    (HB : boundary_bounded g z0 R B)
    (HG0 : real_le (c_norm_sq (g z0)) B)
    (Hdiff : forall (q : Cx)
               (Hq : real_lt real_zero (c_norm_sq (c_plus q (c_opp z0)))),
               c_eq (g1 q) (gaC12_cx_dquot g z0 q Hq)),
  boundary_bounded g1 z0 R
    (real_mult (real_const 4)
       (real_mult B
          (real_inv_pos (real_mult R R) (real_mult_positive R R HR HR)))).
Proof.
  intros g g1 z0 R B HR Hnn HB HG0 Hdiff q Hbq.
  unfold boundary_bounded in HB.
  set (d := c_plus q (c_opp z0)) in *.
  set (dq := c_norm_sq d) in *.
  set (num := c_plus (g q) (c_opp (g z0))) in *.
  set (nsq := c_norm_sq num) in *.
  set (KR := real_inv_pos (real_mult R R) (real_mult_positive R R HR HR)).
  assert (Hdpos : real_lt real_zero dq)
    by exact (gaC12_boundary_dpos q z0 R Hbq HR).
  assert (Hg1q : real_eq (c_norm_sq (g1 q)) (c_norm_sq (gaC12_cx_dquot g z0 q Hdpos)))
    by exact (mm_norm_wd (g1 q) (gaC12_cx_dquot g z0 q Hdpos) (Hdiff q Hdpos)).
  pose proof (gaC12_dquot_norm_sq g z0 q Hdpos) as Hdn.
  assert (Hnum : real_le nsq (real_mult (real_const 4) B)).
  { apply (real_le_trans nsq
             (real_mult (real_const 2) (real_plus (c_norm_sq (g q)) (c_norm_sq (g z0))))
             (real_mult (real_const 4) B)).
    - apply (real_le_trans nsq
               (real_mult (real_const 2)
                  (real_plus (c_norm_sq (g q)) (c_norm_sq (c_opp (g z0)))))
               (real_mult (real_const 2)
                  (real_plus (c_norm_sq (g q)) (c_norm_sq (g z0))))).
      + exact (gaC12_sq_le_2sum Hnn (g q) (c_opp (g z0))).
      + apply RealSetoid.real_eq_le.
        exact (RealSetoid.real_eq_mult_compat_adapt (real_const 2)
                   (real_const 2)
                   (real_plus (c_norm_sq (g q)) (c_norm_sq (c_opp (g z0))))
                   (real_plus (c_norm_sq (g q)) (c_norm_sq (g z0)))
                   (real_eq_refl (real_const 2))
                   (RealSetoid.real_eq_plus_compat (c_norm_sq (g q))
                      (c_norm_sq (c_opp (g z0)))
                      (c_norm_sq (g q)) (c_norm_sq (g z0))
                      (real_eq_refl (c_norm_sq (g q)))
                      (gaC12_norm_opp_sq (g z0)))).
    - apply (real_le_trans
               (real_mult (real_const 2) (real_plus (c_norm_sq (g q)) (c_norm_sq (g z0))))
               (real_mult (real_const 2) (real_plus B B))
               (real_mult (real_const 4) B)).
      + exact (gaC12_le_mult_compat (real_const 2)
                  (real_plus (c_norm_sq (g q)) (c_norm_sq (g z0)))
                  (real_plus B B) gaC12_two_pos
                  (real_le_plus_compat (c_norm_sq (g q)) B
                     (c_norm_sq (g z0)) B (HB q Hbq) HG0)).
      + apply RealSetoid.real_eq_le. exact (gaC12_two_add_four B). }
  set (Kd := real_inv_pos dq Hdpos) in *.
  assert (HinvR : real_eq Kd KR)
    by exact (gaC12_inv_wd dq (real_mult R R) Hdpos
                (real_mult_positive R R HR HR) Hbq).
  apply (real_le_trans (c_norm_sq (g1 q))
           (real_mult nsq Kd)
           (real_mult (real_const 4) (real_mult B KR))).
  - apply RealSetoid.real_eq_le.
    exact (real_eq_trans _ _ _ Hg1q Hdn).
  - apply (real_le_trans (real_mult nsq Kd)
             (real_mult (real_mult (real_const 4) B) Kd)
             (real_mult (real_const 4) (real_mult B KR))).
    + exact (RealSetoid.real_le_compat (real_mult Kd nsq) (real_mult nsq Kd)
                (real_mult Kd (real_mult (real_const 4) B)) (real_mult (real_mult (real_const 4) B) Kd)
                (real_mult_comm Kd nsq) (real_mult_comm Kd (real_mult (real_const 4) B))
                (gaC12_le_mult_compat Kd nsq (real_mult (real_const 4) B) (real_inv_pos_pos dq Hdpos) Hnum)).
    + apply RealSetoid.real_eq_le.
      apply (real_eq_trans
                 (real_mult (real_mult (real_const 4) B) Kd)
                 (real_mult (real_const 4) (real_mult B Kd))
                 (real_mult (real_const 4) (real_mult B KR))).
      * exact (real_eq_sym _ _ (real_mult_assoc (real_const 4) B Kd)).
      * exact (RealSetoid.real_eq_mult_compat_adapt (real_const 4) (real_const 4)
                    (real_mult B Kd) (real_mult B KR)
                    (real_eq_refl (real_const 4))
                    (RealSetoid.real_eq_mult_compat_adapt B B Kd KR (real_eq_refl B) HinvR)).
Qed.

(* == Section 4. The recursion constant faces and the Cn samples.== *)
Lemma gaC12_Cn_S_sq : forall k : nat,
  real_eq (gaC12_sq (gaC12_Cn (S k)))
          (real_mult (real_const 4) (gaC12_sq (gaC12_Cn k))).
Proof.
  intro k. cbn [gaC12_Cn].
  apply (real_eq_trans
           (gaC12_sq (real_mult (real_const 2) (gaC12_Cn k)))
           (real_mult (real_mult (real_const 2) (real_const 2))
              (gaC12_sq (gaC12_Cn k)))
           (real_mult (real_const 4) (gaC12_sq (gaC12_Cn k)))).
  - exact (gaC12_sq_prod (real_const 2) (gaC12_Cn k)).
  - apply real_eq_of_zero_diff. intro n.
    destruct (gaC12_Cn k) as [cq Hcq].
    cbn [projT1 gaC12_sq real_mult real_const]. ring.
Qed.
Lemma gaC12_rdiv_S : forall (k : nat) (M R : Real)
    (HR : real_lt real_zero R)
    (HRk : real_lt real_zero (gaC12_rnatpow R k))
    (HRk1 : real_lt real_zero (gaC12_rnatpow R (S k))),
  real_eq (gaC12_rdiv M (gaC12_rnatpow R (S k)) HRk1)
          (real_mult (gaC12_rdiv M (gaC12_rnatpow R k) HRk)
                     (real_inv_pos R HR)).
Proof.
  intros k M R HR HRk HRk1.
  unfold gaC12_rdiv. cbn [gaC12_rnatpow].
  assert (Hwd : real_eq
                  (real_inv_pos (real_mult (gaC12_rnatpow R k) R) HRk1)
                  (real_inv_pos (real_mult (gaC12_rnatpow R k) R)
                     (real_mult_positive (gaC12_rnatpow R k) R HRk HR)))
    by exact (gaC12_inv_wd (real_mult (gaC12_rnatpow R k) R)
               (real_mult (gaC12_rnatpow R k) R) HRk1
               (real_mult_positive (gaC12_rnatpow R k) R HRk HR)
               (real_eq_refl (real_mult (gaC12_rnatpow R k) R))).
  apply (real_eq_trans
           (real_mult M (real_inv_pos (real_mult (gaC12_rnatpow R k) R) HRk1))
           (real_mult M (real_mult (real_inv_pos (gaC12_rnatpow R k) HRk)
                              (real_inv_pos R HR)))
           (real_mult (real_mult M (real_inv_pos (gaC12_rnatpow R k) HRk))
                      (real_inv_pos R HR))).
  - exact (RealSetoid.real_eq_mult_compat_adapt M M
              (real_inv_pos (real_mult (gaC12_rnatpow R k) R) HRk1)
              (real_mult (real_inv_pos (gaC12_rnatpow R k) HRk)
                 (real_inv_pos R HR))
              (real_eq_refl M)
              (real_eq_trans (real_inv_pos (real_mult (gaC12_rnatpow R k) R) HRk1)
                 (real_inv_pos (real_mult (gaC12_rnatpow R k) R)
                    (real_mult_positive (gaC12_rnatpow R k) R HRk HR))
                 (real_mult (real_inv_pos (gaC12_rnatpow R k) HRk)
                    (real_inv_pos R HR))
                 Hwd
                 (gaC12_inv_mult (gaC12_rnatpow R k) R HRk HR))).
  - apply real_eq_of_zero_diff. intro n.
    destruct (real_inv_pos (gaC12_rnatpow R k) HRk) as [ik Hik].
    destruct (real_inv_pos R HR) as [ir Hir].
    destruct M as [mq Hmq].
    cbn [projT1 real_mult]. ring.
Qed.
Lemma gaC12_cert_cn1 : real_eq (gaC12_Cn 1%nat) (real_const 2).
Proof.
  cbn [gaC12_Cn].
  exact (real_mult_one (real_const 2)).
Qed.
Lemma gaC12_cert_cn2 : real_eq (gaC12_Cn 2%nat) (real_const 4).
Proof.
  cbn [gaC12_Cn].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const real_one]. ring.
Qed.
Lemma gaC12_cert_cn4 : real_eq (gaC12_Cn 4%nat) (real_const 16).
Proof.
  cbn [gaC12_Cn].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const real_one]. ring.
Qed.
