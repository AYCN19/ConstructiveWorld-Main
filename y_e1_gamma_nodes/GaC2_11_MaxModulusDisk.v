(* ConstructiveWorld-Main - the maximum-modulus disk statements: the explicit growth
   direction and the pointwise converse face. *)

(** * GaC2_11_MaxModulusDisk: maximum modulus on a disk, power-series growth route without
      integration or compactness.

    Mission.  Node C2-11 (segment C2, slot W2), statement piece.  Carrier [local_exp_disk]
      packs a local first-order expansion of [f] with explicit quadratic remainder control at
      every point of the closed disk; [deriv1] projects the first-order coefficient.  Growth
      lemma and pointwise maximum-modulus statements (full faces in the Notes block); two
      named Set-carried interface premises [Hrevtri] / [Hgrow_chain] disclosed there too.
    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires [S01_BaseRing] (selective
      [NatLe] import), [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [CxRealPairCore], [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC1_Iface_Real] (C1-04
      rational bridge, C1-05 square root faces), [GaC2_01_DirichletPartialSum], and the
      machine clusters [GaC2_11_MaxModulusDisk_a] through [GaC2_11_MaxModulusDisk_f] of this
      node (order, norm, alignment, radius, theta, and bridge kernel faces consumed by the
      two statements).
    References.  drafts_C2.md C2.11 statement sketch, three registered adaptations (i)-(iii)
      - adaptive radius [rho <= R/2] witnessed jointly with [w] for the sketch exact-R/2
      direction, squared closed form for the sketch absolute constant c, tree-native
      [real_lt real_zero] for the sketch token [eps_lb] (full clauses in the Notes block);
      Ahlfors Ch.2, statement architecture only.
    Constructivity.  Every named construction is carried by [Set]; the order predicates are
      the Set-sorted [real_lt] / [real_le]; the interface premises are discharged as explicit
      arguments at the section close (gap-carrier form, monotonically shrinkable); order
      facts propagate from strict-positivity premises through monotone faces only; zero
      assumed constants; every proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> "" -Q <build dir> ""
      GaC2_11_MaxModulusDisk.v] from the flat build directory, thermal guard wrapper. *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_11_MaxModulusDisk_c.
Require Import GaC2_11_MaxModulusDisk_d.
Require Import GaC2_11_MaxModulusDisk_e.
Require Import GaC2_11_MaxModulusDisk_f.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* Notes.  Disclosure text continued from the header.

    Statement faces.  [growth_lemma] - given [f z0] and the first-order coefficient [a1]
      both explicitly bounded away from zero, an explicit radius [rho] (at most half of
      [R], chosen adaptively against the packed remainder scale) and an explicit direction
      witness [w] with [c_norm_sq w = rho * rho] such that the squared modulus of [f] at
      [z0 + w] dominates the closed form [(|f z0| + rho * tau)^2] with
      [tau = |f z0| |a1| / (|f z0| + (R/4) |a1|)].  [max_modulus_pointwise] - any interior
      point value is bounded by the boundary bound up to the squared margin.

    Honest interface disclosure (both premises Set-carried): [Hrevtri], the reverse
      triangle of the complex norm in squared-carrier data (the pending Cx-norm geometry
      machine), and [Hgrow_chain], the explicit chain-walk contract stated against the
      requested margin (the pending segment-chain machine; its discharge is the walk with
      explicit step count and gain product).

    Registered adaptations of the drafts_C2.md C2.11 statement sketch: (i) the sketch
      direction of modulus exactly R/2 is realized as the adaptive radius [rho <= R/2]
      witnessed jointly with [w], the exact-R/2 form being incompatible with the packed
      quadratic remainder face; (ii) the sketch gain form with the absolute constant c is
      realized as the squared closed form [|f z0| + rho |f z0| |a1| / (|f z0| + (R/4)|a1|)]
      with [rho <= R/2] explicit; (iii) the sketch token [eps_lb] is realized by the
      tree-native [real_lt real_zero] form whose witness carries the explicit lower-bound
      pair.

    Carrier-shape obligation: the [local_exp_disk] and [deriv1] carrier shapes are the L14
      obligation form, subject to the wave-end cross-check; the direction witness is
      carried by the [growth_lemma] witness term itself.

    Reference.  Ahlfors Ch.2, the classical first-order growth direction argument
      (statement architecture only; no proof object transcribed). *)


(* Section 1. The disk carriers. *)

Definition closed_disk (z c : Cx) (R : Real) : Set :=
  real_le (c_norm_sq (c_plus z (c_opp c))) (real_mult R R).

Definition boundary (q c : Cx) (R : Real) : Set :=
  real_eq (c_norm_sq (c_plus q (c_opp c))) (real_mult R R).

Definition boundary_bounded (g : Cx -> Cx) (c : Cx) (R M_sq : Real) : Set :=
  forall q : Cx, boundary q c R -> real_le (c_norm_sq (g q)) M_sq.

(* Local first-order expansion with explicit quadratic remainder. *)
Definition local_exp_disk (g : Cx -> Cx) (c : Cx) (R : Real) : Set :=
  forall p : Cx, closed_disk p c R ->
    sigT (fun a0 : Cx => sigT (fun a1 : Cx => sigT (fun Tmaj : Real =>
      S01_BaseRing.And (c_eq a0 (g p))
      (S01_BaseRing.And (real_lt real_zero Tmaj)
           (forall w : Cx, real_le (c_norm_sq w) (real_mult R R) ->
             real_le (c_norm_sq (c_plus (c_plus (g (c_plus p w)) (c_opp a0))
                                        (c_opp (c_mult a1 w))))
                     (real_mult (real_mult (c_norm_sq w) (c_norm_sq w)) Tmaj)))))).

Definition deriv1 (g : Cx -> Cx) (p c : Cx) (R : Real)
           (Hl : local_exp_disk g c R) (Hp : closed_disk p c R) : Cx :=
  projT1 (projT2 (Hl p Hp)).

(* Section 2. Statement slots, slot-pure closed forms, interfaces. *)

Section MaxModulusDisk.

Variable f : Cx -> Cx.
Variable z0 : Cx.
Variable R : Real.
Hypothesis HR : real_lt real_zero R.
Variable Hloc : local_exp_disk f z0 R.
Variable a1 : Cx.
Hypothesis Hf0 : real_lt real_zero (c_norm_sq (f z0)).

Lemma mm_q4 : QltT 0 (1#4)%Q. Proof. reflexivity. Qed.
Lemma mm_q4pos : real_lt real_zero (real_const (4#1)%Q).
Proof. exact (gaC1_04_qlt_const_lt 0 (4#1)%Q mm_q4). Qed.
Lemma mm_q42 : QltT (1#4)%Q (1#2)%Q. Proof. reflexivity. Qed.
Lemma mm_q21 : QltT (1#2)%Q 1%Q. Proof. reflexivity. Qed.
Lemma mm_q2p : QltT 0 (2#1)%Q. Proof. reflexivity. Qed.
Lemma mm_q2pos : real_lt real_zero (real_const (2#1)%Q).
Proof. exact (gaC1_04_qlt_const_lt 0 (2#1)%Q mm_q2p). Qed.

Definition mm_m0 : Real := c_norm_sq (f z0).
Definition mm_m1 : Real := c_norm_sq a1.
Definition mm_s0 : Real := sqrtR mm_m0 Hf0.
Definition mm_Hs0 : real_lt real_zero mm_s0 := gaC1_05_kroot_pos 2 mm_m0 Hf0.
Definition mm_R4 : Real := real_mult (real_const (1#4)%Q) R.
Definition mm_R2 : Real := real_mult (real_const (1#2)%Q) R.

Definition mm_hdisk0 : closed_disk z0 z0 R :=
  real_le_trans (c_norm_sq (c_plus z0 (c_opp z0))) real_zero (real_mult R R)
    (RealSetoid.real_eq_le (c_norm_sq (c_plus z0 (c_opp z0))) real_zero
       (mm_norm_self_opp z0))
    (real_lt_le_iff real_zero (real_mult R R)
       (inl (real_mult_positive R R HR HR))).

Hypothesis Ha1 : S01_BaseRing.And (real_lt real_zero (c_norm_sq a1))
                     (c_eq a1 (deriv1 f z0 z0 R Hloc mm_hdisk0)).

Definition mm_Ha1pos : real_lt real_zero (c_norm_sq a1) := fst Ha1.
Definition mm_s1 : Real := sqrtR mm_m1 mm_Ha1pos.
Definition mm_Hs1 : real_lt real_zero mm_s1 := gaC1_05_kroot_pos 2 mm_m1 mm_Ha1pos.
Definition mm_den : Real := real_plus mm_s0 (real_mult mm_R4 mm_s1).
Definition mm_HR4 : real_lt real_zero mm_R4 :=
  real_eq_lt_lt real_zero (real_mult (real_const (1#4)%Q) real_zero)
    (real_mult (real_const (1#4)%Q) R)
    (real_eq_sym real_zero (real_mult (real_const (1#4)%Q) real_zero)
       (real_mult_zero (real_const (1#4)%Q)))
    (real_lt_mult_compat real_zero R (real_const (1#4)%Q)
       (gaC1_04_qlt_const_lt 0 (1#4)%Q mm_q4) HR).
Definition mm_Hden : real_lt real_zero mm_den :=
  real_lt_trans real_zero mm_s0 mm_den
    (gaC1_05_kroot_pos 2 mm_m0 Hf0)
    (mm_lt_plus_r mm_s0 (real_mult mm_R4 mm_s1)
       (real_mult_positive mm_R4 mm_s1 mm_HR4
          (gaC1_05_kroot_pos 2 mm_m1 mm_Ha1pos))).
Definition mm_invden : Real := real_inv_pos mm_den mm_Hden.
Definition mm_tau : Real :=
  real_mult (real_mult mm_s0 mm_s1) mm_invden.
(* Interface premise 1b (s0-inv-cancellation machine face). *)
Hypothesis Hs0_inv_cancel :
  real_eq (real_mult (real_mult mm_s0 mm_s1) (real_inv_pos mm_s0 mm_Hs0)) mm_s1.
Hypothesis Htau_lt_s1 : real_lt mm_tau mm_s1.

Definition mm_Htau : real_lt real_zero mm_tau :=
  real_mult_positive (real_mult mm_s0 mm_s1) mm_invden
    (real_mult_positive mm_s0 mm_s1
       (gaC1_05_kroot_pos 2 mm_m0 Hf0)
       (gaC1_05_kroot_pos 2 mm_m1 mm_Ha1pos))
    (real_inv_pos_pos mm_den mm_Hden).

(* Interface premise 1 (pending Cx-norm geometry machine). *)
Hypothesis Hrevtri : forall (u v : Cx) (su sv : Real),
  real_eq (real_mult su su) (c_norm_sq u) ->
  real_le real_zero su ->
  real_le real_zero sv ->
  real_le (c_norm_sq v) (real_mult sv sv) ->
  real_le (real_mult (real_plus su (real_opp sv)) (real_plus su (real_opp sv)))
          (c_norm_sq (c_plus u v)).

(* Interface premise 2 (pending segment-chain machine). *)
Hypothesis Hgrow_chain :
  forall (p : Cx) (dlt : Real), closed_disk p z0 R -> real_lt real_zero dlt ->
    sigT (fun q : Cx =>
      S01_BaseRing.And (boundary q z0 R)
          (real_le (c_norm_sq (f p))
                   (real_plus (c_norm_sq (f q)) (real_mult dlt dlt)))).

(* Section 3. The constructive main force: the growth direction. *)

Lemma growth_lemma :
  sigT (fun w : Cx => sigT (fun rho : Real =>
    S01_BaseRing.And (real_lt real_zero rho)
    (S01_BaseRing.And (real_eq (c_norm_sq w) (real_mult rho rho))
    (S01_BaseRing.And (real_le rho mm_R2)
         (real_le (real_mult (real_plus mm_s0
                                (real_mult (real_const (1#2)%Q)
                                           (real_mult rho mm_tau)))
                             (real_plus mm_s0
                                (real_mult (real_const (1#2)%Q)
                                           (real_mult rho mm_tau))))
                  (c_norm_sq (f (c_plus z0 w)))))))).
Proof.
  destruct Ha1 as [Ha1pos Ha1eq].
  unfold deriv1 in Ha1eq.
  destruct (Hloc z0 mm_hdisk0) as [a0 [a1p [Tmaj [Hval [HTmaj Hrem]]]]].
  cbn [projT1 projT2] in Ha1eq.
  assert (Ha1pq : c_eq a1 a1p) by exact Ha1eq.
  clear Ha1eq.
  assert (Hm1p : real_eq mm_m1 (c_norm_sq a1p))
    by (unfold mm_m1; exact (mm_norm_wd a1 a1p Ha1pq)).
  assert (Hs1 : real_lt real_zero mm_s1) by exact (gaC1_05_kroot_pos 2 mm_m1 mm_Ha1pos).
  assert (Hsq0 : real_eq (real_mult mm_s0 mm_s0) mm_m0) by exact (gaC1_05_sqrt_sq mm_m0 Hf0).
  assert (Hsq1 : real_eq (real_mult mm_s1 mm_s1) mm_m1) by exact (gaC1_05_sqrt_sq mm_m1 mm_Ha1pos).
  assert (Hss : real_lt real_zero (real_mult mm_s0 mm_s1))
    by exact (real_mult_positive mm_s0 mm_s1 mm_Hs0 Hs1).
  assert (HsqT : real_lt real_zero (sqrtR Tmaj HTmaj)) by exact (gaC1_05_kroot_pos 2 Tmaj HTmaj).
  assert (HTR4 : real_lt real_zero (real_mult mm_R4 (sqrtR Tmaj HTmaj)))
    by exact (real_mult_positive mm_R4 (sqrtR Tmaj HTmaj) mm_HR4 HsqT).
  assert (HT4 : real_lt real_zero
                  (real_mult (real_const (4#1)%Q) (real_mult mm_R4 (sqrtR Tmaj HTmaj))))
    by exact (real_mult_positive (real_const (4#1)%Q) (real_mult mm_R4 (sqrtR Tmaj HTmaj)) mm_q4pos HTR4).
  assert (Htau : real_lt real_zero mm_tau) by exact mm_Htau.
  destruct (mm_theta_kit mm_tau
              (real_inv_pos (real_mult (real_const (4#1)%Q)
                 (real_mult mm_R4 (sqrtR Tmaj HTmaj))) HT4) Htau
              (real_inv_pos_pos (real_mult (real_const (4#1)%Q)
                 (real_mult mm_R4 (sqrtR Tmaj HTmaj))) HT4))
    as [th [ivt [HthE [Hthp [Hivtp [Htu [Hivt1 Htule]]]]]]].
  set (rho := real_mult mm_R4 (real_mult th ivt)).
  destruct (mm_rho_faces R mm_R4 mm_R2 th ivt rho HR mm_HR4 Htu Hthp Hivtp
              (real_eq_refl (real_mult (real_const (1#4)%Q) R))
              (real_eq_refl (real_mult (real_const (1#2)%Q) R))
              (real_eq_refl (real_mult mm_R4 (real_mult th ivt))))
    as [Hrhop [Hrho_lt4 [Hr42 Hrho_le]]].
  set (ivss := real_inv_pos (real_mult mm_s0 mm_s1) Hss).
  set (ud := c_scale ivss (c_mult (c_conj a1p) a0)).
  destruct (mm_w_norm_faces a1p a0 rho mm_s0 mm_s1 mm_m0 mm_m1
              Hss Hsq0 Hsq1
              (real_eq_sym _ _ (mm_norm_wd a0 (f z0) Hval)) Hm1p)
    as [Hudone Hwnorm].
  set (w := c_scale rho ud).
  assert (Hwn : real_le (c_norm_sq w) (real_mult R R))
    by exact (real_lt_le_iff (c_norm_sq w) (real_mult R R)
           (inl (mm_w_in_disk (c_norm_sq w) rho mm_R2 R HR
                  (real_eq_refl (real_mult (real_const (1#2)%Q) R))
                  Hrhop (real_lt_trans rho mm_R4 mm_R2 Hrho_lt4 Hr42) Hwnorm))).
  set (kappa := real_mult rho (real_mult ivss mm_m1)).
  assert (Halign : c_eq (c_mult a1p w) (c_scale kappa a0))
    by exact (mm_align_face a1p a0 rho ivss mm_m1 Hm1p).
  set (X0 := c_plus a0 (c_mult a1p w)).
  assert (HX0 : real_eq (c_norm_sq X0)
             (real_plus mm_m0
                (real_plus (real_mult (real_const (2#1)%Q) (real_mult kappa mm_m0))
                           (real_mult (real_mult kappa kappa) mm_m0)))).
  { exact (mm_X0_norm a0 (c_mult a1p w) kappa mm_m0 Halign
             (mm_norm_wd a0 (f z0) Hval)). }
  assert (Hkp : real_lt real_zero kappa) by exact (real_mult_positive rho (real_mult ivss mm_m1) Hrhop (real_mult_positive ivss mm_m1 (real_inv_pos_pos (real_mult mm_s0 mm_s1) Hss) mm_Ha1pos)).
  assert (Hkm0 : real_lt real_zero (real_mult kappa mm_m0)) by exact (real_mult_positive kappa mm_m0 Hkp Hf0).
  assert (Hk2m0 : real_lt real_zero (real_mult (real_mult kappa kappa) mm_m0)) by exact (real_mult_positive (real_mult kappa kappa) mm_m0 (real_mult_positive kappa kappa Hkp Hkp) Hf0).
  assert (HX0pos : real_lt real_zero (c_norm_sq X0))
    by exact (real_lt_eq_lt real_zero
                (real_plus mm_m0
                   (real_plus (real_mult (real_const (2#1)%Q) (real_mult kappa mm_m0))
                      (real_mult (real_mult kappa kappa) mm_m0)))
                (c_norm_sq X0)
                (mm_X0_pos kappa mm_m0 Hkp Hf0) (real_eq_sym _ _ HX0)).
  set (su := sqrtR (c_norm_sq X0) HX0pos).
  assert (Hsu0 : real_le real_zero su) by exact (real_lt_le_iff real_zero su (inl (gaC1_05_kroot_pos 2 (c_norm_sq X0) HX0pos))).
  assert (Hsu2 : real_eq (real_mult su su) (c_norm_sq X0)) by exact (gaC1_05_sqrt_sq (c_norm_sq X0) HX0pos).
  set (A := real_plus mm_s0 (real_mult rho mm_tau)).
  assert (HAp : real_lt real_zero (real_mult rho mm_tau)) by exact (real_mult_positive rho mm_tau Hrhop Htau).
  assert (HApos : real_lt real_zero A) by exact (real_lt_trans real_zero mm_s0 A mm_Hs0 (mm_lt_plus_r mm_s0 (real_mult rho mm_tau) HAp)).
  assert (HA2pos : real_lt real_zero (real_mult A A)) by exact (real_mult_positive A A HApos HApos).
  assert (Hcore : real_lt (real_mult mm_s0 (real_mult rho mm_tau))
                    (real_mult rho (real_mult mm_s0 mm_s1)))
    by exact (mm_HT_shift mm_s0 rho mm_tau mm_s1 mm_Hs0 Hrhop Htau_lt_s1).
  assert (Htault : real_lt (real_mult mm_tau mm_tau) mm_m1)
    by exact (real_lt_eq_lt (real_mult mm_tau mm_tau) (real_mult mm_s1 mm_s1)
                mm_m1
                (mm_sq_strict_mono mm_tau mm_s1
                   (real_lt_le_iff real_zero mm_tau (inl Htau)) Htau_lt_s1)
                Hsq1).
  pose proof (mm_kappa_bridge kappa rho ivss mm_m1 mm_m0 mm_s0 mm_s1 Hss
                (real_eq_refl (real_mult rho (real_mult ivss mm_m1)))
                (real_eq_refl (real_inv_pos (real_mult mm_s0 mm_s1) Hss))
                Hsq0 Hsq1) as HkB.
  assert (HT2 : real_lt (real_mult (real_mult rho mm_tau) (real_mult rho mm_tau))
                  (real_mult (real_mult kappa kappa) mm_m0)).
  { apply (real_eq_lt_lt (real_mult (real_mult rho mm_tau) (real_mult rho mm_tau))
             (real_mult (real_mult rho rho) (real_mult mm_tau mm_tau))
             (real_mult (real_mult kappa kappa) mm_m0)).
    - exact (real_eq_sym _ _ (mm_ABAB rho mm_tau)).
    - exact (real_lt_eq_lt (real_mult (real_mult rho rho) (real_mult mm_tau mm_tau))
                (real_mult (real_mult rho rho) mm_m1)
                (real_mult (real_mult kappa kappa) mm_m0)
                (real_lt_mult_compat (real_mult mm_tau mm_tau) mm_m1
                   (real_mult rho rho)
                   (real_mult_positive rho rho Hrhop Hrhop) Htault)
                (real_eq_sym _ _ (snd HkB))). }
  assert (Hi1k1 : real_lt (real_mult (real_const (2#1)%Q)
                              (real_mult mm_s0 (real_mult rho mm_tau)))
                     (real_mult (real_const (2#1)%Q) (real_mult kappa mm_m0)))
    by exact (real_lt_mult_compat
                (real_mult mm_s0 (real_mult rho mm_tau))
                (real_mult kappa mm_m0) (real_const (2#1)%Q) mm_q2pos
                (real_lt_eq_lt (real_mult mm_s0 (real_mult rho mm_tau))
                   (real_mult rho (real_mult mm_s0 mm_s1))
                   (real_mult kappa mm_m0) Hcore (real_eq_sym _ _ (fst HkB)))).
  assert (HltX : real_lt (real_mult A A) (c_norm_sq X0)).
  { apply (mm_A2_lt_X0 (real_mult A A) mm_m0
             (real_mult (real_const (2#1)%Q) (real_mult kappa mm_m0))
             (real_mult (real_mult kappa kappa) mm_m0)
             (real_mult (real_const (2#1)%Q)
                (real_mult mm_s0 (real_mult rho mm_tau)))
             (real_mult (real_mult rho mm_tau) (real_mult rho mm_tau))
             (c_norm_sq X0)
             (mm_sq_expand mm_s0 (real_mult rho mm_tau) mm_m0 Hsq0)
             HX0 Hi1k1 HT2). }
  assert (HAlt : real_lt A su).
  { assert (HsuEqA : real_eq A (sqrtR (real_mult A A) HA2pos)).
    { exact (gaC1_05_sqrt_unique (real_mult A A) A (sqrtR (real_mult A A) HA2pos)
               HA2pos HApos
               (gaC1_05_kroot_pos 2 (real_mult A A) HA2pos)
               (real_eq_refl (real_mult A A))
               (gaC1_05_sqrt_sq (real_mult A A) HA2pos)). }
    exact (real_eq_lt_lt A (sqrtR (real_mult A A) HA2pos) su HsuEqA
             (mm_sqrt_lt_mono (real_mult A A) (c_norm_sq X0) HA2pos HX0pos HltX)). }
  set (sv := real_mult (real_mult rho rho) (sqrtR Tmaj HTmaj)).
  assert (Hsv0 : real_le real_zero sv) by exact (real_lt_le_iff real_zero sv (inl (real_mult_positive (real_mult rho rho) (sqrtR Tmaj HTmaj) (real_mult_positive rho rho Hrhop Hrhop) HsqT))).
  assert (Hsv2 : real_le (c_norm_sq
                            (c_plus (c_plus (f (c_plus z0 w)) (c_opp a0))
                               (c_opp (c_mult a1p w))))
                     (real_mult sv sv)).
  { exact (mm_rem_cap
             (c_plus (c_plus (f (c_plus z0 w)) (c_opp a0))
                (c_opp (c_mult a1p w)))
             w Tmaj rho (sqrtR Tmaj HTmaj) Hwnorm (Hrem w Hwn)
             (gaC1_05_sqrt_sq Tmaj HTmaj)). }
  pose proof (Hrevtri X0
                (c_plus (c_plus (f (c_plus z0 w)) (c_opp a0)) (c_opp (c_mult a1p w)))
                su sv Hsu2 Hsu0 Hsv0 Hsv2) as Hrev0.
  assert (Hdom : real_le (real_mult (real_plus su (real_opp sv))
                              (real_plus su (real_opp sv)))
                     (c_norm_sq (f (c_plus z0 w)))).
  { exact (mm_dom_face (f (c_plus z0 w)) a0 (c_mult a1p w)
              (real_plus su (real_opp sv)) Hrev0). }
  assert (Hrsq_half : real_lt (real_mult rho (sqrtR Tmaj HTmaj))
                              (real_mult (real_const (1#2)%Q) mm_tau)).
  { exact (mm_rsq_lt_half rho mm_R4 th ivt (sqrtR Tmaj HTmaj) mm_tau
              Hthp Hivt1 mm_HR4 HsqT mm_Htau HT4
              (real_eq_refl (real_mult mm_R4 (real_mult th ivt))) HthE). }
  set (Al := real_plus mm_s0 (real_mult (real_const (1#2)%Q) (real_mult rho mm_tau))).
  assert (Hleaf4 : real_le (real_mult Al Al)
                        (c_norm_sq (f (c_plus z0 w)))).
  { exact (mm_leaf4 mm_s0 rho mm_tau (sqrtR Tmaj HTmaj) su
              (c_norm_sq (f (c_plus z0 w)))
              Hrhop mm_Hs0 mm_Htau Hrsq_half HAp HAlt Hdom). }
  exists w. exists rho.
  exact (pair Hrhop (pair Hwnorm (pair Hrho_le Hleaf4))).
Qed.


(* Section 4. The pointwise converse face. *)

Lemma max_modulus_pointwise : forall (z : Cx) (delta : Real),
  closed_disk z z0 R -> real_lt real_zero delta ->
  forall M_sq : Real, boundary_bounded f z0 R M_sq ->
  real_le (c_norm_sq (f z)) (real_plus M_sq (real_mult delta delta)).
Proof.
  intros z delta Hzd Hdelta M_sq Hbb.
  destruct (Hgrow_chain z delta Hzd Hdelta) as [q [Hqb Hdom]].
  apply (real_le_trans (c_norm_sq (f z))
           (real_plus (c_norm_sq (f q)) (real_mult delta delta))
           (real_plus M_sq (real_mult delta delta))).
  - exact Hdom.
  - apply (mm_le_plus_compat (c_norm_sq (f q)) M_sq
               (real_mult delta delta) (real_mult delta delta)).
    + exact (Hbb q Hqb).
    + exact (real_le_refl (real_mult delta delta)).
Qed.

End MaxModulusDisk.
