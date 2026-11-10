(* ConstructiveWorld-Main - the second-order difference-quotient base
   piece: the centered Cauchy face of the quotient machine. *)

(** * GaC2_12_CauchyCoeffEst_c: the second-order difference-quotient
      base piece.

    Mission.  Node C2-12 machine cluster, piece c.  Defines the
      complex difference quotient [gaC12_cx_dquot] of [f] between
      [z0] and a point [q] whose squared distance is explicitly
      positive (Set-carried division: numerator times [conj(q - z0)]
      times [real_inv_pos] of the squared distance).  Casts the
      distance-positivity transfer [gaC12_dquot_pos], the remainder
      well-definedness face [gaC12_rem_wd], the value face
      [gaC12_dquot_value_eq] (the quotient at [z0+w] minus the
      first-order coefficient equals the second-order remainder of
      [f] carried by [conj w] over the squared distance), and the
      main statement [gaC12_dquot_center_T2]: if the second-order
      remainder of [f] at [z0] is bounded by [T2] at [w], then the
      squared modulus of the difference quotient minus [a1] is
      bounded by [T2] itself - the centered Cauchy face by which
      the second-order data of [f] becomes the first-order slot of
      the quotient.  Set-carried throughout; zero Sections.

    Dependencies.  Stdlib [QArith.QArith], [Lia].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S03_QExp]
      ([real_inv_pos] with its correctness and positivity faces),
      [S07_RealSetoidExpLog] (the Setoid compatibility and order
      faces), [CxRealPairCore], [CxRealPairExpLog]
      ([c_plus_congr]/[c_opp_congr]/[c_mult_congr]),
      [GaC1_Iface_Cx], [GaC1_Iface_Real], the machine cluster
      [GaC2_11_MaxModulusDisk_a] (the [mm_*] algebra kit:
      [mm_norm_wd]/[mm_norm_scale]/[mm_c_mult_scale]/
      [mm_c_scale_scale]/[mm_c_scale_wd]/[mm_c_eq_scale_wd]/
      [mm_inv_mul_one]/[mm_mult_one_l]), this cluster's pieces a
      and b ([GaC2_12_CauchyCoeffEst_a] for the gaC12 algebra
      prefixes, [GaC2_12_CauchyCoeffEst_b] for the algebra faces
      and [gaC12_cauchy_cancel]).

    References.  drafts_C2.md C2.12 card (the difference-quotient
      route: g = (f - f(z0))/(z - z0) is disk-expandable with
      g(z0) = f'(z0), and the circle bound 2M/R is pushed through
      C2-11) and the GaC2_12 seat forensics registered in SOP
      section 2 (C2-11 L14 packs only a0/a1/Tmaj; the
      difference-quotient expandability needs second-order data,
      which the Tmaj quadratic face supplies).  This piece is the
      center face of that route; the full-disk face and the annulus
      recursion land in later pieces of this cluster.  Ahlfors Ch.2
      the classical quotient argument (statement architecture only;
      no proof object transcribed).

    Constructivity.  All statements are Set-sorted; the nonzero
      distance enters only through the explicit
      [real_lt real_zero (c_norm_sq ...)] witness [Hq] and its
      [real_inv_pos] carrier; the order chain runs through
      monotone faces only; no Section wrappers, no premise slots, zero
      assumed constants, zero admitted goals; every proof closes under
      the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_c.v] from the flat
      build directory; acceptance via 50_toolkit/accept_node.py
      (six-chain gate), thermal-guard wrapped. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_11_MaxModulusDisk_a.
Require Import GaC2_12_CauchyCoeffEst_a.
Require Import GaC2_12_CauchyCoeffEst_b.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(* Section 1. The difference quotient and the plumbing faces.            *)
(* ===================================================================== *)

Definition gaC12_cx_dquot (f : Cx -> Cx) (z0 q : Cx)
           (Hq : real_lt real_zero (c_norm_sq (c_plus q (c_opp z0)))) : Cx :=
  c_mult (c_plus (f q) (c_opp (f z0)))
         (c_scale (real_inv_pos (c_norm_sq (c_plus q (c_opp z0))) Hq)
                  (c_conj (c_plus q (c_opp z0)))).

Lemma gaC12_dquot_pos : forall (z0 w : Cx),
  real_lt real_zero (c_norm_sq w) ->
  real_lt real_zero (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))).
Proof.
  intros z0 w Hw.
  apply (real_lt_eq_lt real_zero (c_norm_sq w)
           (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))).
  - exact Hw.
  - exact (mm_norm_wd w (c_plus (c_plus z0 w) (c_opp z0))
             (c_eq_sym _ _ (gaC12_shift_eq z0 w))).
Qed.

Lemma gaC12_rem_wd : forall (f : Cx -> Cx) (z0 w a0 a1 : Cx),
  c_eq a0 (f z0) ->
  c_eq (c_plus (c_plus (f (c_plus z0 w)) (c_opp a0)) (c_opp (c_mult a1 w)))
       (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
               (c_opp (c_mult a1 w))).
Proof.
  intros f z0 w a0 a1 Ha0.
  apply c_plus_congr.
  - apply c_plus_congr.
    + apply c_eq_refl.
    + apply c_opp_congr. exact Ha0.
  - apply c_eq_refl.
Qed.

(* ===================================================================== *)
(* Section 2. The value face.                                            *)
(* ===================================================================== *)

Lemma gaC12_dquot_value_eq :
  forall (f : Cx -> Cx) (z0 w a1 : Cx)
         (Hq : real_lt real_zero (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))),
  c_eq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1))
       (c_scale (real_inv_pos (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) Hq)
                (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                (c_opp (c_mult a1 w)))
                        (c_conj w))).
Proof.
  intros f z0 w a1 Hq.
  unfold gaC12_cx_dquot.
  remember (c_plus (c_plus z0 w) (c_opp z0)) as d eqn:Hddef.
  remember (real_inv_pos (c_norm_sq d) Hq) as K eqn:HKeq.
  assert (Hinv : real_eq (real_mult K (c_norm_sq d)) real_one).
  { rewrite HKeq. exact (mm_inv_mul_one (c_norm_sq d) Hq). }
  assert (Hshift : c_eq d w).
  { rewrite Hddef. exact (gaC12_shift_eq z0 w). }
  assert (Hconj : c_eq (c_conj d) (c_conj w)) by exact (gaC12_conj_wd _ _ Hshift).
  assert (H1 : c_eq (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                            (c_scale K (c_conj d)))
                    (c_scale K (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                       (c_conj d))))
    by exact (mm_c_mult_scale _ K _).
  assert (HA : c_eq (c_opp a1) (c_scale K (c_scale (c_norm_sq d) (c_opp a1)))).
  { apply (c_eq_trans (c_opp a1) (c_scale real_one (c_opp a1))
                      (c_scale K (c_scale (c_norm_sq d) (c_opp a1)))).
    - apply c_eq_sym. exact (gaC12_scale_one (c_opp a1)).
    - apply (c_eq_trans _ (c_scale (real_mult K (c_norm_sq d)) (c_opp a1))).
      + apply mm_c_eq_scale_wd. exact (real_eq_sym _ _ Hinv).
      + apply c_eq_sym. exact (mm_c_scale_scale K (c_norm_sq d) (c_opp a1)). }
  assert (HB : c_eq (c_plus (c_scale K (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0))) (c_conj d)))
                            (c_scale K (c_scale (c_norm_sq d) (c_opp a1))))
                    (c_scale K (c_plus (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0))) (c_conj d))
                                       (c_scale (c_norm_sq d) (c_opp a1))))).
  { apply c_eq_sym. apply gaC12_scale_plus. }
  assert (HC : c_eq (c_plus (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0))) (c_conj d))
                            (c_scale (c_norm_sq d) (c_opp a1)))
                    (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                    (c_opp (c_mult a1 d)))
                            (c_conj d)))
    by exact (gaC12_quot_ringC _ _ _).
  assert (HD : c_eq (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                    (c_opp (c_mult a1 d)))
                            (c_conj d))
                    (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                    (c_opp (c_mult a1 w)))
                            (c_conj w))).
  { apply c_mult_congr.
    - apply c_plus_congr.
      + apply c_eq_refl.
      + apply c_opp_congr.
        apply c_mult_congr; [apply c_eq_refl | exact Hshift].
    - exact Hconj. }
  exact (c_eq_trans
           (c_plus (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                           (c_scale K (c_conj d)))
                   (c_opp a1))
           (c_scale K (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                      (c_opp (c_mult a1 d)))
                              (c_conj d)))
           (c_scale K (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                      (c_opp (c_mult a1 w)))
                              (c_conj w)))
           (c_eq_trans
              (c_plus (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                              (c_scale K (c_conj d)))
                      (c_opp a1))
              (c_plus (c_scale K (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                         (c_conj d)))
                      (c_scale K (c_scale (c_norm_sq d) (c_opp a1))))
              (c_scale K (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                         (c_opp (c_mult a1 d)))
                                 (c_conj d)))
              (c_plus_congr _ _ _ _ H1 HA)
              (c_eq_trans
                 (c_plus (c_scale K (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                            (c_conj d)))
                         (c_scale K (c_scale (c_norm_sq d) (c_opp a1))))
                 (c_scale K (c_plus (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                            (c_conj d))
                                    (c_scale (c_norm_sq d) (c_opp a1))))
                 (c_scale K (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                            (c_opp (c_mult a1 d)))
                                    (c_conj d)))
                 HB
                 (mm_c_scale_wd K
                    (c_plus (c_mult (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                    (c_conj d))
                            (c_scale (c_norm_sq d) (c_opp a1)))
                    (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                    (c_opp (c_mult a1 d)))
                            (c_conj d))
                    HC)))
           (mm_c_scale_wd K
              (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                              (c_opp (c_mult a1 d)))
                      (c_conj d))
              (c_mult (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                              (c_opp (c_mult a1 w)))
                      (c_conj w))
              HD)).
Qed.

(* ===================================================================== *)
(* Section 3. The centered Cauchy face.                                  *)
(* ===================================================================== *)

Lemma gaC12_dquot_center_T2 :
  forall (f : Cx -> Cx) (z0 w a1 : Cx) (T2 : Real)
         (Hq : real_lt real_zero (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))))
         (Hrem : real_le (c_norm_sq (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                            (c_opp (c_mult a1 w))))
                         (real_mult (c_norm_sq w) T2)),
  real_le (c_norm_sq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1))) T2.
Proof.
  intros f z0 w a1 T2 Hq Hrem.
  assert (Haux : forall (K : Real) (E : Cx),
           K = real_inv_pos (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) Hq ->
           E = c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0))) (c_opp (c_mult a1 w)) ->
           real_le (c_norm_sq (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0)))
                                      (c_opp (c_mult a1 w))))
                   (real_mult (c_norm_sq w) T2) ->
           real_le (c_norm_sq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1))) T2).
  { intros K E HKeq Hedef HremQ.
    assert (Hinv : real_eq (real_mult K
                               (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))))
                          real_one).
    { rewrite HKeq.
      exact (mm_inv_mul_one (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) Hq). }
    assert (Hve : c_eq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1))
                       (c_scale K (c_mult E (c_conj w)))).
    { rewrite Hedef. rewrite HKeq.
      exact (gaC12_dquot_value_eq f z0 w a1 Hq). }
    assert (Hs : real_eq (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) (c_norm_sq w)).
    { exact (mm_norm_wd (c_plus (c_plus z0 w) (c_opp z0)) w (gaC12_shift_eq z0 w)). }
    assert (Hn : real_eq
                   (c_norm_sq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1)))
                   (real_mult (real_mult K K)
                      (real_mult (c_norm_sq E)
                                 (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))).
    { apply (real_eq_trans _
               (c_norm_sq (c_scale K (c_mult E (c_conj w))))).
      - exact (mm_norm_wd _ _ Hve).
      - apply (real_eq_trans _
                 (real_mult (real_mult K K) (c_norm_sq (c_mult E (c_conj w))))).
        + exact (mm_norm_scale K (c_mult E (c_conj w))).
        + apply RealSetoid.real_eq_mult_compat.
          * apply real_eq_refl.
          * apply (real_eq_trans _
                     (real_mult (c_norm_sq E) (c_norm_sq (c_conj w)))).
            -- exact (c_norm_sq_mul E (c_conj w)).
            -- apply RealSetoid.real_eq_mult_compat.
               ++ apply real_eq_refl.
               ++ exact (real_eq_trans (c_norm_sq (c_conj w)) (c_norm_sq w)
                            (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))
                            (c_norm_sq_conj w) (real_eq_sym _ _ Hs)). }
    assert (Hbound : real_le (c_norm_sq E)
                               (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))
                                          T2)).
    { rewrite <- Hedef in HremQ.
      apply (real_le_trans (c_norm_sq E)
                 (real_mult (c_norm_sq w) T2)
                 (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)).
      - exact HremQ.
      - apply RealSetoid.real_eq_le.
        exact (RealSetoid.real_eq_mult_compat
                 (c_norm_sq w) T2
                 (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2
                 (real_eq_sym (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))
                              (c_norm_sq w) Hs)
                 (real_eq_refl T2)). }
    assert (HKpos : real_lt real_zero K).
    { rewrite HKeq.
      exact (real_inv_pos_pos (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) Hq). }
    assert (HK2spos : real_lt real_zero
                        (real_mult (real_mult K K)
                                   (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))))).
    { apply real_mult_positive.
      - apply real_mult_positive; exact HKpos.
      - exact Hq. }
    assert (Hc : real_le real_zero
                   (real_mult (real_mult K K)
                              (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
      by exact (real_lt_le_iff real_zero _ (inl HK2spos)).
    assert (Hle : real_le
                    (real_mult (c_norm_sq E)
                               (real_mult (real_mult K K)
                                          (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                    (real_mult (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)
                               (real_mult (real_mult K K)
                                          (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))))))
      by exact (real_le_mult_compat_weak _ _ _ Hc Hbound).
    assert (HLalign : real_eq
                        (real_mult (real_mult K K)
                                   (real_mult (c_norm_sq E)
                                              (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                        (real_mult (c_norm_sq E)
                                   (real_mult (real_mult K K)
                                              (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))).
    { apply (real_eq_trans
               (real_mult (real_mult K K)
                          (real_mult (c_norm_sq E)
                                     (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
               (real_mult (real_mult K K)
                          (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))
                                     (c_norm_sq E)))).
      - apply RealSetoid.real_eq_mult_compat.
        + apply real_eq_refl.
        + exact (real_mult_comm (c_norm_sq E)
                   (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))).
      - apply (real_eq_trans
                 (real_mult (real_mult K K)
                            (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))
                                       (c_norm_sq E)))
                 (real_mult (real_mult (real_mult K K)
                                       (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))))
                            (c_norm_sq E))).
        + exact (real_mult_assoc (real_mult K K)
                   (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) (c_norm_sq E)).
        + exact (real_mult_comm (real_mult (real_mult K K)
                  (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))))
                 (c_norm_sq E)). }
    assert (HRcancel : real_eq
                         (real_mult (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)
                                    (real_mult (real_mult K K)
                                               (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                         T2)
      by exact (gaC12_cauchy_cancel
                  (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) K T2 Hq Hinv).
    exact (real_le_trans
             (c_norm_sq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1)))
             (real_mult (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)
                        (real_mult (real_mult K K)
                                   (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
             T2
             (real_le_trans
                (c_norm_sq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1)))
                (real_mult (real_mult K K)
                           (real_mult (c_norm_sq E)
                                      (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                (real_mult (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)
                           (real_mult (real_mult K K)
                                      (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                (RealSetoid.real_eq_le
                   (c_norm_sq (c_plus (gaC12_cx_dquot f z0 (c_plus z0 w) Hq) (c_opp a1)))
                   (real_mult (real_mult K K)
                              (real_mult (c_norm_sq E)
                                         (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                   Hn)
                (real_le_trans
                   (real_mult (real_mult K K)
                              (real_mult (c_norm_sq E)
                                         (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                   (real_mult (c_norm_sq E)
                              (real_mult (real_mult K K)
                                         (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                   (real_mult (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)
                              (real_mult (real_mult K K)
                                         (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                   (RealSetoid.real_eq_le
                      (real_mult (real_mult K K)
                                 (real_mult (c_norm_sq E)
                                            (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                      (real_mult (c_norm_sq E)
                                 (real_mult (real_mult K K)
                                            (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                      HLalign)
                   Hle))
             (RealSetoid.real_eq_le
                (real_mult (real_mult (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) T2)
                           (real_mult (real_mult K K)
                                      (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0)))))
                T2
                HRcancel)). }
  exact (Haux (real_inv_pos (c_norm_sq (c_plus (c_plus z0 w) (c_opp z0))) Hq)
              (c_plus (c_plus (f (c_plus z0 w)) (c_opp (f z0))) (c_opp (c_mult a1 w)))
              eq_refl eq_refl Hrem).
Qed.
