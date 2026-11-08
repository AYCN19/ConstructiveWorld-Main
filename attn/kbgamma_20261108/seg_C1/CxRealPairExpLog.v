(* ConstructiveWorld-Main - the complex exponential and logarithm on the
   pair carrier, in polar form over the constructive real transcendental
   layer. *)

(** * CxRealPairExpLog: the complex exponential and logarithm on pairs.

    Mission.  The complex exponential and logarithm on the pair carrier
      [Cx] of [CxRealPairCore], in polar form through the constructive
      real exponential of [S03_QExp] and the real sine/cosine of
      [S10_KVQuantTrig]: the value at zero [c_exp_zero], the
      conjugation identity [c_exp_conj], the addition law
      [c_exp_plus], congruence of plus and opposite
      [c_plus_congr]/[c_opp_congr]/[c_mult_congr], a logarithm
      [c_log] whose branch is an explicit angle input, the round trip
      [c_exp_c_log], the multiplicative law [c_log_mult], and the zero
      characterization of the squared modulus
      [c_norm_sq_zero_intro]/[c_norm_sq_zero_elim].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith], [Setoid], [Morphisms], [Lia], [QArith.Qminmax].
      Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S07_RealSetoidExpLog], [S10_KVQuantTrig], and
      [CxRealPairCore] of this development.

    References.  This development, [S07_RealSetoidExpLog] and
      [S10_KVQuantTrig], the baseline modules in ConstructiveWorld-Main
      whose real addition formulas [rs_add_sin]/[rs_add_cos] and real
      logarithm [cw_log] are consumed here; the polar form and addition
      law of the complex exponential.  No classical principles and no
      standard library [Reals] or [Complex] imports.

    Constructivity.  Every named construction is carried by [Set]; all
      predicates are Set-sorted ([c_eq], [real_eq], [real_lt],
      [QltT]); every statement is built from Set-sorted connectives;
      rational-level order reasoning appears only inside proof bodies;
      the development is closed under the global context; every
      definition is transparent; [coqchk] reports zero assumed
      constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" CxRealPairExpLog.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ==== Section 1. Congruence helpers ==== *)

Lemma real_mult_opp_r : forall x y : Real,
  real_eq (real_mult x (real_opp y)) (real_opp (real_mult x y)).
Proof.
  intros [u Hu] [v Hv]. apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

Lemma real_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_mult x real_one)).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

Lemma real_exp_zero_mult_l : forall x : Real,
  real_eq (real_mult (cauchy_real_exp real_zero) x) x.
Proof.
  intro x. apply (real_eq_trans _ (real_mult real_one x)).
  - apply RealSetoid.real_eq_mult_compat.
    + exact cauchy_real_exp_zero.
    + apply real_eq_refl.
  - apply real_mult_one_l.
Qed.

Lemma c_mult_congr : forall z1 z2 w1 w2 : Cx,
  c_eq z1 z2 -> c_eq w1 w2 -> c_eq (c_mult z1 w1) (c_mult z2 w2).
Proof.
  intros z1 z2 w1 w2 Hz Hw.
  unfold c_eq in Hz, Hw.
  destruct Hz as [Hr1 Hi1]. destruct Hw as [Hr2 Hi2].
  unfold c_eq. split.
  - apply (real_eq_minus_compat
      (real_mult (cRe z1) (cRe w1)) (real_mult (cIm z1) (cIm w1))
      (real_mult (cRe z2) (cRe w2)) (real_mult (cIm z2) (cIm w2))).
    + apply RealSetoid.real_eq_mult_compat. exact Hr1. exact Hr2.
    + apply RealSetoid.real_eq_mult_compat. exact Hi1. exact Hi2.
  - apply (RealSetoid.real_eq_plus_compat
      (real_mult (cRe z1) (cIm w1)) (real_mult (cIm z1) (cRe w1))
      (real_mult (cRe z2) (cIm w2)) (real_mult (cIm z2) (cRe w2))).
    + apply RealSetoid.real_eq_mult_compat. exact Hr1. exact Hi2.
    + apply RealSetoid.real_eq_mult_compat. exact Hi1. exact Hr2.
Qed.

Lemma c_plus_congr : forall z1 z2 w1 w2 : Cx,
  c_eq z1 z2 -> c_eq w1 w2 -> c_eq (c_plus z1 w1) (c_plus z2 w2).
Proof.
  intros z1 z2 w1 w2 Hz Hw.
  unfold c_eq in Hz, Hw.
  destruct Hz as [Hr1 Hi1]. destruct Hw as [Hr2 Hi2].
  unfold c_eq. split.
  - apply RealSetoid.real_eq_plus_compat. exact Hr1. exact Hr2.
  - apply RealSetoid.real_eq_plus_compat. exact Hi1. exact Hi2.
Qed.

Lemma c_opp_congr : forall z w : Cx,
  c_eq z w -> c_eq (c_opp z) (c_opp w).
Proof.
  intros z w Hz. unfold c_eq in Hz. destruct Hz as [Hr Hi].
  unfold c_eq. split.
  - apply RealSetoid.real_eq_opp_compat. exact Hr.
  - apply RealSetoid.real_eq_opp_compat. exact Hi.
Qed.

(* ==== Section 2. The complex exponential ==== *)

Definition c_exp (z : Cx) : Cx :=
  (real_mult (cauchy_real_exp (cRe z)) (cauchy_real_cos (cIm z)),
   real_mult (cauchy_real_exp (cRe z)) (cauchy_real_sin (cIm z))).

Lemma c_exp_zero : c_eq (c_exp c_zero) c_one.
Proof.
  unfold c_exp, c_zero, c_one. unfold c_eq. split.
  - apply (real_eq_trans _ (real_mult real_one real_one)).
    + apply RealSetoid.real_eq_mult_compat.
      * exact cauchy_real_exp_zero.
      * exact real_cos_one.
    + apply real_mult_one.
  - apply (real_eq_trans _ (real_mult real_one real_zero)).
    + apply RealSetoid.real_eq_mult_compat.
      * exact cauchy_real_exp_zero.
      * exact real_sin_zero.
    + apply real_mult_zero.
Qed.

Lemma c_exp_conj : forall z : Cx, c_eq (c_exp (c_conj z)) (c_conj (c_exp z)).
Proof.
  intro z. unfold c_exp, c_conj. unfold c_eq. split.
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + apply real_cos_opp.
  - apply (real_eq_trans _
      (real_mult (cauchy_real_exp (cRe z)) (real_opp (cauchy_real_sin (cIm z))))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply real_sin_opp.
    + apply real_mult_opp_r.
Qed.

(* Pointwise algebra: (a*b) * (c*d + e*f) == (a*c)*(b*d) + (a*e)*(b*f). *)
Lemma real_mult_plus_distr_r : forall a b c d e f : Real,
  real_eq (real_mult (real_mult a b) (real_plus (real_mult c d) (real_mult e f)))
          (real_plus (real_mult (real_mult a c) (real_mult b d))
                     (real_mult (real_mult a e) (real_mult b f))).
Proof.
  intros a b c d e f.
  destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2].
  destruct d as [d1 d2]. destruct e as [e1 e2]. destruct f as [f1 f2].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* Pointwise algebra: (a*b) * (c*d - e*f) == (a*c)*(b*d) - (a*e)*(b*f). *)
Lemma real_mult_plus_opp_distr_r : forall a b c d e f : Real,
  real_eq (real_mult (real_mult a b)
                     (real_plus (real_mult c d) (real_opp (real_mult e f))))
          (real_plus (real_mult (real_mult a c) (real_mult b d))
                     (real_opp (real_mult (real_mult a e) (real_mult b f)))).
Proof.
  intros a b c d e f.
  destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2].
  destruct d as [d1 d2]. destruct e as [e1 e2]. destruct f as [f1 f2].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

(* Addition law, assembled from the real exponential addition law
   cauchy_real_exp_plus and the real trigonometric addition formulas
   rs_add_sin and rs_add_cos. *)
Lemma c_exp_plus : forall z w : Cx,
  c_eq (c_exp (c_plus z w)) (c_mult (c_exp z) (c_exp w)).
Proof.
  intros z w. destruct z as [x y]. destruct w as [u v].
  unfold c_eq, c_exp, c_plus, c_mult, cRe, cIm. simpl. split.
  - apply (real_eq_trans _
      (real_mult (real_mult (cauchy_real_exp x) (cauchy_real_exp u))
                 (cauchy_real_cos (real_plus y v)))).
    + apply RealSetoid.real_eq_mult_compat.
      * exact (cauchy_real_exp_plus x u).
      * apply real_eq_refl.
    + apply (real_eq_trans _
        (real_mult (real_mult (cauchy_real_exp x) (cauchy_real_exp u))
          (real_plus (real_mult (cauchy_real_cos y) (cauchy_real_cos v))
                     (real_opp (real_mult (cauchy_real_sin y) (cauchy_real_sin v)))))).
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply rs_add_cos.
      * apply real_mult_plus_opp_distr_r.
  - apply (real_eq_trans _
      (real_mult (real_mult (cauchy_real_exp x) (cauchy_real_exp u))
                 (cauchy_real_sin (real_plus y v)))).
    + apply RealSetoid.real_eq_mult_compat.
      * exact (cauchy_real_exp_plus x u).
      * apply real_eq_refl.
    + apply (real_eq_trans _
        (real_mult (real_mult (cauchy_real_exp x) (cauchy_real_exp u))
          (real_plus (real_mult (cauchy_real_sin y) (cauchy_real_cos v))
                     (real_mult (cauchy_real_cos y) (cauchy_real_sin v))))).
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply rs_add_sin.
      * apply (real_eq_trans _
          (real_plus (real_mult (real_mult (cauchy_real_exp x) (cauchy_real_sin y))
                                (real_mult (cauchy_real_exp u) (cauchy_real_cos v)))
                     (real_mult (real_mult (cauchy_real_exp x) (cauchy_real_cos y))
                                (real_mult (cauchy_real_exp u) (cauchy_real_sin v))))).
        -- apply real_mult_plus_distr_r.
        -- apply real_plus_comm.
Qed.

(* ==== Section 3. The logarithm through an explicit polar interface ==== *)

(* The branch of the logarithm is carried by the explicit angle input th;
   no classical selection principle is used.  The modulus part reuses the
   real logarithm cw_log with its explicit positivity premise. *)
Definition c_scale (a : Real) (z : Cx) : Cx :=
  (real_mult a (cRe z), real_mult a (cIm z)).

Definition c_log (r th : Real) (Hr : real_lt real_zero r) : Cx :=
  (cw_log r Hr, th).

Lemma c_exp_c_log : forall (r th : Real) (Hr : real_lt real_zero r),
  c_eq (c_exp (c_log r th Hr)) (c_scale r (c_exp (real_zero, th))).
Proof.
  intros r th Hr. unfold c_log, c_exp, c_scale, c_eq, cRe, cIm. cbn [fst snd]. split.
  - apply (real_eq_trans _ (real_mult r (cauchy_real_cos th))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply cw_log_exp_right.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult r (real_mult real_one (cauchy_real_cos th)))).
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply (real_eq_sym _ _). apply real_mult_one_l.
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply (real_eq_trans _ (cauchy_real_cos th)).
           ++ apply real_mult_one_l.
           ++ apply (real_eq_sym _ _). apply real_exp_zero_mult_l.
  - apply (real_eq_trans _ (real_mult r (cauchy_real_sin th))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply cw_log_exp_right.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult r (real_mult real_one (cauchy_real_sin th)))).
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply (real_eq_sym _ _). apply real_mult_one_l.
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply (real_eq_trans _ (cauchy_real_sin th)).
           ++ apply real_mult_one_l.
           ++ apply (real_eq_sym _ _). apply real_exp_zero_mult_l.
Qed.

Lemma c_log_mult : forall (r1 th1 r2 th2 : Real)
  (H1 : real_lt real_zero r1) (H2 : real_lt real_zero r2),
  c_eq (c_log (real_mult r1 r2) (real_plus th1 th2)
              (real_mult_positive r1 r2 H1 H2))
       (c_plus (c_log r1 th1 H1) (c_log r2 th2 H2)).
Proof.
  intros r1 th1 r2 th2 H1 H2. unfold c_log, c_plus, c_eq. cbn [fst snd]. split.
  - exact (real_log_mult r1 r2 H1 H2).
  - apply real_eq_refl.
Qed.

(* ==== Section 4. Zero characterization of the squared modulus ==== *)

Lemma c_norm_sq_zero_intro : forall z : Cx,
  c_eq z c_zero -> real_eq (c_norm_sq z) real_zero.
Proof.
  intros z Hz. destruct Hz as [Hr Hi].
  destruct z as [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  unfold c_norm_sq, cRe, cIm. cbn [fst snd].
  intros eps Heps.
  assert (Hhalf : QltT 0 (1 # 2)%Q) by (apply Qlt_to_QltT; unfold Qlt; simpl; lia).
  assert (Hth : QltT 0 (eps * (1 # 2))%Q).
  { apply (qmult_ltT_0_compat eps (1 # 2)). exact Heps. exact Hhalf. }
  destruct (Hr (eps * (1 # 2))%Q Hth) as [N1 HN1].
  destruct (Hi (eps * (1 # 2))%Q Hth) as [N2 HN2].
  destruct (Hr 1%Q qltT_0_1) as [N0 HN0].
  destruct (Hi 1%Q qltT_0_1) as [N3 HN3].
  exists (Nat.max (Nat.max N0 N3) (Nat.max N1 N2)).
  intros n Hn.
  assert (Hring0 : u n * u n + v n * v n - 0 == u n * u n + v n * v n) by ring.
  assert (Ha1 : Qlt (Qabs (u n)) 1).
  { apply QltT_to_Qlt.
    unfold QltT, Qlt_bool.
    assert (Hcmp : (Qabs (u n) ?= 1) = (Qabs (u n - 0) ?= 1)).
    { apply Qcompare_comp. apply Qabs_wd. ring. apply Qeq_refl. }
    rewrite Hcmp.
    pose proof (HN0 n
      (NatLe_lift _ _
        (Nat.le_trans _ _ _ (Nat.le_max_l N0 N3)
          (Nat.le_trans _ _ _ (Nat.le_max_l (Nat.max N0 N3) (Nat.max N1 N2))
            (NatLe_drop _ _ Hn))))) as HN0s.
    unfold QltT, Qlt_bool in HN0s.
    exact HN0s. }
  assert (Hb1 : Qlt (Qabs (v n)) 1).
  { apply QltT_to_Qlt.
    unfold QltT, Qlt_bool.
    assert (Hcmp : (Qabs (v n) ?= 1) = (Qabs (v n - 0) ?= 1)).
    { apply Qcompare_comp. apply Qabs_wd. ring. apply Qeq_refl. }
    rewrite Hcmp.
    pose proof (HN3 n
      (NatLe_lift _ _
        (Nat.le_trans _ _ _ (Nat.le_max_r N0 N3)
          (Nat.le_trans _ _ _ (Nat.le_max_l (Nat.max N0 N3) (Nat.max N1 N2))
            (NatLe_drop _ _ Hn))))) as HN3s.
    unfold QltT, Qlt_bool in HN3s.
    exact HN3s. }
  assert (Ha2 : Qlt (Qabs (u n)) (eps * (1 # 2))).
  { apply QltT_to_Qlt.
    unfold QltT, Qlt_bool.
    assert (Hcmp : (Qabs (u n) ?= (eps * (1 # 2)))
                   = (Qabs (u n - 0) ?= (eps * (1 # 2)))).
    { apply Qcompare_comp. apply Qabs_wd. ring. apply Qeq_refl. }
    rewrite Hcmp.
    pose proof (HN1 n
      (NatLe_lift _ _
        (Nat.le_trans _ _ _ (Nat.le_max_l N1 N2)
          (Nat.le_trans _ _ _ (Nat.le_max_r (Nat.max N0 N3) (Nat.max N1 N2))
            (NatLe_drop _ _ Hn))))) as HN1s.
    unfold QltT, Qlt_bool in HN1s.
    exact HN1s. }
  assert (Hb2 : Qlt (Qabs (v n)) (eps * (1 # 2))).
  { apply QltT_to_Qlt.
    unfold QltT, Qlt_bool.
    assert (Hcmp : (Qabs (v n) ?= (eps * (1 # 2)))
                   = (Qabs (v n - 0) ?= (eps * (1 # 2)))).
    { apply Qcompare_comp. apply Qabs_wd. ring. apply Qeq_refl. }
    rewrite Hcmp.
    pose proof (HN2 n
      (NatLe_lift _ _
        (Nat.le_trans _ _ _ (Nat.le_max_r N1 N2)
          (Nat.le_trans _ _ _ (Nat.le_max_r (Nat.max N0 N3) (Nat.max N1 N2))
            (NatLe_drop _ _ Hn))))) as HN2s.
    unfold QltT, Qlt_bool in HN2s.
    exact HN2s. }
  assert (Hhh : (eps * (1 # 2))%Q + (eps * (1 # 2))%Q == eps) by ring.
  assert (Hmain : Qlt (Qabs (u n * u n + v n * v n)) eps).
  { apply (Qle_lt_trans _ (Qabs (u n * u n) + Qabs (v n * v n))).
    - apply Qabs_triangle.
    - apply (Qle_lt_trans _ (Qabs (u n) * Qabs (u n) + Qabs (v n) * Qabs (v n))).
      + apply Qplus_le_compat.
        * apply qeq_le. apply (Qabs_Qmult (u n) (u n)).
        * apply qeq_le. apply (Qabs_Qmult (v n) (v n)).
      + apply (Qle_lt_trans _ (Qabs (u n) + Qabs (v n))).
        * apply (Qle_trans _ (1 * Qabs (u n) + 1 * Qabs (v n))).
          -- apply Qplus_le_compat.
             ++ apply (Qmult_le_compat_r (Qabs (u n)) 1 (Qabs (u n))).
                apply (Qlt_le_weak (Qabs (u n)) 1). exact Ha1.
                apply Qabs_nonneg.
             ++ apply (Qmult_le_compat_r (Qabs (v n)) 1 (Qabs (v n))).
                apply (Qlt_le_weak (Qabs (v n)) 1). exact Hb1.
                apply Qabs_nonneg.
          -- apply qeq_le. ring.
        * apply (Qlt_le_trans _ ((eps * (1 # 2)) + (eps * (1 # 2)))%Q).
          -- apply Qplus_lt_compat. exact Ha2. exact Hb2.
          -- apply qeq_le. exact Hhh. }
  assert (Hab : Qabs (u n * u n + v n * v n)
                == Qabs (u n * u n + v n * v n - 0))
    by (apply Qabs_wd; ring).
  assert (Habs : Qabs (projT1 (real_plus (real_mult (existT (fun s : Qseq => cauchy s) u Hu)
                                         (existT (fun s : Qseq => cauchy s) u Hu))
                                  (real_mult (existT (fun s : Qseq => cauchy s) v Hv)
                                         (existT (fun s : Qseq => cauchy s) v Hv))) n
                         - projT1 real_zero n)
                 == Qabs (u n * u n + v n * v n))
    by (apply (Qeq_trans _ (Qabs (u n * u n + v n * v n - 0)));
        [ apply Qabs_wd; apply Qeq_refl | apply Qabs_wd; exact Hring0 ]).
  assert (Hcmp : (Qabs (projT1 (real_plus (real_mult (existT (fun s : Qseq => cauchy s) u Hu)
                                                  (existT (fun s : Qseq => cauchy s) u Hu))
                                           (real_mult (existT (fun s : Qseq => cauchy s) v Hv)
                                                  (existT (fun s : Qseq => cauchy s) v Hv))) n
                                   - projT1 real_zero n) ?= eps)
                 = (Qabs (u n * u n + v n * v n) ?= eps)).
  { apply Qcompare_comp. exact Habs. apply Qeq_refl. }
  unfold QltT, Qlt_bool.
  rewrite Hcmp.
  pose proof (Qlt_to_QltT (Qabs (u n * u n + v n * v n)) eps Hmain) as HmT.
  unfold QltT, Qlt_bool in HmT.
  exact HmT.
Qed.

Lemma c_norm_sq_zero_elim : forall z : Cx,
  real_eq (c_norm_sq z) real_zero -> c_eq z c_zero.
Proof.
  intros z Hn.
  destruct z as [p q]. destruct p as [u Hu]. destruct q as [v Hv].
  unfold c_eq, cRe, cIm, c_zero. cbn [fst snd]. split.
  - intros eps Heps.
    assert (Heps2 : QltT 0 (eps * eps)%Q).
    { apply (qmult_ltT_0_compat eps eps). exact Heps. exact Heps. }
    destruct (Hn (eps * eps)%Q Heps2) as [N HN].
    exists N. intros m Hm.
    specialize (HN m Hm).
    assert (Hring0 : u m * u m + v m * v m - 0 == u m * u m + v m * v m) by ring.
    assert (Haa0 : 0 <= u m * u m).
    { assert (Hs : u m * u m == Qabs (u m) * Qabs (u m)).
      { apply (Qabs_case (u m) (fun t => u m * u m == t * t)).
        - intro H0. apply Qeq_refl.
        - intro H0. ring. }
      apply (Qle_trans _ (Qabs (u m) * Qabs (u m))).
      - apply Qmult_le_0_compat; apply Qabs_nonneg.
      - apply qeq_le. apply (Qeq_sym _ _ Hs). }
    assert (Hbb0 : 0 <= v m * v m).
    { assert (Hs : v m * v m == Qabs (v m) * Qabs (v m)).
      { apply (Qabs_case (v m) (fun t => v m * v m == t * t)).
        - intro H0. apply Qeq_refl.
        - intro H0. ring. }
      apply (Qle_trans _ (Qabs (v m) * Qabs (v m))).
      - apply Qmult_le_0_compat; apply Qabs_nonneg.
      - apply qeq_le. apply (Qeq_sym _ _ Hs). }
    apply QltT_to_Qlt in HN.
    assert (Hz2 : u m * u m + 0 == u m * u m) by ring.
    assert (Hsqle : Qlt (u m * u m) (eps * eps)).
    { apply (Qle_lt_trans _ (Qabs (u m * u m + v m * v m - 0))).
      - apply (Qle_trans _ (u m * u m + v m * v m)).
        + apply (Qle_trans _ (u m * u m + 0)%Q).
          * apply qeq_le. apply (Qeq_sym _ _ Hz2).
          * apply Qplus_le_compat. apply Qle_refl. exact Hbb0.
        + apply (Qle_trans _ (u m * u m + v m * v m - 0)).
          * apply qeq_le. apply (Qeq_sym _ _ Hring0).
          * apply Qle_Qabs.
      - exact HN. }
    destruct (Qlt_le_dec (Qabs (u m)) eps) as [Hfin | Hge].
    + unfold QltT, Qlt_bool.
      assert (Hab0 : Qabs (projT1 (existT (fun s : Qseq => cauchy s) u Hu) m
                           - projT1 real_zero m) == Qabs (u m))
        by (apply (Qeq_trans _ (Qabs (u m - 0)));
            [ apply Qabs_wd; apply Qeq_refl | apply Qabs_wd; ring ]).
      assert (Hcmp : (Qabs (projT1 (existT (fun s : Qseq => cauchy s) u Hu) m
                              - projT1 real_zero m) ?= eps)
                     = (Qabs (u m) ?= eps)).
      { apply Qcompare_comp. exact Hab0. apply Qeq_refl. }
      rewrite Hcmp.
      exact (Qlt_to_QltT (Qabs (u m)) eps Hfin).
    + exfalso.
      assert (Habs2 : u m * u m == Qabs (u m) * Qabs (u m)).
      { apply (Qabs_case (u m) (fun t => u m * u m == t * t)).
        - intro H0. apply Qeq_refl.
        - intro H0. ring. }
      assert (Hge2 : eps * eps <= Qabs (u m) * Qabs (u m)).
      { apply (Qle_trans _ (Qabs (u m) * eps)).
        - apply (Qmult_le_compat_r eps (Qabs (u m)) eps). exact Hge.
          apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        - apply (Qle_trans _ (eps * Qabs (u m))).
          + apply qeq_le. ring.
          + apply (Qmult_le_compat_r eps (Qabs (u m)) (Qabs (u m))). exact Hge.
            apply Qabs_nonneg. }
      apply (Qlt_irrefl (u m * u m)).
      apply (Qlt_le_trans _ (eps * eps)).
      -- exact Hsqle.
      -- apply (Qle_trans _ (Qabs (u m) * Qabs (u m))).
         ++ exact Hge2.
         ++ apply qeq_le. apply (Qeq_sym _ _ Habs2).
  - intros eps Heps.
    assert (Heps2 : QltT 0 (eps * eps)%Q).
    { apply (qmult_ltT_0_compat eps eps). exact Heps. exact Heps. }
    destruct (Hn (eps * eps)%Q Heps2) as [N HN].
    exists N. intros m Hm.
    specialize (HN m Hm).
    assert (Hring0 : u m * u m + v m * v m - 0 == u m * u m + v m * v m) by ring.
    assert (Haa0 : 0 <= u m * u m).
    { assert (Hs : u m * u m == Qabs (u m) * Qabs (u m)).
      { apply (Qabs_case (u m) (fun t => u m * u m == t * t)).
        - intro H0. apply Qeq_refl.
        - intro H0. ring. }
      apply (Qle_trans _ (Qabs (u m) * Qabs (u m))).
      - apply Qmult_le_0_compat; apply Qabs_nonneg.
      - apply qeq_le. apply (Qeq_sym _ _ Hs). }
    assert (Hbb0 : 0 <= v m * v m).
    { assert (Hs : v m * v m == Qabs (v m) * Qabs (v m)).
      { apply (Qabs_case (v m) (fun t => v m * v m == t * t)).
        - intro H0. apply Qeq_refl.
        - intro H0. ring. }
      apply (Qle_trans _ (Qabs (v m) * Qabs (v m))).
      - apply Qmult_le_0_compat; apply Qabs_nonneg.
      - apply qeq_le. apply (Qeq_sym _ _ Hs). }
    apply QltT_to_Qlt in HN.
    assert (Hz2v : v m * v m + 0 == v m * v m) by ring.
    assert (Hz3 : u m * u m + v m * v m == v m * v m + u m * u m) by ring.
    assert (Hsqle : Qlt (v m * v m) (eps * eps)).
    { apply (Qle_lt_trans _ (Qabs (u m * u m + v m * v m - 0))).
      - apply (Qle_trans _ (v m * v m + u m * u m)%Q).
        + apply (Qle_trans _ (v m * v m + 0)%Q).
          * apply qeq_le. apply (Qeq_sym _ _ Hz2v).
          * apply Qplus_le_compat. apply Qle_refl. exact Haa0.
        + apply (Qle_trans _ (u m * u m + v m * v m)%Q).
          * apply qeq_le. apply (Qeq_sym _ _ Hz3).
          * apply (Qle_trans _ (u m * u m + v m * v m - 0)).
            -- apply qeq_le. apply (Qeq_sym _ _ Hring0).
            -- apply Qle_Qabs.
      - exact HN. }
    destruct (Qlt_le_dec (Qabs (v m)) eps) as [Hfin | Hge].
    + unfold QltT, Qlt_bool.
      assert (Hab0 : Qabs (projT1 (existT (fun s : Qseq => cauchy s) v Hv) m
                           - projT1 real_zero m) == Qabs (v m))
        by (apply (Qeq_trans _ (Qabs (v m - 0)));
            [ apply Qabs_wd; apply Qeq_refl | apply Qabs_wd; ring ]).
      assert (Hcmp : (Qabs (projT1 (existT (fun s : Qseq => cauchy s) v Hv) m
                              - projT1 real_zero m) ?= eps)
                     = (Qabs (v m) ?= eps)).
      { apply Qcompare_comp. exact Hab0. apply Qeq_refl. }
      rewrite Hcmp.
      exact (Qlt_to_QltT (Qabs (v m)) eps Hfin).
    + exfalso.
      assert (Habs2 : v m * v m == Qabs (v m) * Qabs (v m)).
      { apply (Qabs_case (v m) (fun t => v m * v m == t * t)).
        - intro H0. apply Qeq_refl.
        - intro H0. ring. }
      assert (Hge2 : eps * eps <= Qabs (v m) * Qabs (v m)).
      { apply (Qle_trans _ (Qabs (v m) * eps)).
        - apply (Qmult_le_compat_r eps (Qabs (v m)) eps). exact Hge.
          apply (Qlt_le_weak 0 eps). apply QltT_to_Qlt. exact Heps.
        - apply (Qle_trans _ (eps * Qabs (v m))).
          + apply qeq_le. ring.
          + apply (Qmult_le_compat_r eps (Qabs (v m)) (Qabs (v m))). exact Hge.
            apply Qabs_nonneg. }
      apply (Qlt_irrefl (v m * v m)).
      apply (Qlt_le_trans _ (eps * eps)).
      -- exact Hsqle.
      -- apply (Qle_trans _ (Qabs (v m) * Qabs (v m))).
         ++ exact Hge2.
         ++ apply qeq_le. apply (Qeq_sym _ _ Habs2).
Qed.
