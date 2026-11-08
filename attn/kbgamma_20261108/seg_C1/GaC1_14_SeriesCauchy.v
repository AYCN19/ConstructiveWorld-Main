(* ConstructiveWorld-Main - the series partial-sum Cauchy criterion on the
   complex pair carrier, with the pointwise-Q bridges. *)

(** * GaC1_14_SeriesCauchy: the Cauchy criterion for Cx-valued series.

    Mission.  The series partial-sum Cauchy criterion on the Cx
      carrier: the fold [cxsum], the Real-layer epsilon-N criterion
      [cxseries_cauchy], the pointwise-Q component criterion
      [cxs_pointwise_cauchyQ], the forward pointification bridge
      [gaC1_14_pointwise_to_cauchy], the reverse bridge with explicit
      factor-2 slack [gaC1_14_cauchy_to_pointwise_slack], and the
      sqrt-free two-fold triangle step [gaC1_14_norm_sq_pair_lt]
      feeding the tail engine used by C1-15.

    Dependencies.  Stdlib [Arith.PeanoNat], [QArith.QArith],
      [QArith.Qring], [QArith.Qabs], [Setoid], [Morphisms].  Requires
      [S01_BaseRing] ([And]/[Id]), [S02_CauchyComplete] ([Real],
      cauchy carrier, [real_lt]), and [CxRealPairCore] of this
      development.

    References.  The Taylor partial-sum/remainder face
      piu_zz_pnt_qexp.v:41 (B5.2) as recast mother; [cauchy_real_exp]
      (S03:1203) precedent; mathlib [RadiusOfConvergence.lean]
      summable/hasSum, whose CompleteSpace/Classical carriers are NOT
      transcribed (red line 1); the explicit epsilon-N margin form is
      the minimal sufficient shape.  The reverse bridge carries an
      explicit factor-2 slack (the constructively honest
      direction-bounded form); the closed-form geometric tail is
      delivered by C1-15 on the triangle step.

    Constructivity.  All constructions are Set-carried; Set-sorted
      predicates ([real_lt], [real_eq], [QltT], [Id]); zero classical
      choice (decidable Q order); closed under the global context;
      [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_14_SeriesCauchy.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import CxRealPairCore.

(* ===================================================================== *)
(* Section 1. Carriers: partial sums, differences, the two criteria.      *)
(* ===================================================================== *)

Section SeriesCarriers.

(* Component projections of a complex point at a Cauchy index. *)
Definition cReQ (z : Cx) (k : nat) : Q := projT1 (cRe z) k.
Definition cImQ (z : Cx) (k : nat) : Q := projT1 (cIm z) k.

(* Difference z + (-w) on the Cx carrier. *)
Definition cdiff (z w : Cx) : Cx := c_plus z (c_opp w).

(* Partial sums of a Cx-valued sequence (nat-iterated fold). *)
Fixpoint cxsum (a : nat -> Cx) (n : nat) : Cx :=
  match n with
  | O => c_zero
  | Datatypes.S k => c_plus (cxsum a k) (a k)
  end.

(* The Real-layer epsilon-N criterion on partial sums, symmetric form. *)
Definition cxseries_cauchy (a : nat -> Cx) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      real_lt (c_norm_sq (cdiff (cxsum a m) (cxsum a n)))
              (real_mult (real_const eps) (real_const eps))).

(* The pointwise-Q component criterion: eps > 0 gives N (sequence        *)
(* threshold) and, per pair, K (projection threshold) with the absolute  *)
(* component sums of the difference below eps.                           *)
Definition cxs_pointwise_cauchyQ (a : nat -> Cx) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      sigT (fun K : nat => forall k : nat, NatLe K k ->
        QltT (Qabs (cReQ (cdiff (cxsum a m) (cxsum a n)) k)
             + Qabs (cImQ (cdiff (cxsum a m) (cxsum a n)) k)) eps)).

End SeriesCarriers.

(* ===================================================================== *)
(* Section 2. Rational-level helpers (squares, absolute values).          *)
(* ===================================================================== *)

Section QHelpers.

(* 0 < y -> x < x + y. *)
Lemma c14_qlt_add_r : forall x y : Q, 0 < y -> x < x + y.
Proof.
  intros x y Hy.
  pose proof (proj2 (Qplus_lt_r 0 y x) Hy) as H.
  assert (Hz : x + 0 == x) by ring.
  setoid_rewrite Hz in H. exact H.
Qed.

(* 0 <= t -> x <= x + t. *)
Lemma c14_qle_add_r : forall x t : Q, 0 <= t -> x <= x + t.
Proof.
  intros x t Ht.
  pose proof (proj2 (Qplus_le_r 0 t x) Ht) as H.
  assert (Hz : x + 0 == x) by ring.
  setoid_rewrite Hz in H. exact H.
Qed.

(* |x|^2 == x^2. *)
Lemma c14_qabs_sq : forall x : Q, Qabs x * Qabs x == x * x.
Proof.
  intro x. apply (Qabs_case x (fun y => y * y == x * x)).
  - intros Hpos. ring.
  - intros Hneg. ring.
Qed.

(* x^2 >= 0. *)
Lemma c14_qsq_nonneg : forall x : Q, 0 <= x * x.
Proof.
  intro x. rewrite <- (c14_qabs_sq x).
  apply (Qabs_case x (fun y => 0 <= y * y)).
  - intros Hpos.
    pose proof (Qmult_le_compat_r 0 x x Hpos Hpos) as H.
    rewrite (Qmult_0_l x) in H. exact H.
  - intros Hneg.
    assert (H0neg : 0 <= - x).
    { pose proof (Qopp_le_compat x 0 Hneg) as H.
      assert (Hz : - 0 == 0) by ring.
      rewrite Hz in H. exact H. }
    pose proof (Qmult_le_compat_r 0 (- x) (- x) H0neg H0neg) as H.
    rewrite (Qmult_0_l (- x)) in H.
    exact H.
Qed.

(* 0 <= s < t -> s^2 < t^2. *)
Lemma c14_qsq_strict_mono : forall s t : Q, 0 <= s -> s < t -> s * s < t * t.
Proof.
  intros s t Hs0 Hst.
  assert (Ht : 0 < t) by exact (Qle_lt_trans 0 s t Hs0 Hst).
  assert (Hts : 0 < t + s)
    by exact (Qplus_lt_le_compat 0 t 0 s Ht Hs0).
  pose proof (Qmult_lt_compat_r s t (t + s) Hts Hst) as H.
  assert (Hl : s * (t + s) == s * s + s * t) by ring.
  assert (Hr : t * (t + s) == t * t + s * t) by ring.
  rewrite Hl, Hr in H.
  rewrite (Qplus_comm (s * s) (s * t)), (Qplus_comm (t * t) (s * t)) in H.
  exact (proj1 (Qplus_lt_r (s * s) (t * t) (s * t)) H).
Qed.

(* 0 <= s <= t -> s^2 <= t^2. *)
Lemma c14_qsq_mono : forall s t : Q, 0 <= s -> s <= t -> s * s <= t * t.
Proof.
  intros s t Hs0 Hst.
  apply (Qle_trans _ (t * s)).
  - apply (Qmult_le_compat_r s t s); [exact Hst | exact Hs0].
  - setoid_rewrite (Qmult_comm t s).
    apply (Qmult_le_compat_r s t t); [exact Hst | exact (Qle_trans 0 s t Hs0 Hst)].
Qed.

(* u^2 + v^2 <= (|u| + |v|)^2. *)
Lemma c14_qsq_sum_le_absadd_sq : forall u v : Q,
  u * u + v * v <= (Qabs u + Qabs v) * (Qabs u + Qabs v).
Proof.
  intros u v.
  assert (Hu0 : 0 <= Qabs u) by apply Qabs_nonneg.
  assert (Hv0 : 0 <= Qabs v) by apply Qabs_nonneg.
  assert (Ht1 : 0 <= Qabs u * Qabs v).
  { pose proof (Qmult_le_compat_r 0 (Qabs u) (Qabs v) Hu0 Hv0) as H.
    rewrite (Qmult_0_l (Qabs v)) in H. exact H. }
  assert (H02 : 0 <= 2) by (apply Qlt_le_weak; reflexivity).
  assert (Ht2 : 0 <= (Qabs u * Qabs v) * 2).
  { pose proof (Qmult_le_compat_r 0 (Qabs u * Qabs v) 2 Ht1 H02) as H.
    rewrite (Qmult_0_l 2) in H. exact H. }
  assert (Heq : (Qabs u + Qabs v) * (Qabs u + Qabs v)
                == (Qabs u * Qabs u + Qabs v * Qabs v) + (Qabs u * Qabs v) * 2)
    by ring.
  rewrite (c14_qabs_sq u), (c14_qabs_sq v) in Heq.
  rewrite Heq.
  apply c14_qle_add_r. exact Ht2.
Qed.

(* (|u| + |v|)^2 <= 2 * (u^2 + v^2). *)
Lemma c14_qabsadd_sq_le_2sum : forall u v : Q,
  (Qabs u + Qabs v) * (Qabs u + Qabs v) <= 2 * (u * u + v * v).
Proof.
  intros u v.
  assert (Heq : 2 * (Qabs u * Qabs u + Qabs v * Qabs v)
                == (Qabs u + Qabs v) * (Qabs u + Qabs v)
                   + (Qabs u - Qabs v) * (Qabs u - Qabs v))
    by ring.
  rewrite (c14_qabs_sq u), (c14_qabs_sq v) in Heq.
  rewrite Heq.
  apply c14_qle_add_r. apply c14_qsq_nonneg.
Qed.

End QHelpers.

(* ===================================================================== *)
(* Section 3. G1: pointwise-Q criterion -> Real-layer criterion.          *)
(* ===================================================================== *)

Section G1Forward.

Lemma gaC1_14_pointwise_to_cauchy :
  forall a : nat -> Cx, cxs_pointwise_cauchyQ a -> cxseries_cauchy a.
Proof.
  intros a Hpw eps Heps.
  assert (Heps0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (H012 : Qlt 0 (1#2)%Q) by reflexivity.
  assert (H014 : Qlt 0 (1#4)%Q) by reflexivity.
  assert (Hhalfpos : Qlt 0 (eps * (1#2)%Q)).
  { pose proof (Qmult_lt_compat_r 0 eps (1#2)%Q H012 Heps0) as H.
    rewrite (Qmult_0_l (1#2)%Q) in H. exact H. }
  assert (Heps2pos : Qlt 0 (eps * eps)).
  { pose proof (Qmult_lt_compat_r 0 eps eps Heps0 Heps0) as H.
    rewrite (Qmult_0_l eps) in H. exact H. }
  destruct (Hpw (eps * (1#2)%Q) (Qlt_to_QltT _ _ Hhalfpos)) as [N HN].
  exists N.
  intros m n Hm Hn.
  destruct (HN m n Hm Hn) as [K HK].
  unfold real_lt.
  exists ((eps * eps) * (1#4)%Q).
  split.
  - apply Qlt_to_QltT.
    pose proof (Qmult_lt_compat_r 0 (eps * eps) (1#4)%Q H014 Heps2pos) as H.
    rewrite (Qmult_0_l (1#4)%Q) in H. exact H.
  - exists K. intros j Hj.
    specialize (HK j Hj).
    cbn [real_mult real_const projT1].
    unfold c_norm_sq.
    unfold cReQ, cImQ in HK.
    destruct (cRe (cdiff (cxsum a m) (cxsum a n))) as [u Hcu] eqn:Ere.
    destruct (cIm (cdiff (cxsum a m) (cxsum a n))) as [v Hcv] eqn:Erim.
    cbn [projT1 cRe cIm] in HK.
    cbn [real_plus real_mult projT1 cRe cIm].
    apply QltT_to_Qlt in HK.
    pose proof (Qplus_le_compat 0 (Qabs (u j)) 0 (Qabs (v j))
           (Qabs_nonneg (u j)) (Qabs_nonneg (v j))) as Hs0.
    assert (Hsq1 : u j * u j + v j * v j
                   <= (Qabs (u j) + Qabs (v j)) * (Qabs (u j) + Qabs (v j)))
      by apply c14_qsq_sum_le_absadd_sq.
    assert (Hsq2 : (Qabs (u j) + Qabs (v j)) * (Qabs (u j) + Qabs (v j))
                   < (eps * (1#2)%Q) * (eps * (1#2)%Q))
      by exact (c14_qsq_strict_mono _ _ Hs0 HK).
    assert (Heq2 : (eps * (1#2)%Q) * (eps * (1#2)%Q) == (eps * eps) * (1#4)%Q)
      by ring.
    rewrite Heq2 in Hsq2.
    assert (Hmid : u j * u j + v j * v j < (eps * eps) * (1#4)%Q)
      by exact (Qle_lt_trans _ _ _ Hsq1 Hsq2).
    assert (Hopp : (- ((eps * eps) * (1#4)%Q)) < (- (u j * u j + v j * v j)))
      by (apply (Qopp_lt_compat _ _ Hmid)).
    pose proof (proj2 (Qplus_lt_r (- ((eps * eps) * (1#4)%Q))
                (- (u j * u j + v j * v j)) (eps * eps)) Hopp) as H5p.
    assert (Heq3 : eps * eps + (- ((eps * eps) * (1#4)%Q))
                   == (eps * eps) * (3#4)%Q) by ring.
    rewrite Heq3 in H5p.
    assert (H4 : (eps * eps) * (1#4)%Q < (eps * eps) * (3#4)%Q).
    { rewrite (Qmult_comm (eps * eps) (1#4)%Q), (Qmult_comm (eps * eps) (3#4)%Q).
      apply Qmult_lt_compat_r; [exact Heps2pos | reflexivity]. }
    apply Qlt_to_QltT.
    exact (Qlt_trans ((eps * eps) * (1#4)%Q) ((eps * eps) * (3#4)%Q)
             (eps * eps + (- (u j * u j + v j * v j))) H4 H5p).
Qed.

End G1Forward.

(* ===================================================================== *)
(* Section 4. G2: Real-layer criterion -> pointwise-Q form with explicit  *)
(* factor-2 slack (the constructively honest reverse bridge).             *)
(* ===================================================================== *)

Section G2Reverse.

Lemma gaC1_14_cauchy_to_pointwise_slack :
  forall (a : nat -> Cx) (eps : Q), QltT 0 eps ->
    cxseries_cauchy a ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      sigT (fun K : nat => forall k : nat, NatLe K k ->
        QltT (Qabs (cReQ (cdiff (cxsum a m) (cxsum a n)) k)
             + Qabs (cImQ (cdiff (cxsum a m) (cxsum a n)) k)) (2 * eps))).
Proof.
  intros a eps Heps Hc.
  assert (Heps0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (H02l : Qlt 0 2) by reflexivity.
  assert (H02 : 0 <= 2) by (apply Qlt_le_weak; reflexivity).
  assert (H24 : Qlt 2 4) by reflexivity.
  assert (Heps2pos : Qlt 0 (eps * eps)).
  { pose proof (Qmult_lt_compat_r 0 eps eps Heps0 Heps0) as H.
    rewrite (Qmult_0_l eps) in H. exact H. }
  assert (H02e : 0 <= 2 * eps).
  { pose proof (Qmult_le_compat_r 0 eps 2 (Qlt_le_weak 0 eps Heps0) H02) as H.
    rewrite (Qmult_0_l 2) in H.
    rewrite (Qmult_comm eps 2) in H. exact H. }
  destruct (Hc eps Heps) as [N HN].
  exists N.
  intros m n Hm Hn.
  specialize (HN m n Hm Hn).
  unfold real_lt in HN.
  destruct HN as [eps0 [Heps00 [N0 HN0]]].
  exists N0.
  intros k Hk.
  specialize (HN0 k Hk).
  cbn [real_mult real_const projT1] in HN0.
  unfold c_norm_sq in HN0.
  unfold cReQ, cImQ.
  destruct (cRe (cdiff (cxsum a m) (cxsum a n))) as [u Hcu] eqn:Ere.
  destruct (cIm (cdiff (cxsum a m) (cxsum a n))) as [v Hcv] eqn:Erim.
  cbn [projT1 cRe cIm] in HN0.
  cbn [projT1 cRe cIm].
  cbn [real_plus real_mult projT1] in HN0.
  cbn [real_plus real_mult projT1].
  apply QltT_to_Qlt in HN0.
  apply QltT_to_Qlt in Heps00.
  (* HN0 : eps*eps - (u k^2 + v k^2) > eps0 > 0 *)
  assert (Huv : u k * u k + v k * v k < eps * eps).
  { assert (HeqC : eps * eps
                   == (u k * u k + v k * v k)
                      + (eps * eps - (u k * u k + v k * v k))) by ring.
    pose proof (proj2 (Qplus_lt_r eps0
                (eps * eps - (u k * u k + v k * v k)) (u k * u k + v k * v k)) HN0) as H.
    rewrite <- HeqC in H.
    pose proof (c14_qlt_add_r (u k * u k + v k * v k) eps0 Heps00) as H2.
    exact (Qlt_trans _ _ _ H2 H). }
  pose proof (Qplus_le_compat 0 (Qabs (u k)) 0 (Qabs (v k))
         (Qabs_nonneg (u k)) (Qabs_nonneg (v k))) as Hs0.
  assert (HsqA : (Qabs (u k) + Qabs (v k)) * (Qabs (u k) + Qabs (v k))
                 <= 2 * (u k * u k + v k * v k))
    by apply c14_qabsadd_sq_le_2sum.
  assert (Hb : (u k * u k + v k * v k) * 2 < (eps * eps) * 2)
    by (apply Qmult_lt_compat_r; [exact H02l | exact Huv]).
  rewrite (Qmult_comm (u k * u k + v k * v k) 2),
          (Qmult_comm (eps * eps) 2) in Hb.
  assert (Hc2 : 2 * (eps * eps) < 4 * (eps * eps))
    by (apply Qmult_lt_compat_r; [exact Heps2pos | exact H24]).
  assert (Heq4 : (2 * eps) * (2 * eps) == 4 * (eps * eps)) by ring.
  assert (Hstrict : (Qabs (u k) + Qabs (v k)) * (Qabs (u k) + Qabs (v k))
                    < (2 * eps) * (2 * eps)).
  { pose proof (Qle_lt_trans _ _ _ HsqA Hb) as H1.
    pose proof (Qlt_trans _ _ _ H1 Hc2) as H2.
    rewrite <- Heq4 in H2. exact H2. }
  destruct (Qle_bool (2 * eps) (Qabs (u k) + Qabs (v k))) eqn:Edec.
  - (* 2*eps <= s: then s^2 >= (2*eps)^2 contradicts Hstrict *)
    apply Qle_bool_imp_le in Edec.
    pose proof (c14_qsq_mono (2 * eps) (Qabs (u k) + Qabs (v k)) H02e Edec) as Hmono2.
    pose proof (Qlt_le_trans _ _ _ Hstrict Hmono2) as Hcontra.
    exfalso.
    exact (Qlt_irrefl _ Hcontra).
  - (* ~(2*eps <= s) -> s < 2*eps *)
    apply Qlt_to_QltT.
    assert (Hnle : ~ (2 * eps <= Qabs (u k) + Qabs (v k))).
    { intro Hle.
      assert (Qle_bool (2 * eps) (Qabs (u k) + Qabs (v k)) = true)
        by (apply Qle_bool_iff; exact Hle).
      congruence. }
    exact (Qnot_le_lt _ _ Hnle).
Qed.

End G2Reverse.

(* ===================================================================== *)
(* Section 5. G3: the sqrt-free two-fold triangle step (explicit margin   *)
(* form): |u+v|^2 < 2|u|^2 + 2|v|^2 + d for every rational margin d > 0.  *)
(* ===================================================================== *)

Section G3Triangle.

Lemma gaC1_14_norm_sq_pair_lt :
  forall (u v : Cx) (d : Q), QltT 0 d ->
    real_lt (c_norm_sq (c_plus u v))
            (real_plus (real_mult (real_const 2) (real_plus (c_norm_sq u) (c_norm_sq v)))
                       (real_const d)).
Proof.
  intros u v d Hd.
  assert (Hd0 : Qlt 0 d) by (apply QltT_to_Qlt; exact Hd).
  assert (H012 : Qlt 0 (1#2)%Q) by reflexivity.
  assert (H12 : Qlt (1#2)%Q 1) by reflexivity.
  assert (Hhalfpos : Qlt 0 ((1#2)%Q * d)).
  { pose proof (Qmult_lt_compat_r 0 d (1#2)%Q H012 Hd0) as H.
    rewrite (Qmult_0_l (1#2)%Q) in H.
    rewrite (Qmult_comm d (1#2)%Q) in H. exact H. }
  assert (Hh1 : (1#2)%Q * d < 1 * d)
    by (apply Qmult_lt_compat_r; [exact Hd0 | exact H12]).
  rewrite (Qmult_1_l d) in Hh1.
  unfold real_lt.
  exists ((1#2)%Q * d).
  split.
  - apply Qlt_to_QltT. exact Hhalfpos.
  - exists 0%nat. intros j Hj.
    destruct u as [[uru Hcu] [uiy Hci]].
    destruct v as [[vru Hcv] [viy Hcv2]].
    cbn [c_plus cRe cIm fst snd c_norm_sq real_plus real_mult real_const projT1].
    assert (Heq : 2 * (uru j * uru j + uiy j * uiy j
                       + (vru j * vru j + viy j * viy j)) + d
                  - ((uru j + vru j) * (uru j + vru j)
                     + (uiy j + viy j) * (uiy j + viy j))
                  == d + ((uru j - vru j) * (uru j - vru j)
                          + (uiy j - viy j) * (uiy j - viy j))) by ring.
    assert (Hdle : d <= 2 * (uru j * uru j + uiy j * uiy j
                                 + (vru j * vru j + viy j * viy j)) + d
                   - ((uru j + vru j) * (uru j + vru j)
                      + (uiy j + viy j) * (uiy j + viy j))).
    { setoid_rewrite Heq.
      apply c14_qle_add_r.
      exact (Qplus_le_compat 0 ((uru j - vru j) * (uru j - vru j)) 0
               ((uiy j - viy j) * (uiy j - viy j))
               (c14_qsq_nonneg _) (c14_qsq_nonneg _)). }
    apply Qlt_to_QltT.
    exact (Qlt_le_trans _ _ _ Hh1 Hdle).
Qed.

End G3Triangle.
