(* ConstructiveWorld-Main - base faces for the absolute-convergence tail
   machinery: ring identities, embedding, log congruence, geometric sums. *)
(** * GaC2_02_AbsConvTailBound_a: Section-free base leaf.
    Mission.  The Section-free base faces consumed by the stem
      [GaC2_02_AbsConvTailBound] and its siblings: the pointwise ring
      identity family [r_mult_plus_distr]/[r_mult_opp_l]/[r_expand]/
      [r_tuck]/[r_affine_fold] with the [rring]/[cring] closers; the
      [c_of_real] congruences [c_of_real_mult_gen]/
      [c_of_real_scale_gen]/[c_of_real_wd], the real-slice exponential
      [c_exp_real], and [c_norm_sq_wd]; the nat embedding helpers
      [nat_real_S]/[nat_real_one]/[nat_real_zero]/[nat_real_mul] with
      the premise-parametrised positivity faces [nat_real_pos]
      (NatLe 1 n -> 0 < nat_real n) and [nat_real_lt]
      (NatLe (S m) n -> nat_real m < nat_real n); the log congruence
      [real_log_wd]; the (1 - s) pointwise forms
      [r_one_minus_opp]/[r_one_minus_le], the monotonicity
      [r_exp_le_mono], the inverse congruence [r_inv_wd], and
      [r_ln_nonneg]; the abstract geometric partial sums
      [r_qpow]/[r_gsum]/[r_gsum_bound]/[r_gsum_lt_one]; and the dyadic
      condensation faces [r_pow2_ge1]/[nat_dyadic_cover].
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith], [Lia].  Requires [S01_BaseRing] (selective
      [NatLe] import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog], and [GaC2_01_DirichletPartialSum] of this
      development; Import only (leaf _a and leaf _b never Require each
      other; both are consumed by the stem).
    References.  Card C2.02 leaf split (see the stem header).  The nat
      premise slots are carried by [NatLe]: [nat_real_pos] and
      [nat_real_lt] replace the stdlib Prop forms (0 < n)%nat and
      (m < n)%nat.
    Constructivity.  Red path A: all statements Set-sorted; closed
      under the global context; no stdlib [Complex]/[Reals] imports;
      [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_02_AbsConvTailBound_a.v] compiles cleanly
      (exit 0), wrapped by [cpu_guard v3]. *)

Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_01_DirichletPartialSum.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

(* Pointwise closers: destruct Real hypotheses (sigT pattern), then
   reduce real_eq / c_eq goals to pointwise Q ring identities. *)
Ltac rring :=
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  apply real_eq_of_zero_diff; intro n; simpl; ring.
Ltac cring :=
  repeat match goal with [ x : Real |- _ ] => destruct x end;
  unfold c_eq; split; apply real_eq_of_zero_diff; intro n; simpl; ring.

(* ==== Universal ring identities (consumable at opaque application sites) ==== *)
Lemma r_mult_plus_distr : forall a b c : Real,
  real_eq (real_mult (real_plus a b) c) (real_plus (real_mult a c) (real_mult b c)).
Proof. intros a b c. rring. Qed.
Lemma r_mult_opp_l : forall a b : Real,
  real_eq (real_mult (real_opp a) b) (real_opp (real_mult a b)).
Proof. intros a b. rring. Qed.
Lemma r_opp_invol : forall a : Real, real_eq (real_opp (real_opp a)) a.
Proof. intro a. rring. Qed.
Lemma r_plus_zero_r_gen : forall x : Real, real_eq (real_plus x real_zero) x.
Proof. intro x. rring. Qed.
Lemma r_plus_zero_l_gen : forall x : Real, real_eq (real_plus real_zero x) x.
Proof. intro x. rring. Qed.
Lemma r_assoc_scale : forall a b : Real,
  real_eq (real_mult (real_opp real_one) (real_mult a b)) (real_mult (real_opp a) b).
Proof. intros a b. rring. Qed.
Lemma r_expand : forall a b c : Real,
  real_eq (real_mult a (real_plus b (real_opp c)))
          (real_plus (real_mult a b) (real_opp (real_mult a c))).
Proof. intros a b c. rring. Qed.
Lemma r_tuck : forall b c : Real,
  real_eq (real_plus (real_plus real_one (real_opp b))
                     (real_plus (real_mult b real_one) (real_opp c)))
          (real_plus real_one (real_opp c)).
Proof. intros b c. rring. Qed.
Lemma r_affine_fold : forall a b : Real,
  real_eq (real_plus a (real_mult (real_opp b) a))
          (real_mult (real_opp (real_plus b (real_opp real_one))) a).
Proof. intros a b. rring. Qed.
(* real_le is the Set-sorted inl/inr sum: real_eq refines it from above. *)
Lemma r_le_of_eq : forall x y : Real, real_eq x y -> real_le x y.
Proof. intros x y Heq. exact (inr Heq). Qed.
(* Telescoping difference: a - c = (a - b) + (b - c). *)
Lemma r_tele : forall a b c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c))).
Proof. intros a b c. rring. Qed.
(* Nonnegativity is closed under addition (decided inl/inr form). *)
Lemma r_le_zero_plus : forall a b : Real,
  real_le real_zero a -> real_le real_zero b -> real_le real_zero (real_plus a b).
Proof.
  intros a b Ha Hb.
  apply (RealSetoid.real_le_compat (real_plus real_zero real_zero) real_zero
           (real_plus a b) (real_plus a b)).
  - rring.
  - apply real_eq_refl.
  - apply real_le_plus_compat; assumption.
Qed.
(* x <= x + y for y >= 0. *)
Lemma r_le_plus_nonneg : forall x y : Real, real_le real_zero y -> real_le x (real_plus x y).
Proof.
  intros x y Hy.
  apply (RealSetoid.real_le_compat (real_plus x real_zero) x (real_plus x y) (real_plus x y)).
  - rring.
  - apply real_eq_refl.
  - apply real_le_plus_compat; [apply real_le_refl | exact Hy].
Qed.

(* ==== c_of_real congruences and the real-slice exponential ==== *)
Lemma c_of_real_mult_gen : forall a b : Real,
  c_eq (c_mult (c_of_real a) (c_of_real b)) (c_of_real (real_mult a b)).
Proof. intros a b. cring. Qed.
Lemma c_of_real_scale_gen : forall a b : Real,
  c_eq (c_scale a (c_of_real b)) (c_of_real (real_mult a b)).
Proof. intros a b. cring. Qed.
Lemma c_of_real_wd : forall a b : Real, real_eq a b -> c_eq (c_of_real a) (c_of_real b).
Proof. intros a b H. split. - exact H. - apply real_eq_refl. Qed.
Lemma c_exp_real : forall x : Real,
  c_eq (c_exp (c_of_real x)) (c_of_real (cauchy_real_exp x)).
Proof.
  intro x. unfold c_exp, c_of_real, c_eq, cRe, cIm. cbn [fst snd]. split.
  - apply (real_eq_trans _ (real_mult (cauchy_real_exp x) real_one)).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) real_cos_one).
    + apply real_mult_one.
  - apply (real_eq_trans _ (real_mult (cauchy_real_exp x) real_zero)).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) real_sin_zero).
    + apply real_mult_zero.
Qed.
(* Squared-modulus congruence (consumed by the Cauchy witness in the stem). *)
Lemma c_norm_sq_wd : forall z w : Cx, c_eq z w -> real_eq (c_norm_sq z) (c_norm_sq w).
Proof.
  intros z w H. unfold c_eq in H. destruct H as [Hr Hi]. unfold c_norm_sq.
  apply RealSetoid.real_eq_plus_compat; apply RealSetoid.real_eq_mult_compat; assumption.
Qed.

(* ==== nat embedding helpers (NatLe-premised, H7 unification) ==== *)
Lemma nat_real_S : forall k : nat,
  real_eq (nat_real (S k)) (real_plus (nat_real k) real_one).
Proof.
  intro k. apply real_eq_of_zero_diff. intro n. unfold nat_real.
  rewrite real_plus_proj, !real_const_proj, real_one_pt.
  assert (Hs : Z.of_nat (S k) = (Z.of_nat k + 1)%Z) by lia.
  rewrite Hs. unfold Qeq. simpl. lia.
Qed.
Lemma nat_real_one : real_eq (nat_real 1) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n. unfold nat_real.
  rewrite real_const_proj, real_one_pt. unfold Qeq. simpl. lia.
Qed.
Lemma nat_real_zero : real_eq (nat_real 0) real_zero.
Proof.
  apply real_eq_of_zero_diff. intro n. unfold nat_real.
  rewrite real_const_proj, real_zero_pt. unfold Qeq. simpl. lia.
Qed.
(* Zero/one-step ring identities over the embedded naturals (cast here,
   outside the sectioned development, so the section never runs rring on a
   Section variable). *)
Lemma r_zero_scale_l : forall x : Real, real_eq (real_mult (nat_real 0) x) real_zero.
Proof. intro x. rring. Qed.
Lemma r_succ_scale : forall K x : Real,
  real_eq (real_plus x (real_mult K x)) (real_mult (real_plus K real_one) x).
Proof. intros K x. rring. Qed.
Lemma r_zero_scale_r : forall a x : Real,
  real_eq (real_mult a (real_mult (nat_real 0) x)) real_zero.
Proof. intros a x. rring. Qed.
Lemma r_succ_scale_gen : forall a K x : Real,
  real_eq (real_plus (real_mult a (real_mult K x)) (real_mult a x))
          (real_mult a (real_mult (real_plus K real_one) x)).
Proof. intros a K x. rring. Qed.
Lemma nat_real_mul : forall a b : nat,
  real_eq (nat_real (a * b)) (real_mult (nat_real a) (nat_real b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n. unfold nat_real.
  rewrite real_mult_proj, !real_const_proj.
  assert (Hm : Z.of_nat (a * b) = (Z.of_nat a * Z.of_nat b)%Z) by lia.
  rewrite Hm. unfold Qeq. simpl. ring.
Qed.
Lemma nat_real_pos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Proof.
  intros n Hn. apply NatLe_drop in Hn.
  assert (Hz : (0 < Z.of_nat n)%Z) by lia.
  unfold real_lt. exists ((Z.of_nat n # 2)%Q). split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists 0%nat. intros k Hk. apply Qlt_to_QltT. unfold nat_real.
    rewrite real_const_proj, real_zero_pt. unfold Qlt. simpl. lia.
Qed.
Lemma nat_real_lt : forall m n : nat, NatLe (S m) n -> real_lt (nat_real m) (nat_real n).
Proof.
  intros m n Hlt. apply NatLe_drop in Hlt.
  assert (Hd : (0 < Z.of_nat n - Z.of_nat m)%Z) by lia.
  unfold real_lt. exists (((Z.of_nat n - Z.of_nat m) # 2)%Q). split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists 0%nat. intros k Hk. apply Qlt_to_QltT. unfold nat_real.
    rewrite !real_const_proj. unfold Qlt. simpl. lia.
Qed.

Lemma r_lt_opp_flip : forall x y : Real, real_lt x y -> real_lt (real_opp y) (real_opp x).
Proof.
  intros x y Hlt.
  assert (H0 : real_lt real_zero (real_plus y (real_opp x)))
    by (apply real_lt_opp_plus; exact Hlt).
  apply (real_lt_zero_minus (real_opp y) (real_opp x)).
  apply (RealSetoid.real_lt_compat real_zero real_zero (real_plus y (real_opp x))
           (real_plus (real_opp x) (real_opp (real_opp y)))); [apply real_eq_refl | | exact H0].
  apply (real_eq_trans _ (real_plus (real_opp (real_opp y)) (real_opp x))).
  - apply (RealSetoid.real_eq_plus_compat _ _ _ _
             (real_eq_sym _ _ (r_opp_invol y)) (real_eq_refl _)).
  - apply real_plus_comm.
Qed.

(* ==== real_log congruence (witness-insensitive form) ==== *)
(* real_log x Hx computes a bisection sequence from the witness Hx, so the
   tree offers no congruence; it follows from real_weak_trich (S07:5749),
   cauchy_real_exp_mono (S07:2705), cw_log_exp_right (S07:5541) and
   real_lt_not_eq (S07:5685). *)
Lemma real_log_wd : forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
  real_eq x y -> real_eq (real_log x Hx) (real_log y Hy).
Proof.
  intros x y Hx Hy Hxy. unfold real_log. apply real_weak_trich.
  - intro Hlt.
    pose proof (cauchy_real_exp_mono _ _ Hlt) as He.
    pose proof (real_eq_lt_lt _ _ _ (real_eq_sym _ _ (cw_log_exp_right x Hx)) He) as H1.
    pose proof (real_lt_eq_lt _ _ _ H1 (cw_log_exp_right y Hy)) as H2.
    exact (real_lt_not_eq _ _ H2 Hxy).
  - intro Hlt.
    pose proof (cauchy_real_exp_mono _ _ Hlt) as He.
    pose proof (real_eq_lt_lt _ _ _ (real_eq_sym _ _ (cw_log_exp_right y Hy)) He) as H1.
    pose proof (real_lt_eq_lt _ _ _ H1 (cw_log_exp_right x Hx)) as H2.
    exact (real_lt_not_eq _ _ H2 (real_eq_sym _ _ Hxy)).
Qed.

(* Distributivity on the left (mirror of r_mult_plus_distr for the stem's
   dyadic factorisation). *)
Lemma r_mult_plus_distr_l : forall a x y : Real,
  real_eq (real_mult a (real_plus x y)) (real_plus (real_mult a x) (real_mult a y)).
Proof. intros a x y. rring. Qed.
Lemma r_mult_rotate : forall a b c : Real,
  real_eq (real_mult a (real_mult b c)) (real_mult b (real_mult c a)).
Proof. intros a b c. rring. Qed.
(* (1 - s) pointwise forms. *)
Lemma r_one_minus_opp : forall s L : Real,
  real_eq (real_mult (real_plus real_one (real_opp s)) L)
          (real_mult (real_opp (real_plus s (real_opp real_one))) L).
Proof. intros s L. rring. Qed.
Lemma r_one_minus_le : forall s0 s : Real, real_le s0 s ->
  real_le (real_plus real_one (real_opp s)) (real_plus real_one (real_opp s0)).
Proof.
  intros s0 s Hle.
  apply (real_le_plus_compat real_one real_one (real_opp s) (real_opp s0)).
  - apply real_le_refl.
  - unfold real_le in Hle. unfold real_le. destruct Hle as [Hlt | Heq].
    + exact (inl (r_lt_opp_flip s0 s Hlt)).
    + exact (inr (RealSetoid.real_eq_opp_compat s s0 (real_eq_sym _ _ Heq))).
Qed.
(* Exponential is monotone in the decided le. *)
Lemma r_exp_le_mono : forall a b : Real, real_le a b -> real_le (cauchy_real_exp a) (cauchy_real_exp b).
Proof.
  intros a b H. unfold real_le in H. unfold real_le. destruct H as [Hlt | Heq].
  - exact (inl (cauchy_real_exp_mono a b Hlt)).
  - exact (inr (cauchy_real_exp_wd a b Heq)).
Qed.
(* Positivity-argument congruence of the sigT inverse, via the correctness
   law (no inv_pos wd face in tree). *)
Lemma r_inv_wd : forall (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
  real_eq x y -> real_eq (real_inv_pos x Hx) (real_inv_pos y Hy).
Proof.
  intros x y Hx Hy Hxy.
  pose proof (real_inv_pos_correct x Hx) as Hcx.
  pose proof (real_inv_pos_correct y Hy) as Hcy.
  assert (Hixy : real_eq (real_mult (real_inv_pos x Hx) y) real_one).
  { apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) x)).
    - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | apply (real_eq_sym _ _ Hxy)].
    - apply (real_eq_trans _ (real_mult x (real_inv_pos x Hx))).
      + apply real_mult_comm.
      + exact Hcx. }
  apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) real_one)).
  { apply (real_eq_sym _ _). apply real_mult_one. }
  apply (real_eq_trans _ (real_mult (real_inv_pos x Hx) (real_mult y (real_inv_pos y Hy)))).
  - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl | apply (real_eq_sym _ _ Hcy)].
  - apply (real_eq_trans _ (real_mult (real_mult (real_inv_pos x Hx) y) (real_inv_pos y Hy))).
    + apply real_mult_assoc.
    + apply (real_eq_trans _ (real_mult real_one (real_inv_pos y Hy))).
      * apply RealSetoid.real_eq_mult_compat; [exact Hixy | apply real_eq_refl].
      * apply (real_eq_trans _ (real_inv_pos y Hy)).
        -- apply real_mult_one_l.
        -- apply real_eq_refl.
Qed.

(* 1 + r*i == i whenever (1 - r)*i == 1 (the geometric constant in
   multiplied form folds onto the sigT inverse). *)
Lemma r_geom_inv_fold : forall r i : Real,
  real_eq (real_mult (real_plus real_one (real_opp r)) i) real_one ->
  real_eq (real_plus real_one (real_mult r i)) i.
Proof.
  intros r i H.
  apply (real_eq_trans _ (real_plus (real_mult (real_plus real_one (real_opp r)) i) (real_mult r i))).
  - apply (RealSetoid.real_eq_plus_compat real_one (real_mult r i)
             (real_mult (real_plus real_one (real_opp r)) i) (real_mult r i)).
    + apply (real_eq_sym _ _ H).
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_mult (real_plus (real_plus real_one (real_opp r)) r) i)).
    + apply (real_eq_sym _ _). apply r_mult_plus_distr.
    + apply (real_eq_trans _ (real_mult real_one i)).
      * apply (RealSetoid.real_eq_mult_compat (real_plus (real_plus real_one (real_opp r)) r) i real_one i).
        -- rring.
        -- apply real_eq_refl.
      * apply real_mult_one_l.
Qed.
(* ln of an embedded natural is nonnegative (consumed by the uniform form). *)
Lemma r_ln_nonneg : forall (Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n))
  (n : nat) (Hn : NatLe 1 n), real_le real_zero (real_log (nat_real n) (Hnpos n Hn)).
Proof.
  intros Hnpos n Hn. destruct (Nat.eq_dec n 1) as [Heq | Hne].
  - subst n. apply r_le_of_eq. apply (real_eq_sym _ _).
    apply (real_eq_trans _ (real_log real_one (real_lt_zero_one))).
    + apply (real_log_wd (nat_real 1) real_one). apply nat_real_one.
    + apply (real_log_one real_lt_zero_one).
  - assert (Hlt1 : (1 < n)%nat)
      by (assert (Hge : (1 <= n)%nat) by (apply NatLe_drop; exact Hn); lia).
    apply (real_lt_le_iff real_zero (real_log (nat_real n) (Hnpos n Hn))). left.
    apply (real_eq_lt_lt _ (real_log (nat_real 1%nat) (Hnpos 1%nat (NatLe_one_S 0%nat)))).
    + apply (real_eq_sym _ _).
      apply (real_eq_trans _ (real_log real_one (real_lt_zero_one))).
      * apply (real_log_wd (nat_real 1) real_one). apply nat_real_one.
      * apply (real_log_one real_lt_zero_one).
    + apply (real_log_lt_mono (nat_real 1) (nat_real n)).
      apply nat_real_lt. apply NatLe_lift. lia.
Qed.

(* ==== Abstract geometric partial sums (no log faces) ==== *)
Fixpoint r_qpow (q : Real) (j : nat) : Real :=
  match j with O => real_one | S i => real_mult (r_qpow q i) q end.
Fixpoint r_gsum (q : Real) (J : nat) : Real :=
  match J with O => real_zero | S i => real_plus (r_gsum q i) (r_qpow q i) end.

Lemma r_qpow_pos : forall (q : Real) (Hq : real_lt real_zero q) (j : nat),
  real_lt real_zero (r_qpow q j).
Proof.
  intros q Hq j. induction j as [|j IH].
  - exact real_lt_zero_one.
  - apply real_mult_positive; [exact IH | exact Hq].
Qed.

(* (sum_{j<J} q^j)*(1-q) <= 1 - q^J; multiplied form, no division anywhere. *)
Lemma r_gsum_mult : forall (q : Real) (J : nat),
  real_le (real_mult (r_gsum q J) (real_plus real_one (real_opp q)))
          (real_plus real_one (real_opp (r_qpow q J))).
Proof.
  intros q J. induction J as [|J IH].
  - cbn [r_gsum r_qpow]. apply r_le_of_eq. rring.
  - cbn [r_gsum r_qpow].
    apply (RealSetoid.real_le_compat _ _ _ _
             (real_eq_sym _ _ (r_mult_plus_distr (r_gsum q J) (r_qpow q J)
                (real_plus real_one (real_opp q)))) (real_eq_refl _)).
    apply (real_le_trans _
      (real_plus (real_plus real_one (real_opp (r_qpow q J)))
                 (real_plus (real_mult (r_qpow q J) real_one)
                            (real_opp (real_mult (r_qpow q J) q))))).
    + apply real_le_plus_compat.
      * exact IH.
      * apply r_le_of_eq. apply (r_expand (r_qpow q J) real_one q).
    + apply r_le_of_eq. apply r_tuck.
Qed.

(* Strict form: (sum_{j<J} q^j)*(1-q) < 1 whenever 0 < q (the slack q^J > 0). *)
Lemma r_gsum_lt_one : forall (q : Real) (Hq0 : real_lt real_zero q) (J : nat),
  real_lt (real_mult (r_gsum q J) (real_plus real_one (real_opp q))) real_one.
Proof.
  intros q Hq0 J.
  apply (real_le_lt_trans _ (real_plus real_one (real_opp (r_qpow q J)))).
  - apply r_gsum_mult.
  - apply (real_lt_eq_lt _ (real_plus real_one real_zero)).
    + apply real_lt_plus_translate. apply real_lt_zero_opp. apply (r_qpow_pos q Hq0).
    + apply (r_plus_zero_r_gen real_one).
Qed.

Lemma r_gsum_bound : forall (q : Real) (Hq0 : real_lt real_zero q)
  (Hq1 : real_lt q real_one) (J : nat),
  real_le (real_mult (r_gsum q J) (real_plus real_one (real_opp q))) real_one.
Proof.
  intros q Hq0 Hq1 J. apply (real_lt_le_iff _ _). left. apply r_gsum_lt_one. exact Hq0.
Qed.

(* Real-part additivity on the carrier. *)
Lemma cRe_plus_wd : forall u v : Cx,
  real_eq (cRe (c_plus u v)) (real_plus (cRe u) (cRe v)).
Proof. intros [a b] [c d]. rring. Qed.

(* ==== nat faces for the dyadic condensation ==== *)
Lemma r_pow2_ge1 : forall k : nat, NatLe 1 (Nat.pow 2 k).
Proof.
  intro k. apply NatLe_lift. induction k as [|k IH].
  - apply Nat.le_refl.
  - cbn [Nat.pow]. lia.
Qed.

(* Dyadic cover: every N lies below M * 2^K for some K (Set-sorted sigT). *)
Lemma nat_dyadic_cover : forall M N : nat, NatLe 1 M ->
  sigT (fun K : nat => NatLe N (M * Nat.pow 2 K)).
Proof.
  intros M N HM. apply NatLe_drop in HM. induction N as [|N [K HK]].
  - exists 0%nat. apply NatLe_lift. apply Nat.le_0_l.
  - apply NatLe_drop in HK. exists (S K). apply NatLe_lift.
    pose proof (NatLe_drop _ _ (r_pow2_ge1 K)) as Hp.
    cbn [Nat.pow]. nia.
Qed.
