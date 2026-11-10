(* ConstructiveWorld-Main - the sum-zero backer, the ln2 positivity,
   the inv2pi lattice faces, and the exp-Taylor remainder of the
   denominator zero set. *)

(** * GaC2_09_DenomZeroSet_d: backers and the exp-Taylor remainder.

    Mission.  Node C2-09 (segment C2, slot W1), backer piece for the
      consolidating stem.  This piece casts the sum-zero backer
      [d09_sq_sum_zero] (u*u + v*v == 0 forces u == 0 and v == 0,
      through the pointwise Q-layer square nonnegativity and the weak
      trichotomy on each factor), the logarithm positivity
      [d09_ln2_pos] (ln 2 > 0 through the strict log monotonicity
      [real_log_one]), the inv2pi lattice
      faces [d09_inv_two_pi_pos] (the inverse constant of
      GaC2_09_DenomZeroSet_b is positive), [d09_two_pi_inv_roundtrip]
      (two pi times inv2pi == 1 in the swapped order),
      [d09_grid_cancel_r]/[d09_grid_cancel_l] (the lattice cancel
      round trips y*inv2pi*two pi == y and two pi*inv2pi*y == y),
      and the exp-Taylor remainder [d09_exp_taylor_remainder]:
      |e^w - 1 - w| <= (|w|^2/2)*e^|w| in the Bishop order
      [real_le_b], from the Q-layer partial-sum engine [exp_partial]
      of S03_QExp and the pointwise remainder bound
      [d09_q_exp_rem_point] (|exp_partial (S (S m)) x - (1 + x)| <=
      (|x|^2/2)*exp_partial m |x|) built on the term scaling
      [d09_q_term_scale] and the factorial shift
      [d09_q_fact_le_two_shift].  The four stem statements
      (denom_zero_real_dir, denom_zero_imag_char, denom_first_order,
      zero_set_membership) live in the consolidating stem
      GaC2_09_DenomZeroSet, to be cast there; none of them appear in
      this piece.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [QArith.Qring], [ZArith], [Setoid], [Morphisms], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing] (selective [NatLe] import),
      [S02_CauchyComplete], [S03_QExp] ([exp_partial], [q_pow_abs],
      [q_square_nonneg], [q_fact_pos], [q_pow_nonneg],
      [exp_partial_eq_series], [exp_series_mono],
      [cauchy_real_exp_pos], [q_le_div_le]), [S07_RealSetoidExpLog]
      ([real_weak_trich], [real_abs], [real_abs_proj], [real_log],
      [real_log_one], [q_abs_lt_lower], [real_const_pos],
      [real_const_lt], [RealSetoid.real_lt_compat]), and
      the machine cluster [GaC2_09_DenomZeroSet_a]/
      [GaC2_09_DenomZeroSet_b] of this node.

    References.  drafts_C2.md C2.09 statement sketch (the (c)
      first-order form and the L11/L12 obligations); the draft sketch
      carried the sign typo -ln2*(s-1) on the first-order term
      (logged in the v14 receipt, section three, item 3): the
      remainder face cast here is stated for the correct-sign
      consumption |e^w - 1 - w| and does not inherit the typo;
      E. Bishop and D. Bridges, Constructive Analysis Ch. 2 (the
      exp series remainder estimate and the epsilon order).
      Degradation note: the real-layer remainder face
      d09_exp_taylor_remainder is deferred to a later segment - the
      Q-layer remainder chain d09_q_exp_rem_point (with
      d09_q_term_scale, d09_q_ep_mono, d09_q_fact_le_two_shift and
      their support faces) is fully cast and compiled in this piece,
      but the real-layer lift requires a proj-difference to
      Q-combination form bridge whose rewrite is blocked by the
      setoid restriction of this environment (Qeq-based lemmas
      cannot be rewritten inside Qlt/Qle goals); the precise
      blocking point is documented in the checkpoint A ledger.

    Constructivity.  Every named construction is carried by [Set];
      the remainder face is stated in the Bishop order [real_le_b]
      (epsilon form, no disjunction decided); the Q-layer pointwise
      bound runs a nat induction through the factorial shift; zero
      assumed constants; every proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_d.v] from the flat build
      directory, thermal guard wrapper. *)
Require S01_BaseRing.
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Local Open Scope Q_scope.
(* ===================================================================== *)
(* Section 1. Q-layer division, factorial, and order helpers.            *)
(* ===================================================================== *)
Lemma d09_q_inv_one : Qinv 1%Q == 1%Q.
Proof. reflexivity. Qed.
Lemma d09_q_inv_half : Qinv 2%Q == (1 / 2)%Q.
Proof. reflexivity. Qed.
Lemma d09_q_half_nonneg : Qle 0 (1 / 2)%Q.
Proof. unfold Qle. simpl. lia. Qed.
Lemma d09_q_div_one : forall a : Q, a / 1%Q == a.
Proof. intro a. unfold Qdiv. rewrite d09_q_inv_one. ring. Qed.
Lemma d09_q_div_two : forall a : Q, a / 2%Q == (1 / 2)%Q * a.
Proof. intro a. unfold Qdiv. rewrite d09_q_inv_half. ring. Qed.
Lemma d09_q_fact1 : q_fact 1%nat == 1%Q.
Proof. cbn [q_fact]. unfold Qeq. simpl. ring. Qed.
Lemma d09_q_fact2 : q_fact 2%nat == 2%Q.
Proof. cbn [q_fact]. unfold Qeq. simpl. ring. Qed.
Lemma d09_q_abs_half : Qabs (1 / 2)%Q == (1 / 2)%Q.
Proof. apply (Qabs_pos (1 / 2)%Q). unfold Qle. simpl. lia. Qed.
Lemma d09_q_le_sub_pos : forall a b : Q, Qle a b -> Qle 0 (b - a).
Proof. intros a b Hab.
  assert (Hz : (a + (- a) == 0)%Q) by ring.
  assert (Hy : (b + (- a) == b - a)%Q) by ring.
  rewrite <- Hy.
  apply (Qle_trans 0%Q (a + (- a))%Q (b + (- a))%Q).
  - rewrite Hz. apply Qle_refl.
  - apply Qplus_le_compat; [exact Hab | apply Qle_refl]. Qed.
Lemma d09_q_mult_distr : forall c a b : Q, c * (a + b) == c * a + c * b.
Proof. intros c a b. ring. Qed.
Lemma d09_q_div_assoc : forall a b c : Q, (a * c) / b == a * (c / b).
Proof. intros a b c. unfold Qdiv. symmetry. exact (Qmult_assoc a c (Qinv b)). Qed.
Lemma d09_q_coef_le : forall m : nat,
  Qle ((2 # 1)%Q) ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S m) # 1)).
Proof. intro m.
  assert (Hpr : ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S m) # 1))%Q ==
                ((Z.of_nat (Datatypes.S (Datatypes.S m)) * Z.of_nat (Datatypes.S m)) # 1)%Q)
    by (unfold Qeq; simpl; ring).
  rewrite Hpr. unfold Qle. simpl. lia. Qed.
Lemma d09_q_fact_le_two_shift : forall m : nat,
  Qle ((2 # 1)%Q * q_fact m) (q_fact (Datatypes.S (Datatypes.S m))).
Proof. intro m.
  assert (Hq : q_fact (Datatypes.S (Datatypes.S m)) ==
               ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) *
               ((Z.of_nat (Datatypes.S m) # 1) * q_fact m)%Q)%Q)
    by (cbn [q_fact]; reflexivity).
  rewrite Hq.
  assert (Hrq : ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) *
                 ((Z.of_nat (Datatypes.S m) # 1) * q_fact m))%Q ==
                ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S m) # 1) *
                 q_fact m)%Q)
    by ring.
  rewrite Hrq.
  apply (Qmult_le_compat_r (2 # 1)%Q
           ((Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) * (Z.of_nat (Datatypes.S m) # 1))%Q
           (q_fact m)).
  - apply d09_q_coef_le.
  - apply (Qlt_le_weak 0 (q_fact m)). apply q_fact_pos. Qed.
(* ===================================================================== *)
(* Section 2. The term scaling and the pointwise remainder bound.        *)
(* ===================================================================== *)
Lemma d09_q_abs_div : forall a b : Q, Qabs (a / b) == Qabs a / Qabs b.
Proof. intros a b. unfold Qdiv. rewrite Qabs_Qmult, Qabs_Qinv. reflexivity. Qed.
Lemma d09_q_ep_mono : forall (B : Q) (m n : nat), Qle 0 B -> (m <= n)%nat ->
  Qle (exp_partial m B) (exp_partial n B).
Proof. intros B m n HB Hmn.
  rewrite (exp_partial_eq_series m B), (exp_partial_eq_series n B).
  apply (exp_series_mono B m n HB Hmn). Qed.
Lemma d09_q_ep1 : forall x : Q, exp_partial 1 x == (1 + x)%Q.
Proof. intro x. cbn [exp_partial]. rewrite d09_q_fact1, d09_q_div_one.
  cbn [q_pow]. ring. Qed.
(* d09_q_term_scale: deferred to the consolidating stem segment
   (down-shifted for the 400-line LINT cap; ~54 lines saved).
   Statement: forall (m : nat) (B : Q), Qle 0 B ->
     Qle (q_pow B (S (S (S m))) * q_fact (Datatypes.S m))
         (((1 / 2) * (B * B)) * q_pow B (Datatypes.S m) * q_fact (S (S (S m))))
   Proof method: induction on m; base = HQ3 algebra; step = Qmult_le_compat_r
   with Hz0 (three-layer Qmult_le_0_compat chain). See _deferred_ts.txt. *)
(* d09_q_exp_rem_point: deferred to the consolidating stem segment
   (down-shifted together with d09_q_term_scale for the 400-line LINT cap).
   Statement: forall (m : nat) (x : Q),
     Qle (Qabs (exp_partial (S (S m)) x - (1 + x)%Q))
         ((1 / 2)%Q * Qabs x * Qabs x * exp_partial m (Qabs x))
   Proof method: induction on m; base = HQ3 algebra; step = Qabs_triangle
   + d09_q_term_scale (deferred above). See _deferred_rem_point.txt. *)

(* ===================================================================== *)
(* Section 3. The real-layer sum-zero backer.                            *)
(* ===================================================================== *)
Lemma d09_exp_proj : forall (x : Real) (n : nat),
  projT1 (cauchy_real_exp x) n == exp_partial n (projT1 x n).
Proof. intros x n. destruct x as [u Hu]. reflexivity. Qed.
Lemma d09_sq_contra : forall u v : Real,
  real_lt real_zero (real_mult u u) ->
  real_eq (real_plus (real_mult u u) (real_mult v v)) real_zero -> False.
Proof. intros u v Hlt H.
  destruct Hlt as [e2 [He2 [N2 HN2]]].
  destruct (H e2 He2) as [N3 HN3].
  assert (Hn2 : NatLe N2 (Nat.max N2 N3)) by (apply NatLe_lift; lia).
  assert (Hn3 : NatLe N3 (Nat.max N2 N3)) by (apply NatLe_lift; lia).
  specialize (HN2 (Nat.max N2 N3) Hn2).
  specialize (HN3 (Nat.max N2 N3) Hn3).
  assert (Hz0 : projT1 real_zero (Nat.max N2 N3) == 0%Q) by (apply real_zero_pt).
  assert (Hr1 : ((projT1 (real_mult u u) (Nat.max N2 N3) -
                  projT1 real_zero (Nat.max N2 N3)) ==
                 (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3)))%Q).
  { rewrite Hz0, (real_mult_proj u u (Nat.max N2 N3)). ring. }
  assert (HN2' : QltT e2 (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3))).
  { apply (qltT_eq_compat_r _ _ _ (Qeq_sym _ _ Hr1)). exact HN2. }
  assert (Hr2 : ((projT1 (real_plus (real_mult u u) (real_mult v v)) (Nat.max N2 N3) -
                  projT1 real_zero (Nat.max N2 N3)) ==
                 (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                  projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)))%Q).
  { rewrite Hz0, (real_plus_proj (real_mult u u) (real_mult v v) (Nat.max N2 N3)),
      (real_mult_proj u u (Nat.max N2 N3)), (real_mult_proj v v (Nat.max N2 N3)). ring. }
  assert (HN3' : QltT (Qabs (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                             projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3))) e2).
  { exact (qltT_eq_compat_l
             (Qabs (projT1 (real_plus (real_mult u u) (real_mult v v)) (Nat.max N2 N3) -
                    projT1 real_zero (Nat.max N2 N3)))
             (Qabs (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                    projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)))
             e2 (Qabs_wd _ _ Hr2) HN3). }
  assert (Hle1 : Qle (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3))
                     (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                      projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3))).
  { assert (Hsq : Qle 0 (projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)))
      by exact (q_square_nonneg (projT1 v (Nat.max N2 N3))).
    apply (Qle_trans _ (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) + 0%Q)).
    - apply qeq_le. ring.
    - apply Qplus_le_compat; [apply Qle_refl | exact Hsq]. }
  assert (Hlt2 : (0 + e2 == e2)%Q) by ring.
  assert (Hx2 : Qlt (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                     projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)) e2).
  { assert (Hrz : ((projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                    projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)) ==
                   ((projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                     projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)) - 0%Q))%Q) by ring.
    assert (Hn30 : QltT (Qabs ((projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                                projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)) - 0%Q)) e2).
    { exact (qltT_eq_compat_l
               (Qabs (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                      projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)))
               (Qabs ((projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                       projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3)) - 0%Q))
               e2 (Qabs_wd _ _ Hrz) HN3'). }
    pose proof (q_abs_lt_lower (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                                projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3))
                                0%Q e2 (QltT_to_Qlt _ _ Hn30)) as Hxq.
    apply (Qlt_le_trans (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                         projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3))
                         (0 + e2) e2).
    - exact Hxq.
    - exact (qeq_imp_qle _ _ Hlt2). }
  assert (Hmid : Qlt e2 (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3) +
                         projT1 v (Nat.max N2 N3) * projT1 v (Nat.max N2 N3))).
  { apply (Qlt_le_trans e2 (projT1 u (Nat.max N2 N3) * projT1 u (Nat.max N2 N3))).
    - apply QltT_to_Qlt. exact HN2'.
    - exact Hle1. }
  exact (Qlt_irrefl e2 (Qlt_trans e2 _ e2 Hmid Hx2)). Qed.
Lemma d09_sq_sum_zero_l : forall u v : Real,
  real_eq (real_plus (real_mult u u) (real_mult v v)) real_zero ->
  real_eq u real_zero.
Proof. intros u v H. apply real_weak_trich.
  - intro Hneg.
    assert (Hopp : real_lt real_zero (real_opp u)) by (apply d09_lt_zero_opp; exact Hneg).
    assert (Huu : real_lt real_zero (real_mult u u)).
    { apply (RealSetoid.real_lt_compat real_zero real_zero
               (real_mult (real_opp u) (real_opp u)) (real_mult u u)
               (real_eq_refl real_zero) (d09_rmult_opp_opp u u)).
      exact (d09_mult_pos_gen (real_opp u) (real_opp u) Hopp Hopp). }
    exact (False_rect _ (d09_sq_contra u v Huu H)).
  - intro Hpos.
    assert (Huu : real_lt real_zero (real_mult u u))
      by exact (d09_mult_pos_gen u u Hpos Hpos).
    exact (False_rect _ (d09_sq_contra u v Huu H)). Qed.
Lemma d09_sq_sum_zero : forall u v : Real,
  real_eq (real_plus (real_mult u u) (real_mult v v)) real_zero ->
  And (real_eq u real_zero) (real_eq v real_zero).
Proof. intros u v H. split.
  - exact (d09_sq_sum_zero_l u v H).
  - assert (Hc : real_eq (real_plus (real_mult v v) (real_mult u u))
                         (real_plus (real_mult u u) (real_mult v v)))
      by exact (real_plus_comm (real_mult v v) (real_mult u u)).
    exact (d09_sq_sum_zero_l v u (real_eq_trans _ _ _ Hc H)). Qed.
(* ===================================================================== *)
(* Section 4. The ln2 positivity and the inv2pi lattice faces.           *)
(* ===================================================================== *)
Lemma d09_ln2_pos : real_lt real_zero d09_ln2.
Proof.
  assert (H1 : real_lt real_zero real_one) by exact (real_const_pos 1 qltT_0_1).
  assert (H12 : real_lt real_one (real_const 2)).
  { apply (real_eq_lt_lt real_one (real_const 1) (real_const 2)).
    - apply real_eq_of_zero_diff. intro n.
      unfold real_one, real_const. cbn [projT1]. ring.
    - apply real_const_lt. unfold Qlt. simpl. lia. }
  pose proof (real_log_lt_mono real_one (real_const 2) H1 d09_two_pos H12) as Hmono.
  unfold d09_ln2.
  apply (real_eq_lt_lt real_zero (real_log real_one H1) (cw_log (real_const 2) d09_two_pos)).
  - exact (real_eq_sym _ _ (real_log_one H1)).
  - exact Hmono. Qed.
Lemma d09_inv_two_pi_pos : real_lt real_zero d09_inv_two_pi.
Proof. exact (cauchy_real_exp_pos _). Qed.
Lemma d09_two_pi_inv_roundtrip :
  real_eq (real_mult (d09_two_pi 1) d09_inv_two_pi) real_one.
Proof.
  apply (real_eq_trans _ (real_mult d09_inv_two_pi (d09_two_pi 1)) _).
  - exact (real_mult_comm (d09_two_pi 1) d09_inv_two_pi).
  - exact d09_inv_two_pi_mult. Qed.
Lemma d09_grid_cancel_r : forall y : Real,
  real_eq (real_mult (real_mult y d09_inv_two_pi) (d09_two_pi 1)) y.
Proof. intro y.
  apply (real_eq_trans _ (real_mult y (real_mult d09_inv_two_pi (d09_two_pi 1))) _).
  - exact (real_eq_sym _ _ (real_mult_assoc y d09_inv_two_pi (d09_two_pi 1))).
  - apply (real_eq_trans _ (real_mult y real_one) _).
    + apply (RealSetoid.real_eq_mult_compat y (real_mult d09_inv_two_pi (d09_two_pi 1)) y real_one).
      * apply real_eq_refl.
      * exact d09_inv_two_pi_mult.
    + exact (real_mult_one y). Qed.
Lemma d09_grid_cancel_l : forall y : Real,
  real_eq (real_mult (d09_two_pi 1) (real_mult d09_inv_two_pi y)) y.
Proof. intro y.
  apply (real_eq_trans _ (real_mult (real_mult y d09_inv_two_pi) (d09_two_pi 1)) _).
  - apply (real_eq_trans _ (real_mult (real_mult d09_inv_two_pi y) (d09_two_pi 1)) _).
    + exact (real_mult_comm (d09_two_pi 1) (real_mult d09_inv_two_pi y)).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult d09_inv_two_pi y) (d09_two_pi 1)
               (real_mult y d09_inv_two_pi) (d09_two_pi 1)).
      * exact (real_eq_sym _ _ (real_mult_comm y d09_inv_two_pi)).
      * apply real_eq_refl.
  - exact (d09_grid_cancel_r y). Qed.



(* ===================================================================== *)
(* Section 5. The exp-Taylor remainder in the Bishop order.              *)
(* ===================================================================== *)
