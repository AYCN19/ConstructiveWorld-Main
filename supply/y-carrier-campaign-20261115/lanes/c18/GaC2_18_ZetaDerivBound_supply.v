(** * GaC2_18_ZetaDerivBound_supply: supply face of node C2-18.

    Mission.  Three supply items for the node C2-18 statement carriers
    [r_pos_lower] / [zeta_deriv_bound].  (1) A machine refutation of the minted
    [r_pos_lower] at the zero-lattice center [s0 = 1]: the minted carrier lacks
    a center-positivity premise and the k = 0 zero point of the denominator
    sits in the consumer domain, so the disk-wide denominator slot at the center
    contradicts any positive margin - the evidence behind the reined carrier
    [r_pos_lower_reined], which adds the missing premise.  (2) A conditional
    closure of the derivative bound: consuming [cauchy_est_n1], a circle-bound
    slot, a radius-floor slot and the binding C3 = 4 * C2 / c, it closes the
    squared conclusion of [zeta_deriv_bound]; the three C2-12 slots enter as
    explicit premise arguments.  (3) An alignment face for a caller-supplied
    disk proof.

    Dependencies.  Stdlib [QArith.QArith]; [S02_CauchyComplete], [S03_QExp],
    [S07_RealSetoidExpLog], [CxRealPairCore], [CxRealPairExpLog], [GaC2_09_DenomZeroSet_b],
    [GaC2_10_EtaContinuation], [GaC2_11_MaxModulusDisk], [GaC2_11_MaxModulusDisk_b],
    [GaC2_12_CauchyCoeffEst] with [_a] and [_c], [GaC2_18_ZetaDerivBound].

    References.  cards_C2.md C2.18 (the proof routes); Titchmarsh section 3.9
    (the derivative-bound consumption form); the C2-12 slot registers.

    Constructivity.  Every statement is Set-sorted ([real_lt] / [real_le] /
    [c_eq] / [sigT]); zero assumed constants, zero abandoned proofs, zero
    classical principles; premise slots are explicit arguments so every named
    item stays Closed under the global context; every lemma closes [Defined].

    Build.  [coqc -native-compiler no -q -Q . "" GaC2_18_ZetaDerivBound_supply.v]
    from the flat build directory that holds the compiled closure of the stem. *)

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_10_EtaContinuation.
Require Import GaC2_11_MaxModulusDisk.
Require Import GaC2_11_MaxModulusDisk_b.
Require Import GaC2_12_CauchyCoeffEst_a.
Require Import GaC2_12_CauchyCoeffEst_c.
Require Import GaC2_12_CauchyCoeffEst.
Require Import GaC2_18_ZetaDerivBound.

From Stdlib Require Import QArith.QArith.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The power carrier at the center and the refutation.         *)
(* ===================================================================== *)

(* Congruence of the scalar multiple under pointwise equality. *)
Lemma gaC18_scale_congr : forall (a : Real) (z w : Cx),
  c_eq z w -> c_eq (c_scale a z) (c_scale a w).
Proof.
  intros a z w Hz.
  unfold c_scale, c_eq in Hz.
  destruct Hz as [Hr Hi].
  cbn [fst snd] in Hr, Hi.
  unfold c_scale, c_eq.
  cbn [fst snd].
  split.
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + exact Hr.
  - apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + exact Hi.
Defined.

(* The scalar multiple of zero is zero. *)
Lemma gaC18_scale_zero : forall a : Real, c_eq (c_scale a c_zero) c_zero.
Proof.
  intro a.
  unfold c_scale, c_eq, c_zero.
  cbn [fst snd].
  split.
  - apply real_mult_zero.
  - apply real_mult_zero.
Defined.

(* The power carrier 2^(1-s) at the center s = 1 equals the unit: the
   exponent argument is the scalar multiple of zero, and the complex
   exponential of zero is the unit (the exponential congruence face of
   the C2-09 machine plus the exponential zero face). *)
Lemma gaC18_two_pow_1ms_at_one : c_eq (two_pow_1ms c_one) c_one.
Proof.
  apply (c_eq_trans _ (c_exp (c_scale d09_ln2 c_zero))).
  - apply d09_c_exp_congr.
    apply gaC18_scale_congr.
    exact (c_plus_opp c_one).
  - apply (c_eq_trans _ (c_exp c_zero)).
    + apply d09_c_exp_congr.
      exact (gaC18_scale_zero d09_ln2).
    + exact c_exp_zero.
Defined.

(* The denominator norm at the center is zero: the power carrier at the
   center is the unit, so the denominator is z + (-z), whose squared
   modulus vanishes (the norm face of the C2-11 machine). *)
Lemma gaC18_denom_center_zero :
  real_eq (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms c_one)))) real_zero.
Proof.
  apply (real_eq_trans
           (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms c_one))))
           (c_norm_sq (c_plus c_one (c_opp c_one)))).
  - apply mm_norm_wd.
    apply c_plus_congr.
    + apply c_eq_refl.
    + apply c_opp_congr.
      exact gaC18_two_pow_1ms_at_one.
  - exact (mm_norm_self_opp c_one).
Defined.

(* Machine refutation of the minted [r_pos_lower] carrier at the center
   s0 = 1.  The consumer domain contains the center for every admissible
   cap (its real part is the unit, its imaginary part is zero), and the
   disk-wide denominator slot instantiated at the center itself (the
   zero-distance point) forces the margin strictly below zero, against
   the strict positivity premise.  The minted carrier lacks a
   center-positivity premise; the reined carrier below restores it. *)
Lemma gaC18_r_pos_lower_refuted :
  forall (T c : Real) (HT : real_le (real_const (2#1)) (t_cap T))
         (HT1 : real_lt real_one (t_cap T))
         (Hlogpos : real_lt real_zero (log_t T HT1))
         (eps_lb : Real) (Hep : real_lt real_zero eps_lb)
         (Hdom : consumer_domain T c HT1 Hlogpos c_one),
  r_pos_lower T c HT HT1 Hlogpos eps_lb Hep c_one Hdom -> False.
Proof.
  intros T c HT HT1 Hlogpos eps_lb Hep Hdom Hr.
  destruct Hr as [r [Hrpos [Hdenom _]]].
  assert (Hself : real_le (c_norm_sq (c_plus c_one (c_opp c_one))) (sq r)).
  { apply (RealSetoid.real_le_compat
             (c_norm_sq (c_plus c_one (c_opp c_one)))
             real_zero
             (sq r) (sq r)).
    - exact (mm_norm_self_opp c_one).
    - apply real_eq_refl.
    - apply (real_lt_le_iff real_zero (sq r)).
      left.
      exact (real_mult_positive r r Hrpos Hrpos). }
  assert (Hbad : real_lt eps_lb real_zero).
  { apply (real_lt_eq_lt eps_lb
             (c_norm_sq (c_plus c_one (c_opp (two_pow_1ms c_one))))
             real_zero).
    - exact (Hdenom c_one Hself).
    - exact gaC18_denom_center_zero. }
  exact (match real_lt_irrefl real_zero
                   (real_lt_trans real_zero eps_lb real_zero Hep Hbad) with end).
Defined.

(* The reined radius carrier: the minted statement face restored to
   consistency by the center-positivity premise [Hcen].  Statement
   carrier only; the body closes when the distance-propagation machine
   of the L26 slot (a lower bound of the denominator on a disk around a
   center of positive margin) lands. *)
Definition r_pos_lower_reined
  (T c : Real) (HT : real_le (real_const (2#1)) (t_cap T))
  (HT1 : real_lt real_one (t_cap T))
  (Hlogpos : real_lt real_zero (log_t T HT1))
  (eps_lb : Real) (Hep : real_lt real_zero eps_lb)
  (s0 : Cx) (Hdom : consumer_domain T c HT1 Hlogpos s0)
  (Hcen : GaC2_10_EtaContinuation.denom_nz eps_lb s0) : Set :=
  sigT (fun r : Real =>
    sigT (fun _ : real_lt real_zero r =>
      sigT (fun _ : forall z : Cx,
              real_le (c_norm_sq (c_plus z (c_opp s0))) (sq r) ->
              GaC2_10_EtaContinuation.denom_nz eps_lb z =>
        disk_in_consumer T c HT1 Hlogpos s0 r))).

(* ===================================================================== *)
(* Section 2. Order algebra helpers for the bound closure.                *)
(* ===================================================================== *)

(* Two times two is four at the constant layer (the Q literal product
   computes). *)
Lemma gaC18_two_two_four :
  real_eq (real_mult (real_const (2#1)) (real_const (2#1))) (real_const (4#1)).
Proof.
  exact (d09_const_mult (2#1) (2#1)).
Defined.

(* Multiplication on a common strictly positive factor replaces both
   sides pointwise. *)
Lemma gaC18_le_mult_compat_eq : forall (a b x y : Real),
  real_lt real_zero x -> real_eq x y -> real_le a b ->
  real_le (real_mult a x) (real_mult b y).
Proof.
  intros a b x y Hx Hxy Hab.
  apply (real_le_trans (real_mult a x) (real_mult b x) (real_mult b y)).
  - exact (real_le_mult_compat a b x Hx Hab).
  - apply (RealSetoid.real_le_compat (real_mult b x) (real_mult b x)
                                     (real_mult b x) (real_mult b y)).
    + apply real_eq_refl.
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * exact Hxy.
    + apply real_le_refl.
Defined.

(* Squared monotonicity on strictly positive arguments: from a <= b the
   square order follows, with no square-root dependence. *)
Lemma gaC18_sq_mono : forall a b : Real,
  real_lt real_zero a -> real_lt real_zero b -> real_le a b ->
  real_le (real_mult a a) (real_mult b b).
Proof.
  intros a b Ha Hb Hab.
  assert (Hale : real_le real_zero a) by exact (real_lt_le_iff _ _ (inl Ha)).
  assert (Hble : real_le real_zero b) by exact (real_lt_le_iff _ _ (inl Hb)).
  apply (real_le_trans (real_mult a a) (real_mult b a) (real_mult b b)).
  - exact (real_le_mult_compat_weak a b a Hale Hab).
  - apply (RealSetoid.real_le_compat (real_mult a b) (real_mult b a)
                                     (real_mult b b) (real_mult b b)).
    + exact (real_mult_comm a b).
    + apply real_eq_refl.
    + exact (real_le_mult_compat_weak a b b Hble Hab).
Defined.

(* The radius-floor transfer: from c * u^(-1) <= r the inverse order
   r^(-1) <= u * c^(-1) follows, with the product-inverse identity
   carried by the uniqueness face of the positive-inverse carrier. *)
Lemma gaC18_inv_floor_transfer :
  forall (r c u : Real)
         (HR : real_lt real_zero r) (Hc : real_lt real_zero c)
         (Hu : real_lt real_zero u)
         (Hfloor : real_le (real_mult c (real_inv_pos u Hu)) r),
  real_le (real_inv_pos r HR)
          (real_mult u (real_inv_pos c Hc)).
Proof.
  intros r c u HR Hc Hu Hfloor.
  assert (HX : real_lt real_zero (real_mult c (real_inv_pos u Hu))).
  { exact (real_mult_positive c (real_inv_pos u Hu) Hc
             (real_inv_pos_pos u Hu)). }
  assert (HXY : real_eq
             (real_mult (real_mult c (real_inv_pos u Hu))
                        (real_mult u (real_inv_pos c Hc)))
             real_one).
  { apply (real_eq_trans
             (real_mult (real_mult c (real_inv_pos u Hu))
                        (real_mult u (real_inv_pos c Hc)))
             (real_mult c (real_mult (real_inv_pos u Hu)
                                     (real_mult u (real_inv_pos c Hc))))).
    - exact (real_eq_sym _ _ (real_mult_assoc c (real_inv_pos u Hu)
               (real_mult u (real_inv_pos c Hc)))).
    - apply (real_eq_trans
               (real_mult c (real_mult (real_inv_pos u Hu)
                                       (real_mult u (real_inv_pos c Hc))))
               (real_mult c (real_mult (real_mult (real_inv_pos u Hu) u)
                                       (real_inv_pos c Hc)))).
      + apply RealSetoid.real_eq_mult_compat.
        * apply real_eq_refl.
        * exact (real_mult_assoc (real_inv_pos u Hu) u (real_inv_pos c Hc)).
      + apply (real_eq_trans
                 (real_mult c
                  (real_mult (real_mult (real_inv_pos u Hu) u)
                             (real_inv_pos c Hc)))
                 (real_mult c
                  (real_mult real_one (real_inv_pos c Hc)))).
        * apply RealSetoid.real_eq_mult_compat.
          -- apply real_eq_refl.
          -- apply RealSetoid.real_eq_mult_compat.
             ++ exact (real_eq_trans _ _ _ (real_mult_comm (real_inv_pos u Hu) u)
                        (real_inv_pos_correct u Hu)).
             ++ apply real_eq_refl.
        * apply (real_eq_trans
                   (real_mult c (real_mult real_one (real_inv_pos c Hc)))
                   (real_mult c (real_inv_pos c Hc))).
          -- apply RealSetoid.real_eq_mult_compat.
             ++ apply real_eq_refl.
             ++ exact (real_mult_one_l (real_inv_pos c Hc)).
          -- exact (real_inv_pos_correct c Hc). }
  assert (HinvX : real_eq
             (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX)
             (real_mult u (real_inv_pos c Hc))).
  { exact (real_inv_unique (real_mult c (real_inv_pos u Hu))
             (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX)
             (real_mult u (real_inv_pos c Hc))
             (real_inv_pos_correct (real_mult c (real_inv_pos u Hu)) HX)
             HXY). }
  unfold real_le in Hfloor.
  destruct Hfloor as [Hflt | Heq].
  - apply (real_lt_le_iff (real_inv_pos r HR)
             (real_mult u (real_inv_pos c Hc))).
    left.
    exact (real_lt_eq_lt (real_inv_pos r HR)
             (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX)
             (real_mult u (real_inv_pos c Hc))
             (real_inv_lt_contra (real_mult c (real_inv_pos u Hu)) r HX HR Hflt)
             HinvX).
  - unfold real_le.
    right.
    assert (HrinvX : real_eq
               (real_mult r
                  (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX))
               real_one).
    { apply (real_eq_trans
               (real_mult r
                  (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX))
               (real_mult (real_mult c (real_inv_pos u Hu))
                  (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX))).
      - apply RealSetoid.real_eq_mult_compat.
        + exact (real_eq_sym _ _ Heq).
        + apply real_eq_refl.
      - exact (real_inv_pos_correct (real_mult c (real_inv_pos u Hu)) HX). }
    exact (real_eq_trans
             (real_inv_pos r HR)
             (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX)
             (real_mult u (real_inv_pos c Hc))
             (real_inv_unique r (real_inv_pos r HR)
                (real_inv_pos (real_mult c (real_inv_pos u Hu)) HX)
                (real_inv_pos_correct r HR)
                HrinvX)
             HinvX).
Defined.

(* The constant-binding algebra: two times (C2 * L * (two * L * c^(-1)))
   equals (four * C2 * c^(-1)) * (L * L), the reshuffle behind the C3 =
   4 * C2 / c binding.  The real product is pointwise at the sequence
   level, so the identity closes by the rational ring after the
   projection rewrites. *)
Lemma gaC18_c3_algebra : forall (C2 L ic : Real),
  real_eq (real_mult (real_const (2#1))
            (real_mult (real_mult C2 L)
                       (real_mult (real_mult (real_const (2#1)) L) ic)))
          (real_mult (real_mult (real_const (4#1)) (real_mult C2 ic))
                     (real_mult L L)).
Proof.
  intros C2 L ic.
  apply real_eq_of_zero_diff.
  intro n.
  rewrite (real_mult_proj (real_const (2#1))
             (real_mult (real_mult C2 L)
                        (real_mult (real_mult (real_const (2#1)) L) ic)) n).
  rewrite (real_mult_proj (real_mult C2 L)
             (real_mult (real_mult (real_const (2#1)) L) ic) n).
  rewrite (real_mult_proj C2 L n).
  rewrite (real_mult_proj (real_mult (real_const (2#1)) L) ic n).
  rewrite (real_mult_proj (real_const (2#1)) L n).
  rewrite (real_mult_proj (real_mult (real_const (4#1)) (real_mult C2 ic))
             (real_mult L L) n).
  rewrite (real_mult_proj (real_const (4#1)) (real_mult C2 ic) n).
  rewrite (real_mult_proj C2 ic n).
  rewrite (real_mult_proj L L n).
  rewrite (real_const_proj (2#1) n).
  rewrite (real_const_proj (4#1) n).
  cbn [projT1 real_const].
  ring.
Defined.

(* ===================================================================== *)
(* Section 3. The conditional closure of the derivative bound.            *)
(* ===================================================================== *)

(* The explicit C3 binding form: four times C2 times the inverse of the
   consumer-domain constant c (division-free through the positive
   inverse). *)
Definition gaC18_c3_form (C2 c : Real) (Hc : real_lt real_zero c) : Real :=
  real_mult (real_const (4#1)) (real_mult C2 (real_inv_pos c Hc)).

(* The difference-quotient chain slot of the C2-12 machine, restated at
   the point [s0] and radius [r] of the C2-18 consumer face (the
   discharged section definition [cauchy_Hz0] supplies the canonical
   center-disk proof). *)
Definition gaC18_chain_slot (s0 : Cx) (r : Real)
           (HR : real_lt real_zero r) : Set :=
  forall (g : Cx -> Cx) (Hg : gaC12_local_exp_seq g s0 r),
    sigT (fun g1 : Cx -> Cx =>
      sigT (fun Hg1 : gaC12_local_exp_seq g1 s0 r =>
        S01_BaseRing.And
          (forall (q : Cx)
                  (Hq : real_lt real_zero (c_norm_sq (c_plus q (c_opp s0)))),
             c_eq (g1 q) (gaC12_cx_dquot g s0 q Hq))
          (forall (n : nat),
             c_eq (gaC12_nth_coeff n g1 s0 s0 r Hg1 (cauchy_Hz0 s0 r HR))
                  (gaC12_nth_coeff (S n) g s0 s0 r Hg (cauchy_Hz0 s0 r HR))))).

(* Order transfer under a pointwise identification of the right side.  *)
Lemma gaC18_le_eq_swap : forall (a b c : Real),
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hab Hbc.
  exact (RealSetoid.real_le_compat a a b c (real_eq_refl a) Hbc Hab).
Defined.

(* The conditional closure: the squared first-coefficient face of the
   C2-12 estimate consumed at the circle bound M, the vertical transfer
   M <= C2 * log(cap), the radius floor c / (2 * log(cap)) <= r and the
   explicit binding C3 = 4 * C2 / c close the squared conclusion of the
   minted [zeta_deriv_bound] carrier.  The three C2-12 analytic slots
   (norm nonnegativity, strict maximum modulus gate, difference-quotient
   chain) remain explicit premise arguments. *)
Lemma gaC18_deriv_bound_closure :
  forall (T c C2 r M : Real)
         (HT1 : real_lt real_one (t_cap T))
         (Hlogpos : real_lt real_zero (log_t T HT1))
         (Hc : real_lt real_zero c) (HC2 : real_lt real_zero C2)
         (HR : real_lt real_zero r)
         (Hu2 : real_lt real_zero (c_scale' (real_const (2#1)) (log_t T HT1)))
         (HMpos : real_lt real_zero M)
         (Hfloor : real_le (c_scale' c
                      (real_inv_pos (c_scale' (real_const (2#1)) (log_t T HT1))
                        Hu2))
                    r)
         (HM : real_le M (c_scale' C2 (log_t T HT1)))
         (g : Cx -> Cx) (s0 : Cx)
         (Hloc : gaC12_local_exp_seq g s0 r)
         (Hcirc : boundary_bounded g s0 r (gaC12_sq M))
         (Hnn : forall v : Cx, real_le real_zero (c_norm_sq v))
         (Hmod_gate : forall (h : Cx -> Cx) (B : Real),
                        boundary_bounded h s0 r B -> real_le (c_norm_sq (h s0)) B)
         (Hchain : gaC18_chain_slot s0 r HR)
         (C3 : Real)
         (Hbind : real_eq C3 (gaC18_c3_form C2 c Hc)),
  real_le (c_norm_sq (gaC12_deriv1 g s0 s0 r Hloc (cauchy_Hz0 s0 r HR)))
          (sq (c_scale' C3 (sq (log_t T HT1)))).
Proof.
  intros T c C2 r M HT1 Hlogpos Hc HC2 HR Hu2 HMpos Hfloor HM g s0
         Hloc Hcirc Hnn Hmod_gate Hchain C3 Hbind.
  assert (Hest := cauchy_est_n1 g s0 r HR Hloc M Hcirc Hnn Hmod_gate Hchain).
  assert (Hinvc : real_lt real_zero (real_inv_pos c Hc))
    by exact (real_inv_pos_pos c Hc).
  assert (Hinvr : real_lt real_zero (real_inv_pos r HR))
    by exact (real_inv_pos_pos r HR).
  assert (HL2 : real_lt real_zero (sq (log_t T HT1)))
    by exact (real_mult_positive (log_t T HT1) (log_t T HT1) Hlogpos Hlogpos).
  assert (Ha : real_lt real_zero
                 (real_mult (real_const (2#1)) (gaC12_rdiv M r HR))).
  { exact (real_mult_positive (real_const (2#1)) (gaC12_rdiv M r HR)
             gaC12_two_pos
             (real_mult_positive M (real_inv_pos r HR) HMpos Hinvr)). }
  assert (Hb : real_lt real_zero
                 (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))).
  { exact (real_mult_positive (gaC18_c3_form C2 c Hc) (sq (log_t T HT1))
             (real_mult_positive (real_const (4#1))
                (real_mult C2 (real_inv_pos c Hc))
                (real_const_pos (4#1) S01_BaseRing.id_refl)
                (real_mult_positive C2 (real_inv_pos c Hc) HC2 Hinvc))
             HL2). }
  assert (Hs1 : real_le (real_mult M (real_inv_pos r HR))
                        (real_mult (c_scale' C2 (log_t T HT1))
                                   (real_inv_pos r HR))).
  { exact (gaC18_le_mult_compat_eq M (c_scale' C2 (log_t T HT1))
             (real_inv_pos r HR) (real_inv_pos r HR)
             Hinvr (real_eq_refl (real_inv_pos r HR)) HM). }
  assert (Hs2 : real_le (real_inv_pos r HR)
                        (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                                   (real_inv_pos c Hc))).
  { exact (gaC18_inv_floor_transfer r c
             (c_scale' (real_const (2#1)) (log_t T HT1)) HR Hc Hu2 Hfloor). }
  assert (HL : real_lt real_zero (c_scale' C2 (log_t T HT1)))
    by exact (real_mult_positive C2 (log_t T HT1) HC2 Hlogpos).
  assert (Hs3 : real_le (real_mult (c_scale' C2 (log_t T HT1))
                                   (real_inv_pos r HR))
                        (real_mult (c_scale' C2 (log_t T HT1))
                         (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                                    (real_inv_pos c Hc)))).
  { apply (RealSetoid.real_le_compat
             (real_mult (real_inv_pos r HR) (c_scale' C2 (log_t T HT1)))
             (real_mult (c_scale' C2 (log_t T HT1)) (real_inv_pos r HR))
             (real_mult (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                                   (real_inv_pos c Hc))
                        (c_scale' C2 (log_t T HT1)))
             (real_mult (c_scale' C2 (log_t T HT1))
              (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                         (real_inv_pos c Hc)))).
    - exact (real_mult_comm (real_inv_pos r HR) (c_scale' C2 (log_t T HT1))).
    - exact (real_mult_comm
               (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                          (real_inv_pos c Hc))
               (c_scale' C2 (log_t T HT1))).
    - exact (real_le_mult_compat_weak (real_inv_pos r HR)
               (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                          (real_inv_pos c Hc))
               (c_scale' C2 (log_t T HT1))
               (real_lt_le_iff real_zero (c_scale' C2 (log_t T HT1)) (inl HL))
               Hs2). }
  assert (Hs4 : real_le (real_mult (real_const (2#1))
                            (real_mult M (real_inv_pos r HR)))
                        (real_mult (real_const (2#1))
                         (real_mult (c_scale' C2 (log_t T HT1))
                          (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                                     (real_inv_pos c Hc))))).
  { apply (RealSetoid.real_le_compat
             (real_mult (real_mult M (real_inv_pos r HR)) (real_const (2#1)))
             (real_mult (real_const (2#1)) (real_mult M (real_inv_pos r HR)))
             (real_mult (real_mult (c_scale' C2 (log_t T HT1))
                        (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                                   (real_inv_pos c Hc)))
                        (real_const (2#1)))
             (real_mult (real_const (2#1))
              (real_mult (c_scale' C2 (log_t T HT1))
               (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                          (real_inv_pos c Hc))))).
    - exact (real_mult_comm (real_mult M (real_inv_pos r HR))
               (real_const (2#1))).
    - exact (real_mult_comm
               (real_mult (c_scale' C2 (log_t T HT1))
                (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                           (real_inv_pos c Hc)))
               (real_const (2#1))).
    - exact (gaC18_le_mult_compat_eq (real_mult M (real_inv_pos r HR))
               (real_mult (c_scale' C2 (log_t T HT1))
                (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                           (real_inv_pos c Hc)))
               (real_const (2#1)) (real_const (2#1))
               gaC12_two_pos (real_eq_refl (real_const (2#1)))
               (real_le_trans _ _ _ Hs1 Hs3)). }
  assert (Hs5 : real_le (real_mult (real_const (2#1))
                         (real_mult (c_scale' C2 (log_t T HT1))
                          (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                                     (real_inv_pos c Hc))))
                        (real_mult (gaC18_c3_form C2 c Hc)
                                   (sq (log_t T HT1)))).
  { apply (RealSetoid.real_le_compat
             (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))
             (real_mult (real_const (2#1))
              (real_mult (c_scale' C2 (log_t T HT1))
               (real_mult (c_scale' (real_const (2#1)) (log_t T HT1))
                          (real_inv_pos c Hc))))
             (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))
             (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))).
    - exact (real_eq_sym _ _
               (gaC18_c3_algebra C2 (log_t T HT1) (real_inv_pos c Hc))).
    - apply real_eq_refl.
    - apply real_le_refl. }
  apply (real_le_trans
           (c_norm_sq (gaC12_deriv1 g s0 s0 r Hloc (cauchy_Hz0 s0 r HR)))
           (gaC12_sq (real_mult (real_const (2#1)) (gaC12_rdiv M r HR)))
           (sq (c_scale' C3 (sq (log_t T HT1))))).
  - exact Hest.
  - exact (gaC18_le_eq_swap
             (gaC12_sq (real_mult (real_const (2#1)) (gaC12_rdiv M r HR)))
             (sq (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1))))
             (sq (c_scale' C3 (sq (log_t T HT1))))
             (gaC18_sq_mono
                (real_mult (real_const (2#1)) (gaC12_rdiv M r HR))
                (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))
                Ha Hb (real_le_trans _ _ _ Hs4 Hs5))
             (RealSetoid.real_eq_mult_compat
                (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))
                (real_mult (gaC18_c3_form C2 c Hc) (sq (log_t T HT1)))
                (real_mult C3 (sq (log_t T HT1)))
                (real_mult C3 (sq (log_t T HT1)))
                (RealSetoid.real_eq_mult_compat
                   (gaC18_c3_form C2 c Hc) (sq (log_t T HT1))
                   C3 (sq (log_t T HT1))
                   (real_eq_sym _ _ Hbind) (real_eq_refl (sq (log_t T HT1))))
                (RealSetoid.real_eq_mult_compat
                   (gaC18_c3_form C2 c Hc) (sq (log_t T HT1))
                   C3 (sq (log_t T HT1))
                   (real_eq_sym _ _ Hbind) (real_eq_refl (sq (log_t T HT1)))))).
Defined.

(* The alignment face: the closure at the canonical center disk
   transfers to a caller-supplied disk proof through the pointwise bond
   between the two projected first coefficients.  This is the premise
   the mother chain settles when it builds the expansion witness once. *)
Lemma gaC18_deriv_bound_at_prem :
  forall (T c C2 r M : Real)
         (HT1 : real_lt real_one (t_cap T))
         (Hlogpos : real_lt real_zero (log_t T HT1))
         (Hc : real_lt real_zero c) (HC2 : real_lt real_zero C2)
         (HR : real_lt real_zero r)
         (Hu2 : real_lt real_zero (c_scale' (real_const (2#1)) (log_t T HT1)))
         (HMpos : real_lt real_zero M)
         (Hfloor : real_le (c_scale' c
                      (real_inv_pos (c_scale' (real_const (2#1)) (log_t T HT1))
                        Hu2))
                    r)
         (HM : real_le M (c_scale' C2 (log_t T HT1)))
         (g : Cx -> Cx) (s0 : Cx)
         (Hloc : gaC12_local_exp_seq g s0 r)
         (Hp : gaC12_closed_disk s0 s0 r)
         (Hcirc : boundary_bounded g s0 r (gaC12_sq M))
         (Hnn : forall v : Cx, real_le real_zero (c_norm_sq v))
         (Hmod_gate : forall (h : Cx -> Cx) (B : Real),
                        boundary_bounded h s0 r B -> real_le (c_norm_sq (h s0)) B)
         (Hchain : gaC18_chain_slot s0 r HR)
         (C3 : Real)
         (Hbind : real_eq C3 (gaC18_c3_form C2 c Hc))
         (Hallign : c_eq (gaC12_deriv1 g s0 s0 r Hloc Hp)
                         (gaC12_deriv1 g s0 s0 r Hloc (cauchy_Hz0 s0 r HR))),
  real_le (c_norm_sq (gaC12_deriv1 g s0 s0 r Hloc Hp))
          (sq (c_scale' C3 (sq (log_t T HT1)))).
Proof.
  intros T c C2 r M HT1 Hlogpos Hc HC2 HR Hu2 HMpos Hfloor HM g s0
         Hloc Hp Hcirc Hnn Hmod_gate Hchain C3 Hbind Hallign.
  apply (RealSetoid.real_le_compat
           (c_norm_sq (gaC12_deriv1 g s0 s0 r Hloc (cauchy_Hz0 s0 r HR)))
           (c_norm_sq (gaC12_deriv1 g s0 s0 r Hloc Hp))
           (sq (c_scale' C3 (sq (log_t T HT1))))
           (sq (c_scale' C3 (sq (log_t T HT1))))).
  - exact (real_eq_sym _ _ (mm_norm_wd _ _ Hallign)).
  - apply real_eq_refl.
  - exact (gaC18_deriv_bound_closure T c C2 r M HT1 Hlogpos Hc HC2 HR Hu2
             HMpos Hfloor HM g s0 Hloc Hcirc Hnn Hmod_gate Hchain C3 Hbind).
Defined.
