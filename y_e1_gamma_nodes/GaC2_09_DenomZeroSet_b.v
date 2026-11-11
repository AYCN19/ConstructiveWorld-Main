(** * GaC2_09_DenomZeroSet_b - pi carrier, lattice exponential, and
      the pi-window pin of the denominator zero set.
    Mission.  Node C2-09 (segment C2, slot W1), machine piece.  The
      pi carrier [d09_pi_times]/[d09_two_pi] with its integer-multiple
      faces; the lattice exponential face [d09_exp_i_two_pi_Z] (c_exp
      of (0, two pi k) is c_one, by a nat induction through
      [c_exp_plus] and [c_exp_conj]); the pi shift [d09_sin_pi_shift];
      the pi-window pin [d09_window_pin] (cos d == 1 and sin d == 0
      with |d| < pi + 1/4 force d == 0); the logarithm constant
      [d09_ln2]; the power carrier [two_pow_1ms] and denominator
      [d09_denom] with their zero-set faces; the pi bound faces; the
      inverse constant [d09_inv_two_pi] with its round trip; the
      rational floor bounds (full roster in Notes).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [ZArith], [QArith.Qround], [Setoid], [Morphisms], [Arith.Arith],
      [Lia]; [S01_BaseRing] (selective [NatLe]/[And] import),
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [S10_KVQuantTrig], [CxRealPairCore], [CxRealPairExpLog],
      [GaC1_Iface_Cx], [GaC1_Iface_Real], [GaC2_09_DenomZeroSet_a]
      (named faces in Notes).
    References.  drafts_C2.md C2.09 statement sketch (the L11 obligation:
      the pi carrier pinned to the C1-17 output face [pi_R]; the lattice
      face realizes the e^(iy) = 1 constructive characterization on the
      two-pi grid); Bishop-Bridges Ch. 2; [GaC1_17_TwoPiPeriod] laws.
    Constructivity.  Every named construction is carried by [Set]; the
      Z-indexed exponential face and the weak-trichotomy window pin
      (explicit pi + 1/4 margin) discharge constructively; zero
      assumed constants; every proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_b.v]; flat build dir, thermal guard wrapper. *)
Require S01_BaseRing.
(** Notes.  Full face roster behind the Mission field: the
    integer-multiple faces [d09_two_pi_zero], [d09_two_pi_add],
    [d09_two_pi_opp], [d09_two_pi_one_two_pi_R]; the pi shift
    [d09_sin_pi_shift] (sin(pi + x) == - sin x through [rs_add_sin]);
    the zero-set faces [d09_c_plus_one_opp_eq_zero] and
    [d09_carrier_norm]; the pi bound faces [d09_pi_R_eq_geom],
    [d09_two_pi_pos], [d09_pi_R_lt_ten_thirds]; the lattice
    exponential family runs [d09_exp_i_two_pi_zero],
    [d09_exp_i_two_pi_one], [d09_exp_i_two_pi_nat],
    [d09_exp_i_two_pi_Z].  Named consumed faces behind the
    Dependencies field: [QArith.Qround] supplies [Qfloor_le] and
    [Qlt_floor]; [S10_KVQuantTrig] supplies [rs_add_sin],
    [real_sin_opp], [real_sin_pos_lt_two], [real_pi_geom_gt_three],
    [real_pi_geom_lt_ten_thirds]; [CxRealPairExpLog] supplies
    [c_exp_plus] and [c_exp_conj]; [GaC1_Iface_Cx] supplies [pi_R],
    [two_pi_R], [gaC1_17_sin_pi], [gaC1_17_cos_pi],
    [gaC1_17_cos_two_pi], [gaC1_17_sin_two_pi].  References
    overflow: Bishop-Bridges, Constructive Analysis Ch. 2 (integer
    part of a real through the Cauchy modulus). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.Qround.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
(* ===================================================================== *)
(* Section 1. Pointwise and equality-level algebra faces.                *)
(* ===================================================================== *)
Lemma d09_opp_opp : forall x : Real,
  real_eq (real_opp (real_opp x)) x.
Proof. intro x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_opp real_zero]. ring. Qed.
Lemma d09_const_opp : forall c : Q,
  real_eq (real_const (- c)) (real_opp (real_const c)).
Proof. intros c. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_const real_opp real_zero]. ring. Qed.
Lemma d09_const_plus : forall c d : Q,
  real_eq (real_const (c + d)) (real_plus (real_const c) (real_const d)).
Proof. intros c d. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_const real_plus real_zero]. ring. Qed.
Lemma d09_const_mult : forall c d : Q,
  real_eq (real_const (c * d)) (real_mult (real_const c) (real_const d)).
Proof. intros c d. apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_const real_mult real_zero]. ring. Qed.
(* ===================================================================== *)
(* Section 2. The logarithm constant.                                    *)
(* ===================================================================== *)
Lemma d09_mult_distr_r : forall a b c : Real,
  real_eq (real_mult a (real_plus b c))
          (real_plus (real_mult a b) (real_mult a c)).
Proof. intros a b c.
  destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_plus]. ring. Qed.
Lemma d09_mult_assoc : forall a b c : Real,
  real_eq (real_mult (real_mult a b) c) (real_mult a (real_mult b c)).
Proof. intros a b c.
  destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult]. ring. Qed.
Lemma d09_sub_split : forall a m c : Real,
  real_eq (real_plus a (real_opp c))
          (real_plus (real_plus a (real_opp m)) (real_plus m (real_opp c))).
Proof. intros a m c.
  destruct a as [a1 a2]. destruct m as [m1 m2]. destruct c as [c1 c2].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_opp]. ring. Qed.
Lemma d09_two_pos : real_lt real_zero (real_const 2).
Proof. exact (real_const_pos 2 qltT_0_2). Qed.
Definition d09_pi_times (k : Z) : Real := real_mult (real_const (k # 1)) pi_R.
Definition d09_two_pi (k : Z) : Real := real_mult (real_const 2) (d09_pi_times k).
Lemma d09_qmake_opp : forall k : Z, ((- k) # 1)%Q == (- (k # 1))%Q.
Proof. intro k. unfold Qeq. simpl. ring. Qed.
Lemma d09_two_pi_zero : real_eq (d09_two_pi 0) real_zero.
Proof. unfold d09_two_pi, d09_pi_times.
  unfold pi_R, cos_pi_half.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const real_plus real_zero fst snd].
  ring. Qed.
Lemma d09_two_pi_add : forall j k : Z,
  real_eq (d09_two_pi (j + k)) (real_plus (d09_two_pi j) (d09_two_pi k)).
Proof. intros j k.
  unfold d09_two_pi, d09_pi_times.
  unfold pi_R, cos_pi_half.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const real_plus fst snd].
  assert (Hq : ((j + k) # 1)%Q == ((j # 1) + (k # 1))%Q).
  { unfold Qeq. simpl. ring. }
  rewrite Hq.
  ring. Qed.
Lemma d09_two_pi_opp : forall k : Z,
  real_eq (d09_two_pi (- k)) (real_opp (d09_two_pi k)).
Proof. intros k.
  unfold d09_two_pi, d09_pi_times.
  destruct pi_R as [pp Hp].
  destruct cos_pi_half as [cc Hc].
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const real_opp fst snd].
  rewrite (d09_qmake_opp k).
  ring. Qed.
Lemma d09_two_pi_one_two_pi_R : real_eq (d09_two_pi 1) two_pi_R.
Proof. unfold d09_two_pi, d09_pi_times.
  unfold two_pi_R, pi_R, cos_pi_half.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_mult real_const real_plus fst snd].
  ring. Qed.
Definition d09_ln2 : Real := cw_log (real_const 2) d09_two_pos.

(* ===================================================================== *)
(* Section 4. The power carrier and its zero-set faces.                  *)
(* ===================================================================== *)
Definition two_pow_1ms (s : Cx) : Cx :=
  c_exp (c_scale d09_ln2 (c_plus c_one (c_opp s))).
Definition d09_denom (s : Cx) : Cx :=
  c_plus c_one (c_opp (two_pow_1ms s)).
Lemma d09_c_plus_one_opp_eq_zero : forall w : Cx,
  c_eq (c_plus c_one (c_opp w)) c_zero -> c_eq w c_one.
Proof. intros w H.
  apply (c_eq_trans w (c_plus c_zero w) c_one).
  - apply (c_eq_sym (c_plus c_zero w) w). apply c_plus_zero.
  - apply (c_eq_trans (c_plus c_zero w)
             (c_plus (c_plus c_one (c_opp w)) w)).
    + apply c_plus_congr.
      * apply (c_eq_sym (c_plus c_one (c_opp w)) c_zero). exact H.
      * apply c_eq_refl.
    + apply (c_eq_trans (c_plus (c_plus c_one (c_opp w)) w)
               (c_plus c_one (c_plus (c_opp w) w))).
      * apply (c_eq_sym (c_plus c_one (c_plus (c_opp w) w))
                 (c_plus (c_plus c_one (c_opp w)) w)). apply c_plus_assoc.
      * apply (c_eq_trans (c_plus c_one (c_plus (c_opp w) w))
                 (c_plus c_one c_zero)).
        { apply c_plus_congr.
          - apply c_eq_refl.
          - apply (c_eq_trans (c_plus (c_opp w) w) (c_plus w (c_opp w))).
            { apply c_plus_comm. }
            { apply c_plus_opp. } }
        { apply (c_eq_trans (c_plus c_one c_zero) (c_plus c_zero c_one)).
          - apply c_plus_comm.
          - apply c_plus_zero. } Qed.
Lemma d09_cRe_one_minus : forall s : Cx,
  real_eq (cRe (c_plus c_one (c_opp s)))
          (real_plus real_one (real_opp (cRe s))).
Proof. intros s. apply real_eq_of_zero_diff. intro n.
  destruct s as [s1 s2]. destruct s1 as [u Hu]. destruct s2 as [v Hv].
  cbn [projT1 cRe c_one c_plus c_opp real_plus real_opp real_one fst snd].
  ring. Qed.
Lemma d09_cIm_opp_shift : forall s : Cx,
  real_eq (cIm (c_plus c_one (c_opp s))) (real_opp (cIm s)).
Proof. intros s. apply real_eq_of_zero_diff. intro n.
  destruct s as [s1 s2]. destruct s1 as [u Hu]. destruct s2 as [v Hv].
  cbn [projT1 cIm c_one c_plus c_opp real_plus real_opp real_zero fst snd].
  ring. Qed.
Definition d09_carrier_arg (s : Cx) : Cx :=
  c_scale d09_ln2 (c_plus c_one (c_opp s)).
Lemma d09_carrier_norm : forall s : Cx,
  real_eq (c_norm_sq (two_pow_1ms s))
          (cauchy_real_exp (real_plus (cRe (d09_carrier_arg s))
                                       (cRe (d09_carrier_arg s)))).
Proof. intro s.
  exact (gaC1_16_norm_sq_exp (d09_carrier_arg s)). Qed.



Lemma d09_pi_R_eq_geom : real_eq pi_R real_pi_geom.
Proof.
  unfold pi_R, real_pi_geom, cos_pi_half.
  apply real_eq_of_zero_diff. intro n.
  cbn [projT1 real_plus real_mult real_const fst snd].
  ring.
Qed.

Lemma d09_two_pi_pos : real_lt real_zero (d09_two_pi 1).
Proof.
  apply (real_lt_trans (real_const 0) (real_const 3) (d09_two_pi 1)).
  - apply real_const_lt. unfold Qlt. simpl. lia.
  - apply (RealSetoid.real_lt_compat (real_const 3) (real_const 3)
             (real_plus pi_R pi_R) (d09_two_pi 1)
             (real_eq_refl (real_const 3))
             (real_eq_sym _ _ (d09_two_pi_one_two_pi_R))).
    apply (real_lt_trans (real_const 3) pi_R (real_plus pi_R pi_R)).
    { apply (real_lt_eq_lt (real_const 3) real_pi_geom pi_R).
      { exact real_pi_geom_gt_three. }
      { exact (real_eq_sym _ _ d09_pi_R_eq_geom). } }
    { apply (real_lt_trans pi_R (real_plus pi_R (real_const 1))
               (real_plus pi_R pi_R)).
      { apply real_lt_plus_eps_r.
        exact (real_const_pos 1 qltT_0_1). }
      { apply real_lt_plus_translate.
        apply (real_lt_eq_lt (real_const 1) real_pi_geom pi_R).
        - apply (real_lt_trans (real_const 1) (real_const 3) real_pi_geom).
          { apply real_const_lt. unfold Qlt. simpl. lia. }
          { exact real_pi_geom_gt_three. }
        - exact (real_eq_sym _ _ d09_pi_R_eq_geom). } }
Qed.

Lemma d09_pi_R_lt_ten_thirds : real_lt pi_R (real_const (10 / 3)).
Proof.
  apply (RealSetoid.real_lt_compat real_pi_geom pi_R
             (real_const (10 / 3)) (real_const (10 / 3))
             (real_eq_sym _ _ d09_pi_R_eq_geom) (real_eq_refl (real_const (10 / 3)))).
  exact real_pi_geom_lt_ten_thirds.
Qed.


Definition d09_inv_two_pi : Real :=
  cauchy_real_exp (real_opp (cw_log (d09_two_pi 1) d09_two_pi_pos)).

Lemma d09_inv2pi_aux1 : real_eq (real_mult d09_inv_two_pi (d09_two_pi 1))
    (real_mult (cauchy_real_exp (real_opp (cw_log (d09_two_pi 1) d09_two_pi_pos)))
               (cauchy_real_exp (cw_log (d09_two_pi 1) d09_two_pi_pos))).
Proof.
  apply RealSetoid.real_eq_mult_compat.
  - apply real_eq_refl.
  - exact (real_eq_sym _ _ (cw_log_exp_right (d09_two_pi 1) d09_two_pi_pos)).
Qed.

Lemma d09_inv2pi_aux2 : real_eq
    (real_mult (cauchy_real_exp (real_opp (cw_log (d09_two_pi 1) d09_two_pi_pos)))
               (cauchy_real_exp (cw_log (d09_two_pi 1) d09_two_pi_pos)))
    real_one.
Proof.
  apply (real_eq_trans
           (real_mult
              (cauchy_real_exp (real_opp (cw_log (d09_two_pi 1) d09_two_pi_pos)))
              (cauchy_real_exp (cw_log (d09_two_pi 1) d09_two_pi_pos)))
           (cauchy_real_exp (real_plus (real_opp (cw_log (d09_two_pi 1)
                            d09_two_pi_pos))
                       (cw_log (d09_two_pi 1) d09_two_pi_pos)))
           real_one).
  - exact (real_eq_sym _ _
             (cauchy_real_exp_plus (real_opp (cw_log (d09_two_pi 1)
                                 d09_two_pi_pos))
               (cw_log (d09_two_pi 1) d09_two_pi_pos))).
  - apply (real_eq_trans
             (cauchy_real_exp
                (real_plus (real_opp (cw_log (d09_two_pi 1) d09_two_pi_pos))
                           (cw_log (d09_two_pi 1) d09_two_pi_pos)))
             (cauchy_real_exp real_zero) real_one).
    { apply cauchy_real_exp_wd.
      apply real_eq_of_zero_diff. intro n.
      rewrite (real_plus_proj
                 (real_opp (cw_log (d09_two_pi 1) d09_two_pi_pos))
                 (cw_log (d09_two_pi 1) d09_two_pi_pos) n).
      rewrite (real_opp_proj (cw_log (d09_two_pi 1) d09_two_pi_pos) n).
      rewrite (real_zero_pt n).
      ring. }
    { exact cauchy_real_exp_zero. }
Qed.

Lemma d09_inv_two_pi_mult :
  real_eq (real_mult d09_inv_two_pi (d09_two_pi 1)) real_one.
Proof.
  exact (real_eq_trans _ _ _ d09_inv2pi_aux1 d09_inv2pi_aux2).
Qed.



Lemma d09_floor_bounds : forall q : Q,
  sigT (fun k : Z => And (Qle ((k # 1)) q) (Qlt q ((k + 1) # 1))).
Proof.
  intro q.
  exists (Qfloor q).
  split.
  - exact (Qround.Qfloor_le q).
  - exact (Qround.Qlt_floor q).
Qed.

(* ===================================================================== *)
(* Section 5. The two-pi lattice exponential of the eta denominator.     *)
(* ===================================================================== *)
Definition d09_i_two_pi (k : Z) : Cx := (real_zero, d09_two_pi k).

Lemma d09_c_exp_congr : forall z w : Cx, c_eq z w -> c_eq (c_exp z) (c_exp w).
Proof. intros z w Hz. destruct Hz as [Hr Hi]. unfold c_exp, c_eq. split.
  - apply RealSetoid.real_eq_mult_compat;
      [exact (cauchy_real_exp_wd _ _ Hr) | exact (real_cos_eq_compat _ _ Hi)].
  - apply RealSetoid.real_eq_mult_compat;
      [exact (cauchy_real_exp_wd _ _ Hr) | exact (real_sin_eq_compat _ _ Hi)]. Qed.

Lemma d09_exp_i_two_pi_zero : c_eq (c_exp (d09_i_two_pi 0)) c_one.
Proof. apply (c_eq_trans _ (c_exp c_zero) c_one).
  - apply d09_c_exp_congr. unfold d09_i_two_pi, c_eq. cbn [fst snd].
    split; [apply real_eq_refl | exact d09_two_pi_zero].
  - exact c_exp_zero. Qed.

Lemma d09_exp_i_two_pi_one : c_eq (c_exp (d09_i_two_pi 1)) c_one.
Proof.
  apply (c_eq_trans _ (c_exp (real_zero, two_pi_R)) c_one).
  - apply d09_c_exp_congr. unfold d09_i_two_pi, c_eq. cbn [fst snd].
    split; [apply real_eq_refl | exact d09_two_pi_one_two_pi_R].
  - unfold c_exp, c_eq, c_one. cbn [fst snd]. split.
    + apply (real_eq_trans _ (real_mult real_one real_one)).
      * apply RealSetoid.real_eq_mult_compat;
          [exact cauchy_real_exp_zero | exact gaC1_17_cos_two_pi].
      * apply real_mult_one.
    + apply (real_eq_trans _ (real_mult real_one real_zero)).
      * apply RealSetoid.real_eq_mult_compat;
          [exact cauchy_real_exp_zero | exact gaC1_17_sin_two_pi].
      * apply real_mult_zero.
Qed.

Lemma d09_exp_i_two_pi_nat : forall n : nat,
  c_eq (c_exp (d09_i_two_pi (Z.of_nat n))) c_one.
Proof.
  intro n. induction n as [| n IH].
  - change (Z.of_nat 0) with 0%Z. exact d09_exp_i_two_pi_zero.
  - assert (Hz : c_eq (d09_i_two_pi (Z.of_nat (Datatypes.S n)))
                   (c_plus (d09_i_two_pi (Z.of_nat n)) (d09_i_two_pi 1))).
    { replace (Z.of_nat (Datatypes.S n)) with (Z.of_nat n + 1)%Z by (symmetry; exact (Nat2Z.inj_succ n)).
      unfold d09_i_two_pi, c_plus, c_eq. cbn [cRe cIm c_plus fst snd].
      split; [exact (real_plus_zero real_zero) |
              exact (d09_two_pi_add (Z.of_nat n) 1)]. }
    apply (c_eq_trans _
             (c_exp (c_plus (d09_i_two_pi (Z.of_nat n)) (d09_i_two_pi 1)))
             c_one).
    + apply d09_c_exp_congr. exact Hz.
    + apply (c_eq_trans _ (c_mult (c_exp (d09_i_two_pi (Z.of_nat n))) (c_exp (d09_i_two_pi 1))) c_one).
      * apply c_exp_plus.
      * apply (c_eq_trans _ (c_mult c_one c_one)).
        -- apply c_mult_congr; [exact IH | exact d09_exp_i_two_pi_one].
        -- exact (c_mult_one c_one).
Qed.

Lemma d09_exp_i_two_pi_Z : forall k : Z, c_eq (c_exp (d09_i_two_pi k)) c_one.
Proof.
  intro k. destruct k as [| p | p].
  - exact d09_exp_i_two_pi_zero.
  - rewrite <- (Znat.positive_nat_Z p).
    exact (d09_exp_i_two_pi_nat (Pos.to_nat p)).
  - assert (Hcj : c_eq (d09_i_two_pi (Zneg p)) (c_conj (d09_i_two_pi (Z.pos p)))).
    { unfold d09_i_two_pi, c_conj, c_eq. cbn [cRe cIm c_conj fst snd].
      split; [apply real_eq_refl | exact (d09_two_pi_opp (Z.pos p))]. }
    assert (Hxa : c_eq (c_exp (d09_i_two_pi (Zneg p))) (c_conj (c_exp (d09_i_two_pi (Z.pos p))))).
    { apply (c_eq_trans _ (c_exp (c_conj (d09_i_two_pi (Z.pos p))))).
      - apply d09_c_exp_congr. exact Hcj.
      - exact (c_exp_conj (d09_i_two_pi (Z.pos p))). }
    assert (Hpos : c_eq (c_exp (d09_i_two_pi (Z.pos p))) c_one).
    { rewrite <- (Znat.positive_nat_Z p);
      exact (d09_exp_i_two_pi_nat (Pos.to_nat p)). }
    assert (Hcg : forall z w : Cx, c_eq z w -> c_eq (c_conj z) (c_conj w)).
    { intros z w Hz. unfold c_conj, c_eq. destruct Hz as [Hr Hi].
      split; [exact Hr | exact (RealSetoid.real_eq_opp_compat _ _ Hi)]. }
    apply (c_eq_trans _ (c_conj (c_exp (d09_i_two_pi (Z.pos p))))).
    + exact Hxa.
    + apply (c_eq_trans _ (c_conj c_one)).
      * exact (Hcg _ _ Hpos).
      * unfold c_conj, c_one, c_eq. cbn [cRe cIm c_conj fst snd]. split.
        -- apply real_eq_refl.
        -- apply real_eq_of_zero_diff. intro n.
           cbn [projT1 real_opp real_zero]. ring.
Qed.
