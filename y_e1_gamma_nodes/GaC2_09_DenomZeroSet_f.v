(* ConstructiveWorld-Main - the pi-window transport kit of the denominator zero set *)
(** * GaC2_09_DenomZeroSet_f - - the pi-window transport and the rounding core of the
      denominator zero set
    Mission.  Node C2-09 (segment C2, slot W1), witness-support piece of the
      denominator zero set family.  Casts the pi-window transport [e09_shift_window] (the
      nearest 2-pi grid point to a windowed ratio lands inside the
      pi + 1/4 window), the exponential lattice-shift kit
      ([e09_exp_opp_two_pi], [e09_exp_shift], [e09_proj_cos_sin]),
      and the rounding core [e09_grid_pin] (exp(i d) = 1 forces
      d = 2 pi k for an explicit integer k, through the window pin of
      the shifted point).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [ZArith], [Setoid], [Morphisms],
      [Arith.Arith], [Lia]; [S01_BaseRing] (selective [NatLe]/[And]
      import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC1_Iface_Real],
      [GaC2_09_DenomZeroSet_a] through [e] (named faces in Notes).
    References.  drafts_C2.md C2-09 card (:718-739) with the registered
      L11/L12 concretizations; the v16 receipt section VII casting spec.
    Constructivity.  Every named construction is carried by [Set]; zero
      Sections, zero assumed constants, zero admitted goals; every
      proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_f.v]; flat build
      directory, acceptance via 50_toolkit/accept_node.py. *)
Require S01_BaseRing.
(** Notes.  Named consumed faces behind the Dependencies field:
    [e]: [e09_rat_approx], [e09_round_abs]; [c]:
    [d09_q_abs_le_of_both], [d09_window_pin]; [d]:
    [d09_grid_cancel_l]; [b]: [d09_two_pi], [d09_two_pi_opp],
    [d09_pi_R_eq_geom], [d09_pi_R_lt_ten_thirds],
    [d09_exp_i_two_pi_Z], [d09_c_exp_congr], [d09_floor_bounds];
    [CxRealPairExpLog]: [c_exp_plus], [c_exp_conj],
    [cauchy_real_exp_zero]; [S07_RealSetoidExpLog]:
    [RealSetoid.real_lt_compat], [real_eq_of_zero_diff],
    [real_abs_proj], [Qabs_opp], [real_mult_one], [real_mult_comm],
    [real_lt_not_eq]; [S10_KVQuantTrig]:
    [real_pi_geom_gt_three]; [GaC1_Iface_Cx] supplies [pi_R], [c_exp],
    and the pair carrier faces. *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Local Open Scope Q_scope.

Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop, And).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S10_KVQuantTrig.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
Require Import GaC2_09_DenomZeroSet_a.
Require Import GaC2_09_DenomZeroSet_b.
Require Import GaC2_09_DenomZeroSet_c.
Require Import GaC2_09_DenomZeroSet_d.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Arith.Arith Lia.
Require Import GaC2_09_DenomZeroSet_e.

(* ===================================================================== *)
(* Section 2. The pi-window transport: the nearest grid point lies in    *)
(* the window |d'| < pi + 1/4.                                           *)
(* ===================================================================== *)

Lemma e09_shift_window : forall (d x : Real) (k : Z),
  real_eq (real_mult (d09_two_pi 1) x) d ->
  sigT (fun N0 : nat => forall n : nat, (N0 <= n)%nat ->
        Qle (Qabs (projT1 x n - (k # 1)%Q)) (33 / 64)%Q) ->
  real_lt (real_abs (real_plus d (real_opp (d09_two_pi k))))
          (real_plus pi_R (real_const (1 / 4))).
Proof.
  intros d x k Hxd [N0 Hxk].
  assert (Hq128 : Qlt 0 (1 / 128)) by (unfold Qlt; simpl; lia).
  destruct (Hxd (1 / 128) (Qlt_to_QltT 0 (1 / 128) Hq128)) as [Nmu HNmu].
  assert (Hpilt : real_lt (real_const 3) pi_R).
  { apply (RealSetoid.real_lt_compat (real_const 3) (real_const 3)
             real_pi_geom pi_R (real_eq_refl (real_const 3))
             (real_eq_sym _ _ d09_pi_R_eq_geom)).
    exact real_pi_geom_gt_three. }
  destruct Hpilt as [ep [Hep [Np HNp]]].
  destruct d09_pi_R_lt_ten_thirds as [eu [Heu [Nu HNu]]].
  exists (1 / 64). split.
  - apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exists (Nat.max N0 (Nat.max Nmu (Nat.max Np Nu))). intros n Hn.
    apply NatLe_drop in Hn.
    assert (Hn0 : (N0 <= n)%nat) by lia.
    assert (Hnmu : (Nmu <= n)%nat) by lia.
    assert (Hnp : (Np <= n)%nat) by lia.
    assert (Hnu : (Nu <= n)%nat) by lia.
    assert (Hpi : QltT ep (projT1 pi_R n - 3))
      by exact (HNp n (NatLe_lift Np n Hnp)).
    cbv beta iota zeta delta [real_const projT1 fst snd] in Hpi.
    assert (HepQ : Qlt 0 ep) by (apply QltT_to_Qlt; exact Hep).
    assert (HpiQ : Qlt ep (projT1 pi_R n - 3))
      by (apply QltT_to_Qlt; exact Hpi).
    assert (Hp3 : Qlt 3 (projT1 pi_R n)).
    { apply (proj2 (Qlt_minus_iff 3 (projT1 pi_R n))).
      apply (Qlt_trans 0 ep (projT1 pi_R n + - 3)).
      - exact HepQ.
      - exact HpiQ. }
    assert (Hpu : QltT eu (projT1 (real_const (10 / 3)) n - projT1 pi_R n))
      by exact (HNu n (NatLe_lift Nu n Hnu)).
    cbv beta iota zeta delta [real_const projT1 fst snd] in Hpu.
    assert (Hp4 : Qle (projT1 pi_R n) 4).
    { pose proof Hpu as Hq0.
      apply QltT_to_Qlt in Hq0.
      apply (Qlt_le_weak (projT1 pi_R n) 4).
      apply (Qlt_trans (projT1 pi_R n) (10 / 3 - eu) 4).
      - apply (proj2 (Qlt_minus_iff (projT1 pi_R n) (10 / 3 - eu))).
        assert (Hrw : ((10 / 3 - eu) - projT1 pi_R n)%Q
                      == ((10 / 3 - projT1 pi_R n) - eu)%Q) by field.
        rewrite Hrw.
        apply (proj1 (Qlt_minus_iff eu (10 / 3 - projT1 pi_R n))).
        exact Hq0.
      - apply (Qlt_le_trans (10 / 3 - eu) (10 / 3) 4).
        + apply (proj2 (Qlt_minus_iff (10 / 3 - eu) (10 / 3))).
          assert (Hrw : (10 / 3 - (10 / 3 - eu))%Q == eu) by field.
          rewrite Hrw.
          exact (QltT_to_Qlt 0 eu Heu).
        + change (Qle (10 # 3)%Q 4). unfold Qle. simpl. lia. }
    assert (Habsweq : Qabs (projT1 (real_mult (d09_two_pi 1) x) n - projT1 d n)
                      == Qabs (projT1 d n - 2 * projT1 pi_R n * projT1 x n)).
    { apply (Qeq_trans (Qabs (projT1 (real_mult (d09_two_pi 1) x) n - projT1 d n))
               (Qabs (Qopp (projT1 d n - 2 * projT1 pi_R n * projT1 x n)))).
      - apply (Qabs_wd (projT1 (real_mult (d09_two_pi 1) x) n - projT1 d n)
                 (Qopp (projT1 d n - 2 * projT1 pi_R n * projT1 x n))).
        rewrite (real_mult_proj (d09_two_pi 1) x n).
        assert (Hp1 : projT1 (d09_two_pi 1) n == 2 * projT1 pi_R n).
        { unfold d09_two_pi, d09_pi_times.
          rewrite (real_mult_proj (real_const 2) (real_mult (real_const 1) pi_R) n).
          rewrite (real_mult_proj (real_const 1) pi_R n).
          cbn [projT1 real_const]. ring. }
        rewrite Hp1. ring.
      - apply (Qabs_opp (projT1 d n - 2 * projT1 pi_R n * projT1 x n)). }
    assert (Hmu : Qlt (Qabs (projT1 d n - 2 * projT1 pi_R n * projT1 x n))
                      (1 / 128)).
    { exact (QltT_to_Qlt
               (Qabs (projT1 d n - 2 * projT1 pi_R n * projT1 x n)) (1 / 128)
               (qltT_eq_compat_l
                  (Qabs (projT1 (real_mult (d09_two_pi 1) x) n - projT1 d n))
                  (Qabs (projT1 d n - 2 * projT1 pi_R n * projT1 x n))
                  (1 / 128) Habsweq
                  (HNmu n (NatLe_lift Nmu n Hnmu)))). }
    assert (Heq : (projT1 pi_R n + projT1 (real_const (1 / 4)) n
                   - Qabs (projT1 d n
                           - 2 * ((k # 1)%Q * projT1 pi_R n)))%Q
                  == (projT1 (real_plus pi_R (real_const (1 / 4))) n
                      - projT1 (real_abs
                                  (real_plus d (real_opp (d09_two_pi k)))) n)%Q).
    { rewrite (real_plus_proj pi_R (real_const (1 / 4)) n).
      rewrite (real_abs_proj (real_plus d (real_opp (d09_two_pi k))) n).
      rewrite (real_plus_proj d (real_opp (d09_two_pi k)) n).
      rewrite (real_opp_proj (d09_two_pi k) n).
      assert (Hpk : projT1 (d09_two_pi k) n == 2 * ((k # 1)%Q * projT1 pi_R n)).
      { unfold d09_two_pi, d09_pi_times.
        rewrite (real_mult_proj (real_const 2) (real_mult (real_const (k # 1)%Q) pi_R) n).
        rewrite (real_mult_proj (real_const (k # 1)%Q) pi_R n).
        cbn [projT1 real_const]. reflexivity. }
      rewrite Hpk.
      cbn [projT1 real_const]. reflexivity. }
    apply (qltT_eq_compat_r _ _ _ (Qeq_sym _ _ Heq)).
    set (p := projT1 pi_R n) in *.
    set (u := projT1 x n) in *.
    set (w := projT1 d n) in *.
    set (K := (k # 1)%Q) in *.
    assert (Hp2 : Qlt 0 (2 * p)).
    { apply (Qmult_lt_0_compat 2 p).
      - unfold Qlt. simpl. lia.
      - assert (H03 : Qlt 0 3) by (change (Qlt 0 3); compute; reflexivity).
        exact (Qlt_le_trans 0 3 p H03 (Qlt_le_weak 3 p Hp3)). }
    assert (Htri : Qle (Qabs (w - 2 * (K * p)))
                       (Qabs (w - 2 * p * u) + Qabs ((u - K) * (2 * p)))).
    { assert (Hr1 : ((w - 2 * p * u) + ((u - K) * (2 * p)))%Q
                    == (w - 2 * (K * p))%Q) by ring.
      rewrite <- (Qabs_wd _ _ Hr1).
      apply Qabs_triangle. }
    assert (Hxb : Qle (Qabs (u - K)) (33 / 64)) by (exact (Hxk n Hn0)).
    assert (Habs2 : Qle (Qabs ((u - K) * (2 * p))) ((33 / 64) * (2 * p))).
    { apply (Qle_trans (Qabs ((u - K) * (2 * p)))
               (Qabs (u - K) * Qabs (2 * p))).
      - apply qeq_le. apply Qabs_Qmult.
      - rewrite (Qabs_pos (2 * p) (Qlt_le_weak 0 (2 * p) Hp2)).
        exact (Qmult_le_compat_r (Qabs (u - K)) (33 / 64) (2 * p)
                 Hxb (Qlt_le_weak 0 (2 * p) Hp2)). }
    assert (Hle : Qle (Qabs (w - 2 * (K * p)))
                      (1 / 128 + (33 / 64) * (2 * p))).
    { apply (Qle_trans _ (Qabs (w - 2 * p * u) + Qabs ((u - K) * (2 * p)))).
      - exact Htri.
      - apply Qplus_le_compat.
        + exact (Qlt_le_weak _ _ Hmu).
        + exact Habs2. }
    assert (Hshift : Qle (p + 1 / 4 - (1 / 128 + (33 / 64) * (2 * p)))
                         (p + 1 / 4 - Qabs (w - 2 * (K * p)))).
    { apply (Qplus_le_compat (p + 1 / 4) (p + 1 / 4)
               (Qopp (1 / 128 + (33 / 64) * (2 * p)))
               (Qopp (Qabs (w - 2 * (K * p))))).
      - apply Qle_refl.
      - apply (Qopp_le_compat _ _ Hle). }
    assert (Hnum : Qlt (1 / 64) (p + 1 / 4 - (1 / 128 + (33 / 64) * (2 * p)))).
    { apply (Qlt_le_trans (1 / 64) (15 # 128)%Q
               (p + 1 / 4 - (1 / 128 + (33 / 64) * (2 * p)))).
      - change (Qlt (1 # 64)%Q (15 # 128)%Q). unfold Qlt. simpl. lia.
      - assert (Hrep : (p + 1 / 4 - (1 / 128 + (33 / 64) * (2 * p)))%Q
                       == ((31 # 128)%Q - p * ((1 # 32)%Q))).
        { change (p + (1 # 4)%Q - ((1 # 128)%Q + ((33 # 64)%Q * (2 * p)))
                  == (31 # 128)%Q - p * (1 # 32)%Q). ring. }
        rewrite Hrep.
        apply (proj2 (Qle_minus_iff (15 # 128)%Q ((31 # 128)%Q - p * (1 # 32)%Q))).
        assert (Hrw : (((31 # 128)%Q - p * ((1 # 32)%Q)) - (15 # 128)%Q)%Q
                      == ((4 - p) * ((1 # 32)%Q))) by field.
        rewrite Hrw.
        apply (Qmult_le_0_compat (4 - p) (1 # 32)%Q).
        + exact (proj1 (Qle_minus_iff p 4) Hp4).
        + unfold Qle. simpl. lia. }
    apply Qlt_to_QltT.
    apply (Qlt_le_trans (1 / 64)
             (p + 1 / 4 - (1 / 128 + (33 / 64) * (2 * p)))
             (p + 1 / 4 - Qabs (w - 2 * (K * p)))).
    + exact Hnum.
    + exact Hshift.
Qed.


(* ===================================================================== *)
(* Section 3. The exponential lattice shift and the projection faces.    *)
(* ===================================================================== *)

Lemma e09_exp_opp_two_pi : forall k : Z,
  c_eq (c_exp (real_zero, real_opp (d09_two_pi k))) c_one.
Proof.
  intro k.
  apply (c_eq_trans _ (c_exp (d09_i_two_pi (- k)))).
  - apply d09_c_exp_congr.
    unfold c_eq. split.
    + apply real_eq_refl.
    + exact (real_eq_sym _ _ (d09_two_pi_opp k)).
  - exact (d09_exp_i_two_pi_Z (- k)).
Qed.

Lemma e09_exp_shift : forall (d d' : Real) (k : Z),
  c_eq (c_exp (real_zero, d)) c_one ->
  c_eq (real_zero, d')
       (c_plus (real_zero, d) (real_zero, real_opp (d09_two_pi k))) ->
  c_eq (c_exp (real_zero, d')) c_one.
Proof.
  intros d d' k H0 Hsum.
  apply (c_eq_trans _
           (c_exp (c_plus (real_zero, d) (real_zero, real_opp (d09_two_pi k))))).
  - apply d09_c_exp_congr. exact Hsum.
  - apply (c_eq_trans _
             (c_mult (c_exp (real_zero, d))
                (c_exp (real_zero, real_opp (d09_two_pi k))))).
    + apply c_exp_plus.
    + apply (c_eq_trans _ (c_mult c_one c_one)).
      * apply c_mult_congr; [exact H0 | exact (e09_exp_opp_two_pi k)].
      * apply (c_eq_trans _ c_one).
        -- apply c_mult_one.
        -- apply c_eq_refl.
Qed.

Lemma e09_proj_cos_sin : forall d : Real,
  c_eq (c_exp (real_zero, d)) c_one ->
  And (real_eq (cauchy_real_cos d) real_one)
      (real_eq (cauchy_real_sin d) real_zero).
Proof.
  intros d H.
  unfold c_exp in H. unfold c_eq in H. cbn [cRe cIm fst snd] in H.
  destruct H as [Hr Hi].
  assert (Hr1 : real_eq (real_mult real_one (cauchy_real_cos d)) real_one).
  { apply (real_eq_trans (real_mult real_one (cauchy_real_cos d))
             (real_mult (cauchy_real_exp real_zero) (cauchy_real_cos d))).
    - apply RealSetoid.real_eq_mult_compat;
        [exact (real_eq_sym _ _ cauchy_real_exp_zero) | apply real_eq_refl].
    - exact Hr. }
  assert (Hs1 : real_eq (real_mult real_one (cauchy_real_sin d)) real_zero).
  { apply (real_eq_trans (real_mult real_one (cauchy_real_sin d))
             (real_mult (cauchy_real_exp real_zero) (cauchy_real_sin d))).
    - apply RealSetoid.real_eq_mult_compat;
        [exact (real_eq_sym _ _ cauchy_real_exp_zero) | apply real_eq_refl].
    - exact Hi. }
  split.
  - apply (real_eq_trans (cauchy_real_cos d)
             (real_mult real_one (cauchy_real_cos d)) real_one).
    + apply (real_eq_trans (cauchy_real_cos d)
               (real_mult (cauchy_real_cos d) real_one)
               (real_mult real_one (cauchy_real_cos d))).
      * apply real_eq_sym. apply real_mult_one.
      * exact (real_mult_comm (cauchy_real_cos d) real_one).
    + exact Hr1.
  - apply (real_eq_trans (cauchy_real_sin d)
             (real_mult real_one (cauchy_real_sin d)) real_zero).
    + apply (real_eq_trans (cauchy_real_sin d)
               (real_mult (cauchy_real_sin d) real_one)
               (real_mult real_one (cauchy_real_sin d))).
      * apply real_eq_sym. apply real_mult_one.
      * exact (real_mult_comm (cauchy_real_sin d) real_one).
    + exact Hs1.
Qed.


(* ===================================================================== *)
(* Section 4. The rounding core and the (b) roster statement.            *)
(* ===================================================================== *)

Definition e09_grid_pin (d : Real) (H : c_eq (c_exp (real_zero, d)) c_one)
  : sigT (fun k : Z => real_eq d (d09_two_pi k)).
Proof.
  assert (Hgrid : real_eq (real_mult (d09_two_pi 1) (real_mult d09_inv_two_pi d)) d)
    by exact (d09_grid_cancel_l d).
  destruct (e09_rat_approx (real_mult d09_inv_two_pi d)) as [q [N0 Hap]].
  destruct (e09_round_abs q) as [k Hk].
  assert (Hraw : sigT (fun N1 : nat => forall n : nat, (N1 <= n)%nat ->
            Qle (Qabs (projT1 (real_mult d09_inv_two_pi d) n - (k # 1)%Q))
                (33 / 64)%Q)).
  { exists N0. intros n Hn.
    apply (Qle_trans (Qabs (projT1 (real_mult d09_inv_two_pi d) n - (k # 1)%Q))
                     (Qabs (projT1 (real_mult d09_inv_two_pi d) n - q)
                      + Qabs (q - (k # 1)%Q))
                     (33 / 64)).
    - assert (Hr3 : ((projT1 (real_mult d09_inv_two_pi d) n - q)
                     + (q - (k # 1)%Q))%Q
                    == (projT1 (real_mult d09_inv_two_pi d) n - (k # 1)%Q)%Q)
        by ring.
      rewrite <- (Qabs_wd _ _ Hr3).
      apply Qabs_triangle.
    - apply (Qle_trans (Qabs (projT1 (real_mult d09_inv_two_pi d) n - q)
                        + Qabs (q - (k # 1)%Q))
                 (1 / 64 + 1 / 2)).
      + apply Qplus_le_compat; [exact (Hap n Hn) | exact Hk].
      + apply qeq_le. field. }
  assert (Hwin := e09_shift_window d (real_mult d09_inv_two_pi d) k Hgrid Hraw).
  assert (Hsum : c_eq (real_zero, real_plus d (real_opp (d09_two_pi k)))
                       (c_plus (real_zero, d)
                          (real_zero, real_opp (d09_two_pi k)))).
  { unfold c_eq. split.
    - exact (real_eq_sym _ _ (real_plus_zero real_zero)).
    - apply real_eq_refl. }
  assert (Hexp' := e09_exp_shift d (real_plus d (real_opp (d09_two_pi k))) k H Hsum).
  destruct (e09_proj_cos_sin (real_plus d (real_opp (d09_two_pi k))) Hexp')
    as [Hc Hs].
  assert (Hz : real_eq (real_plus d (real_opp (d09_two_pi k))) real_zero)
    by exact (d09_window_pin (real_plus d (real_opp (d09_two_pi k)))
                Hwin Hc Hs).
  exists k.
  apply (real_eq_trans d (real_plus (real_plus d (real_opp (d09_two_pi k)))
                            (d09_two_pi k)) (d09_two_pi k)).
  - apply real_eq_of_zero_diff. intro n.
    rewrite (real_plus_proj (real_plus d (real_opp (d09_two_pi k)))
               (d09_two_pi k) n).
    rewrite (real_plus_proj d (real_opp (d09_two_pi k)) n).
    rewrite (real_opp_proj (d09_two_pi k) n).
    ring.
  - apply (real_eq_trans (real_plus (real_plus d (real_opp (d09_two_pi k)))
                              (d09_two_pi k))
             (real_plus real_zero (d09_two_pi k)) (d09_two_pi k)).
    + apply RealSetoid.real_eq_plus_compat;
        [exact Hz | apply real_eq_refl].
    + apply (real_eq_trans (real_plus real_zero (d09_two_pi k))
               (real_plus (d09_two_pi k) real_zero)).
      * apply real_plus_comm.
      * apply real_plus_zero.
Defined.


