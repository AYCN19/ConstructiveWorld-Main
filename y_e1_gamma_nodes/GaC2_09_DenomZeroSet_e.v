(* ConstructiveWorld-Main - the Q-layer support kit of the denominator zero set *)
(** * GaC2_09_DenomZeroSet_e - - the Q-layer support kit and the rational rounding faces of
      the denominator zero set
    Mission.  Node C2-09 (segment C2, slot W1), support piece of the
      denominator zero set family.  Casts the absolute-value square faces ([e09q_sq_abs],
      [e09q_le_of_sq], [e09q_abs_le_of_sq]: t*t <= c*c forces |t| <= c),
      the factorial domination [e09_fact_ge_pow2] (2^(k-1) <= k!), the
      recurrence face [e09_exp_step], the rational-approximation face
      [e09_rat_approx] (every real has a rational matching it within
      1/64 at every late index), and the nearest-lattice rounding face
      [e09_round_abs] (the uniform exponential remainder lives in
      GaC2_09_DenomZeroSet_h and the ln 2 < 1 face in [_g]).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [QArith.Qring],
      [ZArith], [Setoid], [Morphisms],
      [Arith.Arith], [Lia]; [S01_BaseRing] (selective [NatLe]
      import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog], [GaC1_Iface_Cx], [GaC1_Iface_Real], and the
      family pieces [GaC2_09_DenomZeroSet_a] through [d] (named faces
      in Notes).
    References.  drafts_C2.md C2-09 card (:718-739) with the registered
      L11/L12 concretizations; the v16 receipt section VII casting spec.
    Constructivity.  Every named construction is carried by [Set]; zero
      Sections, zero assumed constants, zero admitted goals; every
      proof closes under the global context.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_09_DenomZeroSet_e.v]; flat build
      directory, acceptance via 50_toolkit/accept_node.py. *)
Require S01_BaseRing.
(** Notes.  Named consumed faces behind the Dependencies field:
    [c]: [d09_q_abs_pow_le_one], [d09_q_abs_le_of_both]; [d]:
    [d09_q_ep_mono], [d09_q_ep1], [d09_q_abs_div], [d09_ln2_pos];
    [S03_QExp]: [q_pow_abs], [q_fact_pos], [cauchy_real_exp_pos];
    [S07_RealSetoidExpLog]: [real_abs_diff_le_lift],
    [log_inv_exp_neg_thm], [real_log_lt_mono], [exp_const_proj],
    [real_const_lt], [real_eq_of_zero_diff]; [GaC1_Iface_Cx]
    supplies [real_le_b] and the real carrier faces; [d09_ln2] and
    [d09_two_pos] come from [GaC2_09_DenomZeroSet_b] (re-exported
    through [d]). *)
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

(* ===================================================================== *)
(* Section 1. Q-layer absolute values and factorial domination.          *)
(* ===================================================================== *)

Lemma e09q_sq_abs : forall x : Q, (Qabs x * Qabs x)%Q == (x * x)%Q.
Proof.
  intro x. destruct (Qlt_le_dec 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos x (Qlt_le_weak 0 x Hpos)). reflexivity.
  - assert (Hnt : Qle 0 (Qopp x)).
    { apply (Qopp_le_compat x 0 Hneg). }
    rewrite <- (Qabs_opp x).
    rewrite (Qabs_pos (Qopp x) Hnt).
    ring.
Qed.

Lemma e09q_le_of_sq : forall t c : Q,
  Qle 0 c -> Qle 0 t -> Qle (t * t) (c * c) -> Qle t c.
Proof.
  intros t c Hc0 Ht0 Hsq.
  destruct (Qeq_dec c 0) as [Hc0z | Hc0n].
  - rewrite Hc0z in Hsq. rewrite Qmult_0_r in Hsq.
    assert (Hsqe : t * t == 0).
    { apply (Qle_antisym (t * t) 0).
      - exact Hsq.
      - exact (q_square_nonneg t). }
    destruct (Qmult_integral t t Hsqe) as [Ht | Ht].
    + rewrite Ht. rewrite Hc0z. apply Qle_refl.
    + rewrite Ht. rewrite Hc0z. apply Qle_refl.
  - assert (Hcp : Qlt 0 c).
    { destruct (Qlt_le_dec 0 c) as [Hcpp | Hcn].
      - exact Hcpp.
      - exact (False_ind _ (Hc0n (Qeq_sym _ _ (Qle_antisym 0 c Hc0 Hcn)))). }
    destruct (Q_dec t c) as [[Hlt | Hgt] | Heq].
    + exact (Qlt_le_weak t c Hlt).
    + assert (Hcon : False).
      { assert (Hcc : Qlt (c * c) (t * c)).
        { apply (Qmult_lt_compat_r c t c Hcp Hgt). }
        assert (Hct : Qle c t) by exact (Qlt_le_weak c t Hgt).
        pose proof (Qmult_le_compat_r c t t Hct Ht0) as Hle2.
        assert (Hrw : (t * c)%Q == (c * t)%Q) by ring.
        rewrite Hrw in Hcc.
        exact (Qlt_not_le (c * c) (t * t)
                 (Qlt_le_trans (c * c) (c * t) (t * t) Hcc Hle2) Hsq). }
      exact (False_ind _ Hcon).
    + rewrite Heq. apply Qle_refl.
Qed.

Lemma e09q_abs_le_of_sq : forall t c : Q,
  Qle 0 c -> Qle (t * t) (c * c) -> Qle (Qabs t) c.
Proof.
  intros t c Hc0 Hsq.
  destruct (Qlt_le_dec 0 t) as [Hpos | Hneg].
  - apply (proj2 (Qabs_Qle_condition t c)). split.
    + apply (Qle_trans (Qopp c) (Qopp 0) t).
      * exact (Qopp_le_compat 0 c Hc0).
      * change (Qle 0 t). exact (Qlt_le_weak 0 t Hpos).
    + exact (e09q_le_of_sq t c Hc0 (Qlt_le_weak 0 t Hpos) Hsq).
  - assert (Hnt' : Qle 0 (Qopp t)).
    { apply (Qopp_le_compat t 0 Hneg). }
    assert (Hob : Qle (Qopp t) c).
    { assert (Hrw : ((Qopp t) * (Qopp t))%Q == (t * t)%Q) by ring.
      assert (Hsq2 : (Qopp t) * (Qopp t) <= c * c).
      { rewrite Hrw. exact Hsq. }
      exact (e09q_le_of_sq (Qopp t) c Hc0 Hnt' Hsq2). }
    apply (proj2 (Qabs_Qle_condition t c)). split.
    + apply (Qle_trans (Qopp c) (Qopp (Qopp t)) t).
      * apply (Qopp_le_compat (Qopp t) c Hob).
      * apply qeq_le. ring.
    + apply (Qle_trans t 0 c).
      * exact Hneg.
      * exact Hc0.
Qed.

Lemma e09q_pow2_pos : forall j : nat, Qlt 0 (q_pow 2 j).
Proof.
  intro j. induction j as [| j IH].
  - unfold Qlt. simpl. lia.
  - rewrite (q_pow_succ 2 j).
    apply (Qmult_lt_0_compat 2 (q_pow 2 j)).
    + unfold Qlt. simpl. lia.
    + exact IH.
Qed.

Lemma e09_fact_ge_pow2 : forall k : nat, Qle (q_pow 2 (k - 1)) (q_fact k).
Proof.
  intro k. induction k as [| k IH].
  - cbn [Nat.sub q_pow q_fact]. unfold Qle. simpl. lia.
  - destruct k as [| k'].
    + cbn [Nat.sub q_pow q_fact]. unfold Qle. simpl. lia.
    + replace (Nat.sub (Datatypes.S (Datatypes.S k')) 1)
        with (Datatypes.S k') by lia.
      rewrite (q_pow_succ 2 k').
      assert (Hq : q_fact (Datatypes.S (Datatypes.S k')) ==
                   ((Z.of_nat (Datatypes.S (Datatypes.S k')) # 1)
                    * q_fact (Datatypes.S k'))%Q)
        by (cbn [q_fact]; reflexivity).
      rewrite Hq.
      assert (H2 : Qle (2 # 1)
                     ((Z.of_nat (Datatypes.S (Datatypes.S k')) # 1)))
        by (unfold Qle; simpl; lia).
      assert (Hpos : Qle 0 (q_fact (Datatypes.S k')))
        by (apply (Qlt_le_weak 0 (q_fact (Datatypes.S k')));
            apply q_fact_pos).
      assert (H02 : Qle 0 2) by (unfold Qle; simpl; lia).
      replace (Nat.sub (Datatypes.S k') 1) with k' in IH by lia.
      apply (Qle_trans (2 * q_pow 2 k') (2 * q_fact (Datatypes.S k'))
               ((Z.of_nat (Datatypes.S (Datatypes.S k')) # 1)
                * q_fact (Datatypes.S k'))).
      * assert (Hrw2 : (2 * q_pow 2 k')%Q == (q_pow 2 k' * 2)) by ring.
        rewrite Hrw2.
        rewrite (Qmult_comm 2 (q_fact (Datatypes.S k'))).
        exact (Qmult_le_compat_r (q_pow 2 k') (q_fact (Datatypes.S k')) 2
                 IH H02).
      * exact (Qmult_le_compat_r 2
                 ((Z.of_nat (Datatypes.S (Datatypes.S k')) # 1))
                 (q_fact (Datatypes.S k')) H2 Hpos).
Qed.

(* ===================================================================== *)
(* Section 2. The uniform exponential remainder.                         *)
(* ===================================================================== *)

(* Recurrence unfolding: exp_partial (S m) x = exp_partial m x + the
   (S m)-th term. *)
Lemma e09_exp_step : forall (m : nat) (x : Q),
  exp_partial (Datatypes.S m) x
  == exp_partial m x + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m).
Proof. intros m x. reflexivity. Qed.

(* The uniform exponential remainder face (|exp_partial n x - 1 - x| <=
   x*x for |x| <= 1, uniform in n) is cast in GaC2_09_DenomZeroSet_h on
   top of the recurrence [e09_exp_step] and the factorial-geometric
   domination [e09_fact_ge_pow2] cast in this piece. *)

Definition e09_rat_approx (x : Real)
  : sigT (fun q : Q => sigT (fun N0 : nat => forall n : nat,
      (N0 <= n)%nat -> Qle (Qabs (projT1 x n - q)) (1 / 64)%Q)).
Proof.
  destruct x as [u Hu].
  assert (Hq : Qlt 0 (1 / 64)) by (unfold Qlt; simpl; lia).
  destruct (Hu (1 / 64) (Qlt_to_QltT 0 (1 / 64) Hq)) as [N0 HN0].
  exists (u N0). exists N0. intros n Hn.
  apply Qlt_le_weak. apply QltT_to_Qlt.
  exact (HN0 n N0 (NatLe_lift N0 n Hn) (NatLe_lift N0 N0 (le_n N0))).
Defined.


Lemma e09_round_abs : forall q : Q,
  sigT (fun k : Z => Qle (Qabs (q - (k # 1)%Q)) (1 / 2)%Q).
Proof.
  intro q.
  destruct (d09_floor_bounds (q + 1 / 2)) as [k [Hlo Hhi]].
  exists k.
  apply (d09_q_abs_le_of_both (q - (k # 1)%Q) (1 / 2)).
  - assert (Hk1 : ((k + 1) # 1)%Q == ((k # 1)%Q + 1)%Q)
      by (unfold Qeq, Qeq_bool; simpl; ring).
    rewrite Hk1 in Hhi.
    apply (Qlt_le_weak _ _).
    apply (proj2 (Qlt_minus_iff (q - (k # 1)%Q) (1 / 2))).
    assert (Hrw : (1 / 2 - (q - (k # 1)%Q))%Q
                  == ((k # 1)%Q + 1 + -(q + 1 / 2))%Q) by field.
    rewrite Hrw.
    apply (proj1 (Qlt_minus_iff (q + 1 / 2) ((k # 1)%Q + 1))).
    exact Hhi.
  - apply (proj2 (Qle_minus_iff (Qopp (1 / 2)) (q - (k # 1)%Q))).
    assert (Hrw2 : ((q - (k # 1)%Q) - Qopp (1 / 2))%Q
                   == ((q + 1 / 2) - (k # 1)%Q)%Q) by ring.
    rewrite Hrw2.
    exact (proj1 (Qle_minus_iff (k # 1)%Q (q + 1 / 2)) Hlo).
Qed.
