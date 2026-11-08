(* ConstructiveWorld-Main - the dyadic condensation engine behind the
   absolute-convergence tail bounds. *)
(** * GaC2_02_AbsConvTailBound_c: the condensation engine leaf.
    Mission.  The dyadic condensation engine behind the three main
      lemmas of the stem [GaC2_02_AbsConvTailBound]: the real-slice
      tail faces [r_tsum_ge0]/[r_tail_ge0]/[r_tail_zero]/
      [r_tail_chain_add]/[r_tail_chain]/[r_tail_mono] (nonnegativity,
      vanishing, additivity, monotonicity in the right endpoint); the
      three blueprint Definitions [r_two_rpow] (2^t := exp(t * ln 2)),
      [r_geom_den] (1 - 2^{1-sigma}), [r_geom_const]
      (1 + 2^{1-sigma}/(1 - 2^{1-sigma})) with the sigT inverse
      [c_inv_wit] and the faces [r_geom_den_pos]/[r_geom_const_inv]/
      [r_geom_const_pos]; the power carrier [r_m1sig] (M^{1-sigma})
      with [r_m1sig_pos]; the anchored block bound [r_block_le]
      (sum_{L<j<=2L} j^{-sigma} <= L^{1-sigma}); the factorisation
      [r_m1sig_dyadic] ((M*2^k)^{1-sigma} == M^{1-sigma} * q^k); the
      dyadic tail sum [r_tail_dyadic] (tail M (M*2^K) <=
      M^{1-sigma} * gsum q K); and the strict geometric closure
      [r_gsum_lt_geom] (gsum q K < 1 + q/(1-q), multiplied form, zero
      division: the inverse enters only through [c_inv_wit]).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith], [Lia].  Requires [S01_BaseRing] (selective
      [NatLe] import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog], [GaC2_01_DirichletPartialSum], and leaves
      [GaC2_02_AbsConvTailBound_a]/[_b] of this development (DAG
      a <- b <- c <- stem; no leaf Requires the stem; zero Export).
    References.  Card C2.02 leaf split; tree precedent
      piu_zz_tau_segtree_1024_leaf_a..h + _merge.
    Constructivity.  Red path A: all statements Set-sorted; no
      rring/destruct-Real inside the Section; closed under the global
      context; [coqchk] reports zero assumed constants.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_02_AbsConvTailBound_c.v] compiles cleanly
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
Require Import GaC2_02_AbsConvTailBound_a.
Require Import GaC2_02_AbsConvTailBound_b.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Section CondensationEngine.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable sig : Real.
Hypothesis Hsig1 : real_lt real_one sig.
Hypothesis Hlnmono :
  forall (m n : nat) (Hm : real_lt real_zero (nat_real m)) (Hn : real_lt real_zero (nat_real n)),
    real_lt (nat_real m) (nat_real n) ->
    real_lt (real_log (nat_real m) Hm) (real_log (nat_real n) Hn).
Hypothesis Hln2pos : real_lt real_zero (r_ln Hnpos 2 (NatLe_one_S 1)).

Local Notation rtail := (r_tail Hnpos sig).
Local Notation rtsum := (r_tsum Hnpos sig).
Local Notation rnpow := (r_npow Hnpos sig).
Local Notation L2 := (r_ln Hnpos 2 (NatLe_one_S 1)).

(* ==== Real-slice tail faces ==== *)
Lemma r_tsum_ge0 : forall (M N : nat), real_le real_zero (rtsum M N).
Proof.
  intros M N. induction N as [|N IH].
  - cbn [r_tsum]. apply r_le_of_eq. apply real_eq_refl.
  - cbn [r_tsum]. apply r_le_zero_plus.
    + exact IH.
    + destruct (Nat.ltb M (S N)).
      * apply (real_lt_le_iff real_zero (rnpow (S N) (NatLe_one_S N))). left.
        apply r_npow_pos.
      * apply r_le_of_eq. apply real_eq_refl.
Qed.

Lemma r_tail_ge0 : forall (M N : nat), real_le real_zero (rtail M N).
Proof.
  intros M N. pose proof (r_tsum_ge0 M N) as H. pose proof (r_tsum_r_tail Hnpos sig M N) as E.
  unfold real_le. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (inl (real_lt_eq_lt real_zero (rtsum M N) (rtail M N) Hlt E)).
  - exact (inr (real_eq_trans real_zero (rtsum M N) (rtail M N) Heq E)).
Qed.

Lemma r_tail_zero : forall (M N : nat), NatLe N M -> real_eq (rtail M N) real_zero.
Proof.
  intros M N HNM.
  exact (real_eq_trans (rtail M N) (rtsum M N) real_zero
           (real_eq_sym (rtsum M N) (rtail M N) (r_tsum_r_tail Hnpos sig M N))
           (r_tsum_zero_le Hnpos sig M N HNM)).
Qed.

(* Tail additivity on the increment d (real-slice induction). *)
Lemma r_tail_chain_add : forall (M N d : nat), NatLe M N ->
  real_eq (rtail M (N + d)) (real_plus (rtail M N) (rtail N (N + d))).
Proof.
  intros M N d HMN. assert (HMle : (M <= N)%nat) by (apply NatLe_drop; exact HMN).
  induction d as [|d IH].
  - apply (real_eq_trans _ (rtail M N)).
    + rewrite (Nat.add_0_r N). apply real_eq_refl.
    + rewrite (Nat.add_0_r N).
      exact (real_eq_trans (rtail M N) (real_plus (rtail M N) real_zero)
               (real_plus (rtail M N) (rtail N N))
               (real_eq_sym _ _ (r_plus_zero_r_gen (rtail M N)))
               (RealSetoid.real_eq_plus_compat (rtail M N) real_zero (rtail M N) (rtail N N)
                  (real_eq_refl _)
                  (real_eq_sym _ _ (r_tail_zero N N (NatLe_lift _ _ (Nat.le_refl N)))))).
  - assert (HMlt : Nat.ltb M (S (N + d)) = true) by (apply Nat.ltb_lt; lia).
    assert (HNlt : Nat.ltb N (S (N + d)) = true) by (apply Nat.ltb_lt; lia).
    rewrite (Nat.add_succ_r N d).
    unfold r_tail. cbn [c_tail]. rewrite HMlt. rewrite HNlt. cbn [c_tail].
    apply (real_eq_trans _ (real_plus (cRe (c_tail Hnpos M (N + d) (c_of_real sig)))
             (cRe (c_powq Hnpos (S (N + d)) (NatLe_one_S (N + d)) (c_of_real sig))))).
    { apply cRe_plus_wd. }
    apply (real_eq_trans _ (real_plus (real_plus (cRe (c_tail Hnpos M N (c_of_real sig)))
                                                 (cRe (c_tail Hnpos N (N + d) (c_of_real sig))))
             (cRe (c_powq Hnpos (S (N + d)) (NatLe_one_S (N + d)) (c_of_real sig))))).
    { apply (RealSetoid.real_eq_plus_compat _ _ _ _ IH (real_eq_refl _)). }
    apply (real_eq_trans _ (real_plus (cRe (c_tail Hnpos M N (c_of_real sig)))
             (real_plus (cRe (c_tail Hnpos N (N + d) (c_of_real sig)))
                        (cRe (c_powq Hnpos (S (N + d)) (NatLe_one_S (N + d)) (c_of_real sig)))))).
    { apply (real_eq_sym _ _). apply real_plus_assoc. }
    apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)).
    apply (real_eq_sym _ _). apply cRe_plus_wd.
Qed.

Lemma r_tail_chain : forall (M N P : nat), NatLe M N -> NatLe N P ->
  real_eq (rtail M P) (real_plus (rtail M N) (rtail N P)).
Proof.
  intros M N P HMN HNP. apply NatLe_drop in HNP.
  replace P with ((N + (P - N))%nat) by lia.
  exact (r_tail_chain_add M N (P - N) HMN).
Qed.

Lemma r_tail_mono : forall (M N P : nat), NatLe M N -> NatLe N P ->
  real_le (rtail M N) (rtail M P).
Proof.
  intros M N P HMN HNP.
  pose proof (r_tail_ge0 N P) as Hnp.
  pose proof (r_tail_chain M N P HMN HNP) as Hch.
  apply (RealSetoid.real_le_compat (rtail M N) (rtail M N)
           (real_plus (rtail M N) (rtail N P)) (rtail M P)
           (real_eq_refl _) (real_eq_sym _ _ Hch)).
  apply r_le_plus_nonneg. exact Hnp.
Qed.

(* ==== The three blueprint Definitions (card C2.02 (a) closed form) ==== *)
(* 2^t := exp(t * ln 2), constant-power carrier (zero branching). *)
Definition r_two_rpow (t : Real) : Real := cauchy_real_exp (real_mult t L2).

Lemma r_two_rpow_q1 : real_eq (r_two_rpow (real_plus real_one (real_opp sig))) (r_q1 Hnpos sig).
Proof. unfold r_two_rpow, r_q1, r_sub1. apply cauchy_real_exp_wd. apply r_one_minus_opp. Qed.

(* 1 - 2^{1-sigma}, strictly positive for sigma > 1. *)
Definition r_geom_den : Real :=
  real_plus real_one (real_opp (r_two_rpow (real_plus real_one (real_opp sig)))).

Lemma r_geom_den_pos : real_lt real_zero r_geom_den.
Proof.
  unfold r_geom_den.
  apply (RealSetoid.real_lt_compat real_zero real_zero
           (real_plus real_one (real_opp (r_q1 Hnpos sig)))
           (real_plus real_one (real_opp (r_two_rpow (real_plus real_one (real_opp sig)))))
           (real_eq_refl _)).
  - apply RealSetoid.real_eq_plus_compat; [apply real_eq_refl |].
    apply RealSetoid.real_eq_opp_compat. apply (real_eq_sym _ _). apply r_two_rpow_q1.
  - exact (real_lt_opp_plus (r_q1 Hnpos sig) real_one (r_q1_lt_one Hnpos sig Hsig1 Hln2pos)).
Qed.

(* 1 + 2^{1-sigma} * (1-2^{1-sigma})^{-1}; division through the sigT
   inverse witness c_inv_wit (discharged in GaC2_01 Section 4). *)
Definition r_geom_const : Real :=
  real_plus real_one
    (real_mult (r_two_rpow (real_plus real_one (real_opp sig)))
               (c_inv_wit r_geom_den r_geom_den_pos)).

Lemma r_geom_const_inv : real_eq r_geom_const (c_inv_wit r_geom_den r_geom_den_pos).
Proof.
  unfold r_geom_const. apply r_geom_inv_fold.
  exact (c_inv_wit_correct r_geom_den r_geom_den_pos).
Qed.

Lemma r_geom_const_pos : real_lt real_zero r_geom_const.
Proof.
  unfold r_geom_const.
  apply (real_lt_le_trans _ real_one); [exact real_lt_zero_one |].
  apply r_le_plus_nonneg. apply (real_lt_le_iff _ _). left.
  apply real_mult_positive; [apply cauchy_real_exp_pos | unfold c_inv_wit; apply real_inv_pos_pos].
Qed.

(* ==== M^{1-sigma} and the anchored block bound ==== *)
Definition r_m1sig (M : nat) (HM : NatLe 1 M) : Real :=
  cauchy_real_exp (real_mult (real_opp (r_sub1 sig)) (r_ln Hnpos M HM)).

Lemma r_m1sig_pos : forall (M : nat) (HM : NatLe 1 M), real_lt real_zero (r_m1sig M HM).
Proof. intros M HM. apply cauchy_real_exp_pos. Qed.

(* sum_{L<j<=2L} j^{-sigma} <= L * L^{-sigma} = L^{1-sigma}. *)
Lemma r_block_le : forall (L : nat) (HL : NatLe 1 L),
  real_le (rtail L (2 * L)) (r_m1sig L HL).
Proof.
  intros L HL.
  assert (Hcnt : (2 * L - L)%nat = L) by lia.
  assert (Hmain : real_le (rtsum L (2 * L))
                          (real_mult (nat_real (2 * L - L)) (rnpow L HL))).
  { apply r_tsum_le_const.
    - apply NatLe_lift. lia.
    - intros j Hj Hj1 Hj2. apply (r_npow_anti Hnpos sig Hsig1 Hlnmono L j HL Hj).
      apply NatLe_lift. apply NatLe_drop in Hj1. lia. }
  rewrite Hcnt in Hmain. unfold r_m1sig.
  apply (RealSetoid.real_le_compat _ _ _ _ (r_tsum_r_tail Hnpos sig L (2 * L))
           (r_two_npow_prod Hnpos sig L HL)).
  exact Hmain.
Qed.

(* (M * 2^k)^{1-sigma} == M^{1-sigma} * q^k  (log additivity through the
   witness-matched r_ln_mul / r_ln_pow2 and the exp addition law). *)
Lemma r_m1sig_dyadic : forall (M k : nat) (HM : NatLe 1 M) (HMk : NatLe 1 (M * Nat.pow 2 k)),
  real_eq (r_m1sig (M * Nat.pow 2 k) HMk)
          (real_mult (r_m1sig M HM) (r_qpow (r_q1 Hnpos sig) k)).
Proof.
  intros M k HM HMk. unfold r_m1sig.
  apply (real_eq_trans _ (cauchy_real_exp (real_mult (real_opp (r_sub1 sig))
           (real_plus (r_ln Hnpos M HM) (real_mult (nat_real k) L2))))).
  - apply cauchy_real_exp_wd.
    apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)).
    apply (real_eq_trans _ (real_plus (r_ln Hnpos M HM) (r_ln Hnpos (Nat.pow 2 k) (r_pow2_ge1 k)))).
    + exact (r_ln_mul Hnpos M (Nat.pow 2 k) HM (r_pow2_ge1 k) HMk).
    + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) (r_ln_pow2 Hnpos k)).
  - apply (real_eq_trans _ (cauchy_real_exp (real_plus
             (real_mult (real_opp (r_sub1 sig)) (r_ln Hnpos M HM))
             (real_mult (real_opp (r_sub1 sig)) (real_mult (nat_real k) L2))))).
    + apply cauchy_real_exp_wd. apply r_mult_plus_distr_l.
    + apply (real_eq_trans _ (real_mult
               (cauchy_real_exp (real_mult (real_opp (r_sub1 sig)) (r_ln Hnpos M HM)))
               (cauchy_real_exp (real_mult (real_opp (r_sub1 sig)) (real_mult (nat_real k) L2))))).
      * apply cauchy_real_exp_plus.
      * apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
                 (real_eq_sym _ _ (r_q1_qpow Hnpos sig k))).
Qed.

(* tail M (M * 2^K) <= M^{1-sigma} * gsum q K  (dyadic blocks anchored at M). *)
Lemma r_tail_dyadic : forall (M : nat) (HM : NatLe 1 M) (K : nat),
  real_le (rtail M (M * Nat.pow 2 K))
          (real_mult (r_m1sig M HM) (r_gsum (r_q1 Hnpos sig) K)).
Proof.
  intros M HM K. pose proof (NatLe_drop _ _ HM) as HM1.
  induction K as [|K IH].
  - cbn [Nat.pow r_gsum]. rewrite (Nat.mul_1_r M).
    apply (RealSetoid.real_le_compat real_zero (rtail M M) real_zero
             (real_mult (r_m1sig M HM) real_zero)
             (real_eq_sym _ _ (r_tail_zero M M (NatLe_lift _ _ (Nat.le_refl M))))
             (real_eq_sym _ _ (real_mult_zero (r_m1sig M HM)))).
    apply real_le_refl.
  - pose proof (NatLe_drop _ _ (r_pow2_ge1 K)) as HpK.
    assert (HMK : NatLe 1 (M * Nat.pow 2 K)) by (apply NatLe_lift; nia).
    assert (Hle1 : NatLe M (M * Nat.pow 2 K)) by (apply NatLe_lift; nia).
    assert (Hle2 : NatLe (M * Nat.pow 2 K) (M * Nat.pow 2 (S K)))
      by (apply NatLe_lift; cbn [Nat.pow]; nia).
    assert (Heq2 : (M * Nat.pow 2 (S K))%nat = (2 * (M * Nat.pow 2 K))%nat)
      by (cbn [Nat.pow]; lia).
    cbn [r_gsum].
    apply (RealSetoid.real_le_compat
             (real_plus (rtail M (M * Nat.pow 2 K)) (rtail (M * Nat.pow 2 K) (M * Nat.pow 2 (S K))))
             (rtail M (M * Nat.pow 2 (S K)))
             (real_plus (real_mult (r_m1sig M HM) (r_gsum (r_q1 Hnpos sig) K))
                        (real_mult (r_m1sig M HM) (r_qpow (r_q1 Hnpos sig) K)))
             (real_mult (r_m1sig M HM) (real_plus (r_gsum (r_q1 Hnpos sig) K) (r_qpow (r_q1 Hnpos sig) K)))
             (real_eq_sym _ _ (r_tail_chain M (M * Nat.pow 2 K) (M * Nat.pow 2 (S K)) Hle1 Hle2))
             (real_eq_sym _ _ (r_mult_plus_distr_l (r_m1sig M HM) _ _))).
    apply real_le_plus_compat.
    + exact IH.
    + rewrite Heq2.
      apply (RealSetoid.real_le_compat _ _ _ _ (real_eq_refl _) (r_m1sig_dyadic M K HM HMK)).
      exact (r_block_le (M * Nat.pow 2 K) HMK).
Qed.

(* Strict geometric closure: gsum q K < 1 + q/(1-q)  (= (1-q)^{-1}). *)
Lemma r_gsum_lt_geom : forall K : nat, real_lt (r_gsum (r_q1 Hnpos sig) K) r_geom_const.
Proof.
  intro K.
  set (q := r_q1 Hnpos sig). set (inv := c_inv_wit r_geom_den r_geom_den_pos).
  assert (Hinvpos : real_lt real_zero inv) by (unfold inv, c_inv_wit; apply real_inv_pos_pos).
  assert (H1 : real_lt (real_mult (r_gsum q K) r_geom_den) real_one).
  { apply (RealSetoid.real_lt_compat (real_mult (r_gsum q K) (real_plus real_one (real_opp q)))
             (real_mult (r_gsum q K) r_geom_den) real_one real_one).
    - apply RealSetoid.real_eq_mult_compat; [apply real_eq_refl |].
      unfold r_geom_den. apply RealSetoid.real_eq_plus_compat; [apply real_eq_refl |].
      apply RealSetoid.real_eq_opp_compat. apply (real_eq_sym _ _). apply r_two_rpow_q1.
    - apply real_eq_refl.
    - apply r_gsum_lt_one. apply r_q1_pos. }
  assert (H2 : real_lt (real_mult inv (real_mult (r_gsum q K) r_geom_den)) (real_mult inv real_one))
    by (apply real_lt_mult_compat; [exact Hinvpos | exact H1]).
  apply (RealSetoid.real_lt_compat (real_mult inv (real_mult (r_gsum q K) r_geom_den)) (r_gsum q K)
           (real_mult inv real_one) r_geom_const).
  - apply (real_eq_trans _ (real_mult (r_gsum q K) (real_mult r_geom_den inv))).
    + apply r_mult_rotate.
    + apply (real_eq_trans _ (real_mult (r_gsum q K) real_one)).
      * apply RealSetoid.real_eq_mult_compat;
          [apply real_eq_refl | exact (c_inv_wit_correct r_geom_den r_geom_den_pos)].
      * apply real_mult_one.
  - apply (real_eq_trans _ inv).
    + apply real_mult_one.
    + apply (real_eq_sym _ _). apply r_geom_const_inv.
  - exact H2.
Qed.

End CondensationEngine.
