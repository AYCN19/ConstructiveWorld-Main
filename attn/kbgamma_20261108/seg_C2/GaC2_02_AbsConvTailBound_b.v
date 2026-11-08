(* ConstructiveWorld-Main - sectioned term/tail core of the absolute-
   convergence machinery: embedded-natural log, power, and condensation. *)
(** * GaC2_02_AbsConvTailBound_b: the sectioned term/tail core leaf.
    Mission.  The sectioned term/tail core of the absolute-convergence
      machinery: the embedded-natural logarithm [r_ln] and power term
      [r_npow] (n^{-sigma}) with their witness-irrelevance faces
      [r_ln_irrel]/[r_npow_irrel] and antitonicity [r_npow_anti]; the
      partial sum [r_tsum] with its complex-slice mirror [r_tail] and
      the identity [r_tsum_r_tail]; the positivity faces
      [r_npow_pos]/[r_sig_pos]/[r_sub1_pos]; the counting identity
      [r_two_npow_prod]; the log additivity [r_ln_mul]/[r_ln_pow2] on
      the embedded naturals; the bounded-sum faces
      [r_tsum_le_const]/[r_tsum_zero_le]; and the condensation block
      carriers [r_two_block]/[q_condensation_block] with the ratio
      constant [r_q1] and its faces [r_q1_pos]/[r_q1_lt_one]/
      [r_q1_qpow].
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith], [Lia].  Requires [S01_BaseRing] (selective
      [NatLe] import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog], [GaC2_01_DirichletPartialSum], and leaf _a
      [GaC2_02_AbsConvTailBound_a] of this development; Import only
      (never leaf _c or the stem, so the DAG stays acyclic).
    References.  Card C2.02 leaf split (see the stem header).  The nat
      premise slots are carried by [NatLe] throughout: [r_ln]/[r_npow]
      gain the explicit NatLe 1 n argument, while
      [r_tsum]/[r_two_block]/[r_q1] build the witness internally
      (their indices are S m / 2^k / 2); [r_tsum_le_const]'s per-j
      bound premise is NatLe-carried (NatLe (S M) j / NatLe j N),
      with no stdlib Prop order in any nat premise slot.
    Constructivity.  Red path A: all statements Set-sorted; no
      rring/destruct-Real inside the Section; closed under the global
      context; [coqchk] reports zero assumed constants.  GAPASUME
      slots (Section hypotheses, discharged at [End]): L-C2.02-A
      [Hlnmono], L-C2.02-B [Hln2pos], both L0-stock instantiable
      ([real_log_lt_mono] S07:6540, [real_log_one] S07:7894 + leaf-a
      [real_log_wd]); the satisfiability probe instantiates them from
      L0 stock.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_02_AbsConvTailBound_b.v] compiles cleanly
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
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Section AbsConvTailBound.

(* Premise-parametrised positivity face: inhabited exactly on n >= 1. *)
Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable sig : Real.
Hypothesis Hsig1 : real_lt real_one sig.

Definition r_ln (n : nat) (Hn : NatLe 1 n) : Real :=
  real_log (nat_real n) (Hnpos n Hn).

(* GAPASUME slot L-C2.02-A: strict monotonicity of the tree real log on the
   embedded naturals (L0 stock: real_log_lt_mono S07:6540). *)
Hypothesis Hlnmono :
  forall (m n : nat) (Hm : real_lt real_zero (nat_real m)) (Hn : real_lt real_zero (nat_real n)),
    real_lt (nat_real m) (nat_real n) ->
    real_lt (real_log (nat_real m) Hm) (real_log (nat_real n) Hn).
(* GAPASUME slot L-C2.02-B: positivity of ln 2 (L0 stock: real_log_lt_mono
   at (1,2) + real_log_one S07:7894 + leaf-a real_log_wd). *)
Hypothesis Hln2pos : real_lt real_zero (r_ln 2 (NatLe_one_S 1)).

Definition r_npow (n : nat) (Hn : NatLe 1 n) : Real :=
  cauchy_real_exp (real_mult (real_opp sig) (r_ln n Hn)).   (* n^{-sigma} *)
Definition r_sub1 : Real := real_plus sig (real_opp real_one).   (* sigma-1 *)
Fixpoint r_tsum (M N : nat) : Real :=
  match N with
  | O => real_zero
  | S m => real_plus (r_tsum M m)
             (if Nat.ltb M (S m) then r_npow (S m) (NatLe_one_S m) else real_zero)
  end.
Definition r_tail (M N : nat) : Real := cRe (c_tail Hnpos M N (c_of_real sig)).

Lemma r_npow_slice : forall (n : nat) (Hn : NatLe 1 n),
  real_eq (cRe (c_powq Hnpos n Hn (c_of_real sig))) (r_npow n Hn).
Proof.
  intros n Hn. unfold c_powq, r_npow, r_ln. set (l := real_log (nat_real n) (Hnpos n Hn)).
  apply (real_eq_trans _
    (cRe (c_exp (c_of_real (real_mult (real_opp real_one) (real_mult sig l)))))).
  - apply cRe_wd. apply c_exp_wd.
    apply (c_eq_trans _ (c_scale (real_opp real_one) (c_of_real (real_mult sig l)))).
    + apply c_scale_wd. apply (c_of_real_mult_gen sig l).
    + apply (c_of_real_scale_gen (real_opp real_one) (real_mult sig l)).
  - apply (real_eq_trans _
      (cauchy_real_exp (real_mult (real_opp real_one) (real_mult sig l)))).
    + exact (cRe_wd _ _ (c_exp_real (real_mult (real_opp real_one) (real_mult sig l)))).
    + apply cauchy_real_exp_wd. apply (r_assoc_scale sig l).
Qed.

Lemma r_tsum_r_tail : forall M N : nat, real_eq (r_tsum M N) (r_tail M N).
Proof.
  intros M N. unfold r_tail. induction N as [|N IH].
  - cbn [r_tsum c_tail]. apply real_eq_refl.
  - cbn [r_tsum c_tail]. destruct (Nat.ltb M (S N)).
    + apply (real_eq_trans _ (real_plus (cRe (c_tail Hnpos M N (c_of_real sig)))
                                        (cRe (c_powq Hnpos (S N) (NatLe_one_S N) (c_of_real sig))))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ IH
                 (real_eq_sym _ _ (r_npow_slice (S N) (NatLe_one_S N)))).
      * apply (real_eq_sym _ _). apply cRe_plus_wd.
    + apply (real_eq_trans _ (real_plus (cRe (c_tail Hnpos M N (c_of_real sig))) (cRe c_zero))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ IH (real_eq_refl _)).
      * apply (real_eq_sym _ _). apply cRe_plus_wd.
Qed.

Lemma r_npow_pos : forall (n : nat) (Hn : NatLe 1 n), real_lt real_zero (r_npow n Hn).
Proof. intros n Hn. unfold r_npow. apply cauchy_real_exp_pos. Qed.

Lemma r_sig_pos : real_lt real_zero sig.
Proof.
  apply (real_lt_le_trans real_zero real_one sig); [exact real_lt_zero_one |].
  apply (real_lt_le_iff real_one sig). left. exact Hsig1.
Qed.

Lemma r_sub1_pos : real_lt real_zero r_sub1.
Proof.
  unfold r_sub1.
  apply (RealSetoid.real_lt_compat (real_plus real_one (real_opp real_one)) real_zero
           (real_plus sig (real_opp real_one)) (real_plus sig (real_opp real_one))).
  - apply real_eq_of_zero_diff. intro n. simpl. ring.
  - apply real_eq_refl.
  - apply real_lt_plus_compat_lt_le; [exact Hsig1 | apply real_le_refl].
Qed.

(* Witness-irrelevance faces (real_log is sensitive to its positivity
   witness; leaf-a real_log_wd supplies the congruence). *)
Lemma r_ln_irrel : forall (n : nat) (Hn Hn' : NatLe 1 n),
  real_eq (r_ln n Hn) (r_ln n Hn').
Proof.
  intros n Hn Hn'. unfold r_ln.
  apply (real_log_wd (nat_real n) (nat_real n)). apply real_eq_refl.
Qed.

Lemma r_npow_irrel : forall (n : nat) (Hn Hn' : NatLe 1 n),
  real_eq (r_npow n Hn) (r_npow n Hn').
Proof.
  intros n Hn Hn'. unfold r_npow.
  apply cauchy_real_exp_wd.
  apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _) (r_ln_irrel n Hn Hn')).
Qed.

Lemma r_npow_anti : forall (m n : nat) (Hm : NatLe 1 m) (Hn : NatLe 1 n),
  NatLe m n -> real_le (r_npow n Hn) (r_npow m Hm).
Proof.
  intros m n Hm Hn Hmn. destruct (Nat.eq_dec m n) as [Heq | Hne].
  - subst n. apply r_le_of_eq. apply r_npow_irrel.
  - assert (Hlt : (m < n)%nat)
      by (assert (Hle : (m <= n)%nat) by (apply NatLe_drop; exact Hmn); lia).
    assert (Hloglt : real_lt (r_ln m Hm) (r_ln n Hn))
      by (unfold r_ln; apply Hlnmono; apply nat_real_lt; apply NatLe_lift; lia).
    assert (Hscale : real_lt (real_mult sig (r_ln m Hm)) (real_mult sig (r_ln n Hn)))
      by (apply (real_lt_mult_compat _ _ _ r_sig_pos Hloglt)).
    apply (real_lt_le_iff (r_npow n Hn) (r_npow m Hm)). left.
    unfold r_npow. apply cauchy_real_exp_mono.
    apply (RealSetoid.real_lt_compat _ _ _ _
             (real_eq_sym _ _ (r_mult_opp_l sig (r_ln n Hn)))
             (real_eq_sym _ _ (r_mult_opp_l sig (r_ln m Hm)))).
    apply r_lt_opp_flip. exact Hscale.
Qed.

Lemma r_tsum_zero_le : forall (M N : nat), NatLe N M -> real_eq (r_tsum M N) real_zero.
Proof.
  intros M N. revert M. induction N as [|N IH]; intros M HNM.
  - cbn [r_tsum]. apply real_eq_refl.
  - cbn [r_tsum].
    assert (HLtb : Nat.ltb M (S N) = false) by (apply Nat.ltb_ge; apply NatLe_drop; exact HNM).
    rewrite HLtb.
    apply (real_eq_trans _ (r_tsum M N)); [apply (r_plus_zero_r_gen (r_tsum M N)) |].
    apply IH. apply NatLe_lift.
    apply Nat.le_trans with (S N); [apply Nat.le_succ_diag_r | apply NatLe_drop; exact HNM].
Qed.

(* The per-j bound premise is NatLe-carried (NatLe (S M) j / NatLe j N). *)
Lemma r_tsum_le_const : forall (M N : nat) (v : Real), NatLe M N ->
  (forall (j : nat) (Hj : NatLe 1 j), NatLe (S M) j -> NatLe j N -> real_le (r_npow j Hj) v) ->
  real_le (r_tsum M N) (real_mult (nat_real (N - M)) v).
Proof.
  intros M N v. revert M. induction N as [|N IH]; intros M Hle Hbnd.
  - assert (HM : M = 0%nat) by (apply Nat.le_0_r; apply NatLe_drop; exact Hle).
    subst M. cbn [r_tsum]. apply r_le_of_eq.
    destruct v as [uv Hv]. apply real_eq_of_zero_diff. intro k. simpl. ring.
  - cbn [r_tsum]. destruct (Nat.ltb M (S N)) eqn:HLtb.
    + apply Nat.ltb_lt in HLtb.
      assert (HMN : NatLe M N) by (apply NatLe_lift; lia).
      assert (Hsub : (S N - M)%nat = S (N - M)) by lia.
      assert (HRHS : real_eq (real_mult (nat_real (S N - M)) v)
                             (real_plus (real_mult (nat_real (N - M)) v) v)).
      { rewrite Hsub.
        apply (real_eq_trans _ (real_mult (real_plus (nat_real (N - M)) real_one) v)).
        - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (nat_real_S (N - M)) (real_eq_refl _)).
        - apply (real_eq_trans _ (real_plus (real_mult (nat_real (N - M)) v)
                                            (real_mult real_one v))).
          + apply (r_mult_plus_distr (nat_real (N - M)) real_one v).
          + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) (real_mult_one_l v)). }
      apply (real_le_trans _ (real_plus (real_mult (nat_real (N - M)) v) v)).
      * apply real_le_plus_compat.
         -- apply IH; [exact HMN |].
            intros j Hj Hj1 Hj2. apply Hbnd; [exact Hj1 |].
            apply NatLe_lift. apply NatLe_drop in Hj2. lia.
        -- apply Hbnd; [apply NatLe_lift; exact HLtb | apply NatLe_lift; apply Nat.le_refl].
      * apply r_le_of_eq. apply (real_eq_sym _ _). exact HRHS.
    + assert (Hge : (S N <= M)%nat) by (apply Nat.ltb_ge; exact HLtb).
      assert (HMeq : M = S N)
        by (apply Nat.le_antisymm; [apply NatLe_drop; exact Hle | exact Hge]).
      subst M. apply r_le_of_eq. apply (real_eq_trans _ real_zero).
      * apply (real_eq_trans _ (r_tsum (S N) N)).
        -- apply (r_plus_zero_r_gen (r_tsum (S N) N)).
        -- apply r_tsum_zero_le. apply NatLe_lift. apply Nat.le_succ_diag_r.
      * replace (S N - S N)%nat with 0%nat by lia.
        destruct v as [uv Hv]. apply real_eq_of_zero_diff. intro k. simpl. ring.
Qed.

(* Count face: nat_real n * r_npow n = n^{1-sigma}. *)
Lemma r_two_npow_prod : forall (n : nat) (Hn : NatLe 1 n),
  real_eq (real_mult (nat_real n) (r_npow n Hn))
          (cauchy_real_exp (real_mult (real_opp r_sub1) (r_ln n Hn))).
Proof.
  intros n Hn. unfold r_npow, r_ln, r_sub1.
  apply (real_eq_trans _
    (real_mult (cauchy_real_exp (real_log (nat_real n) (Hnpos n Hn)))
               (cauchy_real_exp (real_mult (real_opp sig) (real_log (nat_real n) (Hnpos n Hn)))))).
  - apply (RealSetoid.real_eq_mult_compat _ _ _ _
             (real_eq_sym _ _ (cw_log_exp_right (nat_real n) (Hnpos n Hn))) (real_eq_refl _)).
  - apply (real_eq_trans _ (cauchy_real_exp (real_plus (real_log (nat_real n) (Hnpos n Hn))
               (real_mult (real_opp sig) (real_log (nat_real n) (Hnpos n Hn)))))).
    + apply (real_eq_sym _ _). apply cauchy_real_exp_plus.
    + apply cauchy_real_exp_wd.
      apply (r_affine_fold (real_log (nat_real n) (Hnpos n Hn)) sig).
Qed.

(* log additivity on the embedded naturals (real_log_mult, witness-matched
   via leaf-a real_log_wd over nat_real_mul). *)
Lemma r_ln_mul : forall (a b : nat) (Ha : NatLe 1 a) (Hb : NatLe 1 b) (Hab : NatLe 1 (a * b)),
  real_eq (r_ln (a * b) Hab) (real_plus (r_ln a Ha) (r_ln b Hb)).
Proof.
  intros a b Ha Hb Hab. unfold r_ln.
  apply (real_eq_trans _
    (real_log (real_mult (nat_real a) (nat_real b))
              (real_mult_positive (nat_real a) (nat_real b) (Hnpos a Ha) (Hnpos b Hb)))).
  - apply (real_log_wd (nat_real (a * b))). apply nat_real_mul.
  - exact (real_log_mult (nat_real a) (nat_real b) (Hnpos a Ha) (Hnpos b Hb)).
Qed.

Lemma r_ln_pow2 : forall k : nat,
  real_eq (r_ln (Nat.pow 2 k) (r_pow2_ge1 k))
          (real_mult (nat_real k) (r_ln 2 (NatLe_one_S 1))).
Proof.
  intro k. induction k as [|k IH].
  - cbn [Nat.pow]. apply (real_eq_trans _ real_zero).
    + apply (real_eq_trans _ (real_log real_one (real_lt_zero_one))).
      * apply (real_log_wd (nat_real 1) real_one). apply nat_real_one.
      * apply (real_log_one real_lt_zero_one).
    + apply (real_eq_sym _ _). apply r_zero_scale_l.
  - cbn [Nat.pow]. apply (real_eq_trans _
      (real_plus (r_ln 2 (NatLe_one_S 1)) (r_ln (Nat.pow 2 k) (r_pow2_ge1 k)))).
    + apply (r_ln_mul 2 (Nat.pow 2 k) (NatLe_one_S 1) (r_pow2_ge1 k) (r_pow2_ge1 (S k))).
    + apply (real_eq_trans _ (real_plus (r_ln 2 (NatLe_one_S 1))
                 (real_mult (nat_real k) (r_ln 2 (NatLe_one_S 1))))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) IH).
      * apply (real_eq_trans _ (real_mult (real_plus (nat_real k) real_one)
                 (r_ln 2 (NatLe_one_S 1)))).
        -- exact (r_succ_scale (nat_real k) (r_ln 2 (NatLe_one_S 1))).
        -- exact (real_eq_sym _ _
              (RealSetoid.real_eq_mult_compat (nat_real (S k))
                (r_ln 2 (NatLe_one_S 1)) (real_plus (nat_real k) real_one)
                (r_ln 2 (NatLe_one_S 1)) (nat_real_S k) (real_eq_refl _))).
Qed.

Definition r_two_block (k : nat) : Real :=
  cauchy_real_exp (real_mult (real_opp r_sub1) (r_ln (Nat.pow 2 k) (r_pow2_ge1 k))).

(* Anchored block bound (leaf-b version, absolute anchors 2^k): the block
   tail is at most the block value (2^k)^{1-sigma}. *)
Lemma q_condensation_block : forall k : nat,
  real_le (r_tail (Nat.pow 2 k) (Nat.pow 2 (S k))) (r_two_block k).
Proof.
  intro k.
  assert (Hcnt : (Nat.pow 2 (S k) - Nat.pow 2 k)%nat = Nat.pow 2 k) by (cbn [Nat.pow]; lia).
  assert (Hmain : real_le (r_tsum (Nat.pow 2 k) (Nat.pow 2 (S k)))
                          (real_mult (nat_real (Nat.pow 2 (S k) - Nat.pow 2 k))
                                     (r_npow (Nat.pow 2 k) (r_pow2_ge1 k)))).
  { apply r_tsum_le_const.
    - apply NatLe_lift. cbn [Nat.pow]. lia.
    - intros j Hj Hj1 Hj2. apply (r_npow_anti (Nat.pow 2 k) j (r_pow2_ge1 k) Hj).
      apply NatLe_lift. apply NatLe_drop in Hj1. lia. }
  rewrite Hcnt in Hmain.
  apply (RealSetoid.real_le_compat _ _ _ _
           (r_tsum_r_tail (Nat.pow 2 k) (Nat.pow 2 (S k)))
           (r_two_npow_prod (Nat.pow 2 k) (r_pow2_ge1 k))).
  exact Hmain.
Qed.

(* The ratio constant 2^(1-sigma) lies strictly between 0 and 1. *)
Definition r_q1 : Real :=
  cauchy_real_exp (real_mult (real_opp r_sub1) (r_ln 2 (NatLe_one_S 1))).

Lemma r_q1_pos : real_lt real_zero r_q1.
Proof. unfold r_q1. apply cauchy_real_exp_pos. Qed.

Lemma r_q1_lt_one : real_lt r_q1 real_one.
Proof.
  unfold r_q1.
  assert (Hprod : real_lt real_zero (real_mult r_sub1 (r_ln 2 (NatLe_one_S 1))))
    by (apply real_mult_positive; [exact r_sub1_pos | exact Hln2pos]).
  assert (Harg0 : real_lt (real_mult (real_opp r_sub1) (r_ln 2 (NatLe_one_S 1))) real_zero).
  { apply (RealSetoid.real_lt_compat _ _ real_zero real_zero
             (real_eq_sym _ _ (r_mult_opp_l r_sub1 (r_ln 2 (NatLe_one_S 1))))
             (real_eq_refl real_zero)).
    apply real_lt_zero_opp. exact Hprod. }
  apply (RealSetoid.real_lt_compat
           (cauchy_real_exp (real_mult (real_opp r_sub1) (r_ln 2 (NatLe_one_S 1))))
           (cauchy_real_exp (real_mult (real_opp r_sub1) (r_ln 2 (NatLe_one_S 1))))
           (cauchy_real_exp real_zero) real_one).
  - apply real_eq_refl.
  - apply cauchy_real_exp_zero.
  - apply cauchy_real_exp_mono. exact Harg0.
Qed.

(* r_q1^k == exp(-(sigma-1) * k * ln 2). *)
Lemma r_q1_qpow : forall k : nat,
  real_eq (r_qpow r_q1 k)
          (cauchy_real_exp (real_mult (real_opp r_sub1)
                              (real_mult (nat_real k) (r_ln 2 (NatLe_one_S 1))))).
Proof.
  intro k. induction k as [|k IH].
  - cbn [r_qpow]. apply (real_eq_sym _ _).
    apply (real_eq_trans _ (cauchy_real_exp real_zero)).
    + apply cauchy_real_exp_wd.
      exact (r_zero_scale_r (real_opp r_sub1) (r_ln 2 (NatLe_one_S 1))).
    + apply cauchy_real_exp_zero.
  - cbn [r_qpow]. apply (real_eq_trans _
      (real_mult (cauchy_real_exp (real_mult (real_opp r_sub1)
                        (real_mult (nat_real k) (r_ln 2 (NatLe_one_S 1)))))
                 (cauchy_real_exp (real_mult (real_opp r_sub1)
                        (r_ln 2 (NatLe_one_S 1)))))).
    + apply (RealSetoid.real_eq_mult_compat _ _ _ _ IH (real_eq_refl _)).
    + apply (real_eq_trans _
        (cauchy_real_exp (real_plus (real_mult (real_opp r_sub1)
                          (real_mult (nat_real k) (r_ln 2 (NatLe_one_S 1))))
                        (real_mult (real_opp r_sub1)
                          (r_ln 2 (NatLe_one_S 1)))))).
      * apply (real_eq_sym _ _). apply cauchy_real_exp_plus.
      * apply (real_eq_trans _ (cauchy_real_exp (real_mult (real_opp r_sub1)
                (real_mult (real_plus (nat_real k) real_one) (r_ln 2 (NatLe_one_S 1)))))).
        -- apply cauchy_real_exp_wd.
           exact (r_succ_scale_gen (real_opp r_sub1) (nat_real k) (r_ln 2 (NatLe_one_S 1))).
        -- apply cauchy_real_exp_wd.
           apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)).
           apply (RealSetoid.real_eq_mult_compat _ _ _ _
                    (real_eq_sym _ _ (nat_real_S k)) (real_eq_refl _)).
Qed.

End AbsConvTailBound.
