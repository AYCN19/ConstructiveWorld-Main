(** * GaC2_06_AltMonoFace: the monotone modulus face of the alternating block.

    Mission.  Node C2-06 (segment C2, slot W1).  The real modulus of the
    alternating Dirichlet block: the n^{-sigma} term slice [r_npow] of
    the Dirichlet term carrier [c_powq] (C2.01), its sigma-zero slice
    [r_npow0] (consumption alias [r_npow_at] for the C2.07 consumer),
    and the four statements the alternating test consumes:
    antitonicity ([r_npow_anti]), domination by the sigma-zero slice
    ([r_npow_tozero]), the explicit sigT convergence modulus
    ([r_npow0_tendsto], witness M0 = 2, modulus 2^{-sigma0}), and the
    step-difference nonnegativity ([r_npow_diff_nonneg]).

    Dependencies.  [S01_BaseRing] (selective [NatLe] import), [S02]
    (order kit), [S03_QExp] ([cauchy_real_exp]),
    [S07_RealSetoidExpLog] ([cauchy_real_exp_mono],
    [real_le_mult_compat_weak], [real_le_mult_compat],
    [real_opp_le_compat], [real_lt_mult_compat], [real_log_one]),
    [CxRealPairCore] + [CxRealPairExpLog] (pair carrier), [GaC1_Iface_Real]
    (C1-01 log monotonicity [gaC1_01_log_le_mono] / [gaC1_01_log_lt_mono]),
    [GaC2_01_DirichletPartialSum] ([c_powq], [c_of_real], [nat_real],
    [NatLe_one_S]), [GaC2_02_AbsConvTailBound_a] ([r_mult_opp_l],
    [r_assoc_scale], [c_exp_real], [nat_real_lt], [real_log_wd]);
    Stdlib [Arith] and [Lia] (nat bookkeeping only).

    References.  F8 RiemZeta.lean [summable_riemannZetaSummand] and F3
    Convergence.lean (statement shapes only); the mathlib Real.rpow
    monotone chain re-assembled from the C1-01 log monotone output
    and the S07 exp monotone; drafts_C2.md C2.06 skeleton with three
    adaptations: (i) the positivity premise is NatLe-1-parametrised,
    [forall n, NatLe 1 n -> 0 < nat_real n] (unusable at n = 0; the
    C2.01 rework ruling); (ii) nat bounds are Set-sorted [NatLe];
    (iii) [r_npow0_tendsto] fixes the free modulus eps0 to
    2^{-sigma0}, witness M0 = 2.  The bridge [mn_slice_exp_gen]
    transcribes the C2.02 leaf chain [r_npow_slice] slice-first.
    A second retrieval pass finds no same-route formalization of the
    eta continuation (mathlib: theta/Poisson; Isabelle: Hurwitz zeta
    plus Bernoulli/Euler-Maclaurin; this line: eta over (1 - 2^(1-s)),
    the Z03 supply face).

    Constructivity.  Every named construction is carried by [Set]; the
    order predicates are the Set-sorted [real_le] / [real_lt]; zero
    assumed constants, zero abandoned proofs, zero classical choice;
    every proof closes under the global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC2_06_AltMonoFace.v] from the work directory, thermal guard wrapper. *)

Require S01_BaseRing.
(* Selective import: only the Set-sorted nat bound face is consumed;   *)
(* a full import would shadow the nat constructor S (C2.01 precedent). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Real.
Require Import GaC2_01_DirichletPartialSum.
Require Import GaC2_02_AbsConvTailBound_a.
From Stdlib Require Import Arith.Arith Lia.

(* Weak monotonicity of the exponential: the strict face of S07 plus   *)
(* the equality branch through the congruence of the exponential.      *)
Lemma mn_exp_le : forall x y : Real,
  real_le x y -> real_le (cauchy_real_exp x) (cauchy_real_exp y).
Proof.
  intros x y Hxy. destruct Hxy as [Hlt | Heq].
  - left. exact (cauchy_real_exp_mono x y Hlt).
  - apply r_le_of_eq. exact (cauchy_real_exp_wd x y Heq).
Qed.

Section AltMonoFace.

Variable sig sig0 : Real.
Hypothesis Hs0 : real_lt real_zero sig0.
Hypothesis Hs : real_le sig0 sig.
Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).

(* The n^{-sigma} term slice of the C2.01 carrier and its sigma-zero   *)
(* slice; [r_npow_at] is the registered C2.07 consumption alias.       *)
Definition r_npow (n : nat) (Hn : NatLe 1 n) : Real :=
  cRe (c_powq Hnpos n Hn (c_of_real sig)).
Definition r_npow0 (n : nat) (Hn : NatLe 1 n) : Real :=
  cRe (c_powq Hnpos n Hn (c_of_real sig0)).
Definition r_npow_at (n : nat) (Hn : NatLe 1 n) : Real := r_npow0 n Hn.

(* The sigma position is positive: the strict floor sig0 > 0 lifts     *)
(* along the weak floor sig0 <= sig. *)
Lemma mn_sig_pos : real_lt real_zero sig.
Proof. exact (real_lt_le_trans real_zero sig0 sig Hs0 Hs). Qed.

(* The embedded naturals are order-faithful in the weak sense: the     *)
(* equal case is the reflexive branch, the strict case the leaf bridge.*)
Lemma mn_natreal_le : forall (m n : nat),
  NatLe m n -> real_le (nat_real m) (nat_real n).
Proof.
  intros m n Hmn. destruct (Nat.eq_dec m n) as [Heq | Hne].
  - subst m. apply r_le_of_eq. apply real_eq_refl.
  - assert (Hlt : (m < n)%nat).
    { assert (Hle : (m <= n)%nat) by (apply NatLe_drop; exact Hmn).
      lia. }
    apply real_lt_le_iff. left.
    exact (nat_real_lt m n (NatLe_lift (S m) n Hlt)).
Qed.

(* The real log is nonnegative on the embedded naturals: ln 1 == 0     *)
(* and the log chain lifts the order 1 <= n. *)
Lemma mn_log_nonneg : forall (n : nat) (Hn : NatLe 1 n),
  real_le real_zero (real_log (nat_real n) (Hnpos n Hn)).
Proof.
  intros n Hn.
  apply (real_le_trans real_zero (real_log real_one real_lt_zero_one)
           (real_log (nat_real n) (Hnpos n Hn))).
  - apply r_le_of_eq. apply (real_eq_sym _ _).
    exact (real_log_one real_lt_zero_one).
  - exact (gaC1_01_log_le_mono real_one (nat_real n) real_lt_zero_one
             (Hnpos n Hn) (mn_natreal_le 1 n Hn)).
Qed.

(* The exp-form bridge of the term slice: n^{-sg} as exp(-sg * ln n).  *)
(* Chain: the scaled real product folds into the real axis, the real   *)
(* axis exponential unfolds, and the (-1, sg, ln n) association closes.*)
Lemma mn_slice_exp_gen : forall (sg : Real) (n : nat) (Hn : NatLe 1 n),
  real_eq (cRe (c_powq Hnpos n Hn (c_of_real sg)))
          (cauchy_real_exp (real_mult (real_opp sg)
             (real_log (nat_real n) (Hnpos n Hn)))).
Proof.
  intros sg n Hn. unfold c_powq.
  apply (real_eq_trans _
    (cRe (c_exp (c_of_real (real_mult (real_opp real_one)
              (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))))))).
  - apply cRe_wd. apply c_exp_wd.
    apply (c_eq_trans _ (c_scale (real_opp real_one)
              (c_of_real (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))))).
    + apply c_scale_wd.
      exact (c_of_real_mult_gen sg (real_log (nat_real n) (Hnpos n Hn))).
    + exact (c_of_real_scale_gen (real_opp real_one)
              (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))).
  - apply (real_eq_trans _
      (cauchy_real_exp (real_mult (real_opp real_one)
             (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))))).
    + exact (cRe_wd _ _ (c_exp_real (real_mult (real_opp real_one)
             (real_mult sg (real_log (nat_real n) (Hnpos n Hn)))))).
    + apply cauchy_real_exp_wd.
      exact (r_assoc_scale sg (real_log (nat_real n) (Hnpos n Hn))).
Qed.

Lemma mn_slice_exp : forall (n : nat) (Hn : NatLe 1 n),
  real_eq (r_npow n Hn)
          (cauchy_real_exp (real_mult (real_opp sig)
             (real_log (nat_real n) (Hnpos n Hn)))).
Proof. intros n Hn. exact (mn_slice_exp_gen sig n Hn). Qed.

Lemma mn_slice_exp0 : forall (n : nat) (Hn : NatLe 1 n),
  real_eq (r_npow0 n Hn)
          (cauchy_real_exp (real_mult (real_opp sig0)
             (real_log (nat_real n) (Hnpos n Hn)))).
Proof. intros n Hn. exact (mn_slice_exp_gen sig0 n Hn). Qed.

(* The slice is insensitive to the witness of the positivity premise. *)
Lemma mn_rnpow_irrel : forall (n : nat) (Hn Hn' : NatLe 1 n),
  real_eq (r_npow n Hn) (r_npow n Hn').
Proof.
  intros n Hn Hn'. unfold r_npow, c_powq.
  apply cRe_wd. apply c_exp_wd. apply c_scale_wd. apply c_mult_congr.
  - apply c_eq_refl.
  - apply c_of_real_wd.
    exact (real_log_wd (nat_real n) (nat_real n) (Hnpos n Hn) (Hnpos n Hn')
             (real_eq_refl _)).
Qed.

(* (a) Antitonicity: m <= n gives n^{-sigma} <= m^{-sigma}.  Chain:    *)
(* the log chain lifts m <= n, negation flips it, the strict product   *)
(* law with sigma > 0 closes, and the exp antitone branch transfers.   *)
Lemma r_npow_anti : forall (m n : nat) (Hm : NatLe 1 m) (Hn : NatLe 1 n),
  NatLe m n -> real_le (r_npow n Hn) (r_npow m Hm).
Proof.
  intros m n Hm Hn Hmn. destruct (Nat.eq_dec m n) as [Heq | Hne].
  - subst m. apply r_le_of_eq. exact (mn_rnpow_irrel n Hn Hm).
  - assert (Hlt : (m < n)%nat).
    { assert (Hle : (m <= n)%nat) by (apply NatLe_drop; exact Hmn).
      lia. }
    assert (Hloglt : real_lt (real_log (nat_real m) (Hnpos m Hm))
                             (real_log (nat_real n) (Hnpos n Hn)))
      by (exact (gaC1_01_log_lt_mono (nat_real m) (nat_real n) (Hnpos m Hm)
                   (Hnpos n Hn)
                   (nat_real_lt m n (NatLe_lift (S m) n Hlt)))).
    assert (Hscale : real_lt (real_mult sig (real_log (nat_real m) (Hnpos m Hm)))
                             (real_mult sig (real_log (nat_real n) (Hnpos n Hn))))
      by (exact (real_lt_mult_compat _ _ _ mn_sig_pos Hloglt)).
    assert (Hflip : real_lt
             (real_mult (real_opp sig) (real_log (nat_real n) (Hnpos n Hn)))
             (real_mult (real_opp sig) (real_log (nat_real m) (Hnpos m Hm)))).
    { exact (RealSetoid.real_lt_compat
               (real_opp (real_mult sig (real_log (nat_real n) (Hnpos n Hn))))
               (real_mult (real_opp sig) (real_log (nat_real n) (Hnpos n Hn)))
               (real_opp (real_mult sig (real_log (nat_real m) (Hnpos m Hm))))
               (real_mult (real_opp sig) (real_log (nat_real m) (Hnpos m Hm)))
               (real_eq_sym _ _
                  (r_mult_opp_l sig (real_log (nat_real n) (Hnpos n Hn))))
               (real_eq_sym _ _
                  (r_mult_opp_l sig (real_log (nat_real m) (Hnpos m Hm))))
               (r_lt_opp_flip _ _ Hscale)). }
    apply real_lt_le_iff. left.
    exact (real_eq_lt_lt _ _ _ (mn_slice_exp n Hn)
             (real_lt_eq_lt _ _ _ (cauchy_real_exp_mono _ _ Hflip)
                (real_eq_sym _ _ (mn_slice_exp m Hm)))).
Qed.

(* (b) Domination: sigma >= sig0 > 0 gives n^{-sigma} <= n^{-sigma0}.  *)
(* Chain: sig0 * ln n <= sig * ln n by the weak product law with       *)
(* ln n >= 0, negation flips it, the weak exp branch transfers.        *)
Lemma r_npow_tozero : forall (n : nat) (Hn : NatLe 1 n),
  real_le (r_npow n Hn) (r_npow0 n Hn).
Proof.
  intros n Hn.
  assert (Hcore : real_le
           (real_mult (real_opp sig) (real_log (nat_real n) (Hnpos n Hn)))
           (real_mult (real_opp sig0) (real_log (nat_real n) (Hnpos n Hn)))).
  { apply (real_le_trans _
             (real_opp (real_mult sig (real_log (nat_real n) (Hnpos n Hn))))).
    - apply r_le_of_eq.
      exact (r_mult_opp_l sig (real_log (nat_real n) (Hnpos n Hn))).
    - apply (real_le_trans _
               (real_opp (real_mult sig0 (real_log (nat_real n) (Hnpos n Hn))))).
      + exact (real_opp_le_compat
                 (real_mult sig0 (real_log (nat_real n) (Hnpos n Hn)))
                 (real_mult sig (real_log (nat_real n) (Hnpos n Hn)))
                 (real_le_mult_compat_weak sig0 sig
                    (real_log (nat_real n) (Hnpos n Hn))
                    (mn_log_nonneg n Hn) Hs)).
      + apply r_le_of_eq. apply (real_eq_sym _ _).
        exact (r_mult_opp_l sig0 (real_log (nat_real n) (Hnpos n Hn))). }
  apply (real_le_trans _
           (cauchy_real_exp
              (real_mult (real_opp sig) (real_log (nat_real n) (Hnpos n Hn))))).
  - apply r_le_of_eq. exact (mn_slice_exp n Hn).
  - apply (real_le_trans _
             (cauchy_real_exp
                (real_mult (real_opp sig0) (real_log (nat_real n) (Hnpos n Hn))))).
    + exact (mn_exp_le _ _ Hcore).
    + apply r_le_of_eq. apply (real_eq_sym _ _). exact (mn_slice_exp0 n Hn).
Qed.

(* (c) The explicit convergence modulus of the sigma-zero slice: from  *)
(* M0 = 2 on, n^{-sigma0} <= 2^{-sigma0} (equality included, so the    *)
(* chain is the weak one: log chain at 2 <= n, the strict product law  *)
(* with sig0 > 0, negation flips, the weak exp branch transfers down). *)
Lemma r_npow0_tendsto :
  { M0 : nat & forall (n : nat) (H1 : NatLe 1 n), NatLe M0 n ->
      real_le (r_npow0 n H1) (r_npow0 2 (NatLe_one_S 1)) }.
Proof.
  exists 2. intros n H1 Hge.
  assert (Hlogle : real_le (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))
                           (real_log (nat_real n) (Hnpos n H1)))
    by (exact (gaC1_01_log_le_mono (nat_real 2) (nat_real n)
                 (Hnpos 2 (NatLe_one_S 1)) (Hnpos n H1)
                 (mn_natreal_le 2 n Hge))).
  assert (Hscale : real_le
             (real_mult sig0 (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1))))
             (real_mult sig0 (real_log (nat_real n) (Hnpos n H1)))).
  { apply (real_le_trans _ (real_mult (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1))) sig0)).
    - apply r_le_of_eq. apply real_mult_comm.
    - apply (real_le_trans _ (real_mult (real_log (nat_real n) (Hnpos n H1)) sig0)).
      + exact (real_le_mult_compat _ _ _ Hs0 Hlogle).
      + apply r_le_of_eq. apply real_mult_comm. }
  assert (Hcore : real_le
           (real_mult (real_opp sig0) (real_log (nat_real n) (Hnpos n H1)))
           (real_mult (real_opp sig0) (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1))))).
  { apply (real_le_trans _
             (real_opp (real_mult sig0 (real_log (nat_real n) (Hnpos n H1))))).
    - apply r_le_of_eq.
      exact (r_mult_opp_l sig0 (real_log (nat_real n) (Hnpos n H1))).
    - apply (real_le_trans _
               (real_opp (real_mult sig0 (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))))).
      + exact (real_opp_le_compat
                 (real_mult sig0 (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1))))
                 (real_mult sig0 (real_log (nat_real n) (Hnpos n H1))) Hscale).
      + apply r_le_of_eq. apply (real_eq_sym _ _).
        exact (r_mult_opp_l sig0 (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))). }
  apply (real_le_trans _
           (cauchy_real_exp
              (real_mult (real_opp sig0) (real_log (nat_real n) (Hnpos n H1))))).
  - apply r_le_of_eq. exact (mn_slice_exp0 n H1).
  - apply (real_le_trans _
             (cauchy_real_exp
                (real_mult (real_opp sig0) (real_log (nat_real 2) (Hnpos 2 (NatLe_one_S 1)))))).
    + exact (mn_exp_le _ _ Hcore).
    + apply r_le_of_eq. apply (real_eq_sym _ _).
      exact (mn_slice_exp0 2 (NatLe_one_S 1)).
Qed.

(* (d) The step difference is nonnegative: n^{-sigma} - (n+1)^{-sigma} *)
(* >= 0.  Strict case: the antitone face moves through the difference  *)
(* shift; equal case: the difference collapses onto x - x == 0.        *)
Lemma r_npow_diff_nonneg : forall (n : nat) (Hn : NatLe 1 n),
  real_le real_zero
    (real_plus (r_npow n Hn) (real_opp (r_npow (S n) (NatLe_one_S n)))).
Proof.
  intros n Hn.
  destruct (r_npow_anti n (S n) Hn (NatLe_one_S n)
              (NatLe_lift n (S n) (Nat.le_succ_diag_r n))) as [Hlt | Heq].
  - apply real_lt_le_iff. left.
    exact (real_lt_opp_plus (r_npow (S n) (NatLe_one_S n)) (r_npow n Hn) Hlt).
  - apply r_le_of_eq.
    apply (real_eq_trans real_zero
             (real_plus (r_npow (S n) (NatLe_one_S n))
                        (real_opp (r_npow (S n) (NatLe_one_S n))))
             (real_plus (r_npow n Hn) (real_opp (r_npow (S n) (NatLe_one_S n))))).
    + apply (real_eq_sym _ _).
      exact (real_plus_opp (r_npow (S n) (NatLe_one_S n))).
    + apply RealSetoid.real_eq_plus_compat.
      * exact Heq.
      * apply real_eq_refl.
Qed.

End AltMonoFace.
