(* ConstructiveWorld-Main - the absolute-convergence tail machinery for the
   zeta series in the half-plane Re s > 1. *)
(** * GaC2_02_AbsConvTailBound: absolute-convergence tail bounds.
    Mission.  The three named main lemmas of the absolute-convergence
      tail machinery for Re s = sigma > 1, consumed segment-wide
      (C2.04/C2.05/C2.08): (a) [condensation_tail_bound] :
      sum_{M<n<=N} n^{-sigma} < M^{1-sigma} * (1 + 2^{1-sigma}/(1 -
      2^{1-sigma})) (strict; the slack is the geometric remainder
      q^K > 0); (b) [zeta_part_cauchy_bound] :
      |zeta_N(s) - zeta_M(s)|^2 < [bound]^2 + d for every rational
      margin d > 0 (the GaC1_14 rational-margin carrier; cRe s = sigma;
      via the C2.01 tail-difference identity); (c)
      [tail_bound_uniform] : for 1 < sigma0 <= sigma the bound with
      sigma0 substituted holds uniformly (monotone transfer on both
      factors).
    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [Arith.Arith], [Lia].  Requires [S01_BaseRing] (selective
      [NatLe] import), [S02_CauchyComplete], [S03_QExp],
      [S07_RealSetoidExpLog], [S10_KVQuantTrig], [CxRealPairCore],
      [CxRealPairExpLog], [GaC2_01_DirichletPartialSum], and leaves
      [GaC2_02_AbsConvTailBound_a]/[_b]/[_c] of this development;
      zero Export (consumers Require this stem, and leaf _c for the
      discharged forms of [r_two_rpow]/[r_geom_den]/[r_geom_const]).
    References.  Card C2.02, blueprint drafts_C2.md C2.02 draft-2.
      Statement provenance: the node is leaf-split, stem (this file:
      the three main lemmas plus the L-C2.02-C slot) / leaf _a
      (Section-free base) / leaf _b (sectioned term/tail core, Hnpos
      premise form, [NatLe] unification) / leaf _c (condensation
      engine plus the three blueprint Definitions); tree precedent
      piu_zz_tau_segtree_1024_leaf_a..h + _merge.  DAG:
      a <- b <- c <- stem.
    Constructivity.  Red path A: all statements Set-sorted
      ([real_lt]/[real_le] Set sums, [real_eq], [NatLe], [QltT]);
      every proof closes under the global context; [coqchk] reports
      zero assumed constants.  GAPASUME slots (Section hypotheses,
      discharged at [End]): L-C2.02-A [Hlnmono], L-C2.02-B [Hln2pos]
      (L0-stock instantiable), and the new L-C2.02-C [Hnormtri], the
      complex n-fold triangle inequality in rational-margin form for
      the blocked Dirichlet tail.  [Hnormtri] is NOT L0 stock
      ([gaC1_14_norm_sq_pair_lt] is the 2-fold margin form only; no
      [real_abs] / n-fold Cauchy-Schwarz face in the tree, grep record
      in the cert file); supply route = C1.4 convergence-engine
      extension (pointwise Lagrange identity, GaC1_14 style), carried
      honestly as an open supply face; (b) consumes it.
    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC2_02_AbsConvTailBound.v] compiles cleanly
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
Require Import GaC2_02_AbsConvTailBound_c.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Section AbsConvMain.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable sig : Real.
Hypothesis Hsig1 : real_lt real_one sig.
(* GAPASUME slot L-C2.02-A (L0 stock: real_log_lt_mono S07:6540). *)
Hypothesis Hlnmono :
  forall (m n : nat) (Hm : real_lt real_zero (nat_real m)) (Hn : real_lt real_zero (nat_real n)),
    real_lt (nat_real m) (nat_real n) ->
    real_lt (real_log (nat_real m) Hm) (real_log (nat_real n) Hn).
(* GAPASUME slot L-C2.02-B (L0 stock: real_log_lt_mono + real_log_one + real_log_wd). *)
Hypothesis Hln2pos : real_lt real_zero (r_ln Hnpos 2 (NatLe_one_S 1)).

(* (a) Condensation tail bound, card C2.02 (a) closed form, strict. *)
Lemma condensation_tail_bound : forall (M N : nat) (HM : NatLe 1 M) (HMN : NatLe M N),
  real_lt (r_tail Hnpos sig M N)
          (real_mult (r_m1sig Hnpos sig M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos)).
Proof.
  intros M N HM HMN.
  destruct (nat_dyadic_cover M N HM) as [K HK].
  apply (real_le_lt_trans _ (r_tail Hnpos sig M (M * Nat.pow 2 K))).
  { exact (r_tail_mono Hnpos sig M N (M * Nat.pow 2 K) HMN HK). }
  apply (real_le_lt_trans _ (real_mult (r_m1sig Hnpos sig M HM) (r_gsum (r_q1 Hnpos sig) K))).
  { exact (r_tail_dyadic Hnpos sig Hsig1 Hlnmono M HM K). }
  apply (real_lt_mult_compat _ _ _ (r_m1sig_pos Hnpos sig M HM)).
  exact (r_gsum_lt_geom Hnpos sig Hsig1 Hln2pos K).
Qed.

(* GAPASUME slot L-C2.02-C: complex n-fold triangle in rational-margin form
   on the blocked Dirichlet tail (not L0 stock; see header and cert file). *)
Hypothesis Hnormtri :
  forall (M N : nat) (s : Cx) (d : Q), real_eq (cRe s) sig -> QltT 0 d ->
    real_lt (c_norm_sq (c_tail Hnpos M N s))
            (real_plus (real_mult (r_tsum Hnpos sig M N) (r_tsum Hnpos sig M N)) (real_const d)).

(* (b) Cauchy witness for the partial sums zeta_N(s), cRe s = sigma. *)
Lemma zeta_part_cauchy_bound : forall (M N : nat) (HM : NatLe 1 M) (HMN : NatLe M N) (s : Cx),
    real_eq (cRe s) sig -> forall d : Q, QltT 0 d ->
  real_lt (c_norm_sq (c_plus (c_zeta_part Hnpos N s) (c_opp (c_zeta_part Hnpos M s))))
          (real_plus (real_mult
                        (real_mult (r_m1sig Hnpos sig M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos))
                        (real_mult (r_m1sig Hnpos sig M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos)))
                     (real_const d)).
Proof.
  intros M N HM HMN s Hs d Hd.
  set (B := real_mult (r_m1sig Hnpos sig M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos)).
  set (T := r_tsum Hnpos sig M N).
  apply (real_eq_lt_lt _ (c_norm_sq (c_tail Hnpos M N s))).
  { apply c_norm_sq_wd. exact (c_zeta_part_tail_eq Hnpos M N s HMN). }
  apply (real_lt_le_trans _ (real_plus (real_mult T T) (real_const d))).
  { exact (Hnormtri M N s d Hs Hd). }
  apply real_le_plus_compat; [| apply real_le_refl].
  assert (HTB : real_lt T B).
  { apply (real_eq_lt_lt _ (r_tail Hnpos sig M N) _ (r_tsum_r_tail Hnpos sig M N)).
    exact (condensation_tail_bound M N HM HMN). }
  assert (HT0 : real_le real_zero T) by exact (r_tsum_ge0 Hnpos sig M N).
  assert (HB0 : real_lt real_zero B).
  { apply real_mult_positive.
    - exact (r_m1sig_pos Hnpos sig M HM).
    - exact (r_geom_const_pos Hnpos sig Hsig1 Hln2pos). }
  assert (HTBle : real_le T B) by (apply (real_lt_le_iff T B); left; exact HTB).
  apply (real_le_trans _ (real_mult B T)).
  - exact (real_le_mult_compat_weak T B T HT0 HTBle).
  - apply (RealSetoid.real_le_compat (real_mult T B) (real_mult B T) (real_mult B B) (real_mult B B)
             (real_mult_comm T B) (real_eq_refl _)).
    exact (real_le_mult_compat T B B HB0 HTBle).
Qed.

(* (c) Uniform form: for 1 < sigma0 <= sigma the bound with sigma0 substituted. *)
Lemma tail_bound_uniform : forall (sig0 : Real) (Hs01 : real_lt real_one sig0)
    (Hs0s : real_le sig0 sig) (M N : nat) (HM : NatLe 1 M) (HMN : NatLe M N),
  real_lt (r_tail Hnpos sig M N)
          (real_mult (r_m1sig Hnpos sig0 M HM) (r_geom_const Hnpos sig0 Hs01 Hln2pos)).
Proof.
  intros sig0 Hs01 Hs0s M N HM HMN.
  apply (real_lt_le_trans _
    (real_mult (r_m1sig Hnpos sig M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos))).
  { exact (condensation_tail_bound M N HM HMN). }
  set (Lm := r_ln Hnpos M HM). set (L2 := r_ln Hnpos 2 (NatLe_one_S 1)).
  set (q := r_two_rpow Hnpos (real_plus real_one (real_opp sig))).
  set (q0 := r_two_rpow Hnpos (real_plus real_one (real_opp sig0))).
  set (inv := c_inv_wit (r_geom_den Hnpos sig) (r_geom_den_pos Hnpos sig Hsig1 Hln2pos)).
  set (inv0 := c_inv_wit (r_geom_den Hnpos sig0) (r_geom_den_pos Hnpos sig0 Hs01 Hln2pos)).
  assert (HLm0 : real_le real_zero Lm) by exact (r_ln_nonneg Hnpos M HM).
  assert (HL20 : real_le real_zero L2) by (apply (real_lt_le_iff _ _); left; exact Hln2pos).
  assert (Hsub : real_le (real_plus real_one (real_opp sig)) (real_plus real_one (real_opp sig0)))
    by (apply r_one_minus_le; exact Hs0s).
  (* M^{1-sigma} <= M^{1-sigma0} *)
  assert (Hm1 : real_le (r_m1sig Hnpos sig M HM) (r_m1sig Hnpos sig0 M HM)).
  { unfold r_m1sig. apply r_exp_le_mono.
    apply (RealSetoid.real_le_compat (real_mult (real_plus real_one (real_opp sig)) Lm)
             (real_mult (real_opp (r_sub1 sig)) Lm)
             (real_mult (real_plus real_one (real_opp sig0)) Lm)
             (real_mult (real_opp (r_sub1 sig0)) Lm)
             (r_one_minus_opp sig Lm) (r_one_minus_opp sig0 Lm)).
    exact (real_le_mult_compat_weak _ _ Lm HLm0 Hsub). }
  (* q <= q0 *)
  assert (Hq : real_le q q0).
  { unfold q, q0, r_two_rpow. apply r_exp_le_mono.
    exact (real_le_mult_compat_weak _ _ L2 HL20 Hsub). }
  (* 1 - q0 <= 1 - q *)
  assert (Hden : real_le (r_geom_den Hnpos sig0) (r_geom_den Hnpos sig)).
  { unfold r_geom_den. apply (real_le_plus_compat real_one real_one); [apply real_le_refl |].
    unfold real_le in Hq. unfold real_le. destruct Hq as [Hlt | Heq].
    - exact (inl (r_lt_opp_flip _ _ Hlt)).
    - exact (inr (RealSetoid.real_eq_opp_compat _ _ (real_eq_sym _ _ Heq))). }
  (* inv <= inv0 (the inverse is antitone; the equal case via r_inv_wd) *)
  assert (Hinv : real_le inv inv0).
  { unfold inv, inv0, c_inv_wit. unfold real_le in Hden. unfold real_le. destruct Hden as [Hlt | Heq].
    - exact (inl (real_inv_pos_lt_contra _ _ _ _ Hlt)).
    - exact (inr (r_inv_wd _ _ _ _ (real_eq_sym _ _ Heq))). }
  assert (Hinvpos : real_le real_zero inv)
    by (apply (real_lt_le_iff _ _); left; unfold inv, c_inv_wit; apply real_inv_pos_pos).
  assert (Hq0pos : real_le real_zero q0)
    by (apply (real_lt_le_iff _ _); left; unfold q0, r_two_rpow; apply cauchy_real_exp_pos).
  (* q * inv <= q0 * inv0 *)
  assert (Hprod : real_le (real_mult q inv) (real_mult q0 inv0)).
  { apply (real_le_trans _ (real_mult q0 inv)).
    - exact (real_le_mult_compat_weak q q0 inv Hinvpos Hq).
    - apply (RealSetoid.real_le_compat (real_mult inv q0) (real_mult q0 inv)
               (real_mult inv0 q0) (real_mult q0 inv0)
               (real_mult_comm inv q0) (real_mult_comm inv0 q0)).
      exact (real_le_mult_compat_weak inv inv0 q0 Hq0pos Hinv). }
  (* C(sigma) <= C(sigma0) *)
  assert (HC : real_le (r_geom_const Hnpos sig Hsig1 Hln2pos) (r_geom_const Hnpos sig0 Hs01 Hln2pos)).
  { unfold r_geom_const.
    apply (real_le_plus_compat real_one real_one); [apply real_le_refl | exact Hprod]. }
  assert (HCpos : real_le real_zero (r_geom_const Hnpos sig Hsig1 Hln2pos))
    by (apply (real_lt_le_iff _ _); left; exact (r_geom_const_pos Hnpos sig Hsig1 Hln2pos)).
  assert (Hm1pos0 : real_le real_zero (r_m1sig Hnpos sig0 M HM))
    by (apply (real_lt_le_iff _ _); left; exact (r_m1sig_pos Hnpos sig0 M HM)).
  apply (real_le_trans _ (real_mult (r_m1sig Hnpos sig0 M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos))).
  - exact (real_le_mult_compat_weak _ _ _ HCpos Hm1).
  - apply (RealSetoid.real_le_compat
             (real_mult (r_geom_const Hnpos sig Hsig1 Hln2pos) (r_m1sig Hnpos sig0 M HM))
             (real_mult (r_m1sig Hnpos sig0 M HM) (r_geom_const Hnpos sig Hsig1 Hln2pos))
             (real_mult (r_geom_const Hnpos sig0 Hs01 Hln2pos) (r_m1sig Hnpos sig0 M HM))
             (real_mult (r_m1sig Hnpos sig0 M HM) (r_geom_const Hnpos sig0 Hs01 Hln2pos))
             (real_mult_comm _ _) (real_mult_comm _ _)).
    exact (real_le_mult_compat_weak _ _ _ Hm1pos0 HC).
Qed.

End AbsConvMain.
