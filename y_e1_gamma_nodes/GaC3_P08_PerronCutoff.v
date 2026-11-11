(* ConstructiveWorld-Main - Perron cutoff face, leaf a: bound-side carriers. *)

(** * GaC3_P08_PerronCutoff: leaf a of the Perron truncation face.
    Mission.  Node C3-P08 (segment C3), leaf a: the bound-side carriers of
    the Perron cutoff formula: the natural-log wrapper [GaC3_P08_lnR]; the
    two-case log-distance carrier [GaC3_P08_ln_dist] (the |ln x - ln n|
    form on the decidable nat comparison, no real_abs face) with
    nonnegativity; the positive power [GaC3_P08_powR] (n^c := exp(c * ln n))
    with positivity and n^c >= 1; the one-over face [GaC3_P08_inv_ge1_le_one];
    the harmonic denominator [GaC3_P08_den] (1 + T |ln(x/n)|, >= 1 and > 0);
    and the min-form right side [GaC3_P08_inv_scale_le_one]: together the
    two-form min(1, 1/(T |ln(x/n)|)) registration of the card (weight term,
    truncated sum, main bound: leaf b).
    Dependencies.  [S01_BaseRing] ([NatLe], selective import),
    [S02_CauchyComplete], [S03_QExp] ([cauchy_real_exp]),
    [S07_RealSetoidExpLog] ([real_inv_pos] family, exp pos/mono/wd/zero
    faces, [real_log_lt_mono]), [GaC2_Iface_DS] + leaf a ([nat_real],
    [nat_real_pos], [NatLe_one_S], [NatLe_1_zero_empty],
    [r_plus_zero_l_gen], [r_plus_zero_r_gen], [r_le_of_eq], [real_log_wd]),
    [GaC3_P07_PowerGrowth] ([GaC3_P07_cpowR]), [GaC3_Z01_LogDerivSeries]
    ([z01_log_le_mono], [z01_natreal_le]); Stdlib [QArith], [Arith], [Lia].
    References.  AFP Perrons_Formula perron_bound :1019-1020,
    perron_effective_strong :1208-1225, perron_indicator :26-35;
    PNT_with_Remainder perron_formula :920; cards_C3 C3-P08; drafts_C3 P08.
    Constructivity.  Set-carried statements, Set-sorted predicates; zero
    assumed constants, zero abandoned proofs, zero choice; Section premises
    discharge as explicit arguments at End, so Print Assumptions reads
    Closed; [Hnpos] is L0-stock instantiable via [nat_real_pos].
    Build.  coqc -native-compiler no -q -Q . "" -Q <boot_src> "" GaC3_P08_PerronCutoff.v (work directory, dependency-closure build). *)

Require S01_BaseRing.
(** Notes.  Slot re-registration: the card slot W2 deepens to W4 (leaf b
    consumes the certified [GaC3_P03_ml_vline] face directly; the
    deepen-don't-shallow law, spec section 6 honest appendix 2).  The power
    face consumes the certified [GaC3_P07_cpowR] stem directly (no local
    re-derivation of the exp(s * ln x) body).  Deferred (fail-loud): the
    exact integral identity needs the continuous-integrand line-integral
    carrier and the literal log-derivative integrand object (both open
    slices); the 4(arctan + pi + 1) chain needs a constructive arctan bound
    (P09 slice). *)
(* Selective import (the S01 state-space field S shadows the nat          *)
(* constructor under a full import; only the Set-sorted nat bound face is *)
(* consumed). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_P07_PowerGrowth.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* Left zero product: 0 * x == 0 (the mirror of real_mult_zero). *)
Lemma GaC3_P08_mult_zero_l : forall x : Real,
  real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x.
  apply (real_eq_trans (real_mult real_zero x) (real_mult x real_zero) real_zero).
  - apply real_mult_comm.
  - apply real_mult_zero.
Qed.

(* Subtraction nonnegativity: b <= a gives 0 <= a - b. *)
Lemma GaC3_P08_sub_ge0 : forall a b : Real,
  real_le b a -> real_le real_zero (real_plus a (real_opp b)).
Proof.
  intros a b Hab.
  apply (real_le_trans real_zero
           (real_plus b (real_opp b))
           (real_plus a (real_opp b))).
  - apply r_le_of_eq. apply real_eq_sym. apply real_plus_opp.
  - apply real_le_plus_compat; [ exact Hab | apply real_le_refl ].
Qed.

(* ===================================================================== *)
(* Section 1. The cutoff data and the log-distance carrier.               *)
(* ===================================================================== *)

Section P08Cutoff.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable xk : nat.
Hypothesis Hxk1 : NatLe 1 xk.
Variable c T : Real.
Hypothesis Hc1 : real_lt real_one c.
Hypothesis HT0 : real_lt real_zero T.

(* The natural log on the embedded naturals (the Z01 wrapper shape). *)
Definition GaC3_P08_lnR (n : nat) (Hn : NatLe 1 n) : Real :=
  real_log (nat_real n) (Hnpos n Hn).

(* ln is nonnegative on the embedded naturals: ln 1 == 0 and the tree log *)
(* is monotone. *)
Lemma GaC3_P08_lnR_ge0 : forall (n : nat) (Hn : NatLe 1 n),
  real_le real_zero (GaC3_P08_lnR n Hn).
Proof.
  intros n Hn. destruct n as [|m].
  - destruct (NatLe_1_zero_empty Hn).
  - apply (real_le_trans real_zero
             (GaC3_P08_lnR 1 (NatLe_one_S 0))
             (GaC3_P08_lnR (S m) Hn)).
    + apply r_le_of_eq.
      apply (real_eq_trans real_zero (real_log real_one real_lt_zero_one)
               (GaC3_P08_lnR 1 (NatLe_one_S 0))).
      * apply real_eq_sym. apply real_log_one.
      * apply real_eq_sym.
        exact (real_log_wd (nat_real 1) real_one
                 (Hnpos 1 (NatLe_one_S 0)) real_lt_zero_one nat_real_one).
    + apply z01_log_le_mono.
      apply z01_natreal_le. lia.
Qed.

(* Two-case log distance |ln x - ln n| (no real_abs face; the absolute    *)
(* value is the explicit two-case form split on the decidable nat order). *)
Definition GaC3_P08_ln_dist (n : nat) (Hn : NatLe 1 n) : Real :=
  if Nat.leb n xk
  then real_plus (GaC3_P08_lnR xk Hxk1) (real_opp (GaC3_P08_lnR n Hn))
  else real_plus (GaC3_P08_lnR n Hn) (real_opp (GaC3_P08_lnR xk Hxk1)).

(* The log distance is nonnegative (each branch is a log monotonicity     *)
(* step followed by the subtraction step). *)
Lemma GaC3_P08_ln_dist_ge0 : forall (n : nat) (Hn : NatLe 1 n),
  real_le real_zero (GaC3_P08_ln_dist n Hn).
Proof.
  intros n Hn. unfold GaC3_P08_ln_dist.
  destruct (Nat.leb n xk) eqn:Eleb.
  - assert (Hnx : (n <= xk)%nat) by exact (proj1 (Nat.leb_le n xk) Eleb).
    apply GaC3_P08_sub_ge0.
    apply z01_log_le_mono.
    apply z01_natreal_le. exact Hnx.
  - assert (Hxn : (xk < n)%nat) by exact (proj1 (Nat.leb_gt n xk) Eleb).
    apply GaC3_P08_sub_ge0.
    apply z01_log_le_mono.
    apply z01_natreal_le. lia.
Qed.

(* ===================================================================== *)
(* Section 2. The positive power carrier.                                 *)
(* ===================================================================== *)

(* Positive power n^c := exp(c * ln n), carried by the certified          *)
(* [GaC3_P07_cpowR] stem (direct consumption, no local re-derivation;     *)
(* the P07 complex-power modulus face remains the sibling). *)
Definition GaC3_P08_powR (n : nat) (Hn : NatLe 1 n) : Real :=
  GaC3_P07_cpowR (nat_real n) (Hnpos n Hn) c.

Lemma GaC3_P08_powR_pos : forall (n : nat) (Hn : NatLe 1 n),
  real_lt real_zero (GaC3_P08_powR n Hn).
Proof.
  intros n Hn. unfold GaC3_P08_powR, GaC3_P07_cpowR.
  apply cauchy_real_exp_pos.
Qed.

(* c >= 1 gives c > 0. *)
Lemma GaC3_P08_c_pos : real_lt real_zero c.
Proof.
  apply (real_lt_le_trans real_zero real_one c).
  - exact real_lt_zero_one.
  - apply (real_lt_le_iff real_one c). left. exact Hc1.
Qed.

(* n^c >= 1 for c > 0: c * ln n >= 0 and exp is monotone with exp 0 == 1. *)
Lemma GaC3_P08_powR_ge1 : forall (n : nat) (Hn : NatLe 1 n),
  real_le real_one (GaC3_P08_powR n Hn).
Proof.
  intros n Hn.
  assert (Hcln : real_le real_zero (real_mult c (GaC3_P08_lnR n Hn))).
  { apply (RealSetoid.real_le_compat (real_mult real_zero (GaC3_P08_lnR n Hn))
             real_zero
             (real_mult c (GaC3_P08_lnR n Hn))
             (real_mult c (GaC3_P08_lnR n Hn))).
    - apply GaC3_P08_mult_zero_l.
    - apply real_eq_refl.
    - apply real_le_mult_compat_weak.
      + exact (GaC3_P08_lnR_ge0 n Hn).
      + apply (real_lt_le_iff real_zero c). left. exact GaC3_P08_c_pos. }
  unfold GaC3_P08_powR, GaC3_P07_cpowR.
  unfold real_le in Hcln.
  destruct Hcln as [Hlt | Heq].
  - apply (real_lt_le_iff real_one). left.
    apply (real_eq_lt_lt real_one (cauchy_real_exp real_zero)
             (cauchy_real_exp (real_mult c (GaC3_P08_lnR n Hn)))).
    + apply real_eq_sym. exact cauchy_real_exp_zero.
    + apply cauchy_real_exp_mono. exact Hlt.
  - apply r_le_of_eq.
    apply real_eq_sym.
    apply (real_eq_trans (cauchy_real_exp (real_mult c (GaC3_P08_lnR n Hn)))
             (cauchy_real_exp real_zero) real_one).
    + apply cauchy_real_exp_wd. exact (real_eq_sym _ _ Heq).
    + exact cauchy_real_exp_zero.
Qed.

(* ===================================================================== *)
(* Section 3. The min-form side certificates and the harmonic denominator.*)
(* ===================================================================== *)

Lemma GaC3_P08_inv_one : real_eq (real_inv_pos real_one real_lt_zero_one) real_one.
Proof.
  apply (real_inv_unique real_one (real_inv_pos real_one real_lt_zero_one) real_one).
  - exact (real_inv_pos_correct real_one real_lt_zero_one).
  - apply real_mult_one.
Qed.

(* General one-over face: 1 <= u gives 1/u <= 1 (the min-form left side,  *)
(* min(1, 1/(T|ln(x/n)|)) <= 1). *)
Lemma GaC3_P08_inv_ge1_le_one : forall (u : Real) (Hu : real_lt real_zero u)
    (H1 : real_le real_one u),
  real_le (real_inv_pos u Hu) real_one.
Proof.
  intros u Hu H1. unfold real_le in H1. destruct H1 as [Hlt | Heq].
  - apply (real_lt_le_iff (real_inv_pos u Hu)). left.
    apply (real_lt_le_trans (real_inv_pos u Hu)
             (real_inv_pos real_one real_lt_zero_one) real_one).
    + apply (real_inv_pos_lt_contra real_one u real_lt_zero_one Hu). exact Hlt.
    + apply r_le_of_eq. exact GaC3_P08_inv_one.
  - apply r_le_of_eq.
    apply (real_eq_trans (real_inv_pos u Hu)
             (real_inv_pos real_one real_lt_zero_one) real_one).
    + apply (real_inv_unique u (real_inv_pos u Hu)
               (real_inv_pos real_one real_lt_zero_one)).
      * exact (real_inv_pos_correct u Hu).
      * apply (real_eq_trans (real_mult u (real_inv_pos real_one real_lt_zero_one))
                 (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
                 real_one).
        { apply RealSetoid.real_eq_mult_compat.
          { exact (real_eq_sym real_one u Heq). }
          { apply real_eq_refl. } }
        { apply (real_eq_trans
                   (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
                   (real_mult real_one real_one) real_one).
          { apply RealSetoid.real_eq_mult_compat.
            { apply real_eq_refl. }
            { exact GaC3_P08_inv_one. } }
          { apply real_mult_one. } }
    + exact GaC3_P08_inv_one.
Qed.

(* The harmonic denominator 1 + T * |ln(x/n)|. *)
Definition GaC3_P08_den (n : nat) (Hn : NatLe 1 n) : Real :=
  real_plus real_one (real_mult T (GaC3_P08_ln_dist n Hn)).

Lemma GaC3_P08_den_ge1 : forall (n : nat) (Hn : NatLe 1 n),
  real_le real_one (GaC3_P08_den n Hn).
Proof.
  intros n Hn. unfold GaC3_P08_den.
  apply (RealSetoid.real_le_compat (real_plus real_one real_zero) real_one
           (real_plus real_one (real_mult T (GaC3_P08_ln_dist n Hn)))
           (real_plus real_one (real_mult T (GaC3_P08_ln_dist n Hn)))).
  - apply r_plus_zero_r_gen.
  - apply real_eq_refl.
  - apply real_le_plus_compat.
    + apply real_le_refl.
    + apply (RealSetoid.real_le_compat
               (real_mult real_zero (GaC3_P08_ln_dist n Hn)) real_zero
               (real_mult T (GaC3_P08_ln_dist n Hn))
               (real_mult T (GaC3_P08_ln_dist n Hn))).
      * apply GaC3_P08_mult_zero_l.
      * apply real_eq_refl.
      * apply real_le_mult_compat_weak.
        { exact (GaC3_P08_ln_dist_ge0 n Hn). }
        { apply (real_lt_le_iff real_zero T). left. exact HT0. }
Qed.

Lemma GaC3_P08_den_pos : forall (n : nat) (Hn : NatLe 1 n),
  real_lt real_zero (GaC3_P08_den n Hn).
Proof.
  intros n Hn.
  apply (real_lt_le_trans real_zero real_one (GaC3_P08_den n Hn)).
  - exact real_lt_zero_one.
  - exact (GaC3_P08_den_ge1 n Hn).
Qed.

(* The min-form right side: u/(1+u) <= 1 in the product form D *        *)
(* (T|ln(x/n)|) <= 1 where D := 1/(1 + T|ln(x/n)|) (with min(1, 1/(T L)) *)
(* bounded on the 1/(T L) side by exactly this product inequality). *)
Lemma GaC3_P08_inv_scale_le_one : forall (n : nat) (Hn : NatLe 1 n),
  real_le (real_mult (real_inv_pos (GaC3_P08_den n Hn) (GaC3_P08_den_pos n Hn))
                     (real_mult T (GaC3_P08_ln_dist n Hn)))
          real_one.
Proof.
  intros n Hn.
  assert (Horder : real_le (real_mult T (GaC3_P08_ln_dist n Hn))
                           (GaC3_P08_den n Hn)).
  { unfold GaC3_P08_den.
    apply (RealSetoid.real_le_compat
             (real_plus real_zero (real_mult T (GaC3_P08_ln_dist n Hn)))
             (real_mult T (GaC3_P08_ln_dist n Hn))
             (real_plus real_one (real_mult T (GaC3_P08_ln_dist n Hn)))
             (real_plus real_one (real_mult T (GaC3_P08_ln_dist n Hn)))).
    - apply r_plus_zero_l_gen.
    - apply real_eq_refl.
    - apply real_le_plus_compat.
      + apply (real_lt_le_iff real_zero real_one). left. exact real_lt_zero_one.
      + apply real_le_refl. }
  apply (real_le_trans
           (real_mult (real_inv_pos (GaC3_P08_den n Hn) (GaC3_P08_den_pos n Hn))
                      (real_mult T (GaC3_P08_ln_dist n Hn)))
           (real_mult (real_mult T (GaC3_P08_ln_dist n Hn))
                      (real_inv_pos (GaC3_P08_den n Hn) (GaC3_P08_den_pos n Hn)))
           real_one).
  - apply r_le_of_eq. apply real_mult_comm.
  - apply (real_le_trans
             (real_mult (real_mult T (GaC3_P08_ln_dist n Hn))
                        (real_inv_pos (GaC3_P08_den n Hn) (GaC3_P08_den_pos n Hn)))
             (real_mult (GaC3_P08_den n Hn)
                        (real_inv_pos (GaC3_P08_den n Hn) (GaC3_P08_den_pos n Hn)))
             real_one).
    + apply real_le_mult_compat_weak.
      * apply (real_lt_le_iff real_zero _). left.
        apply real_inv_pos_pos.
      * exact Horder.
    + apply r_le_of_eq.
      exact (real_inv_pos_correct (GaC3_P08_den n Hn) (GaC3_P08_den_pos n Hn)).
Qed.

End P08Cutoff.
