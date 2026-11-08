(* ConstructiveWorld-Main - Perron cutoff face, leaf b: weight and bound. *)

(** * GaC3_P08_PerronCutoff_b: leaf b of the Perron truncation face.

    Mission.  Node C3-P08 (segment C3), leaf b: the Perron weight term,
    the truncated weight sum and the main truncation bound over the
    leaf-a carriers, plus the psi-face endpoint carriers.  Named faces:
    the weight term [GaC3_P08_pw] (Lambda(n) * (x/n)^c / (1 +
    T|ln(x/n)|), the AFP perron_bound :1019 harmonic shape; (x/n)^c
    carried as x^c * 1/n^c via [real_inv_pos], no division face); the
    truncated sum [GaC3_P08_perron_sum] over 1..N; the main bound
    [GaC3_P08_perron_sum_le] (sum <= x^c * psi(N), psi the [z01_mansum]
    carrier, aggregated from [GaC3_P08_pw_le] through the leaf-a
    min-form sides); the psi monotonicity [GaC3_P08_mansum_mono]; the
    half-weight endpoint carrier [GaC3_P08_psi_half] with sandwich
    [GaC3_P08_psi_half_sandwich] (0 <= h <= 1 places the h-weighted
    endpoint between the neighboring full psi values, the
    perron_indicator :26-35 semantics in scalar-slot form; the concrete
    h := 1/2 instance awaits a real_const order face, the registered
    open const-order face); and the ML consumption face
    [GaC3_P08_vline_ml] ([GaC3_P03_ml_vline], the perron_integrable
    :124 side-condition free at this carrier; this direct consumption
    of the certified [GaC3_P03_MLEstimate] face deepens the node slot
    to W4, the deepen-don't-shallow law).  Deferred (fail-loud): the
    exact integral identity needs the continuous-integrand
    line-integral carrier and the literal log-derivative integrand
    object (both open slices; the P07 power stem is consumed through
    leaf a).

    Dependencies.  [GaC3_P08_PerronCutoff] (leaf a), [S01_BaseRing]
    ([NatLe], selective import), [S02_CauchyComplete], [S03_QExp],
    [S07_RealSetoidExpLog], [GaC2_Iface_DS] + leaf a
    ([r_mult_plus_distr_l], [r_le_of_eq]), [GaC3_P02_LineIntegralAlg]
    (over [GaC3_P01_LineIntegralDef]), [GaC3_P03_MLEstimate],
    [GaC3_Z01_LogDerivSeries] ([z01_lam], [z01_lam_ge0], [z01_mansum]);
    Stdlib [QArith], [Arith], [List], [Lia].

    References.  AFP Perrons_Formula perron_bound :1019-1020,
    perron_effective_strong :1208-1225, perron_indicator :26-35;
    PNT_with_Remainder perron_formula :920, perron_integrable :124;
    cards_C3 C3-P08; drafts_C3 P08.

    Constructivity.  Set-carried statements; Set-sorted predicates
    ([real_lt] / [real_le] / [real_eq] / [NatLe]); zero assumed
    constants, zero abandoned proofs, zero choice principles.  Section
    premises discharge as explicit arguments at End, so Print
    Assumptions reads Closed under the global context.

    Build.  [coqc -native-compiler no -q -Q . "" -Q <boot_src> ""
    GaC3_P08_PerronCutoff_b.v] compiles cleanly (exit 0) from the work
    directory (sandbox pair), single compile lane under the cpu_guard
    v3 wrapper. *)

Require S01_BaseRing.
(* Selective import (the S01 state-space field S shadows the nat          *)
(* constructor under a full import; only the Set-sorted nat bound face is *)
(* consumed). *)
Import S01_BaseRing (NatLe, NatLe_lift, NatLe_drop).
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import GaC2_Iface_DS.
Import GaC2_02_AbsConvTailBound_a.
Require Import GaC3_P02_LineIntegralAlg.
Require Import GaC3_P03_MLEstimate.
Require Import GaC3_Z01_LogDerivSeries.
Require Import GaC3_P08_PerronCutoff.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Local Open Scope Q_scope.

(* ===================================================================== *)
(* Section 1. The Perron weight term and the truncated sum.               *)
(* ===================================================================== *)

Section P08Bound.

Variable Hnpos : forall n : nat, NatLe 1 n -> real_lt real_zero (nat_real n).
Variable xk : nat.
Hypothesis Hxk1 : NatLe 1 xk.
Variable c T : Real.
Hypothesis Hc1 : real_lt real_one c.
Hypothesis HT0 : real_lt real_zero T.

(* The Perron weight term: Lambda(n) * (x/n)^c / (1 + T |ln(x/n)|), the  *)
(* AFP perron_bound :1019 harmonic shape; (x/n)^c is the product x^c *   *)
(* 1/n^c (no division face; the reciprocal is [real_inv_pos]). *)
Definition GaC3_P08_pw (n : nat) (Hn : NatLe 1 n) : Real :=
  real_mult (z01_lam n)
    (real_mult (GaC3_P08_powR Hnpos c xk Hxk1)
       (real_mult
          (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                        (GaC3_P08_powR_pos Hnpos c n Hn))
          (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                        (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))).

(* The truncated Perron weight sum over 1..N. *)
Fixpoint GaC3_P08_perron_sum (N : nat) : Real :=
  match N with
  | O => real_zero
  | S m => real_plus (GaC3_P08_perron_sum m) (GaC3_P08_pw (S m) (NatLe_one_S m))
  end.

(* ===================================================================== *)
(* Section 2. The per-term dominance and the main truncation bound.       *)
(* ===================================================================== *)

(* Per-term engine: Lambda(n) * x^c * (1/n^c) * D <= x^c * Lambda(n),    *)
(* by 1/n^c <= 1 and D <= 1 (both min-form sides of leaf a). *)
Lemma GaC3_P08_pw_le : forall (n : nat) (Hn : NatLe 1 n),
  real_le (GaC3_P08_pw n Hn)
          (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (z01_lam n)).
Proof.
  intros n Hn.
  assert (HJ : real_le (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                   (GaC3_P08_powR_pos Hnpos c n Hn))
                       real_one).
  { exact (GaC3_P08_inv_ge1_le_one (GaC3_P08_powR Hnpos c n Hn)
             (GaC3_P08_powR_pos Hnpos c n Hn)
             (GaC3_P08_powR_ge1 Hnpos c Hc1 n Hn)). }
  assert (HD : real_le (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                   (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))
                       real_one).
  { exact (GaC3_P08_inv_ge1_le_one (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
             (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)
             (GaC3_P08_den_ge1 Hnpos xk Hxk1 T HT0 n Hn)). }
  assert (HJD : real_le (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                             (GaC3_P08_powR_pos Hnpos c n Hn))
                                    (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                               (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
                        real_one).
  { apply (real_le_trans
             (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                  (GaC3_P08_powR_pos Hnpos c n Hn))
                        (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                   (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
             (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                        (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))
             real_one).
    - apply (RealSetoid.real_le_compat
               (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                    (GaC3_P08_powR_pos Hnpos c n Hn))
                          (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                     (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
               (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                    (GaC3_P08_powR_pos Hnpos c n Hn))
                          (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                     (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
               (real_mult real_one
                  (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                             (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
               (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                          (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))).
      { apply real_eq_refl. }
      { apply (real_eq_trans
                 (real_mult real_one
                    (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                               (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
                 (real_mult (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                      (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))
                            real_one)
                 (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                            (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))).
        { apply real_mult_comm. }
        { apply real_mult_one. } }
      { apply real_le_mult_compat_weak.
        { apply (real_lt_le_iff real_zero _). left. apply real_inv_pos_pos. }
        { exact HJ. } }
    - exact HD. }
  assert (HXle : real_le (real_mult (GaC3_P08_powR Hnpos c xk Hxk1)
                              (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                                   (GaC3_P08_powR_pos Hnpos c n Hn))
                                         (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                                    (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))))
                         (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one)).
  { apply (real_le_trans
             (real_mult (GaC3_P08_powR Hnpos c xk Hxk1)
                (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                     (GaC3_P08_powR_pos Hnpos c n Hn))
                           (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                      (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))))
             (real_mult (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                            (GaC3_P08_powR_pos Hnpos c n Hn))
                                   (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                              (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
                        (GaC3_P08_powR Hnpos c xk Hxk1))
             (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one)).
    - apply r_le_of_eq. apply real_mult_comm.
    - apply (real_le_trans
               (real_mult (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                              (GaC3_P08_powR_pos Hnpos c n Hn))
                                  (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                             (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))
                          (GaC3_P08_powR Hnpos c xk Hxk1))
               (real_mult real_one (GaC3_P08_powR Hnpos c xk Hxk1))
               (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one)).
      + apply real_le_mult_compat_weak.
        * apply (real_lt_le_iff real_zero _). left.
          exact (GaC3_P08_powR_pos Hnpos c xk Hxk1).
        * exact HJD.
      + apply r_le_of_eq. apply real_mult_comm. }
  unfold GaC3_P08_pw.
  apply (real_le_trans
           (real_mult (z01_lam n)
              (real_mult (GaC3_P08_powR Hnpos c xk Hxk1)
                 (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                      (GaC3_P08_powR_pos Hnpos c n Hn))
                            (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                       (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))))
           (real_mult (z01_lam n) (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one))
           (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (z01_lam n))).
  - apply (RealSetoid.real_le_compat
             (real_mult (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                        (GaC3_P08_powR_pos Hnpos c n Hn))
                              (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                         (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn))))
                        (z01_lam n))
             (real_mult (z01_lam n)
                (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (real_mult (real_inv_pos (GaC3_P08_powR Hnpos c n Hn)
                                        (GaC3_P08_powR_pos Hnpos c n Hn))
                              (real_inv_pos (GaC3_P08_den Hnpos xk Hxk1 T n Hn)
                                         (GaC3_P08_den_pos Hnpos xk Hxk1 T HT0 n Hn)))))
             (real_mult (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one) (z01_lam n))
             (real_mult (z01_lam n) (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one))).
    { apply real_mult_comm. }
    { apply real_mult_comm. }
    { apply real_le_mult_compat_weak.
      { exact (z01_lam_ge0 n). }
      { exact HXle. } }
  - apply r_le_of_eq.
    apply (real_eq_trans
             (real_mult (z01_lam n) (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) real_one))
             (real_mult (z01_lam n) (GaC3_P08_powR Hnpos c xk Hxk1))
             (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (z01_lam n))).
    + apply RealSetoid.real_eq_mult_compat.
      * apply real_eq_refl.
      * apply real_mult_one.
    + apply real_mult_comm.
Qed.

(* The main truncation bound: sum_{n<=N} Lambda(n)(x/n)^c/(1+T|ln(x/n)|) *)
(* <= x^c * psi(N) (psi = the [z01_mansum] carrier; AFP perron_bound     *)
(* :1019 shape aggregated by the per-term dominance). *)
Theorem GaC3_P08_perron_sum_le : forall N : nat,
  real_le (GaC3_P08_perron_sum N)
          (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (z01_mansum N)).
Proof.
  intro N. induction N as [|N IH].
  - cbn [z01_mansum].
    apply r_le_of_eq.
    apply real_eq_sym. apply real_mult_zero.
  - cbn [GaC3_P08_perron_sum z01_mansum].
    apply (real_le_trans
             (real_plus (GaC3_P08_perron_sum N)
                        (GaC3_P08_pw (S N) (NatLe_one_S N)))
             (real_plus (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (z01_mansum N))
                        (real_mult (GaC3_P08_powR Hnpos c xk Hxk1) (z01_lam (S N))))
             (real_mult (GaC3_P08_powR Hnpos c xk Hxk1)
                        (real_plus (z01_mansum N) (z01_lam (S N))))).
    + apply real_le_plus_compat.
      * exact IH.
      * exact (GaC3_P08_pw_le (S N) (NatLe_one_S N)).
    + apply r_le_of_eq.
      apply real_eq_sym. apply r_mult_plus_distr_l.
Qed.

End P08Bound.

(* ===================================================================== *)
(* Section 3. The psi-carrier monotonicity and the half-weight endpoint.  *)
(* ===================================================================== *)

(* Right addition of a nonnegative real preserves order. *)
Lemma GaC3_P08_le_plus_r : forall a b : Real,
  real_le real_zero b -> real_le a (real_plus a b).
Proof.
  intros a b Hb.
  apply (real_le_trans a (real_plus a real_zero) (real_plus a b)).
  - apply r_le_of_eq. apply real_eq_sym. apply r_plus_zero_r_gen.
  - apply real_le_plus_compat; [ apply real_le_refl | exact Hb ].
Qed.

(* Monotonicity of the psi carrier in the cutoff index (Lambda >= 0). *)
Lemma GaC3_P08_mansum_mono : forall m n : nat, (m <= n)%nat ->
  real_le (z01_mansum m) (z01_mansum n).
Proof.
  intros m n. induction n as [|N IH]; intros Hle.
  - assert (Hm0 : m = 0%nat) by lia. subst m. apply real_le_refl.
  - destruct (Nat.eq_dec m (S N)) as [Heq | Hne].
    + rewrite Heq. apply real_le_refl.
    + apply (real_le_trans (z01_mansum m) (z01_mansum N) (z01_mansum (S N))).
      * apply IH. lia.
      * cbn [z01_mansum]. apply GaC3_P08_le_plus_r.
        exact (z01_lam_ge0 (S N)).
Qed.

(* The half-weight endpoint carrier: psi at the cutoff point with a      *)
(* fraction-weighted last term (the sum_upto prime semantics; the scalar *)
(* slot h carries the fraction, the concrete h := 1/2 instance being the *)
(* registered open const-order face). *)
Definition GaC3_P08_psi_half (h : Real) (k : nat) (Hk : NatLe 1 k) : Real :=
  real_plus (z01_mansum (Nat.pred k)) (real_mult h (z01_lam k)).

(* The sandwich: for 0 <= h <= 1 the half-weight carrier lies between    *)
(* the neighboring full psi values (the perron_indicator :26-35          *)
(* semantics in scalar-slot form). *)
Theorem GaC3_P08_psi_half_sandwich : forall (h : Real) (k : nat) (Hk : NatLe 1 k),
  real_le real_zero h -> real_le h real_one ->
  (real_le (z01_mansum (Nat.pred k)) (GaC3_P08_psi_half h k Hk) *
   real_le (GaC3_P08_psi_half h k Hk) (z01_mansum k))%type.
Proof.
  intros h k Hk Hh0 Hh1. destruct k as [|m].
  - destruct (NatLe_1_zero_empty Hk).
  - split.
    + unfold GaC3_P08_psi_half. cbn [Nat.pred].
      apply GaC3_P08_le_plus_r.
      apply (real_le_trans real_zero
               (real_mult real_zero (z01_lam (S m)))
               (real_mult h (z01_lam (S m)))).
      { apply r_le_of_eq. apply real_eq_sym.
        apply (real_eq_trans (real_mult real_zero (z01_lam (S m)))
                 (real_mult (z01_lam (S m)) real_zero) real_zero).
        - apply real_mult_comm.
        - apply real_mult_zero. }
      { exact (real_le_mult_compat_weak real_zero h (z01_lam (S m))
                 (z01_lam_ge0 (S m)) Hh0). }
    + unfold GaC3_P08_psi_half. cbn [Nat.pred].
      apply (real_le_trans (real_plus (z01_mansum m) (real_mult h (z01_lam (S m))))
               (real_plus (z01_mansum m) (real_mult real_one (z01_lam (S m))))
               (real_plus (z01_mansum m) (z01_lam (S m)))).
      * apply real_le_plus_compat.
        { apply real_le_refl. }
        { exact (real_le_mult_compat_weak h real_one (z01_lam (S m))
                   (z01_lam_ge0 (S m)) Hh1). }
      * apply real_le_plus_compat.
        { apply real_le_refl. }
        { apply r_le_of_eq.
          apply (real_eq_trans (real_mult real_one (z01_lam (S m)))
                   (real_mult (z01_lam (S m)) real_one) (z01_lam (S m))).
          - apply real_mult_comm.
          - apply real_mult_one. }
Qed.

(* ===================================================================== *)
(* Section 4. The vertical-line ML consumption face (Q level).            *)
(* ===================================================================== *)

(* The truncated vertical contour at the step carrier: value data        *)
(* bounded by B gives both components at most B * (2T) (the ML corridor  *)
(* the Perron vline consumes). *)
Theorem GaC3_P08_vline_ml : forall (c T : Q) (vs : list (Q * Q)) (B : Q),
  (0 <= T)%Q -> (0 <= B)%Q ->
  (forall v, In v vs -> GaC3_P03_val_bounded v B) ->
  Qabs (GaC3_P02_path_sumR (GaC3_P02_vline_seg c T) vs) <= B * (2 * T)
  /\ Qabs (GaC3_P02_path_sumI (GaC3_P02_vline_seg c T) vs) <= B * (2 * T).
Proof.
  intros c T vs B HT HB Hv. exact (GaC3_P03_ml_vline c T vs B HT HB Hv).
Qed.
