(* ConstructiveWorld-Main - order properties of the real k-th root in the
   Or-form order on the constructive real line. *)

(** * GaC1_06_RealPowOrder: Or-form order of the real k-th root.

    Mission.  Order properties of the real k-th root in the Or-form
      [real_le] (constructively available through the Or-form log
      monotonicity and exp strict monotonicity): the base-order
      monotonicity [gaC1_06_kroot_le_mono] and the coarse bound
      [gaC1_06_kroot_le_one_plus] (kroot x <= 1 + x for x >= 1), on
      the Or-form order helpers [g06_plus_zero_r]/[g06_le_eq_l]/
      [g06_le_eq_r]/[g06_le_trans]/[g06_exp_le]/[g06_const_pos]/
      [g06_const_one]/[g06_scale_le]/[g06_le_one_plus].  Honest
      deferral: F2 (exponent-order reversal x^{1/l} <= x^{1/k} for
      k <= l, x >= 1) is a further Q-order case split on (1/l, 1/k)
      over the same engines and is deferred explicitly; the psi-bridge
      tail constants (Dusart 1.00007 x^{1/2} + 1.78 x^{1/3}) belong to
      the C4 layer and are not cast here.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qring], [Setoid],
      [Morphisms], [Lia].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp], [S07_RealSetoidExpLog],
      [S14_B5BatchBlock] ([real_log_le_mono]), [GaC1_01_LogMono],
      [GaC1_04_QRealBridge] (const-margin positivity), and
      [GaC1_05_RealPowRoot] of this development.

    References.  mathlib [Pow/Real.lean] rpow_le_rpow /
      rpow_le_rpow_of_exponent_le.

    Constructivity.  Every named construction is carried by [Set];
      predicates are Set-sorted ([real_eq], [real_lt], [real_le],
      [QltT], [Id]); zero classical choice (the Q-order decision uses
      the decidable [Qlt_le_dec]); closed under the global context;
      [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_06_RealPowOrder.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import S14_B5BatchBlock.
Require Import GaC1_01_LogMono.
Require Import GaC1_04_QRealBridge.
Require Import GaC1_05_RealPowRoot.

(* ===================================================================== *)
(* Section 1. Or-form order helpers.                                      *)
(* ===================================================================== *)

Section OrHelpers.

Lemma g06_plus_zero_r : forall x : Real, real_eq (real_plus x real_zero) x.
Proof.
  intro x. destruct x as [u Hu].
  apply real_eq_of_zero_diff. intro n.
  cbn [real_plus real_zero projT1]. ring.
Qed.

Lemma g06_le_eq_l : forall a b c : Real,
  real_eq a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Hab Hbc. destruct Hbc as [Hlt | Heq].
  - exact (@inl _ _ (real_eq_lt_lt _ _ _ Hab Hlt)).
  - exact (@inr _ _ (real_eq_trans _ _ _ Hab Heq)).
Qed.

Lemma g06_le_eq_r : forall a b c : Real,
  real_le a b -> real_eq b c -> real_le a c.
Proof.
  intros a b c Hab Hbc. destruct Hab as [Hlt | Heq].
  - exact (@inl _ _ (real_lt_eq_lt _ _ _ Hlt Hbc)).
  - exact (@inr _ _ (real_eq_trans _ _ _ Heq Hbc)).
Qed.

Lemma g06_le_trans : forall a b c : Real,
  real_le a b -> real_le b c -> real_le a c.
Proof.
  intros a b c Hab Hbc.
  destruct Hab as [H1 | H1]; destruct Hbc as [H2 | H2].
  - exact (@inl _ _ (real_lt_trans _ _ _ H1 H2)).
  - exact (@inl _ _ (real_lt_eq_lt _ _ _ H1 H2)).
  - exact (@inl _ _ (real_eq_lt_lt _ _ _ H1 H2)).
  - exact (@inr _ _ (real_eq_trans _ _ _ H1 H2)).
Qed.

(* exp preserves the Or-form order. *)
Lemma g06_exp_le : forall u v : Real,
  real_le u v -> real_le (cauchy_real_exp u) (cauchy_real_exp v).
Proof.
  intros u v H. destruct H as [Hlt | Heq].
  - exact (@inl _ _ (cauchy_real_exp_mono u v Hlt)).
  - exact (@inr _ _ (cauchy_real_exp_wd u v Heq)).
Qed.

(* 0 < real_const q from QltT 0 q. *)
Lemma g06_const_pos : forall q : Q, QltT 0 q -> real_lt real_zero (real_const q).
Proof.
  intros q Hq.
  refine (real_eq_lt_lt _ _ _ _ (gaC1_04_qlt_const_lt 0 q Hq)).
  apply real_eq_of_zero_diff. intro n.
  cbn [real_const projT1 real_zero]. ring.
Qed.

(* real_const 1 == real_one. *)
Lemma g06_const_one : real_eq (real_const 1) real_one.
Proof.
  apply real_eq_of_zero_diff. intro n.
  cbn [real_const real_one projT1]. ring.
Qed.

End OrHelpers.

(* ===================================================================== *)
(* Section 2. F1: base-order monotonicity.                                *)
(* ===================================================================== *)

Section BaseOrder.

Lemma gaC1_06_kroot_le_mono :
  forall (k : positive) (x y : Real) (Hx : real_lt real_zero x) (Hy : real_lt real_zero y),
    real_le x y -> real_le (kroot k x Hx) (kroot k y Hy).
Proof.
  intros k x y Hx Hy Hxy. unfold kroot.
  assert (HhT : QltT 0 (1 # k)%Q) by reflexivity.
  assert (Hh : real_lt real_zero (real_const (1 # k)%Q)) by exact (g06_const_pos _ HhT).
  destruct Hxy as [Hlt | Heq].
  - apply (@inl _ _).
    apply cauchy_real_exp_mono.
    exact (real_mult_lt_compat_l _ _ _ (real_log_lt_mono x y Hx Hy Hlt) Hh).
  - apply (@inr _ _).
    apply cauchy_real_exp_wd.
    apply RealSetoid.real_eq_mult_compat.
    + apply real_eq_refl.
    + exact (gaC1_05_log_eq_transfer x y Hx Hy Heq).
Qed.

End BaseOrder.

(* ===================================================================== *)
(* Section 3. F3: the coarse bound kroot x <= 1 + x for x >= 1.           *)
(* ===================================================================== *)

Section CoarseBound.

(* (1/k) * L <= L for 0 <= L. *)
Lemma g06_scale_le : forall (k : positive) (L : Real),
  real_le real_zero L ->
  real_le (real_mult (real_const (1 # k)%Q) L) L.
Proof.
  intros k L HL.
  destruct (Qlt_le_dec (1 # k)%Q 1) as [Hlt1 | Hge1].
  - (* 1/k < 1 *)
    assert (Hh1 : real_lt (real_const (1 # k)%Q) real_one).
    { apply (real_lt_eq_lt _ _ _ (gaC1_04_qlt_const_lt _ _ (Qlt_to_QltT _ _ Hlt1))).
      exact g06_const_one. }
    destruct HL as [HLpos | HLz].
    + apply (@inl _ _).
      pose proof (real_mult_lt_compat_l _ _ _ Hh1 HLpos) as H.
      (* L * h < L * 1 == L ; transport to h * L *)
      apply (real_eq_lt_lt _ _ _ (real_mult_comm (real_const (1 # k)%Q) L)).
      apply (real_lt_eq_lt _ _ _ H).
      apply real_mult_one.
    + apply (@inr _ _).
      (* h * L == h * 0 == 0 == L *)
      apply (real_eq_trans _ (real_mult (real_const (1 # k)%Q) real_zero)).
      * apply RealSetoid.real_eq_mult_compat.
        -- apply real_eq_refl.
        -- apply (real_eq_sym _ _). exact HLz.
      * apply (real_eq_trans _ real_zero).
        -- apply real_mult_zero.
        -- exact HLz.
  - (* 1 <= 1/k, hence 1/k == 1 since 1/k <= 1 *)
    assert (Hle1 : Qle (1 # k)%Q 1).
    { unfold Qle. cbn. lia. }
    assert (Heq1 : (1 # k)%Q == 1) by exact (Qle_antisym _ _ Hle1 Hge1).
    apply (@inr _ _).
    apply (real_eq_trans _ (real_mult real_one L)).
    + apply RealSetoid.real_eq_mult_compat.
      * apply (real_eq_trans _ (real_const 1)).
        -- apply real_eq_of_zero_diff. intro n.
           cbn [real_const projT1].
           setoid_rewrite Heq1. ring.
        -- exact g06_const_one.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult L real_one)).
      * apply real_mult_comm.
      * apply real_mult_one.
Qed.

(* x <= 1 + x. *)
Lemma g06_le_one_plus : forall x : Real, real_le x (real_plus real_one x).
Proof.
  intro x. apply (@inl _ _).
  assert (H : real_lt (real_plus x real_zero) (real_plus x real_one))
    by exact (real_lt_plus_translate x real_zero real_one real_lt_zero_one).
  apply (real_eq_lt_lt _ _ _ (real_eq_sym _ _ (g06_plus_zero_r x))).
  apply (real_lt_eq_lt _ _ _ H).
  apply real_plus_comm.
Qed.

(* F3. kroot x <= 1 + x for x >= 1. *)
Lemma gaC1_06_kroot_le_one_plus :
  forall (k : positive) (x : Real) (Hx : real_lt real_zero x),
    real_le real_one x -> real_le (kroot k x Hx) (real_plus real_one x).
Proof.
  intros k x Hx Hge.
  assert (H1x : real_lt real_zero (real_plus real_one x))
    by exact (real_plus_positive real_one x real_lt_zero_one Hx).
  (* 0 <= ln x *)
  assert (HL : real_le real_zero (real_log x Hx)).
  { apply (g06_le_eq_l _ _ _ (real_eq_sym _ _ (real_log_one real_lt_zero_one))).
    exact (real_log_le_mono real_one x real_lt_zero_one Hx Hge). }
  (* (1/k) ln x <= ln x <= ln (1+x) *)
  assert (Hchain : real_le (real_mult (real_const (1 # k)%Q) (real_log x Hx))
                           (real_log (real_plus real_one x) H1x)).
  { apply (g06_le_trans _ _ _ (g06_scale_le k _ HL)).
    exact (real_log_le_mono x (real_plus real_one x) Hx H1x (g06_le_one_plus x)). }
  unfold kroot.
  apply (g06_le_eq_r _ _ _ (g06_exp_le _ _ Hchain)).
  unfold real_log.
  exact (cw_log_exp_right (real_plus real_one x) H1x).
Qed.

End CoarseBound.
