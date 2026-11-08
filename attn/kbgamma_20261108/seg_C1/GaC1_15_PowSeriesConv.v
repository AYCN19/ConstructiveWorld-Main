(* ConstructiveWorld-Main - the real-scalar geometric-tail convergence
   scheme in its minimal sufficient shape. *)

(** * GaC1_15_PowSeriesConv: geometric-tail convergence and the Cauchy
      criterion in the GAPASUME slot form.

    Mission.  The real-scalar geometric-tail convergence scheme in its
      minimal sufficient shape: the partial-sum/difference carriers
      [rsum]/[rdif], the craft bridges [gaC1_15_le_b_plus_compat]/
      [gaC1_15_le_b_eq_l]/[gaC1_15_le_b_eq_r]/[gaC1_15_le_b_lt_lt]
      (the le_b + lt -> lt constructive bridge), the closed-form tail
      interface [gaC1_15_tail_closed], and the partial-sum Cauchy
      criterion [gaC1_15_cauchy].  The complex lift runs through
      GaC1_14's bridges; the exp-series instance is carried by the
      piu_zz_pnt_qexp.v:41 face (Node B5.2 plus [cauchy_real_exp]
      S03:1203) and is NOT re-cast.  Honest deferral: the Q-level
      closed-form geometric division lemma
      (sum q^i == (q^N - q^M)/(1-q)) is NOT cast here, because the
      tail interface (tailbound supplier) is the consumption shape for
      the gamma-2 geometric plug and the exp instance plugs the
      Q-level Taylor remainder bounds directly; the omission is
      explicit.

    Dependencies.  Stdlib [Arith.PeanoNat], [QArith.QArith],
      [QArith.Qring], [QArith.Qabs], [Setoid], [Morphisms].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S07_RealSetoidExpLog],
      [GaC1_RB01_RealLeB] ([real_le_b]), [GaC1_14_SeriesCauchy], and
      [GaC1_04_QRealBridge] (the craft helpers) of this development.
      The GaC1_03 Bishop plus-compat artifact is inlined (copy); zero
      new mathematics.

    References.  mathlib [RadiusOfConvergence.lean]
      le_radius_of_bound / summable_norm_mul_pow / protected hasSum;
      the classical sup/CompleteSpace/Classical carriers are NOT
      transcribed (red line 1); the explicit epsilon-N margin form is
      the minimal constructively correct shape.

    Constructivity.  The [tailbound] supplier and its smallness search
      are Section variables discharged at [End] (the
      piu_zz_tau_enclosure_base slot pattern); all constructions are
      Set-carried; closed under the global context; [coqchk] reports
      zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_15_PowSeriesConv.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import QArith.QArith QArith.Qring QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_RB01_RealLeB.
Require Import GaC1_14_SeriesCauchy.
Require Import GaC1_04_QRealBridge.

(* ===================================================================== *)
(* Section 1. Carriers: real partial sums and differences.                *)
(* ===================================================================== *)

Section Carriers15.

Fixpoint rsum (a : nat -> Real) (n : nat) : Real :=
  match n with
  | O => real_zero
  | Datatypes.S k => real_plus (rsum a k) (a k)
  end.

Definition rdif (x y : Real) : Real := real_plus x (real_opp y).

End Carriers15.

(* ===================================================================== *)
(* Section 2. Craft bridges (inlined from GaC1_03).                       *)
(* ===================================================================== *)

Section Craft15.

Lemma gaC1_15_le_b_plus_compat : forall x y z w : Real,
  real_le_b x y -> real_le_b z w ->
  real_le_b (real_plus x z) (real_plus y w).
Proof.
  intros x y z w H1 H2. unfold real_le_b. intros e He.
  assert (HhalfT : QltT 0 (1#2)%Q) by reflexivity.
  assert (Hhalf : real_lt real_zero (real_const (1#2)%Q)).
  { refine (real_eq_lt_lt _ _ _ _ (gaC1_04_qlt_const_lt 0 (1#2)%Q HhalfT)).
    apply real_eq_of_zero_diff. intro n.
    cbn [real_const projT1 real_zero].
    ring. }
  assert (Hm : real_lt real_zero (real_mult e (real_const (1#2)%Q)))
    by exact (real_mult_positive e (real_const (1#2)%Q) He Hhalf).
  pose proof (H1 (real_mult e (real_const (1#2)%Q)) Hm) as Hx.
  pose proof (H2 (real_mult e (real_const (1#2)%Q)) Hm) as Hz.
  assert (Hstep1 : real_lt (real_plus z x)
                     (real_plus z (real_plus y (real_mult e (real_const (1#2)%Q)))))
    by exact (real_lt_plus_translate z x _ Hx).
  assert (Hstep2 : real_lt (real_plus x z)
                     (real_plus z (real_plus y (real_mult e (real_const (1#2)%Q)))))
    by exact (real_eq_lt_lt _ _ _ (real_plus_comm x z) Hstep1).
  assert (Hstep3 : real_lt (real_plus (real_plus y (real_mult e (real_const (1#2)%Q))) z)
                     (real_plus (real_plus y (real_mult e (real_const (1#2)%Q)))
                                (real_plus w (real_mult e (real_const (1#2)%Q)))))
    by exact (real_lt_plus_translate _ z _ Hz).
  assert (Hstep4 : real_lt (real_plus z (real_plus y (real_mult e (real_const (1#2)%Q))))
                     (real_plus (real_plus y (real_mult e (real_const (1#2)%Q)))
                                (real_plus w (real_mult e (real_const (1#2)%Q)))))
    by exact (real_eq_lt_lt _ _ _ (real_plus_comm z (real_plus y (real_mult e (real_const (1#2)%Q))))
                Hstep3).
  assert (Hstep5 : real_lt (real_plus x z)
                     (real_plus (real_plus y (real_mult e (real_const (1#2)%Q)))
                                (real_plus w (real_mult e (real_const (1#2)%Q)))))
    by exact (real_lt_trans _ _ _ Hstep2 Hstep4).
  apply (real_lt_eq_lt _ _ _ Hstep5).
  apply real_eq_of_zero_diff. intro n.
  destruct y as [b Hb]. destruct z as [c Hc]. destruct w as [d Hd].
  destruct e as [v Hv].
  cbn [real_plus real_mult real_const projT1].
  ring.
Qed.

Lemma gaC1_15_le_b_eq_l : forall x y z : Real,
  real_eq x y -> real_le_b y z -> real_le_b x z.
Proof.
  intros x y z Hxy Hyz. unfold real_le_b in *. intros e He.
  exact (real_eq_lt_lt _ _ _ Hxy (Hyz e He)).
Qed.

Lemma gaC1_15_le_b_eq_r : forall x y z : Real,
  real_le_b x y -> real_eq y z -> real_le_b x z.
Proof.
  intros x y z H Hxyz. unfold real_le_b in *. intros e He.
  apply (real_lt_eq_lt _ _ _ (H e He)).
  apply RealSetoid.real_eq_plus_compat.
  - exact Hxyz.
  - apply real_eq_refl.
Qed.

(* le_b x y and real_lt y z give real_lt x z (the constructive bridge).  *)
Lemma gaC1_15_le_b_lt_lt : forall x y z : Real,
  real_le_b x y -> real_lt y z -> real_lt x z.
Proof.
  intros x y z Hle Hlt. unfold real_le_b in *.
  assert (Heq1 : real_eq real_zero (real_plus (real_opp y) y)).
  { apply real_eq_of_zero_diff. intro n.
    destruct y as [u Hu].
    cbn [rdif real_plus real_opp projT1 real_zero].
    ring. }
  assert (Hd : real_lt real_zero (rdif z y)).
  { assert (Ht : real_lt (real_plus (real_opp y) y) (real_plus (real_opp y) z))
      by exact (real_lt_plus_translate (real_opp y) y z Hlt).
    apply (real_lt_eq_lt _ _ _ (real_eq_lt_lt _ _ _ Heq1 Ht)).
    (* (−y)+z == z+(−y) *)
    apply real_eq_of_zero_diff. intro n.
    destruct y as [u Hu]. destruct z as [v Hv].
    cbn [rdif real_plus real_opp projT1].
    ring. }
  pose proof (Hle (rdif z y) Hd) as Hxd.
  apply (real_lt_eq_lt _ _ _ Hxd).
  apply real_eq_of_zero_diff. intro n.
  unfold rdif in Hxd |- *.
  destruct y as [u Hu]. destruct z as [v Hv].
  cbn [real_plus real_opp projT1].
  ring.
Qed.

End Craft15.

(* ===================================================================== *)
(* Section 3. H2 (closed-form tail interface) and H1 (Cauchy criterion)   *)
(* in the GAPASUME slot form.                                             *)
(* ===================================================================== *)

Section GAPASUME.

Variable a : nat -> Real.
Variable tailbound : nat -> Real.

(* The geometric-tail supplier: differences of partial sums are bounded  *)
(* by the closed-form tail value.                                        *)
Hypothesis Htail :
  forall m n : nat, NatLe n m ->
    real_le_b (rdif (rsum a m) (rsum a n)) (tailbound n).

(* The constructive smallness search: tail values are eventually below   *)
(* every rational margin.                                                *)
Hypothesis Htailsmall :
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      real_lt (tailbound n) (real_const eps)).

(* H2. The closed-form tail bound (named consumption shape). *)
Lemma gaC1_15_tail_closed :
  forall m n : nat, NatLe n m ->
    real_le_b (rdif (rsum a m) (rsum a n)) (tailbound n).
Proof.
  intros m n Hnm. exact (Htail m n Hnm).
Qed.

(* H1. Partial sums are Cauchy in the squared-margin real_lt form:       *)
(* for every rational eps > 0 there is N with                            *)
(* rdif (rsum m) (rsum n) < eps^2 for all m >= n >= N.                   *)
Lemma gaC1_15_cauchy :
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat, NatLe N m -> NatLe N n ->
      NatLe n m ->
      real_lt (rdif (rsum a m) (rsum a n))
              (real_mult (real_const eps) (real_const eps))).
Proof.
  intros eps Heps.
  assert (Heps0 : Qlt 0 eps) by (apply QltT_to_Qlt; exact Heps).
  assert (Heps2pos : Qlt 0 (eps * eps)).
  { pose proof (Qmult_lt_compat_r 0 eps eps Heps0 Heps0) as H.
    rewrite (Qmult_0_l eps) in H. exact H. }
  destruct (Htailsmall (eps * eps) (Qlt_to_QltT _ _ Heps2pos)) as [N HN].
  exists N.
  intros m n Hm Hn Hnm.
  exact (gaC1_15_le_b_lt_lt _ _ _ (Htail m n Hnm) (HN n Hn)).
Qed.

End GAPASUME.
