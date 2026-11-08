(* ConstructiveWorld-Main - the log power law, the exponential bridge, and
   the power-form bound for the constructive real logarithm. *)

(** * GaC1_02_LogPowBridge: log power law and the ln/exp bridge.

    Mission.  The log power law for the nat-iterated power with carried
      positivity [gaC1_02_log_ipow], the exponential bridge
      ln(e^t) == t [gaC1_02_log_exp] (thin consumption of the left
      inverse), and the basic power-form effective bound ln x <= x in
      Bishop form [gaC1_02_log_le_x]; the carriers are the
      nat-iterated power [g2_ipow]/[real_ipow]/[real_ipow_pos] and the
      nat-iterated sum [natmulR].

    Dependencies.  Stdlib [Arith.PeanoNat], [QArith.QArith],
      [QArith.Qring], [Setoid], [Morphisms].  Requires [S01_BaseRing],
      [S02_CauchyComplete], [S03_QExp] ([cauchy_real_exp_pos]),
      [S07_RealSetoidExpLog] ([real_log] family),
      [GaC1_RB01_RealLeB] ([real_le_b]),
      [GaC1_RB03_LogLeLinearB] ([real_log_le_linear_B]), and
      [GaC1_01_LogMono] of this development.

    References.  mathlib [Log/Basic.lean] log_pow / log_exp / exp_log.
      Route: [real_log_mult] (S07:7884) as the induction base,
      [log_inv_exp_neg_thm] (S07:5902) as the left inverse, and
      [real_log_le_linear_B] as the Bishop bound.  mathlib's
      [Monoid.npow] is NOT transcribed; the nat-iterated power is cast
      here with positivity carried in the sigT return.

    Constructivity.  Every named construction is carried by [Set];
      predicates are Set-sorted ([real_eq], [real_lt], [real_le_b],
      [QltT]); zero classical choice; closed under the global context;
      [coqchk] reports zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_02_LogPowBridge.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_RB01_RealLeB.
Require Import GaC1_RB03_LogLeLinearB.
Require Import GaC1_01_LogMono.

(* ===================================================================== *)
(* Section 1. Carriers: nat-iterated power with carried positivity and    *)
(* the nat-iterated sum.                                                  *)
(* ===================================================================== *)

Section PowCarriers.

(* The nat-iterated power of a positive real, returning the value with    *)
(* its positivity witness (sigT-carried, red-line path A).                *)
Fixpoint g2_ipow (x : Real) (Hx : real_lt real_zero x) (k : nat)
  : sigT (fun p : Real => real_lt real_zero p) :=
  match k with
  | O => existT _ real_one real_lt_zero_one
  | Datatypes.S k' =>
      match g2_ipow x Hx k' with
      | existT _ p Hp => existT _ (real_mult p x) (real_mult_positive p x Hp Hx)
      end
  end.

Definition real_ipow (x : Real) (Hx : real_lt real_zero x) (k : nat) : Real :=
  projT1 (g2_ipow x Hx k).

Definition real_ipow_pos (x : Real) (Hx : real_lt real_zero x) (k : nat)
  : real_lt real_zero (real_ipow x Hx k) :=
  projT2 (g2_ipow x Hx k).

(* The nat-iterated sum k * t. *)
Fixpoint natmulR (k : nat) (t : Real) : Real :=
  match k with
  | O => real_zero
  | Datatypes.S k' => real_plus (natmulR k' t) t
  end.

End PowCarriers.

(* ===================================================================== *)
(* Section 2. The power law (B1).                                         *)
(* ===================================================================== *)

Section LogPow.

(* B1. ln(x^k) == k * ln x for the nat-iterated power, stated on the     *)
(* sigT components of the positivity-carrying recursor.                  *)
Lemma gaC1_02_log_ipow : forall (k : nat) (x : Real) (Hx : real_lt real_zero x),
  real_eq (real_log (projT1 (g2_ipow x Hx k)) (projT2 (g2_ipow x Hx k)))
          (natmulR k (real_log x Hx)).
Proof.
  intro k. induction k as [| k' IH]; intros x Hx.
  - cbn [natmulR g2_ipow projT1 projT2].
    apply real_log_one.
  - cbn [natmulR g2_ipow].
    destruct (g2_ipow x Hx k') as [p Hp] eqn:E.
    specialize (IH x Hx). rewrite E in IH. cbn [projT1 projT2] in IH.
    apply (real_eq_trans _
      (real_plus (real_log p Hp) (real_log x Hx))).
    + exact (real_log_mult p x Hp Hx).
    + apply RealSetoid.real_eq_plus_compat.
      * exact IH.
      * apply real_eq_refl.
Qed.

End LogPow.

(* ===================================================================== *)
(* Section 3. The exponential bridge (B2) and the power-form bound (B3).  *)
(* ===================================================================== *)

Section LogBridge.

(* B2. ln(e^t) == t: thin consumption of the left inverse, with the       *)
(* positivity premise discharged by [cauchy_real_exp_pos].                *)
Lemma gaC1_02_log_exp : forall t : Real,
  real_eq (real_log (cauchy_real_exp t) (cauchy_real_exp_pos t)) t.
Proof.
  intro t. unfold real_log.
  exact (log_inv_exp_neg_thm t (cauchy_real_exp_pos t)).
Qed.

(* B3. ln x <= x in the Bishop form (Real-epsilon): from the linear       *)
(* bound ln x <= x + (-1), instantiated at the margin e + 1 so that       *)
(* (x + (-1)) + (e + 1) == x + e pointwise.                               *)
Lemma gaC1_02_log_le_x : forall (x : Real) (Hx : real_lt real_zero x),
  real_le_b (real_log x Hx) x.
Proof.
  intros x Hx. unfold real_le_b. intros e He.
  pose proof (real_log_le_linear_B x Hx) as HB.
  unfold real_le_b in HB.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ _ _
    (HB (real_plus e real_one) (real_plus_positive e real_one He Hone))).
  apply real_eq_of_zero_diff. intro n.
  destruct x as [u Hu]. destruct e as [v Hv].
  cbn [real_plus real_opp real_one projT1].
  ring.
Qed.

End LogBridge.
