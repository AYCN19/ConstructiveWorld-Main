(* ConstructiveWorld-Main - the sum/product telescope at the Real layer:
   product expansion, positive-term telescope bound, and tail sums. *)

(** * GaC1_03_LogTelescope: the Real-layer log telescope.

    Mission.  The sum/product telescope at the Real layer: the
      nat-iterated product and sum carriers with carried positivity
      [g3_prod]/[sumR], the finite product expansion
      ln(prod a_i) == sum ln a_i [gaC1_03_log_prod], the positive-term
      telescope bound ln(prod (1+t_i)) <= sum t_i in the
      constructively correct Bishop form [gaC1_03_telescope], and the
      nonnegative tail sum [gaC1_03_sumR_nonneg] (the psi-theta
      dyadic-tail carrier consumed downstream via [GaC1_Iface_Real]);
      Bishop-form arithmetic helpers [gaC1_03_le_b_refl]/
      [gaC1_03_le_b_eq_r]/[gaC1_03_le_b_eq_l]/[gaC1_03_linear_shift]/
      [gaC1_03_log_le_t]/[gaC1_03_le_b_plus_compat].

    Dependencies.  Stdlib [Arith.PeanoNat], [QArith.QArith],
      [QArith.Qring], [Setoid], [Morphisms].  Requires
      [S01_BaseRing], [S02_CauchyComplete], [S07_RealSetoidExpLog],
      [GaC1_RB01_RealLeB] ([real_le_b]),
      [GaC1_RB02_RealLeToLeB] ([real_le_to_le_b], the one-way bridge),
      [GaC1_RB03_LogLeLinearB] ([real_log_le_linear_B]),
      [GaC1_01_LogMono], and [GaC1_04_QRealBridge] (the craft helpers:
      const-margin positivity and the [QltT] pointwise transfer) of
      this development.

    References.  mathlib [Log/Basic.lean] log_prod / log_mul /
      log_le_sub_one_of_pos; nat-side telescope original
      [pec_theta_bound] (abl_Pr_erdos_theta.v:197, all-Set with zero
      assumed constants).  The main chain needs only the relative
      bound.

    Constructivity.  Every named construction is carried by [Set];
      predicates are Set-sorted ([real_eq], [real_lt], [real_le],
      [real_le_b], [QltT], [Id]); zero classical choice; margins are
      explicit (the half-margin uses the literal 1/2 via the Q->Real
      const bridge); closed under the global context; [coqchk] reports
      zero assumed constants.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <dir> "" GaC1_03_LogTelescope.v] compiles cleanly (exit 0),
      wrapped by [cpu_guard v3]. *)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import QArith.QArith QArith.Qring.
From Stdlib Require Import Setoid Morphisms.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import GaC1_RB01_RealLeB.
Require Import GaC1_RB02_RealLeToLeB.
Require Import GaC1_RB03_LogLeLinearB.
Require Import GaC1_01_LogMono.
Require Import GaC1_04_QRealBridge.

(* ===================================================================== *)
(* Section 1. Carriers: nat-iterated product and sum.                     *)
(* ===================================================================== *)

Section Carriers.

(* The nat-iterated product of positive reals, with carried positivity.   *)
Fixpoint g3_prod (t : nat -> Real) (Ht : forall i, real_lt real_zero (t i))
  (N : nat) : sigT (fun p : Real => real_lt real_zero p) :=
  match N with
  | O => existT _ real_one real_lt_zero_one
  | Datatypes.S k =>
      match g3_prod t Ht k with
      | existT _ p Hp =>
          existT _ (real_mult p (t k)) (real_mult_positive p (t k) Hp (Ht k))
      end
  end.

(* The nat-iterated sum of a Real-valued sequence. *)
Fixpoint sumR (f : nat -> Real) (N : nat) : Real :=
  match N with
  | O => real_zero
  | Datatypes.S k => real_plus (sumR f k) (f k)
  end.

End Carriers.

(* ===================================================================== *)
(* Section 2. Craft artifacts: Bishop-form arithmetic helpers.            *)
(* ===================================================================== *)

Section Craft.

(* H3a. real_le_b is reflexive (via the Or-form and the one-way bridge).  *)
Lemma gaC1_03_le_b_refl : forall x : Real, real_le_b x x.
Proof.
  intro x. apply real_le_to_le_b.
  apply RealSetoid.real_eq_le. apply real_eq_refl.
Qed.

(* H3b. real_le_b transports on the right through real_eq (margin kept). *)
Lemma gaC1_03_le_b_eq_r : forall x y z : Real,
  real_le_b x y -> real_eq y z -> real_le_b x z.
Proof.
  intros x y z H Hxyz. unfold real_le_b in *. intros e He.
  apply (real_lt_eq_lt _ _ _ (H e He)).
  apply RealSetoid.real_eq_plus_compat.
  - exact Hxyz.
  - apply real_eq_refl.
Qed.

(* H3b'. Bishop-form transports on the left through real_eq. *)
Lemma gaC1_03_le_b_eq_l : forall x y z : Real,
  real_eq x y -> real_le_b y z -> real_le_b x z.
Proof.
  intros x y z Hxy Hyz. unfold real_le_b in *. intros e He.
  exact (real_eq_lt_lt _ _ _ Hxy (Hyz e He)).
Qed.

(* H3c0. The ring shift (1+t)+(−1) == t. *)
Lemma gaC1_03_linear_shift : forall t : Real,
  real_eq (real_plus (real_plus real_one t) (real_opp real_one)) t.
Proof.
  intro t. apply real_eq_of_zero_diff. intro n.
  destruct t as [v Hv].
  cbn [real_plus real_opp real_one projT1].
  ring.
Qed.

(* H3c. ln(1+t) <= t in Bishop form (from the linear bound). *)
Lemma gaC1_03_log_le_t : forall (t : Real) (Ht : real_lt real_zero t),
  real_le_b (real_log (real_plus real_one t)
               (real_plus_positive real_one t real_lt_zero_one Ht)) t.
Proof.
  intros t Ht.
  exact (gaC1_03_le_b_eq_r _ _ _
    (real_log_le_linear_B (real_plus real_one t)
       (real_plus_positive real_one t real_lt_zero_one Ht))
    (gaC1_03_linear_shift t)).
Qed.

(* H3d. Bishop-form plus-compatibility: the standard half-margin argument *)
(*      with the literal 1/2 through the Q->Real const bridge.            *)
Lemma gaC1_03_le_b_plus_compat : forall x y z w : Real,
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

End Craft.

(* ===================================================================== *)
(* Section 3. C1: the finite product expansion (equality).                *)
(* ===================================================================== *)

Section ProductExpansion.

(* C1. ln(prod a_i) == sum ln a_i for the nat-iterated product. *)
Lemma gaC1_03_log_prod :
  forall (N : nat) (a : nat -> Real) (Ha : forall i, real_lt real_zero (a i)),
    real_eq (real_log (projT1 (g3_prod a Ha N)) (projT2 (g3_prod a Ha N)))
            (sumR (fun i => real_log (a i) (Ha i)) N).
Proof.
  intro N. induction N as [| N IH]; intros a Ha.
  - cbn [g3_prod sumR projT1 projT2].
    apply real_log_one.
  - cbn [g3_prod sumR].
    destruct (g3_prod a Ha N) as [p Hp] eqn:E.
    specialize (IH a Ha). rewrite E in IH. cbn [projT1 projT2] in IH.
    apply (real_eq_trans _
      (real_plus (real_log p Hp) (real_log (a N) (Ha N)))).
    + exact (real_log_mult p (a N) Hp (Ha N)).
    + apply RealSetoid.real_eq_plus_compat.
      * exact IH.
      * apply real_eq_refl.
Qed.

End ProductExpansion.

(* ===================================================================== *)
(* Section 4. C2: the positive-term telescope (Bishop form).              *)
(* ===================================================================== *)

Section Telescope.

(* C2. ln(prod (1+t_i)) <= sum t_i in Bishop form. *)
Lemma gaC1_03_telescope :
  forall (N : nat) (t : nat -> Real) (Ht : forall i, real_lt real_zero (t i)),
    real_le_b (real_log (projT1 (g3_prod (fun i => real_plus real_one (t i))
                                (fun i => real_plus_positive real_one (t i)
                                   real_lt_zero_one (Ht i)) N))
              (projT2 (g3_prod (fun i => real_plus real_one (t i))
                         (fun i => real_plus_positive real_one (t i)
                            real_lt_zero_one (Ht i)) N)))
            (sumR t N).
Proof.
  intro N. induction N as [| N IH]; intros t Ht.
  - cbn [g3_prod sumR projT1 projT2].
    exact (gaC1_03_le_b_eq_r _ _ _ (gaC1_03_le_b_refl _)
             (real_log_one real_lt_zero_one)).
  - cbn [g3_prod sumR].
    destruct (g3_prod (fun i => real_plus real_one (t i))
                (fun i => real_plus_positive real_one (t i)
                   real_lt_zero_one (Ht i)) N) as [p Hp] eqn:E.
    specialize (IH t Ht). rewrite E in IH. cbn [projT1 projT2] in IH.
    exact (gaC1_03_le_b_eq_l _ _ _
      (real_log_mult p (real_plus real_one (t N)) Hp
        (real_plus_positive real_one (t N) real_lt_zero_one (Ht N)))
      (gaC1_03_le_b_plus_compat _ _ _ _
        IH (gaC1_03_log_le_t (t N) (Ht N)))).
Qed.

End Telescope.

(* ===================================================================== *)
(* Section 5. C3: nonnegative tail sums (the psi-theta dyadic carrier).   *)
(* ===================================================================== *)

Section TailSum.

(* C3. sumR of positive terms is nonnegative in Bishop form. *)
Lemma gaC1_03_sumR_nonneg :
  forall (N : nat) (t : nat -> Real) (Ht : forall i, real_lt real_zero (t i)),
    real_le_b real_zero (sumR t N).
Proof.
  intro N. induction N as [| N IH]; intros t Ht.
  - apply gaC1_03_le_b_refl.
  - cbn [sumR]. specialize (IH t Ht).
    exact (gaC1_03_le_b_plus_compat _ _ _ _ IH
      (real_le_to_le_b _ _ (@inl (real_lt real_zero (t N))
                              (real_eq real_zero (t N)) (Ht N)))).
Qed.

End TailSum.
