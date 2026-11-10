(* ConstructiveWorld-Main - the power-series coefficient carrier: the
   nth-coefficient take-item machine of the local expansion layer. *)

(** * GaC2_12_CauchyCoeffEst_a: the local-expansion sequence carrier
      and the nth-coefficient take-item machine.

    Mission.  Node C2-12 machine cluster, piece a.  Defines the
      pointwise local-expansion carrier [gaC12_local_exp_seq] packing
      the full coefficient sequence [nat -> Cx] with an explicit
      quadratic remainder face; the five-argument projector
      [gaC12_nth_coeff] (the nth_coeff supply form of the Cauchy
      coefficient estimate, shape-aligned with the C2-11 [deriv1]
      carrier) and the first-order projection [gaC12_deriv1]; the
      slot truncation [gaC12_slots_of_seq] realizing the C2-11
      three-slot carrier as the truncation of this sequence carrier
      (the monotone-shrink direction of the L14 obligation), with the
      slot-form first-order projection [gaC12_deriv1_slots] and its
      alignment face [gaC12_deriv1_slots_of_seq]; and the constant
      kit of the cauchy_est_n consumption contract: the real square
      [gaC12_sq], the natural power [gaC12_rnatpow] on the real line
      (the rpow R n carrier) with its positivity face
      [gaC12_rnatpow_pos] and its first-power face
      [gaC12_rnatpow_one], the closed coefficient constant [gaC12_Cn]
      (2^n embedded by iterated [real_const 2] products) with its
      positivity face [gaC12_Cn_pos], the squared constant
      [gaC12_Cn_sq], the positive-argument division [gaC12_rdiv],
      and the (1 <= n)/NatLe bridge [gaC12_natle_one_lift].  Every
      named construction is Set-carried; zero Sections; zero
      admitted goals.

    Dependencies.  Stdlib [QArith.QArith].  Requires [S01_BaseRing]
      (the Set-sorted pair former), [S02_CauchyComplete],
      [S03_QExp] ([real_inv_pos]), [S07_RealSetoidExpLog] (the
      positivity and order faces), [CxRealPairCore],
      [CxRealPairExpLog], [GaC1_Iface_Cx] (the C1-14/15/16/17 stems
      via the slice interface), [GaC1_Iface_Real] (the C1-05/06
      real-power-root and order faces via the slice interface).

    References.  drafts_C2.md C2.12 statement sketch (cauchy_est_n1
      and cauchy_est_n, obligation L16: the C_n closed form and the
      rpow R n carrier; deriv1/nth_coeff same-source with C2-11 L14)
      and the registered proposed-name rule of drafts_C2.md:1320:
      these carrier shapes are the C1-15 output alignment target.
      The sequence carrier is a conservative superset of the C2-11
      three-slot [local_exp_disk] (GaC2_11_MaxModulusDisk.v:102-110,
      the L14 obligation form subject to the wave-end cross-check)
      and derives that slot form by [gaC12_slots_of_seq].  A machine
      cluster piece landing before its consolidating stem follows the
      GaC2_Iface_Eta.v:25-26 precedent.  The natural power is cast
      here as an explicit Fixpoint: the tree's [c_powq]
      (GaC2_01_DirichletPartialSum.v:187) is the n^(-s) power of the
      eta denominator carrier, not a general R^n, and is not
      consumed.  Ahlfors Ch.2-3 the classical Cauchy coefficient
      estimate (statement architecture only; no proof object
      transcribed).

    Constructivity.  All statements are Set-sorted (sigT carriers,
      [real_lt]/[real_le]/[c_eq] predicates, [S01_BaseRing.And]
      pairs); the coefficient sequence is a plain function
      [nat -> Cx] inside [sigT]; no Section wrappers, no premise slots,
      zero assumed constants, zero admitted goals; every proof closes
      under the global context.

    Build.  [coqc -native-compiler no -q -Q <certified vo tree> ""
      -Q <build dir> "" GaC2_12_CauchyCoeffEst_a.v] from the flat
      build directory; acceptance via 50_toolkit/accept_node.py
      (six-chain gate), thermal-guard wrapped. *)

Require S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S07_RealSetoidExpLog.
Require Import CxRealPairCore.
Require Import CxRealPairExpLog.
Require Import GaC1_Iface_Cx.
Require Import GaC1_Iface_Real.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(* Section 1. The disk predicate and the two expansion carriers.         *)
(* ===================================================================== *)

Definition gaC12_closed_disk (z c : Cx) (R : Real) : Set :=
  real_le (c_norm_sq (c_plus z (c_opp c))) (real_mult R R).

(* The canonical carrier: at every point of the closed disk a full
   coefficient sequence with a quadratic remainder face.  The 0-th
   coefficient equals the value; the quadratic remainder face is
   stated against the first coefficient; the coefficients of order
   two and beyond are packed here without constraints of their own
   (their bounds are the Cauchy estimate's output, not its input). *)
Definition gaC12_local_exp_seq (g : Cx -> Cx) (c : Cx) (R : Real) : Set :=
  forall p : Cx, gaC12_closed_disk p c R ->
    sigT (fun a : nat -> Cx => sigT (fun T2 : Real =>
      S01_BaseRing.And (c_eq (a 0%nat) (g p))
      (S01_BaseRing.And (real_lt real_zero T2)
        (forall w : Cx, real_le (c_norm_sq w) (real_mult R R) ->
          real_le (c_norm_sq (c_plus (c_plus (g (c_plus p w)) (c_opp (a 0%nat)))
                                     (c_opp (c_mult (a 1%nat) w))))
                  (real_mult (real_mult (c_norm_sq w) (c_norm_sq w)) T2))))).

(* The C2-11 three-slot carrier shape (GaC2_11_MaxModulusDisk.v
   lines 102-110), restated under the gaC12 prefix for the
   truncation face. *)
Definition gaC12_local_exp_slots (g : Cx -> Cx) (c : Cx) (R : Real) : Set :=
  forall p : Cx, gaC12_closed_disk p c R ->
    sigT (fun a0 : Cx => sigT (fun a1 : Cx => sigT (fun Tmaj : Real =>
      S01_BaseRing.And (c_eq a0 (g p))
      (S01_BaseRing.And (real_lt real_zero Tmaj)
        (forall w : Cx, real_le (c_norm_sq w) (real_mult R R) ->
          real_le (c_norm_sq (c_plus (c_plus (g (c_plus p w)) (c_opp a0))
                                     (c_opp (c_mult a1 w))))
                  (real_mult (real_mult (c_norm_sq w) (c_norm_sq w)) Tmaj)))))).

(* ===================================================================== *)
(* Section 2. The projectors and the truncation face.                    *)
(* ===================================================================== *)

Definition gaC12_nth_coeff (n : nat) (g : Cx -> Cx) (p c : Cx) (R : Real)
           (Hl : gaC12_local_exp_seq g c R) (Hp : gaC12_closed_disk p c R) : Cx :=
  projT1 (Hl p Hp) n.

Definition gaC12_deriv1 (g : Cx -> Cx) (p c : Cx) (R : Real)
           (Hl : gaC12_local_exp_seq g c R) (Hp : gaC12_closed_disk p c R) : Cx :=
  gaC12_nth_coeff 1%nat g p c R Hl Hp.

Definition gaC12_deriv1_slots (g : Cx -> Cx) (p c : Cx) (R : Real)
           (Hl : gaC12_local_exp_slots g c R) (Hp : gaC12_closed_disk p c R) : Cx :=
  projT1 (projT2 (Hl p Hp)).

Lemma gaC12_nth_coeff_zero_value :
  forall (g : Cx -> Cx) (p c : Cx) (R : Real)
         (Hl : gaC12_local_exp_seq g c R) (Hp : gaC12_closed_disk p c R),
  c_eq (gaC12_nth_coeff 0%nat g p c R Hl Hp) (g p).
Proof.
  intros g p c R Hl Hp.
  unfold gaC12_nth_coeff.
  destruct (Hl p Hp) as [a [T2 [Ha0 Hrest]]].
  exact Ha0.
Qed.

Lemma gaC12_deriv1_is_nth1 :
  forall (g : Cx -> Cx) (p c : Cx) (R : Real)
         (Hl : gaC12_local_exp_seq g c R) (Hp : gaC12_closed_disk p c R),
  c_eq (gaC12_deriv1 g p c R Hl Hp) (gaC12_nth_coeff 1%nat g p c R Hl Hp).
Proof.
  intros g p c R Hl Hp. apply c_eq_refl.
Qed.

Lemma gaC12_slots_of_seq : forall (g : Cx -> Cx) (c : Cx) (R : Real)
                             (Hl : gaC12_local_exp_seq g c R),
  gaC12_local_exp_slots g c R.
Proof.
  intros g c R Hl p Hp.
  destruct (Hl p Hp) as [a [T2 [Ha0 [HT2 Hrem]]]].
  exact (existT _ (a 0%nat)
           (existT _ (a 1%nat)
              (existT _ T2 (pair Ha0 (pair HT2 Hrem))))).
(* Transparent on purpose: the truncation is a witness construction
   computed from the sequence witness; consumers unfold it. *)
Defined.

Lemma gaC12_deriv1_slots_of_seq :
  forall (g : Cx -> Cx) (p c : Cx) (R : Real)
         (Hl : gaC12_local_exp_seq g c R) (Hp : gaC12_closed_disk p c R),
  c_eq (gaC12_deriv1_slots g p c R (gaC12_slots_of_seq g c R Hl) Hp)
       (gaC12_deriv1 g p c R Hl Hp).
Proof.
  intros g p c R Hl Hp.
  destruct (Hl p Hp) as [a [T2 [Ha0 [HT2 Hrem]]]] eqn:Hlpp.
  unfold gaC12_deriv1_slots, gaC12_slots_of_seq.
  cbv beta.
  rewrite Hlpp.
  unfold gaC12_deriv1, gaC12_nth_coeff.
  rewrite Hlpp.
  cbv beta.
  cbn [projT1 projT2].
  apply c_eq_refl.
Qed.

(* ===================================================================== *)
(* Section 3. The cauchy_est_n constant kit.                             *)
(* ===================================================================== *)

Definition gaC12_sq (x : Real) : Real := real_mult x x.

Fixpoint gaC12_rnatpow (R : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | S k => real_mult (gaC12_rnatpow R k) R
  end.

Lemma gaC12_real_one_pos : real_lt real_zero real_one.
Proof.
  apply (real_lt_eq_lt real_zero (real_const 1) real_one).
  - apply g06_const_pos. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
  - exact g06_const_one.
Qed.

Lemma gaC12_two_pos : real_lt real_zero (real_const 2).
Proof.
  apply g06_const_pos. apply Qlt_to_QltT. unfold Qlt. simpl. lia.
Qed.

Lemma gaC12_rnatpow_pos : forall (R : Real) (n : nat),
  real_lt real_zero R -> real_lt real_zero (gaC12_rnatpow R n).
Proof.
  intros R n HR. induction n as [| k IH].
  - exact gaC12_real_one_pos.
  - exact (real_mult_positive _ _ IH HR).
Qed.

Lemma gaC12_rnatpow_one : forall R : Real,
  real_eq (gaC12_rnatpow R 1%nat) R.
Proof.
  intro R.
  exact (real_eq_trans _ _ _ (real_mult_comm real_one R) (real_mult_one R)).
Qed.

Fixpoint gaC12_Cn (n : nat) : Real :=
  match n with
  | O => real_one
  | S k => real_mult (real_const 2) (gaC12_Cn k)
  end.

Definition gaC12_Cn_sq (n : nat) : Real := gaC12_sq (gaC12_Cn n).

Lemma gaC12_Cn_pos : forall n : nat, real_lt real_zero (gaC12_Cn n).
Proof.
  intro n. induction n as [| k IH].
  - exact gaC12_real_one_pos.
  - exact (real_mult_positive _ _ gaC12_two_pos IH).
Qed.

Definition gaC12_rdiv (M R : Real) (HR : real_lt real_zero R) : Real :=
  real_mult M (real_inv_pos R HR).

Lemma gaC12_natle_one_lift : forall n : nat, (1 <= n)%nat -> S01_BaseRing.NatLe 1 n.
Proof.
  intros n Hn. exact (S01_BaseRing.NatLe_lift 1 n Hn).
Qed.
