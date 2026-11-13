(* ConstructiveWorld-Main - Pade n=1 denominator sign, boxed edition. *)

(** * UpReqPadeSign_a: boxed edition of the Pade n=1 sign node.

    Mission.  Boxed-face edition of the Pade denominator-sign node at
      n = 1: den(x) is the alternating sum sum_upto (Datatypes.S n)
      (fun k => q_pow (-1) k * (pade_coeff n k * q_pow x k)), at n = 1
      reading Q_1(x) = 1 - x/2, positive on 0 < x < 2.  Statements:
      [pds_den0_pos] n = 0 denominator positive; [pds_sum2] two-term
      split; [pds_c11] linear coefficient one half; [pds_den1_expl]
      explicit shape Q_1(x) == 1 + (-(1/2)) * x; [pds_qlt0_eq_r] Qeq
      transport leg for strict positivity (one hop onto the library
      monotonicity leg); [pds_den1_pos] main statement 0 < x < 2
      implies 0 < Q_1(x) via the product shape (1/2) * (2 - x).  The
      three closed numerical companions live in UpReqPadeSign_a_cert;
      one-hop machine reductions are re-closed definitionally.
    Dependencies.  S01 through S03 (library face), UpReqPadeExp_dep5
      (seat-local spine edition, body byte-identical, requires
      reduced to the library face this node loads), UpReqPadeQLeg,
      stdlib QArith, Arith, Lia, Setoid.
    References.  Statement roster conservation: every Lemma statement
      line is byte-identical to the library edition UpReqPadeSign; no
      new library face, no moved quantifier bounds.
    Constructivity.  Set-carried; QltT statements are Id-of-bool
      shaped; Prop appears only as the bridge inside proofs, never in
      carried data; the Qeq-penetration wall is bypassed by reducing
      the alternating sum at the constructors and finishing linearly.
    Build.  coqc -q -native-compiler no over the l0_local plus build
      loadpath roots (opam93 9.3.0, cpu-guard wrapped, 96-band).
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp_dep5.
Require Import UpReqPadeQLeg.
Require Import UpReqPadeSign_a_cert.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeSignQ.

(* ===== S1 base: the n = 0 positivity instance ===== *)

(* The n = 0 denominator is the unit (cert face pds_den0_one), so the
   boolean comparison reduces over the neutral x; the closure here is
   definitional reduction on the same term, without the machine
   word-face. *)
Lemma pds_den0_pos : forall x : Q, QltT 0 (pade_den 0 x).
Proof.
  intro x. unfold QltT. cbv. reflexivity.
Qed.

(* ===== S2 main face: n = 1 denominator positivity ===== *)

(* Two-term split: sum_upto (S 1) f == f 0 + f 1 (left fold with the
   high index behind; two iota steps and the right-unit law; the
   exponent slots of f carry %nat so numeric literals stay in the nat
   scope). *)
Lemma pds_sum2 : forall f : nat -> Q,
  sum_upto (Datatypes.S 1%nat) f == f 0%nat + f 1%nat.
Proof.
  intro f. cbn [sum_upto]. cbv beta. ring.
Qed.

(* Closed coefficient anchor of the linear term, one half. *)
Lemma pds_c11 : pade_coeff 1 1%nat == (1#2)%Q.
Proof. cbv. reflexivity. Qed.

(* Explicit product shape: Q_1(x) == 1 + (-(1/2)) * x.  Route: split
   by pds_sum2, change the index-driven power facts at the exponent
   slots, rewrite with the closed coefficient anchors, finish by ring
   (the additive inverse stays atomic inside the product shape). *)
Lemma pds_den1_expl : forall x : Q, pade_den 1 x == 1%Q + (- (1#2)%Q) * x.
Proof.
  intro x. unfold pade_den.
  setoid_rewrite pds_sum2. cbv beta.
  change (q_pow (- 1)%Q 0%nat) with 1%Q.
  change (q_pow (- 1)%Q 1%nat) with (-1)%Q.
  change (q_pow x 0%nat) with 1%Q.
  change (q_pow x 1%nat) with (x * 1)%Q.
  setoid_rewrite pds_c10.
  setoid_rewrite pds_c11.
  ring.
Qed.

(* Qeq right-transport leg (minimal bridge of this node): a == b moves
   0 < a to 0 < b.  One explicit hop onto the library Q monotonicity
   leg (Z multiplication monotonicity assembled explicitly, linear
   finish), erasing the micromega environment closure. *)
Lemma pds_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* Main statement: 0 < x < 2 implies 0 < Q_1(x) = 1 - x/2.  Route:
   transport to the explicit product shape (1/2) * (2 - x) - two
   positive factors by the product rule; 0 < 2 - x from x < 2 by the
   strict-subtraction characterization (stdlib Qlt_minus_iff). *)
Lemma pds_den1_pos : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1 x).
Proof.
  intros x H0 H2.
  apply QltT_to_Qlt in H2.
  apply Qlt_to_QltT.
  apply (pds_qlt0_eq_r ((1#2)%Q * (2 + - x)%Q) (pade_den 1 x)).
  - apply (Qeq_trans ((1#2)%Q * (2 + - x)%Q) (1%Q + (- (1#2)%Q) * x) (pade_den 1 x)).
    + ring.
    + apply Qeq_sym. apply pds_den1_expl.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. simpl. lia.
    + apply (proj1 (Qlt_minus_iff x (2#1))). exact H2.
Qed.

End PadeSignQ.

Print Assumptions pds_qlt0_eq_r.