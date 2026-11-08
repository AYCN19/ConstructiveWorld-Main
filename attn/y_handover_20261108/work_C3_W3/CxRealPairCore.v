(* ========================================================================= *)
(* CxRealPairCore.v                                                          *)
(*                                                                           *)
(* Mission: the field of complex numbers as pairs of Cauchy reals, with the  *)
(*   full ring algebra, conjugation, and the squared modulus, built on the   *)
(*   constructive real line of S02_CauchyComplete.                           *)
(* Dependencies: S01_BaseRing, S02_CauchyComplete.                           *)
(* References: mirrors the standard complex-field algebra rebuilt on the     *)
(*   constructive Cauchy real line; no classical principles are used and     *)
(*   the standard library Reals and Complex libraries are not imported.      *)
(* Constructivity: every named construction is carried by Set; all           *)
(*   predicates are Set-sorted (c_eq, real_eq, real_lt, QltT); every         *)
(*   statement is built from Set-sorted connectives; the development is      *)
(*   closed under the global context; every definition is transparent.       *)
(* Build: coqc -native-compiler no -q -Q <certified vo tree> "" -Q <dir> ""  *)
(*   CxRealPairCore.v, wrapped by cpu_guard v3.                              *)
(* ========================================================================= *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia QArith.Qminmax.

(* ==== Section 1. The complex carrier, its equality, and its operations ==== *)

Definition Cx : Set := Real * Real.

Definition cRe (z : Cx) : Real := fst z.

Definition cIm (z : Cx) : Real := snd z.

Definition c_eq (z w : Cx) : Set :=
  And (real_eq (cRe z) (cRe w)) (real_eq (cIm z) (cIm w)).

Definition c_zero : Cx := (real_zero, real_zero).

Definition c_one : Cx := (real_one, real_zero).

Definition c_of_Q (a b : Q) : Cx := (real_const a, real_const b).

Definition c_plus (z w : Cx) : Cx :=
  (real_plus (cRe z) (cRe w), real_plus (cIm z) (cIm w)).

Definition c_opp (z : Cx) : Cx := (real_opp (cRe z), real_opp (cIm z)).

Definition c_mult (z w : Cx) : Cx :=
  (real_plus (real_mult (cRe z) (cRe w)) (real_opp (real_mult (cIm z) (cIm w))),
   real_plus (real_mult (cRe z) (cIm w)) (real_mult (cIm z) (cRe w))).

Definition c_conj (z : Cx) : Cx := (cRe z, real_opp (cIm z)).

Definition c_norm_sq (z : Cx) : Real :=
  real_plus (real_mult (cRe z) (cRe z)) (real_mult (cIm z) (cIm z)).

Lemma c_eq_refl : forall z : Cx, c_eq z z.
Proof.
  intro z. unfold c_eq. split.
  - apply real_eq_refl.
  - apply real_eq_refl.
Qed.

Lemma c_eq_sym : forall z w : Cx, c_eq z w -> c_eq w z.
Proof.
  intros z w H. unfold c_eq in *. split.
  - apply real_eq_sym. apply H.
  - apply real_eq_sym. apply H.
Qed.

Lemma c_eq_trans : forall z w u : Cx, c_eq z w -> c_eq w u -> c_eq z u.
Proof.
  intros z w u Hzw Hwu. unfold c_eq in Hzw, Hwu. split.
  - apply (real_eq_trans (cRe z) (cRe w) (cRe u)).
    + apply Hzw.
    + apply Hwu.
  - apply (real_eq_trans (cIm z) (cIm w) (cIm u)).
    + apply Hzw.
    + apply Hwu.
Qed.

(* ==== Section 2. Pointwise faces of the operations ==== *)

Lemma real_zero_pt : forall n : nat, projT1 real_zero n == 0.
Proof. intro n. reflexivity. Qed.

Lemma real_one_pt : forall n : nat, projT1 real_one n == 1.
Proof. intro n. reflexivity. Qed.

Lemma cRe_zero_pt : forall n : nat, projT1 (cRe c_zero) n == 0.
Proof. intro n. reflexivity. Qed.

Lemma cIm_zero_pt : forall n : nat, projT1 (cIm c_zero) n == 0.
Proof. intro n. reflexivity. Qed.

Lemma cRe_one_pt : forall n : nat, projT1 (cRe c_one) n == 1.
Proof. intro n. reflexivity. Qed.

Lemma cIm_one_pt : forall n : nat, projT1 (cIm c_one) n == 0.
Proof. intro n. reflexivity. Qed.

Lemma cRe_of_Q_pt : forall (a b : Q) (n : nat), projT1 (cRe (c_of_Q a b)) n == a.
Proof. intros a b n. reflexivity. Qed.

Lemma cIm_of_Q_pt : forall (a b : Q) (n : nat), projT1 (cIm (c_of_Q a b)) n == b.
Proof. intros a b n. reflexivity. Qed.

Lemma cRe_plus_pt : forall (z w : Cx) (n : nat),
  projT1 (cRe (c_plus z w)) n == projT1 (cRe z) n + projT1 (cRe w) n.
Proof.
  intros [a b] [c d] n. destruct a as [u Hu]. destruct c as [v Hv]. reflexivity.
Qed.

Lemma cIm_plus_pt : forall (z w : Cx) (n : nat),
  projT1 (cIm (c_plus z w)) n == projT1 (cIm z) n + projT1 (cIm w) n.
Proof.
  intros [a b] [c d] n. destruct b as [u Hu]. destruct d as [v Hv]. reflexivity.
Qed.

Lemma cRe_opp_pt : forall (z : Cx) (n : nat),
  projT1 (cRe (c_opp z)) n == - projT1 (cRe z) n.
Proof.
  intros [a b] n. destruct a as [u Hu]. reflexivity.
Qed.

Lemma cIm_opp_pt : forall (z : Cx) (n : nat),
  projT1 (cIm (c_opp z)) n == - projT1 (cIm z) n.
Proof.
  intros [a b] n. destruct b as [u Hu]. reflexivity.
Qed.

Lemma cRe_mult_pt : forall (z w : Cx) (n : nat),
  projT1 (cRe (c_mult z w)) n ==
  projT1 (cRe z) n * projT1 (cRe w) n - projT1 (cIm z) n * projT1 (cIm w) n.
Proof.
  intros [a b] [c d] n.
  destruct a as [u Hu]. destruct b as [ub Hb].
  destruct c as [v Hv]. destruct d as [vd Hd].
  reflexivity.
Qed.

Lemma cIm_mult_pt : forall (z w : Cx) (n : nat),
  projT1 (cIm (c_mult z w)) n ==
  projT1 (cRe z) n * projT1 (cIm w) n + projT1 (cIm z) n * projT1 (cRe w) n.
Proof.
  intros [a b] [c d] n.
  destruct a as [u Hu]. destruct b as [ub Hb].
  destruct c as [v Hv]. destruct d as [vd Hd].
  reflexivity.
Qed.

Lemma cRe_conj_pt : forall (z : Cx) (n : nat),
  projT1 (cRe (c_conj z)) n == projT1 (cRe z) n.
Proof. intros [a b] n. reflexivity. Qed.

Lemma cIm_conj_pt : forall (z : Cx) (n : nat),
  projT1 (cIm (c_conj z)) n == - projT1 (cIm z) n.
Proof.
  intros [a b] n. destruct b as [u Hu]. reflexivity.
Qed.

Lemma c_norm_sq_pt : forall (z : Cx) (n : nat),
  projT1 (c_norm_sq z) n ==
  projT1 (cRe z) n * projT1 (cRe z) n + projT1 (cIm z) n * projT1 (cIm z) n.
Proof.
  intros [a b] n. destruct a as [u Hu]. destruct b as [ub Hb]. reflexivity.
Qed.

(* ==== Section 3. Ring laws on the complex pairs ==== *)
Lemma c_plus_comm : forall z w : Cx, c_eq (c_plus z w) (c_plus w z).
Proof.
  intros [a b] [c d].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_plus_assoc : forall z w u : Cx,
  c_eq (c_plus z (c_plus w u)) (c_plus (c_plus z w) u).
Proof.
  intros [a b] [c d] [e f].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd];
    destruct e as [ue He]; destruct f as [uf Hf].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_plus_zero : forall z : Cx, c_eq (c_plus c_zero z) z.
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_plus_opp : forall z : Cx, c_eq (c_plus z (c_opp z)) c_zero.
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_mult_comm : forall z w : Cx, c_eq (c_mult z w) (c_mult w z).
Proof.
  intros [a b] [c d].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_mult_assoc : forall z w u : Cx,
  c_eq (c_mult z (c_mult w u)) (c_mult (c_mult z w) u).
Proof.
  intros [a b] [c d] [e f].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd];
    destruct e as [ue He]; destruct f as [uf Hf].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_mult_one : forall z : Cx, c_eq (c_mult c_one z) z.
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_mult_zero : forall z : Cx, c_eq (c_mult c_zero z) c_zero.
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_distrib : forall z w u : Cx,
  c_eq (c_mult z (c_plus w u)) (c_plus (c_mult z w) (c_mult z u)).
Proof.
  intros [a b] [c d] [e f].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd];
    destruct e as [ue He]; destruct f as [uf Hf].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

(* ==== Section 4. Conjugation ==== *)

Lemma c_conj_involutive : forall z : Cx, c_eq (c_conj (c_conj z)) z.
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_conj_plus : forall z w : Cx,
  c_eq (c_conj (c_plus z w)) (c_plus (c_conj z) (c_conj w)).
Proof.
  intros [a b] [c d].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_conj_mult : forall z w : Cx,
  c_eq (c_conj (c_mult z w)) (c_mult (c_conj z) (c_conj w)).
Proof.
  intros [a b] [c d].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

Lemma c_conj_opp : forall z : Cx, c_eq (c_conj (c_opp z)) (c_opp (c_conj z)).
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  unfold c_eq. split; apply real_eq_of_zero_diff; intro n; simpl; ring.
Qed.

(* ==== Section 5. Squared modulus and the rational bridge ==== *)

Lemma c_norm_sq_conj : forall z : Cx, real_eq (c_norm_sq (c_conj z)) (c_norm_sq z).
Proof.
  intros [a b].
  destruct a as [ua Ha]; destruct b as [ub Hb].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

Lemma c_norm_sq_mul : forall z w : Cx,
  real_eq (c_norm_sq (c_mult z w)) (real_mult (c_norm_sq z) (c_norm_sq w)).
Proof.
  intros [a b] [c d].
  destruct a as [ua Ha]; destruct b as [ub Hb];
    destruct c as [uc Hc]; destruct d as [ud Hd].
  apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

Lemma c_norm_sq_of_Q : forall a b : Q,
  real_eq (c_norm_sq (c_of_Q a b)) (real_const (a * a + b * b)).
Proof.
  intros a b. apply real_eq_of_zero_diff. intro n. simpl. ring.
Qed.

Lemma c_norm_sq_Q_pos_bridge : forall a b e : Q,
  QltT 0 e -> QltT e (a * a + b * b) ->
  real_lt real_zero (c_norm_sq (c_of_Q a b)).
Proof.
  intros a b e H0e He. exists e. split.
  - exact H0e.
  - exists 0%nat. intros n Hn. simpl.
    assert (Hs : a * a + b * b - 0 == a * a + b * b) by ring.
    assert (Hcmp : (e ?= a * a + b * b - 0) = (e ?= a * a + b * b))
      by (apply Qcompare_comp; [ apply Qeq_refl | exact Hs ]).
    unfold QltT, Qlt_bool. rewrite Hcmp. exact He.
Qed.
