(* ConstructiveWorld-Main - DTPT_Entropy_h: gate-clean LINT-6 split piece 8/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_h.

    Mission.  Q order/division tools (built where the stdlib shapes.
      Carries source lines 2049-2307 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f, DTPT_Entropy_g (linear Require Import chain).
    References.  Boxed face ConstructiveWorld_Live/DTPT_Entropy.v (231/231 statement texts
      mechanically verified verbatim against this cast); seat_wash80 setlive_probe_world.
    Constructivity.  Zero axioms, nothing left open, no classical logic; Set-carried
      statements; every proof closes with Qed.  Numerical check instances live in
      DTPT_Entropy_cert (R2 certificate separation).
    Build.  coqc -native-compiler no -q via cpu_guard_v3 (TempLimit 96), flat work/build face.
 *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Notation S := Datatypes.S.
From Stdlib Require Import Setoid Morphisms.

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Permutation.
Import ListNotations.
Open Scope Q_scope.

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g.

(* ========== Q order/division tools (built where the stdlib shapes
   differ) ========== *)

(* [Qeq] can be rewritten directly into [Qle] goals *)
Lemma qeq_le_l : forall x y : Q, x == y -> QleT' (x) (y).
Proof.
  intros x y H. apply Qle_to_QleT'. rewrite H. apply Qle_refl.
Qed.

(* qn n >= 1 (for n >= 1; via [qadd_le]) *)
Lemma qn_ge1 : forall n : nat, (1 <= n)%nat -> QleT' (1:Q) (qn n).
Proof.
  intros n Hn. apply Qle_to_QleT'. destruct n as [| k].
  - exfalso. lia.
  - simpl.
    pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1)
      (QleT'_to_Qle _ _ (qn_nonneg k))) as HH.
    simpl in HH. exact (QleT'_to_Qle _ _ HH).
Qed.

(* positivity of products of [qn] values (nat-side nonnegative
   multiplication plus monotonicity of [qn]) *)
Lemma qn_mul_pos : forall a b : nat, (0 < a)%nat -> (0 < b)%nat -> QltT (0) (qn a * qn b).
Proof.
  intros a b Ha Hb.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0 (qn a) (qn a * qn b)).
  - apply QltT_to_Qlt. apply qn_pos. exact Ha.
  - assert (Hab : (a <= a * b)%nat).
    { apply (Nat.le_trans a (a * 1) (a * b)).
      - lia.
      - apply Nat.mul_le_mono_l. lia. }
    rewrite <- (qeqT_imp_qeq _ _ (qn_mul a b)).
    apply QleT'_to_Qle. apply qn_le. exact Hab.
Qed.

(* length positivity of a nonempty list (pure nat side; [simpl] only on nat
   goals — on Q goals it would unfold Qlt into Qnum/Qden encodings and
   break the [apply]) *)
Lemma qlen_pos : forall (x : Q) (l : list Q), NatLe 1 (length (x :: l)).
Proof.
  intros x l. apply NatLe_lift.
  change (length (x :: l)) with (S (length l)). lia.
Qed.

(* positivity of products of embedded nonempty-list lengths (the unified Q
   entry of the order chain) *)
Lemma qlen_mul_pos : forall (x : Q) (l : list Q), QltT (0) (qn (length (x :: l)) * qn (length (x :: l))).
Proof.
  intros x l. apply qn_mul_pos;
    [ apply NatLe_drop, qlen_pos | apply NatLe_drop, qlen_pos ].
Qed.

(* same-denominator division is monotone in the numerator (positive
   denominator; positivity of the inverse via [Qinv_lt_0_compat], since the
   stdlib here has no left-compatible le form) *)
Lemma qdiv_ge_num : forall A C B : Q, 0 < B -> C <= A -> QleT' (C / B) (A / B).
Proof.
  intros A C B HB Hle. apply Qle_to_QleT'. unfold Qdiv.
  apply Qmult_le_compat_r.
  - exact Hle.
  - apply (Qlt_le_weak 0 (/ B)). apply (Qinv_lt_0_compat B HB).
Qed.

(* numerator <= denominator gives quotient <= 1 ([Qmult_inv_r] is the
   specialized multiply-out-to-1 form) *)
Lemma qdiv_le_1 : forall A B : Q, A <= B -> 0 < B -> QleT' (A / B) (1).
Proof.
  intros A B Hle HB. apply Qle_to_QleT'. unfold Qdiv.
  assert (Hpos : 0 <= / B)
    by (apply (Qlt_le_weak 0 (/ B)); apply (Qinv_lt_0_compat B HB)).
  assert (Hm : A * / B <= B * / B) by (apply Qmult_le_compat_r; assumption).
  apply (Qle_trans (A * / B) (B * / B) 1 Hm).
  apply QleT'_to_Qle. apply qeq_le_l. apply Qmult_inv_r.
  intro Hc. assert (Hc2 : B == 0) by (rewrite Hc; reflexivity).
  destruct (qpos_neq0 B HB (qeq_imp_qeqT _ _ Hc2)).
Qed.

(* normalization: 1 / P == P / (P * P) (the field side condition is a Qeq
   shape, discharged from the context assumption) *)
Lemma qdiv_norm : forall P : Q, ~ (P == 0) -> ~ (P * P == 0) -> QeqT (1 / P) (P / (P * P)).
Proof.
  intros P HP1 HP2. apply qeq_imp_qeqT. field; assumption.
Qed.

(* order-reversing subtraction (z fixed; unfold Qminus first, then
   [qadd_le], avoiding apply-unification trouble) *)
Lemma qsub_le : forall x y z : Q, x <= y -> QleT' (z - y) (z - x).
Proof.
  intros x y z H. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle. apply (qadd_le z z (- y) (- x)).
  - apply Qle_refl.
  - exact (Qopp_le_compat x y H).
Qed.

(* ========== [nmax]: general nat-indexed maximum with Q values (the dual
   of [nsum]) ========== *)

Fixpoint nmax (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => Nat.max (f y) (nmax f ys)
  end.

Lemma nmax_bound : forall (f : Q -> nat) (l : list Q) (y : Q),
  In y l -> NatLe (f y) ((nmax f l)%nat).
Proof.
  intros f l y Hy. revert Hy.
  induction l as [| z zs IH]; simpl; intros Hy; apply NatLe_lift.
  - destruct Hy.
  - destruct Hy as [Hz | Hy].
    + subst z. apply Nat.le_max_l.
    + apply (Nat.le_trans (f y) (nmax f zs) (Nat.max (f z) (nmax f zs))).
      * apply NatLe_drop. apply IH. exact Hy.
      * apply Nat.le_max_r.
Qed.

Lemma nmax_le_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> NatLe (nmax f l) ((B)%nat).
Proof.
  intros f l B. induction l as [| z zs IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hz : (f z <= B)%nat) by (apply H; left; reflexivity).
    assert (Hzs : NatLe (nmax f zs) B)
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hzs). lia.
Qed.

Lemma nmax_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> Id (nmax f l) (nmax g l).
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H; apply eq_imp_id.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

(* permutation invariance of the general maximum (perm_swap branch closed
   by commutativity of Nat.max) *)
Lemma nmax_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> Id (nmax f l) (nmax f p).
Proof.
  intros f l p H.
  apply eq_imp_id.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

(* ========== frequency complements (the nat-side baseline) ========== *)

(* every member has frequency >= 1 (the false branch of Qeq_bool is closed
   by the contradiction lemma [qeqb_false_neq]) *)
Lemma freq_q_ge1 : forall (x : Q) (l : list Q), In x l -> NatLe (1) ((freq_q x l)%nat).
Proof.
  intros x l Hin. revert Hin.
  induction l as [| y ys IH]; intros Hin; simpl; apply NatLe_lift.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + subst y. destruct (Qeq_bool x x) eqn:Exx.
      * lia.
      * exfalso. apply (qeqb_false_neq x x Exx). reflexivity.
    + destruct (Qeq_bool x y) eqn:Exy.
      * lia.
      * apply NatLe_drop. apply IH. exact Hin.
Qed.

(* lower bound of the general sum (the dual of [nsum_bound]) *)
Lemma nsum_ge_const : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (B <= f x)%nat) -> NatLe (length l * B) ((nsum f l)%nat).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hy : (B <= f y)%nat) by (apply H; left; reflexivity).
    assert (Hys : NatLe (length ys * B) (nsum f ys))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys). lia.
Qed.

(* nat-side baseline core: [sqsum >= length] (pointwise freq >= 1; the
   entry of the Cauchy-Schwarz lower bound) *)
Lemma sqsum_ge_length : forall l : list Q, NatLe (length l) ((sqsum l)%nat).
Proof.
  intros l. unfold sqsum.
  pose proof (nsum_ge_const (fun x => freq_q x l) l 1
                (fun x Hx => NatLe_drop _ _ (freq_q_ge1 x l Hx))) as Hge.
  rewrite Nat.mul_1_r in Hge. exact Hge.
Qed.

(* ========== [collide]: the Renyi-2 / collision-entropy core sum p^2 and
   its bounding theorems (baseline) ========== *)

(* collide l = sum_{x in l} (freq_q x l / n)² = qn (sqsum l) / (qn n * qn n) *)
Definition collide (l : list Q) : Q :=
  qn (sqsum l) / (qn (length l) * qn (length l)).

Lemma collide_zero : QeqT (collide []) (0).
Proof. apply qeq_imp_qeqT.
  assert (Hz : (qn (sqsum []) == 0)%Q).
  { change (qn (nsum (fun x => freq_q x []) []) == 0%Q).
    change (qn 0 == 0%Q).
    reflexivity. }
  unfold collide. unfold Qdiv. rewrite Hz. apply Qmult_0_l.
Qed.

(* upper bound: [collide <= 1] (whole list; [sqsum <= n^2]) *)
Theorem collide_upper : forall l : list Q, QleT' (collide l) (1).
Proof.
  intros l. destruct l as [| x xs].
  - apply Qle_to_QleT'. rewrite (qeqT_imp_qeq _ _ collide_zero).
    apply (Qlt_le_weak 0 1). reflexivity.
  - unfold collide. apply qdiv_le_1.
    + assert (Hle : qn (sqsum (x :: xs))
                    <= qn (length (x :: xs)) * qn (length (x :: xs))).
      { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                         (length (x :: xs)))).
        apply QleT'_to_Qle. apply qn_le. apply NatLe_drop. apply sqsum_le. }
      exact Hle.
    + apply QltT_to_Qlt. apply qlen_mul_pos.
Qed.

(* lower bound: [1/n <= collide] (nonempty; 1/n == n/n^2 by normalization,
   numerator by [sqsum_ge_length]) *)
Theorem collide_lower : forall l : list Q,
  (0 < length l)%nat -> QleT' (1 / qn (length l)) (collide l).
Proof.
  intros l Hl. apply Qle_to_QleT'. destruct l as [| x xs].
  - simpl in Hl. exfalso. lia.
  - unfold collide.
    pose proof (QltT_to_Qlt _ _ (qlen_mul_pos x xs)) as HPP.
    assert (HP2 : ~ (qn (length (x :: xs)) * qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 _ HPP (qeq_imp_qeqT _ _ Hc)). }
    assert (HP1 : ~ (qn (length (x :: xs)) == 0)).
    { intro Hc. destruct (qpos_neq0 (qn (length (x :: xs)))
        (QltT_to_Qlt 0 (qn (length (x :: xs)))
          (qn_pos (length (x :: xs)) (NatLe_drop 1 (length (x :: xs)) (qlen_pos x xs))))
        (qeq_imp_qeqT _ _ Hc)). }
    assert (Hge : (length (x :: xs) <= sqsum (x :: xs))%nat)
      by (apply NatLe_drop; apply sqsum_ge_length).
    assert (Hnum : qn (length (x :: xs)) <= qn (sqsum (x :: xs)))
      by (apply QleT'_to_Qle; apply qn_le; exact Hge).
    rewrite (qeqT_imp_qeq _ _
      (qdiv_norm (qn (length (x :: xs))) HP1 HP2)).
    apply QleT'_to_Qle. apply qdiv_ge_num.
    + exact HPP.
    + exact Hnum.
Qed.

(* permutation invariance (by [sqsum_perm] and [Permutation_length]) *)
Theorem collide_perm : forall l p : list Q,
  Permutation l p -> QeqT (collide l) (collide p).
Proof.
  intros l p H. apply qeq_imp_qeqT. unfold collide.
  destruct (id_sym (sqsum_perm l p H)).
  rewrite (Permutation_length H). reflexivity.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
(* ========== zero-axiom attestation ========== *)
Print Assumptions collide_lower.
Print Assumptions collide_upper.
Print Assumptions collide_perm.
Print Assumptions qlen_pos.
Print Assumptions collide_zero.