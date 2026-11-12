(* ConstructiveWorld-Main - DTPT_Entropy_f: gate-clean LINT-6 split piece 6/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_f.

    Mission.  [qn]: the nat -> Q embedding (self-contained, no Z.of_nat.
      Carries source lines 1347-1697 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e.

(* ========== [qn]: the nat -> Q embedding (self-contained, no Z.of_nat
   dependency) ========== *)

Fixpoint qn (n : nat) : Q :=
  match n with
  | O => 0%Q
  | S k => (1 + qn k)%Q
  end.

Lemma qn_nonneg : forall n : nat, QleT' (0) (qn n).
Proof.
  intro n. induction n as [| k IH]; apply Qle_to_QleT'.
  - apply Qle_refl.
  - simpl. apply QleT'_to_Qle. apply qadd_nonneg.
    + apply (Qlt_le_weak 0 1). reflexivity.
    + apply QleT'_to_Qle. exact IH.
Qed.

Lemma qn_S_pos : forall k : nat, QltT (0) (qn (S k)).
Proof.
  intros k. apply Qlt_to_QltT. simpl. apply (Qlt_le_trans 0 1 (1 + qn k)%Q).
  - reflexivity.
  - pose proof (qadd_le 1 1 0 (qn k) (Qle_refl 1)
      (QleT'_to_Qle _ _ (qn_nonneg k))) as HH.
    simpl in HH. exact (QleT'_to_Qle _ _ HH).
Qed.

Lemma qn_pos : forall n : nat, (0 < n)%nat -> QltT (0) (qn n).
Proof.
  intros n Hn. apply Qlt_to_QltT. destruct n as [| m].
  - exfalso. lia.
  - apply QltT_to_Qlt. apply qn_S_pos.
Qed.

Lemma qn_add : forall a b : nat, QeqT (qn (a + b)%nat) (qn a + qn b).
Proof.
  intros a. induction a as [| a IH]; intros b; apply qeq_imp_qeqT.
  - rewrite Nat.add_0_l. cbn [qn]. rewrite Qplus_0_l. reflexivity.
  - cbn [qn Nat.add]. rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma qn_mul : forall a b : nat, QeqT (qn (a * b)%nat) (qn a * qn b).
Proof.
  intros a. induction a as [| a IH]; intros b; apply qeq_imp_qeqT.
  - simpl. symmetry. apply Qmult_0_l.
  - simpl. rewrite (qeqT_imp_qeq _ _ (qn_add b (a * b))).
    rewrite (qeqT_imp_qeq _ _ (IH b)). ring.
Qed.

Lemma qn_le : forall a b : nat, (a <= b)%nat -> QleT' (qn a) (qn b).
Proof.
  intros a. induction a as [| a IH]; intros b Hle; apply Qle_to_QleT'.
  - apply QleT'_to_Qle. apply qn_nonneg.
  - destruct b as [| b'].
    + exfalso. lia.
    + simpl. apply QleT'_to_Qle. apply (qadd_le 1 1 (qn a) (qn b')).
      * apply Qle_refl.
      * apply QleT'_to_Qle. apply IH. apply (le_S_n _ _ Hle).
Qed.

Lemma qn_inj : forall a b : nat, qn a == qn b -> Id (a) (b).
Proof.
  intros a. induction a as [| a IH]; intros b Heq; apply eq_imp_id.
  - destruct b as [| b'].
    + reflexivity.
    + simpl in Heq. pose proof (qn_S_pos b') as HP. simpl in HP.
      apply QltT_to_Qlt in HP. rewrite <- Heq in HP.
      exfalso. exact (Qlt_irrefl 0 HP).
  - destruct b as [| b'].
    + simpl in Heq. pose proof (qn_S_pos a) as HP. simpl in HP.
      apply QltT_to_Qlt in HP. rewrite Heq in HP.
      exfalso. exact (Qlt_irrefl 0 HP).
    + simpl in Heq.
      rewrite (Qplus_comm 1 (qn a)) in Heq.
      rewrite (Qplus_comm 1 (qn b')) in Heq.
      pose proof (proj1 (Qplus_inj_r (qn a) (qn b') 1) Heq) as H'.
      pose proof (IH b' H') as Hab. destruct (id_sym Hab). reflexivity.
Qed.

(* ========== Q division/subtraction tools (unfold Qminus, then ring; no
   division-premise gaps) ========== *)

Lemma qlt_neq0 : forall y : Q, 0 < y -> y <> 0.
Proof.
  intros y Hpy Heq. rewrite Heq in Hpy. exact (Qlt_irrefl 0 Hpy).
Qed.

Lemma qpos_neq0 : forall y : Q, 0 < y -> Not (QeqT y 0).
Proof.
  intros y Hpy Heq. apply qeqT_imp_qeq in Heq.
  apply (False_rect Empty_set). apply (Qlt_not_eq 0 y Hpy).
  apply (Qeq_sym y 0). exact Heq.
Qed.

(* on this platform the stdlib [Qmult_inv_r] has the shape x * /x == 1
   rather than a cancellation form; a cancellation lemma is built here (the
   field side condition is exactly the Qeq shape ~ (B == 0)) *)
Lemma qmult_inv_cancel_r : forall A B : Q, ~ (B == 0) -> QeqT (A * / B * B) (A).
Proof.
  intros A B HB. apply qeq_imp_qeqT. field. exact HB.
Qed.

Lemma qsub_eq0 : forall a b : Q, a - b == 0 -> QeqT (a) (b).
Proof.
  intros a b H.
  apply qeq_imp_qeqT.
  assert (Ha : a == (a - b) + b).
  { unfold Qminus. ring. }
  rewrite H in Ha. rewrite Qplus_0_l in Ha. exact Ha.
Qed.

(* a zero numerator (including the degenerate zero denominator) gives a
   zero quotient: the case 0/0 == 0 is covered as well *)
Lemma qdiv_zero_num : forall A B : Q, A == 0 -> QeqT (A / B) (0).
Proof.
  intros A B H. apply qeq_imp_qeqT. unfold Qdiv. rewrite H. apply Qmult_0_l.
Qed.

Lemma qdiv_eq0_num : forall A B : Q, 0 < B -> A / B == 0 -> QeqT A 0.
Proof.
  intros A B HB H. apply qeq_imp_qeqT. unfold Qdiv in H.
  assert (HBne : ~ (B == 0)).
  { intro Hb. destruct (qpos_neq0 B HB (qeq_imp_qeqT _ _ Hb)). }
  pose proof (qeqT_imp_qeq _ _ (qmult_inv_cancel_r A B HBne)) as Hcancel.
  rewrite H in Hcancel. rewrite Qmult_0_l in Hcancel.
  apply (Qeq_sym 0 A). exact Hcancel.
Qed.

Lemma qdiv_nonneg : forall A B : Q, 0 <= A -> 0 < B -> QleT' (0) (A / B).
Proof.
  intros A B HA HB. apply Qle_to_QleT'. unfold Qdiv. apply Qmult_le_0_compat.
  - exact HA.
  - apply Qlt_le_weak. apply (Qinv_lt_0_compat B HB).
Qed.

Lemma qnum_zero : forall n s : nat, qn (n * n) == qn s -> QeqT (qn n * qn n - qn s) (0).
Proof.
  intros n s H. apply qeq_imp_qeqT.
  rewrite <- (qeqT_imp_qeq _ _ (qn_mul n n)). rewrite <- H.
  unfold Qminus. apply Qplus_opp_r.
Qed.

Lemma qeqb_false_neq : forall x y : Q, Qeq_bool x y = false -> x <> y.
Proof.
  intros x y H Hxy.
  assert (Ht : Qeq_bool x y = true).
  { apply (proj2 (Qeq_bool_iff x y)). rewrite <- Hxy. apply Qeq_refl. }
  rewrite Ht in H. discriminate H.
Qed.

(* ========== [freq_q]: self-contained frequency counting (decidable by
   Qeq_bool) ========== *)

Fixpoint freq_q (x : Q) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => if Qeq_bool x y then S (freq_q x ys) else freq_q x ys
  end.

Lemma freq_q_le_length : forall (x : Q) (l : list Q), NatLe (freq_q x l) ((length l)%nat).
Proof.
  intros x l. apply NatLe_lift. induction l as [| y ys IH]; simpl.
  - lia.
  - simpl. destruct (Qeq_bool x y); lia.
Qed.

(* baseline: frequencies are additive under concatenation *)
Theorem freq_q_app : forall (x : Q) (l p : list Q), Id (freq_q x (l ++ p)) ((freq_q x l + freq_q x p)%nat).
Proof.
  intros x l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. destruct (Qeq_bool x a); rewrite IH; lia.
Qed.

(* precondition of the main theorem: frequencies are permutation invariant
   (induction on the constructors of Permutation; in the perm_swap branch
   both sides count the same x0, so only the four branches need literal
   reordering, without Qeq_bool symmetry) *)
Theorem freq_q_perm : forall (x : Q) (l p : list Q),
  Permutation l p -> Id (freq_q x l) (freq_q x p).
Proof.
  intros x l p H.
  apply eq_imp_id.
  induction H as [ | y l' p' Hy IH | y z l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. destruct (Qeq_bool x y); rewrite IH; reflexivity.
  - simpl. destruct (Qeq_bool x y); destruct (Qeq_bool x z); reflexivity.
  - rewrite IH1. exact IH2.
Qed.

Lemma freq_q_eq_all : forall (x : Q) (l : list Q),
  (forall z, In z l -> z == x) -> Id (freq_q x l) (length l).
Proof.
  intros x l. induction l as [| y ys IH]; intros H; apply eq_imp_id.
  - reflexivity.
  - assert (Hy : Qeq_bool x y = true).
    { apply (proj2 (Qeq_bool_iff x y)). apply (Qeq_sym y x). apply H.
      left. reflexivity. }
    simpl. rewrite Hy. f_equal.
    destruct (id_sym (IH (fun z Hz => H z (or_intror Hz)))). reflexivity.
Qed.

Lemma freq_q_full_count : forall (x : Q) (l : list Q),
  freq_q x l = length l -> forall y, In y l -> QeqT (y) (x).
Proof.
  intros x l. induction l as [| a l IH]; intros Hcnt y0 Hy0.
  - destruct Hy0.
  - apply qeq_imp_qeqT. destruct Hy0 as [Hy0 | Hy0].
    + subst y0. destruct (Qeq_bool x a) eqn:Hyb.
      * apply (Qeq_sym x a). apply (proj1 (Qeq_bool_iff x a)). exact Hyb.
      * exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
        pose proof (NatLe_drop _ _ (freq_q_le_length x l)) as HL. lia.
    + apply qeqT_imp_qeq. apply IH.
      * destruct (Qeq_bool x a) eqn:Hyb.
        -- simpl in Hcnt. rewrite Hyb in Hcnt. lia.
        -- exfalso. simpl in Hcnt. rewrite Hyb in Hcnt.
           pose proof (NatLe_drop _ _ (freq_q_le_length x l)) as HL. lia.
      * exact Hy0.
Qed.

(* ========== [nsum]: general nat-indexed summation with Q values
   ========== *)

Fixpoint nsum (f : Q -> nat) (l : list Q) : nat :=
  match l with
  | [] => 0%nat
  | y :: ys => (f y + nsum f ys)%nat
  end.

Lemma nsum_ext_in : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> f x = g x) -> Id (nsum f l) (nsum g l).
Proof.
  intros f g l. induction l as [| y ys IH]; simpl; intros H; apply eq_imp_id.
  - reflexivity.
  - rewrite (H y (or_introl eq_refl)).
    rewrite (IH (fun x Hx => H x (or_intror Hx))). reflexivity.
Qed.

Lemma nsum_perm : forall (f : Q -> nat) (l p : list Q),
  Permutation l p -> Id (nsum f l) (nsum f p).
Proof.
  intros f l p H.
  apply eq_imp_id.
  induction H as [ | x l' p' Hx IH | x y l' | l' l'' p' H1 IH1 H2 IH2 ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. lia.
  - rewrite IH1. exact IH2.
Qed.

Lemma nsum_const : forall (n : nat) (l : list Q), Id (nsum (fun _ => n) l) ((length l * n)%nat).
Proof.
  intros n l. apply eq_imp_id. induction l as [| y ys IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_bound : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) -> NatLe (nsum f l) ((length l * B)%nat).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (Hy : (f y <= B)%nat) by (apply H; left; reflexivity).
    assert (Hys : NatLe (nsum f ys) (length ys * B))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys). lia.
Qed.

Lemma nsum_bound_eq : forall (f : Q -> nat) (l : list Q) (B : nat),
  (forall x, In x l -> (f x <= B)%nat) ->
  nsum f l = (length l * B)%nat ->
  forall x, In x l -> Id (f x) (B).
Proof.
  intros f l B. induction l as [| y ys IH]; simpl; intros Hsat Heq x0 Hx0;
    apply eq_imp_id.
  - destruct Hx0.
  - assert (Hy : (f y <= B)%nat) by (apply Hsat; left; reflexivity).
    assert (Hys : NatLe (nsum f ys) (length ys * B))
      by (apply (nsum_bound f ys B); intros x Hx; apply Hsat; right; exact Hx).
    pose proof (NatLe_drop _ _ Hys) as HysL.
    assert (Hfy : f y = B) by lia.
    assert (HysEq : nsum f ys = (length ys * B)%nat) by lia.
    destruct Hx0 as [Hx0 | Hx0].
    + subst x0. exact Hfy.
    + destruct (id_sym (IH (fun z Hz => Hsat z (or_intror Hz)) HysEq x0 Hx0)).
      reflexivity.
Qed.

(* ========== [sqsum]: sum_{x in l} freq_q x l = sum_v c_v^2 (dedup-free)
   ========== *)

Definition sqsum (l : list Q) : nat := nsum (fun x => freq_q x l) l.

Definition all_same (l : list Q) : Set :=
  forall a b, In a l -> In b l -> QeqT a b.

Theorem sqsum_perm : forall l p : list Q,
  Permutation l p -> Id (sqsum l) (sqsum p).
Proof.
  intros l p H. unfold sqsum.
  assert (Hex : forall x, In x l -> freq_q x l = freq_q x p).
  { intros x _. destruct (freq_q_perm x l p H). reflexivity. }
  destruct (id_sym (nsum_ext_in (fun x => freq_q x l) (fun x => freq_q x p) l Hex)).
  exact (nsum_perm (fun x => freq_q x p) l p H).
Qed.

Lemma sqsum_le : forall l : list Q, NatLe (sqsum l) ((length l * length l)%nat).
Proof.
  intros l. unfold sqsum.
  apply (nsum_bound (fun x => freq_q x l) l (length l)).
  intros x _. apply NatLe_drop. apply freq_q_le_length.
Qed.

Lemma freq_q_all_same : forall (x : Q) (l : list Q),
  In x l -> all_same l -> Id (freq_q x l) (length l).
Proof.
  intros x l Hin Hs. apply freq_q_eq_all. intros z Hz.
  unfold all_same in Hs. apply qeqT_imp_qeq. apply Hs.
  - exact Hz.
  - exact Hin.
Qed.

Lemma sqsum_all_same : forall l : list Q,
  all_same l -> Id (sqsum l) ((length l * length l)%nat).
Proof.
  intros l Hs. unfold sqsum.
  assert (Hex : forall x, In x l -> freq_q x l = length l).
  { intros x Hx. destruct (id_sym (freq_q_all_same x l Hx Hs)). reflexivity. }
  destruct (id_sym (nsum_ext_in (fun x => freq_q x l)
              (fun _ : Q => length l) l Hex)).
  apply nsum_const.
Qed.

Lemma sqsum_eq_all_same : forall l : list Q,
  sqsum l = (length l * length l)%nat -> all_same l.
Proof.
  intros l Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - unfold sqsum in Heq.
    pose proof (nsum_bound_eq (fun x0 => freq_q x0 (x :: xs)) (x :: xs)
                  (length (x :: xs))
                  (fun x0 _ => NatLe_drop _ _ (freq_q_le_length x0 (x :: xs)))
                  Heq x (or_introl eq_refl)) as Hfx.
    assert (HfxE : freq_q x (x :: xs) = length (x :: xs))
      by (destruct Hfx; reflexivity).
    pose proof (freq_q_full_count x (x :: xs) HfxE) as Hall.
    intros a b Ha Hb. apply qeq_imp_qeqT. apply (Qeq_trans a x b).
    + apply qeqT_imp_qeq. apply Hall. exact Ha.
    + apply (Qeq_sym b x). apply qeqT_imp_qeq. apply Hall. exact Hb.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
(* ========== zero-axiom attestation of the merged sections ========== *)
Print Assumptions freq_q_app.
Print Assumptions freq_q_perm.