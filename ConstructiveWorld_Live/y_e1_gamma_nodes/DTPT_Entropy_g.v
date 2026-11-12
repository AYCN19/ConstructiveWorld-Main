(* ConstructiveWorld-Main - DTPT_Entropy_g: gate-clean LINT-6 split piece 7/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_g.

    Mission.  [H_freq]: the rational surrogate of the true-frequency Shannon.
      Carries source lines 1698-2048 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f.

(* ========== [H_freq]: the rational surrogate of the true-frequency Shannon
   entropy and its main theorems ========== *)

(* [H_freq l = 1 - sum_v p_v^2 = (n^2 - sum_v c_v^2) / n^2] (over Q; the
   value is 0 when n = 0) *)
Definition H_freq (l : list Q) : Q :=
  (qn (length l) * qn (length l) - qn (sqsum l))
    / (qn (length l) * qn (length l)).

(* main theorem: permutation invariance — a theorem the centroid-offset
   shape of the old [H_devsum] could not express *)
Theorem H_freq_perm : forall l p : list Q,
  Permutation l p -> QeqT (H_freq l) (H_freq p).
Proof.
  intros l p Hp. apply qeq_imp_qeqT. unfold H_freq.
  destruct (id_sym (sqsum_perm l p Hp)).
  rewrite (Permutation_length Hp).
  reflexivity.
Qed.

(* nonnegativity (for the chosen shape: n^2 >= sum c_v^2, and division by a
   positive denominator preserves the sign; for the empty list numerator
   and denominator are both zero and the value is 0) *)
Theorem H_freq_nonneg : forall l : list Q, QleT' (0) (H_freq l).
Proof.
  intros l. apply Qle_to_QleT'. destruct l as [| x xs].
  - assert (Hz : H_freq [] == 0).
    { unfold H_freq. apply qeqT_imp_qeq. apply qdiv_zero_num.
      apply qeqT_imp_qeq. apply qnum_zero. reflexivity. }
    rewrite Hz. apply Qle_refl.
  - unfold H_freq. apply QleT'_to_Qle. apply qdiv_nonneg.
    + apply QleT'_to_Qle. apply (fst (Qle_0_sub' (qn (sqsum (x :: xs)))
                 (qn (length (x :: xs)) * qn (length (x :: xs))))).
      apply Qle_to_QleT'.
      rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs)) (length (x :: xs)))).
      apply QleT'_to_Qle. apply qn_le. apply NatLe_drop. apply sqsum_le.
    + rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs)) (length (x :: xs)))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ.
Qed.

(* degeneracy characterization (forward): all values equal implies
   [H_freq] takes 0 *)
Theorem H_freq_all_same_zero : forall l : list Q,
  all_same l -> QeqT (H_freq l) (0).
Proof.
  intros l Hs. apply qeq_imp_qeqT. unfold H_freq.
  apply qeqT_imp_qeq. apply qdiv_zero_num.
  apply qeqT_imp_qeq. apply qnum_zero.
  destruct (id_sym (sqsum_all_same l Hs)). reflexivity.
Qed.

Theorem H_freq_len_le_1 : forall l : list Q,
  (length l <= 1)%nat -> QeqT (H_freq l) (0).
Proof.
  intros l Hl. destruct l as [| x xs].
  - apply H_freq_all_same_zero. intros a b Ha Hb. destruct Ha.
  - simpl in Hl. destruct xs as [| y ys].
    + apply H_freq_all_same_zero. intros a b Ha Hb.
      destruct (Qeq_bool a x) eqn:Ea.
      * apply qeq_imp_qeqT. apply (Qeq_trans a x b).
        -- apply (proj1 (Qeq_bool_iff a x)). exact Ea.
        -- destruct (Qeq_bool b x) eqn:Eb.
           ++ apply (Qeq_sym b x). apply (proj1 (Qeq_bool_iff b x)). exact Eb.
           ++ exfalso. destruct Hb as [Hb | Hb].
              ** rewrite <- Hb in Eb. rewrite Qeq_bool_refl in Eb.
                 discriminate Eb.
              ** exact Hb.
      * exfalso. destruct Ha as [Ha | Ha].
        -- rewrite <- Ha in Ea. rewrite Qeq_bool_refl in Ea. discriminate Ea.
        -- exact Ha.
    + simpl in Hl. exfalso. lia.
Qed.

(* degeneracy characterization (backward): [H_freq] takes 0 implies all
   values equal (two-sided closure) *)
Theorem H_freq_eq0_all_same : forall l : list Q,
  H_freq l == 0 -> all_same l.
Proof.
  intros l Heq. unfold H_freq in Heq. destruct l as [| x xs].
  - intros a b Ha Hb. destruct Ha.
  - assert (HB : 0 < qn (length (x :: xs)) * qn (length (x :: xs))).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                     (length (x :: xs)))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ. }
    assert (Hnum : qn (length (x :: xs)) * qn (length (x :: xs))
                   - qn (sqsum (x :: xs)) == 0)
      by (apply (qeqT_imp_qeq _ _ (qdiv_eq0_num _ _ HB Heq))).
    pose proof (qeqT_imp_qeq _ _
      (qsub_eq0 (qn (length (x :: xs)) * qn (length (x :: xs)))
                  (qn (sqsum (x :: xs))) Hnum)) as Hab.
    rewrite <- (qeqT_imp_qeq _ _ (qn_mul (length (x :: xs))
                     (length (x :: xs)))) in Hab.
    pose proof (qn_inj (length (x :: xs) * length (x :: xs))
                  (sqsum (x :: xs)) Hab) as Heqnat.
    assert (HeqnatE : sqsum (x :: xs)
                      = (length (x :: xs) * length (x :: xs))%nat)
      by (destruct Heqnat; reflexivity).
    apply sqsum_eq_all_same. exact HeqnatE.
Qed.

(* ############################################################
   The data-processing inequality family for [H_freq].
   ############################################################ *)

(* ========== list/sum transfer tools ========== *)

(* [map] preserves length (built here, avoiding stdlib rename drift) *)
Lemma length_map_self : forall (f : Q -> Q) (l : list Q), Id (length (map f l)) (length l).
Proof.
  intros f l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (id_sym IH). reflexivity.
Qed.

(* pointwise monotonicity of the general sum *)
Lemma nsum_le : forall (g h : Q -> nat) (l : list Q),
  (forall x, In x l -> (g x <= h x)%nat) -> NatLe (nsum g l) ((nsum h l)%nat).
Proof.
  intros g h l. induction l as [| a l IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (H1 : (g a <= h a)%nat) by (apply H; left; reflexivity).
    assert (H2 : NatLe (nsum g l) (nsum h l))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ H2). lia.
Qed.

(* summing over map = summing the composition (the exchange bridge between
   [nsum] and [map]) *)
Lemma nsum_map : forall (g : Q -> nat) (f : Q -> Q) (l : list Q), Id (nsum g (map f l)) (nsum (fun x => g (f x)) l).
Proof.
  intros g f l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (id_sym IH). reflexivity.
Qed.

(* ========== baseline: the pushforward counting lemma and pointwise
   domination ========== *)

(* baseline pushforward lemma, counting form: the frequency of y after
   [map] equals the number of votes of members x with f x == y in the
   original list *)
Theorem freq_q_map : forall (f : Q -> Q) (y : Q) (l : list Q), Id (freq_q y (map f l)) (nsum (fun x : Q => if Qeq_bool y (f x) then 1%nat else 0%nat) l).
Proof.
  intros f y l. induction l as [| a l IH]; simpl; apply eq_imp_id.
  - reflexivity.
  - destruct (Qeq_bool y (f a)); destruct (id_sym IH); reflexivity.
Qed.

(* Qeq-shape bridge, pointwise domination: the votes of x in the original
   list are <= the votes of f x in the image list.  A true vote (x == a)
   still hits under f (the shape assumption preserves hits), and the image
   list may merge additional votes (other values with the same image), so
   votes only grow — the micro-mechanism of the data-processing
   inequality. *)
Lemma freq_q_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall (x : Q) (l : list Q), NatLe (freq_q x l) ((freq_q (f x) (map f l))%nat).
Proof.
  intros f Hf x l. induction l as [| a l IH]; simpl; apply NatLe_lift.
  - lia.
  - pose proof (NatLe_drop _ _ IH) as IHL.
    destruct (Qeq_bool x a) eqn:H1.
    + assert (H2 : Qeq_bool (f x) (f a) = true).
      { apply (proj2 (Qeq_bool_iff (f x) (f a))). apply Hf.
        apply (proj1 (Qeq_bool_iff x a)). exact H1. }
      rewrite H2. lia.
    + destruct (Qeq_bool (f x) (f a)); lia.
Qed.

(* mass-merging monotonicity, collision-sum form:
   [sqsum (map f l) >= sqsum l], by summing over map ([nsum_map]) and
   pointwise domination ([freq_q_map_ge]). *)
Theorem sqsum_map_ge : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, NatLe (sqsum l) ((sqsum (map f l))%nat).
Proof.
  intros f Hf l. unfold sqsum.
  destruct (id_sym (nsum_map (fun y => freq_q y (map f l)) f l)).
  apply nsum_le. intros x _. apply NatLe_drop. apply freq_q_map_ge. exact Hf.
Qed.

(* ========== Q division/subtraction monotonicity tools (the complement
   sign-flip machinery of the DPI) ========== *)

(* subtraction distributes over same-denominator quotients (unfold Qminus
   and Qdiv, then ring; [Qinv] stays atomic) *)
Lemma qdiv_sub_distr : forall A B D : Q, QeqT (A / D - B / D) ((A - B) / D).
Proof.
  intros A B D. apply qeq_imp_qeqT. unfold Qminus, Qdiv. ring.
Qed.

(* right monotonicity of subtraction: A <= B gives D - B <= D - A (the core
   of complement monotonicity with sign flip) *)
Lemma qsub_mono_r : forall D A B : Q, A <= B -> QleT' (D - B) (D - A).
Proof.
  intros D A B H. apply Qle_to_QleT'. unfold Qminus.
  apply QleT'_to_Qle. apply (qadd_le D D (- B) (- A)).
  - apply Qle_refl.
  - apply QleT'_to_Qle. apply qopp_le. exact H.
Qed.

(* core form: for N >= 1 the collision sum in [0, N^2] passes monotonically
   through the complement quotient with a sign flip ([qdiv_sub_distr]
   merges the quotient difference into a single quotient, [qdiv_nonneg]
   keeps the sign; for N = 0 both sides are literally A = B = 0). *)
Lemma hfreq_core_anti : forall (N A B : nat), (A <= B)%nat -> (B <= N * N)%nat -> QleT' ((qn N * qn N - qn B) / (qn N * qn N)) ((qn N * qn N - qn A) / (qn N * qn N)).
Proof.
  intros N A B HAB HBN.
  apply Qle_to_QleT'.
  destruct N as [| m].
  - assert (HA : A = 0%nat) by lia.
    assert (HB : B = 0%nat) by lia.
    subst. apply Qle_refl.
  - assert (HD : 0 < qn (S m) * qn (S m)).
    { rewrite <- (qeqT_imp_qeq _ _ (qn_mul (S m) (S m))).
      apply QltT_to_Qlt. apply qn_pos. simpl. apply Nat.lt_0_succ. }
    pose proof (qpos_neq0 (qn (S m) * qn (S m)) HD) as HDneq.
    apply QleT'_to_Qle. apply (snd (Qle_0_sub'
              ((qn (S m) * qn (S m) - qn B) / (qn (S m) * qn (S m)))
              ((qn (S m) * qn (S m) - qn A) / (qn (S m) * qn (S m))))).
    apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (qdiv_sub_distr (qn (S m) * qn (S m) - qn A)
                            (qn (S m) * qn (S m) - qn B)
                            (qn (S m) * qn (S m)))).
    apply QleT'_to_Qle. apply qdiv_nonneg.
    + apply QleT'_to_Qle. apply (fst (Qle_0_sub' (qn (S m) * qn (S m) - qn B)
                               (qn (S m) * qn (S m) - qn A))).
      apply qsub_mono_r. apply QleT'_to_Qle. apply qn_le. exact HAB.
    + exact HD.
Qed.

(* ========== main theorem: the data-processing inequality (DPI) ========== *)

(* observation (coarse-graining that merges masses) does not increase
   [H_freq]: [H_freq (map f l) <= H_freq l].
   The shape assumption is the Qeq-honest conservation of the
   equivalence-class-merging semantics: for an arbitrary bare function f
   the claim is false — a bare function can observe the Record
   representation of Q (e.g. take the numerator); the counterexample
   l = [1/2; 2/4] has H_freq l = 0 but H_freq (map numerator l) = 1/2.
   Hence the main theorem carries the shape assumption
   (forall x y : Q, x == y -> f x == f y). *)
Theorem H_freq_dpi : forall (f : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  forall l : list Q, QleT' (H_freq (map f l)) (H_freq l).
Proof.
  intros f Hf l.
  apply Qle_to_QleT'.
  assert (Hlen : length (map f l) = length l)
    by (destruct (length_map_self f l); reflexivity).
  destruct l as [| x xs].
  - replace (map f (@nil Q)) with (@nil Q) by reflexivity.
    apply Qle_refl.
  - unfold H_freq. rewrite Hlen.
    apply QleT'_to_Qle. apply (hfreq_core_anti (length (x :: xs))
                           (sqsum (x :: xs)) (sqsum (map f (x :: xs)))).
    + apply NatLe_drop. apply sqsum_map_ge. exact Hf.
    + pose proof (sqsum_le (map f (x :: xs))) as Hs.
      rewrite Hlen in Hs. exact (NatLe_drop _ _ Hs).
Qed.

(* ========== two endpoint examples: pinning the behavior at both ends of
   the DPI ========== *)

(* endpoint one, identity does not decay: the identity map (the finest
   observation) loses nothing — bridged directly by Leibniz equality of
   lists, no shape assumption needed. *)
Theorem H_freq_map_id : forall l : list Q, QeqT (H_freq (map (fun x : Q => x) l)) (H_freq l).
Proof.
  intros l.
  apply qeq_imp_qeqT.
  assert (Hid : map (fun x : Q => x) l = l).
  { induction l as [| a l IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity. }
  rewrite Hid. apply Qeq_refl.
Qed.

(* the image of a constant map is all-equal (Leibniz on lists) *)
Lemma in_map_const : forall (c : Q) (l : list Q) (a : Q),
  In a (map (fun _ : Q => c) l) -> QeqT (a) (c).
Proof.
  intros c l. induction l as [| b l IH]; simpl; intros a H; apply qeq_imp_qeqT.
  - destruct H.
  - destruct H as [H | H].
    + subst a. apply Qeq_refl.
    + apply qeqT_imp_qeq. apply IH. exact H.
Qed.

(* endpoint two, constant maps collapse everything: the coarsest observation
   (merging everything into one bucket) makes [H_freq] take 0 (degenerate
   form; true for the empty list too, whose [H_freq] is 0 anyway). *)
Theorem H_freq_map_const : forall (c : Q) (l : list Q), QeqT (H_freq (map (fun _ : Q => c) l)) (0).
Proof.
  intros c l. apply H_freq_all_same_zero.
  intros a b Ha Hb. apply qeq_imp_qeqT. apply (Qeq_trans a c b).
  - exact (qeqT_imp_qeq _ _ (in_map_const c l a Ha)).
  - apply (Qeq_sym b c). exact (qeqT_imp_qeq _ _ (in_map_const c l b Hb)).
Qed.

(* ========== bonus: the iterated no-decay chain ========== *)

(* two-step composition, directly: the second observation still does not
   increase (g must also respect the shape) *)
Theorem H_freq_map_twice : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT' (H_freq (map g (map f l))) (H_freq (map f l)).
Proof.
  intros f g Hf Hg l. apply (H_freq_dpi g Hg (map f l)).
Qed.

(* chain: H_freq (map g (map f l)) <= H_freq (map f l) <= H_freq l *)
Theorem H_freq_map_chain : forall (f g : Q -> Q),
  (forall x y : Q, x == y -> f x == f y) ->
  (forall x y : Q, x == y -> g x == g y) ->
  forall l : list Q, QleT' (H_freq (map g (map f l))) (H_freq l).
Proof.
  intros f g Hf Hg l.
  apply Qle_to_QleT'.
  apply (Qle_trans (H_freq (map g (map f l))) (H_freq (map f l)) (H_freq l)).
  - apply QleT'_to_Qle. apply (H_freq_dpi g Hg (map f l)).
  - apply QleT'_to_Qle. apply (H_freq_dpi f Hf l).
Qed.

(* ============================================================
   The three missing members of the multi-entropy family ([collide] /
   [maxfreq] / [H_min_q] and [H_max_q]) with the Renyi ladder order-chain
   main theorem [H_chain], plus the [H_freq] coherence bridge and the
   permutation-invariance closure.
   ============================================================ *)

(* ============================================================
   The three missing members of the multi-entropy family:
   [collide] (the Renyi-order-2 collision entropy core sum p_v^2),
   [maxfreq] (normalized maximum frequency), [H_max_q] = 1 - maxfreq and
   [H_min_q] = 1 - collide (the specified shapes).
   Main theorem, the Renyi ladder for nonempty l, all three members in one
   chain: [1 / qn n <= collide l <= maxfreq l <= 1]
   (sum p^2 >= 1/n is the discrete Cauchy-Schwarz; sum p^2 <=
   max p * sum p is proved by nat-side induction and bridged by Q
   division).
   Coherence: [H_freq l == 1 - collide l] for nonempty l ([H_freq] is the
   alias of 1 - collide).
   Convention note: Q has no logarithm, so the entropy complement 1 - x is
   the rational surrogate; it is decreasing in x exactly like -log x, so
   the order properties carry over faithfully.  For all-equal lists
   [maxfreq] takes 1 (the complement takes 0); empty lists take 0; the
   whole family is permutation invariant.
   ============================================================ *)


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions H_freq_perm.
Print Assumptions H_freq_nonneg.
Print Assumptions H_freq_all_same_zero.
Print Assumptions H_freq_len_le_1.
Print Assumptions H_freq_eq0_all_same.
Print Assumptions freq_q_map.
Print Assumptions freq_q_map_ge.
Print Assumptions sqsum_map_ge.
Print Assumptions H_freq_dpi.
Print Assumptions H_freq_map_id.
Print Assumptions H_freq_map_const.
Print Assumptions H_freq_map_twice.
Print Assumptions H_freq_map_chain.