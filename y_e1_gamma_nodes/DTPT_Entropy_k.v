(* ConstructiveWorld-Main - DTPT_Entropy_k: gate-clean LINT-6 split piece 11/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_k.

    Mission.  tools: absolute-value zero, subtraction zero, and splitting a.
      Carries source lines 2985-3309 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f, DTPT_Entropy_g, DTPT_Entropy_h, DTPT_Entropy_i, DTPT_Entropy_j (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g DTPT_Entropy_h DTPT_Entropy_i DTPT_Entropy_j.

(* ========== tools: absolute-value zero, subtraction zero, and splitting a
   vanishing sum of nonnegative terms ========== *)

(* Qabs x == 0 -> x == 0 (direct case analysis on the Qnum encoding; the
   stdlib has no ready-made Qeq form) *)
Lemma xqz_abs0_eq : forall x : Q, Qabs x == 0 -> QeqT x 0.
Proof.
  intros [n d] H. apply qeq_imp_qeqT. unfold Qeq. destruct n as [| p | p].
  - reflexivity.
  - unfold Qabs in H. simpl in H. discriminate H.
  - unfold Qabs in H. simpl in H. discriminate H.
Qed.

(* x - y == 0 -> x == y (both directions of [Qle_0_sub'] plus
   antisymmetry; no setoid rewriting) *)
Lemma xqz_sub_eq0 : forall x y : Q, (x - y == 0)%Q -> QeqT x y.
Proof.
  intros x y H. apply qeq_imp_qeqT.
  assert (Hyx : (y - x == 0)%Q).
  { assert (Hmo : y - x == - (x - y)) by (apply qeqT_imp_qeq; apply xq_minus_opp).
    rewrite Hmo, H. reflexivity. }
  apply qeqT_imp_qeq. apply (xq_Qle_antisym x y).
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' x y)).
    apply xq_Qeq_le. apply Qeq_sym. exact Hyx.
  - apply QleT'_to_Qle. apply (snd (Qle_0_sub' y x)).
    apply xq_Qeq_le. apply Qeq_sym. exact H.
Qed.

(* a vanishing sum of two nonnegative terms forces the first term to zero
   (squeezed between a <= a+b == 0 and 0 <= a) *)
Lemma xqz_plus_eq0_le : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> QeqT a 0.
Proof.
  intros a b Hab Ha Hb. apply qeq_imp_qeqT.
  assert (Hle : QleT' (a + 0) (a + b))
    by (apply qadd_le; [apply Qle_refl | exact Hb]).
  assert (Hle' : a <= 0).
  { apply QleT'_to_Qle in Hle. rewrite Hab in Hle.
    rewrite Qplus_0_r in Hle. exact Hle. }
  apply qeqT_imp_qeq. exact (xq_Qle_antisym a 0 Hle' Ha).
Qed.

(* a vanishing sum of two nonnegative terms forces both terms to zero
   (commute and reuse) *)
Lemma xqz_plus_eq0 : forall a b : Q,
  (a + b == 0)%Q -> (0 <= a)%Q -> (0 <= b)%Q -> And (QeqT a 0) (QeqT b 0).
Proof.
  intros a b Hab Ha Hb. split.
  - exact (xqz_plus_eq0_le a b Hab Ha Hb).
  - rewrite Qplus_comm in Hab.
    exact (xqz_plus_eq0_le b a Hab Hb Ha).
Qed.

(* ========== main theorem: the zero locus of [H_devsum] = the ascending
   lists ========== *)

(* head minimality: the head of an ascending list does not exceed any
   member *)
Lemma xqz_sorted_hd_min : forall (l : list Q) (z : Q),
  SortedQ l -> In z l -> QleT' (hd 0 l) (z).
Proof.
  intros [| a rest] z HS Hin.
  - apply Qle_to_QleT'. destruct Hin.
  - apply Qle_to_QleT'.
    destruct HS as [| c1 c2 HSr HFa].
    * destruct Hin.
    * subst.
      rewrite Forall_forall in HFa.
      change (hd 0 (a :: rest)) with a.
      destruct Hin as [Heq | Hin].
      { subst. apply Qle_refl. }
      { apply HFa. exact Hin. }
Qed.

(* the head of the P0 normal form is a lower bound of the whole list
   (membership transported through the permutation) *)
Lemma xqz_P0_hd_min_all : forall (l : list Q) (z : Q),
  In z l -> QleT' (hd 0 (P0 l)) (z).
Proof.
  intros l z Hin.
  apply (xqz_sorted_hd_min (P0 l) z).
  - apply xq_P0_sorted.
  - apply Permutation_in with (l := l).
    + apply D5_P0_perm.
    + exact Hin.
Qed.

(* backward direction of the main theorem: a vanishing placeholder entropy
   implies ascending (peeling the |head difference| layer by layer, with
   induction) *)
Theorem H_shannon_q_zero_sorted : forall l : list Q,
  H_devsum l == 0 -> SortedQ l.
Proof.
  induction l as [| x xs IH]; intro H.
  - apply sortQ_nil.
  - cbn [H_devsum] in H.
    destruct (xqz_plus_eq0
                (Qabs (x - hd 0 (P0 (x :: xs)))) (H_devsum xs) H
                (QleT'_to_Qle _ _ (abs_nonneg (x - hd 0 (P0 (x :: xs)))))
                (QleT'_to_Qle _ _ (H_shannon_q_nonneg xs))) as [Ha Hs].
    assert (Hxm : x == hd 0 (P0 (x :: xs))).
    { apply qeqT_imp_qeq. apply xqz_sub_eq0. apply qeqT_imp_qeq.
      apply xqz_abs0_eq. apply qeqT_imp_qeq. exact Ha. }
    apply sortQ_cons.
    + apply IH. apply qeqT_imp_qeq. exact Hs.
    + rewrite Forall_forall. intros z Hz.
      apply (Qle_trans x (hd 0 (P0 (x :: xs))) z).
      * apply QleT'_to_Qle. apply xq_Qeq_le. exact Hxm.
      * apply QleT'_to_Qle. apply xqz_P0_hd_min_all. simpl. right. exact Hz.
Qed.

(* main theorem: the zero locus of the placeholder Shannon deviation
   entropy = the ascending lists (forward = the existing
   [xq_H_shannon_sortQ]; contrast: the zero locus of the true-frequency
   entropy = the constant lists) *)
Theorem H_shannon_q_zero_iff_sorted : forall l : list Q,
  And (QeqT (H_devsum l) 0 -> SortedQ l) (SortedQ l -> QeqT (H_devsum l) 0).
Proof.
  intro l. split.
  - intro H. apply qeqT_imp_qeq in H.
    apply H_shannon_q_zero_sorted. exact H.
  - intro Hs. apply xq_H_shannon_sortQ. exact Hs.
Qed.


(* ========== piece A: the all-equal characterization of [H_ms == 1]
   ========== *)

(* elimination by [dedup_aux]: when every member equals x, the dedup
   collapses to the empty list (the Qmem convention, not via [In]) *)
Lemma xqz_dedup_aux_nil : forall (x : Q) (m : list Q),
  (forall z : Q, Qmem z m -> x == z) -> Id (dedup_aux x m) ([]).
Proof.
  intros x m. induction m as [| y ys IH]; intro Hall; apply eq_imp_id.
  - reflexivity.
  - cbn [dedup_aux].
    assert (HxyI : Id (Qeq_bool x y) true).
    { apply Qeqb_true_of. apply Hall. apply Qmem_refl_cons. }
    assert (Hxy : Qeq_bool x y = true)
      by (destruct (id_sym HxyI); reflexivity).
    rewrite Hxy.
    assert (Hall' : forall z : Q, Qmem z ys -> x == z).
    { intros z Hz. apply Hall. apply (snd (Qmem_cons _ _ _)). right.
      exact Hz. }
    destruct (IH Hall'). reflexivity.
Qed.

(* all-equal characterization: [H_ms l == 1] implies any two members are
   Qeq equal (structure of the dedup of length 1 and [dedup_Qmem_r]; no
   dependency on [In]) *)
Theorem H_ms1_all_eq : forall l : list Q,
  (H_ms l == 1)%Q -> forall a b : Q, Qmem a l -> Qmem b l -> QeqT (a) (b).
Proof.
  intro l. intro H. unfold H_ms in H.
  assert (HI : Id (length (dedup l)) 1%nat)
    by (apply (xq_Zlen_inj1 (length (dedup l))); exact H).
  assert (Hlen : length (dedup l) = 1%nat)
    by (destruct (id_sym HI); reflexivity).
  destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
  intros a b Ha Hb.
  assert (Qa : Qmem a (dedup l)) by (apply dedup_Qmem_r; exact Ha).
  assert (Qb : Qmem b (dedup l)) by (apply dedup_Qmem_r; exact Hb).
  revert Qb. revert Qa. destruct (id_sym Hc). intros Qa Qb.
  destruct (Qmem_cons a c nil) as [Qapc _].
  assert (Qa1 : Or (Id (Qeq_bool a c) true) (Qmem a nil))
    by (apply Qapc; exact Qa).
  destruct (Qmem_cons b c nil) as [Qbpc _].
  assert (Qb1 : Or (Id (Qeq_bool b c) true) (Qmem b nil))
    by (apply Qbpc; exact Qb).
  destruct Qa1 as [QaL | QaR];
    [ | unfold Qmem in QaR; simpl in QaR; inversion QaR ].
  destruct Qb1 as [QbL | QbR];
    [ | unfold Qmem in QbR; simpl in QbR; inversion QbR ].
  apply qeq_imp_qeqT. apply Qeq_bool_eq.
  assert (Ea : Qeq_bool a c = true) by (destruct (id_sym QaL); reflexivity).
  assert (Eb : Qeq_bool b c = true) by (destruct (id_sym QbL); reflexivity).
  assert (Eb' : Qeq_bool c b = true)
    by (destruct (Qeqb_sym b c); exact Eb).
  destruct (Qeqb_trans a c b Ea Eb'). reflexivity.
Qed.

(* piece A: [H_ms == 1] iff the list is nonempty with all members Qeq equal
   (exists-Forall form) *)
Theorem H_ms1_iff_const : forall l : list Q,
  IffT (QeqT (H_ms l) 1)
       (And (l <> []) (sigT (fun a : Q => Forall (fun z => z == a) l))).
Proof.
  intro l. split.
  - intro H.
    assert (HlenI : Id (length (dedup l)) 1%nat)
      by (unfold H_ms in H; apply xq_Zlen_inj1;
         apply qeqT_imp_qeq; exact H).
    assert (Hlen : length (dedup l) = 1%nat)
      by (destruct (id_sym HlenI); reflexivity).
    destruct (xq_len1_el (dedup l) Hlen) as [c Hc].
    split.
    + intro He. rewrite He in Hc. simpl in Hc. inversion Hc.
    + apply (existT _ c). apply Forall_forall. intros z Hz.
      assert (HcE : dedup l = [c]) by (destruct (id_sym Hc); reflexivity).
      apply qeqT_imp_qeq. apply (xq_dedup1_all_eq l c HcE z Hz).
  - intros [Hne [a Hfa]].
    destruct l as [| x xs]; [ exfalso; apply Hne; reflexivity | ].
    apply qeq_imp_qeqT. unfold H_ms.
    inversion Hfa as [| z0 zs Hzx Hfxs]; subst.
    assert (HdI : Id (dedup_aux x (dedup xs)) []).
    { rewrite Forall_forall in Hfxs.
      apply xqz_dedup_aux_nil. intros z Hz.
      assert (Qxs : Qmem z xs) by (apply (dedup_Qmem_l xs z); exact Hz).
      assert (QxsE : existsb (fun y => Qeq_bool z y) xs = true)
        by (destruct (id_sym Qxs); reflexivity).
      apply existsb_exists in QxsE.
      destruct QxsE as [w [Hw Hzw]].
      apply (Qeq_trans x a z Hzx).
      apply (Qeq_sym z a).
      apply (Qeq_trans z w a (Qeq_bool_eq z w Hzw) (Hfxs w Hw)). }
    assert (Hd : dedup_aux x (dedup xs) = [])
      by (destruct (id_sym HdI); reflexivity).
    unfold H_ms. cbn [dedup length]. rewrite Hd. reflexivity.
Qed.

(* ========== piece B: the [H_cond] family (nonnegativity iff + absolute
   value bound + zero locus iff) ========== *)

(* the exact iff form of the failed unconditional nonnegativity: the
   missing premise is exactly [H_devsum ctx <= H_devsum l] (a two-way
   strengthening of the guarded version) *)
Theorem H_cond_nonneg_iff : forall l ctx : list Q,
  IffT (QleT' 0 (H_cond l ctx)) (QleT' (H_devsum ctx) (H_devsum l)).
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply (snd (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
  - intro H. apply (fst (Qle_0_sub' (H_devsum ctx) (H_devsum l))).
    exact H.
Qed.

(* absolute-value bound ([Qabs_triangle]):
   |H_cond l ctx| <= H_devsum l + H_devsum ctx
   (both entropies are nonnegative, so the triangle sum is the conservative
   upper bound; the shape follows the actual definition of [H_cond]) *)
Theorem H_cond_abs_bound : forall l ctx : list Q, QleT' (Qabs (H_cond l ctx)) ((H_devsum l + H_devsum ctx)%Q).
Proof.
  intros l ctx. apply Qle_to_QleT'. unfold H_cond, Qminus.
  apply (Qle_trans _ (Qabs (H_devsum l) + Qabs (- H_devsum ctx))).
  - apply Qabs_triangle.
  - rewrite (qeqT_imp_qeq _ _ (xq_abs_id (H_devsum l)
               (QleT'_to_Qle _ _ (H_shannon_q_nonneg l)))).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_opp (H_devsum ctx))).
    rewrite (qeqT_imp_qeq _ _ (xq_abs_id (H_devsum ctx)
               (QleT'_to_Qle _ _ (H_shannon_q_nonneg ctx)))).
    apply Qle_refl.
Qed.

(* zero locus of the conditional entropy:
   [H_cond l ctx == 0] iff the two placeholder entropies are equal *)
Theorem H_cond_zero_iff : forall l ctx : list Q,
  IffT (QeqT (H_cond l ctx) 0) (QeqT (H_devsum l) (H_devsum ctx)).
Proof.
  intros l ctx. unfold H_cond. split.
  - intro H. apply qeq_imp_qeqT.
    apply (Qeq_trans (H_devsum l)
                     (H_devsum l - H_devsum ctx + H_devsum ctx) (H_devsum ctx)).
    + ring.
    + pose proof (qeqT_imp_qeq _ _ H) as Hm.
      rewrite Hm at 1. apply Qplus_0_l.
  - intro H. apply qeq_imp_qeqT.
    rewrite <- (qeqT_imp_qeq _ _ H).
    apply (qeqT_imp_qeq _ _ (xq_minus_self (H_devsum l))).
Qed.

(* ========== bonus: turning the counterexamples into positive forms
   ========== *)

(* the restricted positive form of the permutation counterexample:
   invariance holds exactly under the both-ascending premise (the failure
   of [3;1;2] vs [2;1;3] comes from the permutation destroying the
   ascending order) *)
Theorem H_shannon_q_perm_inv_if_sorted : forall l p : list Q,
  Permutation l p -> SortedQ l -> SortedQ p -> QeqT (H_devsum l) (H_devsum p).
Proof.
  intros l p _Hp Hl Hpp.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _ (xq_H_shannon_sortQ l Hl)).
  rewrite (qeqT_imp_qeq _ _ (xq_H_shannon_sortQ p Hpp)).
  reflexivity.
Qed.

(* the positive twin: double zero locus (placeholder entropy zero and
   multiset entropy 1) iff a nonempty constant list (assembled from
   [H_shannon_q_const_zero] and [H_ms1_iff_const]) *)
Theorem zero_locus_joint : forall l : list Q,
  IffT (And (QeqT (H_devsum l) 0) (QeqT (H_ms l) 1))
       (And (l <> []) (sigT (fun a : Q => Forall (fun z => z == a) l))).
Proof.
  intro l. split.
  - intros [Hh Hm]. exact (fst (H_ms1_iff_const l) Hm).
  - intros [Hne [a Hfa]]. split.
    + apply (H_shannon_q_const_zero a l Hfa).
    + apply (snd (H_ms1_iff_const l)). split.
      * exact Hne.
      * apply (existT _ a). exact Hfa.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions H_shannon_q_zero_iff_sorted.
Print Assumptions H_ms1_iff_const.
Print Assumptions H_cond_abs_bound.
Print Assumptions zero_locus_joint.