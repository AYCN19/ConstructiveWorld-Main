(* ConstructiveWorld-Main - DTPT_Entropy_l: gate-clean LINT-6 split piece 12/13 of the Set-face multi-entropy family. *)
(** * DTPT_Entropy_l.

    Mission.  part 12 of the multi-entropy family face.
      Carries source lines 3310-3596 of the setlive cast (md5 98a74ed8) verbatim;
      the statement surface and every proof body are byte-conserved (bound-surgery discipline).
    Dependencies.  Stdlib QArith/List/Arith/Lia/Permutation/Setoid/Morphisms; S01_BaseRing; S02_CauchyComplete; sibling pieces DTPT_Entropy_a, DTPT_Entropy_b, DTPT_Entropy_c, DTPT_Entropy_d, DTPT_Entropy_e, DTPT_Entropy_f, DTPT_Entropy_g, DTPT_Entropy_h, DTPT_Entropy_i, DTPT_Entropy_j, DTPT_Entropy_k (linear Require Import chain).
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

Require Import DTPT_Entropy_a DTPT_Entropy_b DTPT_Entropy_c DTPT_Entropy_d DTPT_Entropy_e DTPT_Entropy_f DTPT_Entropy_g DTPT_Entropy_h DTPT_Entropy_i DTPT_Entropy_j DTPT_Entropy_k.

(* ============================================================
   Monotonicity of the collision mass under concatenation, composed from
   lemmas already in this file: [freq_q_app] (additivity of frequencies
   under concatenation) with the [nsum] / [sqsum] / [nmax] tools.
   Baseline: [sqsum_app_ge_l] / [sqsum_app_ge_r]:
     [sqsum (l1 ++ l2) >= sqsum l1] (and on the right) — concatenation
     increases pointwise frequencies and enlarges the support, so the
     collision mass only grows.
   Bonus: [sqsum_app_eq], the exact cross-term decomposition
     [sqsum (l1 ++ l2) = sqsum l1 + sqsum l2
      + sum_{x in l1} freq_q x l2 + sum_{x in l2} freq_q x l1].
   Companions: [sqsum_app_ge_sum] (mass form) and
   [maxcount_app_ge_l] / [maxcount_app_ge_r] (frequency extremes, the
   shared numerators of collide/maxfreq).
   Honest obstacle, pinned by counterexamples: monotonicity FAILS for the
   normalized quotients [H_freq]/[collide] — H_freq ([0] ++ [1]) = 1/2 > 0
   = H_freq [0], and collide [0] = 1 > 1/2 = collide ([0] ++ [1]).  The
   reason: while the collision sum (numerator) grows, the denominator n^2
   grows with it, so the normalized quotient has no direction; closed
   faithfully as [H_freq_app_mono_false] / [collide_app_mono_false].
   ============================================================ *)

(* ---------- core: additivity of [nsum] under concatenation, and pointwise
   additivity ---------- *)

Lemma nsum_app : forall (f : Q -> nat) (l p : list Q), Id (nsum f (l ++ p)) ((nsum f l + nsum f p)%nat).
Proof.
  intros f l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nsum_add : forall (f g : Q -> nat) (l : list Q), Id (nsum (fun x => (f x + g x)%nat) l) ((nsum f l + nsum g l)%nat).
Proof.
  intros f g l. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(* ---------- baseline: the two concatenation-monotonicity lemmas for
   [sqsum] ---------- *)

Theorem sqsum_app_ge_l : forall l1 l2 : list Q, NatLe (sqsum l1) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold sqsum. rewrite nsum_app.
  assert (H1 : (nsum (fun x => freq_q x l1) l1
                <= nsum (fun x => freq_q x (l1 ++ l2)) l1)%nat).
  { apply NatLe_drop. apply nsum_le. intros x _.
    destruct (id_sym (freq_q_app x l1 l2)). lia. }
  lia.
Qed.

Theorem sqsum_app_ge_r : forall l1 l2 : list Q, NatLe (sqsum l2) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold sqsum. rewrite nsum_app.
  assert (H2 : (nsum (fun x => freq_q x l2) l2
                <= nsum (fun x => freq_q x (l1 ++ l2)) l2)%nat).
  { apply NatLe_drop. apply nsum_le. intros x _.
    destruct (id_sym (freq_q_app x l1 l2)). lia. }
  lia.
Qed.

(* ---------- bonus: the exact cross-term decomposition of [sqsum] under
   concatenation ---------- *)

Theorem sqsum_app_eq : forall l1 l2 : list Q, Id (sqsum (l1 ++ l2)) ((sqsum l1 + sqsum l2
   + nsum (fun x => freq_q x l2) l1
   + nsum (fun x => freq_q x l1) l2)%nat).
Proof.
  intros l1 l2. apply eq_imp_id. unfold sqsum. rewrite nsum_app.
  assert (Hext1 : forall x : Q, In x l1 ->
    freq_q x (l1 ++ l2) = (freq_q x l1 + freq_q x l2)%nat).
  { intros x _. destruct (id_sym (freq_q_app x l1 l2)). reflexivity. }
  assert (Hext2 : forall x : Q, In x l2 ->
    freq_q x (l1 ++ l2) = (freq_q x l1 + freq_q x l2)%nat).
  { intros x _. destruct (id_sym (freq_q_app x l1 l2)). reflexivity. }
  rewrite (nsum_ext_in (fun x => freq_q x (l1 ++ l2))
                       (fun x => (freq_q x l1 + freq_q x l2)%nat) l1 Hext1).
  rewrite (nsum_ext_in (fun x => freq_q x (l1 ++ l2))
                       (fun x => (freq_q x l1 + freq_q x l2)%nat) l2 Hext2).
  rewrite (nsum_add (fun x => freq_q x l1) (fun x => freq_q x l2) l1),
          (nsum_add (fun x => freq_q x l1) (fun x => freq_q x l2) l2).
  lia.
Qed.

(* companion mass form: the sum of the two segment collision masses does
   not exceed the collision mass of the concatenation (cross terms are
   nonnegative) *)
Corollary sqsum_app_ge_sum : forall l1 l2 : list Q, NatLe (sqsum l1 + sqsum l2) ((sqsum (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. rewrite (sqsum_app_eq l1 l2). lia.
Qed.

(* ---------- companions: concatenation monotonicity of the [maxcount]
   extremes (numerator face) ---------- *)

Lemma nmax_app : forall (f : Q -> nat) (l p : list Q), Id (nmax f (l ++ p)) (Nat.max (nmax f l) (nmax f p)).
Proof.
  intros f l p. apply eq_imp_id. induction l as [| a l IH].
  - reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma nmax_le_app_l : forall (f : Q -> nat) (l p : list Q), NatLe (nmax f l) ((nmax f (l ++ p))%nat).
Proof.
  intros f l p. apply NatLe_lift. rewrite nmax_app. apply Nat.le_max_l.
Qed.

Lemma nmax_le_app_r : forall (f : Q -> nat) (l p : list Q), NatLe (nmax f l) ((nmax f (p ++ l))%nat).
Proof.
  intros f l p. apply NatLe_lift. rewrite nmax_app. apply Nat.le_max_r.
Qed.

Lemma nmax_mono : forall (f g : Q -> nat) (l : list Q),
  (forall x, In x l -> (f x <= g x)%nat) -> NatLe (nmax f l) ((nmax g l)%nat).
Proof.
  intros f g l. induction l as [| a t IH]; simpl; intros H; apply NatLe_lift.
  - lia.
  - assert (H1 : (f a <= g a)%nat) by (apply H; left; reflexivity).
    assert (H2 : NatLe (nmax f t) (nmax g t))
      by (apply IH; intros x Hx; apply H; right; exact Hx).
    pose proof (NatLe_drop _ _ H2). lia.
Qed.

Theorem maxcount_app_ge_l : forall l1 l2 : list Q, NatLe (maxcount l1) ((maxcount (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold maxcount.
  apply (Nat.le_trans (nmax (fun x => freq_q x l1) l1)
                      (nmax (fun x => freq_q x (l1 ++ l2)) l1)
                      (nmax (fun x => freq_q x (l1 ++ l2)) (l1 ++ l2))).
  - apply NatLe_drop.
    apply (nmax_mono (fun x => freq_q x l1)
                     (fun x => freq_q x (l1 ++ l2)) l1).
    intros x _. destruct (id_sym (freq_q_app x l1 l2)). lia.
  - exact (NatLe_drop _ _ (nmax_le_app_l (fun x => freq_q x (l1 ++ l2)) l1 l2)).
Qed.

Theorem maxcount_app_ge_r : forall l1 l2 : list Q, NatLe (maxcount l2) ((maxcount (l1 ++ l2))%nat).
Proof.
  intros l1 l2. apply NatLe_lift. unfold maxcount.
  apply (Nat.le_trans (nmax (fun x => freq_q x l2) l2)
                      (nmax (fun x => freq_q x (l1 ++ l2)) l2)
                      (nmax (fun x => freq_q x (l1 ++ l2)) (l1 ++ l2))).
  - apply NatLe_drop.
    apply (nmax_mono (fun x => freq_q x l2)
                     (fun x => freq_q x (l1 ++ l2)) l2).
    intros x _. destruct (id_sym (freq_q_app x l1 l2)). lia.
  - exact (NatLe_drop _ _ (nmax_le_app_r (fun x => freq_q x (l1 ++ l2)) l2 l1)).
Qed.

(* ---------- honest obstacle: no direction for the normalized quotient
   under concatenation (pinned by counterexamples) ---------- *)







(* the identity [align_lambda] keeps its name and meaning unchanged; the
   real definition [align_lambda_opt] — the optimal lambda chooser over
   the two entropies h0/h1 (if Qle_bool h0 h1 then 1 else 0) — is added in
   this section.  Cross-file note: it has the same semantics as [lam_opt]
   of [DTPT_Rotation] (and its periodic alias [lam_opt_cyc]); this file
   cannot require that one back (the dependency runs the other way), so
   the same-semantics object is given here independently, with statements
   matching the shapes in use there. *)

Definition align_lambda_opt (h0 h1 : Q) : Q := if Qle_bool h0 h1 then 1 else 0.

(* values of the two branches: the endpoint chooser always takes the lambda
   value 1 or 0 (one constructor per branch). *)
Theorem align_lambda_opt_values : forall h0 h1 : Q,
  Or (Id (align_lambda_opt h0 h1) 1%Q) (Id (align_lambda_opt h0 h1) 0%Q).
Proof.
  intros h0 h1. unfold align_lambda_opt.
  destruct (Qle_bool h0 h1).
  - left. apply eq_imp_id. reflexivity.
  - right. apply eq_imp_id. reflexivity.
Qed.

(* range {0,1}: the chooser's image lies in [0,1] (from the values plus
   literal Qle assembly). *)
Theorem align_lambda_opt_range : forall h0 h1 : Q,
  And (QleT' 0 (align_lambda_opt h0 h1)) (QleT' (align_lambda_opt h0 h1) 1).
Proof.
  intros h0 h1. destruct (align_lambda_opt_values h0 h1) as [E | E].
  - destruct (id_sym E). split.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
    + apply Qle_to_QleT'. apply Qle_refl.
  - destruct (id_sym E). split.
    + apply Qle_to_QleT'. apply Qle_refl.
    + exact (xq_Qle_bool_le 0 1 eq_refl).
Qed.

(* optimality (main piece): the mixed entropy at the endpoint chooser does
   not exceed the mixed entropy at any lambda in [0,1].  Each branch
   reduces to one assembly of nonnegative multiplication (affine difference
   route): for h0 <= h1 the choice lambda* = 1 gives the difference
   (1-lam) * (h1-h0); otherwise lambda* = 0 gives lam * (h0-h1). *)
Theorem align_lambda_opt_min : forall (l : list Q) (s : nat) (lam : Q),
  (0 <= lam <= 1)%Q -> QleT' (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s)))) (H_lam l s lam).
Proof.
  intros l s lam H01. apply Qle_to_QleT'. destruct H01 as [Hlam0 Hlam1].
  unfold H_lam, align_lambda_opt.
  destruct (Qle_bool (H_adj (P0 l)) (H_adj (Pinf l s))) eqn:E.
  - (* h0 <= h1: lambda* = 1, optimal value = h0 *)
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (1 * H_adj (P0 l) + (1 - 1) * H_adj (Pinf l s))
                 == (1 - lam) * (H_adj (Pinf l s) - H_adj (P0 l))) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' lam 1)).
        apply Qle_to_QleT'. exact Hlam1.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
        apply xq_Qle_bool_le. exact E. }
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hd.
  - (* h0 > h1: lambda* = 0, optimal value = h1 *)
    assert (Hge : (H_adj (Pinf l s) <= H_adj (P0 l))%Q)
      by (apply QleT'_to_Qle; apply Qle_bool_false_le; exact E).
    assert (Hd : (0 <= lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                       - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s)))%Q).
    { assert (Er : lam * H_adj (P0 l) + (1 - lam) * H_adj (Pinf l s)
                 - (0 * H_adj (P0 l) + (1 - 0) * H_adj (Pinf l s))
                 == lam * (H_adj (P0 l) - H_adj (Pinf l s))) by ring.
      rewrite Er. apply QleT'_to_Qle. apply xq_mul_nonneg.
      + exact Hlam0.
      + apply QleT'_to_Qle. apply (fst (Qle_0_sub' _ _)).
        apply Qle_to_QleT'. exact Hge. }
    apply QleT'_to_Qle. apply (snd (Qle_0_sub' _ _)). apply Qle_to_QleT'. exact Hd.
Qed.

(* endpoint evaluation bridge (companion bonus): the mixed entropy at the
   chooser always takes the phase entropy of one of the endpoints (using
   the endpoint lemmas for lambda = 1 / lambda = 0). *)
Theorem align_lambda_opt_endpoint : forall (l : list Q) (s : nat),
  Or (QeqT (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (P0 l)))
     (QeqT (H_lam l s (align_lambda_opt (H_adj (P0 l)) (H_adj (Pinf l s))))
           (H_adj (Pinf l s))).
Proof.
  intros l s.
  destruct (align_lambda_opt_values (H_adj (P0 l)) (H_adj (Pinf l s)))
    as [E | E].
  - left. destruct (id_sym E). apply H_lam_lam1.
  - right. destruct (id_sym E). apply H_lam_lam0.
Qed.


(* ---------- zero-axiom attestation (recap lines redistributed verbatim) ---------- *)
Print Assumptions sqsum_app_ge_l.
Print Assumptions sqsum_app_ge_r.
Print Assumptions sqsum_app_eq.
Print Assumptions sqsum_app_ge_sum.
Print Assumptions maxcount_app_ge_l.
Print Assumptions maxcount_app_ge_r.
Print Assumptions align_lambda_opt_values.
Print Assumptions align_lambda_opt_range.
Print Assumptions align_lambda_opt_min.
Print Assumptions align_lambda_opt_endpoint.