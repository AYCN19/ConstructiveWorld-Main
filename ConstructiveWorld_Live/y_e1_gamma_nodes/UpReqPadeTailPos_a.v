(* ConstructiveWorld-Main - closed-form positivity of the Pade remainder
   coefficient beta_m. *)

(** * UpReqPadeTailPos_a: the closed-form beta coefficient and its
      positivity and sign-transfer kit.

    Mission.  The coefficient [pbp_beta n m] =
      [n! * (n+m)! / (2n+m+1)!] with its explicit lower-bound witness
      [1/(2n+m+1)!]; strict positivity [pbp_beta_pos] in the Set-level
      QltT witness form, the sigT witness record
      [pbp_beta_pos_sigT], the well-definedness face of the
      factorial ratio, the nonzero-denominator face, the Qeq
      transport leg, sign transfer to the leading remainder
      coefficient, the bound [beta_m <= n!], and the factorial
      monotonicity kit.  The three closed numeric anchors live in
      UpReqPadeTailPos_cert.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,
      UpReqPadeQLeg; Stdlib QArith, Arith, Lia, Setoid, Morphisms,
      Extraction.
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeTailPos (its first section); numeric anchors in
      UpReqPadeTailPos_cert.
    Constructivity.  Pure Set-level content; strict positivity is
      carried by QltT witnesses; no classical principles, no axioms;
      every audited name is Closed under the global context.
    Build.  coqc -q -native-compiler no with the l0_local face plus
      the node build face, Coq 9.3.0, wrapped by the temperature
      guard.
*)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
From Stdlib Require Import Setoid Morphisms.

(* ===== S1 factorial face ===== *)

(* Every factorial is at least 1 (induction on the index; successor
   step by both-factor multiplication). *)
Lemma pbp_qfact_ge1 : forall k : nat, QleT' 1%Q (q_fact k).
Proof.
  induction k as [| j IH].
  - change (QleT' 1%Q 1%Q). apply qleT'_refl.
  - apply Qle_to_QleT'.
    assert (H1 : Qle 1%Q ((Z.of_nat (Datatypes.S j) # 1)))
      by (unfold Qle; cbn [Qnum Qden]; lia).
    change (Qle (1%Q * 1%Q) ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
    apply (Qmult_le_compat_nonneg 1%Q ((Z.of_nat (Datatypes.S j) # 1)) 1%Q (q_fact j)).
    + split.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * exact H1.
    + split.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * apply (QleT'_to_Qle 1%Q (q_fact j)). exact IH.
Qed.

(* Factorial monotone (Set-level <= face): a <= b implies a! <= b!.
   Route: Nat bridge lia (i <= j), successor expansion of q_fact
   (exact conversion face), both-factor Qmult_le_compat_r with ring
   normalization on the swapped sides. *)
Lemma pbp_qfact_mono : forall a b : nat, (a <= b)%nat -> QleT' (q_fact a) (q_fact b).
Proof.
  intros a b. revert a.
  induction b as [| j IH]; intros a H.
  - assert (Ha : a = 0%nat) by lia. subst a. apply qleT'_refl.
  - destruct a as [| i].
    + exact (pbp_qfact_ge1 (Datatypes.S j)).
    + assert (Hij : (i <= j)%nat) by lia.
      specialize (IH i Hij).
      assert (Hprod : Qle ((Z.of_nat (Datatypes.S i) # 1) * q_fact i)
                          ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      { apply (Qle_trans _ (q_fact i * (Z.of_nat (Datatypes.S i) # 1))).
        - apply qeq_le. ring.
        - apply (Qle_trans _ ((Z.of_nat (Datatypes.S i) # 1) * q_fact j)).
          + apply (Qle_trans _ (q_fact j * (Z.of_nat (Datatypes.S i) # 1))).
            * apply Qmult_le_compat_r.
              -- apply (QleT'_to_Qle (q_fact i) (q_fact j)). exact IH.
              -- assert (Hsi : Qle 0%Q ((Z.of_nat (Datatypes.S i) # 1)))
                   by (unfold Qle; cbn [Qnum Qden]; lia).
                 exact Hsi.
            * apply qeq_le. ring.
          + apply Qmult_le_compat_r.
            * assert (HSij : Qle (Z.of_nat (Datatypes.S i) # 1)
                                 (Z.of_nat (Datatypes.S j) # 1))
                by (unfold Qle; cbn [Qnum Qden]; lia).
              exact HSij.
            * apply (Qlt_le_weak 0%Q (q_fact j)). apply q_fact_pos. }
      apply Qle_to_QleT'. exact Hprod.
Qed.

(* ===== S2 main: closed form and positivity of beta_m ===== *)

(* beta_m: the positive-tail series coefficient of the Pade remainder. *)
Definition pbp_beta (n m : nat) : Q :=
  (q_fact n * q_fact (n + m)) / q_fact (2 * n + m + 1).

(* Explicit lower-bound witness: 1/(2n+m+1)! (a computable positive
   rational carrying the positivity). *)
Definition pbp_beta_lb (n m : nat) : Q := 1%Q / q_fact (2 * n + m + 1).

(* Lower bound positive (Qinv strictness plus product of positives). *)
Lemma pbp_beta_lb_pos : forall n m : nat, QltT 0 (pbp_beta_lb n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold pbp_beta_lb.
  change (Qlt 0%Q (1%Q * / q_fact (2 * n + m + 1))).
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* beta_m >= the witness: numerator >= 1*1 (both factorials >= 1),
   same positive denominator (same-denominator comparison). *)
Lemma pbp_beta_ge_lb : forall n m : nat, QleT' (pbp_beta_lb n m) (pbp_beta n m).
Proof.
  intros n m.
  assert (Hn : Qle 1%Q (q_fact n))
    by (apply (QleT'_to_Qle 1%Q (q_fact n)); apply pbp_qfact_ge1).
  assert (Hm : Qle 1%Q (q_fact (n + m)))
    by (apply (QleT'_to_Qle 1%Q (q_fact (n + m))); apply pbp_qfact_ge1).
  assert (Hnum : Qle 1%Q (q_fact n * q_fact (n + m))).
  { apply (Qmult_le_compat_nonneg 1%Q (q_fact n) 1%Q (q_fact (n + m))).
    - split.
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hn.
    - split.
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hm. }
  apply Qle_to_QleT'.
  unfold pbp_beta, pbp_beta_lb.
  apply (q_le_div_le 1%Q (q_fact (2 * n + m + 1))
                     (q_fact n * q_fact (n + m)) (q_fact (2 * n + m + 1))).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply (Qmult_le_compat_r 1%Q (q_fact n * q_fact (n + m))
                              (q_fact (2 * n + m + 1)) Hnum).
    apply (Qlt_le_weak 0%Q (q_fact (2 * n + m + 1))). apply q_fact_pos.
Qed.

(* Main statement: beta_m strictly positive (QltT witness form;
   proof = positive lower bound plus the lower-bound transfer). *)
Lemma pbp_beta_pos : forall n m : nat, QltT 0 (pbp_beta n m).
Proof.
  intros n m.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0%Q (pbp_beta_lb n m) (pbp_beta n m)).
  - apply QltT_to_Qlt. apply pbp_beta_lb_pos.
  - apply (QleT'_to_Qle (pbp_beta_lb n m) (pbp_beta n m)). apply pbp_beta_ge_lb.
Qed.

(* sigT witness form (positivity lifted into the witness): the witness
   is the value of beta_m itself pinned by Id, plus its QltT
   positivity certificate. *)
Definition pbp_beta_pos_sigT (n m : nat) :
  sigT (fun b : Q => sigT (fun _ : Id b (pbp_beta n m) => QltT 0 b)) :=
  existT (fun b : Q => sigT (fun _ : Id b (pbp_beta n m) => QltT 0 b))
         (pbp_beta n m)
         (existT (fun _ : Id (pbp_beta n m) (pbp_beta n m)
                    => QltT 0 (pbp_beta n m))
                 (@id_refl Q (pbp_beta n m))
                 (pbp_beta_pos n m)).

(* ===== S3 companion one: well-definedness / nonzero denominator ===== *)

(* Denominator index Nat bridge: 2n+m+1 >= 1. *)
Lemma pbp_den_index_ge1 : forall n m : nat, (1 <= 2 * n + m + 1)%nat.
Proof. intros n m. lia. Qed.

(* Factorial-ratio well-definedness: the factorial at index
   2n+m+1 equals (2n+m+1) * (2n+m)!; the leading factor
   Z.of_nat(S(2n+m)) >= 1 via the Nat bridge. *)
Lemma pbp_beta_closed : forall n m : nat,
  q_fact (2 * n + m + 1)
  == (Z.of_nat (Datatypes.S (2 * n + m)) # 1) * q_fact (2 * n + m).
Proof.
  intros n m.
  replace (2 * n + m + 1)%nat with (Datatypes.S (2 * n + m)) by lia.
  apply q_fact_succ.
Qed.

(* Denominator positive (Set face). *)
Lemma pbp_den_posT : forall n m : nat, QltT 0 (q_fact (2 * n + m + 1)).
Proof. intros n m. apply Qlt_to_QltT. apply q_fact_pos. Qed.

(* Denominator nonzero (Prop-face bridge placement, for field use). *)
Lemma pbp_den_neq0 : forall n m : nat, ~ (q_fact (2 * n + m + 1) == 0).
Proof. intros n m. apply q_neq_of_lt. apply q_fact_pos. Qed.

(* ===== S3 companion two: sign-transfer preparation ===== *)

(* Qeq right transport leg: 0 < a carries to 0 < b when a == b
   (single hop onto the library monotonicity leg). *)
Lemma pbp_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* Sign transfer: lead == beta_m * posf with 0 < posf implies
   0 < lead (the positive factor part of the leading coefficient is
   supplied downstream; this statement only transfers the sign). *)
Lemma pbp_sign_transfer : forall (lead posf : Q) (n m : nat),
  lead == pbp_beta n m * posf ->
  QltT 0 posf ->
  QltT 0 lead.
Proof.
  intros lead posf n m Heq Hf.
  apply Qlt_to_QltT.
  apply (pbp_qlt0_eq_r (pbp_beta n m * posf) lead).
  - apply Qeq_sym. exact Heq.
  - apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. apply pbp_beta_pos.
    + apply QltT_to_Qlt. exact Hf.
Qed.

(* Additional bound: beta_m <= n! (true use of factorial monotonicity;
   for fixed n this is a concrete constant for downstream tail
   bounds). *)
Lemma pbp_beta_le_nfact : forall n m : nat, QleT' (pbp_beta n m) (q_fact n).
Proof.
  intros n m.
  assert (Hmono : Qle (q_fact (n + m)) (q_fact (2 * n + m + 1))).
  { apply (QleT'_to_Qle (q_fact (n + m)) (q_fact (2 * n + m + 1))).
    apply pbp_qfact_mono. lia. }
  assert (Hneq : ~ (q_fact (n + m) == 0)) by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hleg : Qle ((q_fact n * q_fact (n + m)) * q_fact (n + m))
                     ((q_fact n * q_fact (n + m)) * q_fact (2 * n + m + 1))).
  { apply (Qle_trans _ ((q_fact (n + m)) * (q_fact n * q_fact (n + m)))).
    - apply qeq_le. ring.
    - apply (Qle_trans _ ((q_fact (2 * n + m + 1)) * (q_fact n * q_fact (n + m)))).
      + apply Qmult_le_compat_r.
        * exact Hmono.
        * apply Qmult_le_0_compat.
          -- apply (Qlt_le_weak 0%Q (q_fact n)). apply q_fact_pos.
          -- apply (Qlt_le_weak 0%Q (q_fact (n + m))). apply q_fact_pos.
      + apply qeq_le. ring. }
  apply Qle_to_QleT'.
  unfold pbp_beta.
  apply (Qle_trans ((q_fact n * q_fact (n + m)) / q_fact (2 * n + m + 1))
                   ((q_fact n * q_fact (n + m)) / q_fact (n + m))
                   (q_fact n)).
  - apply (q_le_div_le (q_fact n * q_fact (n + m)) (q_fact (2 * n + m + 1))
                       (q_fact n * q_fact (n + m)) (q_fact (n + m))).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + exact Hleg.
  - apply qeq_le. apply (Qdiv_mult_l (q_fact n) (q_fact (n + m)) Hneq).
Qed.

From Stdlib Require Import Extraction.
Separate Extraction pbp_beta pbp_beta_lb pbp_qfact_ge1 pbp_qfact_mono
  pbp_beta_lb_pos pbp_beta_ge_lb pbp_beta_pos pbp_beta_pos_sigT
  pbp_den_index_ge1 pbp_beta_closed pbp_den_posT pbp_den_neq0
  pbp_qlt0_eq_r pbp_sign_transfer pbp_beta_le_nfact.
Print Assumptions pbp_beta.
Print Assumptions pbp_beta_lb.
Print Assumptions pbp_qfact_ge1.
Print Assumptions pbp_qfact_mono.
Print Assumptions pbp_beta_lb_pos.
Print Assumptions pbp_beta_ge_lb.
Print Assumptions pbp_beta_pos.
Print Assumptions pbp_beta_pos_sigT.
Print Assumptions pbp_den_index_ge1.
Print Assumptions pbp_beta_closed.
Print Assumptions pbp_den_posT.
Print Assumptions pbp_den_neq0.
Print Assumptions pbp_qlt0_eq_r.
Print Assumptions pbp_sign_transfer.
Print Assumptions pbp_beta_le_nfact.
