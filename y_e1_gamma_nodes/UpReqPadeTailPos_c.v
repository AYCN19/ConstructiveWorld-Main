(* ConstructiveWorld-Main - the core step identity and the all-quantified
   n=1 Pade tail series theorem. *)

(** * UpReqPadeTailPos_c: the denominator-clearing core and the
      tail-series theorem.

    Mission.  The induction step identity [ptp_step_core]: both sides
      of the step difference, after multiplication by the positive
      common denominator, reduce to the merge multiplication form
      (Qmult_inj_r with positivity witnesses, quotient elimination,
      merge substitution, field).  On top of it the induction
      theorem [ptp_main_fg] (F k = G k for all k), the all-quantified
      closed forms [ptp_tail_series_k] and [ptp_tail_series], the
      coefficient rechecks, and the carrier agreement instance
      [ptp_tail_FG_agree_half].  Sentinels live in UpReqPadeTailPos_cert.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,
      UpReqPadeQLeg, UpReqPadeExp, the sibling pieces
      UpReqPadeTailPos_a and UpReqPadeTailPos_b; Stdlib QArith,
      Arith, Lia, Setoid, Morphisms, Extraction.
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeTailPos (its second section, core part);
      numeric sentinels in UpReqPadeTailPos_cert.
    Constructivity.  Pure Set-level equalities on rationals; the
      core identity is closed by explicit rewriting plus field over
      free variables; no classical principles, no axioms; every
      audited name is Closed under the global context.
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
From Stdlib Require Import Extraction.
Require Import UpReqPadeTailPos_a.
Require Import UpReqPadeTailPos_b.
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== engine four: the denominator-clearing core (induction-step
   difference identity).  Route: multiply both sides by the positive
   D = 2*u3*v4*w, eliminate the quotients term by term through
   ptp_div_clear_r, substitute the merge multiplication form, finish
   by field. ===== *)

Lemma ptp_step_core : forall k y,
  (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
    * (1 + - (1#2) * y)
  == - ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                 * q_pow y (Datatypes.S (3 + k))))
     + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))
     + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                   / q_fact (Datatypes.S (3 + k)))).
Proof.
  intros k y.
  unfold ptp_beta. cbn [Nat.add Nat.mul].
  replace (k%nat + 1%nat)%nat with (Datatypes.S k) by lia.
  remember (q_pow y (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
    as Aeq eqn:HA.
  assert (Hw0 : ~ (q_fact (Datatypes.S k) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hu0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hv0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (HD : ~ (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                   * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                       (Datatypes.S k)))))
                  * q_fact (Datatypes.S k) == 0)).
  { apply q_neq_of_lt. apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply Qmult_lt_0_compat; [exact Q2_pos | apply q_fact_pos].
      + apply q_fact_pos.
    - apply q_fact_pos. }
  apply (proj1 (Qmult_inj_r _ _ _ HD)).
  (* LHS clearing *)
  rewrite <- (Qmult_assoc (Aeq / q_fact (Datatypes.S (Datatypes.S
              (Datatypes.S (Datatypes.S k)))))
              (1 + - (1#2) * y)
              (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
               * q_fact (Datatypes.S k))).
  assert (HcL : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * ((1 + - (1#2) * y)
                   * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))
                       * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                           (Datatypes.S k)))))
                      * q_fact (Datatypes.S k)))
                == Aeq * ((1 + - (1#2) * y)
                          * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                              (Datatypes.S k)))
                             * q_fact (Datatypes.S k)))).
  { apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             ((1 + - (1#2) * y)
              * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                  * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * q_fact (Datatypes.S k)))
             ((1 + - (1#2) * y)
              * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                 * q_fact (Datatypes.S k))));
    [ exact Hv0 | ring ]. }
  rewrite HcL.
  (* RHS: spread the denominator D block by block and clear it, with explicit instances guarding against a wrong spread on the LHS *)
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq))
              + (1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (- ((1#2) * (y * Aeq
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))))
              )
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq)))
             ((1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  (* block B: beta/w * A * D *)
  rewrite (ptp_opp_mul_move ((1#2) * (q_fact 1 * q_fact (Datatypes.S
             (Datatypes.S k))
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))
             / q_fact (Datatypes.S k) * Aeq))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (1#2)
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k) * Aeq)
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k))
             Aeq
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcB1 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k))))
                  / q_fact (Datatypes.S k))
                 * (Aeq * (((1 + 1)%Q
                            * q_fact (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))
                            * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))))
                           * q_fact (Datatypes.S k)))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                     / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))
                              * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                  (Datatypes.S k))))))).
  { apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
             (q_fact (Datatypes.S k))
             (Aeq * (((1 + 1)%Q
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                          (Datatypes.S k)))))
                     * q_fact (Datatypes.S k)))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))));
    [ exact Hw0 | ring ]. }
  rewrite HcB1.
  assert (HcB2 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * (Aeq * ((1 + 1)%Q
                           * q_fact (Datatypes.S (Datatypes.S
                               (Datatypes.S k)))
                           * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                               (Datatypes.S k))))))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))))).
  { apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k))))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))));
    [ exact Hv0 | ring ]. }
  rewrite HcB2.
  (* block C: A/u3 * D *)
  rewrite <- (Qmult_assoc (1#2)
             (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcC : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == Aeq * ((1 + 1)%Q
                          * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          * q_fact (Datatypes.S k))).
  { apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             (((1 + 1)%Q
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k))))
               * q_fact (Datatypes.S k))));
    [ exact Hu0 | ring ]. }
  rewrite HcC.
  (* block D: y*A/v4 * D *)
  rewrite (ptp_opp_mul_move ((1#2) * (y * Aeq
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (1#2)
             (y * Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcD : ((y * Aeq) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == (y * Aeq) * ((1 + 1)%Q
                                * q_fact (Datatypes.S (Datatypes.S
                                    (Datatypes.S k)))
                                * q_fact (Datatypes.S k))).
  { apply (ptp_div_clear_r (y * Aeq)
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             ((1 + 1)%Q
              * q_fact (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))
               * q_fact (Datatypes.S k)));
    [ exact Hv0 | ring ]. }
  rewrite HcD.
  (* merge substitution (multiplication form, brackets aligned) *)
  rewrite (Qmult_comm Aeq
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             Aeq).
  rewrite (Qmult_comm (1 + 1)%Q
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (1 + 1)%Q).
  rewrite (ptp_n1_merge (Datatypes.S k)).
  field.
Qed.

(* ===== engine five: main statement, the all-quantified identity ===== *)

Lemma ptp_main_fg : forall k : nat, forall y : Q, ptp_F k y == ptp_G k y.
Proof.
  induction k as [| k IH].
  - intro y. unfold ptp_F, ptp_G.
    unfold ptp_beta_prefix, ptp_beta, pade_den, pade_num, pade_coeff.
    cbn. field.
  - intro y. rewrite ptp_F_step. rewrite ptp_G_step.
    rewrite <- ptp_G_eq. rewrite IH. rewrite (ptp_step_core k y).
    reflexivity.
Qed.

Theorem ptp_tail_series_k : forall (k : nat) (y : Q),
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     - (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)).
Proof.
  intros k y. change (ptp_F k y == ptp_G k y). apply ptp_main_fg.
Qed.

Theorem ptp_tail_series : forall (N : nat) (y : Q), (3 <= N)%nat ->
  exp_partial N y * pade_den 1 y - pade_num 1 y
  == - ((1#2) * ptp_beta_prefix 1 (N - 3) y)
     - (1#2) * (q_pow y (Datatypes.S N) / q_fact N).
Proof.
  intros N y HN.
  replace N with (3%nat + (N - 3)%nat)%nat by lia.
  replace (3%nat + (N - 3)%nat - 3%nat)%nat with (N - 3)%nat by lia.
  apply (ptp_tail_series_k (N - 3) y).
Qed.

(* ===== check anchors: N=3/N=4 closed forms against ptp_n1_poly
   coefficient by coefficient; the two sides agree at y = 1/2. ===== *)

Lemma ptp_series_n1_N3 : forall y : Q,
  - ((1#2) * ptp_beta_prefix 1 0 y)
    + - ((1#2) * (q_pow y (4 + 0) / q_fact (3 + 0)))
  == - ((1#12) * q_pow y 3 + (1#12) * q_pow y 4).
Proof. intro y. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

Lemma ptp_series_n1_N4 : forall y : Q,
  - ((1#2) * ptp_beta_prefix 1 1 y)
    + - ((1#2) * (q_pow y (4 + 1) / q_fact (3 + 1)))
  == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5).
Proof. intro y. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

(* the N=4 special case, statement face identical to ptp_n1_poly *)
Lemma ptp_n1_poly_recheck : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5).
Proof.
  intro y.
  change (ptp_F 1 y
          == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4
                + (1#48) * q_pow y 5)).
  transitivity (ptp_G 1 y).
  - apply ptp_main_fg.
  - unfold ptp_G. apply ptp_series_n1_N4.
Qed.

(* the carrier agreement instance of the all-quantified statement *)
Lemma ptp_tail_FG_agree_half : ptp_F 1 (1#2) == ptp_G 1 (1#2).
Proof. apply ptp_main_fg. Qed.

Print Assumptions ptp_tail_series.
Print Assumptions ptp_tail_series_k.
Print Assumptions ptp_main_fg.
Print Assumptions ptp_step_core.
Print Assumptions ptp_n1_merge.
Print Assumptions ptp_n1_poly_recheck.

Separate Extraction ptp_tail_series ptp_step_core ptp_n1_merge.
