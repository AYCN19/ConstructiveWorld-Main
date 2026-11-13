(* ConstructiveWorld-Main - the signed positive-tail prefix and the
   induction engine of the n=1 Pade tail identity. *)

(** * UpReqPadeTailPos_b: the prefix carrier, the positivity theorem,
      the coefficient anchors kit and the step engine.

    Mission.  The prefix carrier [ptp_beta_prefix n M y] of the
      signed positive-tail series, the tail summation engine, the
      closed forms of the linear Pade numerator and denominator, the
      positivity theorem [ptp_beta_pos] for every n and m, the
      polynomial identities [ptp_n1_poly] and [ptp_n2_poly] (all y),
      and the step engine of the n=1 tail identity: the two-sided
      step expansions [ptp_F_step] / [ptp_G_step] around the
      carriers [ptp_F] / [ptp_G], on the free-variable algebra kit
      and the merge form [ptp_n1_merge].  Numeric anchors live in
      UpReqPadeTailPos_cert.
    Dependencies.  S01_BaseRing, S02_CauchyComplete, S03_QExp,
      UpReqPadeQLeg, UpReqPadeExp, UpReqPadeTailPos_a; Stdlib
      QArith, Arith, Lia, Setoid, Morphisms, Extraction.
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeTailPos (its second section, engine part);
      numeric anchors in UpReqPadeTailPos_cert.
    Constructivity.  Pure Set-level content; QltT-witnessed order
      faces; polynomial identities closed by field over free
      variables; no classical principles, no axioms; every audited
      name is Closed under the global context.
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
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== definition face ===== *)

(* beta_m = n!*(n+m)!/(2n+m+1)!, the all-positive closed form of the
   remainder coefficient. *)
Definition ptp_beta (n m : nat) : Q :=
  q_fact n * q_fact (n + m) / q_fact (2 * n + m + 1).

(* Signed positive-tail prefix: sum over m <= M of
   beta_m * y^(2n+1+m) / m! (power inside the term). *)
Definition ptp_beta_prefix (n M : nat) (y : Q) : Q :=
  sum_upto (Datatypes.S M)
    (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m)).

(* ===== small engine ===== *)

(* Tail expansion of sum_upto: definitional. *)
Lemma ptp_sum_S : forall (K : nat) (f : nat -> Q),
  sum_upto (Datatypes.S K) f == sum_upto K f + f K.
Proof. intro K. intro f. exact (Qeq_refl (sum_upto (Datatypes.S K) f)). Qed.

(* Prefix stepping: prefix (S M) = prefix M + f (S M). *)
Lemma ptp_prefix_S : forall (n M : nat) (y : Q),
  ptp_beta_prefix n (Datatypes.S M) y ==
  ptp_beta_prefix n M y +
  (ptp_beta n (Datatypes.S M) / q_fact (Datatypes.S M)
     * q_pow y (2 * n + 1 + Datatypes.S M)).
Proof.
  intros n M y. unfold ptp_beta_prefix.
  rewrite (ptp_sum_S (Datatypes.S M)
             (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m))).
  reflexivity.
Qed.

(* Q1(y) = 1 - y/2 and P1(y) = 1 + y/2 (closed coefficient expansion). *)
Lemma ptp_den1 : forall y : Q, pade_den 1 y == 1 + - (1#2) * y.
Proof.
  intro y. unfold pade_den, pade_coeff. cbn. field.
Qed.

Lemma ptp_num1 : forall y : Q, pade_num 1 y == 1 + (1#2) * y.
Proof.
  intro y. unfold pade_num, pade_coeff. cbn. field.
Qed.

(* ===== positivity (all-quantified n,m, Set-level QltT exit) ===== *)

Theorem ptp_beta_pos : forall (n m : nat), QltT 0 (ptp_beta n m).
Proof.
  intros n m. apply Qlt_to_QltT.
  unfold ptp_beta. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ===== polynomial anchors one: n=1 truncation identity (all y) ===== *)
(* The coefficients -1/12, -1/24 match the full-series coefficients
   -beta_m/(2!*m!) exactly at m=0,1; the y^5 term -1/48 is the
   truncation sliver of exp_partial 4. *)
Lemma ptp_n1_poly : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12)*q_pow y 3 + (1#24)*q_pow y 4 + (1#48)*q_pow y 5).
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== polynomial anchors two: n=2 even-sign instance (all y) ===== *)
(* The ten Pade matching conditions (vanishing of the coefficients of
   y^0..y^4) are read off the missing low-order terms on the right;
   the y^7 coefficient is exactly zero; the leading y^5/720 =
   (2!)^2/(4!*5!). *)
Lemma ptp_n2_poly : forall y : Q,
  exp_partial 6 y * pade_den 2 y - pade_num 2 y
  == (1#720)*q_pow y 5 + (1#1440)*q_pow y 6 + (1#8640)*q_pow y 8.
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== engine zero: free-variable algebra kit ===== *)

Lemma ptp_AC_swap_m : forall a b c : Q, a + b - c == a - c + b.
Proof. intros a b c. unfold Qminus. ring. Qed.

Lemma ptp_opp_plus : forall a b : Q, - (a + b) == - a + - b.
Proof. intros a b. unfold Qminus. ring. Qed.

Lemma ptp_opp_mul_move : forall a b : Q, (- a) * b == - (a * b).
Proof. intros a b. ring. Qed.

Lemma ptp_G_alg : forall a b c p : Q, (a + b) + c == (a + (- p)) + ((b + p) + c).
Proof. intros a b c p. ring. Qed.

Lemma ptp_Qmake_plus : forall a b : Z, (a + b) # 1 == (a # 1) + (b # 1).
Proof. intros a b. unfold Qeq. simpl. lia. Qed.

(* ===== engine one: denominator elimination (cross multiplication
   with positivity present) ===== *)

Lemma ptp_div_clear_r : forall x d D E : Q,
  ~ (d == 0) -> D == E * d -> x / d * D == x * E.
Proof.
  intros x d D E Hd HDE. unfold Qdiv. rewrite HDE.
  rewrite (Qmult_comm E d).
  rewrite <- (Qmult_assoc x (Qinv d) (d * E)).
  rewrite (Qmult_assoc (Qinv d) d E).
  rewrite (Qmult_comm (Qinv d) d). rewrite (Qmult_inv_r d Hd).
  rewrite Qmult_1_l. reflexivity.
Qed.

(* ===== engine two: merge multiplication form ===== *)

Lemma ptp_n1_merge : forall m : nat,
  q_fact 1 * q_fact (Datatypes.S m) * q_fact (Datatypes.S (Datatypes.S m))
  == (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))
      - (1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S m))) * q_fact m.
Proof.
  intro m.
  rewrite (q_fact_succ (Datatypes.S (Datatypes.S m))).
  rewrite (q_fact_succ (Datatypes.S m)).
  rewrite (q_fact_succ m).
  rewrite (q_fact_succ 0%nat).
  cbn [q_fact].
  replace (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m))))
    with (Z.of_nat m + 3)%Z by lia.
  replace (Z.of_nat (Datatypes.S (Datatypes.S m)))
    with (Z.of_nat m + 2)%Z by lia.
  replace (Z.of_nat (Datatypes.S m)) with (Z.of_nat m + 1)%Z by lia.
  replace (Z.of_nat 1) with 1%Z by lia.
  rewrite (ptp_Qmake_plus (Z.of_nat m) 3%Z).
  rewrite (ptp_Qmake_plus (Z.of_nat m) 2%Z).
  rewrite (ptp_Qmake_plus (Z.of_nat m) 1%Z).
  field.
Qed.

(* ===== engine three: the two-sided step carriers ===== *)

Definition ptp_F (k : nat) (y : Q) : Q :=
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y.

Definition ptp_G (k : nat) (y : Q) : Q :=
  - ((1#2) * ptp_beta_prefix 1 k y)
    - (1#2) * (q_pow y (4 + k) / q_fact (3 + k)).

Lemma ptp_exp_S : forall (n : nat) (y : Q),
  exp_partial (Datatypes.S n) y
  == exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n).
Proof. intros n y. exact (Qeq_refl (exp_partial (Datatypes.S n) y)). Qed.

Lemma ptp_G_eq : forall k y,
  ptp_G k y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))).
Proof.
  intros k y. unfold ptp_G, Qminus.
  replace (4%nat + k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  reflexivity.
Qed.

Lemma ptp_F_step : forall k y,
  ptp_F (Datatypes.S k) y
  == ptp_F k y
     + ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
        * (1 + - (1#2) * y)).
Proof.
  intros k y. unfold ptp_F.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite ptp_exp_S. rewrite ptp_den1. rewrite ptp_num1.
  rewrite (Qmult_plus_distr_l (exp_partial (3 + k) y)
             (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
             (1 + - (1#2) * y)).
  rewrite (ptp_AC_swap_m
             (exp_partial (3 + k) y * (1 + - (1#2) * y))
             ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
              * (1 + - (1#2) * y))
             (1 + (1#2) * y)).
  reflexivity.
Qed.

Lemma ptp_G_step : forall k y,
  ptp_G (Datatypes.S k) y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))
     + (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                    * q_pow y (Datatypes.S (3 + k))))
        + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))
        + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                      / q_fact (Datatypes.S (3 + k))))).
Proof.
  intros k y. unfold ptp_G.
  replace (4%nat + Datatypes.S k)%nat
    with (Datatypes.S (Datatypes.S (3%nat + k)%nat)) by lia.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite ptp_prefix_S.
  replace (2%nat * 1%nat + 1%nat + Datatypes.S k)%nat with (Datatypes.S (3%nat + k)%nat) by lia.
  rewrite (q_pow_succ y (Datatypes.S (3 + k))).
  rewrite (Qmult_plus_distr_r (1#2) (ptp_beta_prefix 1 k y)
             (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
              * q_pow y (Datatypes.S (3 + k)))).
  rewrite (ptp_opp_plus ((1#2) * ptp_beta_prefix 1 k y)
             ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                       * q_pow y (Datatypes.S (3 + k))))).
  rewrite (ptp_G_alg (- ((1#2) * ptp_beta_prefix 1 k y))
             (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                          * q_pow y (Datatypes.S (3 + k)))))
             (- ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                          / q_fact (Datatypes.S (3 + k)))))
             ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))).
  reflexivity.
Qed.

Print Assumptions ptp_beta_pos.
Print Assumptions ptp_n1_poly.
Print Assumptions ptp_n2_poly.

Separate Extraction ptp_beta_pos ptp_beta ptp_beta_prefix
  ptp_n1_poly ptp_n2_poly.
