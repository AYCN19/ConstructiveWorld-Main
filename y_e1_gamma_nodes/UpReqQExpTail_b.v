(* ConstructiveWorld-Main - UpReqQExpTail_b.v - Q exponent tail engine part B: statement surface preserved verbatim from UpReqQExpTail.v (seat1 bound surgery split). *)
(* ==========================================================================
   Mission. Split B of UpReqQExpTail (bound surgery, seat1): tail-sum definition (guarded fold), nonnegativity, monotonicity, and the term-decay lemma (b^k/k! decay).
   Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp; Stdlib
     QArith, Setoid, Morphisms, Lia, QArith.Qminmax.
   References. Exponential-decay series tail control and constructive Cauchy
     modulus (convergence construction); source of record: UpReqQExpTail.v
     in the debtscan closure dossier (all-green at surgery time).
   Constructivity. All proofs end in Qed with zero admission literals, no
     classical logic; the statement surface is Set-carried (order predicates
     and equality are Set-valued, zero Prop leakage).
   Build. coqc -q -native-compiler no -Q l0_local "" -Q build "" (Rocq 9.3.0
     at D:/ComplexAnalysis/attn/opam93), compile gate wrapped by
     50_toolkit/cpu_guard_v3.ps1; accepted by 50_toolkit/accept_node.py
     six-chain gate, node UpReqQExpTail.
   ========================================================================== *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround
               Lists.List Bool.Bool Arith.Arith Arith.Factorial.
Import ListNotations.
From Stdlib Require Import Setoid Morphisms Lia QArith.Qminmax.
Require Import UpReqQExpTail_a.

(* ================= S1: tail sum definition + nonnegativity + monotonicity ================= *)

(* qtail_sum b m n = sum over k in [m, n-1] of b^k/k!; the n<m guard prevents nat
   subtraction truncation (empty sum = 0) *)
Fixpoint qtail_sum (b : Q) (m n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => (if Nat.leb m n' then q_pow b n' / q_fact n' else 0)
                      + qtail_sum b m n'
  end.

Lemma qtail_sum_le_m : forall b m n, (n <= m)%nat -> qtail_sum b m n == 0.
Proof.
  intros b m n Hn. revert Hn.
  induction n as [| n IH]; intro Hn.
  - reflexivity.
  - change (qtail_sum b m (Datatypes.S n))
      with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E. exfalso. lia.
    + rewrite IH by lia. reflexivity.
Qed.

Lemma qtail_sum_add : forall b m p n, (m <= p)%nat -> (p <= n)%nat ->
  qtail_sum b m n == qtail_sum b m p + qtail_sum b p n.
Proof.
  intros b m p n Hmp Hpn. revert Hpn.
  induction n as [| n IH]; intro Hpn.
  - assert (Hp : p = 0%nat) by lia. subst p.
    rewrite (qtail_sum_le_m b 0 0) by lia.
    ring.
  - destruct (Nat.eq_dec p (Datatypes.S n)) as [HpSn | Hplt].
    + subst p.
      rewrite (qtail_sum_le_m b (Datatypes.S n) (Datatypes.S n)) by lia.
      ring.
    + assert (Hpn' : (p <= n)%nat) by lia.
      change (qtail_sum b m (Datatypes.S n))
        with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
      change (qtail_sum b p (Datatypes.S n))
        with ((if Nat.leb p n then q_pow b n / q_fact n else 0) + qtail_sum b p n).
      rewrite (IH Hpn').
      destruct (Nat.leb m n) eqn:Em; destruct (Nat.leb p n) eqn:Ep.
      * ring.
      * apply Nat.leb_gt in Ep. exfalso. lia.
      * apply Nat.leb_gt in Em. exfalso. lia.
      * ring.
Qed.

Lemma qtail_geo_nonneg : forall n : nat, Qle 0 (geo_sum n).
Proof.
  induction n as [| n IH].
  - apply Qle_refl.
  - change (geo_sum (Datatypes.S n)) with (geo_sum n + q_pow (1 / 2) n).
    apply (Qle_trans _ (q_pow (1 / 2) n) _).
    + apply q_pow_nonneg. apply Qhalf_nonneg.
    + apply (Qle_trans (q_pow (1 / 2) n) (0 + q_pow (1 / 2) n)
                       (geo_sum n + q_pow (1 / 2) n)).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat 0 (geo_sum n) (q_pow (1 / 2) n) (q_pow (1 / 2) n)).
        -- exact IH.
        -- apply Qle_refl.
Qed.

Lemma qtail_sum_nonneg_aux : forall b m n, Qle 0 b -> Qle 0 (qtail_sum b m n).
Proof.
  intros b m n Hb. induction n as [| n IH].
  - apply Qle_refl.
  - change (qtail_sum b m (Datatypes.S n))
      with ((if Nat.leb m n then q_pow b n / q_fact n else 0) + qtail_sum b m n).
    destruct (Nat.leb m n) eqn:E.
    + apply Nat.leb_le in E.
      apply (Qle_trans _ (q_pow b n / q_fact n) _).
      * apply q_pow_fact_nonneg. exact Hb.
      * apply (qtail_le_plus_r _ (qtail_sum b m n)). apply IH.
    + setoid_replace (0 + qtail_sum b m n) with (qtail_sum b m n) by ring.
      apply IH.
Qed.

(* the tail sum grows with n (monotonicity) *)
Lemma qtail_sum_mono_aux : forall b m n1 n2,
  Qle 0 b -> (m <= n1)%nat -> (n1 <= n2)%nat -> Qle (qtail_sum b m n1) (qtail_sum b m n2).
Proof.
  intros b m n1 n2 Hb H1 H2. revert H2.
  induction n2 as [| n2 IH]; intro H2.
  - assert (Hn1 : n1 = 0%nat) by lia. subst n1. apply Qle_refl.
  - destruct (Nat.eq_dec n1 (Datatypes.S n2)) as [He | Hd].
    + rewrite He. apply Qle_refl.
    + assert (H12 : (n1 <= n2)%nat) by lia.
      apply (Qle_trans _ (qtail_sum b m n2) _).
      * apply IH; assumption.
      * change (qtail_sum b m (Datatypes.S n2))
          with ((if Nat.leb m n2 then q_pow b n2 / q_fact n2 else 0) + qtail_sum b m n2).
        destruct (Nat.leb m n2) eqn:E.
        -- apply Nat.leb_le in E.
           apply (Qle_trans (qtail_sum b m n2) (0 + qtail_sum b m n2)
                            (q_pow b n2 / q_fact n2 + qtail_sum b m n2)).
           ++ apply qeq_le. ring.
           ++ apply (Qplus_le_compat 0 (q_pow b n2 / q_fact n2)
                          (qtail_sum b m n2) (qtail_sum b m n2)).
              ** apply q_pow_fact_nonneg. exact Hb.
              ** apply Qle_refl.
        -- apply Nat.leb_gt in E. exfalso. lia.
Qed.

(* S1 exit (Set-carried, QleT' form) *)
Lemma qtail_sum_nonneg : forall b m n, QleT' 0 b -> QleT' 0 (qtail_sum b m n).
Proof.
  intros b m n Hb. apply Qle_to_QleT'.
  apply qtail_sum_nonneg_aux. apply (QleT'_to_Qle 0 b). exact Hb.
Qed.

Lemma qtail_sum_mono : forall b m n1 n2,
  QleT' 0 b -> (m <= n1)%nat -> (n1 <= n2)%nat ->
  QleT' (qtail_sum b m n1) (qtail_sum b m n2).
Proof.
  intros b m n1 n2 Hb H1 H2. apply Qle_to_QleT'.
  apply qtail_sum_mono_aux.
  - apply (QleT'_to_Qle 0 b). exact Hb.
  - exact H1.
  - exact H2.
Qed.

(* ================= S2-Q: tail term decay control ================= *)

(* b^k/k! <= (b^4/4!) * (b/2)^(k-4) for k >= 4; holds for any b >= 0, the case split
   is handled at the main lemma *)
Lemma qtail_term_decay_aux : forall (b : Q) (j : nat), Qle 0 b ->
  Qle (q_pow b (4 + j) / q_fact (4 + j)) ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j).
Proof.
  intros b j Hb. induction j as [| j IH].
  - apply qeq_le. simpl. ring.
  - replace (4 + Datatypes.S j)%nat with (Datatypes.S (4 + j))%nat by lia.
    rewrite (q_pow_succ b (4 + j)), (q_fact_succ (4 + j)).
    assert (Hc0 : ~ ((Z.of_nat (Datatypes.S (4 + j)) # 1) == 0)).
    { apply qtail_neq0. apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia. }
    assert (Hfc0 : ~ (q_fact (4 + j) == 0)) by (apply qtail_neq0; apply q_fact_pos).
    assert (HCj : Qle 0 ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j)).
    { apply Qmult_le_0_compat.
      - apply q_pow_fact_nonneg. exact Hb.
      - apply q_pow_nonneg.
        apply (Qle_trans 0 (b * (1 / 2)) (b / 2)).
        + apply (Qmult_le_0_compat).
          * exact Hb.
          * apply Qhalf_nonneg.
        + apply qeq_le. reflexivity. }
    assert (Hbc0 : Qle 0 (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
    { apply (q_le_div_le 0 1 b (Z.of_nat (Datatypes.S (4 + j)) # 1)).
      - apply qtail_Qlt01.
      - apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia.
      - apply (Qle_trans (0 * (Z.of_nat (Datatypes.S (4 + j)) # 1)) 0 (b * 1)).
        + apply qeq_le. ring.
        + apply (Qle_trans 0 b (b * 1)).
          * exact Hb.
          * apply qeq_le. ring. }
    apply (Qle_trans _
      ((q_pow b (4 + j) / q_fact (4 + j)) * (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))) _).
    + apply qeq_le.
      rewrite (Qmult_comm (q_pow b (4 + j) / q_fact (4 + j))
                          (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
      apply (qtail_div_split b (Z.of_nat (Datatypes.S (4 + j)) # 1)
                              (q_pow b (4 + j)) (q_fact (4 + j))).
      * exact Hc0.
      * exact Hfc0.
    + apply (Qle_trans _
        ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j
           * (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))) _).
      * apply (Qmult_le_compat_r _ _ (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))).
        -- exact IH.
        -- exact Hbc0.
      * apply (Qle_trans _
          ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j * (b / 2)%Q) _).
        -- apply (qtail_mult_le_compat_l
                    (b / (Z.of_nat (Datatypes.S (4 + j)) # 1))
                    (b / 2)%Q ((q_pow b 4 / q_fact 4) * q_pow (b / 2) j)).
           ++ apply (q_le_div_le b (Z.of_nat (Datatypes.S (4 + j)) # 1) b 2%Q).
              ** apply (Qlt_of_nat_lt 0 (Datatypes.S (4 + j))). lia.
              ** apply Q2_pos.
              ** apply (Qle_trans _ (2 * b)%Q).
                 --- apply qeq_le. ring.
                 --- apply (Qle_trans _
                              ((Z.of_nat (Datatypes.S (4 + j)) # 1) * b)).
                     +++ apply (Qmult_le_compat_r 2
                                  (Z.of_nat (Datatypes.S (4 + j)) # 1) b).
                         *** apply (Qle_of_nat 2 (Datatypes.S (4 + j))). lia.
                         *** exact Hb.
                     +++ apply qeq_le. ring.
           ++ exact HCj.
        -- apply qeq_le.
           rewrite (q_pow_succ (b / 2) j).
           ring.
Qed.

Lemma qtail_term_decay : forall (b : Q) (k : nat), QleT' 0 b -> (4 <= k)%nat ->
  QleT' (q_pow b k / q_fact k) ((q_pow b 4 / q_fact 4) * q_pow (b / 2) (k - 4)).
Proof.
  intros b k Hb Hk. apply Qle_to_QleT'.
  remember (k - 4)%nat as j eqn:Ej.
  replace k with (4 + j)%nat by lia.
  apply qtail_term_decay_aux. apply (QleT'_to_Qle 0 b). exact Hb.
Qed.

