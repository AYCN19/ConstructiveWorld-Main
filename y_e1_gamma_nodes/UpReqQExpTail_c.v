(* ConstructiveWorld-Main - UpReqQExpTail_c.v - Q exponent tail engine part C: statement surface preserved verbatim from UpReqQExpTail.v (seat1 bound surgery split). *)
(* ==========================================================================
   Mission. Split C of UpReqQExpTail (bound surgery, seat1): explicit ratio machine, geometric tail bound and the constructive Cauchy modulus (sigT witness), with S4 interface
     notes toward the S03 exp series files.
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
Require Import UpReqQExpTail_b.

(* ================= S3: explicit ratio machine + geometric tail + constructive Cauchy modulus ================= *)

(* explicit bound: 2b <= (2*nat(floor b)+1)#1 *)
Lemma qtail_two_b_le : forall b : Q, Qle 0 b ->
  Qle ((1 + 1)%Q * b) (Z.of_nat (2 * Z.to_nat (Qnum b) + 1) # 1).
Proof.
  intros b Hb.
  pose proof (qtail_pos_upper b Hb) as Hp.
  apply (Qle_trans _ ((Z.of_nat (Z.to_nat (Qnum b)) # 1) * (1 + 1)%Q) _).
  - apply (Qle_trans ((1 + 1)%Q * b)
                     ((1 + 1)%Q * (Z.of_nat (Z.to_nat (Qnum b)) # 1))
                     ((Z.of_nat (Z.to_nat (Qnum b)) # 1) * (1 + 1)%Q)).
    + apply (qtail_mult_le_compat_l b (Z.of_nat (Z.to_nat (Qnum b)) # 1) (1 + 1)%Q).
      * exact Hp.
      * apply Q2_nonneg.
    + apply qeq_le. ring.
  - apply (Qle_trans _ (Z.of_nat (2 * Z.to_nat (Qnum b)) # 1) _).
    + apply qeq_le.
      replace (2 * Z.to_nat (Qnum b))%nat
        with (Z.to_nat (Qnum b) + Z.to_nat (Qnum b))%nat by lia.
      unfold Qeq. simpl. lia.
    + apply (Qle_of_nat (2 * Z.to_nat (Qnum b)) (2 * Z.to_nat (Qnum b) + 1)). lia.
Qed.

(* single ratio step: k >= K and 2b <= K+1 implies term_{k+1} <= term_k * (1/2) *)
Lemma qtail_ratio_step : forall (b : Q) (K k : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) -> (K <= k)%nat ->
  Qle (q_pow b (Datatypes.S k) / q_fact (Datatypes.S k))
      ((q_pow b k / q_fact k) * (1 / 2)%Q).
Proof.
  intros b K k Hb H2b Hk.
  assert (Hc0 : ~ ((Z.of_nat (Datatypes.S k) # 1) == 0)).
  { apply qtail_neq0. apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia. }
  assert (Hf0 : ~ (q_fact k == 0)) by (apply qtail_neq0; apply q_fact_pos).
  assert (Hbc0 : Qle 0 (b / (Z.of_nat (Datatypes.S k) # 1))).
  { apply (q_le_div_le 0 1 b (Z.of_nat (Datatypes.S k) # 1)).
    - apply qtail_Qlt01.
    - apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia.
    - apply (Qle_trans (0 * (Z.of_nat (Datatypes.S k) # 1)) 0 (b * 1)).
      + apply qeq_le. ring.
      + apply (Qle_trans 0 b (b * 1)).
        * exact Hb.
        * apply qeq_le. ring. }
  apply (Qle_trans _ ((q_pow b k / q_fact k) * (b / (Z.of_nat (Datatypes.S k) # 1))) _).
  - apply qeq_le.
    rewrite (q_pow_succ b k), (q_fact_succ k).
    rewrite (Qmult_comm (q_pow b k / q_fact k) (b / (Z.of_nat (Datatypes.S k) # 1))).
    apply (qtail_div_split b (Z.of_nat (Datatypes.S k) # 1) (q_pow b k) (q_fact k)).
    + exact Hc0.
    + exact Hf0.
  - apply (qtail_mult_le_compat_l (b / (Z.of_nat (Datatypes.S k) # 1))
             (1 / 2)%Q (q_pow b k / q_fact k)).
    + apply (q_le_div_le b (Z.of_nat (Datatypes.S k) # 1) 1 2%Q).
      * apply (Qlt_of_nat_lt 0 (Datatypes.S k)). lia.
      * apply Q2_pos.
      * apply (Qle_trans _ ((1 + 1)%Q * b) _).
        -- apply qeq_le. ring.
        -- apply (Qle_trans _ (Z.of_nat (Datatypes.S K) # 1) _).
           ++ exact H2b.
           ++ apply (Qle_of_nat (Datatypes.S K) (Datatypes.S k)). lia.
    + apply q_pow_fact_nonneg. exact Hb.
Qed.

(* chained: k >= K implies term_k <= term_K * (1/2)^(k-K) *)
Lemma qtail_ratio_chain : forall (b : Q) (K k : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) -> (K <= k)%nat ->
  Qle (q_pow b k / q_fact k) ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K)).
Proof.
  intros b K k Hb H2b. revert k.
  induction k as [| k IH]; intro Hk.
  - assert (HK : K = 0%nat) by lia. subst K.
    apply qeq_le. simpl. ring.
  - destruct (Nat.eq_dec (Datatypes.S k) K) as [He | Hne].
    + rewrite He.
      replace (K - K)%nat with 0%nat by lia.
      apply qeq_le. simpl. ring.
    + assert (Hk' : (K <= k)%nat) by lia.
      replace (Datatypes.S k - K)%nat with (Datatypes.S (k - K))%nat by lia.
      apply (Qle_trans _ ((q_pow b k / q_fact k) * (1 / 2)%Q) _).
      * apply (qtail_ratio_step b K k).
        -- exact Hb.
        -- exact H2b.
        -- lia.
      * apply (Qle_trans _
                 ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K) * (1 / 2)%Q)).
        -- apply (Qmult_le_compat_r (q_pow b k / q_fact k)
                     ((q_pow b K / q_fact K) * q_pow (1 / 2) (k - K)) (1 / 2)%Q).
           ++ apply IH. exact Hk'.
           ++ apply Qhalf_nonneg.
        -- apply qeq_le.
           rewrite (q_pow_succ (1 / 2) (k - K)).
           ring.
Qed.

(* geometric sum: sum_{k=K+t}^{M-1} term_k <= term_K * (1/2)^t * geo_sum(M-(K+t)) *)
Lemma qtail_sum_geo : forall (b : Q) (K t M : nat),
  Qle 0 b -> Qle ((1 + 1)%Q * b) (Z.of_nat (Datatypes.S K) # 1) ->
  ((K + t) <= M)%nat ->
  Qle (qtail_sum b (K + t) M)
      ((q_pow b K / q_fact K) * q_pow (1 / 2) t * geo_sum (M - (K + t))).
Proof.
  intros b K t M Hb H2b. revert t.
  induction M as [| M IH]; intros t Ht.
  - assert (HK : K = 0%nat) by lia.
    assert (Ht0 : t = 0%nat) by lia.
    rewrite HK, Ht0.
    apply qeq_le. simpl. ring.
  - destruct (Nat.leb (K + t) M) eqn:E.
    + apply Nat.leb_le in E.
      assert (HM : (K + t <= M)%nat) by lia.
      specialize (IH t HM).
      change (qtail_sum b (K + t) (Datatypes.S M))
        with ((if Nat.leb (K + t) M then q_pow b M / q_fact M else 0)
              + qtail_sum b (K + t) M).
      assert (HL : Nat.leb (K + t) M = true) by (apply Nat.leb_le; exact E).
      replace (if Nat.leb (K + t) M then q_pow b M / q_fact M else 0)
        with (q_pow b M / q_fact M) by (rewrite HL; reflexivity).
      replace (Datatypes.S M - (K + t))%nat with (Datatypes.S (M - (K + t)))%nat by lia.
      change (geo_sum (Datatypes.S (M - (K + t))))
        with (geo_sum (M - (K + t)) + q_pow (1 / 2) (M - (K + t))).
      assert (Hterm : Qle (q_pow b M / q_fact M)
                        ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                           * q_pow (1 / 2) (M - (K + t)))).
      { apply (Qle_trans _ ((q_pow b K / q_fact K) * q_pow (1 / 2) (M - K)) _).
        - apply qtail_ratio_chain.
          + exact Hb.
          + exact H2b.
          + lia.
        - apply qeq_le.
          replace (M - K)%nat with (t + (M - (K + t)))%nat by lia.
          rewrite (q_pow_add (1 / 2) t (M - (K + t))).
          ring. }
      apply (Qle_trans _
        (((q_pow b K / q_fact K) * q_pow (1 / 2) t * q_pow (1 / 2) (M - (K + t)))
          + (q_pow b K / q_fact K) * q_pow (1 / 2) t * geo_sum (M - (K + t))) _).
      * apply (Qplus_le_compat (q_pow b M / q_fact M)
                  ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                     * q_pow (1 / 2) (M - (K + t)))
                  (qtail_sum b (K + t) M)
                  ((q_pow b K / q_fact K) * q_pow (1 / 2) t
                     * geo_sum (M - (K + t)))).
        -- exact Hterm.
        -- exact IH.
      * apply qeq_le. ring.
    + apply Nat.leb_gt in E.
      apply (Qle_trans _ 0 _).
      * apply qeq_le. apply qtail_sum_le_m. lia.
      * apply Qmult_le_0_compat.
        -- apply Qmult_le_0_compat.
           ++ apply q_pow_fact_nonneg. exact Hb.
           ++ apply q_pow_nonneg. apply Qhalf_nonneg.
        -- apply qtail_geo_nonneg.
Qed.

(* ===== main lemma: constructive Cauchy modulus (Prop kernel; N = max(4, 2*nat(floor b)) + t0, fully explicit) ===== *)
Lemma qtail_cauchy_modulus_aux : forall b e : Q, Qle 0 b -> Qlt 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    Qlt (qtail_sum b (Nat.min m n) (Nat.max m n)) e).
Proof.
  intros b e Hb He.
  assert (Hne : ~ (e == 0)) by (apply qtail_neq0; exact He).
  (* K = max(4, 2*nat(floor b)): explicit; the ratio halves from K on *)
  assert (H2b : Qle ((1 + 1)%Q * b)
                     (Z.of_nat (Datatypes.S (Nat.max 4 (2 * Z.to_nat (Qnum b)))) # 1)).
  { apply (Qle_trans _ (Z.of_nat (2 * Z.to_nat (Qnum b) + 1) # 1) _).
    - apply qtail_two_b_le. exact Hb.
    - apply (Qle_of_nat (2 * Z.to_nat (Qnum b) + 1)
                        (Datatypes.S (Nat.max 4 (2 * Z.to_nat (Qnum b))))). lia. }
  set (K := Nat.max 4 (2 * Z.to_nat (Qnum b))) in *.
  set (C := q_pow b K / q_fact K).
  assert (HC : Qle 0 C) by (unfold C; apply q_pow_fact_nonneg; exact Hb).
  destruct (Qeq_dec C 0) as [Hz | Hnz].
  - (* C = 0: all terms from index K on vanish *)
    remember (Z.to_nat (Qnum ((C * (1 + 1)) / e))) as t0 eqn:Et0.
    exists (K + t0)%nat.
    intros m n Hm Hn.
    assert (Hsum : Qle (qtail_sum b (Nat.min m n) (Nat.max m n))
                        (C * q_pow (1 / 2) t0 * (1 + 1)%Q)).
    { assert (HAnn : Qle 0 (qtail_sum b (K + t0) (Nat.min m n)))
        by (apply qtail_sum_nonneg_aux; exact Hb).
      apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.min m n)
                            + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
      - apply (Qle_trans _ (0 + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
        + apply qeq_le. ring.
        + apply (Qplus_le_compat 0 (qtail_sum b (K + t0) (Nat.min m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))).
          * exact HAnn.
          * apply Qle_refl.
      - apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.max m n)) _).
        + apply qeq_le. apply Qeq_sym.
          apply (qtail_sum_add b (K + t0) (Nat.min m n) (Nat.max m n)); lia.
        + apply (Qle_trans _
                   (C * q_pow (1 / 2) t0 * geo_sum (Nat.max m n - (K + t0))) _).
          * apply (qtail_sum_geo b K t0 (Nat.max m n) Hb H2b). lia.
          * apply (qtail_mult_le_compat_l (geo_sum (Nat.max m n - (K + t0)))
                     (1 + 1)%Q (C * q_pow (1 / 2) t0)).
            -- apply geo_sum_le_two.
            -- apply Qmult_le_0_compat.
               ++ exact HC.
               ++ apply q_pow_nonneg. apply Qhalf_nonneg. }
    apply (Qle_lt_trans _ (C * q_pow (1 / 2) t0 * (1 + 1)%Q) _).
    + exact Hsum.
    + apply (Qle_lt_trans _ 0 _).
      * apply qeq_le. rewrite Hz. ring.
      * exact He.
  - (* C > 0: geometric remainder + explicit 2^t >= t+1 *)
    assert (HC2 : Qle 0 (C * (1 + 1)%Q))
      by (apply Qmult_le_0_compat; [ exact HC | apply Q2_nonneg ]).
    assert (HC2pos : Qlt 0 (C * (1 + 1)%Q)).
    { apply Qmult_lt_0_compat.
      - destruct (Qle_lt_or_eq 0 C HC) as [H | H].
        + exact H.
        + exfalso. exact (Hnz (Qeq_sym _ _ H)).
      - apply Q2_pos. }
    assert (HC2ne : ~ ((C * (1 + 1)%Q) == 0)) by (apply qtail_neq0; exact HC2pos).
    set (w := (C * (1 + 1)%Q) / e).
    assert (Hw0 : Qle 0 w).
    { unfold w. apply (q_le_div_le 0 1 (C * (1 + 1)%Q) e).
      - apply qtail_Qlt01.
      - exact He.
      - apply (Qle_trans (0 * e) 0 ((C * (1 + 1)%Q) * 1)).
        + apply qeq_le. ring.
        + apply (Qle_trans 0 (C * (1 + 1)%Q) ((C * (1 + 1)%Q) * 1)).
          * exact HC2.
          * apply qeq_le. ring. }
    assert (Hwpos : Qlt 0 w) by (unfold w; apply qtail_div_pos; assumption).
    assert (Hwne : ~ (((C * (1 + 1)%Q) / e) == 0)).
    { apply qtail_neq0. unfold w. exact Hwpos. }
    assert (Hwlt : Qlt w (Z.of_nat (Datatypes.S (Z.to_nat (Qnum w))) # 1)).
    { assert (Hup : Qle w (Z.of_nat (Z.to_nat (Qnum w)) # 1))
        by (apply qtail_pos_upper; exact Hw0).
      apply (Qle_lt_trans w (Z.of_nat (Z.to_nat (Qnum w)) # 1)
                           (Z.of_nat (Datatypes.S (Z.to_nat (Qnum w))) # 1)).
      - exact Hup.
      - apply (Qlt_of_nat_lt (Z.to_nat (Qnum w))
                             (Datatypes.S (Z.to_nat (Qnum w)))). lia. }
    remember (Z.to_nat (Qnum w)) as t0 eqn:Et0.
    exists (K + t0)%nat.
    intros m n Hm Hn.
    assert (Hsum : Qle (qtail_sum b (Nat.min m n) (Nat.max m n))
                        (C * q_pow (1 / 2) t0 * (1 + 1)%Q)).
    { assert (HAnn : Qle 0 (qtail_sum b (K + t0) (Nat.min m n)))
        by (apply qtail_sum_nonneg_aux; exact Hb).
      apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.min m n)
                            + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
      - apply (Qle_trans _ (0 + qtail_sum b (Nat.min m n) (Nat.max m n)) _).
        + apply qeq_le. ring.
        + apply (Qplus_le_compat 0 (qtail_sum b (K + t0) (Nat.min m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))
                      (qtail_sum b (Nat.min m n) (Nat.max m n))).
          * exact HAnn.
          * apply Qle_refl.
      - apply (Qle_trans _ (qtail_sum b (K + t0) (Nat.max m n)) _).
        + apply qeq_le. apply Qeq_sym.
          apply (qtail_sum_add b (K + t0) (Nat.min m n) (Nat.max m n)); lia.
        + apply (Qle_trans _
                   (C * q_pow (1 / 2) t0 * geo_sum (Nat.max m n - (K + t0))) _).
          * apply (qtail_sum_geo b K t0 (Nat.max m n) Hb H2b). lia.
          * apply (qtail_mult_le_compat_l (geo_sum (Nat.max m n - (K + t0)))
                     (1 + 1)%Q (C * q_pow (1 / 2) t0)).
            -- apply geo_sum_le_two.
            -- apply Qmult_le_0_compat.
               ++ exact HC.
               ++ apply q_pow_nonneg. apply Qhalf_nonneg. }
    assert (Hst0 : ~ ((Z.of_nat (Datatypes.S t0) # 1) == 0)).
    { apply qtail_neq0. apply (Qlt_of_nat_lt 0 (Datatypes.S t0)). lia. }
    assert (Hinv : Qle ((C * (1 + 1)%Q) * q_pow (1 / 2) t0)
                        ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1)))).
    { apply (qtail_mult_le_compat_l (q_pow (1 / 2) t0)
                               (1 / (Z.of_nat (Datatypes.S t0) # 1))
                               (C * (1 + 1)%Q)).
      - apply qtail_half_pow_le_invT.
      - exact HC2. }
    assert (Hwdef : ((C * (1 + 1)%Q) / w) == e).
    { unfold w. field. repeat split; assumption. }
    assert (Hst0pos : Qlt 0 (Z.of_nat (Datatypes.S t0) # 1)).
    { apply (Qlt_of_nat_lt 0 (Datatypes.S t0)). lia. }
    assert (Hstrict : Qlt ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1))) e).
    { assert (Hdv : Qlt ((C * (1 + 1)%Q) / (Z.of_nat (Datatypes.S t0) # 1))
                        ((C * (1 + 1)%Q) / w)).
      { apply (qtail_div_lt (C * (1 + 1)%Q) (Z.of_nat (Datatypes.S t0) # 1)
                            (C * (1 + 1)%Q) w).
        - exact Hst0pos.
        - exact Hwpos.
        - apply (qtail_mult_lt_compat_l (C * (1 + 1)%Q) w
                    (Z.of_nat (Datatypes.S t0) # 1)).
          + exact HC2pos.
          + exact Hwlt. }
      apply (Qle_lt_trans _ ((C * (1 + 1)%Q) / (Z.of_nat (Datatypes.S t0) # 1)) e).
      - apply qeq_le. field. repeat split; assumption.
      - apply (Qlt_le_trans _ ((C * (1 + 1)%Q) / w) e).
        + exact Hdv.
        + apply qeq_le. unfold w. exact Hwdef. }
    apply (Qle_lt_trans _ ((C * q_pow (1 / 2) t0) * (1 + 1)%Q) _).
    + exact Hsum.
    + apply (Qle_lt_trans _
               ((C * (1 + 1)%Q) * (1 / (Z.of_nat (Datatypes.S t0) # 1))) _).
      * apply (Qle_trans _ ((C * (1 + 1)%Q) * q_pow (1 / 2) t0)).
        -- apply qeq_le. ring.
        -- exact Hinv.
      * exact Hstrict.
Qed.

(* S3 main exit (Set-carried, QltT/sigT; symmetric min/max order form) *)
Lemma qtail_cauchy_modulus : forall b e : Q,
  QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
    QltT (qtail_sum b (Nat.min m n) (Nat.max m n)) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus_aux b e (qtail_QleT_to_Qle 0 b Hb)
              (QltT_to_Qlt 0 e He)) as [N HN].
  exists N. intros m n Hm Hn.
  apply Qlt_to_QltT. apply HN; assumption.
Qed.

(* S3 ordered form (n <= m, both ends >= N) - direct-use form for the path B Cauchy criterion *)
Lemma qtail_cauchy_modulus_ord : forall b e : Q,
  QleT 0 b -> QltT 0 e ->
  sigT (fun N : nat => forall m n : nat, (N <= n)%nat -> (n <= m)%nat ->
    QltT (qtail_sum b n m) e).
Proof.
  intros b e Hb He.
  destruct (qtail_cauchy_modulus b e Hb He) as [N HN].
  exists N. intros m n Hn Hnm.
  assert (HB : QltT (qtail_sum b (Nat.min n m) (Nat.max n m)) e)
    by (apply (HN n m); lia).
  replace (Nat.min n m) with n in HB by lia.
  replace (Nat.max n m) with m in HB by lia.
  exact HB.
Qed.

(* ================= S4: interface notes toward the S03 exp series files =================
   1) Path B (Banach exp series Cauchy property): differences of exp_partial m x reduce
      via exp_partial_diff_tail to the tail sum; for |x| <= b use
      qtail_cauchy_modulus_ord directly (N(b,e) explicit and computable, replacing the
      S03 q_arch_geom + arch_decay double Qarchimedean witness chain).
   2) Path C (Pade error bound): the Pade truncated remainder sum of b^k/k! is
      growth-controlled by qtail_sum_mono, sign-kept by qtail_sum_nonneg,
      with explicit tail bound N from qtail_cauchy_modulus.
   3) Relation to the S03 files: qtail_sum b m n == exp_tail (pred m) (pred n) b
      (m, n >= 1; identity not proven, note only); qtail_fact_ge_pow and
      qtail_term_decay can supply the explicit 2^k <= k! lower bound for the
      S03 pow_fact series. *)
