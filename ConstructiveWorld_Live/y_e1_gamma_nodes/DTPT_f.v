(* ConstructiveWorld-Main - the D8 factorial-series stem of the DTPT base library *)

(** * DTPT_f: the D8 factorial-series stem of the DTPT base library (stem F of fourteen).

    Mission.  merged block M1, the D8 factorial-series family: the Z.pos positivity witness, the recurrence equation, the monotone chain, the reciprocal antitone, the series upper bound (partial sums of 1/k! below 3 via the exponential invariant), the constructive convergence rate, and the 2^k lower-bound family.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [List], [Arith], [Lia], [Permutation], [Sorting.Sorted]; [DTPT_a], [DTPT_b], [DTPT_c], [DTPT_d], [DTPT_e]

    References.  the DTPT base library of the constructive development (the judged-code truth-predicate line); statements conserved verbatim from the boxed original piece; consumed by the later stems of this node.

    Constructivity.  All carriers [Set]; conclusions in Set-valued order
    predicates and equality forms; zero assumed constants; zero admissions;
    every proof closes by Qed.

    Build.  [coqc -q -native-compiler no] under the acceptance build
    faces, [cpu_guard v3] wrapped. *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import List.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import Sorting.Sorted.
Import ListNotations.
Open Scope Q_scope.
Require Import DTPT_a.
Require Import DTPT_b.
Require Import DTPT_c.
Require Import DTPT_d.
Require Import DTPT_e.
(* ============================================================
   merged block M1 (section 10): the merge of DTPT_D8Ext.v - the D8 factorial-series family
   source piece DTPT-U7 (the theoremization of the D8 factorial family). Only the standalone-file
   Require/Import/Open Scope headers (carried uniformly by this file's header)
   were removed; comments and all proof bodies, the Qed face zero-change.
   ============================================================ *)
(* ============================================================
   DTPT_D8Ext.v - hotspot upgrade unit D8X (the theoremization of the D8 factorial family)
   source piece: DTPT-U7 | base module: Require Import DTPT
   (the DTPT.vo stable baseline; the existing thirteen .v pieces zero-change, the six D8 pieces not re-proven)

   delivery tiers (D8X upgrade targets 1-4):
   [floor piece 1 - the recurrence equation]
     q_fact_recurrence : q_fact (S n) == q_fact n * (Z.of_nat (S n) # 1)
   [floor piece 2 - the monotone family]
     nat_fact_mono / nat_fact_le (the factorial monotonicity chain)
     q_fact_recip_anti : (k <= k')%nat -> (1/q_fact k' <= 1/q_fact k)%Q
     D8_mono (the checklist-suggested corollary: 1/q_fact (S K) <= 1/q_fact K)
   [main piece 3 - the series upper bound]
     sum_fact_recip_lt3 : (sum_fact_recip n < 3)%Q
     route: the exponential invariant sum_fact_recip n + 1/n! <= 3 (two-base induction over 0/1)
     (the core step (the shifted form) 2/(n+2)! <= 1/(n+1)!: n+2 >= 2 holds unconditionally;
       the unshifted form 2/(n+1)! <= 1/n! fails at n=0 (2 > 1), recorded honestly.
       the final strictness comes from 0 < 1/n!: S_n < S_n + 1/n! <= 3.
       the same theorem as the geometric-series route, shorter, and free of the Q-power geometric partial sums;
       the 2^k lower-bound family of the geometric route is still delivered as bonus section 6.)
   [bonus piece 4 - the constructive convergence rate]
     q_fact_rate / q_fact_rate_exists (starting at K0 = 4: k >= 4 implies 1/k! * 4 < 1)
   [bonus piece 5 - the 2^k lower-bound family]
     nat_fact_pow2_lb : 2^k <= nat_fact (S k) (i.e. (k+1)! >= 2^k)
     q_fact_inv_le_pow2 : 1/(k+1)! <= 1/2^k

   discipline: zero assumed constants, zero admissions, zero aborts, zero classical excluded middle, completed by Qed throughout.
   Q-level lia disabled: all inequalities go through Qnum/Qden expansion + Z-level lia/ring;
   the '#' denominator slot is positive (a verified pitfall); Z denominators always go through q_inv_den1.
   ============================================================ *)
(* the standalone-file Require/Import/Open Scope headers (From Stdlib QArith/List/Arith/Lia,
   Require Import DTPT, Open Scope Q_scope) were removed at merge time. *)

(* ========== section 0: the positivity witness - Z.of_nat (nat_fact n) is always Z.pos ========== *)

Lemma nat_fact_pos_Z : forall n : nat,
  exists p : positive, Z.of_nat (nat_fact n) = Z.pos p.
Proof.
  intro n. pose proof (nat_fact_ge1 n) as H.
  apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact n))) in H.
  destruct (Z.of_nat (nat_fact n)) as [| p | p] eqn:E.
  - exfalso. lia.
  - exists p. reflexivity.
  - exfalso. lia.
Qed.

(* the Q inverse of the denominator-1 form (the DTPT.v D8 style: unfold Qdiv, Qinv collects it directly) *)
Lemma q_inv_den1 : forall p : positive, 1 / (Z.pos p # 1) == (1 # p)%Q.
Proof. intro p. unfold Qdiv, Qinv; reflexivity. Qed.

Lemma q_fact_ne0 : forall n : nat, ~ (q_fact n == 0)%Q.
Proof.
  intro n. destruct (nat_fact_pos_Z n) as [p Ep].
  unfold q_fact. rewrite Ep. intro Hc.
  unfold Qeq in Hc. simpl in Hc. lia.
Qed.

(* ========== section 1, floor piece: the recurrence equation ========== *)

Theorem q_fact_recurrence : forall n : nat,
  q_fact (S n) == q_fact n * (Z.of_nat (S n) # 1)%Q.
Proof.
  intro n. unfold q_fact.
  change (nat_fact (S n)) with (S n * nat_fact n)%nat.
  rewrite Znat.Nat2Z.inj_mul.
  rewrite Qmult_comm. apply Qeq_refl.
Qed.

(* ========== section 2, floor piece: the monotone family ========== *)

Lemma nat_fact_mono : forall n m : nat,
  (n <= m)%nat -> (nat_fact n <= nat_fact m)%nat.
Proof.
  intros n m Hle. induction Hle as [| m Hle IH].
  - apply Nat.le_refl.
  - apply (Nat.le_trans _ (nat_fact m) _).
    + exact IH.
    + change (nat_fact (S m)) with (S m * nat_fact m)%nat.
      assert (H2 : (1 * nat_fact m <= S m * nat_fact m)%nat)
        by (apply Nat.mul_le_mono_r; lia).
      rewrite Nat.mul_1_l in H2. exact H2.
Qed.

Lemma nat_fact_le : forall n : nat, (nat_fact n <= nat_fact (S n))%nat.
Proof. intro n. apply nat_fact_mono. apply Nat.le_succ_diag_r. Qed.

Lemma nat_fact_le_Z : forall n m : nat,
  (n <= m)%nat -> (Z.of_nat (nat_fact n) <= Z.of_nat (nat_fact m))%Z.
Proof.
  intros n m Hle.
  apply (proj1 (Znat.Nat2Z.inj_le (nat_fact n) (nat_fact m))).
  apply nat_fact_mono. exact Hle.
Qed.

(* ========== section 3, floor piece: the reciprocal antitone (the Q division order bridge + the positivity guard) ========== *)

Theorem q_fact_recip_anti : forall k k' : nat,
  (k <= k')%nat -> (1 / q_fact k' <= 1 / q_fact k)%Q.
Proof.
  intros k k' Hle.
  pose proof (nat_fact_le_Z k k' Hle) as Hz.
  destruct (nat_fact_pos_Z k) as [pk Ek].
  destruct (nat_fact_pos_Z k') as [pk' Ek'].
  rewrite Ek, Ek' in Hz.
  unfold q_fact. rewrite Ek, Ek'.
  rewrite (q_inv_den1 pk'), (q_inv_den1 pk).
  unfold Qle. simpl. lia.
Qed.

(* the checklist-suggested form D8_mono: the successor reciprocal is non-increasing *)
Corollary D8_mono : forall K : nat,
  (0 < K)%nat -> (1 / q_fact (S K) <= 1 / q_fact K)%Q.
Proof.
  intros K HK. apply q_fact_recip_anti. apply Nat.le_succ_diag_r.
Qed.

(* ============ section 4, main piece: the partial sum of 1/k! over k = 0..n is < 3 ============ *)

Fixpoint sum_fact_recip (n : nat) : Q :=
  match n with
  | O => 1 / q_fact 0
  | S m => sum_fact_recip m + 1 / q_fact (S m)
  end.

(* the core step (the shifted form, true from the very start of n): 2/(n+2)! <= 1/(n+1)!.
   note that the unshifted form 2/(n+1)! <= 1/n! fails at n=0 (2 > 1),
   hence the invariant goes through a two-base induction (end of section 4). *)
Lemma q_recip_step_Z : forall a b : Z,
  (0 < b)%Z -> (2 * b <= a)%Z -> (2 / (a # 1) <= 1 / (b # 1))%Q.
Proof.
  intros a b Hb Hab.
  destruct a as [| pa | pa]; try lia.
  destruct b as [| pb | pb]; try lia.
  assert (H2 : 2 / (Z.pos pa # 1) == 2 # pa).
  { unfold Qdiv, Qinv; reflexivity. }
  assert (H1 : 1 / (Z.pos pb # 1) == 1 # pb).
  { unfold Qdiv, Qinv; reflexivity. }
  rewrite H2, H1. unfold Qle. cbn [Qnum Qden]. lia.
Qed.

Lemma q_fact_step2_le : forall n : nat,
  (2 / q_fact (S (S n)) <= 1 / q_fact (S n))%Q.
Proof.
  intro n.
  pose proof (nat_fact_ge1 (S n)) as Hg.
  apply (proj1 (Znat.Nat2Z.inj_le 1 (nat_fact (S n)))) in Hg.
  unfold q_fact. change (nat_fact (S (S n))) with (S (S n) * nat_fact (S n))%nat.
  rewrite Znat.Nat2Z.inj_mul.
  apply q_recip_step_Z.
  - lia.
  - apply Z.mul_le_mono_nonneg_r.
    + lia.
    + apply (proj1 (Znat.Nat2Z.inj_le 2 (S (S n)))). lia.
Qed.

(* the exponential invariant: S_n + 1/n! <= 3 (self-sustaining by induction; two bases: 0 and 1) *)
Lemma sum_fact_recip_inv : forall n : nat,
  (sum_fact_recip n + 1 / q_fact n <= 3)%Q.
Proof.
  intro n.
  assert (Hboth : (sum_fact_recip n + 1 / q_fact n <= 3)%Q /\
                  (sum_fact_recip (S n) + 1 / q_fact (S n) <= 3)%Q).
  { induction n as [| n [IH1 IH2]].
    - split.
      + cbn [sum_fact_recip].
        assert (H0 : (1 / q_fact 0 == 1)%Q) by (unfold q_fact; reflexivity).
        rewrite H0. unfold Qle. simpl. lia.
      + cbn [sum_fact_recip].
        assert (H0 : (1 / q_fact 0 == 1)%Q) by (unfold q_fact; reflexivity).
        assert (H1 : (1 / q_fact 1 == 1)%Q) by (unfold q_fact; reflexivity).
        rewrite H0, H1. unfold Qle. simpl. lia.
    - split.
      + exact IH2.
      + cbn [sum_fact_recip].
        assert (Hassoc : (sum_fact_recip (S n) + 1 / q_fact (S (S n))
                           + 1 / q_fact (S (S n))
                         == sum_fact_recip (S n) + 2 / q_fact (S (S n)))%Q).
        { field. apply q_fact_ne0. }
        rewrite Hassoc.
        apply (Qle_trans _ (sum_fact_recip (S n) + 1 / q_fact (S n))%Q).
        * apply qadd_le; [ apply Qle_refl | apply q_fact_step2_le ].
        * exact IH2. }
  exact (proj1 Hboth).
Qed.

(* positivity: 0 < 1/n! (the source of the final strictness) *)
Lemma q_fact_inv_pos : forall n : nat, (0 < 1 / q_fact n)%Q.
Proof.
  intro n. destruct (nat_fact_pos_Z n) as [p Ep].
  unfold q_fact. rewrite Ep. rewrite (q_inv_den1 p).
  unfold Qlt. simpl. lia.
Qed.

(* main theorem: the partial sum of 1/k! over k = 0..n is < 3
   (S_n < S_n + 1/n! strictly <--- 0 < 1/n!; then <= 3 by the invariant) *)
Theorem sum_fact_recip_lt3 : forall n : nat, (sum_fact_recip n < 3)%Q.
Proof.
  intro n.
  pose proof (q_fact_inv_pos n) as Hpos.
  apply (Qlt_le_trans _ (sum_fact_recip n + 1 / q_fact n)%Q).
  - pose proof (proj2 (Qplus_lt_r 0 (1 / q_fact n) (sum_fact_recip n)) Hpos) as Hlt.
    rewrite Qplus_0_r in Hlt. exact Hlt.
  - apply sum_fact_recip_inv.
Qed.

(* ========== section 5, bonus piece: the constructive convergence rate (explicit K0 = 4) ========== *)

Theorem q_fact_rate : forall k : nat,
  (4 <= k)%nat -> (1 / q_fact k * 4 < 1)%Q.
Proof.
  intros k Hk.
  destruct (nat_fact_pos_Z k) as [p Ep].
  pose proof (nat_fact_le_Z 4%nat k Hk) as HZ.
  rewrite Ep in HZ. simpl in HZ.
  unfold q_fact. rewrite Ep. rewrite (q_inv_den1 p).
  unfold Qmult. simpl. unfold Qlt. simpl. lia.
Qed.

Theorem q_fact_rate_exists : exists K0 : nat,
  forall k : nat, (K0 <= k)%nat -> (1 / q_fact k * 4 < 1)%Q.
Proof. exists 4%nat. apply q_fact_rate. Qed.

(* ========== section 6, bonus piece: the 2^k lower-bound family (the load-bearing piece of the geometric route) ========== *)

Lemma pow2_ge1 : forall k : nat, (1 <= 2 ^ k)%nat.
Proof. induction k as [| k IH]; simpl; lia. Qed.

(* (k+1)! >= 2^k: the S k branch = 2 * 2^k <= 2 * k! <= (k+2) * k!, order preserved twice by multiplication *)
Lemma nat_fact_pow2_lb : forall k : nat, (2 ^ k <= nat_fact (S k))%nat.
Proof.
  induction k as [| k IH].
  - simpl. lia.
  - change (2 ^ S k)%nat with (2 * 2 ^ k)%nat.
    change (nat_fact (S (S k))) with (S (S k) * nat_fact (S k))%nat.
    assert (H1 : (2 * 2 ^ k <= 2 * nat_fact (S k))%nat)
      by (apply Nat.mul_le_mono_l; exact IH).
    assert (H2 : (2 * nat_fact (S k) <= S (S k) * nat_fact (S k))%nat)
      by (apply Nat.mul_le_mono_r; lia).
    lia.
Qed.

Theorem q_fact_inv_le_pow2 : forall k : nat,
  (1 / q_fact (S k) <= 1 / (Z.of_nat (2 ^ k) # 1))%Q.
Proof.
  intro k.
  destruct (nat_fact_pos_Z (S k)) as [p Ep].
  pose proof (proj1 (Znat.Nat2Z.inj_le (2 ^ k)%nat (nat_fact (S k)))
                    (nat_fact_pow2_lb k)) as Hq.
  rewrite Ep in Hq.
  assert (Hp2 : (0 < Z.of_nat (2 ^ k))%Z).
  { pose proof (pow2_ge1 k) as H1.
    apply (proj1 (Znat.Nat2Z.inj_le 1 (2 ^ k))) in H1. lia. }
  destruct (Z.of_nat (2 ^ k)) as [| q | q] eqn:Eq; try lia.
  unfold q_fact. rewrite Ep.
  rewrite (q_inv_den1 p), (q_inv_den1 q).
  unfold Qle. simpl. lia.
Qed.

