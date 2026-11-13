(* ConstructiveWorld-Main - UpReqQExpTail_a.v - Q exponent tail engine part A: statement surface preserved verbatim from UpReqQExpTail.v (seat1 bound surgery split). *)
(* ==========================================================================
   Mission. Split A of UpReqQExpTail (bound surgery, seat1): the nat engine (2^t >= t+1, 2^k <= k! for k >= 4) and the Q-side small engine (positivity, division, order
     monotonicity lemmas) consumed by splits B and C.
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

(* ================= S2-nat engine ================= *)

Lemma qtail_two_pow_ge : forall t : nat, (Datatypes.S t <= 2 ^ t)%nat.
Proof.
  induction t as [| t IH]; simpl; lia.
Qed.

(* factorial dominates 2^k (nat induction; bootstrap at 4! = 24 >= 16 = 2^4) *)
Lemma qtail_fact_ge_pow : forall k : nat, (4 <= k)%nat -> (2 ^ k <= fact k)%nat.
Proof.
  induction k as [| k IH]; intro Hk.
  - lia.
  - assert (H1 : (2 ^ Datatypes.S k = 2 * 2 ^ k)%nat) by reflexivity.
    assert (H2 : (fact (Datatypes.S k)
                  = Datatypes.S k * fact k)%nat) by reflexivity.
    rewrite H1, H2.
    destruct (Nat.eq_dec k 3%nat) as [Hk3 | Hkne].
    + subst k. simpl. lia.
    + assert (Hk4 : (4 <= k)%nat) by lia.
      specialize (IH Hk4).
      apply Nat.mul_le_mono.
      * lia.
      * exact IH.
Qed.

(* ================= Q-side small engine (Prop kernel) ================= *)

Lemma qtail_Qlt01 : Qlt 0 1.
Proof.
  unfold Qlt. cbn [Qnum Qden].
  (* goal is the Z strict order 0 * den(1) < 1 * den(0); reduce via *)
  (* Z.mul_0_l / Z.mul_1_l explicitly; the remaining 0 < 1 is witnessed *)
  (* constructively by the positivity witness Pos2Z.is_pos of 1 *)
  rewrite Z.mul_0_l, Z.mul_1_l.
  exact (Pos2Z.is_pos 1%positive).
Qed.

Lemma qtail_neq0 : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof. intros x H. apply (q_neq_of_lt x). exact H. Qed.

Lemma qtail_neq0_mul : forall v s : Q, ~ (v == 0) -> ~ (s == 0) -> ~ (v * s == 0).
Proof.
  intros v s Hv Hs Hz.
  exact (Hs (Qmult_integral_l v s Hv Hz)).
Qed.

(* product split for division: (u*r)/(v*s) == (u/v)*(r/s) *)
Lemma qtail_div_split : forall u v r s : Q,
  ~ (v == 0) -> ~ (s == 0) -> (u * r) / (v * s) == (u / v) * (r / s).
Proof.
  intros u v r s Hv Hs.
  assert (Hvs : ~ (v * s == 0)) by (apply qtail_neq0_mul; assumption).
  field. repeat split; assumption.
Qed.

Lemma qtail_QleT_to_Qle : forall x y : Q, QleT x y -> Qle x y.
Proof.
  intros x y H. destruct H as [H | H].
  - apply (Qlt_le_weak x y). apply (QltT_to_Qlt x y). exact H.
  - apply qeq_le. destruct H. reflexivity.
Qed.

Lemma qtail_le_plus_r : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy.
  apply (Qle_trans x (x + 0) (x + y)).
  - apply qeq_le. ring.
  - apply (Qplus_le_compat x x 0 y).
    + apply Qle_refl.
    + exact Hy.
Qed.

(* x >= 0 implies x <= (Z.of_nat (Z.to_nat (Qnum x)))#1 (explicit computable upper bound) *)
Lemma qtail_pos_upper : forall x : Q, Qle 0 x -> Qle x (Z.of_nat (Z.to_nat (Qnum x)) # 1).
Proof.
  intros x Hx. destruct x as [n d]. simpl.
  assert (Hn : (0 <= n)%Z).
  { unfold Qle in Hx. simpl in Hx. lia. }
  replace (Z.of_nat (Z.to_nat n)) with n by lia.
  unfold Qle.
  apply Z.mul_le_mono_nonneg_l.
  - exact Hn.
  - assert (H1 : (1 <= Z.pos d)%Z) by (induction d as [p IHp | p IHp | ]; simpl; lia).
    exact H1.
Qed.

(* denominator positivity of the explicit Q form of 2^t (reused for field side goals) *)
Lemma qtail_pow2_denom_pos : forall t : nat, Qlt 0 (Z.of_nat (2 ^ t) # 1).
Proof.
  intro t.
  assert (Hp : (0 < 2 ^ t)%nat)
    by (apply (proj1 (Nat.neq_0_lt_0 (2 ^ t))); apply Nat.pow_nonzero; lia).
  unfold Qlt. simpl. lia.
Qed.

(* (1/2)^t <= 1/(t+1): explicit from 2^t >= t+1 *)
Lemma qtail_half_pow_le_invT : forall t : nat,
  Qle (q_pow (1 / 2) t) (1 / (Z.of_nat (Datatypes.S t) # 1)).
Proof.
  intro t.
  assert (H2pos : (0 < 2 ^ t)%nat).
  { apply (proj1 (Nat.neq_0_lt_0 (2 ^ t))).
    apply Nat.pow_nonzero. lia. }
  assert (E : forall t0 : nat, q_pow (1 / 2) t0 == 1 / (Z.of_nat (2 ^ t0) # 1)).
  { intro t0. induction t0 as [| t0 IH].
    - reflexivity.
    - rewrite (q_pow_succ (1 / 2) t0), IH.
      assert (Hz2 : (2 ^ Datatypes.S t0 = 2 * 2 ^ t0)%nat) by reflexivity.
      rewrite Hz2.
      assert (Hb : (0 < Z.of_nat (2 ^ t0))%Z).
      { assert (Hp : (0 < 2 ^ t0)%nat)
          by (apply (proj1 (Nat.neq_0_lt_0 (2 ^ t0))); apply Nat.pow_nonzero; lia).
        lia. }
      assert (HZ : ((Z.of_nat (2 * 2 ^ t0)) # 1
                    == (((Z.of_nat (2 ^ t0)) # 1) + ((Z.of_nat (2 ^ t0)) # 1)))%Q)
        by (unfold Qeq; simpl; lia).
      rewrite HZ.
      field.
      repeat split;
        first [ assumption
              | apply qtail_neq0; unfold Qlt; simpl; lia ]. }
  rewrite (E t).
  apply (q_le_div_le 1 (Z.of_nat (2 ^ t) # 1) 1 (Z.of_nat (Datatypes.S t) # 1)).
  - apply (Qlt_of_nat_lt 0 (2 ^ t)). exact H2pos.
  - apply (Qlt_of_nat_lt 0 (Datatypes.S t)). lia.
  - setoid_replace (1 * (Z.of_nat (Datatypes.S t) # 1))
      with (Z.of_nat (Datatypes.S t) # 1) by ring.
    setoid_replace (1 * (Z.of_nat (2 ^ t) # 1))
      with (Z.of_nat (2 ^ t) # 1) by ring.
    apply (Qle_of_nat (Datatypes.S t) (2 ^ t)).
    exact (qtail_two_pow_ge t).
Qed.

(* strict cross multiplication: a*d < c*b implies a/b < c/d (positive denominators) *)
Lemma qtail_div_lt : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qlt (a * d) (c * b) -> Qlt (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hcore.
  assert (Hnb : ~ (b == 0)) by (apply qtail_neq0; exact Hb).
  assert (Hnd : ~ (d == 0)) by (apply qtail_neq0; exact Hd).
  assert (Hle : Qle (a / b) (c / d)).
  { apply (q_le_div_le a b c d).
    - exact Hb.
    - exact Hd.
    - apply (Qlt_le_weak _ _ Hcore). }
  destruct (Qle_lt_or_eq _ _ Hle) as [Hlt | Heq].
  - exact Hlt.
  - exfalso.
    assert (Hs : (a / b) * (b * d) == (c / d) * (b * d)) by (rewrite Heq; reflexivity).
    assert (E1 : (a / b) * (b * d) == a * d) by (field; repeat split; assumption).
    assert (E2 : (c / d) * (b * d) == c * b) by (field; repeat split; assumption).
    rewrite E1 in Hs. rewrite E2 in Hs.
    exact (Qlt_not_eq _ _ Hcore Hs).
Qed.

(* 0 < u, 0 < v ⟹ 0 < u/v *)
Lemma qtail_div_pos : forall u v : Q, Qlt 0 u -> Qlt 0 v -> Qlt 0 (u / v).
Proof.
  intros u v Hu Hv.
  assert (Hcore : Qlt (0 * v) (u * 1)).
  { apply (Qle_lt_trans (0 * v) (0 * 1) (u * 1)).
    - apply qeq_le. ring.
    - apply (Qmult_lt_compat_r 0 u 1).
      + apply qtail_Qlt01.
      + exact Hu. }
  apply (qtail_div_lt 0 1 u v).
  - apply qtail_Qlt01.
  - exact Hv.
  - exact Hcore.
Qed.

(* this platform lacks Qmult_le_compat_l/Qmult_lt_compat_l; rebuilt here via the r variants closed by qeq ring steps *)
Lemma qtail_mult_le_compat_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z H1 H2.
  apply (Qle_trans _ (x * z)).
  - apply qeq_le. ring.
  - apply (Qle_trans _ (y * z)).
    + apply (Qmult_le_compat_r x y z).
      * exact H1.
      * exact H2.
    + apply qeq_le. ring.
Qed.

Lemma qtail_mult_lt_compat_l : forall z x y : Q,
  Qlt 0 z -> Qlt x y -> Qlt (z * x) (z * y).
Proof.
  intros z x y Hz Hxy.
  apply (Qle_lt_trans _ (x * z)).
  - apply qeq_le. ring.
  - apply (Qlt_le_trans (x * z) (y * z) (z * y)).
    + pose proof (Qmult_lt_compat_r x y z Hz Hxy) as Hr.
      exact Hr.
    + apply qeq_le. ring.
Qed.
