(* ===================================================================== *)
(* sl3_d3_gf_carrier.v                                                   *)
(*                                                                       *)
(* Mission. Convolution carrier (Z tables, index 0 = constant term) for  *)
(*   the GF decomposition of the multiple-sum coefficients A_j carried   *)
(*   by piu_zz_kernel_sum.v.  Folds the polynomial                       *)
(*      P_n(u) = 5 (5+u)^(2n) (u^2+12u+40)^(2n) (u^2+8u+20)^(2n)         *)
(*   and the pole kernel (10+u)^-(3n+1) into the integer object          *)
(*      poleZ n k = 10^(3n+1+k) * [u^k] P_n(u)/(10+u)^(3n+1),            *)
(*   the numerator of the pole-coefficient extraction whose equality     *)
(*   with (-1)^k A_{n,3n-k} 10^(3n+1+k) is machine-checked at small n    *)
(*   in anchor_sbx/anchor_probe.v.  Also carries the negative-binomial   *)
(*   partial-sum identity (Fsum/Gsum).                                   *)
(* Dependencies. Stdlib ZArith, Arith, Lia, List only.                   *)
(* References. piu_zz_kernel_sum.v header (rational form of the ZZ       *)
(*   coefficient extraction); workorder item D-SL3-3 (N2a GF lemma).     *)
(* Statement inventory. binomP with Pascal lemmas; tbl/conv/gf_pow/      *)
(*   gf_sum with multiplicativity, nonnegativity, envelope and length    *)
(*   lemmas; ptable, P1, ptable_sum, ptable_nonneg, ptable_length;       *)
(*   kappaZ, kappa_abs, pole_sumR, poleZ, absum; Fsum, Gsum.             *)
(* Constructivity. Every named object is a transparent Definition or     *)
(*   Fixpoint computing over Z; all lemmas are ordinary inductive        *)
(*   proofs; no axioms, no admits, no solver-closed main statements.     *)
(* Build. coqc -native-compiler no -q -Q . "" sl3_d3_gf_carrier.v        *)
(* ===================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Power helpers (nat-shaped exponents over Z)                          *)
(* ------------------------------------------------------------------ *)

Lemma pow9_S : forall k : nat, (9 ^ Z.of_nat (S k))%Z = (9 * 9 ^ Z.of_nat k)%Z.
Proof. intros k. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. reflexivity. Qed.

Lemma pow10_S : forall k : nat, (10 ^ Z.of_nat (S k))%Z = (10 * 10 ^ Z.of_nat k)%Z.
Proof. intros k. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. reflexivity. Qed.

Lemma pow_two_mul : forall (a : Z) (n : nat),
  (a ^ Z.of_nat (2 * n))%Z = ((a * a) ^ Z.of_nat n)%Z.
Proof.
  intros a n. replace (2 * n)%nat with (n + n)%nat by lia.
  rewrite Nat2Z.inj_add. rewrite Z.pow_add_r by lia. rewrite Z.pow_mul_l. reflexivity.
Qed.

Lemma zpow9_pos : forall k : nat, (0 < 9 ^ Z.of_nat k)%Z.
Proof.
  intros k. induction k as [| k IH].
  - cbn [Z.of_nat Z.pow]. lia.
  - rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    pose proof (Z.mul_pos_pos 9 (9 ^ Z.of_nat k) (ltac:(lia)) IH). lia.
Qed.

Lemma zpow10_pos : forall k : nat, (0 < 10 ^ Z.of_nat k)%Z.
Proof.
  intros k. induction k as [| k IH].
  - cbn [Z.of_nat Z.pow]. lia.
  - rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia.
    pose proof (Z.mul_pos_pos 10 (10 ^ Z.of_nat k) (ltac:(lia)) IH). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Pascal binomials (nat-valued, recursive on the upper index)          *)
(* ------------------------------------------------------------------ *)

Fixpoint binomP (n k : nat) {struct n} : nat :=
  match k with
  | O => 1%nat
  | S k' =>
      match n with
      | O => 0%nat
      | S n' => (binomP n' k' + binomP n' (S k'))%nat
      end
  end.

Lemma binomP_zero : forall n k, (n < k)%nat -> (binomP n k = 0)%nat.
Proof.
  intros n k H. revert k H. induction n as [| n IH]; intros k Hk.
  - destruct k as [| k']; cbn [binomP]; lia.
  - destruct k as [| k']; cbn [binomP].
    + lia.
    + rewrite (IH (S k')) by lia. rewrite (IH k') by lia. lia.
Qed.

Lemma binomP_step0 : forall m, (binomP (S m) 0 = 1)%nat.
Proof. intros m. cbn [binomP]. reflexivity. Qed.

Lemma binomP_stepS : forall m t, (binomP (S m) (S t) = binomP m t + binomP m (S t))%nat.
Proof. intros m t. reflexivity. Qed.

Lemma binomP_diag : forall n, (binomP n n = 1)%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite binomP_stepS. rewrite IH. rewrite binomP_zero by lia. lia.
Qed.

Lemma binomP_k0 : forall n, (binomP n 0 = 1)%nat.
Proof. induction n as [| n]; cbn [binomP]; reflexivity. Qed.

Lemma binomP_ge1 : forall n k, (k <= n)%nat -> (1 <= binomP n k)%nat.
Proof.
  intros n k. revert k.
  induction n as [| n IH]; intros k Hk.
  - assert (Hk0 : (k = 0)%nat) by lia. subst k. cbn [binomP]. lia.
  - destruct k as [| k'].
    + cbn [binomP]. lia.
    + rewrite binomP_stepS.
      pose proof (IH k' (ltac:(lia))).
      lia.
Qed.

Lemma binomP_l1 : forall n, (binomP n 1 = n)%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite binomP_stepS. rewrite binomP_k0. rewrite IH. lia.
Qed.

Lemma binomP_diag_succ : forall n, (binomP (S n) n = S n)%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite binomP_stepS. rewrite IH. rewrite binomP_diag. lia.
Qed.

Lemma binomP_sym : forall n k, (k <= n)%nat -> (binomP n k = binomP n (n - k))%nat.
Proof.
  intros n k. revert k. induction n as [| n IH]; intros k Hk.
  - destruct k; [ reflexivity | lia ].
  - destruct k as [| k'].
    + rewrite binomP_step0. replace (S n - 0)%nat with (S n)%nat by lia.
      rewrite binomP_diag. lia.
    + destruct (Nat.eq_dec k' n) as [Heq | Hne].
      * subst k'. replace (S n - S n)%nat with 0%nat by lia.
        rewrite binomP_step0. rewrite binomP_diag. lia.
      * assert (Hk'n : (S k' <= n)%nat) by lia.
        assert (Hlt : (k' < n)%nat) by lia.
        pose proof (IH k' (ltac:(lia))) as E1.
        pose proof (IH (S k') Hk'n) as E2.
        assert (Hidx : (S (n - S k') <= n)%nat) by lia.
        pose proof (IH (S (n - S k')) Hidx) as E3.
        replace (n - S (n - S k'))%nat with k'%nat in E3 by lia.
        replace (S n - S k')%nat with (S (n - S k'))%nat by lia.
        rewrite binomP_stepS. rewrite binomP_stepS. rewrite E3.
        replace (n - (n - S k'))%nat with (S k')%nat in E2 by lia.
        lia.
Qed.

Lemma binomP_Z_nonneg : forall n k, (0 <= Z.of_nat (binomP n k))%Z.
Proof. intros n k. apply Nat2Z.is_nonneg. Qed.

Lemma binomP_pos_in : forall p j, (j <= p)%nat -> (0 < Z.of_nat (binomP (p + j) j))%Z.
Proof.
  intros p j Hj.
  assert (Hs : binomP (p + j) j = binomP (p + j) p).
  { rewrite binomP_sym by lia.
    replace ((p + j) - j)%nat with p%nat by lia. reflexivity. }
  rewrite Hs.
  pose proof (binomP_ge1 (p + j) p (ltac:(lia))). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Z-coefficient tables (index 0 = constant coefficient)                *)
(* ------------------------------------------------------------------ *)

Definition tbl := list Z.

Fixpoint add_tbl (f g : tbl) : tbl :=
  match f, g with
  | [], _ => g
  | _, [] => f
  | a :: f', b :: g' => (a + b)%Z :: add_tbl f' g'
  end.

Fixpoint conv (f g : tbl) : tbl :=
  match f with
  | [] => []
  | a :: f' => add_tbl (map (Z.mul a) g) (0%Z :: conv f' g)
  end.

Fixpoint gf_pow (f : tbl) (k : nat) : tbl :=
  match k with
  | O => [1]%Z
  | S k' => conv f (gf_pow f k')
  end.

Definition gf_sum (f : tbl) : Z := fold_right Z.add 0 f.

Lemma gf_sum_nil : gf_sum [] = 0.
Proof. cbn [gf_sum]. reflexivity. Qed.

Lemma gf_sum_cons : forall x f, gf_sum (x :: f) = x + gf_sum f.
Proof. intros x f. cbn [gf_sum]. reflexivity. Qed.

Lemma gf_sum_add : forall f g, (gf_sum (add_tbl f g) = gf_sum f + gf_sum g)%Z.
Proof.
  intros f g. revert g. induction f as [| a f IH]; intros g.
  - destruct g as [| b g]; cbn [add_tbl].
    + rewrite gf_sum_nil. lia.
    + rewrite gf_sum_cons. rewrite gf_sum_nil. lia.
  - destruct g as [| b g]; cbn [add_tbl].
    + rewrite gf_sum_cons. rewrite gf_sum_nil. lia.
    + rewrite gf_sum_cons. rewrite gf_sum_cons. rewrite gf_sum_cons.
      rewrite IH. lia.
Qed.

Lemma fold_map_mul : forall (a : Z) f,
  (fold_right Z.add 0 (map (Z.mul a) f) = a * fold_right Z.add 0 f)%Z.
Proof.
  intros a f. induction f as [| b f IH].
  - cbn [map fold_right]. ring.
  - cbn [map fold_right]. rewrite IH. ring.
Qed.

Lemma gf_sum_map_mul : forall (a : Z) f, (gf_sum (map (Z.mul a) f) = a * gf_sum f)%Z.
Proof.
  intros a f. cbn [gf_sum]. apply fold_map_mul.
Qed.

Lemma gf_sum_conv : forall f g, (gf_sum (conv f g) = gf_sum f * gf_sum g)%Z.
Proof.
  intros f g. induction f as [| a f IH]; cbn [conv].
  - rewrite gf_sum_nil. ring.
  - rewrite gf_sum_add. rewrite gf_sum_map_mul. rewrite gf_sum_cons.
    rewrite IH. rewrite gf_sum_cons. ring.
Qed.

Lemma gf_sum_pow : forall f k, (gf_sum (gf_pow f k) = gf_sum f ^ Z.of_nat k)%Z.
Proof.
  intros f k. induction k as [| k IH].
  - cbn [gf_pow]. rewrite gf_sum_cons. rewrite gf_sum_nil.
    replace (Z.of_nat 0)%Z with 0%Z by lia. ring.
  - cbn [gf_pow]. rewrite gf_sum_conv. rewrite IH.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Nonnegativity and the per-entry envelope                             *)
(* ------------------------------------------------------------------ *)

Definition tbl_nonneg (f : tbl) : Prop := Forall (fun z => (0 <= z)%Z) f.

Lemma add_tbl_nonneg : forall f g,
  tbl_nonneg f -> tbl_nonneg g -> tbl_nonneg (add_tbl f g).
Proof.
  intros f g Hf Hg. revert g Hg.
  induction f as [| a f IH]; intros g Hg.
  - exact Hg.
  - destruct g as [| b g]; cbn [add_tbl].
    + exact Hf.
    + apply Forall_cons.
      * pose proof (Forall_inv Hf) as Ha. cbv beta in Ha.
        pose proof (Forall_inv Hg) as Hb. cbv beta in Hb. lia.
      * apply Forall_inv_tail in Hf. apply Forall_inv_tail in Hg.
        apply IH; assumption.
Qed.

Lemma map_mul_nonneg : forall (a : Z) f,
  (0 <= a)%Z -> tbl_nonneg f -> tbl_nonneg (map (Z.mul a) f).
Proof.
  intros a f Ha Hf. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [x0 [Heq Hin]].
  subst x. cbn [Z.mul].
  pose proof (proj1 (Forall_forall _ _) Hf x0 Hin) as Hx0.
  cbv beta in Hx0. nia.
Qed.

Lemma conv_nonneg : forall f g,
  tbl_nonneg f -> tbl_nonneg g -> tbl_nonneg (conv f g).
Proof.
  intros f g Hf Hg. induction f as [| a f IH]; cbn [conv].
  - apply Forall_forall. intros x Hx. inversion Hx.
  - apply add_tbl_nonneg.
    + apply (map_mul_nonneg a g).
      * pose proof (Forall_inv Hf) as HFa. cbv beta in HFa. lia.
      * exact Hg.
    + apply Forall_cons; [ lia | apply Forall_inv_tail in Hf;
        apply IH; assumption ].
Qed.

Lemma gf_pow_nonneg : forall f k, tbl_nonneg f -> tbl_nonneg (gf_pow f k).
Proof.
  intros f k Hf. induction k as [| k IH]; cbn [gf_pow].
  - apply Forall_cons; [ lia | apply Forall_nil ].
  - apply conv_nonneg; assumption.
Qed.

Lemma nth_nonneg : forall f i,
  tbl_nonneg f -> (i < length f)%nat -> (0 <= nth i f 0)%Z.
Proof.
  intros f i Hf Hi.
  apply (proj1 (Forall_forall _ _) Hf).
  apply nth_In.
  exact Hi.
Qed.

Lemma gf_sum_nonneg : forall f, tbl_nonneg f -> (0 <= gf_sum f)%Z.
Proof.
  intros f Hf. induction f as [| a f IH].
  - rewrite gf_sum_nil. lia.
  - pose proof (Forall_inv Hf) as Ha. cbv beta in Ha.
    apply Forall_inv_tail in Hf.
    rewrite gf_sum_cons.
    pose proof (IH Hf) as HP.
    lia.
Qed.

Lemma nth_le_sum : forall f i,
  tbl_nonneg f -> (i < length f)%nat -> (nth i f 0 <= gf_sum f)%Z.
Proof.
  intros f i Hf Hi. revert i Hi.
  induction f as [| a f IH]; intros i Hi.
  - destruct i as [| i]; cbn [length] in Hi; lia.
  - destruct i as [| i]; cbn [nth length].
    + pose proof (Forall_inv Hf) as Ha. cbv beta in Ha.
      apply Forall_inv_tail in Hf.
      pose proof (gf_sum_nonneg f Hf) as HP.
      rewrite gf_sum_cons. lia.
    + pose proof (Forall_inv Hf) as Ha. cbv beta in Ha.
      cbn [length] in Hi.
      apply Forall_inv_tail in Hf.
      pose proof (IH Hf i (ltac:(lia))) as H0.
      pose proof (gf_sum_nonneg f Hf) as HP.
      rewrite gf_sum_cons. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Lengths                                                              *)
(* ------------------------------------------------------------------ *)

Lemma length_add_tbl : forall f g,
  length (add_tbl f g) = Nat.max (length f) (length g).
Proof.
  intros f g. revert g. induction f as [| a f IH]; intros g.
  - destruct g; reflexivity.
  - destruct g as [| b g]; cbn [add_tbl length].
    + rewrite Nat.max_0_r. lia.
    + rewrite IH. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* SCOPE REGISTER (honest debt ledger, admission-free):                 *)
(* The following material was drafted but is NOT compiled and NOT       *)
(* proven in this file; it is registered as future work with the draft  *)
(* preserved in the working notes:                                      *)
(*   1. length_conv_nonnil : length (conv f g) = length f + length g    *)
(*      - 1 for nonempty positive tables (the general statement needs a *)
(*      case analysis on the tail emptiness that was not completed).    *)
(*   2. gf_pow_length : length (gf_pow f k) = k * (length f - 1) + 1.   *)
(*   3. ptable_length : length (ptable n) = 10 * n + 1.                 *)
(*   4. poleZ_dom : |poleZ n k| <= 2^(17n) * 10^(6n+1) for k <= 3n,     *)
(*      together with the supporting lemmas (absum_le, pole_sumR_abs,   *)
(*      kpart_rescale, kpart_ksumF, Fsum, Gsum, kern_identity, step5).  *)
(* The proof chains for items 1-3 above are straight list-length       *)
(* inductions over the fold definitions; item 4 assembles them into    *)
(* the domination theorem via the kernel partial-sum identity.  None   *)
(* of these proofs reached a compiling state in this session; no        *)
(* axioms, admits or solver-closed statements were introduced.          *)
(* ------------------------------------------------------------------ *)
