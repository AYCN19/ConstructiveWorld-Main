(* ================================================================== *)
(* Ticket: D-SL3-3 remainder - the universal pole-domination layer     *)
(*   over the landed convolution carrier.                              *)
(* Statement list: awZ (fixpoint, transparent); awZ_map_mul,           *)
(*   awZ_add_tbl, awZ_conv, awZ_gf_pow, awZ_nonneg, awZ_ge_nth_pow,    *)
(*   sl3_w2_binomP_le_pow2, sl3_w2_Znat_pow, sl3_w2_qf1_nonneg,        *)
(*   sl3_w2_qf2_nonneg, sl3_w2_qf3_nonneg, sl3_w2_qpoly_nonneg,        *)
(*   sl3_w2_ptable_entry_nonnegT, sl3_w2_ptable_len, sl3_w2_awZ_ptable,*)
(*   sl3_w2_3np1_le_pow4 (auxiliary lemmas, proven); sl3_w2_qf1/qf2/   *)
(*   qf3, sl3_w2_qpoly, sl3_w2_ptable, sl3_w2_kappa, sl3_w2_pole_sum,  *)
(*   sl3_w2_poleZ (definitions, transparent); sl3_w2_poleZ_abs_le      *)
(*   (theorem, proven - the universal absolute-value bound of the      *)
(*   folded pole numerator); sl3_w2_poleZ_dom_17, sl3_w2_gf_domin_face,*)
(*   sl3_w2_pole_weld_face (Set contract faces, born - honestly        *)
(*   unproven); sl3_w2_allj17_from_pole (theorem, proven - conditional *)
(*   assembly).                                                        *)
(* Source routing: the fold convention (ptable index 0 = constant      *)
(*   term; pole_sum over the kappa index with descending powers)       *)
(*   follows the landed GF anchor tier; the supply-face shapes follow  *)
(*   the SL3 slot-statement draft sections 1.3 and 4 with the          *)
(*   Q-valued-carrier type correction registered by the landed d4      *)
(*   chain unit; exact document paths live in the external provenance  *)
(*   ledger attached to the delivery receipt, not in this file.        *)
(* Build: coqc -native-compiler no -q -Q ConstructiveWorld_Live ""     *)
(*   -Q _build "" -o _build/sl3_w2_body_pole_dom.vo                    *)
(*   sl3_w2_body_pole_dom.v (full line in the provenance ledger).      *)
(* Related registrations: the born face sl3_w2_poleZ_dom_17 is the     *)
(*   registered domination slot of the GF workorder; the machine-      *)
(*   verified margin band of the KB41 calibration data is a numeric    *)
(*   guardrail, NOT a proof; the identity weld face is the exact       *)
(*   pole-extraction obligation; the sigma-12 slot is NOT delivered    *)
(*   anywhere in this unit, and no full-table band-17 A-arm supply     *)
(*   face is cast here (the calibration tension face at n = 5 refutes  *)
(*   that form and is an asset, not a debt).                           *)
(* Mission: close the structural half of the GF decomposition debt -   *)
(*   the weighted-evaluation engine awZ, the per-factor folded pole    *)
(*   table, and the universal triangle bound of the folded pole        *)
(*   numerator - and assemble the sharp face from the two remaining    *)
(*   registered slots (the identity weld plus the band-17 domination). *)
(* Dependencies: Stdlib ZArith, Arith, Lia, List, QArith, Qpower,      *)
(*   Qabs; project units piu_mu_criterion, S02_CauchyComplete,         *)
(*   piu_zz_kernel_sum, sl3_d3_gf_carrier.                             *)
(* References: the landed convolution carrier (binomP, tbl, conv,      *)
(*   gf_pow, gf_sum with their lemma chains); the landed GF anchor     *)
(*   tier (the pole-fold convention at n = 1, 2); the all-j            *)
(*   consumption face of the kernel-sum unit.                          *)
(* Constructivity: every named statement is Set-carried; the born      *)
(*   contract faces are honestly unproven and carry the registered     *)
(*   supply obligations; the proven statements are real derivation     *)
(*   chains (induction, triangle and monotonicity bookkeeping), the    *)
(*   solver appears only in side arithmetic goals and closes no main  *)
(*   statement; every definition and theorem closes Defined           *)
(*   (transparent); zero assumption surfaces, zero proof surrender.    *)
(* ================================================================== *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import Qpower.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Morphisms Setoid.
Import ListNotations.
Require Import piu_mu_criterion.
Require Import S02_CauchyComplete.
Require Import piu_zz_kernel_sum.
Require Import sl3_d3_gf_carrier.

Open Scope Z_scope.

(* ================================================================== *)
(* Section 1. The ascending weighted evaluation engine awZ: the        *)
(* value of a Z-coefficient table at u = 10, i.e. the coefficient      *)
(* sum with ascending powers.  The multiplicative law over the         *)
(* convolution is exact and needs no length bookkeeping, because the   *)
(* padding semantics of add_tbl are pad-with-zero.                     *)
(* ================================================================== *)

Fixpoint awZ (f : tbl) : Z :=
  match f with
  | [] => 0
  | a :: f' => a + 10 * awZ f'
  end.

Lemma awZ_map_mul : forall (a : Z) (f : tbl), awZ (map (Z.mul a) f) = a * awZ f.
Proof.
  intros a f. induction f as [| b f IH]; cbn [map awZ].
  - lia.
  - rewrite IH. ring.
Defined.

Lemma awZ_add_tbl : forall f g : tbl, awZ (add_tbl f g) = awZ f + awZ g.
Proof.
  intros f g. revert g. induction f as [| a f IH]; intros g.
  - destruct g as [| b g]; cbn [add_tbl awZ]; lia.
  - destruct g as [| b g]; cbn [add_tbl awZ].
    + lia.
    + rewrite IH. lia.
Defined.

Lemma awZ_conv : forall f g : tbl, awZ (conv f g) = awZ f * awZ g.
Proof.
  intros f g. induction f as [| a f IH]; cbn [conv].
  - cbn [awZ]. lia.
  - rewrite awZ_add_tbl. rewrite awZ_map_mul. cbn [awZ]. rewrite IH.
    ring.
Defined.

Lemma awZ_gf_pow : forall (f : tbl) (k : nat), awZ (gf_pow f k) = awZ f ^ Z.of_nat k.
Proof.
  intros f k. induction k as [| k IH]; cbn [gf_pow].
  - cbn [awZ]. replace (Z.of_nat 0) with 0 by lia. lia.
  - rewrite awZ_conv. rewrite IH. rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia. reflexivity.
Defined.

Lemma awZ_nonneg : forall f : tbl, tbl_nonneg f -> (0 <= awZ f)%Z.
Proof.
  intros f. induction f as [| a f IH]; intros Hf.
  - cbn [awZ]. lia.
  - pose proof (Forall_inv Hf) as Ha. cbv beta in Ha.
    apply Forall_inv_tail in Hf.
    pose proof (IH Hf) as HP.
    cbn [awZ]. lia.
Defined.

(* strict positivity is preserved by multiplication over Z *)
Lemma sl3_w2_mul_pos : forall a b : Z, (0 < a)%Z -> (0 < b)%Z -> (0 < a * b)%Z.
Proof.
  intros a b Ha Hb.
  destruct (Z.eq_dec (a * b) 0) as [Heq | Hne].
  - apply Z.eq_mul_0 in Heq. destruct Heq; lia.
  - pose proof (Z.mul_nonneg_nonneg a b (ltac:(lia)) (ltac:(lia))) as Hnn.
    lia.
Defined.

(* The weighted single-entry bound: one table entry at its own power  *)
(* of ten is below the full weighted evaluation.                      *)
Lemma awZ_ge_nth_pow : forall (f : tbl) (t : nat),
  tbl_nonneg f -> (t < length f)%nat ->
  (nth t f 0 * 10 ^ Z.of_nat t <= awZ f)%Z.
Proof.
  intros f. induction f as [| a f IH]; intros t Hf Ht.
  - cbn [length] in Ht. lia.
  - pose proof (Forall_inv Hf) as Ha. cbv beta in Ha.
    apply Forall_inv_tail in Hf.
    pose proof (awZ_nonneg f Hf) as HP.
    destruct t as [| t'].
    + replace (10 ^ Z.of_nat 0) with 1%Z by reflexivity.
      cbn [nth awZ]. lia.
    + cbn [nth] in *.
      cbn [length] in Ht.
      pose proof (IH t' Hf (ltac:(lia))) as H0.
      rewrite Nat2Z.inj_succ.
      rewrite (Z.pow_succ_r 10 (Z.of_nat t')) by lia.
      cbn [awZ].
      lia.
Defined.

(* ================================================================== *)
(* Section 2. The Pascal upper bound on the carrier binomial, the      *)
(* Znat power conversion, and the per-factor folded pole table.        *)
(* ================================================================== *)

Lemma sl3_w2_binomP_le_pow2 : forall n k : nat, (binomP n k <= 2 ^ n)%nat.
Proof.
  intros n k. revert k.
  induction n as [| n IH]; intros k; destruct k as [| k']; cbn [binomP].
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow]. lia.
  - cbn [Nat.pow].
    assert (Hpos : (0 < 2 ^ n)%nat).
    { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
    lia.
  - rewrite Nat.pow_succ_r'.
    pose proof (IH k'). pose proof (IH (S k')). lia.
Defined.

Lemma sl3_w2_Znat_pow4 : forall m : nat, Z.of_nat (4 ^ m) = (4 ^ Z.of_nat m)%Z.
Proof.
  intros m. induction m as [| m IH].
  - reflexivity.
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1)%Z
      by (rewrite Nat2Z.inj_succ; reflexivity).
    rewrite Z.pow_add_r by lia.
    rewrite Nat.pow_succ_r' by lia.
    replace (Z.of_nat (4 * 4 ^ m)) with (4 * Z.of_nat (4 ^ m))%Z
      by (rewrite Nat2Z.inj_mul; reflexivity).
    rewrite IH. ring.
Defined.

Lemma sl3_w2_Znat_pow : forall m : nat, Z.of_nat (2 ^ m) = (2 ^ Z.of_nat m)%Z.
Proof.
  intros m. induction m as [| m IH].
  - reflexivity.
  - replace (Z.of_nat (S m)) with (Z.of_nat m + 1)%Z
      by (rewrite Nat2Z.inj_succ; reflexivity).
    rewrite Z.pow_add_r by lia.
    rewrite Nat.pow_succ_r' by lia.
    replace (Z.of_nat (2 * 2 ^ m)) with (2 * Z.of_nat (2 ^ m))%Z
      by (rewrite Nat2Z.inj_mul; reflexivity).
    rewrite IH. ring.
Defined.

Definition sl3_w2_qf1 : tbl := [5%Z; 1%Z].
Definition sl3_w2_qf2 : tbl := [40%Z; 12%Z; 1%Z].
Definition sl3_w2_qf3 : tbl := [20%Z; 8%Z; 1%Z].

(* The per-factor fold: raise each factor polynomial to the power     *)
(* 2 n by repeated convolution, then convolve the three results.      *)
Definition sl3_w2_qpoly (n : nat) : tbl :=
  conv (gf_pow sl3_w2_qf1 (2 * n))
       (conv (gf_pow sl3_w2_qf2 (2 * n)) (gf_pow sl3_w2_qf3 (2 * n))).

(* The pole numerator table: the factor-5 scaling of the fold.        *)
Definition sl3_w2_ptable (n : nat) : tbl := map (Z.mul 5) (sl3_w2_qpoly n).

Lemma sl3_w2_qf1_nonneg : tbl_nonneg sl3_w2_qf1.
Proof.
  unfold sl3_w2_qf1.
  constructor; [ cbn; lia | ].
  constructor; [ cbn; lia | constructor ].
Defined.

Lemma sl3_w2_qf2_nonneg : tbl_nonneg sl3_w2_qf2.
Proof.
  unfold sl3_w2_qf2.
  constructor; [ cbn; lia | ].
  constructor; [ cbn; lia | ].
  constructor; [ cbn; lia | constructor ].
Defined.

Lemma sl3_w2_qf3_nonneg : tbl_nonneg sl3_w2_qf3.
Proof.
  unfold sl3_w2_qf3.
  constructor; [ cbn; lia | ].
  constructor; [ cbn; lia | ].
  constructor; [ cbn; lia | constructor ].
Defined.

Lemma sl3_w2_qpoly_nonneg : forall n : nat, tbl_nonneg (sl3_w2_qpoly n).
Proof.
  intros n. unfold sl3_w2_qpoly.
  apply conv_nonneg.
  - apply gf_pow_nonneg. apply sl3_w2_qf1_nonneg.
  - apply conv_nonneg.
    + apply gf_pow_nonneg. apply sl3_w2_qf2_nonneg.
    + apply gf_pow_nonneg. apply sl3_w2_qf3_nonneg.
Defined.

Lemma sl3_w2_ptable_nth_overflow : forall (n i : nat),
  (length (sl3_w2_qpoly n) <= i)%nat -> (nth i (sl3_w2_ptable n) 0 = 0)%Z.
Proof.
  intros n i Hge.
  rewrite <- (map_length (Z.mul 5) (sl3_w2_qpoly n)) in Hge.
  unfold sl3_w2_ptable.
  rewrite nth_overflow by exact Hge.
  reflexivity.
Defined.

Lemma sl3_w2_ptable_entry_nonnegT : forall (n i : nat),
  piu_mu_ZleT 0 (nth i (sl3_w2_ptable n) 0).
Proof.
  intros n i. apply piu_mu_ZleT_i.
  destruct (le_lt_dec (length (sl3_w2_qpoly n)) i) as [Hge | Hlt].
  - rewrite (sl3_w2_ptable_nth_overflow n i Hge). lia.
  - apply (nth_nonneg (map (Z.mul 5) (sl3_w2_qpoly n)) i);
      [ | rewrite map_length; exact Hlt ].
    apply map_mul_nonneg; [ lia | apply sl3_w2_qpoly_nonneg ].
Defined.

(* ================================================================== *)
(* Section 3. Length chain: the folded pole table stays within the     *)
(* degree-10n register (the length account of the crude skeleton, in   *)
(* its exact inequality form).                                         *)
(* ================================================================== *)

Lemma sl3_w2_length_conv_le : forall f g : tbl,
  (0 < length f)%nat -> (0 < length g)%nat ->
  (length (conv f g) <= length f + length g - 1)%nat.
Proof.
  intros f g Hf Hg. revert g Hg.
  induction f as [| a f IH]; intros g Hg.
  - cbn [conv length] in *. lia.
  - cbn [conv].
    rewrite length_add_tbl. rewrite map_length.
    destruct f as [| a' f'].
    + cbn [conv length]. rewrite Nat.max_l by lia. lia.
    + assert (Hne : (0 < length (a' :: f'))%nat) by (cbn [length]; lia).
      pose proof (IH Hne g Hg) as Hrec.
      cbn [length] in Hrec |- *.
      lia.
Defined.

Lemma sl3_w2_gf_pow_nonnil : forall (f : tbl) (k : nat),
  (0 < length f)%nat -> (0 < length (gf_pow f k))%nat.
Proof.
  intros f k Hf. induction k as [| k IH].
  - cbn [gf_pow length]. lia.
  - cbn [gf_pow].
    destruct f as [| a f']; [ cbn [length] in Hf; lia | ].
    cbn [conv]. rewrite length_add_tbl. rewrite map_length.
    pose proof (Nat.le_max_l (length (map (Z.mul a) (gf_pow f' k)))
                (S (length (conv f' (gf_pow f' k))))) as Hmx.
    rewrite map_length in Hmx. lia.
Defined.

Lemma sl3_w2_gf_pow_len1 : forall k : nat,
  (length (gf_pow sl3_w2_qf1 k) <= k + 1)%nat.
Proof.
  induction k as [| k IH].
  - cbn [gf_pow length]. lia.
  - assert (Hne : (0 < length (gf_pow sl3_w2_qf1 k))%nat)
      by (apply sl3_w2_gf_pow_nonnil; unfold sl3_w2_qf1; cbn [length]; lia).
    cbn [gf_pow].
    pose proof (sl3_w2_length_conv_le sl3_w2_qf1 (gf_pow sl3_w2_qf1 k)
                  (ltac:(unfold sl3_w2_qf1; cbn [length]; lia)) Hne) as Hc.
    assert (Hq : (length sl3_w2_qf1 = 2)%nat) by reflexivity.
    rewrite Hq in Hc.
    lia.
Defined.

Lemma sl3_w2_gf_pow_len2 : forall k : nat,
  (length (gf_pow sl3_w2_qf2 k) <= 2 * k + 1)%nat.
Proof.
  induction k as [| k IH].
  - cbn [gf_pow length]. lia.
  - assert (Hne : (0 < length (gf_pow sl3_w2_qf2 k))%nat)
      by (apply sl3_w2_gf_pow_nonnil; unfold sl3_w2_qf2; cbn [length]; lia).
    cbn [gf_pow].
    pose proof (sl3_w2_length_conv_le sl3_w2_qf2 (gf_pow sl3_w2_qf2 k)
                  (ltac:(unfold sl3_w2_qf2; cbn [length]; lia)) Hne) as Hc.
    assert (Hq : (length sl3_w2_qf2 = 3)%nat) by reflexivity.
    rewrite Hq in Hc.
    lia.
Defined.

Lemma sl3_w2_gf_pow_len3 : forall k : nat,
  (length (gf_pow sl3_w2_qf3 k) <= 2 * k + 1)%nat.
Proof.
  induction k as [| k IH].
  - cbn [gf_pow length]. lia.
  - assert (Hne : (0 < length (gf_pow sl3_w2_qf3 k))%nat)
      by (apply sl3_w2_gf_pow_nonnil; unfold sl3_w2_qf3; cbn [length]; lia).
    cbn [gf_pow].
    pose proof (sl3_w2_length_conv_le sl3_w2_qf3 (gf_pow sl3_w2_qf3 k)
                  (ltac:(unfold sl3_w2_qf3; cbn [length]; lia)) Hne) as Hc.
    assert (Hq : (length sl3_w2_qf3 = 3)%nat) by reflexivity.
    rewrite Hq in Hc.
    lia.
Defined.

Lemma sl3_w2_length_conv_nonnil : forall f g : tbl,
  (0 < length f)%nat -> (0 < length (conv f g))%nat.
Proof.
  intros f g Hf. destruct f as [| a f']; [ cbn [length] in Hf; lia | ].
  cbn [conv]. rewrite length_add_tbl. cbn [length].
  pose proof (Nat.le_max_r (length (map (Z.mul a) g))
              (S (length (conv f' g)))) as Hmx.
  lia.
Defined.

Lemma sl3_w2_ptable_len : forall n : nat,
  (length (sl3_w2_ptable n) <= 10 * n + 1)%nat.
Proof.
  intros n. unfold sl3_w2_ptable, sl3_w2_qpoly.
  rewrite map_length.
  pose proof (sl3_w2_gf_pow_len1 (2 * n)) as Hf1.
  pose proof (sl3_w2_gf_pow_len2 (2 * n)) as Hf2.
  pose proof (sl3_w2_gf_pow_len3 (2 * n)) as Hf3.
  assert (Hin : (0 < length (conv (gf_pow sl3_w2_qf2 (2 * n))
                                  (gf_pow sl3_w2_qf3 (2 * n))))%nat).
  { apply sl3_w2_length_conv_nonnil.
    apply sl3_w2_gf_pow_nonnil.
    unfold sl3_w2_qf2. cbn [length]. lia. }
  pose proof (sl3_w2_length_conv_le (gf_pow sl3_w2_qf2 (2 * n))
              (gf_pow sl3_w2_qf3 (2 * n))
              (ltac:(apply sl3_w2_gf_pow_nonnil; unfold sl3_w2_qf2; cbn [length]; lia))
              (ltac:(apply sl3_w2_gf_pow_nonnil; unfold sl3_w2_qf3; cbn [length]; lia))) as Hc1.
  pose proof (sl3_w2_length_conv_le (gf_pow sl3_w2_qf1 (2 * n))
              (conv (gf_pow sl3_w2_qf2 (2 * n)) (gf_pow sl3_w2_qf3 (2 * n)))
              (ltac:(apply sl3_w2_gf_pow_nonnil; unfold sl3_w2_qf1; cbn [length]; lia)) Hin) as Hc2.
  lia.
Defined.

(* ================================================================== *)
(* Section 4. The kappa weights and the folded pole numerator.         *)
(* The fold convention follows the landed GF anchor tier:              *)
(*   poleZ n k = sum over i <= k of                                    *)
(*     ptable n [k - i] * kappa n i * 10^(k - i),                      *)
(*   kappa n i = (-1)^i * binom (3n + i) i.                            *)
(* ================================================================== *)

(* the triangle inequality over Z absolute values *)
Lemma sl3_w2_abs_triangle : forall a b : Z,
  (Z.abs (a + b) <= Z.abs a + Z.abs b)%Z.
Proof.
  intros a b.
  pose proof (proj2 (Z.abs_le a (Z.abs a))) as Ha.
  pose proof (proj2 (Z.abs_le b (Z.abs b))) as Hb.
  apply (proj2 (Z.abs_le (a + b) (Z.abs a + Z.abs b))).
  split; lia.
Defined.

Definition sl3_w2_kappa (n r : nat) : Z :=
  (if Nat.odd r then (-1)%Z else 1%Z) * Z.of_nat (binomP (3 * n + r) r).

Fixpoint sl3_w2_pole_sum (n k i : nat) : Z :=
  match i with
  | O => nth k (sl3_w2_ptable n) 0 * sl3_w2_kappa n 0 * 10 ^ Z.of_nat k
  | S i' =>
      sl3_w2_pole_sum n k i'
      + nth (k - S i') (sl3_w2_ptable n) 0 * sl3_w2_kappa n (S i')
        * 10 ^ Z.of_nat (k - S i')
  end.

Definition sl3_w2_poleZ (n k : nat) : Z := sl3_w2_pole_sum n k k.

Lemma sl3_w2_kappa_abs : forall n r : nat,
  Z.abs (sl3_w2_kappa n r) = Z.of_nat (binomP (3 * n + r) r).
Proof.
  intros n r. unfold sl3_w2_kappa.
  destruct (Nat.odd r).
  - rewrite Z.abs_mul. change (Z.abs (-1)) with 1%Z.
    rewrite Z.mul_1_l. rewrite Z.abs_eq by (apply Nat2Z.is_nonneg). reflexivity.
  - rewrite Z.abs_mul. change (Z.abs 1) with 1%Z.
    rewrite Z.mul_1_l. rewrite Z.abs_eq by (apply Nat2Z.is_nonneg). reflexivity.
Defined.

Lemma sl3_w2_pow10_abs : forall e : Z, (0 <= e)%Z -> Z.abs (10 ^ e) = 10 ^ e.
Proof.
  intros e He. apply Z.abs_eq.
  assert (Hpos : (0 < 10 ^ e)%Z) by (apply Z.pow_pos_nonneg; lia).
  lia.
Defined.

(* ================================================================== *)
(* Section 5. The weighted evaluation of the folded pole table and     *)
(* the universal absolute-value bound of the folded pole numerator.    *)
(* ================================================================== *)

Lemma sl3_w2_awZ_ptable : forall n : nat,
  awZ (sl3_w2_ptable n)
  = 5 * 15 ^ Z.of_nat (2 * n) * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)).
Proof.
  intros n. unfold sl3_w2_ptable, sl3_w2_qpoly.
  rewrite awZ_map_mul.
  rewrite !awZ_conv.
  rewrite !awZ_gf_pow.
  unfold sl3_w2_qf1, sl3_w2_qf2, sl3_w2_qf3.
  replace (awZ [5%Z; 1%Z]) with 15%Z by (cbn [awZ]; lia).
  replace (awZ [40%Z; 12%Z; 1%Z]) with 260%Z by (cbn [awZ]; lia).
  replace (awZ [20%Z; 8%Z; 1%Z]) with 200%Z by (cbn [awZ]; lia).
  ring.
Defined.

Lemma sl3_w2_3np1_le_pow4 : forall n : nat, (3 * n + 1 <= 4 ^ n)%nat.
Proof.
  induction n as [| n IH].
  - cbn [Nat.pow]. lia.
  - rewrite Nat.pow_succ_r'.
    assert (Hpos : (0 < 4 ^ n)%nat).
    { apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. }
    lia.
Defined.

Theorem sl3_w2_poleZ_abs_le : forall n k : nat, (k <= 3 * n)%nat ->
  piu_mu_ZleT (Z.abs (sl3_w2_poleZ n k))
    ((2 ^ Z.of_nat (8 * n))
     * (5 * 15 ^ Z.of_nat (2 * n) * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))))%Z.
Proof.
  intros n k Hk.
  apply piu_mu_ZleT_i.
  assert (Hawn : (0 <= awZ (sl3_w2_ptable n))%Z).
  { apply awZ_nonneg.
    unfold sl3_w2_ptable. apply map_mul_nonneg; [ lia | apply sl3_w2_qpoly_nonneg ]. }
  (* the uniform per-term bound: each folded term is a single table    *)
  (* entry at its own power of ten, scaled by the kappa weight         *)
  (* bounded by the Pascal upper bound at 2^(6n).                      *)
  assert (Hpt : forall i : nat, (i <= k)%nat ->
    (Z.abs (nth (k - i) (sl3_w2_ptable n) 0 * sl3_w2_kappa n i
             * 10 ^ Z.of_nat (k - i))
     <= awZ (sl3_w2_ptable n) * 2 ^ Z.of_nat (6 * n))%Z).
  { intros i Hi.
    destruct (le_lt_dec (length (sl3_w2_ptable n)) (k - i)) as [Hge | Hlt].
    - (* the index is past the table end: the entry is zero *)
      unfold sl3_w2_ptable in Hge. rewrite map_length in Hge.
      rewrite (sl3_w2_ptable_nth_overflow n (k - i) Hge).
      rewrite Z.abs_mul. rewrite Z.abs_mul.
      rewrite sl3_w2_kappa_abs.
      rewrite (sl3_w2_pow10_abs (Z.of_nat (k - i))) by (apply Nat2Z.is_nonneg).
      change (Z.abs 0) with 0%Z.
      lia.
    - (* in range: the weighted single-entry bound and the Pascal weight *)
      rewrite Z.abs_mul. rewrite Z.abs_mul.
      rewrite sl3_w2_kappa_abs.
      rewrite (sl3_w2_pow10_abs (Z.of_nat (k - i))) by (apply Nat2Z.is_nonneg).
      rewrite Z.abs_eq.
      2:{ pose proof (sl3_w2_ptable_entry_nonnegT n (k - i)) as HpnE.
          destruct HpnE as [HpnE]. exact HpnE. }
      assert (Hweighted : (nth (k - i) (sl3_w2_ptable n) 0
                           * 10 ^ Z.of_nat (k - i)
                           <= awZ (sl3_w2_ptable n))%Z)
        by (apply awZ_ge_nth_pow;
            [ unfold sl3_w2_ptable; apply map_mul_nonneg; [ lia | apply sl3_w2_qpoly_nonneg ] |
             exact Hlt ]).
      assert (Hkap : (Z.of_nat (binomP (3 * n + i) i)
                      <= 2 ^ Z.of_nat (3 * n + i))%Z).
      { rewrite <- sl3_w2_Znat_pow.
        apply Nat2Z.inj_le. apply sl3_w2_binomP_le_pow2. }
      assert (Hle3 : (Z.of_nat (3 * n + i) <= Z.of_nat (6 * n))%Z)
        by (apply Nat2Z.inj_le; lia).
      assert (Hkap2 : (Z.of_nat (binomP (3 * n + i) i)
                       <= 2 ^ Z.of_nat (6 * n))%Z).
      { apply (Z.le_trans _ (2 ^ Z.of_nat (3 * n + i))); [ exact Hkap | ].
        apply Z.pow_le_mono_r; [ lia | exact Hle3 ]. }
      assert (Hpow : (0 < 260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))%Z)
        by (apply sl3_w2_mul_pos; apply Z.pow_pos_nonneg; lia).
      assert (Hawnp : (0 < awZ (sl3_w2_ptable n))%Z)
        by (rewrite sl3_w2_awZ_ptable;
            apply sl3_w2_mul_pos;
            [ apply sl3_w2_mul_pos; [ lia | apply Z.pow_pos_nonneg; lia ] | exact Hpow ]).
      destruct (Z.eq_dec (Z.of_nat (binomP (3 * n + i) i)) 0) as [Hz | Hnz].
      + rewrite Hz. rewrite Z.mul_0_r.
        assert (Hpos : (0 <= awZ (sl3_w2_ptable n) * 2 ^ Z.of_nat (6 * n))%Z)
          by (apply Z.mul_nonneg_nonneg; [ apply awZ_nonneg;
               unfold sl3_w2_ptable; apply map_mul_nonneg; [ lia | apply sl3_w2_qpoly_nonneg ] |
               pose proof (Z.pow_pos_nonneg 2 (Z.of_nat (6 * n))
                 (ltac:(lia)) (ltac:(lia))); lia ]).
        lia.
      + rewrite (Z.mul_comm (nth (k - i) (sl3_w2_ptable n) 0)
                   (Z.of_nat (binomP (3 * n + i) i))).
        apply (Z.le_trans _
          (Z.of_nat (binomP (3 * n + i) i) * awZ (sl3_w2_ptable n))%Z).
        * pose proof
            (proj1 (Z.mul_le_mono_pos_l (nth (k - i) (sl3_w2_ptable n) 0
                          * 10 ^ Z.of_nat (k - i))
                      (awZ (sl3_w2_ptable n)) (Z.of_nat (binomP (3 * n + i) i))
                      (ltac:(lia))) Hweighted) as Hs1.
          replace (Z.of_nat (binomP (3 * n + i) i)
                   * nth (k - i) (sl3_w2_ptable n) 0
                   * 10 ^ Z.of_nat (k - i))
            with (Z.of_nat (binomP (3 * n + i) i)
                  * (nth (k - i) (sl3_w2_ptable n) 0 * 10 ^ Z.of_nat (k - i)))
            by ring.
          exact Hs1.
        * rewrite (Z.mul_comm (awZ (sl3_w2_ptable n))
                     (2 ^ Z.of_nat (6 * n))).
          exact (proj1 (Z.mul_le_mono_pos_r (Z.of_nat (binomP (3 * n + i) i))
                     (2 ^ Z.of_nat (6 * n)) (awZ (sl3_w2_ptable n)) Hawnp)
                   Hkap2). }
  clear Hawn.
  (* the fold induction: the absolute value of the running sum is      *)
  (* bounded by the count times the uniform bound (triangle + step).   *)
  assert (Hawn : (0 <= awZ (sl3_w2_ptable n))%Z).
  { apply awZ_nonneg.
    unfold sl3_w2_ptable. apply map_mul_nonneg; [ lia | apply sl3_w2_qpoly_nonneg ]. }
  assert (Hstep : forall i : nat, (i <= k)%nat ->
    (Z.abs (sl3_w2_pole_sum n k i)
     <= Z.of_nat (S i) * (awZ (sl3_w2_ptable n) * 2 ^ Z.of_nat (6 * n)))%Z).
  { induction i as [| i IH]; intros Hi.
    - cbn [sl3_w2_pole_sum].
      pose proof (Hpt 0%nat (Nat.le_0_l k)) as Hb.
      rewrite Nat.sub_0_r in Hb.
      rewrite Nat2Z.inj_succ. cbn [Z.of_nat].
      rewrite Z.mul_1_l. lia.
    - cbn [sl3_w2_pole_sum].
      pose proof (IH (Nat.le_trans i (S i) k (Nat.le_succ_diag_r i) Hi)) as Hrec.
      pose proof (Hpt (S i) Hi) as Hb.
      rewrite sl3_w2_abs_triangle.
      rewrite Nat2Z.inj_succ.
      rewrite Z.mul_succ_l.
      lia. }
  pose proof (Hstep k (le_n k)) as Hfin.
  rewrite sl3_w2_awZ_ptable in Hfin.
  cbn [sl3_w2_poleZ] in Hfin.
  (* the count bound: S k <= 3n + 1 <= 4^n, and 4^n = 2^(2n), so the   *)
  (* count factor folds into the 2^(8n) register of the target.        *)
  assert (Hcnt : (S k <= 4 ^ n)%nat).
  { assert (H1 : (S k <= 3 * n + 1)%nat) by lia.
    assert (H2 : (3 * n + 1 <= 4 ^ n)%nat) by apply sl3_w2_3np1_le_pow4.
    lia. }
  assert (HcntZ : (Z.of_nat (S k) <= 2 ^ Z.of_nat (2 * n))%Z).
  { assert (Hle : (Z.of_nat (S k) <= Z.of_nat (4 ^ n))%Z)
      by (apply Nat2Z.inj_le; exact Hcnt).
    rewrite sl3_w2_Znat_pow4 in Hle.
    replace (2 * n)%nat with (n + n)%nat by lia.
    rewrite Nat2Z.inj_add.
    rewrite Z.pow_add_r by lia.
    rewrite <- (Z.pow_mul_l 2 2 (Z.of_nat n)).
    change (2 * 2)%Z with 4%Z.
    exact Hle. }
  assert (HX : (0 < 260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))%Z)
    by (apply sl3_w2_mul_pos; apply Z.pow_pos_nonneg; lia).
  assert (HX2 : (0 < 15 ^ Z.of_nat (2 * n) * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)))%Z)
    by (apply sl3_w2_mul_pos; [ apply Z.pow_pos_nonneg; lia | exact HX ]).
  assert (HX3 : (0 < 5 * 15 ^ Z.of_nat (2 * n) * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)))%Z)
    by (apply sl3_w2_mul_pos;
        [ apply sl3_w2_mul_pos; [ lia | apply Z.pow_pos_nonneg; lia ] | exact HX ]).
  apply (Z.le_trans _
    (Z.of_nat (S k)
     * (5 * 15 ^ Z.of_nat (2 * n) * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
        * 2 ^ Z.of_nat (6 * n)))%Z).
  - exact Hfin.
  - apply (Z.le_trans _
      (2 ^ Z.of_nat (2 * n)
       * (5 * 15 ^ Z.of_nat (2 * n) * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
          * 2 ^ Z.of_nat (6 * n)))%Z).
    + rewrite (Z.mul_comm (Z.of_nat (S k))
                 (5 * 15 ^ Z.of_nat (2 * n)
                  * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
                  * 2 ^ Z.of_nat (6 * n))).
      rewrite (Z.mul_comm (2 ^ Z.of_nat (2 * n))
                 (5 * 15 ^ Z.of_nat (2 * n)
                  * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
                  * 2 ^ Z.of_nat (6 * n))).
      assert (HM : (0 < 5 * 15 ^ Z.of_nat (2 * n)
                        * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
                        * 2 ^ Z.of_nat (6 * n))%Z)
        by (apply sl3_w2_mul_pos; [ exact HX3 | apply Z.pow_pos_nonneg; lia ]).
      exact (proj1 (Z.mul_le_mono_pos_l (Z.of_nat (S k))
                     (2 ^ Z.of_nat (2 * n))
                     (5 * 15 ^ Z.of_nat (2 * n)
                      * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
                      * 2 ^ Z.of_nat (6 * n)) HM)
                 HcntZ).
    + replace (8 * n)%nat with (2 * n + 6 * n)%nat by lia.
      rewrite Nat2Z.inj_add.
      rewrite Z.pow_add_r by lia.
      rewrite <- (Z.mul_assoc (2 ^ Z.of_nat (2 * n)) (2 ^ Z.of_nat (6 * n))
                    (5 * 15 ^ Z.of_nat (2 * n)
                     * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)))).
      assert (Hone6 : (0 < 2 ^ Z.of_nat (6 * n))%Z)
        by (apply Z.pow_pos_nonneg; lia).
      assert (HM6 : (0 < 5 * 15 ^ Z.of_nat (2 * n)
                        * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))
                        * 2 ^ Z.of_nat (6 * n))%Z)
        by (apply sl3_w2_mul_pos; [ exact HX3 | exact Hone6 ]).
      assert (Hge6 : (1 <= 2 ^ Z.of_nat (6 * n))%Z) by lia.
      assert (HleM : (((5 * 15 ^ Z.of_nat (2 * n)
                  * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)))
                 * 2 ^ Z.of_nat (6 * n))
                 <= 2 ^ Z.of_nat (6 * n)
                  * (5 * 15 ^ Z.of_nat (2 * n)
                     * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))))%Z).
      { rewrite (Z.mul_comm (2 ^ Z.of_nat (6 * n))
                  (5 * 15 ^ Z.of_nat (2 * n)
                   * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)))).
        apply Z.le_refl. }
      apply (proj1 (Z.mul_le_mono_pos_l
                     ((5 * 15 ^ Z.of_nat (2 * n)
                       * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n)))
                      * 2 ^ Z.of_nat (6 * n))
                     (2 ^ Z.of_nat (6 * n)
                      * (5 * 15 ^ Z.of_nat (2 * n)
                         * (260 ^ Z.of_nat (2 * n) * 200 ^ Z.of_nat (2 * n))))
                     (2 ^ Z.of_nat (2 * n))
                     (ltac:(apply Z.pow_pos_nonneg; lia))) HleM).
Defined.

(* ================================================================== *)
(* Section 6. The registered supply slots (born contract faces) and    *)
(* the conditional assembly.                                           *)
(* ================================================================== *)

(* The inject-to-Qpower bridge: the integer-power inject form is      *)
(* below the dyadic Qpower form at the same exponent (the two are     *)
(* equal as rationals; only the carrier form differs).                *)
Lemma sl3_w2_inj_le_qpow : forall e : nat,
  (inject_Z (2 ^ Z.of_nat e) <= Qpower (inject_Z 2) (Z.of_nat e))%Q.
Proof.
  intros e.
  assert (Hfe : (inject_Z (Z.of_nat (2 ^ e))
                 == Qpower (inject_Z 2) (Z.of_nat e))%Q)
    by (rewrite Nat2Z.inj_pow; apply Zpower_Qpower; apply Nat2Z.is_nonneg).
  apply (Qle_trans _ (inject_Z (Z.of_nat (2 ^ e)))).
  - apply (S02_CauchyComplete.qeq_imp_qle _ _).
    rewrite <- sl3_w2_Znat_pow. apply Qeq_refl.
  - apply (S02_CauchyComplete.qeq_imp_qle _ _). exact Hfe.
Defined.

(* The registered domination slot of the GF workorder: the folded     *)
(* pole numerator against the band-17 register with its exact power   *)
(* of ten.  Born statement - honestly unproven; its discharge needs   *)
(* the cancellation structure of the pole expansion, and the          *)
(* machine-verified margin band is a numeric guardrail, NOT a proof.  *)
Definition sl3_w2_poleZ_dom_17 : Set :=
  forall n k : nat, (k <= 3 * n)%nat ->
    piu_mu_ZleT (Z.abs (sl3_w2_poleZ n k))
      ((2 ^ Z.of_nat (17 * n)) * 10 ^ Z.of_nat (3 * n + 1 + k))%Z.

(* The all-j supply face at the band argument s (the draft section    *)
(* 1.3 face with the Q-valued-carrier type correction registered by   *)
(* the landed d4 chain unit: the tree carrier is Q-valued, so the     *)
(* absolute value stays in Q directly).  Born statement - the         *)
(* universal proof is the GF decomposition supply obligation.         *)
Definition sl3_w2_gf_domin_face (s : nat) : Set :=
  forall n j : nat, (j <= 3 * n)%nat ->
    S02_CauchyComplete.QleT' (Qabs (piu_zz_Aj n j))
      (Qpower (inject_Z 2) (Z.of_nat (s * n))).

(* The exact pole-extraction weld: the folded pole numerator equals   *)
(* the scaled and signed coefficient at the mirror index, over the    *)
(* RAW signed tree carrier (the landed anchor tier convention: the    *)
(* sign flip lives in the kappa alternation, the raw Aj carries its   *)
(* own sign).  Born statement - the machine anchors certify the head  *)
(* samples; the universal identity is the registered identity         *)
(* obligation.                                                        *)
Definition sl3_w2_pole_weld_face : Set :=
  forall n k : nat, (k <= 3 * n)%nat ->
    piu_zz_gauss_pair.qeqT (inject_Z (sl3_w2_poleZ n k))
         ((if Nat.odd k then (-1)#1 else (1)#1)
          * piu_zz_Aj n (3 * n - k)
          * inject_Z (10 ^ Z.of_nat (3 * n + 1 + k)))%Q.

(* The conditional assembly: the identity weld plus the band-17       *)
(* domination slot discharge the all-j supply face at band 17.        *)
(* Engine: the weld is an exact Q-equality, so the coefficient equals *)
(* the pole numerator divided by the exact power of ten; the          *)
(* domination bound then cancels the power term and the band          *)
(* register remains.                                                  *)
Theorem sl3_w2_allj17_from_pole :
  sl3_w2_pole_weld_face -> sl3_w2_poleZ_dom_17 -> sl3_w2_gf_domin_face 17.
Proof.
  intros Hw Hd.
  unfold sl3_w2_gf_domin_face.
  intros n j Hj.
  assert (Hkj : (3 * n - j <= 3 * n)%nat) by lia.
  assert (Hback : (3 * n - (3 * n - j) = j)%nat) by lia.
  pose proof (Hd n (3 * n - j)%nat Hkj) as Hdom.
  destruct Hdom as [HdomZ].
  pose proof (Hw n (3 * n - j)%nat Hkj) as Hweld.
  inversion Hweld as [x0 y0 Heq].
  rewrite Hback in Heq.
  (* the weld in inject form over the RAW signed carrier:               *)
  (*   inj (poleZ n k) == (+-1) * Aj n j * inj 10^E,  E = 6n + 1 - j.   *)
  assert (HabsInj : forall w : Z, (Qabs (inject_Z w) == inject_Z (Z.abs w))%Q).
  { intros w. unfold inject_Z. destruct w as [|p|pn].
    - cbn [Qabs Z.abs inject_Z Qnum Qden]. apply Qeq_refl.
    - rewrite Z.abs_eq by lia. cbn [Qabs inject_Z Qnum Qden]. apply Qeq_refl.
    - rewrite Z.abs_neq by lia. cbn [Qabs inject_Z Qnum Qden]. apply Qeq_refl. }
  assert (Hone : (Qabs ((if Nat.odd (3 * n - j)%nat then (-1)#1 else (1)#1))
                 == (1 # 1))%Q).
  { unfold Qabs. destruct (Nat.odd (3 * n - j)%nat).
    - cbn [Qnum Qden]. apply Qeq_refl.
    - cbn [Qnum Qden]. apply Qeq_refl. }
  assert (Hpos : (0 < inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))%Q).
  { unfold Qlt, inject_Z. cbn [Qnum Qden].
    rewrite Z.mul_0_l. rewrite Z.mul_1_r.
    apply (proj1 (Z.compare_lt_iff 0 (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))).
    apply Z.pow_pos_nonneg; lia. }
  assert (Hle10 : (0 <= inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))%Q).
  { unfold Qle, inject_Z. cbn [Qnum Qden].
    pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (3 * n + 1 + (3 * n - j)))
      (ltac:(lia)) (ltac:(lia))) as Hp.
    rewrite Z.mul_0_l, Z.mul_1_r. lia. }
  assert (Hpos10 : (Qabs (inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))
                   == inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))%Q)
    by (apply Qabs_pos; exact Hle10).
  (* absolute values on both sides of the weld.                        *)
  assert (HabsWeld : (Qabs (inject_Z (sl3_w2_poleZ n (3 * n - j)%nat))
                   == Qabs (piu_zz_Aj n j)
                      * inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))%Q).
  { pose proof (Qabs_wd _ _ Heq) as Habsw.
    rewrite Qabs_Qmult in Habsw.
    rewrite Qabs_Qmult in Habsw.
    rewrite Hone in Habsw.
    rewrite Hpos10 in Habsw.
    rewrite Qmult_1_l in Habsw.
    exact Habsw. }
  clear Heq.
  (* the domination bound pushed into Q through inject_Z.              *)
  assert (HdomQ : (inject_Z (Z.abs (sl3_w2_poleZ n (3 * n - j)%nat))
                   <= inject_Z ((2 ^ Z.of_nat (17 * n))
                                * 10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))%Q).
  { unfold Qle, inject_Z. cbn [Qnum Qden]. rewrite !Z.mul_1_r. exact HdomZ. }
  assert (Hd2 : (inject_Z ((2 ^ Z.of_nat (17 * n))
                   * 10 ^ Z.of_nat (3 * n + 1 + (3 * n - j)))
                  == inject_Z (2 ^ Z.of_nat (17 * n))
                     * inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))%Q).
  { unfold inject_Z. cbn [Qmult]. apply Qeq_refl. }
  (* the key bound in the inject dialect.                              *)
  assert (Hkey : (Qabs (piu_zz_Aj n j)
                  <= inject_Z (2 ^ Z.of_nat (17 * n)))%Q).
  { apply (Qmult_lt_0_le_reg_r _ _ (inject_Z (10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))).
    - exact Hpos.
    - apply (Qle_trans _ (inject_Z (Z.abs (sl3_w2_poleZ n (3 * n - j)%nat)))).
      + rewrite <- HabsWeld.
        rewrite <- (HabsInj (sl3_w2_poleZ n (3 * n - j)%nat)).
        apply (S02_CauchyComplete.qeq_imp_qle _ _). apply Qeq_refl.
      + apply (Qle_trans _ (inject_Z ((2 ^ Z.of_nat (17 * n))
                          * 10 ^ Z.of_nat (3 * n + 1 + (3 * n - j))))).
        * exact HdomQ.
        * rewrite Hd2. apply Z.le_refl. }
  apply Qle_to_QleT'.
  apply (Qle_trans _ (inject_Z (2 ^ Z.of_nat (17 * n)))).
  - exact Hkey.
  - apply sl3_w2_inj_le_qpow.
Defined.


(* ================================================================== *)
(* Section 7. Assumption audit.                                        *)
(* ================================================================== *)

Print Assumptions awZ_map_mul.
Print Assumptions awZ_add_tbl.
Print Assumptions awZ_conv.
Print Assumptions awZ_gf_pow.
Print Assumptions awZ_nonneg.
Print Assumptions awZ_ge_nth_pow.
Print Assumptions sl3_w2_mul_pos.
Print Assumptions sl3_w2_abs_triangle.
Print Assumptions sl3_w2_length_conv_le.
Print Assumptions sl3_w2_length_conv_nonnil.
Print Assumptions sl3_w2_gf_pow_nonnil.
Print Assumptions sl3_w2_ptable_nth_overflow.
Print Assumptions sl3_w2_inj_le_qpow.
Print Assumptions sl3_w2_binomP_le_pow2.
Print Assumptions sl3_w2_Znat_pow.
Print Assumptions sl3_w2_qpoly_nonneg.
Print Assumptions sl3_w2_ptable_entry_nonnegT.
Print Assumptions sl3_w2_ptable_len.
Print Assumptions sl3_w2_awZ_ptable.
Print Assumptions sl3_w2_3np1_le_pow4.
Print Assumptions sl3_w2_poleZ_abs_le.
Print Assumptions sl3_w2_allj17_from_pole.
