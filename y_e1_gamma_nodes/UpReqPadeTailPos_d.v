(* ConstructiveWorld-Main - positivity of the Pade denominator on the
   open interval from 1 to 2. *)

(** * UpReqPadeTailPos_d: the (1,2)-segment denominator positivity
      with the ratio-bound engine.

    Mission.  For the Pade denominator Q_n(x) on the open interval
      1 < x < 2: the ratio bound [pdq_R_ge_2] (the term ratio at
      least 2 whenever k < n, supported by the Z-level arithmetic
      leg k(2n-k+2) >= 0), the term-decay upgrade [pdq_term_decay_2],
      the non-strict main statement [pdq_den_pos_12] and the strict
      main statement [pdq_den_pos_12_strict] for all n (the n = 0
      unit case, the n = 1 closed form 1 - x/2, the alternating-sum
      strict engine for n >= 2), plus the closed forms [pdq_g0_one],
      [pdq_den0_one], [pdq_den1_form] and the strict first-pair
      step [pdq_g1_lt_g0].
    Dependencies.  S01_BaseRing through S15_TailFEPUp, UpReqPadeExp,
      UpReqPadeDenPos, UpReqPadeSign, UpReqAltSumPos,
      UpReqPadeQLeg; Stdlib QArith, Arith, Lia, Setoid, Morphisms.
    References.  Statement face conserved verbatim from the live-tree
      module UpReqPadeTailPos (its third section); the pdp and
      altsum engine legs of the library editions supply the ratio,
      coefficient and alternating-sum machinery.
    Constructivity.  Pure Set-level content; QleT'/QltT witness
      faces; the decidability branches go through boolean Nat tests;
      no classical principles, no axioms; every audited name is
      Closed under the global context.
    Build.  coqc -q -native-compiler no with the l0_local face plus
      the node build face, Coq 9.3.0, temperature guard wrapped.
*)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
Require Import UpReqPadeExp UpReqPadeDenPos UpReqPadeSign UpReqAltSumPos.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
From Stdlib Require Import Setoid Morphisms.

Local Open Scope Q_scope.

(* statement one: the ratio lower bound pdp_R n k >= 2 (k < n) *)
(* same skeleton as pdp_R_ge_1: 2 = inv(a) * (2*a) <= inv(a) * (b*c)
   = pdp_R, where 2*a <= b*c is supported by the Z-level arithmetic
   leg (k*(2n-k+2) >= 0). *)
Lemma pdq_R_ge_2 : forall n k : nat, (k < n)%nat -> QleT' 2%Q (pdp_R n k).
Proof.
  intros n k Hk.
  assert (Hlit : QleT' ((2 # 1) *
                          (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q
                       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
                         (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden Qmult Pos.mul].
    pose proof (pql_nat_ratio_mono2 n k Hk) as Hp.
    rewrite !Z.mul_1_r, ?Z.mul_1_l. exact Hp. }
  assert (Hinvpos : QleT' 0%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt, Qcompare. cbn [Qnum Qden]. apply Z.compare_lt_iff.
    rewrite Z.mul_0_l, !Z.mul_1_r, Znat.Nat2Z.inj_succ.
    exact (proj2 (Z.lt_succ_r 0%Z (Z.of_nat (n - Datatypes.S k)))
             (Znat.Nat2Z.is_nonneg (n - Datatypes.S k))). }
  assert (Ez : Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
               (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) == 1%Q).
  { apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))
      ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1) *
       Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      1%Q).
    - ring.
    - apply Qmult_inv_r. apply pdp_ZS1_nz. }
  apply (qleT'_trans 2%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
     (((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q)
    (pdp_R n k)).
  - apply qeq_leT'. apply Qeq_sym.
    apply (Qeq_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       ((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))
      (((2 # 1) *
        (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
         (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))))
      2%Q).
    + ring.
    + rewrite Ez. ring.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((2 # 1) * (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q)
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. unfold pdp_R. ring.
Qed.

(* statement two: the decay upgrade - termwise decrease while x <= 2
   (the x<=1 multiplicative monotone step replaced by the ratio step
   x <= 2 <= c_k/c_{k+1}). *)
Lemma pdq_term_decay_2 : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0%Q x -> QleT' x 2%Q ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx0 Hx2.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; exact Hk).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_trans _ _ _ (Nat.le_succ_diag_r k) Hk)).
  unfold pdp_g. rewrite E1, E2.
  change (q_pow x (Datatypes.S k)) with (x * q_pow x k).
  assert (HstepT : QleT' (pade_coeff n (Datatypes.S k) * x) (pade_coeff n k)).
  { apply (qleT'_trans (pade_coeff n (Datatypes.S k) * x)
                       (pade_coeff n (Datatypes.S k) * pdp_R n k)
                       (pade_coeff n k)).
    - apply pdp_qmult_le_compat_l.
      + apply (qleT'_trans x 2%Q (pdp_R n k)).
        * exact Hx2.
        * apply pdq_R_ge_2. exact Hk.
      + apply qltT_leT'. apply pdp_coeff_pos_any.
    - apply qeq_leT'. apply Qeq_sym. apply pdp_coeff_ratio. exact Hk. }
  apply (qleT'_trans
           (pade_coeff n (Datatypes.S k) * (x * q_pow x k))
           ((pade_coeff n (Datatypes.S k) * x) * q_pow x k)
           (pade_coeff n k * q_pow x k)).
  - apply qeq_leT'. ring.
  - apply pdp_qmult_le_compat_r.
    + exact HstepT.
    + apply Qle_to_QleT'. apply q_pow_nonneg. apply QleT'_to_Qle. exact Hx0.
Qed.

(* statement three (main, non-strict): 1 < x < 2 implies 0 <= Q_n(x).
   Statement face follows the pdp_den_pos shape (QleT' conclusion);
   skeleton as pdp_den_pos, with the decay slot replaced by
   pdq_term_decay_2. *)
Theorem pdq_den_pos_12 : forall (n : nat) (x : Q),
  QltT 1%Q x -> QltT x 2%Q -> QleT' 0%Q (pade_den n x).
Proof.
  intros n x Hlo Hhi.
  assert (Hx0 : QleT 0%Q x).
  { left. apply Qlt_to_QltT. apply (Qlt_trans 0%Q 1%Q x).
    - unfold Qlt. reflexivity.
    - apply QltT_to_Qlt. exact Hlo. }
  assert (Hxa : QleT' 0%Q x) by (apply altsum_QleT_to_QleT'; exact Hx0).
  assert (Hx2 : QleT' x 2%Q)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hhi).
  assert (Hb : pade_den n x == altsum (pdp_g n x) (Datatypes.S n))
    by apply pdp_den_altsum.
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply pdq_term_decay_2;
          [apply Nat.leb_le in E; exact E | exact Hxa | exact Hx2].
      * apply pdp_g_decay_hi; [exact Hxa | apply Nat.leb_gt in E; exact E].
  - apply qeq_leT'. apply Qeq_sym. exact Hb.
Qed.

(* statement four support: strictness kit *)

(* 4a: g(0) = 1 (c_{n,0} = 1 and x^0 = 1, for all n) *)
Lemma pdq_g0_one : forall (n : nat) (x : Q), pdp_g n x 0%nat == 1%Q.
Proof.
  intros n x. unfold pdp_g.
  assert (E0 : (0 <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_0_l n)).
  rewrite E0. cbn [q_pow].
  rewrite (pade_coeff_0_one n). ring.
Qed.

(* 4b: strict first pair g(1) < g(0) - without computing c_{n,1}
   explicitly, through the ratio identity c_0 == c_1 * R_0 with
   x < 2 <= R_0 and c_1 > 0. *)
Lemma pdq_g1_lt_g0 : forall (n : nat) (x : Q),
  (1 <= n)%nat -> QltT 1%Q x -> QltT x 2%Q ->
  QltT (pdp_g n x 1%nat) (pdp_g n x 0%nat).
Proof.
  intros n x Hn Hlo Hhi.
  assert (Hk : (0 < n)%nat) by exact Hn.
  assert (E0 : (0 <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_trans _ _ _ (Nat.le_0_l 1) Hn)).
  assert (E1 : (1 <=? n)%nat = true) by (apply Nat.leb_le; exact Hn).
  unfold pdp_g. rewrite E1, E0. cbn [q_pow].
  apply Qlt_to_QltT.
  repeat rewrite Qmult_1_r.
  rewrite (pdp_coeff_ratio n 0%nat Hk).
  assert (Hc : x * pade_coeff n (Datatypes.S 0)
               < pdp_R n 0 * pade_coeff n (Datatypes.S 0)).
  { apply (Qmult_lt_compat_r x (pdp_R n 0) (pade_coeff n (Datatypes.S 0))).
    - apply QltT_to_Qlt. apply pdp_coeff_pos_any.
    - apply (Qlt_le_trans x 2%Q (pdp_R n 0)).
      + apply QltT_to_Qlt. exact Hhi.
      + apply QleT'_to_Qle. apply pdq_R_ge_2. exact Hk. }
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) x).
  rewrite (Qmult_comm (pade_coeff n (Datatypes.S 0)) (pdp_R n 0)).
  exact Hc.
Qed.

(* 4c: the n=1 closed form den_1(x) == 1 - x/2 (explicit application
   of the numeric coefficient anchor) *)
Lemma pdq_den1_form : forall x : Q,
  pade_den 1%nat x == 1%Q + Qopp ((1#2)%Q * x).
Proof.
  intros x. rewrite (pdp_den_altsum 1%nat x).
  unfold altsum. rewrite altsum_acc_T. rewrite altsum_acc_F.
  rewrite (altsum_acc_0_eq true (pdp_g 1%nat x) 2%nat).
  assert (E0 : (0 <=? 1)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_0_l 1)).
  assert (E1 : (1 <=? 1)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_refl 1)).
  unfold pdp_g. rewrite E0, E1. cbn [q_pow].
  rewrite (pade_coeff_0_one 1%nat). rewrite pds_c11. ring.
Qed.

(* 4c': the n=0 closed form den_0(x) == 1 (independent of x) *)
Lemma pdq_den0_one : forall x : Q, pade_den 0%nat x == 1%Q.
Proof.
  intros x. rewrite (pdp_den_altsum 0%nat x).
  unfold altsum. rewrite altsum_acc_T.
  rewrite (altsum_acc_0_eq false (pdp_g 0%nat x) 1%nat).
  rewrite (pdq_g0_one 0%nat x). ring.
Qed.

(* statement five (main, strict): 1 < x < 2 implies 0 < Q_n(x) for all
   n.  For n >= 2 through the strict alternating-sum engine (strict
   first pair plus nonnegative tail); n = 0 is the unit, n = 1 the
   closed form 1 - x/2 > 0. *)
Theorem pdq_den_pos_12_strict : forall (n : nat) (x : Q),
  QltT 1%Q x -> QltT x 2%Q -> QltT 0%Q (pade_den n x).
Proof.
  intros n x Hlo Hhi.
  assert (Hx2 : QleT' x 2%Q)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply QltT_to_Qlt; exact Hhi).
  destruct n as [|[|m]].
  - apply Qlt_to_QltT. rewrite pdq_den0_one. unfold Qlt. reflexivity.
  - apply Qlt_to_QltT. rewrite pdq_den1_form.
    apply QltT_to_Qlt in Hhi.
    assert (Hp : 0%Q < (1#2)%Q).
    { apply (Qinv_lt_0_compat 2%Q). unfold Qlt. reflexivity. }
    assert (Hs : x * (1#2)%Q < 2 * (1#2)%Q).
    { apply Qmult_lt_compat_r.
      - exact Hp.
      - exact Hhi. }
    pose proof Hs as Hs2.
    rewrite (Qmult_comm x (1#2)%Q), (Qmult_comm 2%Q (1#2)%Q) in Hs2.
    assert (E21 : (1#2)%Q * 2%Q == 1%Q) by ring.
    rewrite E21 in Hs2.
    apply (proj1 (Qlt_minus_iff ((1#2)%Q * x) 1%Q)).
    exact Hs2.
  - assert (Hxa : QleT' 0%Q x).
    { apply altsum_QleT_to_QleT'.
      left. apply Qlt_to_QltT. apply (Qlt_trans 0%Q 1%Q x).
      - unfold Qlt. reflexivity.
      - apply QltT_to_Qlt. exact Hlo. }
    assert (Hdec : forall k : nat,
              QleT' (pdp_g (Datatypes.S (Datatypes.S m)) x (Datatypes.S k))
                    (pdp_g (Datatypes.S (Datatypes.S m)) x k)).
    { intro k.
      destruct (Nat.leb (Datatypes.S k) (Datatypes.S (Datatypes.S m))) eqn:E.
      - apply pdq_term_decay_2;
          [apply Nat.leb_le in E; exact E | exact Hxa | exact Hx2].
      - apply pdp_g_decay_hi; [exact Hxa | apply Nat.leb_gt in E; exact E]. }
    apply (qeq_ltT
             (altsum (pdp_g (Datatypes.S (Datatypes.S m)) x)
                     (Datatypes.S (Datatypes.S (Datatypes.S m))))
             (pade_den (Datatypes.S (Datatypes.S m)) x)).
    + apply Qeq_sym. apply pdp_den_altsum.
    + apply altsum_pos_strict.
      * intro k. apply pdp_g_nonneg. exact Hxa.
      * exact Hdec.
      * apply pdq_g1_lt_g0;
          [exact (Nat.le_le_succ_r 1 (Datatypes.S m)
                    (proj1 (Nat.succ_le_mono 0 m) (Nat.le_0_l m)))
          | exact Hlo | exact Hhi].
      * exact (Nat.le_le_succ_r 2 (Datatypes.S (Datatypes.S m))
                 (proj1 (Nat.succ_le_mono 1 (Datatypes.S m))
                        (proj1 (Nat.succ_le_mono 0 m) (Nat.le_0_l m)))).
Qed.

Print Assumptions pdq_den_pos_12.
Print Assumptions pdq_den_pos_12_strict.
