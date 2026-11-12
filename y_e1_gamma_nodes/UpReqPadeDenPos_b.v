(* ConstructiveWorld-Main - UpReqPadeDenPos_b.v - general-n Pade denominator positivity for path C, statement surface preserved verbatim from UpReqPadeDenPos.v (seat1 bound surgery). *)
(* ==========================================================================
   Mission. blocks 4-6: index wrapping, coefficient ratio and adjacent decay, the den bridge and the main theorem pdp_den_pos
     (0 <= x <= 1 implies 0 <= pade_den n x) with its strict corollary.
   Dependencies. S01_BaseRing..S15_TailFEPUp chain, UpReqPadeExp,
     UpReqAltSumPos, UpReqPadeQLeg, UpReqPadeDenPos_a; Stdlib QArith, Arith, Lia, Setoid.
   References. Path C general-n Pade denominator positivity (PC2 engine
     altsum_nonneg_leT); source of record: UpReqPadeDenPos.v
     in the debtscan closure dossier (all-green at surgery time).
   Constructivity. Zero admission literals, no classical logic; statement
     surface fully Set-carried (QltT/QleT/QleT'); explicit assumptions
     declared symmetrically in the source dossier header, none forced.
   Build. coqc -q -native-compiler no -Q l0_local "" -Q build "" (Rocq 9.3.0
     at D:/ComplexAnalysis/attn/opam93), compile gate wrapped by
     50_toolkit/cpu_guard_v3.ps1; accepted by 50_toolkit/accept_node.py
     six-chain gate, node UpReqPadeDenPos.
   ========================================================================== *)
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
Require Import S15_TailFEPUp_dep.
Require Import UpReqPadeExp_dep UpReqAltSumPos_dep.
Require Import UpReqPadeQLeg_dep.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
Require Import UpReqPadeDenPos_a.

Section PadeDenPosQ.

(* ===== block 4: index wrapping (engine hypotheses must be index-total; the tail segment is zeroed) ===== *)

Definition pdp_g (n : nat) (x : Q) (k : nat) : Q :=
  (if (k <=? n)%nat then pade_coeff n k else 0%Q) * q_pow x k.

Lemma pdp_g_nonneg : forall (n : nat) (x : Q) (k : nat),
  QleT' 0 x -> QleT' 0 (pdp_g n x k).
Proof.
  intros n x k Hx. unfold pdp_g.
  destruct (k <=? n)%nat eqn:E.
  - apply Qle_to_QleT'. apply Qmult_le_0_compat.
    + apply Qlt_le_weak. apply QltT_to_Qlt. apply pdp_coeff_pos_any.
    + apply q_pow_nonneg. apply QleT'_to_Qle. exact Hx.
  - apply Qle_to_QleT'.
    apply (Qle_trans 0%Q 0%Q).
    + apply Qle_refl.
    + apply qeq_imp_qle. apply Qeq_sym. apply Qmult_0_l.
Qed.

Lemma pdp_g_decay_hi : forall (n : nat) (x : Q) (k : nat),
  QleT' 0 x -> (n < Datatypes.S k)%nat ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n x k Hx Hhi. unfold pdp_g.
  assert (E : (Datatypes.S k <=? n)%nat = false)
    by (apply Nat.leb_gt; lia).
  rewrite E.
  apply Qle_to_QleT'.
  apply (Qle_trans (0%Q * q_pow x (Datatypes.S k)) 0%Q).
  - apply qeq_imp_qle. apply Qmult_0_l.
  - apply QleT'_to_Qle. apply pdp_g_nonneg. exact Hx.
Qed.

(* ===== block 5: coefficient ratio and adjacent decay (S1 engine) =====

   core algebra: c_k / c_{k+1} = (2n-k)(k+1)/(n-k) >= 1 (k < n)
   (Z layer: (n-k) <= (2n-k)(k+1), discharged by pql_nat_ratio_mono;
   multiplication monotonicity assembled explicitly, zero Psatz).
   The coefficient ratio identity is closed by field. *)

Definition pdp_R (n k : nat) : Q :=
  (Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
  (Z.of_nat (Datatypes.S k) # 1) *
  Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q.

Lemma pdp_ZS1_nz : forall j : nat,
  ~ ((Z.of_nat (Datatypes.S j) # 1) == 0%Q).
Proof.
  intros j Heq. apply (Qlt_not_eq 0%Q ((Z.of_nat (Datatypes.S j)) # 1)%Q).
  - unfold Qlt. simpl. lia.
  - apply Qeq_sym. exact Heq.
Qed.

Lemma pdp_R_ge_1 : forall n k : nat, (k < n)%nat -> QleT' 1 (pdp_R n k).
Proof.
  intros n k Hk.
  assert (Hlit : QleT' ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q)
    (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
      (Z.of_nat (Datatypes.S k) # 1))%Q)).
  { apply Qle_to_QleT'. unfold Qle.
    cbn [Qnum Qden Qmult Pos.mul].
    pose proof (pql_nat_ratio_mono n k Hk). lia. }
  assert (Hinvpos : QleT' 0
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)%Q))).
  { apply qltT_leT'. apply Qlt_to_QltT. apply Qinv_lt_0_compat.
    unfold Qlt. cbn [Qnum Qden]. lia. }
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
  apply (qleT'_trans 1%Q
    (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
     ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)))%Q
    (pdp_R n k)).
  - apply qeq_leT'. apply Qeq_sym. exact Ez.
  - apply (qleT'_trans
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1))%Q
      (Qinv ((Z.of_nat (Datatypes.S (n - Datatypes.S k)) # 1)) *
       (((Z.of_nat (Datatypes.S (2 * n - Datatypes.S k)) # 1) *
         (Z.of_nat (Datatypes.S k) # 1)))%Q)
      (pdp_R n k)).
    + apply pdp_qmult_le_compat_l; assumption.
    + apply qeq_leT'. unfold pdp_R. ring.
Qed.

Lemma pdp_coeff_ratio : forall n k : nat, (k < n)%nat ->
  pade_coeff n k == pade_coeff n (Datatypes.S k) * pdp_R n k.
Proof.
  intros n k Hk.
  unfold pade_coeff, Qdiv, pdp_R.
  replace (2 * n - k)%nat
    with (Datatypes.S (2 * n - Datatypes.S k))%nat by lia.
  replace (n - k)%nat
    with (Datatypes.S (n - Datatypes.S k))%nat by lia.
  rewrite (q_fact_succ (2 * n - Datatypes.S k)%nat).
  rewrite (q_fact_succ k%nat).
  rewrite (q_fact_succ (n - Datatypes.S k)%nat).
  field.
  all: repeat split.
  all: try solve [apply q_neq_of_lt; apply q_fact_pos | apply pdp_ZS1_nz].
Qed.

Lemma pdp_coeff_decay : forall n k : nat, (k < n)%nat ->
  QleT' (pade_coeff n (Datatypes.S k)) (pade_coeff n k).
Proof.
  intros n k Hk.
  assert (Hpos : QleT' 0 (pade_coeff n (Datatypes.S k))).
  { apply qltT_leT'. apply pdp_coeff_pos_any. }
  apply (qleT'_trans (pade_coeff n (Datatypes.S k))
    (pade_coeff n (Datatypes.S k) * pdp_R n k)
    (pade_coeff n k)).
  - apply (qleT'_trans (pade_coeff n (Datatypes.S k))
      (pade_coeff n (Datatypes.S k) * 1%Q)
      (pade_coeff n (Datatypes.S k) * pdp_R n k)).
    + apply qeq_leT'. ring.
    + apply pdp_qmult_le_compat_l.
      * apply pdp_R_ge_1. exact Hk.
      * exact Hpos.
  - apply qeq_leT'. apply Qeq_sym. apply pdp_coeff_ratio. exact Hk.
Qed.

Lemma pdp_term_decay : forall (n k : nat) (x : Q),
  (k < n)%nat -> QleT' 0 x -> QleT' x 1 ->
  QleT' (pdp_g n x (Datatypes.S k)) (pdp_g n x k).
Proof.
  intros n k x Hk Hx Hx1.
  assert (E1 : (Datatypes.S k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  assert (E2 : (k <=? n)%nat = true)
    by (apply Nat.leb_le; lia).
  unfold pdp_g. rewrite E1, E2.
  apply Qle_to_QleT'.
  assert (Hq : Qle 0 (q_pow x k))
    by (apply q_pow_nonneg; apply QleT'_to_Qle; exact Hx).
  assert (Hc0 : Qle 0 (pade_coeff n k)).
  { apply Qlt_le_weak. apply QltT_to_Qlt. apply pdp_coeff_pos_any. }
  assert (Hin : Qle (x * q_pow x k) (1%Q * q_pow x k)).
  { apply Qmult_le_compat_r.
    - apply QleT'_to_Qle. exact Hx1.
    - exact Hq. }
  assert (Hsc : Qle ((x * q_pow x k) * pade_coeff n k)
                    ((1%Q * q_pow x k) * pade_coeff n k))
    by (apply Qmult_le_compat_r; assumption).
  apply (Qle_trans (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
                   (pade_coeff n k * (x * q_pow x k))
                   (pade_coeff n k * q_pow x k)).
  - apply (Qle_trans (pade_coeff n (Datatypes.S k) * q_pow x (Datatypes.S k))
                     (pade_coeff n k * q_pow x (Datatypes.S k))
                     (pade_coeff n k * (x * q_pow x k))).
    + apply Qmult_le_compat_r.
      * apply QleT'_to_Qle. apply pdp_coeff_decay. exact Hk.
      * apply q_pow_nonneg. apply QleT'_to_Qle. exact Hx.
    + apply qeq_imp_qle. reflexivity.
  - apply (Qle_trans (pade_coeff n k * (x * q_pow x k))
                     ((x * q_pow x k) * pade_coeff n k)
                     (pade_coeff n k * q_pow x k)).
    + apply qeq_imp_qle. apply Qmult_comm.
    + apply (Qle_trans ((x * q_pow x k) * pade_coeff n k)
                       ((1%Q * q_pow x k) * pade_coeff n k)
                       (pade_coeff n k * q_pow x k)).
      * exact Hsc.
      * apply qeq_imp_qle. ring.
Qed.

(* ===== block 6: den bridge + S2 main theorem ===== *)

Lemma pdp_den_altsum : forall (n : nat) (x : Q),
  pade_den n x == altsum (pdp_g n x) (Datatypes.S n).
Proof.
  intros n x. unfold pade_den.
  apply (Qeq_trans
    (sum_upto (Datatypes.S n)
       (fun k : nat => q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k)))
    (sum_upto (Datatypes.S n)
       (fun k : nat => q_pow (- 1)%Q k * pdp_g n x k))
    (altsum (pdp_g n x) (Datatypes.S n))).
  - apply pdp_sum_upto_ext_range. intros k Hk. cbv beta. unfold pdp_g.
    destruct (k <=? n)%nat eqn:E.
    + reflexivity.
    + apply Nat.leb_gt in E. exfalso. lia.
  - apply (Qeq_trans
      (sum_upto (Datatypes.S n)
         (fun k : nat => q_pow (- 1)%Q k * pdp_g n x k))
      (sum_upto (Datatypes.S n)
         (fun k : nat =>
            (if altsum_sgp k then pdp_g n x k else Qopp (pdp_g n x k))))
      (altsum (pdp_g n x) (Datatypes.S n))).
    + apply sum_upto_ext. intro k. cbv beta. apply pdp_sign_term.
    + apply Qeq_sym. apply pdp_altsum_sum.
Qed.

(* S2 main theorem: 0 <= x <= 1 implies 0 <= denominator (general n, covering the n=0/n=1 cases) *)
Theorem pdp_den_pos : forall (n : nat) (x : Q),
  QleT 0 x -> QleT x 1 -> QleT' 0 (pade_den n x).
Proof.
  intros n x Hx0 Hx1.
  assert (Hxa : QleT' 0 x) by (apply altsum_QleT_to_QleT'; exact Hx0).
  assert (Hxb : QleT' x 1) by (apply altsum_QleT_to_QleT'; exact Hx1).
  assert (Hb : pade_den n x == altsum (pdp_g n x) (Datatypes.S n))
    by apply pdp_den_altsum.
  apply (qleT'_trans 0%Q (altsum (pdp_g n x) (Datatypes.S n)) (pade_den n x)).
  - apply altsum_nonneg_leT.
    + intro k. apply pdp_g_nonneg. exact Hxa.
    + intro k. destruct (Nat.leb (Datatypes.S k) n) eqn:E.
      * apply (pdp_term_decay n k x).
        -- apply Nat.leb_le in E. lia.
        -- exact Hxa.
        -- exact Hxb.
      * apply (pdp_g_decay_hi n x k).
        -- exact Hxa.
        -- apply Nat.leb_gt in E. lia.
  - apply qeq_leT'. apply Qeq_sym. exact Hb.
Qed.

Corollary pdp_den_pos_lt : forall (n : nat) (x : Q),
  QleT 0 x -> QltT x 1 -> QleT' 0 (pade_den n x).
Proof.
  intros n x H0 H1. apply pdp_den_pos.
  - exact H0.
  - left. exact H1.
Qed.

End PadeDenPosQ.
