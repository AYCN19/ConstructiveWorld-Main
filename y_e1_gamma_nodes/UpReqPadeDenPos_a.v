(* ConstructiveWorld-Main - UpReqPadeDenPos_a.v - general-n Pade denominator positivity for path C, statement surface preserved verbatim from UpReqPadeDenPos.v (seat1 bound surgery). *)
(* ==========================================================================
   Mission. blocks 0-3: Set-layer Q multiplication monotonicity engine, the (-1)^k closed form with parity shield,
     coefficient positivity, and the sum-shape bridge (altsum_acc vs
     sum_upto alignment).
   Dependencies. S01_BaseRing..S15_TailFEPUp chain, UpReqPadeExp,
     UpReqAltSumPos, UpReqPadeQLeg; Stdlib QArith, Arith, Lia, Setoid.
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

Section PadeDenPosQ.

(* ===== block 0: statement-surface multiplication monotonicity (fully Set-carried; Prop order translated inside proofs only) ===== *)

Lemma pdp_qmult_le_0 : forall a b : Q,
  QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof.
  intros a b Ha Hb.
  apply Qle_to_QleT'.
  apply Qmult_le_0_compat; apply QleT'_to_Qle; assumption.
Qed.

Lemma pdp_qmult_le_compat_r : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (a * c) (b * c).
Proof.
  intros a b c Hab Hc.
  apply Qle_to_QleT'.
  apply Qmult_le_compat_r; apply QleT'_to_Qle; assumption.
Qed.

Lemma pdp_qmult_le_compat_l : forall a b c : Q,
  QleT' a b -> QleT' 0 c -> QleT' (c * a) (c * b).
Proof.
  intros a b c Hab Hc.
  assert (Hr : QleT' (a * c) (b * c))
    by (apply pdp_qmult_le_compat_r; assumption).
  apply Qle_to_QleT'.
  apply (Qle_trans (c * a) (a * c)).
  - apply qeq_imp_qle. apply Qmult_comm.
  - apply (Qle_trans (a * c) (b * c)).
    + apply QleT'_to_Qle. exact Hr.
    + apply qeq_imp_qle. apply Qmult_comm.
Qed.

(* ===== block 1: closed form of (-1)^k + parity shield ===== *)

Lemma pdp_qpow_neg1_even : forall m : nat, q_pow (- 1)%Q (2 * m)%nat == 1%Q.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    change (q_pow (- 1)%Q (Datatypes.S (Datatypes.S (2 * m))))
      with ((- 1)%Q * q_pow (- 1)%Q (Datatypes.S (2 * m))).
    change (q_pow (- 1)%Q (Datatypes.S (2 * m)))
      with ((- 1)%Q * q_pow (- 1)%Q (2 * m)).
    rewrite IH. ring.
Qed.

Lemma pdp_qpow_neg1_odd : forall m : nat, q_pow (- 1)%Q (2 * m + 1)%nat == (- 1)%Q.
Proof.
  induction m as [| m IH].
  - reflexivity.
  - replace (2 * Datatypes.S m + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * m + 1)))%nat by lia.
    change (q_pow (- 1)%Q (Datatypes.S (Datatypes.S (2 * m + 1))))
      with ((- 1)%Q * q_pow (- 1)%Q (Datatypes.S (2 * m + 1))).
    change (q_pow (- 1)%Q (Datatypes.S (2 * m + 1)))
      with ((- 1)%Q * q_pow (- 1)%Q (2 * m + 1)).
    rewrite IH. ring.
Qed.

Lemma pdp_sgp_succ_T : forall k : nat,
  altsum_sgp k = true -> altsum_sgp (Datatypes.S k) = false.
Proof.
  intros k H.
  destruct (altsum_pbit k) eqn:Ep.
  - assert (Hk : k = (2 * altsum_phalf k)%nat)
      by exact (altsum_peven_eq k Ep).
    replace (Datatypes.S k)%nat with (2 * altsum_phalf k + 1)%nat by lia.
    apply altsum_sgp_2k1.
  - assert (Hk : k = (2 * altsum_phalf k + 1)%nat)
      by exact (altsum_podd_eq k Ep).
    rewrite Hk in H. rewrite altsum_sgp_2k1 in H. discriminate H.
Qed.

Lemma pdp_sgp_succ_F : forall k : nat,
  altsum_sgp k = false -> altsum_sgp (Datatypes.S k) = true.
Proof.
  intros k H.
  destruct (altsum_pbit k) eqn:Ep.
  - assert (Hk : k = (2 * altsum_phalf k)%nat)
      by exact (altsum_peven_eq k Ep).
    rewrite Hk in H. rewrite altsum_sgp_2k in H. discriminate H.
  - assert (Hk : k = (2 * altsum_phalf k + 1)%nat)
      by exact (altsum_podd_eq k Ep).
    replace (Datatypes.S k)%nat
      with (2 * Datatypes.S (altsum_phalf k))%nat by lia.
    apply altsum_sgp_2k.
Qed.

Lemma pdp_qpow_neg1_sgp : forall k : nat,
  q_pow (- 1)%Q k == (if altsum_sgp k then 1%Q else (- 1)%Q).
Proof.
  intro k. destruct (altsum_pbit k) eqn:Ep.
  - assert (Hk : k = (2 * altsum_phalf k)%nat)
      by exact (altsum_peven_eq k Ep).
    rewrite Hk. rewrite altsum_sgp_2k. apply pdp_qpow_neg1_even.
  - assert (Hk : k = (2 * altsum_phalf k + 1)%nat)
      by exact (altsum_podd_eq k Ep).
    rewrite Hk. rewrite altsum_sgp_2k1. apply pdp_qpow_neg1_odd.
Qed.

(* per-term sign absorption: (-1)^k * g k == if sgp k then g k else - g k *)
Lemma pdp_sign_term : forall (g : nat -> Q) (k : nat),
  q_pow (- 1)%Q k * g k ==
  (if altsum_sgp k then g k else Qopp (g k)).
Proof.
  intros g k. rewrite pdp_qpow_neg1_sgp.
  destruct (altsum_sgp k); cbv iota; ring.
Qed.

(* ===== block 2: coefficient positivity (unbounded; Nat.sub truncated values stay positive, same as the PC precedent) ===== *)

Lemma pdp_coeff_pos_any : forall n k : nat, QltT 0 (pade_coeff n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold pade_coeff. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply q_fact_pos.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
Qed.

(* ===== block 3: sum-shape bridge (head folding + range extension + altsum_acc alignment) ===== *)

Lemma pdp_sum_head : forall (f : nat -> Q) (m : nat),
  sum_upto (Datatypes.S m) f ==
  f 0%nat + sum_upto m (fun j : nat => f (Datatypes.S j)%nat).
Proof.
  intros f. induction m as [| m IH].
  - change (sum_upto (Datatypes.S 0%nat) f) with (0%Q + f 0%nat).
    change (sum_upto 0%nat (fun j : nat => f (Datatypes.S j)%nat)) with 0%Q.
    ring.
  - change (sum_upto (Datatypes.S (Datatypes.S m)) f)
      with (sum_upto (Datatypes.S m) f + f (Datatypes.S m)%nat).
    rewrite IH.
    change (sum_upto (Datatypes.S m) (fun j : nat => f (Datatypes.S j)%nat))
      with (sum_upto m (fun j : nat => f (Datatypes.S j)%nat)
            + f (Datatypes.S m)%nat).
    ring.
Qed.

Lemma pdp_sum_upto_ext_range : forall (m : nat) (f g : nat -> Q),
  (forall k : nat, (k < m)%nat -> f k == g k) ->
  sum_upto m f == sum_upto m g.
Proof.
  intros m f g H. induction m as [| m IH].
  - reflexivity.
  - assert (IH' : sum_upto m f == sum_upto m g).
    { apply IH. intros k Hk. apply H. lia. }
    change (sum_upto (Datatypes.S m) f)
      with (sum_upto m f + f m%nat).
    change (sum_upto (Datatypes.S m) g)
      with (sum_upto m g + g m%nat).
    rewrite IH'.
    apply altsum_qplus_eq_compat.
    + reflexivity.
    + apply H. lia.
Qed.

(* term-by-term alignment bridge between altsum_acc (sign-accumulator recursion)
   and sum_upto: with start index k and first sign sg == sgp k, the two sums agree term by term. *)
Lemma pdp_acc_sum : forall (g : nat -> Q) (n k : nat) (sg : bool),
  sg = altsum_sgp k ->
  altsum_acc sg g k n ==
  sum_upto n (fun j : nat =>
    (if altsum_sgp (k + j)%nat then g (k + j)%nat else Qopp (g (k + j)%nat))).
Proof.
  intros g n. induction n as [| m IH]; intros k sg Esg.
  - rewrite altsum_acc_0_eq. reflexivity.
  - destruct sg.
    + assert (Esk : altsum_sgp (Datatypes.S k) = false).
      { apply pdp_sgp_succ_T. symmetry. exact Esg. }
      rewrite (altsum_acc_T g k m).
      rewrite (IH (Datatypes.S k) false (eq_sym Esk)).
      rewrite pdp_sum_head. cbv beta.
      assert (E0 : (if altsum_sgp (k + 0)%nat
                    then g (k + 0)%nat
                    else Qopp (g (k + 0)%nat)) == g k).
      { replace (k + 0)%nat with k%nat by lia.
        rewrite <- Esg. reflexivity. }
      rewrite E0.
      apply (Qeq_trans (g k
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (Datatypes.S k + j)%nat
             then g (Datatypes.S k + j)%nat
             else Qopp (g (Datatypes.S k + j)%nat))))
        (g k
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (k + Datatypes.S j)%nat
             then g (k + Datatypes.S j)%nat
             else Qopp (g (k + Datatypes.S j)%nat))))).
      * apply altsum_qplus_eq_compat.
        -- reflexivity.
        -- apply sum_upto_ext. intro j. cbv beta.
           replace (Datatypes.S k + j)%nat
             with (k + Datatypes.S j)%nat by lia.
           reflexivity.
      * reflexivity.
    + assert (Esk : altsum_sgp (Datatypes.S k) = true).
      { apply pdp_sgp_succ_F. symmetry. exact Esg. }
      rewrite (altsum_acc_F g k m).
      rewrite (IH (Datatypes.S k) true (eq_sym Esk)).
      rewrite pdp_sum_head. cbv beta.
      assert (E0 : (if altsum_sgp (k + 0)%nat
                    then g (k + 0)%nat
                    else Qopp (g (k + 0)%nat)) == Qopp (g k)).
      { replace (k + 0)%nat with k%nat by lia.
        rewrite <- Esg. reflexivity. }
      rewrite E0.
      apply (Qeq_trans (Qopp (g k)
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (Datatypes.S k + j)%nat
             then g (Datatypes.S k + j)%nat
             else Qopp (g (Datatypes.S k + j)%nat))))
        (Qopp (g k)
        + sum_upto m (fun j : nat =>
            (if altsum_sgp (k + Datatypes.S j)%nat
             then g (k + Datatypes.S j)%nat
             else Qopp (g (k + Datatypes.S j)%nat))))).
      * apply altsum_qplus_eq_compat.
        -- reflexivity.
        -- apply sum_upto_ext. intro j. cbv beta.
           replace (Datatypes.S k + j)%nat
             with (k + Datatypes.S j)%nat by lia.
           reflexivity.
      * reflexivity.
Qed.

Lemma pdp_altsum_sum : forall (g : nat -> Q) (n : nat),
  altsum g (Datatypes.S n) ==
  sum_upto (Datatypes.S n)
    (fun j : nat => (if altsum_sgp j then g j else Qopp (g j))).
Proof.
  intros g n. unfold altsum.
  rewrite (pdp_acc_sum g (Datatypes.S n) 0%nat true).
  - apply sum_upto_ext. intro j. cbv beta.
    replace (0 + j)%nat with j%nat by lia. reflexivity.
  - reflexivity.
Qed.

End PadeDenPosQ.
