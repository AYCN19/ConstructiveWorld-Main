(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqPadeDenPos.v *)
(* *)
(* 目的： 路径 C 通用 n 的 Padé 分母正性。 *)
(* 主件： pdp_den_pos 通用段与 pdp_sign_term 符号项定律。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqPadeExp、UpReqPadeQLeg。 *)
(* 备注： 显式假设对称申报（禁强造），见正文；符号交替经 q 的负一幂奇偶定律承担。 *)
(* ============================================================ *)

(* ============================================================ *)
(*                  （den_pos 通项化：0 <= x <= 1 ⟹ 分母非负）       *)
(*                                                                 *)
(*   pds_den0_pos / pds_den1_pos）。本件把分母正性通项化：           *)
(*     pdp_den_pos : forall n x, QleT 0 x -> QleT x 1 ->            *)
(*                              QleT' 0 (pade_den n x)              *)
(*   结论面取 QleT'——PC2 表示墙裁决：bool 反映形才可一般构造，        *)

(*                                                                 *)
(* 数学路线：pade_den n x = sum_upto (S n)((-1)^k · c_k x^k)。       *)
(*   记 t_k = c_k x^k。于 0 <= x <= 1：                              *)
(*     系数比 c_k / c_{k+1} = (2n-k)(k+1)/(n-k) >= 1（k < n），      *)
(*   故 c_{k+1} <= c_k；两端乘非负 x 幂得 t_{k+1} <= t_k（加法装配，  *)
(*   零除零消元）。喂 PC2 引擎 altsum_nonneg_leT（非负递减有限      *)
(*   交错和非负）即闭合；n=0/n=1 统一覆盖（CS 两特例为其手工实例）。  *)
(*                                                                 *)
(* 工程注记：                                                        *)
(*   ① nat 字面量全带 %nat；后继写 Datatypes.S（S01.S 遮蔽坑）。      *)
(*   ② Qeq 方程不 rewrite 进 Id-of-bool 语句面目标——Qeq 桥经        *)
(*      qeq_imp_qle / qeq_leT' / qleT'_trans 组装（PC2 卡⑤生路）。   *)
(*   ③ 系数比恒等式用 field 完成：分母非零副目标 q_neq_of_lt +       *)
(*      q_fact_pos / Z 层 lia；Z 不等式 AA12 肢化（pql_nat_ratio_mono， *)
(*      乘法单调显式装配，零 Psatz）。                                *)
(*   ④ 语句面全 Set 层（QltT/QleT/QleT'）；Prop 序仅证内转译。        *)
(*                                                                 *)
(* 显式假设（对称，禁强造）：                                            *)
(*   a. 严格正版 QltT 0：引擎出口 altsum_pos_strict 需首对严格       *)
(*      t_1 < t_0，即 x < 1/c_1 = 2/(2n-1)，n >= 2 时比 x < 1 细，   *)
(*   b. x ∈ (1,2) 段：系数比极小值实为 2（k=0 处），衰减对 x <= 2     *)
(*      成立（分母真零点在 x = 2），但 x ∈ (1,2] 段递减装配需比式     *)
(*      消元（乘 Qinv 正因子），待下轮。                              *)
(*   c. 误差积分表示：构造性积分基建缺位（PC 件已登记，同题显式假设）。    *)
(* ============================================================ *)

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
Require Import UpReqPadeExp UpReqAltSumPos.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeDenPosQ.

(* ===== 件 0：语句面乘法单调（全 Set 层面；Prop 序仅证内转译） ===== *)

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

(* ===== 件 1：(-1)^k 闭形 + 奇偶盾 ===== *)

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

(* 逐项符号吸收：(-1)^k · g k == if sgp k then g k else - g k *)
Lemma pdp_sign_term : forall (g : nat -> Q) (k : nat),
  q_pow (- 1)%Q k * g k ==
  (if altsum_sgp k then g k else Qopp (g k)).
Proof.
  intros g k. rewrite pdp_qpow_neg1_sgp.
  destruct (altsum_sgp k); cbv iota; ring.
Qed.

(* ===== 件 2：系数正性（无界——Nat.sub 截断值仍正，PC 先例同款） ===== *)

Lemma pdp_coeff_pos_any : forall n k : nat, QltT 0 (pade_coeff n k).
Proof.
  intros n k. apply Qlt_to_QltT. unfold pade_coeff. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply q_fact_pos.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
Qed.

(* ===== 件 3：和形桥（头折叠 + 范围外延 + altsum_acc 对齐） ===== *)

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

(* altsum_acc（符号累加器递归）与 sum_upto 的逐项对齐桥：
   起指标 k、首项符号 sg == sgp k 时，两和逐项相等。 *)
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

(* ===== 件 4：指标包装（引擎假设须全指标；尾段清零） ===== *)

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

(* ===== 件 5：系数比与相邻递减（S1 引擎） =====

   核心代数：c_k / c_{k+1} = (2n-k)(k+1)/(n-k) >= 1（k < n）
   （Z 层：(n-k) <= (2n-k)(k+1)，AA12 肢 pql_nat_ratio_mono）。
   系数比恒等式 field 完成。 *)

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

(* ===== 件 6：den 桥 + S2 主件 ===== *)

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

(* S2 主件：0 <= x <= 1 ⟹ 0 <= 分母（通用 n，含 n=0/n=1 特例） *)
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

(* ===== S3 加分：n=2/n=3 实例 vm_compute 端到端核对 ===== *)
(* den_2(x) = 1 - x/2 + x^2/12；den_3(x) = 1 - x/2 + x^2/10 - x^3/120 *)

Lemma pdp_den2_three_fifths : QltT 0 (pade_den 2 (3#5)).
Proof. vm_compute. reflexivity. Qed.

Lemma pdp_den2_one : QleT' 0 (pade_den 2 1%Q).
Proof. vm_compute. reflexivity. Qed.

Lemma pdp_den3_one : QleT' 0 (pade_den 3 1%Q).
Proof. vm_compute. reflexivity. Qed.

End PadeDenPosQ.
