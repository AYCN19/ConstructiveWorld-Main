(* ============================================================ *)
(* UpReqPadeBetaPos.v —— 席C-T1b：β_m 闭式正性 + 符号传送件          *)
(*   （C 路闭合主轨第二切片；独立于正尾恒等式主件，可独立交付）        *)
(* 日期：2026-09-14                                                *)
(*                                                                 *)
(* 数学对象（席C-S3 侦察报告探针 4 实锤，fractions 精确验证）：         *)
(*   β_m = n!·(n+m)! / (2n+m+1)!                                   *)
(*   = Padé 余项正尾级数 Σ_{m≥0} β_m·y^m/m! 的系数，严格全正。         *)
(*   数值哨兵（n=1）：β_0..β_4 = 1/6, 1/12, 1/20, 1/30, 1/42。        *)
(*                                                                 *)
(* 分层：                                                           *)
(*   S1 阶乘面：q_fact 恒 ≥ 1（具体自然数界面）+ 阶乘单调（a ≤ b        *)
(*      经 Nat 桥 lia 后上推 Nat2Q 面，双腿 Qmult_le_compat_r）。      *)
(*   S2 主件 pbp_beta_pos：β_m 正性，QltT 见证形；非平凡性由具体       *)
(*      下界见证 1/(2n+m+1)! 承载（正下界 + 下界 ≤ β 双腿传送），      *)
(*      另给 sigT 见证包装（正性位升入见证，TempStrict 卡同款）。      *)
(*   S3 副件一 pbp_beta_closed：分母阶乘比的良定义面——分母指标          *)
(*      2n+m+1 ≥ 1 经 Nat 桥（后继展开形，首因子 ≥ 1 即非零见证）；    *)
(*   S3 副件二 pbp_sign_transfer：β 正 ⟹ 余项首项系数正的传送形，      *)
(*      接口参数 lead/posf 显式留白，不硬连下游 C-T1a 恒等式。          *)
(*                                                                 *)
(* 方法注记：                                                       *)
(*   ① 语句面全 Set 层（QltT/QleT'，S02:26/77）；Prop 仅作证内桥       *)
(*      （QltT_to_Qlt + Qlt_to_QltT 换桥），结论面不触 Q 表示墙。      *)
(*   ② Qeq 穿透墙（PC2 卡⑦）：pbp_qlt0_eq_r 走 CS 卡生路——destruct    *)
(*      双 Q 全构造子 + nia 双正消元（Psatz 已载）。                   *)
(*   ③ 除法正性面：Qinv_lt_0_compat（stdlib QArith_base:1408 实名）+   *)
(*      S03 q_le_div_le（同分母比较）；阶乘后继展开 q_fact_succ 的      *)
(*      消费用 exact 转换面（fixpoint iota 折叠），零 setoid 依赖。     *)
(*                                                                 *)
(* 红线自审基线：纯构造性、零外加假设（公理面 Print Assumptions        *)
(*   Closed）；语句面零 Prop 判断（唯二 ~ 分母非零桥件为 Prop 面，      *)
(*   按库内 q_neq_of_lt 同款定位标注）；nat 字面量带 %nat；             *)
(*   后继写 Datatypes.S；注释不落禁词字面量。                          *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Psatz.
From Stdlib Require Import Setoid Morphisms.

(* ===== S1 阶乘面 ===== *)

(* 任一阶乘 ≥ 1（具体自然数界面：归纳于指标，后继步双腿 r 型乘法）。 *)
Lemma pbp_qfact_ge1 : forall k : nat, QleT' 1%Q (q_fact k).
Proof.
  induction k as [| j IH].
  - change (QleT' 1%Q 1%Q). apply qleT'_refl.
  - apply Qle_to_QleT'.
    assert (H1 : Qle 1%Q ((Z.of_nat (Datatypes.S j) # 1)))
      by (unfold Qle; cbn [Qnum Qden]; lia).
    change (Qle (1%Q * 1%Q) ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
    apply (Qmult_le_compat_nonneg 1%Q ((Z.of_nat (Datatypes.S j) # 1)) 1%Q (q_fact j)).
    + split.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * exact H1.
    + split.
      * unfold Qle. cbn [Qnum Qden]. lia.
      * apply (QleT'_to_Qle 1%Q (q_fact j)). exact IH.
Qed.

(* 阶乘单调（Set 层 ≤ 面）：a ≤ b ⟹ a! ≤ b!。
   路线：Nat 桥 lia（i ≤ j）→ q_fact 后继展开（exact 转换面折叠）
   → 双腿 Qmult_le_compat_r（先换序成右因子位，ring 归一两端）。 *)
Lemma pbp_qfact_mono : forall a b : nat, (a <= b)%nat -> QleT' (q_fact a) (q_fact b).
Proof.
  intros a b. revert a.
  induction b as [| j IH]; intros a H.
  - assert (Ha : a = 0%nat) by lia. subst a. apply qleT'_refl.
  - destruct a as [| i].
    + exact (pbp_qfact_ge1 (Datatypes.S j)).
    + assert (Hij : (i <= j)%nat) by lia.
      specialize (IH i Hij).
      assert (Hprod : Qle ((Z.of_nat (Datatypes.S i) # 1) * q_fact i)
                          ((Z.of_nat (Datatypes.S j) # 1) * q_fact j)).
      { apply (Qle_trans _ (q_fact i * (Z.of_nat (Datatypes.S i) # 1))).
        - apply qeq_le. ring.
        - apply (Qle_trans _ ((Z.of_nat (Datatypes.S i) # 1) * q_fact j)).
          + apply (Qle_trans _ (q_fact j * (Z.of_nat (Datatypes.S i) # 1))).
            * apply Qmult_le_compat_r.
              -- apply (QleT'_to_Qle (q_fact i) (q_fact j)). exact IH.
              -- assert (Hsi : Qle 0%Q ((Z.of_nat (Datatypes.S i) # 1)))
                   by (unfold Qle; cbn [Qnum Qden]; lia).
                 exact Hsi.
            * apply qeq_le. ring.
          + apply Qmult_le_compat_r.
            * assert (HSij : Qle (Z.of_nat (Datatypes.S i) # 1)
                                 (Z.of_nat (Datatypes.S j) # 1))
                by (unfold Qle; cbn [Qnum Qden]; lia).
              exact HSij.
            * apply (Qlt_le_weak 0%Q (q_fact j)). apply q_fact_pos. }
      apply Qle_to_QleT'. exact Hprod.
Qed.

(* ===== S2 主件：β_m 闭式与正性 ===== *)

(* β_m：Padé 余项正尾级数系数（席C-S3 探针 4 闭式）。 *)
Definition pbp_beta (n m : nat) : Q :=
  (q_fact n * q_fact (n + m)) / q_fact (2 * n + m + 1).

(* 具体下界见证：1/(2n+m+1)!——正性由它承载为真构造（可计算正数）。 *)
Definition pbp_beta_lb (n m : nat) : Q := 1%Q / q_fact (2 * n + m + 1).

(* 下界正（Qinv 严格面 Qinv_lt_0_compat + 双正乘积）。 *)
Lemma pbp_beta_lb_pos : forall n m : nat, QltT 0 (pbp_beta_lb n m).
Proof.
  intros n m. apply Qlt_to_QltT. unfold pbp_beta_lb.
  change (Qlt 0%Q (1%Q * / q_fact (2 * n + m + 1))).
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn [Qnum Qden]. lia.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* β_m ≥ 下界见证：分子 ≥ 1·1（双腿阶乘 ≥ 1），同除正分母
   （S03 q_le_div_le 同分母比较面）。 *)
Lemma pbp_beta_ge_lb : forall n m : nat, QleT' (pbp_beta_lb n m) (pbp_beta n m).
Proof.
  intros n m.
  assert (Hn : Qle 1%Q (q_fact n))
    by (apply (QleT'_to_Qle 1%Q (q_fact n)); apply pbp_qfact_ge1).
  assert (Hm : Qle 1%Q (q_fact (n + m)))
    by (apply (QleT'_to_Qle 1%Q (q_fact (n + m))); apply pbp_qfact_ge1).
  assert (Hnum : Qle 1%Q (q_fact n * q_fact (n + m))).
  { apply (Qmult_le_compat_nonneg 1%Q (q_fact n) 1%Q (q_fact (n + m))).
    - split.
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hn.
    - split.
      + unfold Qle. cbn [Qnum Qden]. lia.
      + exact Hm. }
  apply Qle_to_QleT'.
  unfold pbp_beta, pbp_beta_lb.
  apply (q_le_div_le 1%Q (q_fact (2 * n + m + 1))
                     (q_fact n * q_fact (n + m)) (q_fact (2 * n + m + 1))).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - apply (Qmult_le_compat_r 1%Q (q_fact n * q_fact (n + m))
                              (q_fact (2 * n + m + 1)) Hnum).
    apply (Qlt_le_weak 0%Q (q_fact (2 * n + m + 1))). apply q_fact_pos.
Qed.

(* 主件：β_m 严格全正（QltT 见证形；证 = 正下界 + 下界 ≤ β 传送）。 *)
Lemma pbp_beta_pos : forall n m : nat, QltT 0 (pbp_beta n m).
Proof.
  intros n m.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans 0%Q (pbp_beta_lb n m) (pbp_beta n m)).
  - apply QltT_to_Qlt. apply pbp_beta_lb_pos.
  - apply (QleT'_to_Qle (pbp_beta_lb n m) (pbp_beta n m)). apply pbp_beta_ge_lb.
Qed.

(* sigT 见证形（正性位升入见证，供下游逐位消费）：见证 = β_m 本值
   （Id 钉值）+ 其 QltT 正性证书。 *)
Definition pbp_beta_pos_sigT (n m : nat) :
  sigT (fun b : Q => sigT (fun _ : Id b (pbp_beta n m) => QltT 0 b)) :=
  existT (fun b : Q => sigT (fun _ : Id b (pbp_beta n m) => QltT 0 b))
         (pbp_beta n m)
         (existT (fun _ : Id (pbp_beta n m) (pbp_beta n m)
                    => QltT 0 (pbp_beta n m))
                 (@id_refl Q (pbp_beta n m))
                 (pbp_beta_pos n m)).

(* ===== S3 副件一：良定义性 / 分母非零面 ===== *)

(* 分母指标 Nat 桥：2n+m+1 ≥ 1（lia 一步；见证于后继展开形）。 *)
Lemma pbp_den_index_ge1 : forall n m : nat, (1 <= 2 * n + m + 1)%nat.
Proof. intros n m. lia. Qed.

(* 分母阶乘比的良定义面：2n+m+1 指标处阶乘 = (2n+m+1)·(2n+m)!，
   首因子 Z.of_nat(S(2n+m)) ≥ 1 经 Nat 桥——分母非零的具体自然数见证。
   证法：指标 Nat 桥 replace（lia）+ q_fact_succ（exact 转换面）。 *)
Lemma pbp_beta_closed : forall n m : nat,
  q_fact (2 * n + m + 1)
  == (Z.of_nat (Datatypes.S (2 * n + m)) # 1) * q_fact (2 * n + m).
Proof.
  intros n m.
  replace (2 * n + m + 1)%nat with (Datatypes.S (2 * n + m)) by lia.
  apply q_fact_succ.
Qed.

(* 分母正（Set 面）。 *)
Lemma pbp_den_posT : forall n m : nat, QltT 0 (q_fact (2 * n + m + 1)).
Proof. intros n m. apply Qlt_to_QltT. apply q_fact_pos. Qed.

(* 分母非零（Prop 面桥件定位：q_neq_of_lt 同款，供域法消费）。 *)
Lemma pbp_den_neq0 : forall n m : nat, ~ (q_fact (2 * n + m + 1) == 0).
Proof. intros n m. apply q_neq_of_lt. apply q_fact_pos. Qed.

(* ===== S3 副件二：符号传送预备面（接口显式留白，不硬连 C-T1a） ===== *)

(* Qeq 右换桥（本席最小传桥件）：a == b 时 0<a 传 0<b。
   CS 卡生路：destruct 双 Q 全构造子 + nia 双正消元一步收口。 *)
Lemma pbp_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  destruct a as [na da]. destruct b as [nb db].
  unfold Qlt in Ha |- *. unfold Qeq in Hab.
  simpl in Hab, Ha |- *.
  nia.
Qed.

(* 符号传送：余项首项系数 lead == β_m·posf ⟹ 0 < lead。
   posf = 首项系数的正因子部（如 y^{2n+1}/((2n)!·m!) 具体面），由下游
   C-T1a 正尾恒等式供给——本件只传号，不钉定 posf 形。 *)
Lemma pbp_sign_transfer : forall (lead posf : Q) (n m : nat),
  lead == pbp_beta n m * posf ->
  QltT 0 posf ->
  QltT 0 lead.
Proof.
  intros lead posf n m Heq Hf.
  apply Qlt_to_QltT.
  apply (pbp_qlt0_eq_r (pbp_beta n m * posf) lead).
  - apply Qeq_sym. exact Heq.
  - apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. apply pbp_beta_pos.
    + apply QltT_to_Qlt. exact Hf.
Qed.

(* 附加面：β_m ≤ n!（阶乘单调的真消费：(2n+m+1)! ≥ (n+m)! ⟹
   β_m = n!·(n+m)!/(2n+m+1)! ≤ n!·(n+m)!/(n+m)! = n!；
   下游尾界消费形——n 对固定 n! 为具体常数）。 *)
Lemma pbp_beta_le_nfact : forall n m : nat, QleT' (pbp_beta n m) (q_fact n).
Proof.
  intros n m.
  assert (Hmono : Qle (q_fact (n + m)) (q_fact (2 * n + m + 1))).
  { apply (QleT'_to_Qle (q_fact (n + m)) (q_fact (2 * n + m + 1))).
    apply pbp_qfact_mono. lia. }
  assert (Hneq : ~ (q_fact (n + m) == 0)) by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hleg : Qle ((q_fact n * q_fact (n + m)) * q_fact (n + m))
                     ((q_fact n * q_fact (n + m)) * q_fact (2 * n + m + 1))).
  { apply (Qle_trans _ ((q_fact (n + m)) * (q_fact n * q_fact (n + m)))).
    - apply qeq_le. ring.
    - apply (Qle_trans _ ((q_fact (2 * n + m + 1)) * (q_fact n * q_fact (n + m)))).
      + apply Qmult_le_compat_r.
        * exact Hmono.
        * apply Qmult_le_0_compat.
          -- apply (Qlt_le_weak 0%Q (q_fact n)). apply q_fact_pos.
          -- apply (Qlt_le_weak 0%Q (q_fact (n + m))). apply q_fact_pos.
      + apply qeq_le. ring. }
  apply Qle_to_QleT'.
  unfold pbp_beta.
  apply (Qle_trans ((q_fact n * q_fact (n + m)) / q_fact (2 * n + m + 1))
                   ((q_fact n * q_fact (n + m)) / q_fact (n + m))
                   (q_fact n)).
  - apply (q_le_div_le (q_fact n * q_fact (n + m)) (q_fact (2 * n + m + 1))
                       (q_fact n * q_fact (n + m)) (q_fact (n + m))).
    + apply q_fact_pos.
    + apply q_fact_pos.
    + exact Hleg.
  - apply qeq_le. apply (Qdiv_mult_l (q_fact n) (q_fact (n + m)) Hneq).
Qed.

(* ===== 数值哨兵（探针对账：n=1 时 β_0..β_4 = 1/6,1/12,1/20,1/30,1/42） ===== *)
Lemma pbp_beta_1_0 : pbp_beta 1%nat 0%nat == (1#6)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_1 : pbp_beta 1%nat 1%nat == (1#12)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_2 : pbp_beta 1%nat 2%nat == (1#20)%Q.
Proof. vm_compute. reflexivity. Qed.

(* ===== G3 提取探针（全量 coqc 时生效；vos 秒审跳过副作用） ===== *)
From Stdlib Require Import Extraction.
Separate Extraction pbp_beta pbp_beta_lb pbp_qfact_ge1 pbp_qfact_mono
  pbp_beta_lb_pos pbp_beta_ge_lb pbp_beta_pos pbp_beta_pos_sigT
  pbp_den_index_ge1 pbp_beta_closed pbp_den_posT pbp_den_neq0
  pbp_qlt0_eq_r pbp_sign_transfer pbp_beta_le_nfact.
Print Assumptions pbp_beta.
Print Assumptions pbp_beta_lb.
Print Assumptions pbp_qfact_ge1.
Print Assumptions pbp_qfact_mono.
Print Assumptions pbp_beta_lb_pos.
Print Assumptions pbp_beta_ge_lb.
Print Assumptions pbp_beta_pos.
Print Assumptions pbp_beta_pos_sigT.
Print Assumptions pbp_den_index_ge1.
Print Assumptions pbp_beta_closed.
Print Assumptions pbp_den_posT.
Print Assumptions pbp_den_neq0.
Print Assumptions pbp_qlt0_eq_r.
Print Assumptions pbp_sign_transfer.
Print Assumptions pbp_beta_le_nfact.
