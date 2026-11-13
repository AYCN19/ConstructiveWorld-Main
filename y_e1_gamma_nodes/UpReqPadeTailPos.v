(* ==========================================================================)
   UpReqPadeTailPos —— ptp_beta / ptp_beta_prefix / ptp_sum_S 语句面；同域语句面
   使命：本件形式化ptp_beta / ptp_beta_prefix / ptp_sum_S 语句面。
   本件并载：C-T1b：β_m 闭式正性 + 符号传送件；路径 C 分母正性的 (1,2) 段 使命：本件形式化 Pade 逼近分母在 x ∈ (1,2) 上的正性：Q_n(x) ≥ 0 且；qtr_qlt_sub / qtr_div2_lt / qtr_div2_ltT 语句面。
   依赖：S01_BaseRing, S02_CauchyComplete, S03_QExp, UpReqPadeQLeg, QArith.QArith, Arith.Arith, Lia, Setoid
     Morphisms, Extraction, UpReqPadeExp, S04_RealExpLogConv, S05_AlignmentGRPO, S06_DiffSamplingGibbs, S07_RealSetoidExpLog, S08_RealMainlineDPO,
     S09_EntropyReal, S10_KVQuantTrig, S11_TP3B5, S12_B5RecycleSF, S13_NLiveAudit, S14_B5BatchBlock, S15_TailFEPUp, UpReqPadeDenPos,
     UpReqPadeSign, UpReqAltSumPos, UpReqQExpTail, UpReqPadeLower, QArith.Qabs。
   构造性：零公理、零承认式语句；语句面 Set 层承载，Print Assumptions 全 Closed。
   编译配方：Rocq 9.1 coqc -native-compiler no -Q . ""，cpu_guard 包裹限载。
   ========================================================================== *)

(* ============================ §1 C-T1b：β_m 闭式正性 + 符号传送件 ============================ *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.
From Stdlib Require Import Setoid Morphisms.

(* ===== S1 阶乘面 ===== *)

(* 任一阶乘 ≥ 1（具体自然数界面：归纳于指标，后继步双肢 r 型乘法）。 *)
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
   → 双肢 Qmult_le_compat_r（先换序成右因子位，ring 归一两端）。 *)
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

(* β_m：Padé 余项正尾级数系数（C-S3 检验 4 闭式）。 *)
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

(* β_m ≥ 下界见证：分子 ≥ 1·1（双肢阶乘 ≥ 1），同除正分母
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

(* sigT 见证形（正性位升入见证，供下游逐位使用）：见证 = β_m 本值
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

(* 分母非零（Prop 面桥接引理定位：q_neq_of_lt 同款，供域法使用）。 *)
Lemma pbp_den_neq0 : forall n m : nat, ~ (q_fact (2 * n + m + 1) == 0).
Proof. intros n m. apply q_neq_of_lt. apply q_fact_pos. Qed.

(* ===== S3 副件二：符号传送预备面（接口显式留白，不硬连 C-T1a） ===== *)

(* Qeq 右换桥（本件最小传桥接引理）：a == b 时 0<a 传 0<b。
   AA12 肢化：一跳 UpReqPadeQLeg.pql_qlt0_eq_r（语句面不变，
   原件 Require Psatz 的环境闭包公理三件随之不引入）。 *)
Lemma pbp_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
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

(* 附加面：β_m ≤ n!（阶乘单调的真使用：(2n+m+1)! ≥ (n+m)! ⟹
   β_m = n!·(n+m)!/(2n+m+1)! ≤ n!·(n+m)!/(n+m)! = n!；
   下游尾界使用形——n 对固定 n! 为具体常数）。 *)
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

(* ===== 数值数值锚（检验核对：n=1 时 β_0..β_4 = 1/6,1/12,1/20,1/30,1/42） ===== *)
Lemma pbp_beta_1_0 : pbp_beta 1%nat 0%nat == (1#6)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_1 : pbp_beta 1%nat 1%nat == (1#12)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pbp_beta_1_2 : pbp_beta 1%nat 2%nat == (1#20)%Q.
Proof. vm_compute. reflexivity. Qed.


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

Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqPadeExp.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

(* ===== 定义面 ===== *)

(* β_m = n!·(n+m)!/(2n+m+1)!——S3 检验 beta_term 同式，全正闭式 *)
Definition ptp_beta (n m : nat) : Q :=
  q_fact n * q_fact (n + m) / q_fact (2 * n + m + 1).

(* 带符号正尾前缀：Σ_{m=0}^{M} β_m·y^{2n+1+m}/m!（幂次在项内） *)
Definition ptp_beta_prefix (n M : nat) (y : Q) : Q :=
  sum_upto (Datatypes.S M)
    (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m)).

(* ===== 小引擎 ===== *)

(* sum_upto 尾部展开：定义性（sum_upto (S K) f = sum_upto K f + f K） *)
Lemma ptp_sum_S : forall (K : nat) (f : nat -> Q),
  sum_upto (Datatypes.S K) f == sum_upto K f + f K.
Proof. intro K. intro f. exact (Qeq_refl (sum_upto (Datatypes.S K) f)). Qed.

(* 前缀步进：prefix (S M) = prefix M + f (S M) *)
Lemma ptp_prefix_S : forall (n M : nat) (y : Q),
  ptp_beta_prefix n (Datatypes.S M) y ==
  ptp_beta_prefix n M y +
  (ptp_beta n (Datatypes.S M) / q_fact (Datatypes.S M)
     * q_pow y (2 * n + 1 + Datatypes.S M)).
Proof.
  intros n M y. unfold ptp_beta_prefix.
  rewrite (ptp_sum_S (Datatypes.S M)
             (fun m => ptp_beta n m / q_fact m * q_pow y (2 * n + 1 + m))).
  reflexivity.
Qed.

(* Q₁(y) = 1 − y/2、P₁(y) = 1 + y/2（系数闭式展开） *)
Lemma ptp_den1 : forall y : Q, pade_den 1 y == 1 + - (1#2) * y.
Proof.
  intro y. unfold pade_den, pade_coeff. cbn. field.
Qed.

Lemma ptp_num1 : forall y : Q, pade_num 1 y == 1 + (1#2) * y.
Proof.
  intro y. unfold pade_num, pade_coeff. cbn. field.
Qed.

(* ===== 正性件（全称 n,m，Set 层 QltT 出口） ===== *)

Theorem ptp_beta_pos : forall (n m : nat), QltT 0 (ptp_beta n m).
Proof.
  intros n m. apply Qlt_to_QltT.
  unfold ptp_beta. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ===== β 标记族（S3 检验 fractions 精确对照） ===== *)

Lemma ptp_beta_n1_0 : ptp_beta 1 0%nat == (1#6).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_1 : ptp_beta 1 1%nat == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_2 : ptp_beta 1 2%nat == (1#20).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_3 : ptp_beta 1 3%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n1_4 : ptp_beta 1 4%nat == (1#42).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_0 : ptp_beta 2 0%nat == (1#30).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_1 : ptp_beta 2 1%nat == (1#60).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_2 : ptp_beta 2 2%nat == (1#105).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* 首项闭式实例：(n!)^2/((2n)!(2n+1)!)——n=1 得 1/12（y^3 位首系数
   带 (−1)^1 符号），n=2 得 1/720（y^5 位首系数偶号正），与修正令②对照 *)
Lemma ptp_beta_n1_first : ptp_beta 1 0%nat / q_fact 2 == (1#12).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_beta_n2_first : ptp_beta 2 0%nat / q_fact 4 == (1#720).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== 保底件一：n=1 截断多项式恒等式（全称 y） =====
   系数 −1/12, −1/24 与全级数 −β_m/(2!·m!) 精确对照（m=0,1），
   y^5 项 −1/48 为 exp_partial 4 的截断窄条。 *)
Lemma ptp_n1_poly : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12)*q_pow y 3 + (1#24)*q_pow y 4 + (1#48)*q_pow y 5).
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== 保底件二：n=2 偶号正尾实例（S1 g2_poly 同款，全称 y） =====
   十个 Padé 匹配条件（y^0..y^4 系数全零）由右端无低次项读出；
   y^7 系数恰零（右端无 y^7 项）；首项 y^5/720 = (2!)^2/(4!·5!)。 *)
Lemma ptp_n2_poly : forall y : Q,
  exp_partial 6 y * pade_den 2 y - pade_num 2 y
  == (1#720)*q_pow y 5 + (1#1440)*q_pow y 6 + (1#8640)*q_pow y 8.
Proof.
  intro y.
  unfold exp_partial, pade_den, pade_num, pade_coeff.
  cbn. field.
Qed.

(* ===== 数值标记（y = 1/2 核对；vm_compute + Qeq 交叉乘 lia） ===== *)

Lemma ptp_sentinel_n1_half :
  exp_partial 4 (1#2) * pade_den 1 (1#2) - pade_num 1 (1#2) == - (7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_sentinel_n2_half :
  exp_partial 6 (1#2) * pade_den 2 (1#2) - pade_num 2 (1#2)
  == (1#720)*(1#32) + (1#1440)*(1#64) + (1#8640)*(1#256).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

(* ===== 审计与提取 ===== *)

Print Assumptions ptp_beta_pos.
Print Assumptions ptp_n1_poly.
Print Assumptions ptp_n2_poly.

From Stdlib Require Import Extraction.
Separate Extraction ptp_beta_pos ptp_beta ptp_beta_prefix
  ptp_n1_poly ptp_n2_poly.

(* ============================================================ *)

(*   ptp_tail_series——按 T1a 报告④配方：归纳不变式                  *)
(*     Φ_k : exp_partial (3+k) y·Q₁(y) − P₁(y)                    *)
(*       == −((1#2)·prefix_1 k y) − ((1#2)·y^{S(3+k)}/(3+k)!)     *)
(*   两处 (−1#2) 即 (−1)^1 符号面显式（奇 n 负尾）；偶 n 对偶形由    *)
(*   ptp_n2_poly 正号实例承贴。N=3/N=4 闭式与 ptp_n1_poly 逐系数    *)
(*   对照（ptp_series_n1_N3/N4 + recheck + y=1/2 数值核对）。       *)

(*   merge 乘法形（纯变元 field）→ ptp_div_clear_r 交叉乘消去       *)
(*   （Qmult_inj_r + q_fact_pos 正性）→ 清分母后 field 完成。       *)
(* ============================================================ *)

(* —— 0. 纯变元小引擎（ring/field 只见自由变元与字面常量）—— *)

Lemma ptp_AC_swap_m : forall a b c : Q, a + b - c == a - c + b.
Proof. intros a b c. unfold Qminus. ring. Qed.

Lemma ptp_opp_plus : forall a b : Q, - (a + b) == - a + - b.
Proof. intros a b. unfold Qminus. ring. Qed.

Lemma ptp_opp_mul_move : forall a b : Q, (- a) * b == - (a * b).
Proof. intros a b. ring. Qed.

Lemma ptp_G_alg : forall a b c p : Q, (a + b) + c == (a + (- p)) + ((b + p) + c).
Proof. intros a b c p. ring. Qed.

Lemma ptp_Qmake_plus : forall a b : Z, (a + b) # 1 == (a # 1) + (b # 1).
Proof. intros a b. unfold Qeq. simpl. lia. Qed.

(* —— 1. 分母消去（Qmult_inj_r 型交叉乘，正性在场）—— *)

Lemma ptp_div_clear_r : forall x d D E : Q,
  ~ (d == 0) -> D == E * d -> x / d * D == x * E.
Proof.
  intros x d D E Hd HDE. unfold Qdiv. rewrite HDE.
  rewrite (Qmult_comm E d).
  rewrite <- (Qmult_assoc x (Qinv d) (d * E)).
  rewrite (Qmult_assoc (Qinv d) d E).
  rewrite (Qmult_comm (Qinv d) d). rewrite (Qmult_inv_r d Hd).
  rewrite Qmult_1_l. reflexivity.
Qed.

(* —— 2. merge 乘法形（T1a 报告④骨架照抄；q_fact 链 lia 归一）—— *)

Lemma ptp_n1_merge : forall m : nat,
  q_fact 1 * q_fact (Datatypes.S m) * q_fact (Datatypes.S (Datatypes.S m))
  == (q_fact (Datatypes.S (Datatypes.S (Datatypes.S m)))
      - (1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S m))) * q_fact m.
Proof.
  intro m.
  rewrite (q_fact_succ (Datatypes.S (Datatypes.S m))).
  rewrite (q_fact_succ (Datatypes.S m)).
  rewrite (q_fact_succ m).
  rewrite (q_fact_succ 0%nat).
  cbn [q_fact].
  replace (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S m))))
    with (Z.of_nat m + 3)%Z by lia.
  replace (Z.of_nat (Datatypes.S (Datatypes.S m)))
    with (Z.of_nat m + 2)%Z by lia.
  replace (Z.of_nat (Datatypes.S m)) with (Z.of_nat m + 1)%Z by lia.
  replace (Z.of_nat 1) with 1%Z by lia.
  rewrite (ptp_Qmake_plus (Z.of_nat m) 3%Z).
  rewrite (ptp_Qmake_plus (Z.of_nat m) 2%Z).
  rewrite (ptp_Qmake_plus (Z.of_nat m) 1%Z).
  field.
Qed.

(* —— 3. 双侧步进展开（rewrite-only，不触原子分母完成）—— *)

Definition ptp_F (k : nat) (y : Q) : Q :=
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y.

Definition ptp_G (k : nat) (y : Q) : Q :=
  - ((1#2) * ptp_beta_prefix 1 k y)
    - (1#2) * (q_pow y (4 + k) / q_fact (3 + k)).

Lemma ptp_exp_S : forall (n : nat) (y : Q),
  exp_partial (Datatypes.S n) y
  == exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n).
Proof. intros n y. exact (Qeq_refl (exp_partial (Datatypes.S n) y)). Qed.

Lemma ptp_G_eq : forall k y,
  ptp_G k y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))).
Proof.
  intros k y. unfold ptp_G, Qminus.
  replace (4%nat + k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  reflexivity.
Qed.

Lemma ptp_F_step : forall k y,
  ptp_F (Datatypes.S k) y
  == ptp_F k y
     + ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
        * (1 + - (1#2) * y)).
Proof.
  intros k y. unfold ptp_F.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite ptp_exp_S. rewrite ptp_den1. rewrite ptp_num1.
  rewrite (Qmult_plus_distr_l (exp_partial (3 + k) y)
             (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
             (1 + - (1#2) * y)).
  rewrite (ptp_AC_swap_m
             (exp_partial (3 + k) y * (1 + - (1#2) * y))
             ((q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
              * (1 + - (1#2) * y))
             (1 + (1#2) * y)).
  reflexivity.
Qed.

Lemma ptp_G_step : forall k y,
  ptp_G (Datatypes.S k) y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     + - ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))
     + (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                    * q_pow y (Datatypes.S (3 + k))))
        + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))
        + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                      / q_fact (Datatypes.S (3 + k))))).
Proof.
  intros k y. unfold ptp_G.
  replace (4%nat + Datatypes.S k)%nat
    with (Datatypes.S (Datatypes.S (3%nat + k)%nat)) by lia.
  replace (3%nat + Datatypes.S k)%nat with (Datatypes.S (3 + k)%nat) by lia.
  rewrite ptp_prefix_S.
  replace (2%nat * 1%nat + 1%nat + Datatypes.S k)%nat with (Datatypes.S (3%nat + k)%nat) by lia.
  rewrite (q_pow_succ y (Datatypes.S (3 + k))).
  rewrite (Qmult_plus_distr_r (1#2) (ptp_beta_prefix 1 k y)
             (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
              * q_pow y (Datatypes.S (3 + k)))).
  rewrite (ptp_opp_plus ((1#2) * ptp_beta_prefix 1 k y)
             ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                       * q_pow y (Datatypes.S (3 + k))))).
  rewrite (ptp_G_alg (- ((1#2) * ptp_beta_prefix 1 k y))
             (- ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                          * q_pow y (Datatypes.S (3 + k)))))
             (- ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                          / q_fact (Datatypes.S (3 + k)))))
             ((1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)))).
  reflexivity.
Qed.

(* —— 4. 清分母核心：归纳步差恒等式（ΔL == ΔR）——
   路线：Qmult_inj_r 两侧同乘 D = 2·u3·v4·w（正性 q_fact_pos 在场）
   → ptp_div_clear_r 逐商消去 → merge 乘法形回代 → field 完成。 *)

Lemma ptp_step_core : forall k y,
  (q_pow y (Datatypes.S (3 + k)) / q_fact (Datatypes.S (3 + k)))
    * (1 + - (1#2) * y)
  == - ((1#2) * (ptp_beta 1 (Datatypes.S k) / q_fact (Datatypes.S k)
                 * q_pow y (Datatypes.S (3 + k))))
     + (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k))
     + - ((1#2) * (y * q_pow y (Datatypes.S (3 + k))
                   / q_fact (Datatypes.S (3 + k)))).
Proof.
  intros k y.
  unfold ptp_beta. cbn [Nat.add Nat.mul].
  replace (k%nat + 1%nat)%nat with (Datatypes.S k) by lia.
  remember (q_pow y (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
    as Aeq eqn:HA.
  assert (Hw0 : ~ (q_fact (Datatypes.S k) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hu0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (Hv0 : ~ (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))) == 0))
    by (apply q_neq_of_lt; apply q_fact_pos).
  assert (HD : ~ (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                   * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                       (Datatypes.S k)))))
                  * q_fact (Datatypes.S k) == 0)).
  { apply q_neq_of_lt. apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply Qmult_lt_0_compat; [exact Q2_pos | apply q_fact_pos].
      + apply q_fact_pos.
    - apply q_fact_pos. }
  apply (proj1 (Qmult_inj_r _ _ _ HD)).
  (* LHS 消去 *)
  rewrite <- (Qmult_assoc (Aeq / q_fact (Datatypes.S (Datatypes.S
              (Datatypes.S (Datatypes.S k)))))
              (1 + - (1#2) * y)
              (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
               * q_fact (Datatypes.S k))).
  assert (HcL : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * ((1 + - (1#2) * y)
                   * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))
                       * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                           (Datatypes.S k)))))
                      * q_fact (Datatypes.S k)))
                == Aeq * ((1 + - (1#2) * y)
                          * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                              (Datatypes.S k)))
                             * q_fact (Datatypes.S k)))).
  { apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             ((1 + - (1#2) * y)
              * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                  * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * q_fact (Datatypes.S k)))
             ((1 + - (1#2) * y)
              * ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))
                 * q_fact (Datatypes.S k))));
    [ exact Hv0 | ring ]. }
  rewrite HcL.
  (* RHS：D 逐块分摊 + 消去（显式实例，防 LHS 误分摊） *)
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq))
              + (1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (- ((1#2) * (y * Aeq
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))))
              )
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite (Qmult_plus_distr_l
             (- ((1#2) * (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          / q_fact (Datatypes.S k) * Aeq)))
             ((1#2) * (Aeq / q_fact (Datatypes.S (Datatypes.S
                    (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  (* 块 B：β/w·A·D *)
  rewrite (ptp_opp_mul_move ((1#2) * (q_fact 1 * q_fact (Datatypes.S
             (Datatypes.S k))
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))
             / q_fact (Datatypes.S k) * Aeq))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (1#2)
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k) * Aeq)
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k))))
              / q_fact (Datatypes.S k))
             Aeq
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcB1 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k))))
                  / q_fact (Datatypes.S k))
                 * (Aeq * (((1 + 1)%Q
                            * q_fact (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))
                            * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                (Datatypes.S k)))))
                           * q_fact (Datatypes.S k)))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                     / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))
                              * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                                  (Datatypes.S k))))))).
  { apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
              / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
             (q_fact (Datatypes.S k))
             (Aeq * (((1 + 1)%Q
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                      * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                          (Datatypes.S k)))))
                     * q_fact (Datatypes.S k)))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k)))))));
    [ exact Hw0 | ring ]. }
  rewrite HcB1.
  assert (HcB2 : (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k))
                  / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))))
                 * (Aeq * ((1 + 1)%Q
                           * q_fact (Datatypes.S (Datatypes.S
                               (Datatypes.S k)))
                           * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                               (Datatypes.S k))))))
                 == (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
                    * (Aeq * ((1 + 1)%Q
                              * q_fact (Datatypes.S (Datatypes.S
                                  (Datatypes.S k)))))).
  { apply (ptp_div_clear_r
             (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                         (Datatypes.S k))))))
             (Aeq * ((1 + 1)%Q
                     * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))));
    [ exact Hv0 | ring ]. }
  rewrite HcB2.
  (* 块 C：A/u3·D *)
  rewrite <- (Qmult_assoc (1#2)
             (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcC : (Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == Aeq * ((1 + 1)%Q
                          * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                              (Datatypes.S k))))
                          * q_fact (Datatypes.S k))).
  { apply (ptp_div_clear_r Aeq
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             (((1 + 1)%Q
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k))))
               * q_fact (Datatypes.S k))));
    [ exact Hu0 | ring ]. }
  rewrite HcC.
  (* 块 D：y·A/v4·D *)
  rewrite (ptp_opp_mul_move ((1#2) * (y * Aeq
             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k))))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  rewrite <- (Qmult_assoc (1#2)
             (y * Aeq / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                 (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))).
  assert (HcD : ((y * Aeq) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))))
                * (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S
                      (Datatypes.S k)))
                    * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                        (Datatypes.S k)))))
                   * q_fact (Datatypes.S k))
                == (y * Aeq) * ((1 + 1)%Q
                                * q_fact (Datatypes.S (Datatypes.S
                                    (Datatypes.S k)))
                                * q_fact (Datatypes.S k))).
  { apply (ptp_div_clear_r (y * Aeq)
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S k)))))
             (((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k)))
               * q_fact (Datatypes.S (Datatypes.S (Datatypes.S
                   (Datatypes.S k)))))
              * q_fact (Datatypes.S k))
             ((1 + 1)%Q
              * q_fact (Datatypes.S (Datatypes.S
                  (Datatypes.S k)))
               * q_fact (Datatypes.S k)));
    [ exact Hv0 | ring ]. }
  rewrite HcD.
  (* merge 回代（乘法形，括号对齐） *)
  rewrite (Qmult_comm Aeq
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             ((1 + 1)%Q * q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             Aeq).
  rewrite (Qmult_comm (1 + 1)%Q
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))).
  rewrite (Qmult_assoc (q_fact 1 * q_fact (Datatypes.S (Datatypes.S k)))
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S k))))
             (1 + 1)%Q).
  rewrite (ptp_n1_merge (Datatypes.S k)).
  field.
Qed.

(* —— 5. 主件：全称 N 形恒等式（归纳完成）—— *)

Lemma ptp_main_fg : forall k : nat, forall y : Q, ptp_F k y == ptp_G k y.
Proof.
  induction k as [| k IH].
  - intro y. unfold ptp_F, ptp_G.
    unfold ptp_beta_prefix, ptp_beta, pade_den, pade_num, pade_coeff.
    cbn. field.
  - intro y. rewrite ptp_F_step. rewrite ptp_G_step.
    rewrite <- ptp_G_eq. rewrite IH. rewrite (ptp_step_core k y).
    reflexivity.
Qed.

Theorem ptp_tail_series_k : forall (k : nat) (y : Q),
  exp_partial (3 + k) y * pade_den 1 y - pade_num 1 y
  == - ((1#2) * ptp_beta_prefix 1 k y)
     - (1#2) * (q_pow y (Datatypes.S (3 + k)) / q_fact (3 + k)).
Proof.
  intros k y. change (ptp_F k y == ptp_G k y). apply ptp_main_fg.
Qed.

Theorem ptp_tail_series : forall (N : nat) (y : Q), (3 <= N)%nat ->
  exp_partial N y * pade_den 1 y - pade_num 1 y
  == - ((1#2) * ptp_beta_prefix 1 (N - 3) y)
     - (1#2) * (q_pow y (Datatypes.S N) / q_fact N).
Proof.
  intros N y HN.
  replace N with (3%nat + (N - 3)%nat)%nat by lia.
  replace (3%nat + (N - 3)%nat - 3%nat)%nat with (N - 3)%nat by lia.
  apply (ptp_tail_series_k (N - 3) y).
Qed.

(* —— 6. 核对标记：N=3/N=4 闭式与 ptp_n1_poly 逐系数对照；
   y=1/2 数值两侧同值（reflexively 一致）。 —— *)

Lemma ptp_series_n1_N3 : forall y : Q,
  - ((1#2) * ptp_beta_prefix 1 0 y)
    + - ((1#2) * (q_pow y (4 + 0) / q_fact (3 + 0)))
  == - ((1#12) * q_pow y 3 + (1#12) * q_pow y 4).
Proof. intro y. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

Lemma ptp_series_n1_N4 : forall y : Q,
  - ((1#2) * ptp_beta_prefix 1 1 y)
    + - ((1#2) * (q_pow y (4 + 1) / q_fact (3 + 1)))
  == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5).
Proof. intro y. unfold ptp_beta_prefix, ptp_beta. cbn. field. Qed.

(* N=4 特例与 T1a 定值件 ptp_n1_poly 的语句面逐字一致 *)
Lemma ptp_n1_poly_recheck : forall y : Q,
  exp_partial 4 y * pade_den 1 y - pade_num 1 y
  == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4 + (1#48) * q_pow y 5).
Proof.
  intro y.
  change (ptp_F 1 y
          == - ((1#12) * q_pow y 3 + (1#24) * q_pow y 4
                + (1#48) * q_pow y 5)).
  transitivity (ptp_G 1 y).
  - apply ptp_main_fg.
  - unfold ptp_G. apply ptp_series_n1_N4.
Qed.

(* 全称件实例与定值件数值核对：同一 y=1/2 两侧同值 −(7#512) *)
Lemma ptp_tail_sentinel_F_half : ptp_F 1 (1#2) == -(7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_sentinel_G_half : ptp_G 1 (1#2) == -(7#512).
Proof. vm_compute. unfold Qeq. simpl. lia. Qed.

Lemma ptp_tail_FG_agree_half : ptp_F 1 (1#2) == ptp_G 1 (1#2).
Proof. apply ptp_main_fg. Qed.

(* —— 审计与提取（T1c 增量）—— *)

Print Assumptions ptp_tail_series.
Print Assumptions ptp_tail_series_k.
Print Assumptions ptp_main_fg.
Print Assumptions ptp_step_core.
Print Assumptions ptp_n1_merge.
Print Assumptions ptp_n1_poly_recheck.

Separate Extraction ptp_tail_series ptp_step_core ptp_n1_merge.

(* ============================ §2 路径 C 分母正性的 (1,2) 段 使命：本件形式化 Pade 逼近分母在 x ∈ (1,2) 上的正性：Q_n(x) ≥ 0 且 ============================ *)
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

Local Open Scope Q_scope.

(* ============================================================ *)
(* 件 1：比率下界 pdp_R n k ≥ 2（k < n）——本件核心新数学。           *)
(*   与 pdp_R_ge_1 同构骨架：2 = inv(a)·(2·a) ≤ inv(a)·(b·c) = pdp_R， *)
(*   其中 2·a ≤ b·c 由 Z 层算术支件（pql_nat_ratio_mono2，             *)
(*   k(2n−k+2) ≥ 0）支撑。                                           *)
(* ============================================================ *)
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

(* ============================================================ *)
(* 件 2：递减面升档——x ≤ 2 时逐项递减（与 pdp_term_decay 同构，       *)
(*   把「x≤1 乘法单调步」换成「x ≤ 2 ≤ c_k/c_{k+1} 比率步」）。        *)
(* ============================================================ *)
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

(* ============================================================ *)
(* 件 3（主件·非严格）：1 < x < 2 ⟹ 0 ≤ Q_n(x)。                     *)
(*   语句面照 pdp_den_pos 实形档（结论 QleT'）；骨架同 pdp_den_pos，  *)
(*   仅递减假设位换 pdq_term_decay_2。                                 *)
(* ============================================================ *)
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

(* ============================================================ *)
(* 件 4：严格版支撑（首对严格 + 引擎 altsum_pos_strict 直供）。        *)
(* ============================================================ *)

(* 件 4a：g(0) = 1（c_{n,0}=1、x^0=1，全 n 成立） *)
Lemma pdq_g0_one : forall (n : nat) (x : Q), pdp_g n x 0%nat == 1%Q.
Proof.
  intros n x. unfold pdp_g.
  assert (E0 : (0 <=? n)%nat = true)
    by (apply Nat.leb_le; exact (Nat.le_0_l n)).
  rewrite E0. cbn [q_pow].
  rewrite (pade_coeff_0_one n). ring.
Qed.

(* 件 4b：首对严格 g(1) < g(0)——不显式算 c_{n,1}，经比率恒等式        *)
(*   c_0 == c_1·R_0 与 x < 2 ≤ R_0、c_1 > 0 传递。                   *)
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

(* 件 4c：n=1 闭形 den_1(x) == 1 − x/2（pds_c11 数值锚系数显式应用） *)
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

(* 件 4c'：n=0 闭形 den_0(x) == 1（与变元无关） *)
Lemma pdq_den0_one : forall x : Q, pade_den 0%nat x == 1%Q.
Proof.
  intros x. rewrite (pdp_den_altsum 0%nat x).
  unfold altsum. rewrite altsum_acc_T.
  rewrite (altsum_acc_0_eq false (pdp_g 0%nat x) 1%nat).
  rewrite (pdq_g0_one 0%nat x). ring.
Qed.

(* 件 4d：半线性事实内联于件 5 的 n=1 分支（Prop 序仅证内作桥，        *)
(*   不设独立语句面——纪律：语句面不落 Qlt Prop 形）。                  *)

(* ============================================================ *)
(* 件 5（主件·严格）：1 < x < 2 ⟹ 0 < Q_n(x)（全 n）。               *)
(*   n≥2 走引擎 altsum_pos_strict（首对严格 + 非负尾）；n=0 恒一、      *)
(*   n=1 闭式 1 − x/2 > 0。                                          *)
(* ============================================================ *)
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

(* ============================ §3 qtr_qlt_sub / qtr_div2_lt / qtr_div2_ltT 语句面 ============================ *)
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
Require Import UpReqPadeExp.
Require Import UpReqQExpTail.
Require Import UpReqPadeLower.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith Lia Setoid.

(* ============================================================ *)
(* B0 桥接引理：Q 层小组合件（自持零外部依赖）                          *)
(* ============================================================ *)

(* a < b ⟹ 0 < b − a（QltT 面）。
   证法：Qplus_lt_r（z+x < z+y <-> x<y，z := −a）+ Qplus_opp_r/
   Qplus_comm setoid 换形；Qminus b a 定义性 == b + (−a)。
   （destruct-lia 不可行：分母正性不在 lia 可达面。） *)
Lemma qtr_qlt_sub : forall a b : Q, QltT a b -> QltT 0 (b - a).
Proof.
  intros a b H.
  assert (Hlt : Qlt a b) by (apply QltT_to_Qlt; exact H).
  assert (H1 : Qlt (- a + a) (- a + b)).
  { exact (proj2 (Qplus_lt_r a b (- a)) Hlt). }
  apply Qlt_to_QltT.
  setoid_rewrite (Qplus_comm (- a) a) in H1.
  setoid_rewrite (Qplus_opp_r a) in H1.
  setoid_rewrite (Qplus_comm (- a) b) in H1.
  exact H1.
Qed.

(* 0 < x ⟹ x/2 < x（半额严格收缩）。
   destruct-lia：H 多项式形 0 < nx·dx，目标 −(nx·dx) < 2·(nx·dx)，
   线性于 P := nx·dx（micromega 环形范化；cpl_qlt_le 同族）。 *)
Lemma qtr_div2_lt : forall x : Q, Qlt 0 x -> Qlt (x / 2) x.
Proof.
  intro x. unfold Qlt in *.
  destruct x as [nx dx]. simpl in *. lia.
Qed.

Lemma qtr_div2_ltT : forall x : Q, QltT 0 x -> QltT (x / 2) x.
Proof.
  intros x H. apply Qlt_to_QltT. apply qtr_div2_lt.
  apply QltT_to_Qlt. exact H.
Qed.

(* 约分证书：m ≠ 0 ⟹ (a/m)·m == a（Qmult_inv_r，零除法目标面） *)
Lemma qtr_div_cancel : forall a m : Q, ~ (m == 0) -> a / m * m == a.
Proof.
  intros a m Hm. unfold Qdiv.
  rewrite <- (Qmult_assoc a (/ m) m).
  rewrite (Qmult_comm (/ m) m).
  rewrite (Qmult_inv_r m Hm).
  apply Qmult_1_r.
Qed.

(* ============================================================ *)
(* G1① 嵌入保序桥：Q 层序 ⟹ Real 层嵌入序                          *)
(* ============================================================ *)

(* 严格形：a < b ⟹ real_const a < real_const b。
   见证 eps := (b−a)/2 > 0、N := 0（常值序列逐点合同）。 *)
Theorem qtr_embed_mono : forall a b : Q, QltT a b ->
  real_lt (real_const a) (real_const b).
Proof.
  intros a b Hab.
  assert (Hsub : QltT 0 (b - a)) by (apply qtr_qlt_sub; exact Hab).
  assert (Hhalf : QltT ((b - a) / 2) (b - a)) by (apply qtr_div2_ltT; exact Hsub).
  unfold real_lt.
  exists ((b - a) / 2)%Q. split.
  - apply qltT_div_pos.
    + exact Hsub.
    + exact qltT_0_2.
  - exists 0%nat. intros n _.
    assert (Hraw : projT1 (real_const b) n - projT1 (real_const a) n
                   == b - a).
    { apply Qminus_comp; apply real_const_proj. }
    apply qltT_eq_compat_r with (a' := (b - a)%Q).
    + exact Hraw.
    + exact Hhalf.
Qed.

(* 弱形：a ≤ b ⟹ real_const a ≤ real_const b（real_le 三形：
   严格支走嵌入桥；Id 等值支走 Qabs 零合同）。 *)
Theorem qtr_embed_le : forall a b : Q, QleT a b ->
  real_le (real_const a) (real_const b).
Proof.
  intros a b Hab. destruct Hab as [Hlt | H0].
  - left. apply qtr_embed_mono. exact Hlt.
  - right. intros eps Heps. exists 0%nat. intros n _.
    assert (Hab0 : a - b == 0).
    { destruct H0. ring. }
    assert (Habs0 : Qabs (projT1 (real_const a) n
                          - projT1 (real_const b) n) == 0).
    { apply Qeq_trans with (y := Qabs (a - b)).
      - apply Qabs_wd. apply Qminus_comp; apply real_const_proj.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. exact Hab0.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ============================================================ *)
(* G1② 级数桥墩：Q 层部分和尾差下界（e^y ≥ 部分和 的 Q 内核）        *)
(* ============================================================ *)

(* 尾差首项下界：0 ≤ y、d ≥ 0 ⟹
   y^{n+1}/(n+1)! ≤ E_{n+1+d}(y) − E_n(y)。
   归纳不变式：每步追加非负项 y^k/k!（q_pow_fact_nonneg）。 *)
Lemma qtr_partial_gap : forall (y : Q) (n d : nat), QleT 0 y ->
  Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
      (exp_partial (Datatypes.S n + d) y - exp_partial n y).
Proof.
  intros y n d Hy. revert d.
  assert (Hy0 : Qle 0 y) by (apply qtail_QleT_to_Qle; exact Hy).
  induction d as [| d IH].
  - replace (Datatypes.S n + 0)%nat with (Datatypes.S n)%nat by lia.
    change (exp_partial (Datatypes.S n) y) with
      (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    (* 除法原子化：ring 不吃 Qdiv 原子（判例 同款坑） *)
    set (T := q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    apply qeq_imp_qle. ring.
  - replace (Datatypes.S n + Datatypes.S d)%nat
      with (Datatypes.S (Datatypes.S n + d))%nat by lia.
    change (exp_partial (Datatypes.S (Datatypes.S n + d)) y) with
      (exp_partial (Datatypes.S n + d) y
       + q_pow y (Datatypes.S (Datatypes.S n + d))
         / q_fact (Datatypes.S (Datatypes.S n + d))).
    set (T2 := q_pow y (Datatypes.S (Datatypes.S n + d))
                 / q_fact (Datatypes.S (Datatypes.S n + d))).
    apply (Qle_trans _
             ((exp_partial (Datatypes.S n + d) y - exp_partial n y) + T2)%Q _).
    + (* 首项 ≤ 旧尾差 ≤ 旧尾差 + 非负新项 *)
      apply (Qle_trans _ (exp_partial (Datatypes.S n + d) y - exp_partial n y) _).
      * exact IH.
      * apply qtail_le_plus_r.
        unfold T2. apply q_pow_fact_nonneg. exact Hy0.
    + (* 换形：(E − F) + T2 == E + T2 − F（ring，除法已原子化） *)
      apply qeq_imp_qle. ring.
Qed.

(* ============================================================ *)
(* G1② 级数桥：Real 层 e^y ≥ 第 n 部分和（eps/Bishop 形）           *)
(* ============================================================ *)

(* 严格形：y > 0 ⟹ real_const(E_n(y)) < e^y。
   见证 eps := (y^{n+1}/(n+1)!)/2 > 0、N := n+1；逐点差
   E_m(y) − E_n(y) ≥ y^{n+1}/(n+1)! > eps（m ≥ n+1，尾差递增）。 *)
Theorem qtr_exp_gt_partial : forall (y : Q) (n : nat), QltT 0 y ->
  real_lt (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy.
  assert (Hterm : QltT 0 (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
  { apply qltT_div_pos.
    - apply Qlt_to_QltT. apply (cpl_qpow_pos y (Datatypes.S n)).
      apply QltT_to_Qlt. exact Hy.
    - apply Qlt_to_QltT. apply q_fact_pos. }
  unfold real_lt.
  exists (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)%Q.
  split.
  - apply qltT_div_pos.
    + exact Hterm.
    + exact qltT_0_2.
  - exists (Datatypes.S n). intros m Hm.
    assert (Hle : (Datatypes.S n <= m)%nat) by (apply NatLe_drop; exact Hm).
    assert (Hraw : projT1 (cauchy_real_exp (real_const y)) m
                   - projT1 (real_const (exp_partial n y)) m
                   == exp_partial m y - exp_partial n y).
    { apply Qminus_comp.
      - apply exp_const_proj.
      - apply real_const_proj. }
    assert (Hgap : Qle (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))
                       (exp_partial m y - exp_partial n y)).
    { replace m with (Datatypes.S n + (m - Datatypes.S n))%nat by lia.
      apply qtr_partial_gap.
      left. exact Hy. }
    assert (HgapT : QltT (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n) / 2)
                         (exp_partial m y - exp_partial n y)).
    { apply Qlt_to_QltT.
      apply (Qlt_le_trans _ (q_pow y (Datatypes.S n) / q_fact (Datatypes.S n))).
      - apply qtr_div2_lt. apply QltT_to_Qlt. exact Hterm.
      - exact Hgap. }
    apply qltT_eq_compat_r with (a' := (exp_partial m y - exp_partial n y)%Q).
    + exact Hraw.
    + exact HgapT.
Qed.

(* 弱形：y ≥ 0 ⟹ real_const(E_n(y)) ≤ e^y（real_le 三形：
   严格支走级数桥；y == 0 支走全 1 部分和的 real_eq 合同，
   Id 分支经 destruct 收 Qeq）。 *)
Theorem qtr_exp_ge_partial : forall (y : Q) (n : nat), QleT 0 y ->
  real_le (real_const (exp_partial n y)) (cauchy_real_exp (real_const y)).
Proof.
  intros y n Hy. destruct Hy as [Hlt | H0].
  - left. apply qtr_exp_gt_partial. exact Hlt.
  - assert (H0q : 0 == y) by (destruct H0; apply Qeq_refl).
    assert (Hn1 : exp_partial n y == 1%Q).
    { apply Qeq_trans with (y := exp_partial n 0).
      - apply Qeq_sym. apply (cpl_ep_ext n 0 y H0q).
      - apply exp_partial_zero. }
    assert (Hk1 : forall k : nat, exp_partial k y == 1%Q).
    { intro k. apply Qeq_trans with (y := exp_partial k 0).
      - apply Qeq_sym. apply (cpl_ep_ext k 0 y H0q).
      - apply exp_partial_zero. }
    right. intros eps Heps. exists 0%nat. intros k _.
    assert (Habs0 : Qabs (projT1 (real_const (exp_partial n y)) k
                          - projT1 (cauchy_real_exp (real_const y)) k) == 0).
    { apply Qeq_trans with (y := Qabs (1%Q - 1%Q)).
      - apply Qabs_wd.
        apply Qminus_comp.
        + apply Qeq_trans with (y := exp_partial n y).
          * apply real_const_proj.
          * exact Hn1.
        + apply Qeq_trans with (y := exp_partial k y).
          * apply exp_const_proj.
          * apply Hk1.
      - apply Qeq_trans with (y := Qabs 0).
        + apply Qabs_wd. ring.
        + apply Qeq_refl. }
    apply qltT_eq_compat_l with (a := 0%Q).
    + apply Qeq_sym. exact Habs0.
    + exact Heps.
Qed.

(* ============================================================ *)
(* G2 核心：real_mult 对 real_eq 的左合同（运输引擎）                *)
(* ============================================================ *)

(* 约分证书已备（qtr_div_cancel）。
   左合同：x ≡ z ⟹ x·v ≡ z·v（real_eq 面）。
   证法：real_norm_bounded 取 |v| ≤ Mv，半额松弛 eps/2：
   |u_n−z_n|·|w_n| ≤ (eps/2/Mv')·Mv' == eps/2 < eps
   （Qmult_le_compat_nonneg + Qmult_inv_r 证书；零除法目标面）。 *)
Lemma qtr_mult_eq_compat_l : forall x z v : Real,
  real_eq x z -> real_eq (real_mult x v) (real_mult z v).
Proof.
  intros [u Hu] [z Hz] [w Hw] Heq eps Heps.
  destruct (real_norm_bounded (existT (fun s : Qseq => cauchy s) w Hw))
    as [Mv [HMvT HMv]].
  set (Mv' := (Qabs Mv + 1)%Q).
  assert (HMv'0 : Qlt 0 Mv').
  { unfold Mv'. setoid_rewrite <- (Qplus_comm 1%Q (Qabs Mv)).
    apply (Qlt_le_trans 0%Q 1%Q).
    - reflexivity.
    - apply Qle_plus_nonneg_r. apply Qabs_nonneg. }
  assert (HMv'posT : QltT 0 Mv') by (apply Qlt_to_QltT; exact HMv'0).
  (* 半额放大：以 eps/2 喂 Heq，末段 eps/2 < eps 补严格性 *)
  destruct (Heq (eps / 2 / Mv')
    (qltT_div_pos (eps / 2) Mv'
       (qltT_div_pos eps 2%Q Heps qltT_0_2) HMv'posT)) as [N HN].
  exists N. intros n Hn.
  specialize (HN n Hn).
  (* HN : QltT |u_n − z_n| (eps/2/Mv') *)
  assert (Hwn : Qle (Qabs (w n)) Mv').
  { apply (Qle_trans _ Mv _).
    - apply (QleT'_to_Qle _ _ (HMv n)).
    - apply (Qle_trans _ (Qabs Mv) _).
      + apply Qle_Qabs.
      + apply Qle_plus_nonneg_r.
        (* 0 <= 1：Qle 展开后 lia（Z 层平凡） *)
        unfold Qle. simpl. lia. }
  assert (Hle2 : Qle (Qabs (u n - z n) * Qabs (w n))
                     ((eps / 2 / Mv') * Mv')).
  { apply (Qmult_le_compat_nonneg (Qabs (u n - z n))
             (eps / 2 / Mv')%Q (Qabs (w n)) Mv').
    - split.
      + apply Qabs_nonneg.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact HN.
    - split.
      + apply Qabs_nonneg.
      + exact Hwn. }
  assert (Hab : Qabs (u n * w n - z n * w n)
                == Qabs (u n - z n) * Qabs (w n)).
  { apply Qeq_trans with (y := Qabs ((u n - z n) * w n)).
    - apply Qabs_wd. ring.
    - apply Qabs_Qmult. }
  assert (Hchain : QltT (Qabs (u n - z n) * Qabs (w n)) eps).
  { apply Qlt_to_QltT.
    apply (Qle_lt_trans _ (eps / 2) eps).
    - apply (Qle_trans _ ((eps / 2 / Mv') * Mv')).
      + exact Hle2.
      + apply qeq_imp_qle.
        apply qtr_div_cancel. apply qtail_neq0. exact HMv'0.
    - apply qtr_div2_lt.
      apply QltT_to_Qlt. exact Heps. }
  apply qltT_eq_compat_l with (a := Qabs (u n - z n) * Qabs (w n)).
  - apply Qeq_sym. exact Hab.
  - exact Hchain.
Qed.

(* ============================================================ *)
(* G2 主件：Padé 精度 Real 层下界首件（载体任取）                    *)
(* ============================================================ *)

(* y > 0、w ≡ e^y（real_eq 意义下任意 Real 载体）⟹
   P₂(y) < w·Q₂(y)（乘开免除法形）。
   运输路径：cpl_lower_even（特定对角载体）→ real_lt_eq_lt +
   real_mult 左合同（qtr_mult_eq_compat_l）→ 任意载体。 *)
Theorem qtr_pade_lower_real : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw.
  apply (real_lt_eq_lt _ _ _ (cpl_lower_even y Hy)).
  apply qtr_mult_eq_compat_l.
  apply real_eq_sym. exact Hw.
Qed.

(* ============================================================ *)
(* G2b 反桥：real_lt 证书解包为显式 N/eps 的逐点 QltT 形              *)
(* （eps/Bishop 见证反射：Real 层语句 ⟹ 逐点 Q 层精度账；            *)
(*   N/eps 由 cpl 的 sigT 见证原样透传：y⁵/720、N := 6）             *)
(* ============================================================ *)

Theorem qtr_pade_lower_extract : forall y : Q, QltT 0 y ->
  sigT (fun N : nat => sigT (fun eps : Q => And (QltT 0 eps)
    (forall m : nat, NatLe N m ->
      QltT eps (exp_partial m y * pade_den 2%nat y
                - pade_num 2%nat y)%Q))).
Proof.
  intros y Hy.
  destruct (cpl_lower_even y Hy) as [eps [Heps [N HN]]].
  exists N. exists eps. split.
  - exact Heps.
  - intros m Hm.
    specialize (HN m Hm).
    assert (Hmult : projT1 (real_mult (cauchy_real_exp (real_const y))
                                      (real_const (pade_den 2%nat y))) m
                    == exp_partial m y * pade_den 2%nat y).
    { apply Qeq_trans with
        (y := projT1 (cauchy_real_exp (real_const y)) m
              * projT1 (real_const (pade_den 2%nat y)) m).
      - apply real_mult_proj.
      - apply Qmult_comp.
        + apply exp_const_proj.
        + apply real_const_proj. }
    assert (Hconst : projT1 (real_const (pade_num 2%nat y)) m
                     == pade_num 2%nat y).
    { apply real_const_proj. }
    assert (Hraw : projT1 (real_mult (cauchy_real_exp (real_const y))
                                     (real_const (pade_den 2%nat y))) m
                   - projT1 (real_const (pade_num 2%nat y)) m
                   == exp_partial m y * pade_den 2%nat y
                      - pade_num 2%nat y).
    { apply Qminus_comp.
      - exact Hmult.
      - exact Hconst. }
    exact (qltT_eq_compat_r _ _ _ (Qeq_sym _ _ Hraw) HN).
Qed.

(* 弱形补全（real_le 三形）：y > 0、w ≡ e^y ⟹ P₂(y) ≤ w·Q₂(y)。 *)
Theorem qtr_pade_lower_real_le : forall (y : Q) (w : Real), QltT 0 y ->
  real_eq w (cauchy_real_exp (real_const y)) ->
  real_le (real_const (pade_num 2%nat y))
          (real_mult w (real_const (pade_den 2%nat y))).
Proof.
  intros y w Hy Hw. left.
  apply (qtr_pade_lower_real y w Hy Hw).
Qed.

(* ============================================================ *)
(* 认证面（公理面：预期全员 Closed）                                *)
(* ============================================================ *)

Print Assumptions qtr_embed_mono.
Print Assumptions qtr_embed_le.
Print Assumptions qtr_partial_gap.
Print Assumptions qtr_exp_gt_partial.
Print Assumptions qtr_exp_ge_partial.
Print Assumptions qtr_mult_eq_compat_l.
Print Assumptions qtr_pade_lower_real.
Print Assumptions qtr_pade_lower_extract.
Print Assumptions qtr_pade_lower_real_le.
