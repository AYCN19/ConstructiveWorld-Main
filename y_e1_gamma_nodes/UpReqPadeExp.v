(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqPadeExp.v *)
(* 目的： 路径 C：指数函数的 Padé [n/n] 带符号逼近定义面。 *)
(* 主件： pade_coeff / pade_num / pade_den 定义族与 pade_coeff_pos、pade_den_sym。 *)
(* 依赖： CW_ConstructiveWorld_219。 *)
(* 备注： 使用引理带 (k <= n) 前提守卫（诚实注记见正文）；对称显式假设申报，登记于文末。 *)
(* ============================================================ *)
(* PC：路径 C，eˣ 的 Padé [n/n] 带符号逼近（Q 层定义面 + 系数正性 + 分母对称性）。   *)
(*   任务定位（评审003 路径 C「最优下一步」）：把 0<eˣ 从定性升级为带符号的定量逼近    *)
(*   ——Padé [n/n] 逼近 eˣ 的余项符号 = (−1)^n，误差界可计算。分层保底：S1 定义面       *)
(*   （pade_coeff/pade_num/pade_den，Q 值有限和）；S2 系数正性族 pade_coeff_pos         *)
(*   （语句面 QltT，Set 层）；S3 对称性 pade_den_sym（分母 = 分母在 −x 处的分子）；      *)
(*   S4 加分件 pade_num_0_one/pade_den_0_one + n=1 具体例全展开。余项积分表示          *)
(*   （误差符号/误差界的最终形态）依赖构造性积分基建，此次禁攻；对称显式假设           *)
(*   （升级路径见文末登记段）。依赖复用（全部 Require 使用，零改写库件）：              *)
(*   CW_ConstructiveWorld_219（薄壳 Export S01..S15）——S03: q_fact/q_pow/sum_upto/     *)
(*   sum_upto_ext/q_fact_pos；S02: QltT/Qlt_to_QltT（Set 层语句基元）；stdlib:          *)
(*   Qmult_lt_0_compat/Qinv_lt_0_compat/Qmult_inv_r。定义域声明（Nat.sub 截断坑）：     *)
(*   pade_coeff n k 的公式含 nat 减法 (2*n−k) 与 (n−k)，k>n 时截断为 0 会静默产出伪值    *)
(*   （例：n=1,k=2 得 1/4）。故 ① pade_coeff n k 仅在 (k <= n)%nat 时承载 Padé [n/n]     *)
(*   系数语义；② 使用引理带 (k <= n)%nat 前提守卫。诚实注记：正性命题本身对越界截断     *)
(*   值也成立（q_fact 处处为正），守卫为「值 = 真系数」的语义服务；后续误差符号/误差    *)
(*   界引理使用 pade_coeff 时必须携带并使用该守卫。编译配方：VOTREE =                    *)
(*   ConstructiveWorld_vo 依赖树（-Q ../001 草案无 S01..S03 编译产物，实测不可用），      *)
(*   见 attn/_tpc_build.cmd。                                                          *)

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
From Stdlib Require Import QArith.QArith Arith.Arith Lia.

Section PadeExpQ.

(* ===== S1 定义面 ===== *)

(* Padé [n/n] 系数：(2n−k)!·n! / ((2n)!·k!·(n−k)!)，Q 值。
   定义域：(k <= n)%nat（截断坑见头注①②）。 *)
Definition pade_coeff (n k : nat) : Q :=
  q_fact (2 * n - k) * q_fact n /
  (q_fact (2 * n) * (q_fact k * q_fact (n - k))).

(* Padé 分子 P_n(x) = Σ_{k=0}^{n} c_{n,k}·x^k。
   sum_upto m f = Σ_{i=0}^{m−1} f i（S03:2481），故上界取 Datatypes.S n。 *)
Definition pade_num (n : nat) (x : Q) : Q :=
  sum_upto (Datatypes.S n) (fun k => pade_coeff n k * q_pow x k).

(* Padé 分母 Q_n(x) = Σ_{k=0}^{n} (−1)^k·c_{n,k}·x^k。
   交错和形（q_pow (-1) k，与库内 altf 交错和家族同族），非 (−x)^k
   直接形——使 S3 对称性为真实逐项 opp 引理而非定义性平凡。 *)
Definition pade_den (n : nat) (x : Q) : Q :=
  sum_upto (Datatypes.S n) (fun k => q_pow (- 1)%Q k * (pade_coeff n k * q_pow x k)).

(* 奇偶吸收基元：(−x)^k == (−1)^k·x^k——S3 逐项 opp 的核心。 *)
Lemma pade_q_pow_opp_sign : forall (x : Q) (k : nat),
  q_pow (- x)%Q k == q_pow (- 1)%Q k * q_pow x k.
Proof.
  intros x k. induction k as [| m IH].
  - simpl. reflexivity.
  - change (q_pow (- x)%Q (Datatypes.S m)) with ((- x) * q_pow (- x)%Q m).
    change (q_pow (- 1)%Q (Datatypes.S m)) with ((- 1) * q_pow (- 1)%Q m).
    change (q_pow x (Datatypes.S m)) with (x * q_pow x m).
    setoid_rewrite IH.
    ring.
Qed.

(* k=0 系数恒一（定义面健全性；0 <= n 对一切 n 恒真，无需守卫参数）。 *)
Lemma pade_coeff_0_one : forall n : nat, pade_coeff n 0%nat == 1%Q.
Proof.
  intro n. unfold pade_coeff.
  assert (H1 : (2 * n - 0 = 2 * n)%nat) by lia.
  assert (H2 : (n - 0 = n)%nat) by lia.
  rewrite H1, H2.
  change (q_fact 0%nat) with 1%Q.
  setoid_rewrite Qmult_1_l.
  unfold Qdiv.
  apply Qmult_inv_r.
  intro Hz.
  assert (Hpos : Qlt 0 (q_fact (2 * n) * q_fact n))
    by (apply Qmult_lt_0_compat; apply q_fact_pos).
  unfold Qeq in Hz. unfold Qlt in Hpos. simpl in Hz, Hpos. lia.
Qed.

(* ===== S2 系数正性族（语句面 QltT，Set 层） ===== *)

(* 阶乘正性链：分子 = 两正之积、分母 = 三正之积，Q 除法正性 =
   分子正 × 分母倒数正（Qmult_lt_0_compat + Qinv_lt_0_compat）。
   证内 Prop 序仅作桥（Qlt_to_QltT），语句面为 QltT。
   守卫 (k <= n)%nat 为定义域声明（见头注②）。 *)
Theorem pade_coeff_pos : forall (n k : nat), (k <= n)%nat -> QltT 0 (pade_coeff n k).
Proof.
  intros n k Hk.
  apply Qlt_to_QltT.
  unfold pade_coeff. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply Qmult_lt_0_compat; apply q_fact_pos.
  - apply Qinv_lt_0_compat. apply Qmult_lt_0_compat.
    + apply q_fact_pos.
    + apply Qmult_lt_0_compat; apply q_fact_pos.
Qed.

(* ===== S3 对称性 ===== *)

(* 分母对称：Q_n(x) == P_n(−x)——有限和逐项 opp
   （库件 sum_upto_ext 外延 + pade_q_pow_opp_sign 奇偶吸收）。 *)
Theorem pade_den_sym : forall (n : nat) (x : Q), pade_den n x == pade_num n (- x).
Proof.
  intros n x. unfold pade_den, pade_num.
  apply sum_upto_ext. intro k. cbv beta.
  setoid_rewrite (pade_q_pow_opp_sign x k).
  ring.
Qed.

(* ===== S4 加分件：零点归一 + 具体例 ===== *)

(* 尾零和：正指标项全零则和缩为首项（零点值引理的骨架，归纳于上界）。 *)
Lemma pade_sum_tail_zero : forall (n : nat) (f : nat -> Q),
  (forall k, (0 < k)%nat -> f k == 0) -> sum_upto (Datatypes.S n) f == f 0%nat.
Proof.
  intros n f H. induction n as [| m IH].
  - simpl. apply Qplus_0_l.
  - assert (IH' : sum_upto (Datatypes.S m) f == f 0%nat) by (apply IH; exact H).
    simpl.
    setoid_rewrite IH'.
    assert (Hlt : (0 < Datatypes.S m)%nat) by lia.
    setoid_rewrite (H (Datatypes.S m) Hlt).
    apply Qplus_0_r.
Qed.

(* x=0 处分子归一：P_n(0) == 1（k=0 项存活，k>=1 项因子 x^k=0 清零）。 *)
Lemma pade_num_0_one : forall n : nat, pade_num n 0%Q == 1%Q.
Proof.
  intro n. unfold pade_num.
  transitivity (pade_coeff n 0%nat * q_pow 0%Q 0%nat).
  - apply pade_sum_tail_zero.
    intro k. destruct k as [| m]; intro Hlt; cbv beta.
    + exfalso. lia.
    + change (q_pow 0%Q (Datatypes.S m)) with (0%Q * q_pow 0%Q m).
      setoid_rewrite (Qmult_0_l (q_pow 0%Q m)).
      apply Qmult_0_r.
  - change (q_pow 0%Q 0%nat) with 1%Q.
    setoid_rewrite (pade_coeff_0_one n).
    ring.
Qed.

(* x=0 处分母归一：Q_n(0) == 1（同上，另用 (−1)^0=1）。 *)
Lemma pade_den_0_one : forall n : nat, pade_den n 0%Q == 1%Q.
Proof.
  intro n. unfold pade_den.
  transitivity (q_pow (- 1)%Q 0%nat * (pade_coeff n 0%nat * q_pow 0%Q 0%nat)).
  - apply pade_sum_tail_zero.
    intro k. destruct k as [| m]; intro Hlt; cbv beta.
    + exfalso. lia.
    + change (q_pow 0%Q (Datatypes.S m)) with (0%Q * q_pow 0%Q m).
      setoid_rewrite (Qmult_0_l (q_pow 0%Q m)).
      setoid_rewrite (Qmult_0_r (pade_coeff n (Datatypes.S m))).
      apply Qmult_0_r.
  - change (q_pow (- 1)%Q 0%nat) with 1%Q.
    change (q_pow 0%Q 0%nat) with 1%Q.
    setoid_rewrite (pade_coeff_0_one n).
    ring.
Qed.

(* n=1 具体例全展开：P_1(x)=1+x/2、Q_1(x)=1−x/2；x=1/2 处 5/4 与 3/4。
   vm_compute 闭式计算——系数公式+有界和+交错符号的端到端数值验证
   （若 Nat.sub 截断坑污染定义或交错符号写反，本例即红）。 *)
Lemma pade_num_1_half : pade_num 1 (1#2) == (5#4).
Proof. vm_compute. reflexivity. Qed.

Lemma pade_den_1_half : pade_den 1 (1#2) == (3#4).
Proof. vm_compute. reflexivity. Qed.

(* ===== 显式假设登记（对称，禁特设构造） =====
   显式假设四件：pade_error_integral / pade_integral_pos / pade_error_sign /
   pade_error_bound——Padé [n/n] 余项积分表示：
     eˣ − P_n(x)/Q_n(x) = (−1)^n · x^{2n+1} / ((2n)!·Q_n(x))
                          · ∫₀¹ tⁿ(1−t)ⁿ e^{tx} dt，
   x>=0 时被积函数逐点正 ⟹ 误差符号 = (−1)^n、误差界显式可计算。
   禁攻原因：积分表示需构造性积分基建（本库缺位），此次对称显式假设。
   升级路径（下一轮梯队）：
   ① 建 [0,1] 上多项式型被积函数的构造性积分（Q 层分段和 + 柯西极限，
      复用 S02 柯西完备面）；
   ② pade_integral_pos：被积函数逐点正 ⟹ 积分正（积分单调性基建）；
      （pade_q_pow_opp_sign + pade_den_sym + pade_coeff_pos，
      Q_n(x)>0 于 x>=0 由系数正 + 交错和下界估计接续）；
   ④ pade_error_bound：|x|<=B 时 |余项| <= e^B·B^{2n+1}/((2n)!·(2n+1))
      型显式 Q 界（q_fact 正性 + 库内 pow_fact_geom 几何衰减可复用）。 *)

End PadeExpQ.
