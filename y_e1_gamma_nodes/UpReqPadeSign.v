(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   pds_qlt0_eq_r（原 L96，2 句玩具证）                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeSign.v *)
(* *)
(* 主件： pds_den1_pos / pds_den1_half：n=1 分母正性与半形。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqPadeExp、UpReqPadeQLeg。 *)
(* 备注： 结论面未触及 Q 表示墙（全为严格不等式）；注释不含禁词字面量；零外加假设。 *)
(* ============================================================ *)

(* ============================================================ *)
(*                  （den_pos 家族第一块可构造闭合砖，分层 S1/S2/S3）  *)
(*                                                                 *)
(* 任务定位（§15.5 二轮梯队候选）：Padé [n/n] 分母                   *)
(*   den(x) = sum_upto (Datatypes.S n)                              *)
(*              (fun k => q_pow (-1) k * (pade_coeff n k * q_pow x k)) *)
(*   n=1 时为两项交错和 Q_1(x) = 1 − x/2，于 0<x<2 为正。            *)
(*   本件证：S1 n=0 恒一+正、S2 主件 pds_den1_pos（0<x<2 ⟹ 正）、    *)
(*   S3 锚交叉 pds_den1_half（与 PC 锚 Q_1(1/2)=3/4 数值核对）。  *)
(*                                                                 *)
(* 方法注记：                                                       *)
(*   ① 语句面全 Set 层 QltT（S02:26，Id-of-bool 形）；证内 Prop 序   *)
(*      仅作桥（QltT_to_Qlt + unfold Qlt + lia，pade_coeff_pos       *)
(*      先例），结论面未触 Q 表示墙（本件全为严格不等式，无需        *)
(*      QleT' 换桥）。                                              *)
(*   ② 主件证法绕开 Qeq-穿透墙（PC2 卡⑦⑤：Qeq 方程不能 rewrite     *)
(*      进 Id-of-bool 目标）：x 直接 destruct 为 Qmake nx dx，       *)
(*      全定义面（sum_upto/q_pow/q_fact/pade_coeff/Q 算子）随之      *)
(*      构造子归约干净，Z 层线性，lia 一步完成——零换桥、零          *)
(*      兼容性引理依赖。                                            *)
(*   ③ 显式形 pds_den1_expl：vm_compute 把两侧归一到 Qnum x /        *)
(*      QDen x 上的 Z 恒等式（乘积单子两侧同比出现），lia 完成。      *)
(*                                                                 *)
(* 红线自审基线：无 stdlib 序语句面；nat 字面量带 %nat；后继写        *)
(*   Datatypes.S；注释不落禁词字面量；零外加假设。                    *)
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
Require Import UpReqPadeExp.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeSignQ.

(* ===== S1 保底：n=0 具体例 ===== *)

(* n=0 分母恒一：sum_upto 1 只存 k=0 项，且 q_pow 递归于 nat 指标
   （不触 x），q_pow x 0 == 1 对变元 x 依指标归约——左端除 x 的
   指标位外全闭，vm_compute 端到端归一。 *)
Lemma pds_den0_one : forall x : Q, pade_den 0 x == 1%Q.
Proof. intro x. vm_compute. reflexivity. Qed.

(* S1 主张：Q_0(x) 恒正（Qlt_bool 闭式计算直绿，qltT_0_1 同款）。 *)
Lemma pds_den0_pos : forall x : Q, QltT 0 (pade_den 0 x).
Proof. intro x. unfold QltT. vm_compute. reflexivity. Qed.

(* ===== S2 保底主件：n=1 分母正性 ===== *)

(* 两项和分裂：sum_upto 2 f == f 0 + f 1（高位在后的左折叠，
   iota 两步 + Qplus_0_l；f 的指数位全 %nat 防 Q_scope 吞字面量）。 *)
Lemma pds_sum2 : forall f : nat -> Q,
  sum_upto (Datatypes.S 1%nat) f == f 0%nat + f 1%nat.
Proof.
  intro f. cbn [sum_upto]. cbv beta. ring.
Qed.

(* n=1 闭式系数锚（PC 锚件 pade_den_1_half 同款 vm_compute 口径：
   Nat.sub 截断坑或交错符号写反即红）。 *)
Lemma pds_c10 : pade_coeff 1 0%nat == 1%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma pds_c11 : pade_coeff 1 1%nat == (1#2)%Q.
Proof. vm_compute. reflexivity. Qed.

(* 显式形：Q_1(x) == 1 + (−1)·(1/2)·x——两项交错和的语义面。
   分裂 + q_pow 指标位 change + 系数锚改写 + ring 完成
   （Qopp 原子挂乘积结构，ring 直绿不触 判例）。 *)
Lemma pds_den1_expl : forall x : Q, pade_den 1 x == 1%Q + (- (1#2)%Q) * x.
Proof.
  intro x. unfold pade_den.
  setoid_rewrite pds_sum2. cbv beta.
  change (q_pow (- 1)%Q 0%nat) with 1%Q.
  change (q_pow (- 1)%Q 1%nat) with (-1)%Q.
  change (q_pow x 0%nat) with 1%Q.
  change (q_pow x 1%nat) with (x * 1)%Q.
  setoid_rewrite pds_c10.
  setoid_rewrite pds_c11.
  ring.
Qed.

(* Qeq 右换桥（本件最小传桥接引理）：a == b 时 0<a 传 0<b。
   AA12 肢化：语句面不变，证明体退化为自建 Q 单调肢一跳
   （UpReqPadeQLeg.pql_qlt0_eq_r，Z 乘法单调显式装配 + lia，
   根除 Psatz/micromega 环境闭包）。 *)
Lemma pds_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* 主件：0 < x < 2 ⟹ 0 < Q_1(x) = 1 − x/2。
   证法：传桥到显式乘积形 (1/2)·(2−x)——双正乘 Qmult_lt_0_compat，
   0<2−x 由 Qlt_minus_iff（p<q ↔ 0<q+−p，stdlib:1127 实名）从 x<2
*)
Lemma pds_den1_pos : forall x : Q,
  QltT 0 x -> QltT x (2#1) -> QltT 0 (pade_den 1 x).
Proof.
  intros x H0 H2.
  apply QltT_to_Qlt in H2.
  apply Qlt_to_QltT.
  apply (pds_qlt0_eq_r ((1#2)%Q * (2 + - x)%Q) (pade_den 1 x)).
  - apply (Qeq_trans ((1#2)%Q * (2 + - x)%Q) (1%Q + (- (1#2)%Q) * x) (pade_den 1 x)).
    + ring.
    + apply Qeq_sym. apply pds_den1_expl.
  - apply Qmult_lt_0_compat.
    + unfold Qlt. simpl. lia.
    + apply (proj1 (Qlt_minus_iff x (2#1))). exact H2.
Qed.

(* ===== S3 加分：锚交叉 ===== *)

(* Q_1(1/2) > 0：与 PC 锚 pade_den_1_half（Q_1(1/2) == 3/4）
   数值核对——Qlt_bool 0 (3/4) 闭式归 true，vm_compute 直绿。 *)
Lemma pds_den1_half : QltT 0 (pade_den 1 (1#2)).
Proof. unfold QltT. vm_compute. reflexivity. Qed.

(* ===== 显式假设登记（通用 n 版 den_pos，禁强造） =====
   通用 n 的 den_pos 实例化图（下一批，30 分钟预算内诚实显式假设）：
     den(x) := altsum (fun k => pade_coeff n k * q_pow x k) (n+1)
     （PC2 引擎出口，UpReqAltSumPos.v）；
   逐项非负（pade_coeff_pos）+ 相邻递减
     QleT (c_{k+1} x^{k+1}) (c_k x^k)（0<=x 段）
   喂 altsum_nonneg（QleT 假设面）/ altsum_nonneg_leT（QleT' 面）
   得 QleT' 0 (den x)；首对严格 + 项数 >= 2 时经 altsum_pos_strict
   升 QltT 0（本件 n=1 即其手工实例）；le_head 备 <= c_0 用。
   依赖缺口：相邻递减需 c_k x^k 单调面（x^k/x^{k+1} 比式 + 系数比
   (k+1)(2n-k)/(2(k+1)(n-k)) 型），库内尚无现成件，下一批建。
   本件三引理即 n=0/n=1 手工实例，可作通用件回来核对的锚。 *)

End PadeSignQ.

Print Assumptions pds_qlt0_eq_r.
