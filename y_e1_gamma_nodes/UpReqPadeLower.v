(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 头批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   cpl_sent_exp0（原 L157，1 句玩具证）                                 *)
(*   cpl_sent_s_b2（原 L139，1 句玩具证）                                 *)
(*   cpl_sent_s_b1（原 L136，1 句玩具证）                                 *)
(*   cpl_qlt_eq_sr（原 L85，2 句玩具证）                                  *)
(*   cpl_qmult_comp（原 L80，2 句玩具证）                                 *)
(*   cpl_qminus_comp（原 L77，2 句玩具证）                                *)
(*   cpl_qplus_comp（原 L74，2 句玩具证）                                 *)
(*   cpl_qlt_eq_l（原 L66，2 句玩具证）                                   *)
(*   cpl_qlt0_eq_r（原 L59，2 句玩具证）                                  *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeLower.v *)
(* *)
(* 目的： Padé [2/2] 免除法正尾下界（误差界装配切片）。 *)
(* 主件： cpl_qpow_pos / cpl_sq_nonneg 与正尾下界构造（数值实证 n=2）。 *)
(* 依赖： CW_ConstructiveWorld_219、UpReqPadeExp、UpReqQExpTail、UpReqPadeQLeg。 *)
(* 备注： 语句面取 real_lt sigT 见证形，免除法（乘积面）；免积分第三形态。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqPadeLower.v —— C-S1：Padé [2/2] 免除法正尾下界（误差界装配切片③） *)
(* 日期：                                                *)
(*                                                                 *)
(* 任务定位：侦察报告 attn/_tcs1_侦察报告-.md 结论【直通】的   *)
(*   执行件。施工依据 attn/_tcs4_ 误差界卷 依赖闸门实测：             *)
(*   UpReqPadeTailPos / UpReqPadeBetaPos 未落盘（闸门0不过）——        *)

(*                                                                 *)
(* 数学内核（免积分第三形态，数值实证 n=2）：                         *)
(*   e^y·Q₂(y) − P₂(y) = (e^y − E₆)·Q₂ + (E₆·Q₂ − P₂)，其中          *)
(*   E₆·Q₂ − P₂ == y⁵/720 + y⁶/1440 + y⁸/8640（Q 层符号 y 恒等式），   *)
(*   尾项全非负且 y⁶/1440 > 0（y>0）⟹ e^y·Q₂ − P₂ > y⁵/720。          *)
(*   见证：eps := y⁵/720（=β₀·y^(2n+1)，β₀=(2!)²/(4!·5!)=1/720，      *)
(*   与 S1 检验经典式同值；总纲 §1.3 的额外 /(2n)! 因子系笔误，   *)
(*   以 S1 实测为准）。N := 6（截断指数安全位：M=5 时 y⁶ 系数 −1/1440  *)
(*   为负、M=6 起无损伤——S1 报告②-4 截断损伤警示）。                  *)
(*                                                                 *)
(* 语句面：real_lt sigT 见证形（S02:455），免除法（乘积面），          *)
(*   正性全走 QltT/Qlt 见证形——LPO 墙规避（判例 逐点可判定口径），     *)
(*   零经典极限/积分性质。奇 n 对偶（上界）对称显式假设，禁特设构造。          *)
(*                                                                 *)
(* 使用面：CW_ConstructiveWorld_219（S01 NatLe_drop/S02 real_lt       *)
(*   real_mult_proj real_const_proj QltT_to_Qlt Qlt_to_QltT /        *)
(*   S03 exp_partial q_pow q_fact q_fact_pos）；UpReqPadeExp          *)
(*   （pade_num/pade_den/pade_coeff）；UpReqQExpTail（qtail_le_plus_r）。*)

(*   -Q . "" UpReqPadeLower.v（PC 卡实测配方；总纲草方 ../001 无       *)

(* 公理面：主件 Print Assumptions 预期 Closed（无公理依赖）。          *)
(* 数值锚值（核对总纲 §1.4，S1 检验实测）：                            *)
(*   S-b: pade_num 1 (1#2)==5#4、pade_den 1 (1#2)==3#4（直引 PC 数值锚）； *)
(*   G6 恒等式 y=1/2: 121/2211840、y=1: 19/8640（fractions 精确）；    *)
(*   见证 y=1/2: (1#2)^5/720 == 1#23040；n=0 退化: exp_partial 0 == 1， *)
(*   P₀=Q₀=1（pade_num_0_one/pade_den_0_one 既有）。                   *)
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
Require Import UpReqQExpTail.
Require Import UpReqPadeQLeg.
From Stdlib Require Import QArith.QArith Arith.Arith Lia Setoid.

Section PadeLower.

(* ===== B0 桥接引理（Qeq→Qlt 传桥；AA12 肢化：自建 Q 单调肢一跳，
   不引入 Psatz/micromega 环境闭包；语句面全不变） ===== *)

(* 等值右传桥：a==b 时 0<a 传给 0<b（pds_qlt0_eq_r 同款证法，自持零依赖）。 *)
Lemma cpl_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  exact (pql_qlt0_eq_r a b Hab Ha).
Qed.

(* 等值左传桥：x==a 时 x<b 传给 a<b（主件严格项重写用）。 *)
Lemma cpl_qlt_eq_l : forall x a b : Q, x == a -> Qlt x b -> Qlt a b.
Proof.
  intros x a b Hxa Hlt.
  exact (pql_qlt_eq_l x a b Hxa Hlt).
Qed.

(* Qeq 加/减/乘组合件：stdlib QArith_base 的 Proper Instance 直接当函数用 *)
(* （实测名位：Qplus_comp:467 / Qminus_comp:493 / Qmult_comp:500），零 nia。 *)
Lemma cpl_qplus_comp : forall w x y z : Q, w == x -> y == z -> w + y == x + z.
Proof. intros w x y z H1 H2. apply Qplus_comp; assumption. Qed.

Lemma cpl_qminus_comp : forall w x y z : Q, w == x -> y == z -> w - y == x - z.
Proof. intros w x y z H1 H2. apply Qminus_comp; assumption. Qed.

Lemma cpl_qmult_comp : forall w x y z : Q, w == x -> y == z -> w * y == x * z.
Proof. intros w x y z H1 H2. apply Qmult_comp; assumption. Qed.

(* 严格右传桥（x 起点）：a==b ⟹ Qlt x a -> Qlt x b。
   AA12 肢化：一跳 pql_qlt_eq_r（原注记「零 nia」目标至此真兑现）。 *)
Lemma cpl_qlt_eq_sr : forall (x a b : Q), a == b -> Qlt x a -> Qlt x b.
Proof.
  intros x a b Hab Ha.
  exact (pql_qlt_eq_r a b x Hab Ha).
Qed.

(* 幂非负：0<=y ⟹ 0<=y^k（逐项非负的单调性链基础模块）。 *)
Lemma cpl_qpow_nonneg : forall (y : Q) (k : nat), Qle 0 y -> Qle 0 (q_pow y k).
Proof.
  intros y k Hy. induction k as [| k IH].
  - change (q_pow y 0%nat) with 1%Q. apply Qle_0_1.
  - change (q_pow y (Datatypes.S k)) with (y * q_pow y k).
    apply Qmult_le_0_compat.
    + exact Hy.
    + exact IH.
Qed.

(* 幂严格正：0<y ⟹ 0<y^k（见证严格性来源）。 *)
Lemma cpl_qpow_pos : forall (y : Q) (k : nat), Qlt 0 y -> Qlt 0 (q_pow y k).
Proof.
  intros y k Hy. induction k as [| k IH].
  - change (q_pow y 0%nat) with 1%Q. unfold Qlt. simpl. lia.
  - change (q_pow y (Datatypes.S k)) with (y * q_pow y k).
    apply Qmult_lt_0_compat.
    + exact Hy.
    + exact IH.
Qed.

(* 严格传非严格：Qlt x y -> Qle x y（自持桥，Qlt/Qle 同 Z 展开式）。 *)
Lemma cpl_qlt_le : forall x y : Q, Qlt x y -> Qle x y.
Proof.
  intros x y H. unfold Qlt, Qle in *.
  destruct x as [nx dx]. destruct y as [ny dy]. simpl in *. lia.
Qed.

(* 平方非负：Q 序逐点可判定（Qlt_le_dec），非 LPO 面；负支走 −t·−t 对偶。 *)
Lemma cpl_sq_nonneg : forall t : Q, Qle 0 (t * t).
Proof.
  intro t. destruct t as [tn td].
  destruct (Qlt_le_dec 0 (tn#td)) as [Hlt | Hle].
  - apply cpl_qlt_le. apply Qmult_lt_0_compat; exact Hlt.
  - assert (Hnn : Qle 0 (- (tn#td))).
    { unfold Qle, Qopp in *. simpl in Hle |- *. lia. }
    apply (Qle_trans 0 ((- (tn#td)) * (- (tn#td))) ((tn#td) * (tn#td))).
    + apply Qmult_le_0_compat; exact Hnn.
    + apply qeq_le. ring.
Qed.

(* ===== B1 数值锚件（总纲 §1.4 核对；字面量点 vm_compute——CS 卡数值锚纪律） ===== *)

(* S-b：PC 数值锚直引（系数公式+有界和+交错符号端到端）。 *)
Lemma cpl_sent_s_b1 : pade_num 1%nat (1#2) == (5#4).
Proof. exact pade_num_1_half. Qed.

Lemma cpl_sent_s_b2 : pade_den 1%nat (1#2) == (3#4).
Proof. exact pade_den_1_half. Qed.

(* G6 恒等式数值交叉（S1 检验 fractions 精确值）。 *)
Lemma cpl_sent_g6_half : exp_partial 6%nat (1#2) * pade_den 2%nat (1#2)
                         - pade_num 2%nat (1#2) == (121#2211840).
Proof. vm_compute. reflexivity. Qed.

Lemma cpl_sent_g6_one : exp_partial 6%nat (1#1) * pade_den 2%nat (1#1)
                        - pade_num 2%nat (1#1) == (19#8640).
Proof. vm_compute. reflexivity. Qed.

(* 见证数值：β₀·y⁵ = (1#720)·(1#2)^5 = 1#23040。 *)
Lemma cpl_sent_witness_half : q_pow (1#2) 5%nat / 720 == (1#23040).
Proof. vm_compute. reflexivity. Qed.

(* n=0 退化：E₀==1（P₀=Q₀=1 即 e^y−1 >= y 面，pade_num_0_one/ *)
(* pade_den_0_one 既有直引，此处补部分和基例数值锚）。 *)
Lemma cpl_sent_exp0 : forall y : Q, exp_partial 0%nat y == 1%Q.
Proof. intro y. exact (Qeq_refl 1%Q). Qed.

(* ===== B2 Q 层主代数 ===== *)

(* 分母 n=2 闭式展开（接口缺口件一：pdp_den_pos 只覆盖 [0,1]， *)
(* 本件配方实例给全 y>0——Q₂(y)=1−y/2+y²/12=((y−3)²+3)/12>0）。 *)
Lemma cpl_den2_expl : forall y : Q,
  pade_den 2%nat y == 1%Q + (- (1#2)%Q) * y + (1#12)%Q * (y * y).
Proof.
  intro y.
  unfold pade_den, pade_coeff.
  cbn [sum_upto q_pow q_fact Z.of_nat Nat.sub Nat.mul Nat.add]. cbv beta.
  field.
Qed.

Lemma cpl_den2_pos : forall y : Q, Qlt 0 y -> Qlt 0 (pade_den 2%nat y).
Proof.
  intros y Hy.
  assert (Hexpl : pade_den 2%nat y == 1%Q + (- (1#2)%Q) * y + (1#12)%Q * (y * y))
    by (apply cpl_den2_expl).
  (* 12·显式形 == (y−3)²+3 > 0 *)
  assert (H12 : Qlt 0 (12 * (1%Q + - (1#2)%Q * y + (1#12)%Q * (y * y)))).
  { apply (cpl_qlt0_eq_r ((y + -3) * (y + -3) + 3)
                         (12 * (1 + - (1#2) * y + (1#12) * (y * y)))).
    - field.
    - assert (Hsq : Qle 0 ((y + -3) * (y + -3))) by (apply cpl_sq_nonneg).
      assert (H3 : Qlt 0 3%Q) by (unfold Qlt; simpl; lia).
      apply (cpl_qlt0_eq_r (3 + (y + -3) * (y + -3))%Q
                           ((y + -3) * (y + -3) + 3)%Q).
      + ring.
      + apply (Qlt_le_trans 0 3%Q (3 + (y + -3) * (y + -3))%Q).
        * exact H3.
        * apply (qtail_le_plus_r 3%Q ((y + -3) * (y + -3))). exact Hsq. }
  (* Qlt 0 ((12·E)·(1/12)) ⟹ Qlt 0 E ⟹ Qlt 0 pade_den（右传桥链） *)
  apply (cpl_qlt0_eq_r ((12 * (1 + - (1#2) * y + (1#12) * (y * y))) * (1#12))
                       (pade_den 2%nat y)).
  - transitivity (1%Q + - (1#2)%Q * y + (1#12)%Q * (y * y)).
    + unfold Qdiv. field.
    + apply Qeq_sym. exact Hexpl.
  - apply (Qmult_lt_0_compat _ (1#12)).
    + exact H12.
    + unfold Qlt. simpl. lia.
Qed.

(* 部分和步进非降：0<=y ⟹ E_m <= E_{m+1}（识别件 Q 层半区）。 *)
Lemma cpl_ep_step_le : forall (y : Q) (m : nat),
  Qle 0 y -> Qle (exp_partial m y) (exp_partial (Datatypes.S m) y).
Proof.
  intros y m Hy.
  change (exp_partial (Datatypes.S m) y)
    with (exp_partial m y + q_pow y (Datatypes.S m) / q_fact (Datatypes.S m)).
  apply (qtail_le_plus_r (exp_partial m y) (q_pow y (Datatypes.S m) / q_fact (Datatypes.S m))).
  unfold Qdiv. apply Qmult_le_0_compat.
  - apply (cpl_qpow_nonneg y (Datatypes.S m) Hy).
  - apply cpl_qlt_le. apply (Qinv_lt_0_compat (q_fact (Datatypes.S m))).
    apply q_fact_pos.
Qed.

(* 部分和单调：0<=y ∧ a<=b ⟹ E_a <= E_b（主件 N:=6 槽的 Q 层内核）。 *)
Lemma cpl_ep_mono : forall (y : Q) (a b : nat),
  Qle 0 y -> (a <= b)%nat -> Qle (exp_partial a y) (exp_partial b y).
Proof.
  intros y a b Hy Hab.
  revert a Hab. induction b as [| b' IH].
  - intros a Hab. assert (Ha0 : a = 0%nat) by lia. subst a. apply Qle_refl.
  - intros a Hab. destruct (Nat.eq_dec a (Datatypes.S b')) as [Heq | Hne].
    + rewrite Heq. apply Qle_refl.
    + assert (Hab' : (a <= b')%nat) by lia.
      apply (Qle_trans _ (exp_partial b' y)).
      * apply IH. exact Hab'.
      * apply (cpl_ep_step_le y b' Hy).
Qed.

(* 核心恒等式（接口缺口件二：E₆·Q₂−P₂ 免积分正尾多项式； *)
(* S1 检验 500 随机 Q 点 fractions 全验 + 数值锚 B1 双点交叉）。 *)
Lemma cpl_g6_identity : forall y : Q,
  exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y ==
  q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640.
Proof.
  intro y.
  unfold pade_den, pade_num, pade_coeff.
  cbn [exp_partial sum_upto q_pow q_fact Z.of_nat Nat.sub Nat.mul Nat.add]. cbv beta.
  field.
Qed.

(* 幂逐点外延：a==b ⟹ y^k 合同（Qmult_comp 逐层）。 *)
Lemma cpl_qpow_ext : forall (k : nat) (a b : Q), a == b -> q_pow a k == q_pow b k.
Proof.
  intros k a b Hab. induction k as [| k IH].
  - reflexivity.
  - apply Qmult_comp.
    + exact Hab.
    + exact IH.
Qed.

(* 部分和逐点外延：a==b ⟹ E_m(a)==E_m(b)（Hc 抬升进 exp_partial 用）。 *)
Lemma cpl_ep_ext : forall (m : nat) (a b : Q), a == b -> exp_partial m a == exp_partial m b.
Proof.
  intros m a b Hab. induction m as [| m IH].
  - reflexivity.
  - apply Qplus_comp.
    + exact IH.
    + unfold Qdiv. apply cpl_qmult_comp.
      * change (q_pow a (Datatypes.S m)) with (a * q_pow a m).
        change (q_pow b (Datatypes.S m)) with (b * q_pow b m).
        apply cpl_qmult_comp.
        -- exact Hab.
        -- exact (cpl_qpow_ext m a b Hab).
      * apply Qeq_refl.
Qed.

(* ===== C Real 层主件（cpl_lower_even：免除法 real_lt sigT 见证形） ===== *)

(* 语句：e^y·Q₂(y) − P₂(y) > β₀·y⁵（β₀=1/720），sigT 见证
   eps := y⁵/720、N := 6 显式可计算；real_lt 内部 Q 减法自带，
   零除法面。派生语义：P₂>0 ∧ Q₂>0 ⟹ 0 < e^y 且 e^y > P₂/Q₂。 *)
Theorem cpl_lower_even : forall y : Q,
  QltT 0 y ->
  real_lt (real_const (pade_num 2%nat y))
          (real_mult (cauchy_real_exp (real_const y)) (real_const (pade_den 2%nat y))).
Proof.
  intros y Hy.
  assert (Hylt : Qlt 0 y) by (apply QltT_to_Qlt; exact Hy).
  assert (Hy0 : Qle 0 y) by (apply cpl_qlt_le; exact Hylt).
  (* 先例：逐 eps 直构——real_const 打开、投影逐点归约 *)
  assert (Hc : forall k, projT1 (real_const y) k == y) by (intro k; apply real_const_proj).
  destruct (real_const y) as [u Hu] eqn:Eu.
  (* destruct 已连带重写 Hc 中的 real_const y——直接投影归约 *)
  cbn [projT1] in Hc.
  unfold real_lt.
  exists (q_pow y 5%nat / 720)%Q.
  split.
  - (* 见证正性：0 < y⁵/720 *)
    apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat (q_pow y 5%nat) (1#720)).
    + apply (cpl_qpow_pos y 5%nat Hylt).
    + apply (Qinv_lt_0_compat (720#1)). unfold Qlt. simpl. lia.
  - exists 6%nat.
    intros m Hm.
    assert (Hle : (6 <= m)%nat) by (apply NatLe_drop; exact Hm).
    (* 投影装配走 qeq 桥（EXPADD4 卡：QltT 面禁 rewrite、setoid 实例断档—— *)
    (* 自持 Qeq 组合件 + 全显式 Qeq_trans；S02:1301 real_mult_proj / S02:1313 real_const_proj） *)
    assert (Hexp : projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                   == exp_partial m (u m)).
    { unfold cauchy_real_exp. reflexivity. }
    assert (Hexp2 : projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    == exp_partial m y)
      by (apply (Qeq_trans _ (exp_partial m (u m)) _ Hexp (cpl_ep_ext m (u m) y (Hc m)))).
    assert (HDe : projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                    (real_const (pade_den 2%nat y))) m
                    - projT1 (real_const (pade_num 2%nat y)) m
                  == exp_partial m y * pade_den 2%nat y - pade_num 2%nat y).
    { apply (Qeq_trans _
              (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                 * projT1 (real_const (pade_den 2%nat y)) m
                 - projT1 (real_const (pade_num 2%nat y)) m) _).
      - apply (cpl_qminus_comp
                 (projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                    (real_const (pade_den 2%nat y))) m)
                 (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    * projT1 (real_const (pade_den 2%nat y)) m)).
        + apply (real_mult_proj (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                (real_const (pade_den 2%nat y)) m).
        + apply Qeq_refl.
      - apply (cpl_qminus_comp
                 (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m
                    * projT1 (real_const (pade_den 2%nat y)) m)
                 (exp_partial m y * pade_den 2%nat y)).
        + apply (cpl_qmult_comp
                   (projT1 (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu)) m)
                   (exp_partial m y)
                   (projT1 (real_const (pade_den 2%nat y)) m) (pade_den 2%nat y)).
          * exact Hexp2.
          * apply (real_const_proj (pade_den 2%nat y) m).
        + apply (real_const_proj (pade_num 2%nat y) m). }
    assert (Hchain : Qlt (q_pow y 5%nat / 720)
                       (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y)).
    { (* Q 层完成链（Prop 证内） *)
    assert (Hident : exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y ==
                     q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)
      by (apply cpl_g6_identity).
    assert (Hmono : Qle (exp_partial 6%nat y) (exp_partial m y))
      by (apply (cpl_ep_mono y 6%nat m Hy0 Hle)).
    assert (Hden : Qle 0 (pade_den 2%nat y))
      by (apply cpl_qlt_le; apply (cpl_den2_pos y Hylt)).
    assert (Hstep1 : Qle (exp_partial 6%nat y * pade_den 2%nat y)
                         (exp_partial m y * pade_den 2%nat y))
      by (apply (Qmult_le_compat_r _ _ (pade_den 2%nat y)); assumption).
    assert (Hstep2 : Qle (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y)
                         (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y))
      by (apply (proj2 (Qplus_le_l _ _ (- pade_num 2%nat y))); exact Hstep1).
    assert (Hstep3 : Qle (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)
                         (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y))
      by (apply (Qle_trans _ (exp_partial 6%nat y * pade_den 2%nat y - pade_num 2%nat y));
          [apply qeq_le; apply Qeq_sym; exact Hident | exact Hstep2]).
    (* 严格项：0 < y⁶/1440 ⟹ A < A + y⁶/1440 *)
    assert (Hb : Qlt 0 (q_pow y 6%nat / 1440)).
    { unfold Qdiv. apply Qmult_lt_0_compat.
      - apply (cpl_qpow_pos y 6%nat Hylt).
      - apply (Qinv_lt_0_compat (1440#1)). unfold Qlt. simpl. lia. }
    assert (Hc1 : Qlt (q_pow y 5%nat / 720)
                      (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720)).
    { apply (cpl_qlt_eq_l (0 + q_pow y 5%nat / 720)%Q).
      - ring.
      - apply (proj2 (Qplus_lt_l 0%Q (q_pow y 6%nat / 1440) (q_pow y 5%nat / 720))).
        exact Hb. }
    assert (Hswap : Qle (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720)
                        (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440))
      by (apply qeq_le; ring).
    apply (Qlt_le_trans _ (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440)).
    - exact (Qlt_le_trans _ (q_pow y 6%nat / 1440 + q_pow y 5%nat / 720) _ Hc1 Hswap).
    - apply (Qle_trans _ (q_pow y 5%nat / 720 + q_pow y 6%nat / 1440 + q_pow y 8%nat / 8640)).
      + apply (qtail_le_plus_r _ (q_pow y 8%nat / 8640)).
        unfold Qdiv. apply Qmult_le_0_compat.
        * apply (cpl_qpow_nonneg y 8%nat Hy0).
        * apply cpl_qlt_le. apply (Qinv_lt_0_compat (8640#1)). unfold Qlt. simpl. lia.
      + exact Hstep3.
    }
    assert (Hpt : Qlt (q_pow y 5%nat / 720)
                      (projT1 (real_mult (cauchy_real_exp (existT (fun s : Qseq => cauchy s) u Hu))
                                          (real_const (pade_den 2%nat y))) m
                        - projT1 (real_const (pade_num 2%nat y)) m)).
    { apply (cpl_qlt_eq_sr (q_pow y 5%nat / 720)
              (exp_partial m y * pade_den 2%nat y - pade_num 2%nat y)).
      - exact (Qeq_sym _ _ HDe).
      - exact Hchain. }
    apply Qlt_to_QltT. exact Hpt.
Qed.

End PadeLower.
