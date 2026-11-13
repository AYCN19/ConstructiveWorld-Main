(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqBanachInst.v —— INS：BanachAlg （）    *)
(* ============================================================ *)
(* 使命：为冻结类 BanachAlg（UpReqBanachExp.v，实例为零）落地第一个 *)
(*   具体实例。实形普查已证结论：墙不在 bcauchy_complete（BCE 已证结论），   *)
(*   而在 bnorm 字段族：bnorm_wd 余域是 Id（ML 恒等型），bnorm_coef *)
(*   把标量范数 Leibniz-钉死为 Qabs q。三载体全数受阻：             *)
(*   (a) Q 载体 + QeqT 等词：2#4 == 1#2 可证，wd+coef 强逼          *)
(*       Id (2#4) (1#2) 假等式（S3 墙一，机器形式化）；             *)
(*   (b) Q 载体 + Leibniz 等词：bplus_opp 撞分母规范化墙            *)
(*       （Id (0#16) (0#1) 型假等式，S3 墙二，机器形式化）；         *)
(*   (c) Real 载体：real_eq 不变性的 Q 值函数=商映射，早项扰动反例   *)
(*       （v := (10,0,0,..) 与 const 0 real_eq 而 witness 界不同）   *)
(*       击穿一切可计算候选；上界近似（real_norm_bounded）给值但     *)
(*       给不出 Id-良定性——LPO 墙之上的更强 Id-余域墙。             *)
(* 本件承载（全 Set 面，纯构造）：                                 *)
(*   S1 = 类内正件：任意 B 的 1/n 标量柯西列（全链首件具体柯西      *)
(*        见证，只用 bnorm_plus/opp/coef + Q 算术）+ 完备性强制      *)
(*        极限元（bcauchy_complete 逐字段 discharge 演示）；        *)
(*   S2 = 两堵墙的机器形式化（Implication 面，不落 Prop 终面）；     *)
(*   S3 = BanachAlgPre 37 字段记录 + 完备性缺口感装配桥              *)
(*        （Pre + 完备性 -> 完整 BanachAlg，机器核验唯一缺口）。     *)
(* 降档声明：完整 Q/Real 实例因 S2 墙不可达（禁特设构造），墙的消解=     *)
(*   上游手术（bnorm : BA -> Real，或 bnorm_wd 余域弱化为 Qeq 型）   *)
(*   ——详见交付报告实例设计单。                                     *)
(* 铁律自审：零公理零遗留零中断；语句面零 Prop；冻结类未动一字；      *)
(*   前缀 bxin_ 全库零撞名。                                        *)
(* 工程注：Rocq 9 无 Pos2Z.inj_le/Z.mul_le_mono_l 旧名；positive 桥  *)
(*   一律走 lia（zify 内建 positive 实例），Z 假设形直传。           *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：Id 与 QeqT/Qle 的迁移小工具（Id 非 setoid，显式桥）         *)
(* ============================================================ *)

(* ML 恒等单侧保 Qle：Id x y -> Qle z x -> Qle z y *)
Lemma bxin_id_qle_r : forall x y z : Q, Id x y -> Qle z x -> Qle z y.
Proof. intros x y z H Hle. destruct H. exact Hle. Qed.

(* 1/p ≤ 1/r（正分母反比单调；Z 层序假设直传） *)
Lemma bxin_qinv_le : forall p r : positive,
  (Z.pos r <= Z.pos p)%Z -> Qle (1#p)%Q (1#r)%Q.
Proof.
  intros p r Hrp.
  assert (H1 : (1 <= Z.pos r)%Z) by lia.
  unfold Qle. simpl. lia.
Qed.

(* 两项和界：p,q ≥ r >= 1 -> 1/p + 1/q ≤ 2/r *)
Lemma bxin_qsum_bound : forall p q r : positive,
  (Z.pos r <= Z.pos p)%Z -> (Z.pos r <= Z.pos q)%Z ->
  Qle (Qplus (1#p)%Q (1#q)%Q) (2#r)%Q.
Proof.
  intros p q r Hp Hq.
  eapply Qle_trans with (y := (Qplus (1#r)%Q (1#r)%Q)).
  - apply Qplus_le_compat.
    + apply (bxin_qinv_le p r Hp).
    + apply (bxin_qinv_le q r Hq).
  - apply qeq_imp_qle. unfold Qeq, Qplus.
    change ((Z.pos r + Z.pos r) * Z.pos r = Z.pos 2 * (Z.pos r * Z.pos r))%Z.
    ring.
Qed.

(* nat -> positive 桥：Z 层逐字等式（定义级，destruct 即闭） *)
Lemma bxin_zpos_succ_nat : forall n : nat,
  Z.pos (Pos.of_succ_nat n) = Z.succ (Z.of_nat n).
Proof. intros [|n]. lia. lia. Qed.

(* ============================================================ *)
(* S1：类内正件 —— 任意 BanachAlg 的标量柯西列与完备性强制极限    *)
(* （只用类字段 bnorm_plus/bnorm_opp/bnorm_coef + Q 算术；        *)
(*   全链首件非泛型具体柯西见证：v n := bcoef (1/(n+1))。）        *)
(* ============================================================ *)

Lemma bxin_scalar_seq_cauchy : forall B : BanachAlg,
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (@bnorm B
        (@bplus B (@bcoef B (1#(Pos.of_succ_nat m))%Q)
                  (@bopp B (@bcoef B (1#(Pos.of_succ_nat n))%Q)))) eps).
Proof.
  intros B eps Heps.
  (* 阿基米德步：0 < eps = a#b 给出界 L := 4b（positive） *)
  destruct eps as [a b].
  assert (Hlt0 : Qlt 0 (a#b)%Q) by (apply QltT_to_Qlt; exact Heps).
  unfold Qlt in Hlt0. simpl in Hlt0.
  (* Hlt0 : (0 < a * Z.pos 1)%Z *)
  assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
  assert (Ha1 : (1 <= a)%Z).
  { assert (E : (a * Z.pos 1 = a)%Z) by ring. rewrite E in Hlt0. lia. }
  assert (Hmul : Z.pos (4 * b)%positive = (Z.pos 4 * Z.pos b)%Z) by lia.
  assert (HmL : (2 * Z.pos b < a * Z.pos (4 * b)%positive)%Z).
  { rewrite Hmul. nia. }
  exists (Z.to_nat (Z.pos (4 * b)%positive)).
  intros m n Hm Hn.
  assert (Hmle : (Z.to_nat (Z.pos (4 * b)%positive) <= m)%nat)
    by (apply (NatLe_drop _ _ Hm)).
  assert (Hnle : (Z.to_nat (Z.pos (4 * b)%positive) <= n)%nat)
    by (apply (NatLe_drop _ _ Hn)).
  assert (HmZ : (Z.pos (4 * b)%positive <= Z.of_nat m)%Z) by lia.
  assert (HnZ : (Z.pos (4 * b)%positive <= Z.of_nat n)%Z) by lia.
  assert (HpLm : (Z.pos (4 * b)%positive <= Z.pos (Pos.of_succ_nat m))%Z).
  { rewrite bxin_zpos_succ_nat. lia. }
  assert (HpLn : (Z.pos (4 * b)%positive <= Z.pos (Pos.of_succ_nat n))%Z).
  { rewrite bxin_zpos_succ_nat. lia. }
  (* Q 层链：‖v_m − v_n‖ ≤ |1/pm| + |1/pn| ≤ 2/(4b) < a#b *)
  assert (Hle : Qle
    (@bnorm B (@bplus B (@bcoef B (1#(Pos.of_succ_nat m))%Q)
                        (@bopp B (@bcoef B (1#(Pos.of_succ_nat n))%Q))))
    (Qplus (1#(Pos.of_succ_nat m)%Q) (1#(Pos.of_succ_nat n)%Q))).
  { assert (HQsum : (@bnorm B (@bcoef B (1#(Pos.of_succ_nat m))%Q)
                     + @bnorm B (@bopp B (@bcoef B (1#(Pos.of_succ_nat n))%Q)))%Q
                    == (Qabs (1#(Pos.of_succ_nat m)%Q)
                        + Qabs (1#(Pos.of_succ_nat n)%Q))%Q).
    { apply Qplus_comp.
      - apply bnorm_coef_qeq.
      - rewrite (@bnorm_opp B (@bcoef B (1#(Pos.of_succ_nat n))%Q)).
        apply bnorm_coef_qeq. }
    eapply Qle_trans with
      (y := (@bnorm B (@bcoef B (1#(Pos.of_succ_nat m))%Q)
              + @bnorm B (@bopp B (@bcoef B (1#(Pos.of_succ_nat n))%Q)))%Q).
    - (* bnorm_plus 次可加 *)
      apply QleT'_to_Qle. apply bnorm_plus.
    - (* Qeq 换底（原 id_cong2 Id 链的 Qeq 面替代，CLS-R ⑤思路落地） *)
      apply qeq_le. exact HQsum. }
  apply Qlt_to_QltT.
  eapply Qle_lt_trans with (y := (2#(4 * b)%positive)%Q).
  - eapply Qle_trans with (y := (Qplus (1#(Pos.of_succ_nat m)%Q) (1#(Pos.of_succ_nat n)%Q))).
    + exact Hle.
    + exact (bxin_qsum_bound (Pos.of_succ_nat m) (Pos.of_succ_nat n)
                             (4 * b)%positive HpLm HpLn).
  - exact HmL.
Qed.

(* 完备性字段强制极限元：任何（未来）实例都内含 1/n 序列的极限。 *)
(* 这是「完备标量副本构造性强制」的机器形态——非空叙事的承载点。 *)
Lemma bxin_scalar_limit_exists : forall B : BanachAlg,
  sigT (fun l : (@BA B) =>
    forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall n : nat,
        NatLe N n ->
        QltT (@bnorm B (@bplus B (@bcoef B (1#(Pos.of_succ_nat n))%Q)
                                 (@bopp B l))) eps)).
Proof.
  intros B.
  apply (@bcauchy_complete B (fun n => @bcoef B (1#(Pos.of_succ_nat n))%Q)).
  intros eps Heps.
  exact (bxin_scalar_seq_cauchy B eps Heps).
Qed.

(* 标量范数钉定检验：bnorm_coef 把 bcoef q 的范数逐点钉为 Qabs q。 *)
(* 离散范数否证的类内承载：q := 1/2 处钉值为 1#2，离散值 1 直接矛盾。 *)
Lemma bxin_bnorm_coef_pin : forall (B : BanachAlg) (q : Q),
  QeqT (@bnorm B (@bcoef B q)) (Qabs q).
Proof. intros B q. apply bnorm_coef. Qed.

(* 冒烟自测恒等面：bxin_bone_is_one 型（类内恒等，bcoef 1 ~ bone） *)
Lemma bxin_bone_is_one : forall B : BanachAlg,
  @bae B (@bcoef B 1%Q) (@bone B).
Proof. intros B. apply bcoef_one. Qed.

(* ============================================================ *)
(* S2：两堵墙的机器形式化（Implication 面，结论全 Set 型，禁 Prop） *)
(* ============================================================ *)

(* 2#4 == 1#2（QeqT 层可证：交叉乘 4 = 4，Qcompare 计算闭合） *)
Lemma bxin_qeqT_quarter_half : QeqT (2#4)%Q (1#2)%Q.
Proof. unfold QeqT. reflexivity. Qed.

(* 墙一（QeqT 载体）：bnorm_wd(Id 余域) + bnorm_coef 联手强逼          *)
(* Id (2#4) (1#2) —— 经 Qnum/QDen 注入即 2=1 型矛盾。任何 Q 载体模型   *)
(* 若等词取 QeqT，范数字段族即不可满足。                              *)
Lemma bxin_Q_bnorm_wall : forall (bn : Q -> Q),
  (forall a b : Q, QeqT a b -> Id (bn a) (bn b)) ->
  (forall q : Q, Id (bn q) (Qabs q)) ->
  Id (2#4)%Q (1#2)%Q.
Proof.
  intros bn Hwd Hpin.
  pose proof (Hwd (2#4)%Q (1#2)%Q bxin_qeqT_quarter_half) as H1.
  pose proof (Hpin (2#4)%Q) as H2.
  pose proof (Hpin (1#2)%Q) as H3.
  exact (id_trans (id_trans (id_sym H2) H1) H3).
Qed.

(* 墙二（Leibniz 载体）：bplus_opp 字段强逼分母规范化假等式。          *)
(* Q 值加法不约分：2#4 + -(2#4) = 0#16 而 bzero = 0#1，Leibniz 等词下  *)
(* Id (0#16) (0#1) 不可证——分母位 16 vs 1 即墙。                      *)
Definition bxin_Q_zero_quarter : Q := Qplus (2#4)%Q (Qopp (2#4)%Q).

Lemma bxin_Q_leibniz_opp_wall :
  Id bxin_Q_zero_quarter (0#1)%Q ->
  Id (QDen bxin_Q_zero_quarter) (QDen (0#1)%Q).
Proof. intros H. exact (id_cong (fun q : Q => QDen q) H). Qed.

(* ============================================================ *)
(* S3：BanachAlgPre 37 字段记录 + 装配桥（完备性缺口感机器化）      *)
(* （字段面逐字承 BanachAlg，仅缺 bcauchy_complete；装配桥证明       *)
(*   Pre + 完备性 -> 完整 BanachAlg：唯一缺口=完备性字段的机器证。）  *)
(* ============================================================ *)

Class bxin_BanachAlgPre := {
  bxin_BA : Set;
  bxin_bae : bxin_BA -> bxin_BA -> Set;
  bxin_bae_refl   : forall a : bxin_BA, bxin_bae a a;
  bxin_bae_sym    : forall a b : bxin_BA, bxin_bae a b -> bxin_bae b a;
  bxin_bae_trans  : forall a b c : bxin_BA,
    bxin_bae a b -> bxin_bae b c -> bxin_bae a c;
  bxin_bzero : bxin_BA;
  bxin_bone : bxin_BA;
  bxin_bplus : bxin_BA -> bxin_BA -> bxin_BA;
  bxin_bmult : bxin_BA -> bxin_BA -> bxin_BA;
  bxin_bopp : bxin_BA -> bxin_BA;
  bxin_bcoef : Q -> bxin_BA;
  bxin_bnorm : bxin_BA -> Q;
  bxin_bplus_assoc : forall a b c : bxin_BA,
    bxin_bae (bxin_bplus a (bxin_bplus b c)) (bxin_bplus (bxin_bplus a b) c);
  bxin_bplus_comm  : forall a b : bxin_BA,
    bxin_bae (bxin_bplus a b) (bxin_bplus b a);
  bxin_bplus_zero  : forall a : bxin_BA, bxin_bae (bxin_bplus a bxin_bzero) a;
  bxin_bplus_opp   : forall a : bxin_BA,
    bxin_bae (bxin_bplus a (bxin_bopp a)) bxin_bzero;
  bxin_bmult_assoc : forall a b c : bxin_BA,
    bxin_bae (bxin_bmult a (bxin_bmult b c)) (bxin_bmult (bxin_bmult a b) c);
  bxin_bmult_one_l : forall a : bxin_BA, bxin_bae (bxin_bmult bxin_bone a) a;
  bxin_bmult_one_r : forall a : bxin_BA, bxin_bae (bxin_bmult a bxin_bone) a;
  bxin_bdistrib_l  : forall a b c : bxin_BA,
    bxin_bae (bxin_bmult a (bxin_bplus b c))
             (bxin_bplus (bxin_bmult a b) (bxin_bmult a c));
  bxin_bdistrib_r  : forall a b c : bxin_BA,
    bxin_bae (bxin_bmult (bxin_bplus a b) c)
             (bxin_bplus (bxin_bmult a c) (bxin_bmult b c));
  bxin_bmult_zero  : forall a : bxin_BA,
    bxin_bae (bxin_bmult a bxin_bzero) bxin_bzero;
  bxin_bplus_wd : forall a b c d : bxin_BA,
    bxin_bae a c -> bxin_bae b d -> bxin_bae (bxin_bplus a b) (bxin_bplus c d);
  bxin_bmult_wd : forall a b c d : bxin_BA,
    bxin_bae a c -> bxin_bae b d -> bxin_bae (bxin_bmult a b) (bxin_bmult c d);
  bxin_bopp_wd  : forall a b : bxin_BA,
    bxin_bae a b -> bxin_bae (bxin_bopp a) (bxin_bopp b);
  bxin_bnorm_wd : forall a b : bxin_BA,
    bxin_bae a b -> QeqT (bxin_bnorm a) (bxin_bnorm b);
  bxin_bcoef_zero : bxin_bae (bxin_bcoef 0%Q) bxin_bzero;
  bxin_bcoef_one  : bxin_bae (bxin_bcoef 1%Q) bxin_bone;
  bxin_bcoef_mult : forall q r : Q,
    bxin_bae (bxin_bcoef (q * r)%Q) (bxin_bmult (bxin_bcoef q) (bxin_bcoef r));
  bxin_bcoef_comm : forall (q : Q) (a : bxin_BA),
    bxin_bae (bxin_bmult a (bxin_bcoef q)) (bxin_bmult (bxin_bcoef q) a);
  (* ----  补丁 B 联动：BCE 二字段 Pre 对偶扩容（37→39）---- *)
  bxin_bcoef_plus : forall q r : Q,
    bxin_bae (bxin_bplus (bxin_bcoef q) (bxin_bcoef r)) (bxin_bcoef (q + r)%Q);
  bxin_bcoef_wd : forall q r : Q, q == r -> bxin_bae (bxin_bcoef q) (bxin_bcoef r);
  bxin_bnorm_zero : Id (bxin_bnorm bxin_bzero) 0%Q;
  bxin_bnorm_one  : Id (bxin_bnorm bxin_bone) 1%Q;
  bxin_bnorm_opp  : forall a : bxin_BA, Id (bxin_bnorm (bxin_bopp a)) (bxin_bnorm a);
  bxin_bnorm_pos  : forall a : bxin_BA, QleT' 0 (bxin_bnorm a);
  bxin_bnorm_plus : forall a b : bxin_BA,
    QleT' (bxin_bnorm (bxin_bplus a b)) (bxin_bnorm a + bxin_bnorm b)%Q;
  bxin_bnorm_mult : forall a b : bxin_BA,
    QleT' (bxin_bnorm (bxin_bmult a b)) (bxin_bnorm a * bxin_bnorm b)%Q;
  bxin_bnorm_coef : forall q : Q, QeqT (bxin_bnorm (bxin_bcoef q)) (Qabs q);
}.

(* Pre 上的完备性语句（与类字段 bcauchy_complete 逐字同构） *)
Definition bxin_pre_complete (p : bxin_BanachAlgPre) : Set :=
  forall (u : nat -> (@bxin_BA p)),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n ->
        QltT (@bxin_bnorm p
          (@bxin_bplus p (u m) (@bxin_bopp p (u n)))) eps)) ->
    sigT (fun l : (@bxin_BA p) => forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall n : nat,
        NatLe N n ->
        QltT (@bxin_bnorm p
          (@bxin_bplus p (u n) (@bxin_bopp p l))) eps)).

(* 装配桥：Pre + 完备性 -> 完整 BanachAlg。 *)
(* 机器核验：除完备性字段外零缺口——后续只需补一个 p 与一份 Hc。 *)
Definition bxin_BanachAlg_of_pre (p : bxin_BanachAlgPre)
  (Hc : bxin_pre_complete p) : BanachAlg.
Proof.
  exact {| BA := @bxin_BA p;
           bae := @bxin_bae p;
           bae_refl := @bxin_bae_refl p;
           bae_sym := @bxin_bae_sym p;
           bae_trans := @bxin_bae_trans p;
           bzero := @bxin_bzero p;
           bone := @bxin_bone p;
           bplus := @bxin_bplus p;
           bmult := @bxin_bmult p;
           bopp := @bxin_bopp p;
           bcoef := @bxin_bcoef p;
           bnorm := @bxin_bnorm p;
           bplus_assoc := @bxin_bplus_assoc p;
           bplus_comm := @bxin_bplus_comm p;
           bplus_zero := @bxin_bplus_zero p;
           bplus_opp := @bxin_bplus_opp p;
           bmult_assoc := @bxin_bmult_assoc p;
           bmult_one_l := @bxin_bmult_one_l p;
           bmult_one_r := @bxin_bmult_one_r p;
           bdistrib_l := @bxin_bdistrib_l p;
           bdistrib_r := @bxin_bdistrib_r p;
           bmult_zero := @bxin_bmult_zero p;
           bplus_wd := @bxin_bplus_wd p;
           bmult_wd := @bxin_bmult_wd p;
           bopp_wd := @bxin_bopp_wd p;
           bnorm_wd := @bxin_bnorm_wd p;
           bcoef_zero := @bxin_bcoef_zero p;
           bcoef_one := @bxin_bcoef_one p;
           bcoef_mult := @bxin_bcoef_mult p;
           bcoef_comm := @bxin_bcoef_comm p;
           bcoef_plus := @bxin_bcoef_plus p;
           bcoef_wd := @bxin_bcoef_wd p;
           bnorm_zero := @bxin_bnorm_zero p;
           bnorm_one := @bxin_bnorm_one p;
           bnorm_opp := @bxin_bnorm_opp p;
           bnorm_pos := @bxin_bnorm_pos p;
           bnorm_plus := @bxin_bnorm_plus p;
           bnorm_mult := @bxin_bnorm_mult p;
           bnorm_coef := @bxin_bnorm_coef p;
           bcauchy_complete := Hc |}.
Defined.

(* 装配桥冒烟：装配产物满足类内恒等面（bxin_bone_is_one 实例化） *)
Lemma bxin_asmoke_bone_is_one : forall (p : bxin_BanachAlgPre)
  (Hc : bxin_pre_complete p),
  @bae (bxin_BanachAlg_of_pre p Hc)
       (@bcoef (bxin_BanachAlg_of_pre p Hc) 1%Q)
       (@bone (bxin_BanachAlg_of_pre p Hc)).
Proof.
  intros p Hc. apply bxin_bone_is_one.
Qed.

(* ============================================================ *)
(* 提取检验（G3 面）                                              *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction bxin_scalar_seq_cauchy bxin_scalar_limit_exists
  bxin_bnorm_coef_pin bxin_bone_is_one bxin_Q_bnorm_wall
  bxin_Q_leibniz_opp_wall bxin_BanachAlg_of_pre.
