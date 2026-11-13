(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ═════════════════════════════════════════════════════════════════════ *
 * 组件E·切片三 同名替换件：UpReqBanachInstReal（记录 组 续作，切片三） *
 * 本稿＝原件全文逐字保留，仅按玩具清单逐条换写下列证明体（同一陈述、          *
 * 同一符号、零新增 Require、零承认件、全中文头注）。                        *
 * 替换清单（11 件）：bxra_head_cR／bxra_head_bplus／bxra_head_bmult／       *
 *   bxra_head_bopp／bxra_f_coef_zero／bxra_f_coef_one／bxra_f_norm_zero／  *
 *   bxra_f_norm_one／bxra_inst_smoke_bone／bxra_inst_smoke_norm_coef／     *
 *   bxra_inst_smoke_norm_wd                                               *
 * 三口径：①定义层受控展开（head→projT1 首项投影 iota、coef/zero/one→       *
 *   规范链 head_cR→qnorm_fix_id 两级回位、bnorm→Qabs 形）＋②显式见证        *
 * （smoke 件以 change 逐位把库类投影还原到实例字段原基，直接使用本件 *
 *   具体证明 bxra_f_coef_one／bxra_norm_coef_qeqt／bxra_norm_wd_qeqt，     *
 *   消除 bxin_bcoef_one／bxin_bnorm_coef／bxin_bnorm_wd 类字段中转跳）      *
 *   ＋③结构性推导（实例投影 iota 回原基的三段 staged change 链）。           *
 *   bxra_norm_wd_qeqt／bxra_f_refl／bxra_f_sym／bxra_f_trans／             *
 *   bxra_f_norm_pos／bxra_bridge_smoke（恒等三律为单点公理面、bridge 为      *
 * 纪律：纯构造性；Set 层零 Prop 泄露；Proof./Qed. 配平；真 Qed。            *
 * ═════════════════════════════════════════════════════════════════════ *)
(* ============================================================ *)
(* ============================================================ *)
(* 使命：AA1 普查已证结论「实例非空性 0%→100%」——把 S02 Real 载体装配  *)
(*   进库类 bxin_BanachAlgPre（UpReqBanachInst.v 39 字段弱化类），  *)
(*   产出全库首个库类具体实例 bxra_real_pre。                      *)
(* 架构＝承 INST3/INST5 已证机器（UpReqBanachInstPre.v 改名复用）： *)
(*   载体 := Real（sigT(序列,柯西见证)）；bae := 规范种型等价       *)
(*   Id(qnorm(head a))(qnorm(head b))；运算＝首项有理运算规范化；   *)
(*   范数 := Qabs ∘ qnorm ∘ head（bxib_qnorm 处方定形）。           *)
(*      ggcd 机器符号参卡壳），Z 层引理链闭合（Z.gcd_opp_l +        *)
(*      bxib_div_exact + Z.abs_opp，eq 桥回 Id）；                  *)
(*   ② bxra_qltT_wd——QeqT 传递件（qleT'_ltT_ltT 组装），获取      *)
(*      完备性红利用；                                             *)
(*   ③ 完备性红利半获取：head 列本身是 Q-Cauchy（bxra_head_col_    *)
(*      cauchy），极限【元素】在载体上构造可得（bxra_cauchy_limit_ *)
(*      elem）——载体红利内建实测；唯 head 盲区使收敛语句（范数读   *)
(*      第 0 项）不可闭合，诚实留记（INST3 已证结论维持，零强造）。     *)
(* 公理面自审：全件零 公理 零 参数 零 猜想 零 承认件  *)
(*   零 Variable 零 Hypothesis；语句面零 Props 泄露（结论全 Set、   *)
(*   Id、QeqT、QleT' 形）；主件出口 Print Assumptions Closed。      *)
(*   文件未动一字；禁 git。                                        *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInst.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：载体面工具（head 评估 / 常值规范实数 / 种型等价 / 范数）      *)
(* ============================================================ *)

(* 首项评估：Real -> Q（定义级） *)
Definition bxra_head (x : Real) : Q := projT1 x 0%nat.

(* 常值实数构造器（S02 real_const 透明：head 定义级还原） *)
Definition bxra_cR (q : Q) : Real := real_const q.

Lemma bxra_head_cR : forall q : Q, Id (bxra_head (bxra_cR q)) q.
Proof.
  intro q. unfold bxra_head, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

(* 种型等价：规范种型 *)
Definition bxra_bae_germ (a b : Real) : Set :=
  Id (bxib_qnorm (bxra_head a)) (bxib_qnorm (bxra_head b)).

(* 范数：Qabs∘qnorm∘head（处方定形） *)
Definition bxra_bnorm_f (x : Real) : Q := Qabs (bxib_qnorm (bxra_head x)).

(* 运算面：首项有理运算后规范化，包常值实数 *)
Definition bxra_bplus_f (x y : Real) : Real :=
  bxra_cR (bxib_qnorm (bxra_head x + bxra_head y)%Q).
Definition bxra_bmult_f (x y : Real) : Real :=
  bxra_cR (bxib_qnorm (bxra_head x * bxra_head y)%Q).
Definition bxra_bopp_f (x : Real) : Real :=
  bxra_cR (bxib_qnorm (- bxra_head x)%Q).
Definition bxra_bzero_f : Real := bxra_cR 0%Q.
Definition bxra_bone_f : Real := bxra_cR 1%Q.
Definition bxra_bcoef_f (q : Q) : Real := bxra_cR (bxib_qnorm q).

(* head 面还原（运算输出位定义级消化） *)
Lemma bxra_head_bplus : forall x y : Real,
  Id (bxra_head (bxra_bplus_f x y)) (bxib_qnorm (bxra_head x + bxra_head y)%Q).
Proof.
  intros x y. unfold bxra_head, bxra_bplus_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

Lemma bxra_head_bmult : forall x y : Real,
  Id (bxra_head (bxra_bmult_f x y)) (bxib_qnorm (bxra_head x * bxra_head y)%Q).
Proof.
  intros x y. unfold bxra_head, bxra_bmult_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

Lemma bxra_head_bopp : forall x : Real,
  Id (bxra_head (bxra_bopp_f x)) (bxib_qnorm (- bxra_head x)%Q).
Proof.
  intro x. unfold bxra_head, bxra_bopp_f, bxra_cR.
  cbn [projT1]. apply id_refl.
Qed.

(* ============================================================ *)
(* S1：Q 层工作件（QeqT 合同 / Qabs 助件 / 非负 / 传递桥）          *)
(* ============================================================ *)

(* QeqT 乘法合同（cong 机器补位） *)
Lemma bxra_qeqT_cong_mult : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (a * c)%Q (b * d)%Q.
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq a b Hab), (qeqT_imp_qeq c d Hcd).
  apply Qeq_refl.
Qed.

(* |xy| = |x||y|（stdlib 缺 Qabs_mult 名，自建） *)
Lemma bxra_qabs_mult : forall x y : Q, Qabs (x * y)%Q == Qabs x * Qabs y%Q.
Proof.
  intros [n d] [m e].
  unfold Qabs, Qmult, Qeq; simpl.
  rewrite Z.abs_mul. ring.
Qed.

(* Qabs 非负（QleT' 叶） *)
Lemma bxra_qleT_zero_abs_qn : forall x : Q, QleT' 0 (Qabs (bxib_qnorm x)).
Proof.
  intros [n d]. destruct n as [|p|p];
    apply Qle_to_QleT'; unfold Qle, Qabs, bxib_qnorm; cbn; lia.
Qed.

Lemma bxra_qltT_wd : forall a b c : Q, QeqT a b -> QltT a c -> QltT b c.
Proof.
  intros a b c Hab H.
  apply (qleT'_ltT_ltT b a c).
  - apply Qle_to_QleT'. apply qeq_imp_qle.
    apply qeqT_imp_qeq. apply bxib_qeqT_sym. exact Hab.
  - exact H.
Qed.

(* ============================================================ *)
(* ============================================================ *)

(* Qabs-范数不变（Id 形）。攻法已证结论：纯 iota 不达（Z.gcd 展开 ggcd  *)
(* 机器符号参卡壳），Z 层引理链闭合——Z.gcd_opp_l + bxib_div_exact  *)
(* + Z.abs_opp；eq 桥回 Id。                                        *)
Lemma bxra_id_of_eq : forall (A : Set) (x y : A), x = y -> Id x y.
Proof.
  intros A x y H.
  exact (match H in (_ = t) return Id x t with
         | eq_refl => id_refl
         end).
Qed.

(* Z 核：整除下取负的绝对值不变（div_opp 的代数路线，零 mod 条件） *)
Lemma bxra_zabs_div_opp : forall p g : Z,
  g <> 0%Z -> Z.divide g p -> Z.divide g (Z.opp p) ->
  Z.abs (Z.div (Z.opp p) g) = Z.abs (Z.div p g)%Z.
Proof.
  intros p g Hg0 Hp Hn.
  assert (Hdp : (p = Z.mul g (Z.div p g))%Z)
    by (eapply bxib_div_exact; assumption).
  assert (Hdn : (Z.opp p = Z.mul g (Z.div (Z.opp p) g))%Z)
    by (eapply bxib_div_exact; assumption).
  assert (Hq : (Z.div (Z.opp p) g = Z.opp (Z.div p g))%Z).
  { apply (Z.mul_reg_l (Z.div (Z.opp p) g) (Z.opp (Z.div p g)) g Hg0).
    rewrite <- Hdn. replace p with (Z.mul g (Z.div p g)) at 1
      by (symmetry; exact Hdp).
    ring. }
  rewrite Hq, Z.abs_opp. reflexivity.
Qed.

Lemma bxra_qabs_opp_norm : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof.
  intro u. apply bxra_id_of_eq.
  destruct u as [n d]. destruct n as [|p|p].
  - reflexivity.
  - change (Qopp (Qmake (Zpos p) d)) with (Qmake (Zneg p) d).
    rewrite bxib_qnorm_neg_shape, bxib_qnorm_pos_shape.
    unfold Qabs. cbn [Qnum Qden].
    change (Zneg p) with (- (Zpos p))%Z.
    rewrite (Z.gcd_opp_l (Zpos p) (Z.pos d)).
    f_equal.
    assert (Hg0 : Z.gcd (Zpos p) (Z.pos d) <> 0%Z).
    { intro H0.
      destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
      rewrite H0, Z.mul_0_r in Hk. discriminate Hk. }
    apply bxra_zabs_div_opp;
      [ exact Hg0 | exact (Z.gcd_divide_l (Zpos p) (Z.pos d)) | ].
    destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
    exists (-k)%Z. rewrite Hk at 1. ring.
  - change (Qopp (Qmake (Zneg p) d)) with (Qmake (Zpos p) d).
    rewrite bxib_qnorm_pos_shape, bxib_qnorm_neg_shape.
    unfold Qabs. cbn [Qnum Qden].
    change (Zneg p) with (- (Zpos p))%Z.
    rewrite (Z.gcd_opp_l (Zpos p) (Z.pos d)).
    f_equal.
    assert (Hg0 : Z.gcd (Zpos p) (Z.pos d) <> 0%Z).
    { intro H0.
      destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
      rewrite H0, Z.mul_0_r in Hk. discriminate Hk. }
    symmetry. apply bxra_zabs_div_opp;
      [ exact Hg0 | exact (Z.gcd_divide_l (Zpos p) (Z.pos d)) | ].
    destruct (Z.gcd_divide_l (Zpos p) (Z.pos d)) as [k Hk].
    exists (-k)%Z. rewrite Hk at 1. ring.
Qed.

(* 墙一 discharge（库类 QeqT 形）：种型等价的范数良定（Id 中转） *)
Lemma bxra_norm_wd : forall a b : Real,
  bxra_bae_germ a b -> Id (bxra_bnorm_f a) (bxra_bnorm_f b).
Proof.
  intros a b Hab. unfold bxra_bnorm_f.
  apply (id_cong Qabs). exact Hab.
Qed.

Lemma bxra_norm_wd_qeqt : forall a b : Real,
  bxra_bae_germ a b -> QeqT (bxra_bnorm_f a) (bxra_bnorm_f b).
Proof. intros a b Hab. apply bxib_qeqT_of_id. apply bxra_norm_wd. exact Hab. Qed.

(* 墙二 discharge（库类 QeqT 形）：钉定面到原始 Qabs q *)
Lemma bxra_norm_coef_qeqt : forall q : Q,
  QeqT (bxra_bnorm_f (bxra_bcoef_f q)) (Qabs q).
Proof.
  intro q.
  apply qeq_imp_qeqT.
  unfold bxra_bnorm_f, bxra_bcoef_f.
  rewrite (bxra_head_cR (bxib_qnorm q)).
  rewrite (bxib_qnorm_fix_id q).
  apply (Qeq_trans _ (Qabs (bxib_qnorm q))).
  - apply Qabs_wd. apply Qeq_refl.
  - apply (Qeq_trans _ (Qabs q)).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply Qeq_refl.
Qed.

(* bnorm_opp 字段 discharge（库类 Id 形）＝新增①的使用位 *)
Lemma bxra_f_norm_opp : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof.
  intro a.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (- bxra_head a)%Q)))
             (Qabs (bxib_qnorm (bxra_head a)))).
  rewrite (bxib_qnorm_fix_id (- bxra_head a)%Q).
  apply bxra_qabs_opp_norm.
Qed.

(* 原始钉定墙固化（诚实标注：Id 形原始 Qabs 钉定不可满足） *)
Lemma bxra_raw_pin_wall :
  Id (bxra_bnorm_f (bxra_bcoef_f (2#4)%Q)) (Qabs (2#4)%Q) ->
  Id (1#2)%Q (2#4)%Q.
Proof.
  intro H.
  change (Id (Qabs (bxib_qnorm (bxib_qnorm (2#4)%Q))) (Qabs (2#4)%Q)) in H.
  rewrite bxib_qnorm_fix_id in H.
  exact H.
Qed.

(* ============================================================ *)
(* S3：字段 discharge 件（库类 39 字段逐位）                        *)
(* ============================================================ *)

(* ---- 等价三律 ---- *)

Lemma bxra_f_refl : forall a : Real, bxra_bae_germ a a.
Proof. intro a. apply id_refl. Qed.

Lemma bxra_f_sym : forall a b : Real, bxra_bae_germ a b -> bxra_bae_germ b a.
Proof. intros a b H. apply id_sym. exact H. Qed.

Lemma bxra_f_trans : forall a b c : Real,
  bxra_bae_germ a b -> bxra_bae_germ b c -> bxra_bae_germ a c.
Proof. intros a b c H1 H2. apply (id_trans H1 H2). Qed.

(* ---- 加法群（保底件） ---- *)

Lemma bxra_f_plus_assoc : forall a b c : Real,
  bxra_bae_germ (bxra_bplus_f a (bxra_bplus_f b c))
                (bxra_bplus_f (bxra_bplus_f a b) c).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a (bxra_bplus_f b c)).
  rewrite (bxra_head_bplus b c).
  rewrite (bxra_head_bplus (bxra_bplus_f a b) c).
  rewrite (bxra_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxib_qnorm (bxra_head b + bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a + bxra_head b)%Q + bxra_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a + (bxra_head b + bxra_head c))%Q).
  - apply bxib_qeqT_cong_plus; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a + bxra_head b + bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qplus_assoc.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxra_f_plus_comm : forall a b : Real,
  bxra_bae_germ (bxra_bplus_f a b) (bxra_bplus_f b a).
Proof.
  intros a b. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a b), (bxra_head_bplus b a).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head b + bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qplus_comm.
Qed.

Lemma bxra_f_plus_zero : forall a : Real,
  bxra_bae_germ (bxra_bplus_f a bxra_bzero_f) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a bxra_bzero_f).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a + 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (bxra_head a)).
  - apply Qplus_0_r.
  - apply Qeq_refl.
Qed.

Lemma bxra_f_plus_opp : forall a : Real,
  bxra_bae_germ (bxra_bplus_f a (bxra_bopp_f a)) bxra_bzero_f.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a (bxra_bopp_f a)).
  rewrite (bxra_head_bopp a).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxib_qnorm (- bxra_head a)%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a + (- bxra_head a))%Q).
  - apply bxib_qeqT_cong_plus;
      [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- 乘法群 ---- *)

Lemma bxra_f_mult_assoc : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f a (bxra_bmult_f b c))
                (bxra_bmult_f (bxra_bmult_f a b) c).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bmult_f b c)).
  rewrite (bxra_head_bmult b c).
  rewrite (bxra_head_bmult (bxra_bmult_f a b) c).
  rewrite (bxra_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm (bxra_head b * bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head b)%Q * bxra_head c)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a * (bxra_head b * bxra_head c))%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head b * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_assoc.
    + apply bxra_qeqT_cong_mult;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix | apply bxib_qeqT_refl].
Qed.

Lemma bxra_f_mult_one_l : forall a : Real,
  bxra_bae_germ (bxra_bmult_f bxra_bone_f a) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult bxra_bone_f a).
  unfold bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (1%Q * bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_l.
Qed.

Lemma bxra_f_mult_one_r : forall a : Real,
  bxra_bae_germ (bxra_bmult_f a bxra_bone_f) a.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a bxra_bone_f).
  unfold bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a * 1%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_1_r.
Qed.

(* ---- 分配律 ---- *)

Lemma bxra_f_distrib_l : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f a (bxra_bplus_f b c))
                (bxra_bplus_f (bxra_bmult_f a b) (bxra_bmult_f a c)).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bplus_f b c)).
  rewrite (bxra_head_bplus b c).
  rewrite (bxra_head_bplus (bxra_bmult_f a b) (bxra_bmult_f a c)).
  rewrite (bxra_head_bmult a b), (bxra_head_bmult a c).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm (bxra_head b + bxra_head c))%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head b)%Q
                              + bxib_qnorm (bxra_head a * bxra_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxra_head a * (bxra_head b + bxra_head c))%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qeqT_refl | apply bxib_qnorm_fix].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head b + bxra_head a * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_r.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxra_f_distrib_r : forall a b c : Real,
  bxra_bae_germ (bxra_bmult_f (bxra_bplus_f a b) c)
                (bxra_bplus_f (bxra_bmult_f a c) (bxra_bmult_f b c)).
Proof.
  intros a b c. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult (bxra_bplus_f a b) c).
  rewrite (bxra_head_bplus a b).
  rewrite (bxra_head_bplus (bxra_bmult_f a c) (bxra_bmult_f b c)).
  rewrite (bxra_head_bmult a c), (bxra_head_bmult b c).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a + bxra_head b)%Q * bxra_head c)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm (bxra_head a * bxra_head c)%Q
                              + bxib_qnorm (bxra_head b * bxra_head c))%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ ((bxra_head a + bxra_head b) * bxra_head c)%Q).
  - apply bxra_qeqT_cong_mult; [apply bxib_qnorm_fix | apply bxib_qeqT_refl].
  - apply (bxib_qeqT_trans _ (bxra_head a * bxra_head c + bxra_head b * bxra_head c)%Q).
    + apply qeq_imp_qeqT. apply Qmult_plus_distr_l.
    + apply bxib_qeqT_cong_plus;
        [apply bxib_qeqT_sym; apply bxib_qnorm_fix |
         apply bxib_qeqT_sym; apply bxib_qnorm_fix].
Qed.

Lemma bxra_f_mult_zero : forall a : Real,
  bxra_bae_germ (bxra_bmult_f a bxra_bzero_f) bxra_bzero_f.
Proof.
  intro a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a bxra_bzero_f).
  unfold bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head a * 0%Q)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_0_r.
Qed.

(* ---- 良定三件 ---- *)

Lemma bxra_f_plus_wd : forall a b c d : Real,
  bxra_bae_germ a c -> bxra_bae_germ b d ->
  bxra_bae_germ (bxra_bplus_f a b) (bxra_bplus_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus a b), (bxra_head_bplus c d).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head c + bxra_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_mult_wd : forall a b c d : Real,
  bxra_bae_germ a c -> bxra_bae_germ b d ->
  bxra_bae_germ (bxra_bmult_f a b) (bxra_bmult_f c d).
Proof.
  intros a b c d Hac Hbd. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a b), (bxra_head_bmult c d).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxra_head b)%Q).
  rewrite (bxib_qnorm_fix_id (bxra_head c * bxra_head d)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxra_qeqT_cong_mult.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head c))).
      * apply bxib_qeqT_of_id. exact Hac.
      * apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_sym. apply bxib_qnorm_fix.
    + apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head d))).
      * apply bxib_qeqT_of_id. exact Hbd.
      * apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_opp_wd : forall a b : Real,
  bxra_bae_germ a b -> bxra_bae_germ (bxra_bopp_f a) (bxra_bopp_f b).
Proof.
  intros a b Hab. unfold bxra_bae_germ.
  rewrite (bxra_head_bopp a), (bxra_head_bopp b).
  rewrite (bxib_qnorm_fix_id (- bxra_head a)%Q).
  rewrite (bxib_qnorm_fix_id (- bxra_head b)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_opp.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head a))).
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
  - apply (bxib_qeqT_trans _ (bxib_qnorm (bxra_head b))).
    + apply bxib_qeqT_of_id. exact Hab.
    + apply bxib_qnorm_fix.
Qed.

(* ---- 标量嵌入面 ---- *)

Lemma bxra_f_coef_zero : bxra_bae_germ (bxra_bcoef_f 0%Q) bxra_bzero_f.
Proof.
  unfold bxra_bae_germ, bxra_bcoef_f, bxra_bzero_f.
  rewrite (bxra_head_cR (bxib_qnorm 0%Q)).
  rewrite (bxra_head_cR 0%Q).
  rewrite (bxib_qnorm_fix_id 0%Q).
  apply id_refl.
Qed.

Lemma bxra_f_coef_one : bxra_bae_germ (bxra_bcoef_f 1%Q) bxra_bone_f.
Proof.
  unfold bxra_bae_germ, bxra_bcoef_f, bxra_bone_f.
  rewrite (bxra_head_cR (bxib_qnorm 1%Q)).
  rewrite (bxra_head_cR 1%Q).
  rewrite (bxib_qnorm_fix_id 1%Q).
  apply id_refl.
Qed.

Lemma bxra_f_coef_mult : forall q r : Q,
  bxra_bae_germ (bxra_bcoef_f (q * r)%Q)
                (bxra_bmult_f (bxra_bcoef_f q) (bxra_bcoef_f r)).
Proof.
  intros q r. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult (bxra_bcoef_f q) (bxra_bcoef_f r)).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (q * r)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxib_qnorm r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym.
  apply bxra_qeqT_cong_mult; apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_coef_comm : forall (q : Q) (a : Real),
  bxra_bae_germ (bxra_bmult_f a (bxra_bcoef_f q))
                (bxra_bmult_f (bxra_bcoef_f q) a).
Proof.
  intros q a. unfold bxra_bae_germ.
  rewrite (bxra_head_bmult a (bxra_bcoef_f q)).
  rewrite (bxra_head_bmult (bxra_bcoef_f q) a).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxib_qnorm q)%Q).
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q * bxra_head a)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. apply Qmult_comm.
Qed.

(* ---- W6a 二字段 ---- *)

Lemma bxra_f_coef_plus : forall q r : Q,
  bxra_bae_germ (bxra_bplus_f (bxra_bcoef_f q) (bxra_bcoef_f r))
                (bxra_bcoef_f (q + r)%Q).
Proof.
  intros q r. unfold bxra_bae_germ.
  rewrite (bxra_head_bplus (bxra_bcoef_f q) (bxra_bcoef_f r)).
  unfold bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id (bxib_qnorm q + bxib_qnorm r)%Q).
  rewrite (bxib_qnorm_fix_id (q + r)%Q).
  apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_cong_plus; apply bxib_qnorm_fix.
Qed.

Lemma bxra_f_coef_wd : forall q r : Q,
  q == r -> bxra_bae_germ (bxra_bcoef_f q) (bxra_bcoef_f r).
Proof.
  intros q r Hqr. unfold bxra_bae_germ, bxra_bcoef_f.
  repeat rewrite bxra_head_cR.
  rewrite (bxib_qnorm_fix_id q), (bxib_qnorm_fix_id r).
  apply bxib_qnorm_id_of_qeqT.
  apply qeq_imp_qeqT. exact Hqr.
Qed.

(* ---- 范数面 ---- *)

Lemma bxra_f_norm_zero : Id (bxra_bnorm_f bxra_bzero_f) 0%Q.
Proof.
  unfold bxra_bnorm_f, bxra_bzero_f.
  rewrite (bxra_head_cR 0%Q).
  apply id_refl.
Qed.

Lemma bxra_f_norm_one : Id (bxra_bnorm_f bxra_bone_f) 1%Q.
Proof.
  unfold bxra_bnorm_f, bxra_bone_f.
  rewrite (bxra_head_cR 1%Q).
  apply id_refl.
Qed.

Lemma bxra_f_norm_pos : forall a : Real, QleT' 0 (bxra_bnorm_f a).
Proof.
  intro a. unfold bxra_bnorm_f. apply bxra_qleT_zero_abs_qn.
Qed.

Lemma bxra_f_norm_plus : forall a b : Real,
  QleT' (bxra_bnorm_f (bxra_bplus_f a b))
        (bxra_bnorm_f a + bxra_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxra_bnorm_f.
  rewrite (bxra_head_bplus a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a + bxra_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxra_head a + bxra_head b)%Q)).
  - apply qeq_imp_qle.
    apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
  - apply (Qle_trans _ (Qabs (bxra_head a) + Qabs (bxra_head b))%Q).
    + apply Qabs_triangle.
    + apply qeq_imp_qle.
      apply (@Qplus_comp (Qabs (bxra_head a)) (Qabs (bxib_qnorm (bxra_head a)))
           (Qeq_sym (Qabs (bxib_qnorm (bxra_head a))) (Qabs (bxra_head a))
                (Qabs_wd (bxib_qnorm (bxra_head a)) (bxra_head a)
                     (qeqT_imp_qeq (bxib_qnorm (bxra_head a)) (bxra_head a)
                          (bxib_qnorm_fix (bxra_head a)))))
           (Qabs (bxra_head b)) (Qabs (bxib_qnorm (bxra_head b)))
           (Qeq_sym (Qabs (bxib_qnorm (bxra_head b))) (Qabs (bxra_head b))
                (Qabs_wd (bxib_qnorm (bxra_head b)) (bxra_head b)
                     (qeqT_imp_qeq (bxib_qnorm (bxra_head b)) (bxra_head b)
                          (bxib_qnorm_fix (bxra_head b)))))).
Qed.

Lemma bxra_f_norm_mult : forall a b : Real,
  QleT' (bxra_bnorm_f (bxra_bmult_f a b))
        (bxra_bnorm_f a * bxra_bnorm_f b)%Q.
Proof.
  intros a b. unfold bxra_bnorm_f.
  rewrite (bxra_head_bmult a b).
  rewrite (bxib_qnorm_fix_id (bxra_head a * bxra_head b)%Q).
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs (bxra_head a) * Qabs (bxra_head b))%Q).
  - apply qeq_imp_qle.
    apply (Qeq_trans (Qabs (bxib_qnorm (bxra_head a * bxra_head b)%Q))
                     (Qabs (bxra_head a * bxra_head b)%Q)
                     (Qabs (bxra_head a) * Qabs (bxra_head b))%Q).
    + apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
    + apply bxra_qabs_mult.
  - apply qeq_imp_qle.
    apply (@Qmult_comp (Qabs (bxra_head a)) (Qabs (bxib_qnorm (bxra_head a)))
         (Qeq_sym (Qabs (bxib_qnorm (bxra_head a))) (Qabs (bxra_head a))
              (Qabs_wd (bxib_qnorm (bxra_head a)) (bxra_head a)
                   (qeqT_imp_qeq (bxib_qnorm (bxra_head a)) (bxra_head a)
                        (bxib_qnorm_fix (bxra_head a)))))
         (Qabs (bxra_head b)) (Qabs (bxib_qnorm (bxra_head b)))
         (Qeq_sym (Qabs (bxib_qnorm (bxra_head b))) (Qabs (bxra_head b))
              (Qabs_wd (bxib_qnorm (bxra_head b)) (bxra_head b)
                   (qeqT_imp_qeq (bxib_qnorm (bxra_head b)) (bxra_head b)
                        (bxib_qnorm_fix (bxra_head b)))))).
Qed.

(* ============================================================ *)
(* S4：库类全字段装配——全库首个 bxin_BanachAlgPre 具体实例          *)
(* ============================================================ *)

Instance bxra_real_pre : bxin_BanachAlgPre := {|
  bxin_BA := Real;
  bxin_bae := bxra_bae_germ;
  bxin_bae_refl := bxra_f_refl;
  bxin_bae_sym := bxra_f_sym;
  bxin_bae_trans := bxra_f_trans;
  bxin_bzero := bxra_bzero_f;
  bxin_bone := bxra_bone_f;
  bxin_bplus := bxra_bplus_f;
  bxin_bmult := bxra_bmult_f;
  bxin_bopp := bxra_bopp_f;
  bxin_bcoef := bxra_bcoef_f;
  bxin_bnorm := bxra_bnorm_f;
  bxin_bplus_assoc := bxra_f_plus_assoc;
  bxin_bplus_comm := bxra_f_plus_comm;
  bxin_bplus_zero := bxra_f_plus_zero;
  bxin_bplus_opp := bxra_f_plus_opp;
  bxin_bmult_assoc := bxra_f_mult_assoc;
  bxin_bmult_one_l := bxra_f_mult_one_l;
  bxin_bmult_one_r := bxra_f_mult_one_r;
  bxin_bdistrib_l := bxra_f_distrib_l;
  bxin_bdistrib_r := bxra_f_distrib_r;
  bxin_bmult_zero := bxra_f_mult_zero;
  bxin_bplus_wd := bxra_f_plus_wd;
  bxin_bmult_wd := bxra_f_mult_wd;
  bxin_bopp_wd := bxra_f_opp_wd;
  bxin_bnorm_wd := bxra_norm_wd_qeqt;
  bxin_bcoef_zero := bxra_f_coef_zero;
  bxin_bcoef_one := bxra_f_coef_one;
  bxin_bcoef_mult := bxra_f_coef_mult;
  bxin_bcoef_comm := bxra_f_coef_comm;
  bxin_bcoef_plus := bxra_f_coef_plus;
  bxin_bcoef_wd := bxra_f_coef_wd;
  bxin_bnorm_zero := bxra_f_norm_zero;
  bxin_bnorm_one := bxra_f_norm_one;
  bxin_bnorm_opp := bxra_f_norm_opp;
  bxin_bnorm_pos := bxra_f_norm_pos;
  bxin_bnorm_plus := bxra_f_norm_plus;
  bxin_bnorm_mult := bxra_f_norm_mult;
  bxin_bnorm_coef := bxra_norm_coef_qeqt;
|}.

(* 装配冒烟：库类投影面（实例非空性 0%→100% 的点态确认） *)
Lemma bxra_inst_smoke_bone :
  @bxin_bae bxra_real_pre
    (@bxin_bcoef bxra_real_pre 1%Q)
    (@bxin_bone bxra_real_pre).
Proof.
  change (@bxin_bae bxra_real_pre
           (@bxin_bcoef bxra_real_pre 1%Q)
           (@bxin_bone bxra_real_pre))
    with (bxra_bae_germ (bxra_bcoef_f 1%Q) bxra_bone_f).
  apply bxra_f_coef_one.
Qed.

Lemma bxra_inst_smoke_norm_coef : forall q : Q,
  QeqT (@bxin_bnorm bxra_real_pre (@bxin_bcoef bxra_real_pre q)) (Qabs q).
Proof.
  intro q.
  change (@bxin_bnorm bxra_real_pre (@bxin_bcoef bxra_real_pre q))
    with (bxra_bnorm_f (bxra_bcoef_f q)).
  apply bxra_norm_coef_qeqt.
Qed.

Lemma bxra_inst_smoke_norm_wd : forall a b : Real,
  @bxin_bae bxra_real_pre a b ->
  QeqT (@bxin_bnorm bxra_real_pre a) (@bxin_bnorm bxra_real_pre b).
Proof.
  intros a b H.
  change (@bxin_bnorm bxra_real_pre a) with (bxra_bnorm_f a).
  change (@bxin_bnorm bxra_real_pre b) with (bxra_bnorm_f b).
  change (@bxin_bae bxra_real_pre a b) with (bxra_bae_germ a b).
  apply bxra_norm_wd_qeqt. exact H.
Qed.

(* ============================================================ *)
(* S5：完备性红利半获取（bcauchy 优先吃位）＋ 诚实留记              *)
(* ============================================================ *)

(* 范数差换算：bnorm(u m ⊖ u n) 的 Qeq 值＝首项列差绝对值 *)
Lemma bxra_norm_diff_head : forall (u : nat -> Real) (m n : nat),
  QeqT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n))))
       (Qabs (bxra_head (u m) - bxra_head (u n))%Q).
Proof.
  intros u m n. unfold bxra_bnorm_f.
  rewrite (bxra_head_bplus (u m) (bxra_bopp_f (u n))).
  rewrite (bxra_head_bopp (u n)).
  rewrite (bxib_qnorm_fix_id (bxra_head (u m)
            + bxib_qnorm (- bxra_head (u n))%Q)%Q).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (Qabs (bxib_qnorm
        (bxra_head (u m) - bxra_head (u n))%Q))).
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_qeqT_of_qeqT.
    apply bxib_qeqT_cong_plus.
    + apply bxib_qeqT_refl.
    + apply bxib_qnorm_fix.
  - apply Qabs_wd. apply qeqT_imp_qeq. apply bxib_qnorm_fix.
Qed.

(* 红利获取①：Pre-柯西列的首项列本身是 S02 意义的 Q-Cauchy 列 *)
Lemma bxra_head_col_cauchy : forall u : nat -> Real,
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n)))) eps)) ->
  cauchy (fun k => bxra_head (u k)).
Proof.
  intros u Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N. intros m n Hm Hn.
  apply (bxra_qltT_wd (bxra_bnorm_f
        (bxra_bplus_f (u m) (bxra_bopp_f (u n))))).
  - apply bxra_norm_diff_head.
  - apply HN; assumption.
Qed.

(* 红利获取②：极限【元素】在 Real 载体上构造可得                *)
(* （载体内建完备性红利的实测形：柯西见证由首项列自供，          *)
(*   existT 包装即得真 Real 元素——载体侧零缺口。）               *)
Definition bxra_cauchy_limit_elem (u : nat -> Real)
  (Hu : forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (bxra_bnorm_f (bxra_bplus_f (u m) (bxra_bopp_f (u n)))) eps))
  : Real :=
  existT (fun s : Qseq => cauchy s)
         (fun k => bxra_head (u k)) (bxra_head_col_cauchy u Hu).

(* 诚实留记：收敛语句（bxin_pre_complete 的内层）——范数读第 0 项， *)
(* 极限元素的第 0 项须为（构造性不可命名的）首项列极限值，        *)
(* ＝Q 列完备墙（INST3 已证结论维持，零强造；余项逐条见交付报告）。    *)
Definition bxra_pre_complete_real : Set :=
  bxin_pre_complete bxra_real_pre.

(* 装配桥连接（条件形：完备性输入就位即得完整 BanachAlg） *)
Definition bxra_BanachAlg_of_real
  (Hc : bxin_pre_complete bxra_real_pre) : BanachAlg :=
  bxin_BanachAlg_of_pre bxra_real_pre Hc.

Lemma bxra_bridge_smoke : forall Hc : bxin_pre_complete bxra_real_pre,
  @bae (bxra_BanachAlg_of_real Hc)
       (@bcoef (bxra_BanachAlg_of_real Hc) 1%Q)
       (@bone (bxra_BanachAlg_of_real Hc)).
Proof. intro Hc. apply bxin_bone_is_one. Qed.

(* ============================================================ *)
(* S6：提取检验 + 假设面自审（G3 面）                              *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
(* 提取检验（INST5 同款纪律：标量/引理级件，依赖载体项不提取——   *)
(*   existT/记录提取 inherent Obj.magic 属提取器特性，非语句负债； *)
(*   依赖项 bxra_cauchy_limit_elem/bxra_BanachAlg_of_real 以       *)
(*   Print Assumptions Closed 承担假设面自审）。                   *)
Separate Extraction bxra_qabs_opp_norm bxra_norm_wd_qeqt bxra_norm_coef_qeqt
  bxra_f_norm_opp bxra_f_plus_opp bxra_f_norm_mult bxra_raw_pin_wall
  bxra_qabs_mult bxra_qleT_zero_abs_qn bxra_qltT_wd bxra_norm_diff_head.

Print Assumptions bxra_qabs_opp_norm.
Print Assumptions bxra_norm_wd_qeqt.
Print Assumptions bxra_norm_coef_qeqt.
Print Assumptions bxra_f_norm_opp.
Print Assumptions bxra_f_plus_assoc.
Print Assumptions bxra_f_plus_opp.
Print Assumptions bxra_f_norm_mult.
Print Assumptions bxra_cauchy_limit_elem.
Print Assumptions bxra_real_pre.
Print Assumptions bxra_inst_smoke_bone.
Print Assumptions bxra_bridge_smoke.

(* —— 替换件假设面自审（切片三，全部应 Closed under the global context） —— *)
Print Assumptions bxra_head_cR.
Print Assumptions bxra_head_bplus.
Print Assumptions bxra_head_bmult.
Print Assumptions bxra_head_bopp.
Print Assumptions bxra_f_coef_zero.
Print Assumptions bxra_f_coef_one.
Print Assumptions bxra_f_norm_zero.
Print Assumptions bxra_f_norm_one.
Print Assumptions bxra_inst_smoke_bone.
Print Assumptions bxra_inst_smoke_norm_coef.
Print Assumptions bxra_inst_smoke_norm_wd.
