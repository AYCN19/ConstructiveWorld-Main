(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ═════════════════════════════════════════════════════════════════════ *
 * 组件E·切片六 同名替换件：UpReqBanachInstB（记录 组 续作，切片六） *
 * 本稿＝原件全文逐字保留，仅按玩具清单逐条换写下列证明体（同一陈述、         *
 * 同一符号、零新增 Require、零承认件、全中文头注）。                       *
 * 替换清单（9 件）：bxib_coef_half_canon／bxib_half_quarter_canon_id／      *
 *   bxib_zero_canon_lit／bxib_zero_canon_all／bxib_bnorm_zero／             *
 *   bxib_bnorm_one／bxib_bnorm_coef_canon／bxib_bnorm_half_quarter_smoke／  *
 *   bxib_bnorm_pos                                                         *
 * 三口径：①定义层受控展开（qnorm/bcnorm/bnorm/ev 定义面 unfold＋cbv iota    *
 *   zeta 构造子分支分派至通配肢／Z0 肢；系数件 cbn [bxib_ev] 构造子肢复原——  *
 *   InstReal 首项投影同族范式）＋②显式见证（阻隔位保底件以 replace-by-        *
 *   reflexivity 数值见证链逐步给出 gcd/div/Z.abs/Z.to_pos 各步计算值；      *
 *   bnorm_pos 以 bxib_qabs_nonneg 全应用闭项依存，消除单点转发跳）＋        *
 *   ③结构性推导（Qmake 字面中间形 change＋ring 零见证：Qplus/Qopp 定义面    *
 *   抬升至分子显式归零后 iota 分派 Z0 肢）。                                *
 * 不可化标注（批量，如实不改）：shape 双件（pos/neg_shape：语句面为         *
 *   stdlib eq＝Prop 位，处于替换件 Set 面纪律边界，如实不改）；qeqT 小工具族  *
 *   （refl/sym/trans/cong_plus/of_id/qnorm_qeqT_of_qeqT/qeq_make：Qeq/QeqT  *
 *   引擎单点依存，改写即同项转述）；bae 恒等三律与 bnorm_wd（id 族单跳，    *
 *   bae 定义包装即内容）；bplus_comm/zero/opp 与 bcoef_mult（stdlib        *
 *   Qplus/Qmult 引擎单点依存＋破墙机中转，内联即复制）；已显式链面件        *
 *   （id_of_qeqT_canon/canon_pin_wall/qabs_opp_raw/gcd_nz：原链已最简，    *
 *   换序即注水）。                                                         *
 * 纪律：纯构造性；Set 层零 Prop 泄露；Proof./Qed. 配平；真 Qed。           *
 * ═════════════════════════════════════════════════════════════════════ *)
(* ============================================================ *)
(* ============================================================ *)
(* 使命：冻结类签名不变，以 gcd 正规化（bxib_qnorm：约分至最简 +  *)
(*   分母正 + 零规范到 0#1）破 INS 两墙：                        *)
(*   墙一 bxin_Q_bnorm_wall：2#4 == 1#2 而 Id 余域钉定强逼       *)
(*        Id (2#4) (1#2)；墙二 bxin_Q_leibniz_opp_wall：         *)
(*        Id (0#16) (0#1) 封死。对策：数值相等的 Q 归约到同一      *)
(*        规范形后，Id/定义等可 discharge。                      *)
(* 交付分层：                                                   *)
(*   S0 = bxib_qnorm 正规化 + 保底两件：                         *)
(*        bxib_coef_half_canon（墙一同位：1/2 钉定在规范形下成立）*)
(*        bxib_zero_canon 系（墙二位：0#16/0#1 规范一致）         *)
(*   S1 = 规范形唯一性引理 bxib_qnorm_id_of_qeqT（INS 遗留②6-3   *)
(*        的 Z-gcd/互素工作：Zis_gcd + Gauss/rel_prime_cross_    *)
(*        prod 交叉乘唯一性）——破墙机器。                       *)
(*   S2 = 规范形钉定墙形式化 bxib_canon_pin_wall：Qabs 原始钉定  *)
(*        字段（bnorm_coef 语句形）在 canon-bnorm 下仍不可满足    *)
(*        ——修正 INS 升级处方③：Qred 路线须同步改钉定字段语句面。 *)
(*   S3 = E-载体（自由项树）规范形实例正件：canon-bae 下 bae 三律 *)
(*        + wd 三件 + 加法交换群全字段 + 标量嵌入律 + 范数钉定族； *)
(*        乘法结合/分配与 norm_plus/mult 位遗留（见文件尾声明）。  *)
(* 铁律自审：公理面零命中；语句面全 Set；冻结类与 INS/UNQ/CLS    *)
(*   产物零改动（仅 Require 依存）；前缀 bxib_ 全库零撞名。       *)
(* 工程注：Rocq 9 无 Pos.div（BinPos 除法已移除）；正数除法走     *)
(*   Z.div（pos/pos 定义级归约）+ Z.to_pos 还原分母；Z.gcd 在    *)
(*   pos/pos 定义级还原；Z.abs 在 Zpos/Zneg 构造子上 iota 还原；  *)
(*   positive→Z 桥一律 lia；Z.compare 结论位走 compare_lt_iff；  *)
(*   含 Z.gcd/Z.div 的目标禁 simpl（过度约简断匹配），走 shape    *)
(*   引理改写 + cbn 显式清单。                                     *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：bxib_qnorm —— gcd 正规化（保底件核心）                    *)
(* ============================================================ *)

Definition bxib_qnorm (q : Q) : Q :=
  match q with
  | Qmake n d =>
      match n with
      | Z0 => (0#1)%Q
      | _ => let g := Z.gcd n (Z.pos d) in
             Qmake (Z.div n g) (Z.to_pos (Z.div (Z.pos d) g))
      end
  end.

(* 规范形还原形（分母正性由 d ≥ g ≥ 1 保证；shape 引理供改写用） *)
Lemma bxib_qnorm_pos_shape : forall (p d : positive),
  bxib_qnorm (Qmake (Zpos p) d) =
  Qmake (Z.div (Zpos p) (Z.gcd (Zpos p) (Z.pos d)))
        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))).
Proof. intros p d. reflexivity. Qed.

Lemma bxib_qnorm_neg_shape : forall (p d : positive),
  bxib_qnorm (Qmake (Zneg p) d) =
  Qmake (Z.div (Zneg p) (Z.gcd (Zneg p) (Z.pos d)))
        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))).
Proof. intros p d. reflexivity. Qed.

(* ============================================================ *)
(* 保底件①：bxib_coef_half_canon —— bcoef 语义下 1/2 钉定成立    *)
(* （INS 墙一同位：规范形标量范数 bcnorm := Qabs ∘ qnorm 下，     *)
(*   墙一的 2#4/1#2 同位语句成为定义级可证等式。）               *)
(* ============================================================ *)

Definition bxib_bcnorm (q : Q) : Q := Qabs (bxib_qnorm q).

Lemma bxib_coef_half_canon : Id (bxib_bcnorm (2#4)%Q) (Qabs (1#2)%Q).
Proof.
  unfold bxib_bcnorm, bxib_qnorm. cbv iota zeta.
  replace (Z.gcd (Zpos 2) (Zpos 4)) with (Zpos 2) by reflexivity.
  replace (Z.div (Zpos 2) (Zpos 2)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 4) (Zpos 2)) with (Zpos 2) by reflexivity.
  change (Z.to_pos (Zpos 2)) with 2%positive.
  apply id_refl.
Qed.

(* 对照：墙一原始形态 Id (2#4) (1#2) 的规范形可证版 *)
Lemma bxib_half_quarter_canon_id : Id (bxib_qnorm (2#4)%Q) (1#2)%Q.
Proof.
  unfold bxib_qnorm. cbv iota zeta.
  replace (Z.gcd (Zpos 2) (Zpos 4)) with (Zpos 2) by reflexivity.
  replace (Z.div (Zpos 2) (Zpos 2)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 4) (Zpos 2)) with (Zpos 2) by reflexivity.
  change (Z.to_pos (Zpos 2)) with 2%positive.
  apply id_refl.
Qed.

(* ============================================================ *)
(* 保底件②：零规范一致件（INS 墙二的 0#16/0#1 位）               *)
(* ============================================================ *)

(* 字面位：Qplus 不约分产生的 0#16 归约到 0#1（墙二直击位） *)
Lemma bxib_zero_canon_lit : Id (bxib_qnorm (Qplus (2#4)%Q (Qopp (2#4)%Q))) (0#1)%Q.
Proof.
  unfold bxib_qnorm.
  change (Qplus (2#4)%Q (Qopp (2#4)%Q))
    with (Qmake (2 * Z.pos 4 + Z.opp 2 * Z.pos 4)%Z
                (4 * 4)%positive).
  replace (2 * Z.pos 4 + Z.opp 2 * Z.pos 4)%Z with 0%Z by ring.
  cbv iota zeta.
  apply id_refl.
Qed.

(* 一般位 1：任意分母的零都规范到 0#1（iota 即闭） *)
Lemma bxib_zero_canon_all : forall d : positive, Id (bxib_qnorm (0#d)%Q) (0#1)%Q.
Proof.
  intros d. unfold bxib_qnorm. cbv iota zeta.
  apply id_refl.
Qed.

(* 一般位 2：任意 Q 值自加逆后规范到 0#1（墙二一般形态的规范形解） *)
Lemma bxib_zero_canon_opp : forall q : Q, Id (bxib_qnorm (Qplus q (Qopp q))) (0#1)%Q.
Proof.
  intros q. destruct q as [n d].
  change (Qplus (Qmake n d) (Qopp (Qmake n d)))
    with (Qmake (n * Z.pos d + Z.opp n * Z.pos d)%Z (d * d)%positive).
  replace (n * Z.pos d + Z.opp n * Z.pos d) with 0%Z by ring.
  apply id_refl.
Qed.

(* ============================================================ *)
(* S1：规范形唯一性引理（破墙机器）                               *)
(* ============================================================ *)

(* 除法精确性：g | n 时 n = g * (n/g) *)
Lemma bxib_div_exact : forall n g : Z, g <> 0 -> Z.divide g n -> n = g * (n / g)%Z.
Proof.
  intros n g Hg Hn.
  pose proof (Z_div_mod_eq_full n g) as E.
  rewrite (Zdivide_mod _ _ Hn) in E. lia.
Qed.

(* gcd 非零桥 *)
Lemma bxib_gcd_nz : forall n d : Z, n <> 0 -> (Z.gcd n d <> 0)%Z.
Proof.
  intros n d Hn Hc. exact (Hn (Z.gcd_eq_0_l n d Hc)).
Qed.

(* 互素转移：g = gcd n d（n,d 非零）时既约因子 n/g 与 d/g 互素 *)
Lemma bxib_coprime_cofactor : forall n d : Z, n <> 0 -> d <> 0 ->
  rel_prime (n / Z.gcd n d) (d / Z.gcd n d).
Proof.
  intros n d Hn Hd.
  assert (HG : (Z.gcd n d <> 0)%Z) by (apply bxib_gcd_nz; exact Hn).
  assert (HN : Z.divide (Z.gcd n d) n) by apply Z.gcd_divide_l.
  assert (HD : Z.divide (Z.gcd n d) d) by apply Z.gcd_divide_r.
  pose proof (bxib_div_exact n (Z.gcd n d) HG HN) as En.
  pose proof (bxib_div_exact d (Z.gcd n d) HG HD) as Ed.
  apply Zis_gcd_intro.
  - apply Z.divide_1_l.
  - apply Z.divide_1_l.
  - intros z Hz1 Hz2.
    destruct Hz1 as [k1 Ek1]. destruct Hz2 as [k2 Ek2].
    assert (Hzn : Z.divide (z * Z.gcd n d) n).
    { exists k1. rewrite En at 1. rewrite Ek1. ring. }
    assert (Hzd : Z.divide (z * Z.gcd n d) d).
    { exists k2. rewrite Ed at 1. rewrite Ek2. ring. }
    pose proof (Zgcd_is_gcd n d) as Hg3.
    destruct Hg3 as [_ _ Hdiv].
    destruct (Hdiv (z * Z.gcd n d) Hzn Hzd) as [j Ej].
    assert (E1 : (Z.gcd n d * 1 = Z.gcd n d * (z * j))%Z)
      by (rewrite Ej at 1; ring).
    pose proof (Z.mul_reg_l 1 (z * j) (Z.gcd n d) HG E1) as E2.
    exists j. rewrite Z.mul_comm. exact E2.
Qed.

(* 免非线性战术的单变量消去桥（纯重写 + Z.mul_reg_l） *)
Lemma bxib_cancel_aux : forall N E M D X Y Z1 W G1 G2 : Z,
  N = G1 * X -> E = G2 * Y -> M = G2 * Z1 -> D = G1 * W ->
  N * E = M * D -> G1 * G2 <> 0 -> G1 <> 0 -> G2 <> 0 ->
  X * Y = Z1 * W.
Proof.
  intros N E M D X Y Z1 W G1 G2 HN HE HM HD Hc HG12 HG1 HG2.
  assert (T : ((N * E) * (G1 * G2) = (M * D) * (G1 * G2))%Z)
    by (rewrite Hc; reflexivity).
  rewrite HN, HE, HM, HD in T.
  rewrite (Z.mul_comm _ (G1 * G2)) in T.
  rewrite (Z.mul_comm _ (G1 * G2)) in T.
  pose proof (Z.mul_reg_l _ _ (G1 * G2) HG12 T) as T1.
  rewrite (Z.mul_comm (G2 * Z1) (G1 * W)) in T1.
  assert (Hp : (G1 * G2 * (X * Y) = G1 * G2 * (Z1 * W))%Z).
  { transitivity ((G1 * X) * (G2 * Y))%Z.
    - ring.
    - rewrite T1. ring. }
  exact (Z.mul_reg_l (X * Y) (Z1 * W) (G1 * G2) HG12 Hp).
Qed.

(* 核心：既约交叉乘唯一（Gauss/Bezout 面 rel_prime_cross_prod） *)
Lemma bxib_cross_unique : forall n d m e : Z,
  n <> 0 -> m <> 0 -> 0 < d -> 0 < e -> (n * e = m * d)%Z ->
  (n / Z.gcd n d = m / Z.gcd m e)%Z /\
  (d / Z.gcd n d = e / Z.gcd m e)%Z.
Proof.
  intros n d m e Hn Hm Hd He Hcross.
  assert (HG1 : (Z.gcd n d <> 0)%Z) by (apply bxib_gcd_nz; exact Hn).
  assert (HG2 : (Z.gcd m e <> 0)%Z) by (apply bxib_gcd_nz; exact Hm).
  assert (HG1p : (0 < Z.gcd n d)%Z) by (pose proof (Z.gcd_nonneg n d); lia).
  assert (HG2p : (0 < Z.gcd m e)%Z) by (pose proof (Z.gcd_nonneg m e); lia).
  pose proof (bxib_div_exact n (Z.gcd n d) HG1 (Z.gcd_divide_l n d)) as En.
  pose proof (bxib_div_exact d (Z.gcd n d) HG1 (Z.gcd_divide_r n d)) as Ed.
  pose proof (bxib_div_exact m (Z.gcd m e) HG2 (Z.gcd_divide_l m e)) as Em.
  pose proof (bxib_div_exact e (Z.gcd m e) HG2 (Z.gcd_divide_r m e)) as Ee.
  assert (Hdz : ((d / Z.gcd n d) <> 0)%Z).
  { intro Hz. rewrite Hz in Ed. lia. }
  assert (Hez : ((e / Z.gcd m e) <> 0)%Z).
  { intro Hz. rewrite Hz in Ee. lia. }
  assert (Hbp : (0 < d / Z.gcd n d)%Z).
  { assert ((0 <= d / Z.gcd n d)%Z) by (apply Z.div_pos; lia). lia. }
  assert (Hdp : (0 < e / Z.gcd m e)%Z).
  { assert ((0 <= e / Z.gcd m e)%Z) by (apply Z.div_pos; lia). lia. }
  assert (HG12 : (Z.gcd n d * Z.gcd m e <> 0)%Z) by lia.
  assert (Hc1 : ((n / Z.gcd n d) * (e / Z.gcd m e)
              = (m / Z.gcd m e) * (d / Z.gcd n d))%Z).
  { exact (bxib_cancel_aux n e m d
      (n / Z.gcd n d) (e / Z.gcd m e) (m / Z.gcd m e) (d / Z.gcd n d)
      (Z.gcd n d) (Z.gcd m e) En Ee Em Ed Hcross HG12 HG1 HG2). }
  assert (Hbp2 : (d / Z.gcd n d > 0)%Z) by (apply (proj2 (Z.compare_gt_iff _ 0)); exact Hbp).
  assert (Hdp2 : (e / Z.gcd m e > 0)%Z) by (apply (proj2 (Z.compare_gt_iff _ 0)); exact Hdp).
  assert (Hc1' : (n / Z.gcd n d * (e / Z.gcd m e)
                = d / Z.gcd n d * (m / Z.gcd m e))%Z).
  { rewrite (Z.mul_comm (d / Z.gcd n d) (m / Z.gcd m e)). exact Hc1. }
  destruct (rel_prime_cross_prod (n / Z.gcd n d) (d / Z.gcd n d)
                                 (m / Z.gcd m e) (e / Z.gcd m e)
    (bxib_coprime_cofactor n d Hn ltac:(lia)) (bxib_coprime_cofactor m e Hm ltac:(lia))
    Hbp2 Hdp2 Hc1') as [E1 E2].
  split.
  - exact E1.
  - exact E2.
Qed.

(* 破墙机器：QeqT（可判定等词）下规范形唯一 —— Id 可 discharge *)
Lemma bxib_qnorm_id_of_qeqT : forall x y : Q, QeqT x y -> Id (bxib_qnorm x) (bxib_qnorm y).
Proof.
  intros x y HT.
  assert (Heq : x == y) by (apply qeqT_imp_qeq; exact HT).
  destruct x as [n d]; destruct y as [m e].
  unfold Qeq in Heq; simpl in Heq.
  destruct n as [|p|p]; destruct m as [|q|q].
  - apply id_refl.
  - exfalso; nia.
  - exfalso; nia.
  - exfalso; nia.
  - (* Zpos Zpos *)
    destruct (bxib_cross_unique (Z.pos p) (Z.pos d) (Z.pos q) (Z.pos e)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq) as [H1 H2].
    rewrite (bxib_qnorm_pos_shape p d), (bxib_qnorm_pos_shape q e).
    rewrite H1, H2. apply id_refl.
  - exfalso; nia.
  - exfalso; nia.
  - exfalso; nia.
  - (* Zneg Zneg *)
    destruct (bxib_cross_unique (Z.neg p) (Z.pos d) (Z.neg q) (Z.pos e)
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Heq) as [H1 H2].
    rewrite (bxib_qnorm_neg_shape p d), (bxib_qnorm_neg_shape q e).
    rewrite H1, H2. apply id_refl.
Qed.

(* 等价形式：Qeq（Prop 引擎面）入，Id（Set 面）出 *)
Lemma bxib_qnorm_id_of_qeq : forall x y : Q, x == y -> Id (bxib_qnorm x) (bxib_qnorm y).
Proof.
  intros x y H. exact (bxib_qnorm_id_of_qeqT x y (qeq_imp_qeqT x y H)).
Qed.

(* ---- QeqT 小工具族 ---- *)

Lemma bxib_qeqT_refl : forall x : Q, QeqT x x.
Proof. intro x. apply qeq_imp_qeqT. apply Qeq_refl. Qed.

Lemma bxib_qeqT_of_id : forall x y : Q, Id x y -> QeqT x y.
Proof.
  intros x y H. destruct H. apply bxib_qeqT_refl.
Qed.

Lemma bxib_qnorm_qeqT_of_qeqT : forall x y : Q,
  QeqT x y -> QeqT (bxib_qnorm x) (bxib_qnorm y).
Proof.
  intros x y H. apply bxib_qeqT_of_id.
  apply bxib_qnorm_id_of_qeqT. exact H.
Qed.

Lemma bxib_qeqT_sym : forall x y : Q, QeqT x y -> QeqT y x.
Proof.
  intros x y H. apply qeq_imp_qeqT. apply Qeq_sym.
  apply qeqT_imp_qeq. exact H.
Qed.

Lemma bxib_qeqT_trans : forall x y z : Q, QeqT x y -> QeqT y z -> QeqT x z.
Proof.
  intros x y z H1 H2. apply qeq_imp_qeqT.
  exact (Qeq_trans x y z (qeqT_imp_qeq _ _ H1) (qeqT_imp_qeq _ _ H2)).
Qed.

Lemma bxib_qeqT_cong_plus : forall a b c d : Q,
  QeqT a b -> QeqT c d -> QeqT (Qplus a c) (Qplus b d).
Proof.
  intros a b c d Hab Hcd.
  apply qeq_imp_qeqT.
  apply qeqT_imp_qeq in Hab. apply qeqT_imp_qeq in Hcd.
  rewrite <- Hab, <- Hcd. apply Qeq_refl.
Qed.

Lemma bxib_qeqT_cong_opp : forall a b : Q, QeqT a b -> QeqT (Qopp a) (Qopp b).
Proof.
  intros a b H. apply qeq_imp_qeqT.
  apply qeqT_imp_qeq in H.
  destruct a as [n d]; destruct b as [m e].
  unfold Qeq in H; simpl in H. unfold Qeq; simpl.
  assert (H2 : (Z.opp n * Z.pos e = Z.opp (n * Z.pos e))%Z) by ring.
  assert (H3 : (Z.opp m * Z.pos d = Z.opp (m * Z.pos d))%Z) by ring.
  rewrite H2, H3, H. reflexivity.
Qed.
(* Qmake 层面的 Qeq 构造器（避免目标里出现投影） *)
Lemma bxib_qeq_make : forall (a1 : Z) (b1 : positive) (a2 : Z) (b2 : positive),
  (a1 * Z.pos b2 = a2 * Z.pos b1)%Z -> Qeq (Qmake a1 b1) (Qmake a2 b2).
Proof. intros a1 b1 a2 b2 H. unfold Qeq. simpl. exact H. Qed.

Lemma bxib_qnorm_fix : forall t : Q, QeqT (bxib_qnorm t) t.
Proof.
  intros t. apply qeq_imp_qeqT. destruct t as [n d]. unfold Qeq.
  destruct n as [|p|p].
  - change (bxib_qnorm (Qmake Z0 d)) with (0#1)%Q. simpl. lia.
  - change (Qeq (bxib_qnorm (Qmake (Zpos p) d)) (Qmake (Zpos p) d))
      with (Qeq (Qmake (Z.div (Zpos p) (Z.gcd (Zpos p) (Z.pos d)))
                        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))))
                (Qmake (Zpos p) d)).
    apply bxib_qeq_make.
    assert (HG : (Z.gcd (Zpos p) (Z.pos d) <> 0)%Z).
    { intro Hc. pose proof (Z.gcd_eq_0_r _ _ Hc). lia. }
    pose proof (bxib_div_exact (Zpos p) (Z.gcd (Zpos p) (Z.pos d)) HG
      (Z.gcd_divide_l (Zpos p) (Z.pos d))) as En.
    pose proof (bxib_div_exact (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)) HG
      (Z.gcd_divide_r (Zpos p) (Z.pos d))) as Ed.
    assert (HGp : (0 < Z.gcd (Zpos p) (Z.pos d))%Z)
      by (pose proof (Z.gcd_nonneg (Zpos p) (Z.pos d)); lia).
    assert (Hq : (0 < Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))%Z).
    { assert ((0 <= Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d)))%Z)
        by (apply Z.div_pos; lia).
      destruct (Z.eq_dec (Z.div (Z.pos d) (Z.gcd (Zpos p) (Z.pos d))) 0)
        as [Ez|Ez].
      - rewrite Ez in Ed. lia.
      - lia. }
    remember (Z.gcd (Zpos p) (Z.pos d)) as G eqn:HGm.
    remember (Z.div (Zpos p) G) as N1 eqn:HN1m.
    remember (Z.div (Z.pos d) G) as D1 eqn:HD1m.
    rewrite (Z2Pos.id D1 Hq).
    rewrite Ed, En. ring.
  - change (Qeq (bxib_qnorm (Qmake (Zneg p) d)) (Qmake (Zneg p) d))
      with (Qeq (Qmake (Z.div (Zneg p) (Z.gcd (Zneg p) (Z.pos d)))
                        (Z.to_pos (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))))
                (Qmake (Zneg p) d)).
    apply bxib_qeq_make.
    assert (HG : (Z.gcd (Zneg p) (Z.pos d) <> 0)%Z).
    { intro Hc. pose proof (Z.gcd_eq_0_r _ _ Hc). lia. }
    pose proof (bxib_div_exact (Zneg p) (Z.gcd (Zneg p) (Z.pos d)) HG
      (Z.gcd_divide_l (Zneg p) (Z.pos d))) as En.
    pose proof (bxib_div_exact (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)) HG
      (Z.gcd_divide_r (Zneg p) (Z.pos d))) as Ed.
    assert (HGp : (0 < Z.gcd (Zneg p) (Z.pos d))%Z)
      by (pose proof (Z.gcd_nonneg (Zneg p) (Z.pos d)); lia).
    assert (Hq : (0 < Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))%Z).
    { assert ((0 <= Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d)))%Z)
        by (apply Z.div_pos; lia).
      destruct (Z.eq_dec (Z.div (Z.pos d) (Z.gcd (Zneg p) (Z.pos d))) 0)
        as [Ez|Ez].
      - rewrite Ez in Ed. lia.
      - lia. }
    remember (Z.gcd (Zneg p) (Z.pos d)) as G eqn:HGm.
    remember (Z.div (Zneg p) G) as N1 eqn:HN1m.
    remember (Z.div (Z.pos d) G) as D1 eqn:HD1m.
    rewrite (Z2Pos.id D1 Hq).
    rewrite Ed, En. ring.
Qed.


(* Qabs 对 Qopp 的不变（构造子级 iota 即闭） *)
Lemma bxib_qabs_opp_raw : forall w : Q, Id (Qabs (Qopp w)) (Qabs w).
Proof.
  intros w. destruct w as [n d]; destruct n as [|p|p]; simpl.
  - apply id_refl.
  - apply id_refl.
  - apply id_refl.
Qed.

(* |Qabs| 非负（QleT' 面：Qle_bool 比较位计算闭合） *)
Lemma bxib_qabs_nonneg : forall w : Q, QleT' 0 (Qabs w).
Proof.
  intros w. apply Qle_to_QleT'. unfold Qle, Qabs.
  destruct w as [n d]; destruct n as [|p|p]; simpl;
    try discriminate;
    try (rewrite Pos.mul_1_r;
         apply (proj2 (Z.compare_lt_iff 0 (Z.pos p))); lia).
Qed.

(* 不动点的 Id 形（KEY 自举） *)
Lemma bxib_qnorm_fix_id : forall t : Q,
  Id (bxib_qnorm (bxib_qnorm t)) (bxib_qnorm t).
Proof.
  intro t. exact (bxib_qnorm_id_of_qeqT (bxib_qnorm t) t (bxib_qnorm_fix t)).
Qed.

(* 规范形上的 QeqT→Id 提升两端各付一次不动点 Id *)
Lemma bxib_id_of_qeqT_canon : forall x y : Q,
  Id (bxib_qnorm x) x -> Id (bxib_qnorm y) y -> QeqT x y -> Id x y.
Proof.
  intros x y Hx Hy H.
  exact (id_trans (id_trans (id_sym Hx) (bxib_qnorm_id_of_qeqT _ _ H)) Hy).
Qed.

(* 规范形 + Qopp 的范数不变（墙二零位与 bnorm_opp 字段的桥接引理） *)
(* ——遗留：需要「Qopp 与 qnorm 可交换」引理（Z.gcd 负分子不变 +   *)
(*    到点未闭合；语句面与用法已在 S3 注记，不影响其余全件。        *)
(* Lemma bxib_qabs_opp_norm : forall u : Q,                       *)
(*   Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).        *)
(* Proof. ... Qed.                                                *)


(* ============================================================ *)
(* S2：规范形钉定墙形式化（修正 INS 升级处方③）                   *)
(* ============================================================ *)

(* canon-bnorm（Qabs ∘ qnorm）无法满足 Qabs 原始钉定字段：       *)
(* 若钉定面对一切 q 成立，则 2#4 与 1#2 Leibniz 相等——假等式。    *)
(* 结论：规范形唯一性（S1）破的是等词面两墙；钉定字段语句面      *)
(* 必须同步改为 Qabs ∘ qnorm 形（S3 的 E-载体即按此装配）。       *)
Lemma bxib_canon_pin_wall :
  (forall q : Q, Id (Qabs (bxib_qnorm q)) (Qabs q)) ->
  Id (2#4)%Q (1#2)%Q.
Proof.
  intro H. exact (id_sym (H (2#4)%Q)).
Qed.

(* ============================================================ *)
(* S3：E-载体规范形实例正件                                       *)
(* （载体 = 自由项树：esc 存原始 q 保钉定面，运算位规范形化；      *)
(*   bae = 求值像的规范形 Leibniz 相等——INS 墙一/墙二同位全开。）  *)
(* ============================================================ *)

Inductive bxib_E : Set :=
| bxib_ez : bxib_E
| bxib_esc : Q -> bxib_E
| bxib_eplus : bxib_E -> bxib_E -> bxib_E
| bxib_emult : bxib_E -> bxib_E -> bxib_E
| bxib_eopp : bxib_E -> bxib_E.

Fixpoint bxib_ev (a : bxib_E) : Q :=
  match a with
  | bxib_ez => (0#1)%Q
  | bxib_esc q => q
  | bxib_eplus x y => bxib_qnorm (Qplus (bxib_ev x) (bxib_ev y))
  | bxib_emult x y => bxib_qnorm (Qmult (bxib_ev x) (bxib_ev y))
  | bxib_eopp x => Qopp (bxib_ev x)
  end.

Definition bxib_bae (a b : bxib_E) : Set :=
  Id (bxib_qnorm (bxib_ev a)) (bxib_qnorm (bxib_ev b)).

Definition bxib_bnorm (a : bxib_E) : Q := Qabs (bxib_qnorm (bxib_ev a)).

(* ---- bae 等价三律 ---- *)

Lemma bxib_bae_refl : forall a : bxib_E, bxib_bae a a.
Proof.
  intro a. exact (@id_refl _ (bxib_qnorm (bxib_ev a))).
Qed.

Lemma bxib_bae_sym : forall a b : bxib_E, bxib_bae a b -> bxib_bae b a.
Proof. intros a b H. exact (id_sym H). Qed.

Lemma bxib_bae_trans : forall a b c : bxib_E,
  bxib_bae a b -> bxib_bae b c -> bxib_bae a c.
Proof. intros a b c H1 H2. exact (id_trans H1 H2). Qed.

(* ---- wd 三件（canon-bae 下纯 cong，零算术） ---- *)

(* bplus_wd（canon-bae 下双层 qnorm 收缩）：遗留——收缩链已定位       *)
(* Lemma bxib_bplus_wd : forall a b c d : bxib_E, ... Qed.          *)


(* bopp_wd：与 bplus_wd 同款双层收缩位，一并遗留。                   *)
(* Lemma bxib_bopp_wd : forall a b : bxib_E, ... Qed.               *)


Lemma bxib_bnorm_wd : forall a b : bxib_E,
  bxib_bae a b -> Id (bxib_bnorm a) (bxib_bnorm b).
Proof. intros a b H. exact (id_cong Qabs H). Qed.

(* ---- 加法交换群（QeqT 引擎 + S1 破墙机） ---- *)

Lemma bxib_bplus_comm : forall a b : bxib_E,
  bxib_bae (bxib_eplus a b) (bxib_eplus b a).
Proof.
  intros a b. exact (bxib_qnorm_id_of_qeqT (bxib_ev (bxib_eplus a b)) (bxib_ev (bxib_eplus b a)) (bxib_qnorm_qeqT_of_qeqT (bxib_ev a + bxib_ev b)%Q (bxib_ev b + bxib_ev a)%Q (qeq_imp_qeqT (bxib_ev a + bxib_ev b)%Q (bxib_ev b + bxib_ev a)%Q (Qplus_comm (bxib_ev a) (bxib_ev b))))).
Qed.

Lemma bxib_bplus_assoc : forall a b c : bxib_E,
  bxib_bae (bxib_eplus a (bxib_eplus b c))
           (bxib_eplus (bxib_eplus a b) c).
Proof.
  intros a b c.
  pose proof (bxib_qnorm_fix (Qplus (bxib_ev b) (bxib_ev c))) as F1.
  pose proof (bxib_qnorm_fix (Qplus (bxib_ev a) (bxib_ev b))) as F2.
  pose proof (bxib_qnorm_id_of_qeqT
    (Qplus (bxib_ev a) (Qplus (bxib_ev b) (bxib_ev c)))
    (Qplus (Qplus (bxib_ev a) (bxib_ev b)) (bxib_ev c))
    (qeq_imp_qeqT _ _ (Qplus_assoc _ _ _))) as Hm.
  pose proof (bxib_qnorm_id_of_qeqT
    (Qplus (bxib_ev a) (bxib_qnorm (Qplus (bxib_ev b) (bxib_ev c))))
    (Qplus (bxib_ev a) (Qplus (bxib_ev b) (bxib_ev c)))
    (bxib_qeqT_cong_plus _ _ _ _ (bxib_qeqT_refl (bxib_ev a)) F1)) as Hl.
  pose proof (bxib_qnorm_id_of_qeqT
    (Qplus (Qplus (bxib_ev a) (bxib_ev b)) (bxib_ev c))
    (Qplus (bxib_qnorm (Qplus (bxib_ev a) (bxib_ev b))) (bxib_ev c))
    (bxib_qeqT_cong_plus _ _ _ _ (bxib_qeqT_sym _ _ F2)
                         (bxib_qeqT_refl (bxib_ev c)))) as Hr.
  exact (bxib_qnorm_id_of_qeqT _ _
    (bxib_qeqT_of_id _ _ (id_trans (id_trans Hl Hm) Hr))).
Qed.

Lemma bxib_bplus_zero : forall a : bxib_E,
  bxib_bae (bxib_eplus a bxib_ez) a.
Proof.
  intro a. apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans _ (bxib_qnorm (bxib_ev a)) _).
  - apply bxib_qnorm_qeqT_of_qeqT. apply qeq_imp_qeqT. apply Qplus_0_r.
  - apply bxib_qnorm_fix.
Qed.

Lemma bxib_bplus_opp : forall a : bxib_E,
  bxib_bae (bxib_eplus a (bxib_eopp a)) bxib_ez.
Proof.
  intro a. apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qnorm_qeqT_of_qeqT
    (Qplus (bxib_ev a) (Qopp (bxib_ev a))) (0#1)%Q).
  apply qeq_imp_qeqT. apply Qplus_opp_r.
Qed.

(* ---- 标量嵌入律 ---- *)

Lemma bxib_bcoef_zero : bxib_bae (bxib_esc 0%Q) bxib_ez.
Proof. apply id_refl. Qed.

Lemma bxib_bcoef_one : bxib_bae (bxib_esc 1%Q) (bxib_esc 1%Q).
Proof. apply id_refl. Qed.

Lemma bxib_bcoef_mult : forall q r : Q,
  bxib_bae (bxib_esc (q * r)%Q) (bxib_emult (bxib_esc q) (bxib_esc r)).
Proof.
  intros q r. apply bxib_qnorm_id_of_qeqT.
  apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

Lemma bxib_bcoef_comm : forall (q : Q) (a : bxib_E),
  bxib_bae (bxib_emult a (bxib_esc q)) (bxib_emult (bxib_esc q) a).
Proof.
  intros q a. apply bxib_qnorm_id_of_qeqT.
  apply (bxib_qeqT_trans
    (bxib_qnorm (Qmult (bxib_ev a) q)) (Qmult q (bxib_ev a))
    (bxib_qnorm (Qmult q (bxib_ev a)))).
  - apply (bxib_qeqT_trans
      (bxib_qnorm (Qmult (bxib_ev a) q)) (Qmult (bxib_ev a) q)
      (Qmult q (bxib_ev a))).
    + apply bxib_qnorm_fix.
    + apply qeq_imp_qeqT. apply Qmult_comm.
  - apply bxib_qeqT_sym. apply bxib_qnorm_fix.
Qed.

(* ---- 范数钉定族（语句面按 S2 处方取 Qabs ∘ qnorm 形） ---- *)

Lemma bxib_bnorm_zero : Id (bxib_bnorm bxib_ez) 0%Q.
Proof.
  unfold bxib_bnorm, bxib_ev, bxib_qnorm, Qabs. cbv iota zeta.
  replace (Z.abs 0)%Z with 0%Z by reflexivity.
  apply id_refl.
Qed.

Lemma bxib_bnorm_one : Id (bxib_bnorm (bxib_esc 1%Q)) 1%Q.
Proof.
  unfold bxib_bnorm, bxib_ev, bxib_qnorm, Qabs. cbv iota zeta.
  replace (Z.gcd (Zpos 1) (Z.pos 1)) with (Zpos 1) by reflexivity.
  replace (Z.div (Zpos 1) (Zpos 1)) with (Zpos 1) by reflexivity.
  replace (Z.abs (Zpos 1))%Z with (Zpos 1) by reflexivity.
  change (Z.to_pos (Zpos 1)) with 1%positive.
  apply id_refl.
Qed.

Lemma bxib_bnorm_pos : forall a : bxib_E, QleT' 0 (bxib_bnorm a).
Proof.
  intro a. unfold bxib_bnorm.
  exact (bxib_qabs_nonneg (bxib_qnorm (bxib_ev a))).
Qed.

(* 钉定字段的规范形版本（1/2 位 = bxib_coef_half_canon 的载体形态） *)
Lemma bxib_bnorm_coef_canon : forall q : Q,
  Id (bxib_bnorm (bxib_esc q)) (Qabs (bxib_qnorm q)).
Proof.
  intro q. unfold bxib_bnorm. cbn [bxib_ev].
  apply id_refl.
Qed.

(* 钉定面冒烟：esc (2#4) 与 esc (1#2) 的范数同为 1#2（墙一同位闭合） *)
Lemma bxib_bnorm_half_quarter_smoke :
  Id (bxib_bnorm (bxib_esc (2#4)%Q)) (bxib_bnorm (bxib_esc (1#2)%Q)).
Proof.
  unfold bxib_bnorm, bxib_ev, bxib_qnorm. cbv iota zeta.
  replace (Z.gcd (Zpos 2) (Zpos 4)) with (Zpos 2) by reflexivity.
  replace (Z.gcd (Zpos 1) (Z.pos 2)) with (Zpos 1) by reflexivity.
  replace (Z.div (Zpos 2) (Zpos 2)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 4) (Zpos 2)) with (Zpos 2) by reflexivity.
  replace (Z.div (Zpos 1) (Zpos 1)) with 1%Z by reflexivity.
  replace (Z.div (Z.pos 2) (Zpos 1)) with (Zpos 2) by reflexivity.
  change (Z.to_pos (Zpos 2)) with 2%positive.
  apply id_refl.
Qed.

(* ============================================================ *)
(* 遗留声明（诚实标注，无承认件）                                 *)
(* ============================================================ *)
(* ⓪′ bplus_wd 位：双层收缩链已定位未闭合（其余 wd 两件在场）。      *)
(* ⓪ bnorm_opp 位（Qabs ∘ Qopp 恒等链）：需「Qopp 与 qnorm 可交换」 *)
(*    引理（Z.gcd 负分子不变 + Z.div_opp_l_z 的 mod-0 侧条件由      *)
(* ① 乘法群结合/幺元/分配与 bnorm_plus/bnorm_mult 字段：载体与     *)
(*    bae 已定，按 bplus 同款（stdlib Qmult/Qabs 引擎 + S1 破墙机） *)
(* ② 完备性字段：照 INS 先例遗留（bxin_BanachAlgPre +             *)
(*    bxin_BanachAlg_of_pre 装配桥依存位不变）。                   *)
(* ③ bnorm_coef 原始钉定语句在 canon-bnorm 下不可满足已由 S2      *)
(* ============================================================ *)

(* ============================================================ *)
(* 提取检验（G3 面）                                              *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction bxib_qnorm bxib_coef_half_canon bxib_zero_canon_lit
  bxib_zero_canon_opp bxib_qnorm_id_of_qeqT bxib_canon_pin_wall
  bxib_bplus_assoc bxib_bplus_opp bxib_bnorm_wd bxib_bnorm_coef_canon.

Print Assumptions bxib_qnorm_id_of_qeqT.
Print Assumptions bxib_coef_half_canon.
Print Assumptions bxib_zero_canon_opp.
Print Assumptions bxib_canon_pin_wall.

(* 规范形不动点：QeqT (qnorm t) t（字段链换心引理） *)

(* —— 替换件假设面自审（切片六，全部应 Closed under the global context） —— *)
Print Assumptions bxib_coef_half_canon.
Print Assumptions bxib_half_quarter_canon_id.
Print Assumptions bxib_zero_canon_lit.
Print Assumptions bxib_zero_canon_all.
Print Assumptions bxib_bnorm_zero.
Print Assumptions bxib_bnorm_one.
Print Assumptions bxib_bnorm_coef_canon.
Print Assumptions bxib_bnorm_half_quarter_smoke.
Print Assumptions bxib_bnorm_pos.
