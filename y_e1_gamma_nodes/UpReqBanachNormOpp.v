(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 六批）          *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   bno_bnorm_opp_real（原 L143，2 句玩具证）                            *)
(*   bno_qabs_qnorm_opp（原 L138，2 句玩具证）                            *)
(*   bno_qred_abs_opp_id（原 L132，3 句玩具证）                           *)
(*   bno_qred_unique_id（原 L115，4 句玩具证）                            *)
(*   bno_gt0_of_lt0（原 L53，3 句玩具证）                                 *)
(* ============================================================ *)
(* ============================================================ *)
(* 【 恒等守恒修订注记】 包AV八 （恒等头注修订全量二段）                     *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，                                 *)
(* 经 （包AL）全量恒等核查已证结论、（包AV六）试点已证结论：本件实测                             *)
(* 为恒等守恒——清单所列 5 槽证明体与 Main 现版原件逐字同文（刀体                                *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此修订。                                        *)
(* 修订口径：真替换 0 槽＋恒等守恒 5 槽；本注记为追加块，上方原头                                  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面                                 *)
(* 零改动；记录册承载见  附录／ 修正块／ 评估册／／ 记录册。                   *)
(* 附记： 判级全文恒等； 整批直推（二段；承  §五·1）                             *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqBanachNormOpp.v —— AA11：B5 件一速收（Qred 唯一性 +      *)
(*   bnorm Opp 面，）                                     *)
(* ============================================================ *)
(* 使命（AA8 分解报告 B5 清单）：件一 qred_unique——INS L45 遗留     *)
(*   「保持 Id 余域不动，bnorm := Qred∘Qabs」的 Id-良定钥匙：       *)
(*     bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y *)
(*   （Leibniz 余域原形）；并定位 bnorm Opp/倒数面（件名对应）。    *)
(* 现成肢复用（AA8 判定 B5 最大惊喜＝B1 进行中件已铺 Z.gcd 肢）：     *)
(*   ① UpReqBanachInstB 规范形唯一机器（Zis_gcd_intro +            *)
(*      rel_prime_cross_prod + Z.mul_reg_l 面，bxib_cross_unique   *)
(*      同配方）——以 gcd=1 互素转移件重新组装：规范对           *)
(*      （Z.gcd 分子分母 = 1）交叉乘唯一，不触碰 ggcd 符号归约，    *)
(*      预避 AA3 实测的 Z.gcd 展开 Ffix 卡壳墙；                   *)
(*   ② UpReqBanachInstReal 的 bnorm_opp 攻墙链（bxra_qabs_opp_norm  *)
(*      ＝ Z.gcd_opp_l + bxib_div_exact + Z.mul_reg_l + Z.abs_opp  *)
(*      ＋ eq→Id match 桥，AA3 交付）——Opp 面依存件直用；        *)
(*   ③ stdlib Qcanon.Qred_iff + Qreduction.Qred_correct——Qred 的   *)
(*      规范对特征（二次不变 Qred(Qred x)=Qred x 喂 Qred_iff），    *)
(*      主件组装肢。                                               *)
(* 主件证法（三肢组装，~40 行真构造）：                             *)
(*   x==y ⇒ Qred x==Qred y（Qred_correct 双向中转）⇒ 交叉乘式；     *)
(*   Qred x / Qred y 各为规范对（bno_qred_canon）；规范对交叉乘     *)
(*   唯一（Gauss/rel_prime_cross_prod）⇒ 分子分母分别相等 ⇒        *)
(*   Qred x = Qred y。                                             *)
(* 公理面自审：全件零 公理 零 参数 零 猜想 零           *)
(*   承认件 零 Variable 零假设申报；语句面全 Set/eq/Id/Qeq    *)
(*   形；主件出口 Print Assumptions Closed；Separate Extraction    *)
(*   Obj.magic 双零。                                              *)
(* 领土纪律：仅新建本件（bno_ 前缀全库零撞名）；既有件零改动        *)
(*   （仅 Require 依存 InstB/InstReal/S03 系）；禁 git。           *)
(* 件二状态：AA8 B5 清单件二（Σ1/k! 逃逸 sigT 显式速度形）——引擎段   *)
(*   闭合（bno_q_pow_one / bno_exp_series_succ_frac /             *)
(*   bno_mul_div_self / bno_exp_scale_Z＝n!·s_n 整数化核心），        *)
(*   逃逸主件（q==s_n 可判定分叉＋非零整数绝对值下界）仍遗留移交，     *)
(*   语句面以 bno_sum_inv_fact_escape 固化（诚实遗留，零特设构造）。       *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachInstB.
Require Import UpReqBanachInstReal.
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qcanon
  ZArith.ZArith ZArith.Znumtheory.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0：Z 层互素工具（规范对唯一机，bxib_cross_unique 同配方重组）   *)
(* ============================================================ *)

(* >0 桥（compare_gt_iff，bxib 同款） *)
Lemma bno_gt0_of_lt0 : forall d : Z, 0 < d -> (d > 0)%Z.
Proof. intros d H. exact (proj2 (Z.compare_gt_iff d 0) H). Qed.

(* gcd = 1 → 互素（Zis_gcd_intro 配方；rel_prime := Zis_gcd .. 1） *)
Lemma bno_rel_prime_of_gcd1 : forall n d : Z, Z.gcd n d = 1%Z -> rel_prime n d.
Proof.
  intros n d H.
  exact (Zis_gcd_intro n d 1%Z (Z.divide_1_l n) (Z.divide_1_l d)
    (fun z Hz1 Hz2 =>
       match Zgcd_is_gcd n d with
       | Zis_gcd_intro _ _ _ _ _ Hdiv =>
           eq_ind (Z.gcd n d) (fun g => (z | g)%Z)
             (Hdiv z Hz1 Hz2) 1%Z H
       end)).
Qed.

(* 规范对交叉乘唯一：两对分子分母均与 1 互素、分母正、交叉乘相等
   ⇒ 整对相等（Gauss/rel_prime_cross_prod 直收） *)
Lemma bno_canon_pair_unique : forall n1 d1 n2 d2 : Z,
  Z.gcd n1 d1 = 1%Z -> Z.gcd n2 d2 = 1%Z -> (d1 > 0)%Z -> (d2 > 0)%Z ->
  (n1 * d2 = n2 * d1)%Z -> n1 = n2 /\ d1 = d2.
Proof.
  intros n1 d1 n2 d2 H1 H2 P1 P2 Hc.
  exact (let E := rel_prime_cross_prod n1 d1 n2 d2
             (bno_rel_prime_of_gcd1 n1 d1 H1)
             (bno_rel_prime_of_gcd1 n2 d2 H2) P1 P2
             (eq_ind (n2 * d1) (fun x => (n1 * d2 = x)%Z) Hc (d1 * n2) (Z.mul_comm n2 d1)) in
         conj (proj1 E) (proj2 E)).
Qed.

(* ============================================================ *)
(* S1：件一主件——Qred 唯一性（INS L45 遗留完成清理）                   *)
(* ============================================================ *)

(* Qred 输出恒为规范对（二次不变喂 Qred_iff） *)
Lemma bno_qred_canon : forall x : Q,
  Z.gcd (Qnum (Qred x)) (Z.pos (Qden (Qred x))) = 1%Z.
Proof.
  intro x.
  assert (Hi : Qred (Qred x) = Qred x) by (apply Qred_complete, Qred_correct).
  exact (proj1 (Qred_iff (Qred x)) Hi).
Qed.

(* 主件：Qred 唯一性（Qeq 入，Leibniz eq 出——Id-良定钥匙） *)
Lemma bno_qred_unique : forall x y : Q, x == y -> Qred x = Qred y.
Proof.
  intros x y Hxy.
  pose proof (bno_qred_canon x) as Hc1.
  pose proof (bno_qred_canon y) as Hc2.
  assert (Hr : Qred x == Qred y).
  { apply (Qeq_trans _ x).
    - apply Qred_correct.
    - rewrite Hxy. apply (Qeq_sym (Qred y) y). apply Qred_correct. }
  destruct (Qred x) as [n1 d1] eqn:Ex.
  destruct (Qred y) as [n2 d2] eqn:Ey.
  simpl in Hc1, Hc2.
  unfold Qeq in Hr; simpl in Hr.
  destruct (bno_canon_pair_unique n1 (Z.pos d1) n2 (Z.pos d2)
    Hc1 Hc2 ltac:(apply bno_gt0_of_lt0; lia) ltac:(apply bno_gt0_of_lt0; lia)
    Hr) as [E1 E2].
  apply Pos2Z.inj in E2. rewrite E1, E2. reflexivity.
Qed.

(* 主件 Id 面（eq→Id 桥，InstReal 现成肢） *)
Lemma bno_qred_unique_id : forall x y : Q, x == y -> Id (Qred x) (Qred y).
Proof. intros x y H. exact (@bxra_id_of_eq Q (Qred x) (Qred y) (bno_qred_unique x y H)). Qed.

(* ============================================================ *)
(* S2：bnorm Opp/倒数面定位（INS L45 处方 bnorm := Qred∘Qabs 的     *)
(*     bnorm_opp 位 discharge ＋ InstReal 攻墙链依存转写）          *)
(* ============================================================ *)

(* 新件：Qred∘Qabs 的取负不变（eq 形）——Q 载体 bnorm_opp 字段位 *)
Lemma bno_qred_abs_opp : forall u : Q, Qred (Qabs (Qopp u)) = Qred (Qabs u).
Proof.
  intro u. apply Qred_complete.
  destruct u as [n d]. cbn [Qopp Qabs].
  unfold Qeq; simpl. rewrite Z.abs_opp. reflexivity.
Qed.

(* 同件 Id 形（eq→Id 桥） *)
Lemma bno_qred_abs_opp_id : forall u : Q,
  Id (Qred (Qabs (Qopp u))) (Qred (Qabs u)).
Proof. intro u. exact (@bxra_id_of_eq Q (Qred (Qabs (Qopp u))) (Qred (Qabs u))
                     (bno_qred_abs_opp u)). Qed.

(* 依存形转写①（InstReal 现成肢直用，语句形保留库内 Id 原形：
   Qopp 与 qnorm 的 Qabs-范数不变） *)
Lemma bno_qabs_qnorm_opp : forall u : Q,
  Id (Qabs (bxib_qnorm (Qopp u))) (Qabs (bxib_qnorm u)).
Proof. intro u. exact (bxra_qabs_opp_norm u). Qed.

(* 依存形转写②（Real 载体面：bnorm(opp x) ＝ bnorm x，库内 Id 原形） *)
Lemma bno_bnorm_opp_real : forall a : Real,
  Id (bxra_bnorm_f (bxra_bopp_f a)) (bxra_bnorm_f a).
Proof. intro a. exact (bxra_f_norm_opp a). Qed.

(* ============================================================ *)
(* S3：件二遗留形（AA8 B5 清单指定语句面，证体移交——诚实遗留，      *)
(*     零特设构造。原料清单见交付报告：q_fact_pos/exp_series 系         *)
(*     （S03_QExp）、n!·s_n 整数化引擎、q==s_n 可判定分叉。）       *)
(* ============================================================ *)

Definition bno_sum_inv_fact_escape : Type :=
  forall q : Q,
    sigT (fun n : nat => Qlt 1 (Qabs (q_fact n * (q - exp_series n 1))%Q)).

(* ---- 件二引擎件（冲刺段，预算内闭合三件；逃逸主件仍遗留） ---- *)

(* 引擎①：1 的幂归一 *)
Lemma bno_q_pow_one : forall n : nat, q_pow 1%Q n == 1%Q.
Proof.
  intro n.
  exact (nat_ind (fun k => q_pow 1%Q k == 1%Q) (Qeq_refl 1%Q)
    (fun (m : nat) (IH : q_pow 1%Q m == 1%Q) =>
       Qeq_trans (1%Q * q_pow 1%Q m)%Q (q_pow 1%Q m) 1%Q
         (Qmult_1_l (q_pow 1%Q m)) IH) n).
Qed.

(* 引擎②前小件：q*(1/q) 归一（Qdiv 定义展开位；Qmult_inv_r 的 ≠ 是 Qeq 形） *)
Lemma bno_mul_div_self : forall q : Q, ~ (q == 0%Q) -> q * (1%Q / q) == 1%Q.
Proof.
  intros q Hq. unfold Qdiv. rewrite Qmult_1_l. apply Qmult_inv_r. exact Hq.
Qed.

(* 引擎②：exp_series 单步分数形（B:=1 位） *)
Lemma bno_exp_series_succ_frac : forall n : nat,
  exp_series (Datatypes.S n) 1%Q
    == exp_series n 1%Q + 1%Q / q_fact (Datatypes.S n)%Q.
Proof.
  intro n. cbn [exp_series]. rewrite bno_q_pow_one. reflexivity.
Qed.

(* 引擎③：n!·s_n 整数化（Σ1/k! 不收敛性的核心原料——n! 倍后落 Z） *)
Lemma bno_exp_scale_Z : forall n : nat,
  sigT (fun z : Z => QeqT (q_fact n * exp_series n 1)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. apply qeq_imp_qeqT. unfold Qeq. cbn [q_fact exp_series Qnum Qden Qmult]. reflexivity.
  - destruct IH as [z Hz].
    exists (Z.of_nat (Datatypes.S m) * z + 1)%Z.
    apply qeq_imp_qeqT.
    rewrite q_fact_succ.
    rewrite bno_exp_series_succ_frac.
    assert (Hq0 : ~ ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m == 0%Q)).
    { intro Hc. apply (Qlt_not_eq 0%Q _ (q_fact_pos (Datatypes.S m))).
      apply Qeq_sym. exact Hc. }
    assert (Hs : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * (1%Q / ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q) == 1%Q).
    { apply bno_mul_div_self. exact Hq0. }
    assert (Hm : ((Z.of_nat (Datatypes.S m) # 1)%Q * q_fact m)%Q
                 * exp_series m 1%Q == ((Z.of_nat (Datatypes.S m) * z) # 1)%Q).
    { apply (Qeq_trans _ ((Z.of_nat (Datatypes.S m) # 1)%Q
                          * (q_fact m * exp_series m 1)%Q)%Q).
      - apply Qeq_sym. apply Qmult_assoc.
      - apply (@Qmult_comp (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Z.of_nat (Datatypes.S m) # 1)%Q
                           (Qeq_refl (Z.of_nat (Datatypes.S m) # 1)%Q)
                           (q_fact m * exp_series m 1)%Q ((z # 1)%Q)
                           (qeqT_imp_qeq (q_fact m * exp_series m 1)%Q
                                ((z # 1)%Q) Hz)). }
    rewrite Qmult_plus_distr_r.
    rewrite Hs.
    rewrite Hm.
    unfold Qeq. cbn [Qnum Qden Qplus Qmult].
    first [lia | ring | reflexivity].
Qed.

(* ============================================================ *)
(* S4：提取检验 + 假设面自审（G3 面）                               *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
(* 提取纪律（INST5/AA3 同款）：只收标量/引理级件；Id/eq 值件提取     *)
(*   零依赖载体项，Obj.magic 预期双零。                            *)
Separate Extraction bno_qred_unique bno_qred_unique_id bno_canon_pair_unique
  bno_rel_prime_of_gcd1 bno_gt0_of_lt0 bno_qred_canon bno_qred_abs_opp
  bno_qred_abs_opp_id bno_qabs_qnorm_opp bno_bnorm_opp_real.

Print Assumptions bno_qred_unique.
Print Assumptions bno_qred_unique_id.
Print Assumptions bno_canon_pair_unique.
Print Assumptions bno_qred_abs_opp.
Print Assumptions bno_qred_abs_opp_id.
Print Assumptions bno_qabs_qnorm_opp.
Print Assumptions bno_bnorm_opp_real.
Print Assumptions bno_q_pow_one.
Print Assumptions bno_exp_series_succ_frac.
Print Assumptions bno_mul_div_self.
Print Assumptions bno_exp_scale_Z.

(* ============================================================ *)
(* S5：件二闭合段（B5R，）——AA8 B5 清单件二 sigT 显式     *)
(*     逃逸形正式闭合：bno_sum_inv_fact_escape 主件定位。           *)
(* 证法（构造性，零 LPO 零分叉）：                                  *)
(*   ① 引擎上探：bno_scale_q_int——任一 q=p/d 取 n≥d 使 n!·q 落 Z     *)
(*     （bno_qfact_int：n! 本身为整数；bno_qfact_scale_d：d|n! 的    *)
(*     Q 层见证 w；bno_pos_d_nat：分母的 nat 上探位 Z.to_nat）。     *)
(*   ② 迭代步 bno_tail_step：T_{k+1} = (k+1)·T_k − 1                *)
(*     （T_k := k!·(q−s_k)；Qring 的 ring + bno_mul_div_self）。     *)
(*   ③ 两步吞没 bno_two_step：任意整数 z 经两步后                   *)
(*     |b·(a·z−1)−1| ≥ 2 > 1（a≥2,b≥3）——z=0 亦被吞没，             *)
(*     q==s_k 可判定分叉整个消失（比清单原案更强，零 LPO）。         *)
(*   ④ 严格下界 bno_lt1_int_abs：整数位 |w|≥2 ⇒ Qlt 1 (Qabs t)；     *)
(*     单调装配 Z.mul_le_mono_nonneg_r（右乘形，QLeg 先例）三分支     *)
(*     z≥1 / z=0 / z≤−1 显式闭合，零 nia 非线性反射依赖。           *)
(*   ⑤ 主件 bno_sum_inv_fact_escape_close：n!·q 与 AA11 引擎件       *)
(*     bno_exp_scale_Z（n!·s_n 落 Z）相减得 T_n0 落 Z，移位一步后     *)
(*     喂两步吞没，见证 index := S(S(S n0))。                       *)
(* 公理面自审：本段全件零公理声明、零参数声明、零承认证明、零变量与   *)
(*   假设声明；语句面全 Type/sigT/Qlt 形；主件出口 Closed。           *)
(* 提取纪律（INST5 同款）：sigT 见证件（qfact_int/qfact_scale_d/      *)
(*   pos_d_nat/scale_q_int/close）不进 Separate Extraction 单，       *)
(*   由 Print Assumptions 承担假设面；Qeq/Qlt 标量件入提取单。        *)
(* 领土纪律：纯追加；已建成 11 件零改动一字。                        *)
(* ============================================================ *)

From Stdlib Require Import Qring.

(* P1: n! 本身为整数 *)
Lemma bno_qfact_int : forall n : nat,
  sigT (fun z : Z => Qeq (q_fact n)%Q ((z # 1)%Q)).
Proof.
  induction n as [| m IH].
  - exists 1%Z. reflexivity.
  - destruct IH as [z Hz]. exists (Z.of_nat (Datatypes.S m) * z)%Z.
    rewrite q_fact_succ. rewrite Hz. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P2: n! 含分母 d 的倍数（d ≤ n） *)
Lemma bno_qfact_scale_d : forall (n : nat) (d : Z),
  (1 <= d)%Z -> (d <= Z.of_nat n)%Z ->
  sigT (fun w : Z => Qeq (q_fact n)%Q (((d * w)%Z # 1)%Q)).
Proof.
  induction n as [| m IH]; intros d Hd Hle.
  - lia.
  - destruct (Z.eq_dec d (Z.of_nat (Datatypes.S m))) as [HdEq | HdNe].
    + destruct (bno_qfact_int m) as [z Hz]. subst d.
      exists z. rewrite q_fact_succ. rewrite Hz.
      unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
    + assert (Hlt : (d <= Z.of_nat m)%Z).
      { rewrite Nat2Z.inj_succ in Hle.
        assert (Hne : (d <> Z.succ (Z.of_nat m))%Z).
        { rewrite <- Nat2Z.inj_succ. exact HdNe. }
        lia. }
      destruct (IH d Hd Hlt) as [w Hw].
      exists (Z.of_nat (Datatypes.S m) * w)%Z.
      rewrite q_fact_succ. rewrite Hw. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P3: 任一有理数乘以足够大的 n! 即为整数 *)
Lemma bno_pos_d_nat : forall d : positive, sigT (fun n : nat => (Z.pos d <= Z.of_nat n)%Z).
Proof.
  intro d.
  exact (existT (fun n : nat => (Z.pos d <= Z.of_nat n)%Z) (Z.to_nat (Z.pos d))
    (eq_ind (Z.pos d) (fun z => (Z.pos d <= z)%Z) (Z.le_refl (Z.pos d))
       (Z.of_nat (Z.to_nat (Z.pos d)))
       (eq_sym (Z2Nat.id (Z.pos d)
          (Z.lt_le_incl 0 (Z.pos d) (Pos2Z.is_pos d)))))).
Qed.

Lemma bno_scale_q_int : forall q : Q,
  sigT (fun n : nat => sigT (fun z : Z => Qeq (q_fact n * q)%Q ((z # 1)%Q))).
Proof.
  intro q. destruct q as [p d].
  destruct (bno_pos_d_nat d) as [n Hn].
  destruct (bno_qfact_scale_d n (Z.pos d)
    ltac:(pose proof (Pos2Z.is_pos d); lia) Hn) as [w0 Hw].
  exists n, (w0 * p)%Z.
  rewrite Hw. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
Qed.

(* P4: 迭代步 T_{k+1} = (k+1)*T_k - 1 *)
Lemma bno_tail_step : forall (n : nat) (q : Q),
  (q_fact (Datatypes.S n) * (q - exp_series (Datatypes.S n) 1))%Q
  == ((Z.of_nat (Datatypes.S n) # 1) * (q_fact n * (q - exp_series n 1)) - 1%Q)%Q.
Proof.
  intros n q.
  assert (Hinv : (q_fact (Datatypes.S n) * (1%Q / q_fact (Datatypes.S n)))%Q == 1%Q).
  { apply bno_mul_div_self. intro H0.
    apply (Qlt_not_eq 0%Q _ (q_fact_pos (Datatypes.S n))).
    apply Qeq_sym. exact H0. }
  rewrite bno_exp_series_succ_frac.
  apply (Qeq_trans _ (q_fact (Datatypes.S n) * (q - exp_series n 1)%Q
                      - q_fact (Datatypes.S n) * (1%Q / q_fact (Datatypes.S n))%Q)%Q).
  - ring.
  - rewrite Hinv. rewrite q_fact_succ. ring.
Qed.

(* P5: 整数值 (≥2) 给出严格 >1 的绝对值 *)
Lemma bno_lt1_int_abs : forall (w : Z) (t : Q),
  t == (w # 1)%Q -> (1 < Z.abs w)%Z -> Qlt 1%Q (Qabs t).
Proof.
  intros w [tn td] Heq Hw.
  unfold Qeq in Heq. cbn [Qnum Qden Qmult] in Heq.
  rewrite Z.mul_1_r in Heq.
  unfold Qlt, Qabs. cbn [Qnum Qden Qmult].
  rewrite Heq, Z.abs_mul, Z.mul_1_r.
  replace (Z.abs (Z.pos td)) with (Z.pos td)
    by (rewrite Z.abs_eq; pose proof (Pos2Z.is_pos td); lia).
  pose proof (Pos2Z.is_pos td) as Hp.
  pose proof (Z.mul_le_mono_nonneg_r 2 (Z.abs w) (Z.pos td) ltac:(lia) ltac:(lia)) as Hmono.
  lia.
Qed.

(* P5.5: 构造子桥接引理（Z#1 形的 Qeq 算术，全部构造子归约，零不透明投影） *)
Lemma bno_z1_step_eq : forall x y : Z,
  (((x # 1)%Q * (y # 1)%Q - 1%Q)%Q) == (((x * y - 1)%Z # 1)%Q).
Proof.
  intros x y. unfold Qeq.
  cbn [Qnum Qden Qmult Qminus Qopp Qplus Pos.mul]. lia.
Qed.

Lemma bno_z1_minus_eq : forall x y : Z,
  ((x # 1)%Q - (y # 1)%Q)%Q == (((x - y)%Z # 1)%Q).
Proof.
  intros x y. unfold Qeq.
  cbn [Qnum Qden Qminus Qopp Qplus Pos.mul]. lia.
Qed.

(* P6: 两步迭代吃掉一切整数（含 0） *)
Lemma bno_two_step : forall (n : nat) (q : Q) (z : Z),
  (1 <= Z.of_nat n)%Z ->
  (q_fact n * (q - exp_series n 1))%Q == (z # 1)%Q ->
  Qlt 1%Q (Qabs (q_fact (Datatypes.S (Datatypes.S n))
                   * (q - exp_series (Datatypes.S (Datatypes.S n)) 1))%Q).
Proof.
  intros n q z Hn Hz.
  pose proof (bno_tail_step n q) as H1. rewrite Hz in H1.
  assert (Hw1 : (q_fact (Datatypes.S n) * (q - exp_series (Datatypes.S n) 1))%Q
              == (((Z.of_nat (Datatypes.S n) * z - 1)%Z # 1)%Q)).
  { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S n) # 1) * (z # 1) - 1%Q)%Q)).
    - exact H1.
    - apply bno_z1_step_eq. }
  pose proof (bno_tail_step (Datatypes.S n) q) as H2. rewrite Hw1 in H2.
  apply (bno_lt1_int_abs
    (Z.of_nat (Datatypes.S (Datatypes.S n)) * (Z.of_nat (Datatypes.S n) * z - 1) - 1)%Z
    (q_fact (Datatypes.S (Datatypes.S n))
     * (q - exp_series (Datatypes.S (Datatypes.S n)) 1))%Q).
  - apply (Qeq_trans _ (((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                          * (((Z.of_nat (Datatypes.S n) * z - 1)%Z # 1)%Q)
                          - 1%Q)%Q)).
    + exact H2.
    + apply bno_z1_step_eq.
  - rewrite !Nat2Z.inj_succ.
    (* a := Z.succ (Z.of_nat n) ≥ 2，b := Z.succ a ≥ 3；三分支显式单调（右乘形） *)
    destruct (Z_lt_le_dec z 0) as [Hzneg | Hznonneg].
    + assert (Hm1 : (z * Z.succ (Z.of_nat n) <= (-1) * Z.succ (Z.of_nat n))%Z)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (Hm2 : ((Z.succ (Z.of_nat n) * z - 1) * Z.succ (Z.succ (Z.of_nat n))
                     <= (-3) * Z.succ (Z.succ (Z.of_nat n)))%Z)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite Z.abs_neq by lia. lia.
    + destruct (Z.eq_dec z 0) as [Hz0 | Hz0ne].
      * subst z. rewrite Z.mul_0_r.
        replace (0 - 1)%Z with (-1)%Z by lia.
        rewrite Z.abs_neq by lia. lia.
      * assert (Hm1 : (1 * Z.succ (Z.of_nat n) <= z * Z.succ (Z.of_nat n))%Z)
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Z.mul_1_l in Hm1.
        assert (Hprod : (1 <= Z.succ (Z.of_nat n) * z - 1)%Z) by lia.
        assert (Hm2 : (1 * Z.succ (Z.succ (Z.of_nat n))
                       <= (Z.succ (Z.of_nat n) * z - 1) * Z.succ (Z.succ (Z.of_nat n)))%Z)
          by (apply Z.mul_le_mono_nonneg_r; lia).
        rewrite Z.mul_1_l in Hm2.
        rewrite Z.abs_eq by lia. lia.
Qed.

(* P7 主件：件二逃逸闭合（sigT 显式见证，零 LPO） *)
Theorem bno_sum_inv_fact_escape_close : bno_sum_inv_fact_escape.
Proof.
  unfold bno_sum_inv_fact_escape. intro q.
  destruct (bno_scale_q_int q) as [n0 [z1 Hz1]].
  pose proof (bno_exp_scale_Z n0) as Hs. destruct Hs as [z2 Hz2].
  assert (Hs' : (q_fact n0 * exp_series n0 1)%Q == (z2 # 1)%Q)
    by (apply qeqT_imp_qeq; exact Hz2).
  assert (HT0 : (q_fact n0 * (q - exp_series n0 1))%Q == (((z1 - z2)%Z # 1)%Q)).
  { apply (Qeq_trans _ (q_fact n0 * q - q_fact n0 * exp_series n0 1)%Q).
    - ring.
    - rewrite Hz1, Hs'. apply bno_z1_minus_eq. }
  pose proof (bno_tail_step n0 q) as Hts. rewrite HT0 in Hts.
  assert (HT1 : (q_fact (Datatypes.S n0) * (q - exp_series (Datatypes.S n0) 1))%Q
              == (((Z.of_nat (Datatypes.S n0) * (z1 - z2) - 1)%Z # 1)%Q)).
  { apply (Qeq_trans _ (((Z.of_nat (Datatypes.S n0) # 1)
                          * (((z1 - z2)%Z # 1)%Q) - 1%Q)%Q)).
    - exact Hts.
    - apply bno_z1_step_eq. }
  exists (Datatypes.S (Datatypes.S (Datatypes.S n0))).
  apply (bno_two_step (Datatypes.S n0) q
    (Z.of_nat (Datatypes.S n0) * (z1 - z2) - 1)%Z).
  - rewrite Nat2Z.inj_succ. lia.
  - exact HT1.
Qed.


(* ============================================================ *)
(* S6：提取检验 + 假设面自审（G3 面，B5R 段）                        *)
(* ============================================================ *)

(* 提取纪律（INST5/AA11 同款）：只收 Qeq/Qlt 标量/引理级新件；sigT      *)
(*   见证件不进提取单（existT 见证件 inherent magic 风险），由          *)
(*   Print Assumptions 承担假设面。                                  *)
Separate Extraction bno_tail_step bno_lt1_int_abs bno_two_step
  bno_z1_step_eq bno_z1_minus_eq.

Print Assumptions bno_pos_d_nat.
Print Assumptions bno_qfact_int.
Print Assumptions bno_qfact_scale_d.
Print Assumptions bno_scale_q_int.
Print Assumptions bno_tail_step.
Print Assumptions bno_lt1_int_abs.
Print Assumptions bno_z1_step_eq.
Print Assumptions bno_z1_minus_eq.
Print Assumptions bno_two_step.
Print Assumptions bno_sum_inv_fact_escape_close.
