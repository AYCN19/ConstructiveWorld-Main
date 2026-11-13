(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。 *)
(* ============================================================ *)
(* ============================================================ *)
(* 评审003 路径 B：把 0<e^x 推广到 Banach 代数层。             *)
(* 分层交付：S1 = Class BanachAlg（Set 层最小面）；             *)
(*           S2 = exp 级数部分和 Fixpoint + 尾界 + 柯西性；     *)
(*           S3 = 交换 exp_add：留记（依赖闭包见文件尾+交付报告）*)
(*                                                             *)
(* 红线自审（文档 B.3.1 草图 req : A -> A -> Prop 系 Prop 泄露，*)
(* 禁照抄）：本文件语句面全 Set 层——                           *)
(*   等词   req:A->A->Prop  ->  bae : BA -> BA -> Set          *)
(*         （库 real_eq/Id 风格：bae_refl/sym/trans 字段化）；  *)
(*   合取   And            ->  And := A*B（本环境 Set 承载，    *)
(*         S03 exp_series_arch L1095 同款先例）；               *)
(*   存在   ex             ->  sigT（S02 cauchy_complete 同构）；*)
(*   序比较 Qle (Prop)     ->  QleT'（= Id (Qle_bool x y) true，*)
(*         库内 QleT 比较面的 Qle_bool 反映形；S02 L64-93 在案：*)
(*         Qle_to_QleT'/QleT'_to_Qle 齐备，为库内正选比较面）。 *)
(* 证内 Prop 层 Qle/Qlt 仅作引擎内衬，不落语句面。             *)
(* 工程注：Rocq 9 类投影实例参为隐式（Check 投影形如            *)
(*   "BA : Set where ?Foo : |- Foo"），类字段/字段引理一律      *)
(*   @显式喂实例（经验卡「先槽后证」同款），自定 Fixpoint/      *)
(*   Lemma 为常规显式参不加 @。                                 *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1：Class BanachAlg —— Banach 代数 Set 层接口最小面          *)
(*   bpow/bnorm/bae/bcoef/bcauchy/blim 均为库内首用名。）       *)
(* ============================================================ *)

Class BanachAlg := {
  BA : Set;                                (* 载体 *)

  bae : BA -> BA -> Set;                   (* Set 层等词（库 Id 风格） *)
  bae_refl   : forall a : BA, bae a a;
  bae_sym    : forall a b : BA, bae a b -> bae b a;
  bae_trans  : forall a b c : BA, bae a b -> bae b c -> bae a c;

  bzero : BA;                              (* 零 *)
  bone : BA;                               (* 单位 *)
  bplus : BA -> BA -> BA;                  (* 加 *)
  bmult : BA -> BA -> BA;                  (* 乘（不交换） *)
  bopp : BA -> BA;                         (* 加法逆 *)

  bcoef : Q -> BA;                         (* Q 标量嵌入（级数系数 1/k! 载体） *)
  bnorm : BA -> Q;                         (* Q 值范数 *)

  (* ---- 加法交换群（bae 等词面）---- *)
  bplus_assoc : forall a b c : BA,
    bae (bplus a (bplus b c)) (bplus (bplus a b) c);
  bplus_comm  : forall a b : BA, bae (bplus a b) (bplus b a);
  bplus_zero  : forall a : BA, bae (bplus a bzero) a;
  bplus_opp   : forall a : BA, bae (bplus a (bopp a)) bzero;

  (* ---- 乘法幺半群 + 双分配（非交换关键面）---- *)
  bmult_assoc : forall a b c : BA,
    bae (bmult a (bmult b c)) (bmult (bmult a b) c);
  bmult_one_l : forall a : BA, bae (bmult bone a) a;
  bmult_one_r : forall a : BA, bae (bmult a bone) a;
  bdistrib_l  : forall a b c : BA,
    bae (bmult a (bplus b c)) (bplus (bmult a b) (bmult a c));
  bdistrib_r  : forall a b c : BA,
    bae (bmult (bplus a b) c) (bplus (bmult a c) (bmult b c));
  bmult_zero  : forall a : BA, bae (bmult a bzero) bzero;

  (* ---- 等词与运算相容 ---- *)
  bplus_wd : forall a b c d : BA,
    bae a c -> bae b d -> bae (bplus a b) (bplus c d);
  bmult_wd : forall a b c d : BA,
    bae a c -> bae b d -> bae (bmult a b) (bmult c d);
  bopp_wd  : forall a b : BA, bae a b -> bae (bopp a) (bopp b);
  bnorm_wd : forall a b : BA, bae a b -> QeqT (bnorm a) (bnorm b);

  (* ---- Q 标量嵌入律 ---- *)
  bcoef_zero : bae (bcoef 0%Q) bzero;
  bcoef_one  : bae (bcoef 1%Q) bone;
  bcoef_mult : forall q r : Q, bae (bcoef (q * r)%Q) (bmult (bcoef q) (bcoef r));
  bcoef_comm : forall (q : Q) (a : BA), bae (bmult a (bcoef q)) (bmult (bcoef q) a);

  bcoef_plus : forall q r : Q, bae (bplus (bcoef q) (bcoef r)) (bcoef (q + r)%Q);
  bcoef_wd   : forall q r : Q, q == r -> bae (bcoef q) (bcoef r);

  (* ---- 范数律（QleT' 比较面）---- *)
  bnorm_zero : Id (bnorm bzero) 0%Q;
  bnorm_one  : Id (bnorm bone) 1%Q;
  bnorm_opp  : forall a : BA, Id (bnorm (bopp a)) (bnorm a);
  bnorm_pos  : forall a : BA, QleT' 0 (bnorm a);
  bnorm_plus : forall a b : BA,
    QleT' (bnorm (bplus a b)) (bnorm a + bnorm b)%Q;             (* 次可加 *)
  bnorm_mult : forall a b : BA,
    QleT' (bnorm (bmult a b)) (bnorm a * bnorm b)%Q;             (* 次可乘 *)
  bnorm_coef : forall q : Q, QeqT (bnorm (bcoef q)) (Qabs q);

  (* ---- 完备性字段（显式柯西/极限接口位，S02 cauchy 同构内联）---- *)
  bcauchy_complete :
    forall (u : nat -> BA),
      (forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n ->
          QltT (bnorm (bplus (u m) (bopp (u n)))) eps)) ->
      sigT (fun l : BA => forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall n : nat,
          NatLe N n -> QltT (bnorm (bplus (u n) (bopp l))) eps));
}.

(* 下游 Id 改写位点改走布尔观察者同余三件（迁移包 §2.4 配方）。 *)

Lemma qeqT_sym_hw : forall x y : Q, QeqT x y -> QeqT y x.
Proof. intros x y H. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. exact H. Qed.

Lemma QeqT_Qlt_bool_cong : forall x y k : Q, QeqT x y -> QltT x k -> QltT y k.
Proof.
  intros x y k Hxy Hx.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans y x k).
  - apply qeq_le. apply Qeq_sym. apply qeqT_imp_qeq. exact Hxy.
  - apply QltT_to_Qlt. exact Hx.
Qed.

Lemma QeqT_Qle_bool_cong : forall x y k : Q, QeqT x y -> QleT' x k -> QleT' y k.
Proof.
  intros x y k Hxy Hx.
  apply Qle_to_QleT'.
  apply (Qle_trans y x k).
  - apply qeq_le. apply Qeq_sym. apply qeqT_imp_qeq. exact Hxy.
  - apply QleT'_to_Qle. exact Hx.
Qed.

(* 运移形反写伴 ride：QeqT 对称侧（NormConv 反写位点用） *)
Lemma QeqT_Qle_bool_cong_r : forall x y k : Q, QeqT x y -> QleT' k x -> QleT' k y.
Proof.
  intros x y k Hxy Hx.
  apply Qle_to_QleT'.
  apply (Qle_trans k x y).
  - apply QleT'_to_Qle. exact Hx.
  - apply qeq_le. apply qeqT_imp_qeq. exact Hxy.
Qed.

(* Qeq 改写桥（Qle/Qeq 面位点：stdlib Qle 已注册 Qeq 同伦实例，一线转换） *)
Lemma bnorm_wd_qeq : forall (B : BanachAlg) (a b : (@BA B)),
  bae a b -> @bnorm B a == @bnorm B b.
Proof. intros B a b H. apply qeqT_imp_qeq. apply (@bnorm_wd B a b H). Qed.

(* Qeq 目标面位点专用桥（Qle/Qeq 改写族同关系面直改，免同余件；适配层配方具象件） *)
Lemma bnorm_coef_qeq : forall (B : BanachAlg) (q : Q),
  @bnorm B (@bcoef B q) == Qabs q.
Proof. intros B q. apply qeqT_imp_qeq. apply (@bnorm_coef B q). Qed.

(* 柯西 / 极限的具名形态（与 bcauchy_complete 内联体逐字同构） *)
Definition bcauchy (B : BanachAlg) (u : nat -> (@BA B)) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (@bnorm B (@bplus B (u m) (@bopp B (u n)))) eps).

Definition blim (B : BanachAlg) (u : nat -> (@BA B)) (l : (@BA B)) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat,
      NatLe N n -> QltT (@bnorm B (@bplus B (u n) (@bopp B l))) eps).

(* 完备性字段 → 具名形态（定义性同构，exact 直连） *)
Lemma bcauchy_complete_sig : forall (B : BanachAlg) (u : nat -> (@BA B)),
  bcauchy B u -> sigT (fun l : (@BA B) => blim B u l).
Proof.
  intros B u Hu. exact (@bcauchy_complete B u Hu).
Qed.

(* ============================================================ *)
(* Set 层等词代数：加法群引理（bae 直构，无经典公理）           *)
(* ============================================================ *)

Lemma bplus_wd_l : forall (B : BanachAlg) (a b c : (@BA B)),
  @bae B a b -> @bae B (@bplus B a c) (@bplus B b c).
Proof.
  intros B a b c H. exact (@bplus_wd B a c b c H (@bae_refl B c)).
Qed.

Lemma bplus_wd_r : forall (B : BanachAlg) (a b c : (@BA B)),
  @bae B a b -> @bae B (@bplus B c a) (@bplus B c b).
Proof.
  intros B a b c H. exact (@bplus_wd B c a c b (@bae_refl B c) H).
Qed.

Lemma bplus_zero_l : forall (B : BanachAlg) (a : (@BA B)),
  @bae B (@bplus B (@bzero B) a) a.
Proof.
  intros B a.
  exact (@bae_trans B _ _ _ (@bplus_comm B (@bzero B) a) (@bplus_zero B a)).
Qed.

Lemma bopp_unique : forall (B : BanachAlg) (z w : (@BA B)),
  @bae B (@bplus B z w) (@bzero B) -> @bae B z (@bopp B w).
Proof.
  intros B z w H.
  (* z = z+0 = z+(w+(-w)) = (z+w)+(-w) = 0+(-w) = (-w)+0 = -w *)
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_zero B z)). }
  eapply bae_trans.
  { exact (@bplus_wd_r B (@bzero B) (@bplus B w (@bopp B w)) z
             (@bae_sym B _ _ (@bplus_opp B w))). }
  eapply bae_trans.
  { exact (@bplus_assoc B z w (@bopp B w)). }
  eapply bae_trans.
  { exact (@bplus_wd_l B (@bplus B z w) (@bzero B) (@bopp B w) H). }
  eapply bae_trans.
  { exact (@bplus_comm B (@bzero B) (@bopp B w)). }
  exact (@bplus_zero B (@bopp B w)).
Qed.

Lemma bplus_middle_swap : forall (B : BanachAlg) (a b c : (@BA B)),
  @bae B (@bplus B (@bplus B a b) c) (@bplus B (@bplus B a c) b).
Proof.
  intros B a b c.
  (* (a+b)+c = a+(b+c) = a+(c+b) = (a+c)+b *)
  eapply bae_trans.
  { exact (@bae_sym B _ _ (@bplus_assoc B a b c)). }
  eapply bae_trans.
  { exact (@bplus_wd_r B (@bplus B b c) (@bplus B c b) a (@bplus_comm B b c)). }
  exact (@bplus_assoc B a c b).
Qed.

(* 加法逆元换位：(-a)+b = -(a+(-b))（exp_series_cauchy 对称化用） *)
Lemma bplus_opp_swap : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bplus B (@bopp B a) b) (@bopp B (@bplus B a (@bopp B b))).
Proof.
  intros B a b.
  apply (@bopp_unique B (@bplus B (@bopp B a) b) (@bplus B a (@bopp B b))).
  (* (-a+b)+(a+(-b)) = 0，六步重结合 *)
  eapply bae_trans.
  { (* = (-a) + (b + (a+(-b))) *)
    exact (@bae_sym B _ _
             (@bplus_assoc B (@bopp B a) b (@bplus B a (@bopp B b)))). }
  eapply bae_trans.
  { (* = (-a) + ((b+a) + (-b)) *)
    exact (@bplus_wd_r B (@bplus B b (@bplus B a (@bopp B b)))
                         (@bplus B (@bplus B b a) (@bopp B b))
                         (@bopp B a) (@bplus_assoc B b a (@bopp B b))). }
  eapply bae_trans.
  { (* = (-a) + ((a+b) + (-b)) *)
    exact (@bplus_wd_r B (@bplus B (@bplus B b a) (@bopp B b))
                         (@bplus B (@bplus B a b) (@bopp B b))
                         (@bopp B a)
                         (@bplus_wd_l B (@bplus B b a) (@bplus B a b) (@bopp B b) (@bplus_comm B b a))). }
  eapply bae_trans.
  { (* = ((-a) + (a+b)) + (-b) *)
    exact (@bplus_assoc B (@bopp B a) (@bplus B a b) (@bopp B b)). }
  eapply bae_trans.
  { (* = (((-a)+a)+b) + (-b) *)
    exact (@bplus_wd_l B (@bplus B (@bopp B a) (@bplus B a b))
                         (@bplus B (@bplus B (@bopp B a) a) b)
                         (@bopp B b) (@bplus_assoc B (@bopp B a) a b)). }
  (* = (0+b)+(-b) = b+(-b) = 0 *)
  exact (@bae_trans B _ _ _
           (@bplus_wd_l B (@bplus B (@bplus B (@bopp B a) a) b)
                          (@bplus B (@bzero B) b)
                          (@bopp B b)
                          (@bplus_wd_l B (@bplus B (@bopp B a) a)
                                         (@bzero B) b
                                         (@bae_trans B _ _ _
                                            (@bplus_comm B (@bopp B a) a)
                                            (@bplus_opp B a))))
           (@bae_trans B _ _ _
              (@bplus_wd_l B (@bplus B (@bzero B) b) b (@bopp B b)
                             (bplus_zero_l B b))
              (@bplus_opp B b))).
Qed.

(* ============================================================ *)
(* S2：exp 级数部分和、尾界、柯西性                             *)
(* （Q 层引擎复用 S03：q_pow/q_fact/exp_tail_abs/q_arch_geom/    *)
(*   arch_decay/exp_tail_arch/exp_tail_abs_geom2/               *)
(*   exp_tail_abs_le_m/q_fact_pos；骨架同                       *)
(*   exp_partial_cauchy_bounded L1054。）                       *)
(* ============================================================ *)

Fixpoint bpow (B : BanachAlg) (a : (@BA B)) (n : nat) : (@BA B) :=
  match n with
  | 0%nat => @bone B
  | Datatypes.S m => @bmult B (bpow B a m) a
  end.

Fixpoint exp_series_partial (B : BanachAlg) (a : (@BA B)) (n : nat) : (@BA B) :=
  match n with
  | 0%nat => @bone B
  | Datatypes.S m =>
      @bplus B (exp_series_partial B a m)
        (@bmult B (bpow B a (Datatypes.S m))
                  (@bcoef B (/ q_fact (Datatypes.S m))))
  end.

(* 幂的范数界：‖a^k‖ ≤T ‖a‖^k（次可乘迭代） *)
Lemma bnorm_bpow : forall (B : BanachAlg) (a : (@BA B)) (k : nat),
  QleT' (@bnorm B (bpow B a k)) (q_pow (@bnorm B a) k).
Proof.
  intros B a k. induction k as [| m IH].
  - change (bpow B a 0%nat) with (@bone B).
    rewrite (@bnorm_one B). apply qleT'_refl.
  - change (bpow B a (Datatypes.S m)) with (@bmult B (bpow B a m) a).
    change (q_pow (@bnorm B a) (Datatypes.S m))
      with ((@bnorm B a) * q_pow (@bnorm B a) m)%Q.
    eapply qleT'_trans.
    + exact (@bnorm_mult B (bpow B a m) a).
    + apply Qle_to_QleT'.
      apply (Qle_trans _ ((q_pow (@bnorm B a) m) * (@bnorm B a))%Q).
      * apply (Qmult_le_compat_r (@bnorm B (bpow B a m))
                                 (q_pow (@bnorm B a) m) (@bnorm B a)).
        -- apply QleT'_to_Qle. exact IH.
        -- apply QleT'_to_Qle. apply (@bnorm_pos B a).
      * apply qeq_le. ring.
Qed.

(* 级数项范数界：‖a^{S k}·(1/(S k)!)‖ ≤T ‖a‖^{S k}/(S k)! *)
Lemma bnorm_esp_term : forall (B : BanachAlg) (a : (@BA B)) (k : nat),
  QleT' (@bnorm B (@bmult B (bpow B a (Datatypes.S k))
                            (@bcoef B (/ q_fact (Datatypes.S k)))))
        (q_pow (@bnorm B a) (Datatypes.S k) / q_fact (Datatypes.S k)).
Proof.
  intros B a k.
  apply (qleT'_trans _ _ _
    (@bnorm_mult B (bpow B a (Datatypes.S k))
                   (@bcoef B (/ q_fact (Datatypes.S k))))).
  apply Qle_to_QleT'.
  apply (Qle_trans _
    ((q_pow (@bnorm B a) (Datatypes.S k))
       * (@bnorm B (@bcoef B (/ q_fact (Datatypes.S k)))))%Q).
  - apply (Qmult_le_compat_r (@bnorm B (bpow B a (Datatypes.S k)))
                             (q_pow (@bnorm B a) (Datatypes.S k))
                             (@bnorm B (@bcoef B (/ q_fact (Datatypes.S k))))).
    + apply QleT'_to_Qle. apply (bnorm_bpow B a (Datatypes.S k)).
    + apply QleT'_to_Qle. apply (@bnorm_pos B (@bcoef B (/ q_fact (Datatypes.S k)))).
  - apply qeq_le.
    rewrite (@bnorm_coef_qeq B (/ q_fact (Datatypes.S k))).
    assert (Hq : 0 <= / q_fact (Datatypes.S k))
      by (apply Qlt_le_weak; apply Qinv_lt_0_compat; apply q_fact_pos).
    rewrite (Qabs_pos (/ q_fact (Datatypes.S k)) Hq).
    reflexivity.
Qed.

(* 尾界主引理：m ≤ n ⟹ ‖esp n − esp m‖ ≤T Σ_{k=m+1..n} ‖a‖^k/k! *)
Lemma esp_diff_le_tail : forall (B : BanachAlg) (a : (@BA B)) (m n : nat),
  (m <= n)%nat ->
  QleT' (@bnorm B (@bplus B (exp_series_partial B a n)
                            (@bopp B (exp_series_partial B a m))))
        (exp_tail_abs m n (@bnorm B a)).
Proof.
  intros B a m n Hm. revert m Hm.
  induction n as [| n' IH]; intros m Hm.
  - (* n = 0：m = 0，差为零 *)
    assert (Hm0 : m = 0%nat) by lia. subst m.
    pose proof (@bnorm_wd B _ _ (@bplus_opp B (exp_series_partial B a 0))) as Hwd0.
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ Hwd0)).
    apply Qle_to_QleT'.
    rewrite (@bnorm_zero B).
    apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n')) as [Heq | Hne].
    + (* m = S n'：差为零，尾和 exp_tail_abs m m == 0 *)
      subst m.
      pose proof (@bnorm_wd B _ _
        (@bplus_opp B (exp_series_partial B a (Datatypes.S n')))) as HwdS.
      eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ HwdS)).
      apply Qle_to_QleT'.
      rewrite (@bnorm_zero B).
      rewrite (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n')
                 (@bnorm B a) (Nat.le_refl _)).
      apply Qle_refl.
    + (* m ≤ n'：S n' 项拆出，中项换位后三角不等式 *)
      assert (Hmn' : (m <= n')%nat) by lia.
      assert (Hleb : Nat.leb m n' = true) by (apply Nat.leb_le; exact Hmn').
      change (exp_series_partial B a (Datatypes.S n'))
        with (@bplus B (exp_series_partial B a n')
                (@bmult B (bpow B a (Datatypes.S n'))
                          (@bcoef B (/ q_fact (Datatypes.S n'))))).
      pose proof (@bnorm_wd B _ _
        (bplus_middle_swap B (exp_series_partial B a n')
            (@bmult B (bpow B a (Datatypes.S n'))
                      (@bcoef B (/ q_fact (Datatypes.S n'))))
            (@bopp B (exp_series_partial B a m)))) as HwdM.
      eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ HwdM)).
      eapply qleT'_trans.
      * (* 三角：‖(esp n' − esp m) + term‖ ≤ ‖esp n' − esp m‖ + ‖term‖ *)
        exact (@bnorm_plus B
                 (@bplus B (exp_series_partial B a n')
                          (@bopp B (exp_series_partial B a m)))
                 (@bmult B (bpow B a (Datatypes.S n'))
                            (@bcoef B (/ q_fact (Datatypes.S n'))))).
      * (* 两界相加；右端定义性展开 + leb true 后逐项对应 *)
        change (exp_tail_abs m (Datatypes.S n') (@bnorm B a))
          with ((exp_tail_abs m n' (@bnorm B a))
                + (if Nat.leb m n'
                   then q_pow (@bnorm B a) (Datatypes.S n') / q_fact (Datatypes.S n')
                   else 0)%Q).
        rewrite Hleb.
        apply (qleT'_plus_compat _ _ _ _).
        -- exact (IH m Hmn').
        -- exact (bnorm_esp_term B a n').
Qed.

(* S2 主定理：exp 级数部分和序列是柯西列（Set 层 bcauchy 形态） *)
Lemma exp_series_cauchy : forall (B : BanachAlg) (a : (@BA B)),
  bcauchy B (fun n => exp_series_partial B a n).
Proof.
  intros B a eps Heps.
  assert (Hr : Qle 0 (@bnorm B a)) by (apply QleT'_to_Qle; apply (@bnorm_pos B a)).
  destruct (q_arch_geom (@bnorm B a)) as [N0 HN0].
  assert (Harch : forall u : nat, (N0 <= u)%nat ->
            Qle (Qmult (1 + 1)%Q (@bnorm B a)) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (HC : Qle 0 ((q_pow (@bnorm B a) N0 / q_fact N0) * (1 + 1)%Q))
    by (apply q_pow_fact2_nonneg; exact Hr).
  destruct (arch_decay ((q_pow (@bnorm B a) N0 / q_fact N0) * (1 + 1)%Q) eps
             (Qle_to_QleT' _ _ HC) Heps) as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  assert (HNm : (N0 <= m)%nat) by lia.
  assert (HNn : (N0 <= n)%nat) by lia.
  destruct (Nat.leb m n) eqn:Emn.
  - (* m ≤ n：对称化 ‖esp m − esp n‖ = ‖esp n − esp m‖
       （bplus_comm + bplus_opp_swap + bnorm_opp，全 Id/bae 面） *)
    apply Nat.leb_le in Emn.
    pose proof (@bnorm_wd B _ _
      (@bplus_comm B (exp_series_partial B a m)
                    (@bopp B (exp_series_partial B a n)))) as HwdC1.
    eapply (QeqT_Qlt_bool_cong _ _ eps (qeqT_sym_hw _ _ HwdC1)).
    pose proof (@bnorm_wd B _ _
      (bplus_opp_swap B (exp_series_partial B a n)
                       (exp_series_partial B a m))) as HwdC2.
    eapply (QeqT_Qlt_bool_cong _ _ eps (qeqT_sym_hw _ _ HwdC2)).
    rewrite (@bnorm_opp B (@bplus B (exp_series_partial B a n)
                                    (@bopp B (exp_series_partial B a m)))).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow (@bnorm B a) m / q_fact m) * (1 + 1)%Q) eps).
    + apply QleT'_to_Qle.
      apply (qleT'_trans _ _ _
        (esp_diff_le_tail B a m n Emn)
        (Qle_to_QleT' _ _
           (exp_tail_abs_geom2 (@bnorm B a) m n Hr
              (fun t Ht => Harch t (Nat.le_trans N0 m t HNm Ht)) Emn))).
    + apply (exp_tail_arch (@bnorm B a) N0 t m eps Hr Harch
               (QltT_to_Qlt 0 eps Heps) (QltT_to_Qlt _ _ Hdec)).
      lia.
  - (* n < m：直接以 n 为底 *)
    apply Nat.leb_gt in Emn.
    assert (Hnm : (n <= m)%nat) by lia.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow (@bnorm B a) n / q_fact n) * (1 + 1)%Q) eps).
    + apply QleT'_to_Qle.
      apply (qleT'_trans _ _ _
        (esp_diff_le_tail B a n m Hnm)
        (Qle_to_QleT' _ _
           (exp_tail_abs_geom2 (@bnorm B a) n m Hr
              (fun t Ht => Harch t (Nat.le_trans N0 n t HNn Ht)) Hnm))).
    + apply (exp_tail_arch (@bnorm B a) N0 t n eps Hr Harch
               (QltT_to_Qlt 0 eps Heps) (QltT_to_Qlt _ _ Hdec)).
      lia.
Qed.

(* ============================================================ *)
(* S3 留记（对称登记，不落承认件）：                           *)
(*   exp_add（交换情形 e^{a+b}=e^a·e^b）与 exp 可逆性           *)
(*   (e^a)^{-1}=e^{-a} 依赖闭包：                               *)
(*   ① S2 尾界（本件 esp_diff_le_tail + exp_series_cauchy 已交） *)
(*   ② 极限定义 exp a := 极限(esp n a)，经 bcauchy_complete_sig  *)
(*      取 l（Banach 层完备性字段位已给）                       *)
(*   ③ 交换前提 a·b=b·a 下 (a+b)^n 的二项式逐项恒等（非交换化   *)
(*      是唯一缺口：comm 下逐项冒泡 = Set 层等词重排引擎，       *)
(*      bplus_middle_swap/bplus_opp_swap 同族放大）；           *)
(*      极限乘法连续性 + ‖·‖ 次可乘界收尾                       *)
(*   ④ C* 层正性/Löwner：构造性谱定理=已知开放难题，禁攻，      *)
(*      对称留记（评审003 判定原文）。                          *)
(* ============================================================ *)
