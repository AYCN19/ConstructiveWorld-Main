(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* UpReqBanachAdd.v —— BA：路径 B bpow_add （） *)
(* ============================================================ *)
(* 任务（S3 装配前置主件，B3Sv2 报告点名"约一件中型件工期"）：    *)
(*   bpow_add：ab=ba 时 bpow (a+b) n == Σ_{k≤n} C(n,k)·a^k·b^(n−k) *)
(*   （二项式恒等，Pascal 归纳）。与已绿的柯西方块恒等            *)
(*   esp_prod_square 分工：本件管 (a+b)^n，方块管 e^a·e^b。       *)
(*                                                               *)
(* 分层：                                                        *)
(*   S1 bpa_binom：Pascal 递归 Fixpoint（Q 值，S-形匹配免        *)
(*      Nat.sub 截断；边界 k=0/n 由 match 分支+out/diag 件守卫）  *)
(*      + Pascal 单点（定义形）+ 出界为零 + 对角为一。            *)
(*   S2 bpa_bpow_add：主件（Pascal 归纳，使用 bpow_comm_r 清项   *)
(*      链 + bsum rot/加法 AC 引擎）。                            *)
(*   S3 bpa_esp_term_binom/bpa_esp_binom：esp 的二项式展开形。    *)
(*                                                               *)
(* 依赖复用（Require，禁重定义）：UpReqBanachExp（BanachAlg/bpow） *)
(*   + UpReqBanachProd（bsum 引擎/清项链，只读冻结）。            *)
(*                                                               *)
(* 接口缺口（如实遗留，非承认件）：冻结类 BanachAlg 只有          *)
(*   bcoef_mult/comm/zero/one，无「Q 加法同调入 bcoef」字段——    *)
(*   Pascal 配对合并（c1+c2 系数合并进标量载体）数学上必需此面。  *)
(*   故主件带两个显式假设（hplus: bcoef 加法同调；               *)
(*   hwd: Qeq 同调入 bcoef），与 UpReqBanachExpDef/Basic          *)
(*   「类缺字段即显式假设+遗留」先例同款。上游扩类后假设即消。    *)
(*                                                               *)
(* 红线自审：语句面全 Set 层（bae 承载等词；Q 层 Qeq 仅假设面），  *)
(*   证内无经典逻辑；无承认件。                                   *)
(* 工程注（沿 B3Sv2 七坑卡）：bae 无 rewrite 实例——一律 change    *)
(*   （定义形）+ bae_trans 显式中件链（中件在 y 槽第 3 显式参）；  *)
(*   bmult_wd 源对 (a,b) 在前、目标对 (c,d) 在后；类投影 @显式。  *)
(*   主链分段 assert（L1..L13）+ 末尾 @bae_trans 项式嵌套组链。   *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S1：二项式系数 bpa_binom（Pascal 递归，Q 值）                  *)
(*                                                               *)
(* 设计注：取 Pascal 递归形而非阶乘比——(i) Pascal 配对点成为定义  *)
(*   形（iota 可达，免除法/通分/非零链）；(ii) S-形匹配免          *)
(*   Nat.sub 截断（边界 k=0 由 match 分支守卫，k>n 出界由 out 件  *)
(*   守卫）。配对序（k' 项在前）对齐主件卷积配对：                *)
(*   C(n',i)+C(n',S i) 恰为 C(S n',S i) 的定义形。                *)
(* ============================================================ *)

Fixpoint bpa_binom (n k : nat) {struct n} : Q :=
  match n with
  | 0%nat =>
      match k with
      | 0%nat => 1%Q
      | Datatypes.S _ => 0%Q
      end
  | Datatypes.S n' =>
      match k with
      | 0%nat => 1%Q
      | Datatypes.S k' => (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q
      end
  end.

(* Pascal 单点（S-形，定义形：reflexivity 级） *)
Lemma bpa_binom_pascal : forall n k : nat,
  bpa_binom (Datatypes.S n) (Datatypes.S k)
    = (bpa_binom n k + bpa_binom n (Datatypes.S k))%Q.
Proof. intros n k. reflexivity. Qed.

(* 左边界：C(n,0) = 1（Leibniz） *)
Lemma bpa_binom_0 : forall n : nat, bpa_binom n 0%nat = 1%Q.
Proof. intros n. destruct n as [| n']; reflexivity. Qed.

(* 出界：k>n 时为零（Qeq，对 n 归纳；0+0 经 Qplus 引擎闭合） *)
Lemma bpa_binom_out : forall n k : nat, (n < k)%nat -> bpa_binom n k == 0%Q.
Proof.
  intros n. induction n as [| n' IH]; intros k Hk.
  - destruct k as [| k']; [ lia | ].
    apply Qeq_refl.
  - destruct k as [| k']; [ lia | ].
    change (bpa_binom (Datatypes.S n') (Datatypes.S k'))
      with (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q.
    setoid_rewrite (IH k' ltac:(lia)).
    setoid_rewrite (IH (Datatypes.S k') ltac:(lia)).
    apply Qplus_0_l.
Qed.

(* 对角：C(n,n) = 1（Qeq，配 out 件 + Qplus_0_r） *)
Lemma bpa_binom_diag : forall n : nat, bpa_binom n n == 1%Q.
Proof.
  intros n. induction n as [| n' IH].
  - apply Qeq_refl.
  - change (bpa_binom (Datatypes.S n') (Datatypes.S n'))
      with (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q.
    setoid_rewrite IH.
    setoid_rewrite (bpa_binom_out n' (Datatypes.S n') (Nat.lt_succ_diag_r n')).
    apply Qplus_0_r.
Qed.

(* 使命字面 Pascal 形（Nat.sub 形；边界守卫 1≤k≤n 防 sub 截断。
   项序按本件 Fixpoint 配对序：(k−1) 项在前，与 S-形定义形同序——
   Q 层 Qplus 非交换于 Leibniz 面，序不可对调，特此注明。） *)
Lemma bpa_binom_pascal_sub : forall n k : nat, (1 <= k)%nat -> (k <= n)%nat ->
  bpa_binom n k
    = (bpa_binom (Nat.sub n 1) (Nat.sub k 1)
       + bpa_binom (Nat.sub n 1) k)%Q.
Proof.
  intros n k Hk1 Hkn.
  destruct n as [| n']; [ lia | ].
  destruct k as [| k']; [ lia | ].
  assert (E1 : (Datatypes.S n' - 1)%nat = n') by lia.
  assert (E2 : (Datatypes.S k' - 1)%nat = k') by lia.
  rewrite E1, E2.
  reflexivity.
Qed.

(* ============================================================ *)
(* S2 前备：bae 面标量引擎与逐项清形件                            *)
(* ============================================================ *)

(* 左零消去：bzero·x == bzero（类只有 bmult_zero 右零；经
   u == u+u（bzero == bzero+bzero + bdistrib_r）与 bopp 消去导出） *)
Lemma bpa_bmult_zero_l : forall (B : BanachAlg) (x : (@BA B)),
  @bae B (@bmult B (@bzero B) x) (@bzero B).
Proof.
  intros B x.
  assert (Ha : @bae B (@bmult B (@bzero B) x)
                      (@bplus B (@bmult B (@bzero B) x)
                                (@bmult B (@bzero B) x))).
  { eapply bae_trans.
    - apply (@bmult_wd B (@bzero B) x
               (@bplus B (@bzero B) (@bzero B)) x).
      + apply (@bae_sym B). exact (@bplus_zero B (@bzero B)).
      + apply (@bae_refl B).
    - exact (@bdistrib_r B (@bzero B) (@bzero B) x). }
  apply (@bae_sym B).
  eapply bae_trans.
  - apply (@bae_sym B). exact (@bplus_opp B (@bmult B (@bzero B) x)).
  - eapply bae_trans.
    + apply (@bplus_wd_l B (@bmult B (@bzero B) x)
               (@bplus B (@bmult B (@bzero B) x)
                          (@bmult B (@bzero B) x))
               (@bopp B (@bmult B (@bzero B) x)) Ha).
    + eapply bae_trans.
      * apply (@bae_sym B).
        exact (@bplus_assoc B (@bmult B (@bzero B) x)
                 (@bmult B (@bzero B) x) (@bopp B (@bmult B (@bzero B) x))).
      * eapply bae_trans.
        -- apply (@bplus_wd_r B). exact (@bplus_opp B (@bmult B (@bzero B) x)).
        -- exact (@bplus_zero B (@bmult B (@bzero B) x)).
Qed.

(* 右乘拉出（bsum_mult_l 对偶）：Σ (f i·x) == (Σ f)·x
   （bdistrib_r 对称向；基例零元经 bpa_bmult_zero_l 左零消） *)
Lemma bpa_bsum_mult_r : forall (B : BanachAlg) (n : nat) (x : (@BA B))
                               (f : nat -> (@BA B)),
  @bae B (bsum B n (fun i : nat => @bmult B (f i) x))
         (@bmult B (bsum B n f) x).
Proof.
  intros B n x f. induction n as [| m IH].
  - apply (@bae_sym B). apply bpa_bmult_zero_l.
  - change (bsum B (Datatypes.S m) (fun i : nat => @bmult B (f i) x))
      with (@bplus B (bsum B m (fun i : nat => @bmult B (f i) x))
                     (@bmult B (f m) x)).
    change (@bmult B (bsum B (Datatypes.S m) f) x)
      with (@bmult B (@bplus B (bsum B m f) (f m)) x).
    eapply bae_trans.
    + apply (@bplus_wd_l B). exact IH.
    + apply (@bae_sym B). exact (@bdistrib_r B (bsum B m f) (f m) x).
Qed.

(* 标量配对合并：bcoef q·T + bcoef r·T == bcoef (q+r)·T
   （使用 hplus：bcoef 加法同调——类缺字段，显式假设面） *)
Lemma bpa_scal_plus : forall (B : BanachAlg) (q r : Q) (T : (@BA B)),
  (forall q r : Q, @bae B (@bplus B (@bcoef B q) (@bcoef B r))
                           (@bcoef B (q + r)%Q)) ->
  @bae B (@bplus B (@bmult B (@bcoef B q) T) (@bmult B (@bcoef B r) T))
         (@bmult B (@bcoef B (q + r)%Q) T).
Proof.
  intros B q r T H. eapply bae_trans.
  - apply (@bae_sym B).
    exact (@bdistrib_r B (@bcoef B q) (@bcoef B r) T).
  - apply (@bmult_wd B (@bplus B (@bcoef B q) (@bcoef B r)) T
                       (@bcoef B (q + r)%Q) T).
    + exact (H q r).
    + apply (@bae_refl B).
Qed.

(* a 项清形：(c·(a^k·b^m))·a == c·(a^(S k)·b^m)
   （a 落右侧：(b^m·a) = (a·b^m) 经 bpow_comm_r（b 作底、hab 对称角色）；
     a^k·a = a^(S k) 定义形闭合） *)
Lemma bpa_term_A : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  forall (c : Q) (k m : nat),
    @bae B (@bmult B (@bmult B (@bcoef B c)
                                (@bmult B (bpow B a k) (bpow B b m))) a)
           (@bmult B (@bcoef B c)
                     (@bmult B (bpow B a (Datatypes.S k)) (bpow B b m))).
Proof.
  intros B a b hab c k m. eapply bae_trans.
  - apply (@bae_sym B).
    exact (@bmult_assoc B (@bcoef B c)
              (@bmult B (bpow B a k) (bpow B b m)) a).
  - eapply bae_trans.
    + apply (@bmult_wd B (@bcoef B c)
               (@bmult B (@bmult B (bpow B a k) (bpow B b m)) a)
               (@bcoef B c)
               (@bmult B (bpow B a k)
                          (@bmult B (bpow B b m) a))).
      * apply (@bae_refl B).
      * apply (@bae_sym B).
        exact (@bmult_assoc B (bpow B a k) (bpow B b m) a).
    + eapply bae_trans.
      * apply (@bmult_wd B (@bcoef B c)
                 (@bmult B (bpow B a k) (@bmult B (bpow B b m) a))
                 (@bcoef B c)
                 (@bmult B (bpow B a k) (@bmult B a (bpow B b m)))).
        -- apply (@bae_refl B).
        -- apply (@bmult_wd B (bpow B a k) (@bmult B (bpow B b m) a)
                    (bpow B a k) (@bmult B a (bpow B b m))).
           ++ apply (@bae_refl B).
           ++ exact (bpow_comm_r B b a
                       (@bae_sym B (@bmult B a b) (@bmult B b a) hab) m).
      * eapply bae_trans.
        -- apply (@bmult_wd B (@bcoef B c)
                    (@bmult B (bpow B a k) (@bmult B a (bpow B b m)))
                    (@bcoef B c)
                    (@bmult B (@bmult B (bpow B a k) a) (bpow B b m))).
           ++ apply (@bae_refl B).
           ++ exact (@bmult_assoc B (bpow B a k) a (bpow B b m)).
        -- (* (a^k·a)·b^m ≡ a^(S k)·b^m：bpow 定义形自反闭合 *)
           apply (@bae_refl B).
Qed.

(* b 项清形：(c·(a^k·b^m))·b == c·(a^k·b^(S m))
   （b 落右侧恰与 b^m 直接结合，免交换前提） *)
Lemma bpa_term_B : forall (B : BanachAlg) (a b : (@BA B)) (c : Q) (k m : nat),
  @bae B (@bmult B (@bmult B (@bcoef B c)
                              (@bmult B (bpow B a k) (bpow B b m))) b)
         (@bmult B (@bcoef B c)
                   (@bmult B (bpow B a k)
                            (bpow B b (Datatypes.S m)))).
Proof.
  intros B a b c k m. eapply bae_trans.
  - apply (@bae_sym B).
    exact (@bmult_assoc B (@bcoef B c)
              (@bmult B (bpow B a k) (bpow B b m)) b).
  - eapply bae_trans.
    + apply (@bmult_wd B (@bcoef B c)
               (@bmult B (@bmult B (bpow B a k) (bpow B b m)) b)
               (@bcoef B c)
               (@bmult B (bpow B a k) (@bmult B (bpow B b m) b))).
      * apply (@bae_refl B).
      * apply (@bae_sym B).
        exact (@bmult_assoc B (bpow B a k) (bpow B b m) b).
    + apply (@bmult_wd B (@bcoef B c)
               (@bmult B (bpow B a k) (@bmult B (bpow B b m) b))
               (@bcoef B c)
               (@bmult B (bpow B a k) (bpow B b (Datatypes.S m)))).
      * apply (@bae_refl B).
      * apply (@bae_refl B).
Qed.

(* 配对首项（j=0）：gB 0 == h 0
   C(n',0)=C(S n',0)=1 双侧 Leibniz 换形 + 幂指 S(n'−0)=S n' lia 桥 *)
Lemma bpa_pair_head : forall (B : BanachAlg) (a b : (@BA B)) (n' : nat),
  @bae B (@bmult B (@bcoef B (bpa_binom n' 0%nat))
                   (@bmult B (bpow B a 0%nat)
                            (bpow B b (Datatypes.S (Nat.sub n' 0%nat)))))
         (@bmult B (@bcoef B (bpa_binom (Datatypes.S n') 0%nat))
                   (@bmult B (bpow B a 0%nat)
                            (bpow B b (Nat.sub (Datatypes.S n') 0%nat)))).
Proof.
  intros B a b n'.
  assert (E1 : bpa_binom n' 0%nat = 1%Q) by apply bpa_binom_0.
  assert (E2 : bpa_binom (Datatypes.S n') 0%nat = 1%Q) by reflexivity.
  assert (E3 : (Datatypes.S (Nat.sub n' 0%nat))%nat = Datatypes.S n') by lia.
  rewrite E1, E2, E3.
  change (bpow B b (Nat.sub (Datatypes.S n') 0%nat))
    with (bpow B b (Datatypes.S n')).
  apply (@bae_refl B).
Qed.

(* 配对中段：gA i + gB (S i) == h (S i)（i < n'）
   系数 C(n',i)+C(n',S i) 恰为 C(S n',S i) 定义形（Pascal 递归
   配对序）；b 幂 S(n'−S i)=n'−i（lia 桥）与 S n'−S i（iota）归一 *)
Lemma bpa_pair_mid : forall (B : BanachAlg) (a b : (@BA B)) (n' i : nat),
  (forall q r : Q, @bae B (@bplus B (@bcoef B q) (@bcoef B r))
                           (@bcoef B (q + r)%Q)) ->
  (i < n')%nat ->
  @bae B (@bplus B
            (@bmult B (@bcoef B (bpa_binom n' i))
                      (@bmult B (bpow B a (Datatypes.S i))
                               (bpow B b (Nat.sub n' i))))
            (@bmult B (@bcoef B (bpa_binom n' (Datatypes.S i)))
                      (@bmult B (bpow B a (Datatypes.S i))
                               (bpow B b (Datatypes.S (Nat.sub n' (Datatypes.S i)))))))
         (@bmult B (@bcoef B (bpa_binom (Datatypes.S n') (Datatypes.S i)))
                   (@bmult B (bpow B a (Datatypes.S i))
                            (bpow B b (Nat.sub (Datatypes.S n') (Datatypes.S i))))).
Proof.
  intros B a b n' i hplus Hi.
  assert (E : (Datatypes.S (Nat.sub n' (Datatypes.S i)))%nat = Nat.sub n' i)
    by lia.
  rewrite E.
  change (bpa_binom (Datatypes.S n') (Datatypes.S i))
    with (bpa_binom n' i + bpa_binom n' (Datatypes.S i))%Q.
  change (bpow B b (Nat.sub (Datatypes.S n') (Datatypes.S i)))
    with (bpow B b (Nat.sub n' i)).
  eapply bae_trans.
  - exact (bpa_scal_plus B (bpa_binom n' i) (bpa_binom n' (Datatypes.S i))
             (@bmult B (bpow B a (Datatypes.S i)) (bpow B b (Nat.sub n' i)))
             hplus).
  - apply (@bae_refl B).
Qed.

(* 配对尾项：gA n' == h (S n')
   C(S n',S n') ≡ C(n',n')+C(n',S n') 定义形；C(n',S n')==0（出界）
   经 hwd（Qeq 同调入 bcoef）+ Qplus_0_r 收拢；b 幂双侧 iota 归一 *)
Lemma bpa_pair_tail : forall (B : BanachAlg) (a b : (@BA B)) (n' : nat),
  (forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r)) ->
  @bae B (@bmult B (@bcoef B (bpa_binom n' n'))
                   (@bmult B (bpow B a (Datatypes.S n'))
                            (bpow B b (Nat.sub n' n'))))
         (@bmult B (@bcoef B (bpa_binom (Datatypes.S n') (Datatypes.S n')))
                   (@bmult B (bpow B a (Datatypes.S n'))
                            (bpow B b (Nat.sub (Datatypes.S n')
                                               (Datatypes.S n'))))).
Proof.
  intros B a b n' hwd.
  change (bpa_binom (Datatypes.S n') (Datatypes.S n'))
    with (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q.
  change (bpow B b (Nat.sub (Datatypes.S n') (Datatypes.S n')))
    with (bpow B b (Nat.sub n' n')).
  apply (@bae_sym B).
  apply (@bmult_wd B
           (@bcoef B (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q)
           (@bmult B (bpow B a (Datatypes.S n')) (bpow B b (Nat.sub n' n')))
           (@bcoef B (bpa_binom n' n'))
           (@bmult B (bpow B a (Datatypes.S n')) (bpow B b (Nat.sub n' n')))).
  - apply (hwd (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q
             (bpa_binom n' n')).
    setoid_rewrite (bpa_binom_out n' (Datatypes.S n') (Nat.lt_succ_diag_r n')).
    apply Qplus_0_r.
  - apply (@bae_refl B).
Qed.

(* ============================================================ *)
(* S2 主件：bpow_add 二项式恒等                                   *)
(* ============================================================ *)

Lemma bpa_bpow_add : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  (forall q r : Q, @bae B (@bplus B (@bcoef B q) (@bcoef B r))
                           (@bcoef B (q + r)%Q)) ->
  (forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r)) ->
  forall n : nat,
    @bae B (bpow B (@bplus B a b) n)
           (bsum B (Datatypes.S n)
              (fun k : nat =>
                 @bmult B (@bcoef B (bpa_binom n k))
                          (@bmult B (bpow B a k)
                                   (bpow B b (Nat.sub n k))))).
Proof.
  intros B a b hab hplus hwd n.
  induction n as [| n' IH].
  - (* 基例 n=0：bone == bzero + C(0,0)·(bone·bone) *)
    change (bpow B (@bplus B a b) 0%nat) with (@bone B).
    change (bsum B (Datatypes.S 0%nat)
              (fun k : nat => @bmult B (@bcoef B (bpa_binom 0%nat k))
                                       (@bmult B (bpow B a k)
                                                (bpow B b (Nat.sub 0%nat k)))))
      with (@bplus B (@bzero B)
              (@bmult B (@bcoef B (bpa_binom 0%nat 0%nat))
                       (@bmult B (@bpow B a 0%nat)
                                (@bpow B b (Nat.sub 0%nat 0%nat))))).
    assert (E : bpa_binom 0%nat 0%nat = 1%Q) by reflexivity.
    rewrite E.
    change (@bpow B a 0%nat) with (@bone B).
    change (@bpow B b (Nat.sub 0%nat 0%nat)) with (@bone B).
    assert (HX : @bae B (@bmult B (@bcoef B 1%Q)
                                  (@bmult B (@bone B) (@bone B)))
                        (@bone B)).
    { eapply bae_trans.
      - apply (@bmult_wd B (@bcoef B 1%Q)
                 (@bmult B (@bone B) (@bone B))
                 (@bone B)
                 (@bmult B (@bone B) (@bone B))).
        + exact (@bcoef_one B).
        + apply (@bae_refl B).
      - eapply bae_trans.
        + exact (@bmult_one_l B (@bmult B (@bone B) (@bone B))).
        + exact (@bmult_one_l B (@bone B)). }
    eapply bae_trans.
    + apply (@bae_sym B). exact (@bplus_zero_l B (@bone B)).
    + apply (@bplus_wd_r B).
      apply (@bae_sym B). exact HX.
  - (* 归纳步：Pascal 配对组装（蓝图 判例降层） *)
    set (g := fun k : nat =>
                @bmult B (@bcoef B (bpa_binom n' k))
                         (@bmult B (bpow B a k)
                                  (bpow B b (Nat.sub n' k)))).
    set (gA := fun k : nat =>
                 @bmult B (@bcoef B (bpa_binom n' k))
                          (@bmult B (bpow B a (Datatypes.S k))
                                   (bpow B b (Nat.sub n' k)))).
    set (gB := fun k : nat =>
                 @bmult B (@bcoef B (bpa_binom n' k))
                          (@bmult B (bpow B a k)
                                   (bpow B b (Datatypes.S (Nat.sub n' k))))).
    set (h := fun k : nat =>
                @bmult B (@bcoef B (bpa_binom (Datatypes.S n') k))
                         (@bmult B (bpow B a k)
                                  (bpow B b (Nat.sub (Datatypes.S n') k)))).
    (* ① 幂拆出 + IH 代入 *)
    assert (L1 : @bae B (@bmult B (bpow B (@bplus B a b) n') (@bplus B a b))
                        (@bmult B (bsum B (Datatypes.S n') g)
                                  (@bplus B a b))).
    { exact (@bmult_wd B (bpow B (@bplus B a b) n')
                       (@bplus B a b)
                       (bsum B (Datatypes.S n') g)
                       (@bplus B a b) IH
                       (@bae_refl B (@bplus B a b))). }
    (* ② (a+b) 拉入和内（bsum_mult_l 对称向） *)
    assert (L2 : @bae B (@bmult B (bsum B (Datatypes.S n') g)
                                  (@bplus B a b))
                        (bsum B (Datatypes.S n')
                                  (fun k : nat => @bmult B (g k) (@bplus B a b)))).
    { apply (@bae_sym B).
      exact (bpa_bsum_mult_r B (Datatypes.S n') (@bplus B a b) g). }
    (* ③ 逐项 bdistrib_r 拆 a 项/b 项（ext 直拆双和） *)
    assert (L3 : @bae B (bsum B (Datatypes.S n')
                                  (fun k : nat => @bmult B (g k) (@bplus B a b)))
                        (@bplus B (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) a))
                                  (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) b)))).
    { eapply bae_trans.
      - apply (bsum_ext B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) (@bplus B a b))
                  (fun k : nat =>
                     @bplus B (@bmult B (g k) a) (@bmult B (g k) b))).
        intros k _. apply (@bdistrib_l B (g k) a b).
      - apply (bsum_plus B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) a)
                  (fun k : nat => @bmult B (g k) b)). }
    (* ④ 逐项清形：a 项提幂（bpa_term_A）、b 项清交换（bpa_term_B） *)
    assert (L4 : @bae B (@bplus B (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) a))
                                  (bsum B (Datatypes.S n')
                                            (fun k : nat => @bmult B (g k) b)))
                        (@bplus B (bsum B (Datatypes.S n') gA)
                                  (bsum B (Datatypes.S n') gB))).
    { apply (@bplus_wd B
               (bsum B (Datatypes.S n') (fun k : nat => @bmult B (g k) a))
               (bsum B (Datatypes.S n') (fun k : nat => @bmult B (g k) b))
               (bsum B (Datatypes.S n') gA)
               (bsum B (Datatypes.S n') gB)).
      - apply (bsum_ext B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) a) gA).
        intros k _.
        exact (bpa_term_A B a b hab (bpa_binom n' k) k (Nat.sub n' k)).
      - apply (bsum_ext B (Datatypes.S n')
                  (fun k : nat => @bmult B (g k) b) gB).
        intros k _.
        exact (bpa_term_B B a b (bpa_binom n' k) k (Nat.sub n' k)). }
    (* ⑤ b 和换元（rot 首项提出） *)
    assert (L5 : @bae B (@bplus B (bsum B (Datatypes.S n') gA)
                                  (bsum B (Datatypes.S n') gB))
                        (@bplus B (bsum B (Datatypes.S n') gA)
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bplus_wd_r B). exact (bsum_rot B n' gB). }
    (* ⑥ a 和尾项拆出（bsum 定义形，转换面闭合） *)
    assert (L6 : @bae B (@bplus B (bsum B (Datatypes.S n') gA)
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus B (@bplus B (bsum B n' gA) (gA n'))
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bae_refl B). }
    (* ⑦ 加法 AC 重排：gB 0 提首、gA n' 收尾、两主段并列 *)
    assert (L7 : @bae B (@bplus B (@bplus B (bsum B n' gA) (gA n'))
                                  (@bplus B (gB 0%nat)
                                     (bsum B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus B (@bplus B (gB 0%nat) (bsum B n' gA))
                                  (@bplus B (bsum B n'
                                                (fun i : nat => gB (Datatypes.S i)))
                                            (gA n')))).
    { eapply bae_trans.
      - exact (bplus_swap4 B (bsum B n' gA) (gA n') (gB 0%nat)
                   (bsum B n' (fun i : nat => gB (Datatypes.S i)))).
      - apply (@bplus_wd B (@bplus B (bsum B n' gA) (gB 0%nat))
                 (@bplus B (gA n')
                            (bsum B n' (fun i : nat => gB (Datatypes.S i))))
                 (@bplus B (gB 0%nat) (bsum B n' gA))
                 (@bplus B (bsum B n'
                               (fun i : nat => gB (Datatypes.S i)))
                            (gA n'))).
        + exact (@bplus_comm B (bsum B n' gA) (gB 0%nat)).
        + exact (@bplus_comm B (gA n')
                   (bsum B n' (fun i : nat => gB (Datatypes.S i)))). }
    assert (L8 : @bae B (@bplus B (@bplus B (gB 0%nat) (bsum B n' gA))
                                  (@bplus B (bsum B n'
                                                (fun i : nat => gB (Datatypes.S i)))
                                            (gA n')))
                        (@bplus B (gB 0%nat)
                           (@bplus B (@bplus B (bsum B n' gA)
                                                (bsum B n'
                                                   (fun i : nat => gB (Datatypes.S i))))
                                     (gA n')))).
    { eapply bae_trans.
      - apply (@bae_sym B).
        exact (@bplus_assoc B (gB 0%nat) (bsum B n' gA)
                 (@bplus B (bsum B n' (fun i : nat => gB (Datatypes.S i)))
                            (gA n'))).
      - apply (@bplus_wd_r B).
        exact (@bplus_assoc B (bsum B n' gA)
                 (bsum B n' (fun i : nat => gB (Datatypes.S i)))
                 (gA n')). }
    (* ⑧ Pascal 中段并段 + 逐项配对合并 + 首尾对位 *)
    assert (L9 : @bae B (@bplus B (gB 0%nat)
                                  (@bplus B (@bplus B (bsum B n' gA)
                                                       (bsum B n'
                                                          (fun i : nat => gB (Datatypes.S i))))
                                            (gA n')))
                        (@bplus B (gB 0%nat)
                                  (@bplus B (bsum B n'
                                                (fun i : nat =>
                                                   @bplus B (gA i)
                                                     (gB (Datatypes.S i))))
                                            (gA n')))).
    { apply (@bplus_wd_r B
               (@bplus B (@bplus B (bsum B n' gA)
                                  (bsum B n'
                                     (fun i : nat => gB (Datatypes.S i))))
                          (gA n'))
               (@bplus B (bsum B n'
                             (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
                          (gA n'))
               (gB 0%nat)).
      apply (@bplus_wd_l B
               (@bplus B (bsum B n' gA)
                          (bsum B n' (fun i : nat => gB (Datatypes.S i))))
               (bsum B n'
                  (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
               (gA n')).
      apply (@bae_sym B).
      exact (bsum_plus B n' gA (fun i : nat => gB (Datatypes.S i))). }
    assert (L10 : @bae B (@bplus B (gB 0%nat)
                                   (@bplus B (bsum B n'
                                                 (fun i : nat =>
                                                    @bplus B (gA i)
                                                      (gB (Datatypes.S i))))
                                              (gA n')))
                         (@bplus B (gB 0%nat)
                                   (@bplus B (bsum B n'
                                                 (fun i : nat => h (Datatypes.S i)))
                                              (gA n')))).
    { apply (@bplus_wd_r B
               (@bplus B (bsum B n'
                             (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
                          (gA n'))
               (@bplus B (bsum B n' (fun i : nat => h (Datatypes.S i)))
                          (gA n'))
               (gB 0%nat)).
      apply (@bplus_wd_l B
               (bsum B n'
                  (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i))))
               (bsum B n' (fun i : nat => h (Datatypes.S i)))
               (gA n')).
      apply (bsum_ext B n'
                (fun i : nat => @bplus B (gA i) (gB (Datatypes.S i)))
                (fun i : nat => h (Datatypes.S i))).
      intros i Hi.
      exact (bpa_pair_mid B a b n' i hplus Hi). }
    assert (L11 : @bae B (@bplus B (gB 0%nat)
                                   (@bplus B (bsum B n'
                                                 (fun i : nat => h (Datatypes.S i)))
                                              (gA n')))
                         (@bplus B (@bplus B (gB 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (gA n'))).
    { exact (@bplus_assoc B (gB 0%nat)
               (bsum B n' (fun i : nat => h (Datatypes.S i))) (gA n')). }
    assert (L12 : @bae B (@bplus B (@bplus B (gB 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (gA n'))
                         (@bplus B (@bplus B (h 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (h (Datatypes.S n')))).
    { apply (@bplus_wd B
               (@bplus B (gB 0%nat)
                          (bsum B n' (fun i : nat => h (Datatypes.S i))))
               (gA n')
               (@bplus B (h 0%nat)
                          (bsum B n' (fun i : nat => h (Datatypes.S i))))
               (h (Datatypes.S n'))).
      - apply (@bplus_wd B (gB 0%nat)
                 (bsum B n' (fun i : nat => h (Datatypes.S i)))
                 (h 0%nat)
                 (bsum B n' (fun i : nat => h (Datatypes.S i)))).
        + exact (bpa_pair_head B a b n').
        + apply (@bae_refl B).
      - exact (bpa_pair_tail B a b n' hwd). }
    (* ⑨ 目标和拆形闭合：rot 反向归位（bsum 定义形 change + 转换） *)
    assert (L13 : @bae B (@bplus B (@bplus B (h 0%nat)
                                               (bsum B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (h (Datatypes.S n')))
                         (bsum B (Datatypes.S (Datatypes.S n')) h)).
    { change (bsum B (Datatypes.S (Datatypes.S n')) h)
        with (@bplus B (bsum B (Datatypes.S n') h) (h (Datatypes.S n'))).
      eapply bae_trans.
      - apply (@bplus_wd_l B).
        apply (@bae_sym B). exact (bsum_rot B n' h).
      - apply (@bae_refl B). }
    (* 幂拆出（定义形）+ L1..L13 组链 *)
    change (bpow B (@bplus B a b) (Datatypes.S n'))
      with (@bmult B (bpow B (@bplus B a b) n') (@bplus B a b)).
    exact (@bae_trans B _ _ _ L1
             (@bae_trans B _ _ _ L2
                (@bae_trans B _ _ _ L3
                   (@bae_trans B _ _ _ L4
                      (@bae_trans B _ _ _ L5
                         (@bae_trans B _ _ _ L6
                            (@bae_trans B _ _ _ L7
                               (@bae_trans B _ _ _ L8
                                  (@bae_trans B _ _ _ L9
                                     (@bae_trans B _ _ _ L10
                                        (@bae_trans B _ _ _ L11
                                           (@bae_trans B _ _ _ L12 L13)))))))))))).
Qed.

(* ============================================================ *)
(* S3 加分：esp 的二项式展开形（与 esp_prod_square 对接注记：      *)
(*   本件管 (a+b)^k 单和层；柯西方块管 e^a·e^b 双和层——三角转置    *)
(*   （exp_cauchy_swap 降层，进行中）后方能对接装配 exp_add。）  *)
(* ============================================================ *)

(* 标量重封装：(bcoef c·T)·bcoef s == bcoef (c·s)·T *)
Lemma bpa_scal_repack : forall (B : BanachAlg) (c s : Q) (T : (@BA B)),
  @bae B (@bmult B (@bmult B (@bcoef B c) T) (@bcoef B s))
         (@bmult B (@bcoef B (c * s)%Q) T).
Proof.
  intros B c s T. eapply bae_trans.
  - apply (@bae_sym B).
    exact (@bmult_assoc B (@bcoef B c) T (@bcoef B s)).
  - eapply bae_trans.
    + apply (@bmult_wd B (@bcoef B c)
               (@bmult B T (@bcoef B s)) (@bcoef B c)
               (@bmult B (@bcoef B s) T)).
      * apply (@bae_refl B).
      * exact (@bcoef_comm B s T).
    + eapply bae_trans.
      * exact (@bmult_assoc B (@bcoef B c) (@bcoef B s) T).
      * apply (@bmult_wd B (@bmult B (@bcoef B c) (@bcoef B s)) T
                  (@bcoef B (c * s)%Q) T).
        -- apply (@bae_sym B). exact (@bcoef_mult B c s).
        -- apply (@bae_refl B).
Qed.

(* 项级：bpow (a+b) k·(1/k!) == Σ_{j≤k} (C(k,j)/k!)·a^j·b^(k−j) *)
Lemma bpa_esp_term_binom : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  (forall q r : Q, @bae B (@bplus B (@bcoef B q) (@bcoef B r))
                           (@bcoef B (q + r)%Q)) ->
  (forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r)) ->
  forall k : nat,
    @bae B (@bmult B (bpow B (@bplus B a b) k)
                     (@bcoef B (/ q_fact k)))
           (bsum B (Datatypes.S k)
              (fun j : nat =>
                 @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                          (@bmult B (bpow B a j)
                                   (bpow B b (Nat.sub k j))))).
Proof.
  intros B a b hab hplus hwd k.
  set (F := fun j : nat =>
              @bmult B (@bcoef B (bpa_binom k j))
                       (@bmult B (bpow B a j)
                                (bpow B b (Nat.sub k j)))).
  eapply bae_trans.
  - apply (@bmult_wd B (bpow B (@bplus B a b) k)
                     (@bcoef B (/ q_fact k))
                     (bsum B (Datatypes.S k) F)
                     (@bcoef B (/ q_fact k))).
    + exact (bpa_bpow_add B a b hab hplus hwd k).
    + apply (@bae_refl B).
  - eapply bae_trans.
    + apply (@bae_sym B).
      exact (bsum_scal B (Datatypes.S k) (/ q_fact k) F).
    + apply (bsum_ext B (Datatypes.S k)
                (fun j : nat => @bmult B (F j) (@bcoef B (/ q_fact k)))
                (fun j : nat =>
                   @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                            (@bmult B (bpow B a j)
                                     (bpow B b (Nat.sub k j))))).
      intros j _.
      exact (bpa_scal_repack B (bpa_binom k j) (/ q_fact k)
               (@bmult B (bpow B a j) (bpow B b (Nat.sub k j)))).
Qed.

(* 级数级：esp n (a+b) 的二项式展开形（对接 esp_as_bsum） *)
Lemma bpa_esp_binom : forall (B : BanachAlg) (a b : (@BA B)),
  @bae B (@bmult B a b) (@bmult B b a) ->
  (forall q r : Q, @bae B (@bplus B (@bcoef B q) (@bcoef B r))
                           (@bcoef B (q + r)%Q)) ->
  (forall q r : Q, q == r -> @bae B (@bcoef B q) (@bcoef B r)) ->
  forall n : nat,
    @bae B (exp_series_partial B (@bplus B a b) n)
           (bsum B (Datatypes.S n)
              (fun k : nat =>
                 bsum B (Datatypes.S k)
                   (fun j : nat =>
                      @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                               (@bmult B (bpow B a j)
                                        (bpow B b (Nat.sub k j)))))).
Proof.
  intros B a b hab hplus hwd n.
  eapply bae_trans.
  - exact (esp_as_bsum B (@bplus B a b) n).
  - apply (bsum_ext B (Datatypes.S n)
              (fun k : nat => @bmult B (bpow B (@bplus B a b) k)
                                      (@bcoef B (/ q_fact k)))
              (fun k : nat =>
                 bsum B (Datatypes.S k)
                   (fun j : nat =>
                      @bmult B (@bcoef B (bpa_binom k j * / q_fact k)%Q)
                               (@bmult B (bpow B a j)
                                        (bpow B b (Nat.sub k j)))))).
    intros k _.
    exact (bpa_esp_term_binom B a b hab hplus hwd k).
Qed.

(* ============================================================ *)
(* 遗留登记（对称登记，不落承认件）：                              *)
(*   ① 接口缺口：BanachAlg 类缺 bcoef 加法同调/Qeq 同调字段——     *)
(*     本件以显式假设（hplus/hwd）承载，上游扩类后即消。          *)
(*   ② exp_add 装配：需三角转置 exp_cauchy_swap 降层（进行中）  *)
(*     + 极限乘法连续性；本件 S2 为其 (a+b)^n 层，S3 为其          *)
(*     esp 展开层，。                                   *)
(*   ③ 系数桥：Pascal 递归形 bpa_binom 与阶乘比形                 *)
(*     q_fact n/(q_fact k·q_fact (n−k)) 的等价（供下游 #29 项      *)
(*     分裂 exp_term_split）为对接件，另立。                       *)
(* ============================================================ *)
