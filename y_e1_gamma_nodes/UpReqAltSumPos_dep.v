(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   altsum_ex_dec3（原 L685，1 句玩具证）                                *)
(*   altsum_ex_1（原 L681，1 句玩具证）                                   *)
(*   altsum_ex_3（原 L677，1 句玩具证）                                   *)
(*   altsum_ex_2（原 L673，1 句玩具证）                                   *)
(*   altsum_acc_0_eq（原 L268，2 句玩具证）                               *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqAltSumPos.v *)
(* *)
(* 目的： Q 层有限交错和正性引擎。 *)
(* 主件： altsum_strict_plus_le 与 altsum_qleT'_* 序定律族；altsum 交错和及其符号约定 altsum_sgp。 *)
(* 依赖： S01_BaseRing、S02_CauchyComplete。 *)
(* 备注： 假设面取 Or 形 QleT，并附 QleT 到 QleT' 的换桥（两支均可健全入 QleT'）。 *)
(* ============================================================ *)

(* ============================================================ *)
(*                                                                *)
(* 使命：把「非负递减序列的有限交错和为正（Leibniz 有限形）」做成    *)
(* 独立 Q 层引擎件，供路径 C（Padé [n/n] 误差符号）den_pos 直接使用： *)
(*   den(x) = Σ_{k=0}^{n} (−1)^k c_k x^k，0 ≤ x < 2 时各项          *)
(*   (c_k x^k) 非负递减 ⟹ den(x) ≥ 0。                              *)
(*                                                                *)
(* 【S03 对接判定（实名侦察结论）】S03_QExp.v 的 altf 家族不是通用形： *)
(*   altf_zero (S03:) : forall N, 1 <= N -> altf N == 0 ——      *)
(*   是 (1−1)^N 展开系数==0 的【具体恒等式】（Pascal 归纳），序列项    *)
(*   1/(u!(N−u)!) 无递减条件面、结论是无条件 ==0；vander_4m2/4m4     *)
(*   (S03:4390/4596) 是 corr 家族的 Vandermonde 恒等。均不可承载      *)
(*                                                                *)
(* 【S1 实现选择（二选一之「递归吸收符号」）】符号不由 (−1)^k 显式    *)
(*   判定装配（避开 Z 指数与 Q 显式装配坑），而在递归中经 bool 累加器  *)
(*   sg 逐层 negb 吸收：altacc sg f k n = 从指标 k 起共 n 项、首项    *)
(*   符号为 sg 的交错尾和；altsum f n := altacc true f 0%nat n 即        *)
(*   Σ_{k<n} (−1)^k·f(k)。sg=false 分支取 Qopp，全 Q 侧只用 Qplus/    *)
(*   Qopp（零 Qminus，判例 规避）。符号-奇偶对齐由 sgp 盾引理固定。   *)
(*                                                                *)
(*   Id (Qle_bool x y) true，bool 反映健全形）而非 Or 形 QleT        *)
(*   （S02:27）：Or 形右支 Id x y 受 Q 表示正规化墙（S02 头注已言     *)
(*   Id 分支无法从 Prop 层 Qle 健全构造；反例 f≡(1#2), n:=2 时       *)
(*   altsum == Qmake 0 4 表示上异于 0=Qmake 0 1，Or 形结论不可证）。  *)
(*   到 QleT' 假设面的换桥（QleT 的两支均可健全入 QleT'）。           *)
(*   全文件语句面零 stdlib Prop Qlt/Qle；Qle/Qlt 仅在证明体内转译用。 *)
(*                                                                *)
(* 【den_pos 连接说明】使用者定义 den(x) := altsum (fun k => c_k x^k)  *)
(*   (n+1)，然后：递减条件面 forall k, QleT 0 (c_k x^k) +             *)
(*   QleT (c_{k+1} x^{k+1}) (c_k x^k) ⟹ altsum_nonneg 直接给出        *)
(*   QleT' 0 (den x)。奇偶分段使用用 altsum_nonneg_even/odd；        *)
(*   展开方程用 altsum_skip2（步长 2）。                              *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* 件 0：Q 助手（QleT'/QltT 加法组合与表示平移；全库现成件拼装）     *)
(* ============================================================ *)

(* 两个非负相加非负（0+0 表示平移经 qeq） *)
Lemma altsum_qleT'_0_plus : forall x y : Q,
  QleT' 0 x -> QleT' 0 y -> QleT' 0 (x + y).
Proof.
  intros x y Hx Hy.
  apply (qleT'_trans 0 (0 + 0) (x + y)).
  - apply qeq_leT'. ring.
  - apply qleT'_plus_compat; assumption.
Qed.

(* 两个非正相加非正 *)
Lemma altsum_qleT'_plus_nonpos : forall x y : Q,
  QleT' x 0 -> QleT' y 0 -> QleT' (x + y) 0.
Proof.
  intros x y Hx Hy.
  apply Qle_to_QleT'.
  apply (Qle_trans (x + y) (0 + 0) 0).
  - apply (Qplus_le_compat x 0 y 0); apply QleT'_to_Qle; assumption.
  - apply qeq_imp_qle. ring.
Qed.

(* 加非正不增：y ≤ 0 ⟹ x + y ≤ x（x+0 表示平移） *)
Lemma altsum_qleT'_plus_r0 : forall x y : Q, QleT' y 0 -> QleT' (x + y) x.
Proof.
  intros x y Hy.
  apply (qleT'_trans (x + y) (x + 0) x).
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + exact Hy.
  - apply qeq_leT'. ring.
Qed.

(* 取负翻身：0 ≤ a ⟹ −a ≤ 0（−0 表示平移） *)
Lemma altsum_qleT'_neg_le0 : forall a : Q, QleT' 0 a -> QleT' (Qopp a) 0.
Proof.
  intros a H.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qopp a) (Qopp 0) 0).
  - apply Qopp_le_compat. apply QleT'_to_Qle. exact H.
  - apply qeq_imp_qle. ring.
Qed.

(* 差非正：a ≤ b ⟹ a + (−b) ≤ 0（b+(−b)==0 平移） *)
Lemma altsum_qleT'_sub_le0 : forall a b : Q, QleT' a b -> QleT' (a + Qopp b) 0.
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  apply (Qle_trans (a + Qopp b) (b + Qopp b) 0).
  - apply (Qplus_le_compat a b (Qopp b) (Qopp b)).
    + apply QleT'_to_Qle. exact H.
    + apply Qle_refl.
  - apply qeq_imp_qle. apply Qplus_opp_r.
Qed.

(* 差非负：a ≤ b ⟹ 0 ≤ b + (−a)（a+(−a)==0 平移） *)
Lemma altsum_qleT'_ge_sub : forall a b : Q, QleT' a b -> QleT' 0 (b + Qopp a).
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  apply (Qle_trans 0 (a + Qopp a) (b + Qopp a)).
  - apply qeq_imp_qle. apply Qeq_sym. apply Qplus_opp_r.
  - apply (Qplus_le_compat a b (Qopp a) (Qopp a)).
    + apply QleT'_to_Qle. exact H.
    + apply Qle_refl.
Qed.

(* Q 加法对 Qeq 的双面相容（Qplus_inj_r/l + Qplus_comm 组合） *)
Lemma altsum_qplus_eq_compat : forall x y z t : Q,
  x == y -> z == t -> x + z == y + t.
Proof.
  intros x y z t H1 H2.
  apply (Qeq_trans (x + z) (y + z) (y + t)).
  - apply (proj2 (Qplus_inj_r x y z)). exact H1.
  - apply (Qeq_trans (y + z) (z + y) (y + t)).
    + apply Qplus_comm.
    + apply (Qeq_trans (z + y) (t + y) (y + t)).
      * apply (proj2 (Qplus_inj_r z t y)). exact H2.
      * apply Qplus_comm.
Qed.

(* QltT 左平移：a == c 且 a <T b ⟹ c <T b *)
Lemma altsum_qltT_shift_l : forall a b c : Q, a == c -> QltT a b -> QltT c b.
Proof.
  intros a b c Hac Hlt.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans c a b).
  - apply qeq_imp_qle. apply Qeq_sym. exact Hac.
  - apply QltT_to_Qlt. exact Hlt.
Qed.

(* 严格差正：a <T b ⟹ 0 <T b + (−a) *)
Lemma altsum_qltT_sub_pos : forall a b : Q, QltT a b -> QltT 0 (b + Qopp a).
Proof.
  intros a b H.
  apply (altsum_qltT_shift_l (a + Qopp a) (b + Qopp a) 0).
  - apply Qplus_opp_r.
  - apply Qlt_to_QltT.
    apply (Qplus_lt_le_compat a b (Qopp a) (Qopp a)).
    + apply QltT_to_Qlt. exact H.
    + apply Qle_refl.
Qed.

(* 严格和正：0 <T x 且 0 ≤T' y ⟹ 0 <T x + y *)
Lemma altsum_strict_plus_le : forall x y : Q,
  QltT 0 x -> QleT' 0 y -> QltT 0 (x + y).
Proof.
  intros x y Hx Hy.
  assert (H1 : QltT (0 + 0) (y + x)).
  { apply (qleT'_plus_ltT_ltT 0 y 0 x).
    - exact Hy.
    - exact Hx. }
  apply (qeq_ltT (y + x) (x + y)).
  - ring.
  - apply (altsum_qltT_shift_l (0 + 0) (y + x) 0).
    + ring.
    + exact H1.
Qed.

(*
   左支 QltT 经 qltT_leT'；右支 Id 是表示相等，destruct 后 refl *)
Lemma altsum_QleT_to_QleT' : forall x y : Q, QleT x y -> QleT' x y.
Proof.
  intros x y H. destruct H as [Hlt | Hid].
  - apply qltT_leT'. exact Hlt.
  - destruct Hid. apply qleT'_refl.
Qed.

(* ============================================================ *)
(* 件 1：奇偶数据分裂（pbit/phalf，Set 层数据；eq 假设非 Prop 分裂） *)
(* ============================================================ *)

Fixpoint altsum_pbit (n : nat) : bool :=
  match n with
  | 0%nat => true
  | Datatypes.S 0%nat => false
  | Datatypes.S (Datatypes.S m) => altsum_pbit m
  end.

Fixpoint altsum_phalf (n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | Datatypes.S 0%nat => 0%nat
  | Datatypes.S (Datatypes.S m) => Datatypes.S (altsum_phalf m)
  end.

Lemma altsum_peven_eq : forall n : nat,
  altsum_pbit n = true -> n = (2 * altsum_phalf n)%nat.
Proof.
  assert (Hadj : forall n : nat,
    And (altsum_pbit n = true -> n = (2 * altsum_phalf n)%nat)
        (altsum_pbit (Datatypes.S n) = true ->
         Datatypes.S n = (2 * altsum_phalf (Datatypes.S n))%nat)).
  { induction n as [| n IH].
    - split; intro H.
      + reflexivity.
      + discriminate.
    - destruct IH as [IH1 IH2]. split.
      + exact IH2.
      + intro H.
        change (altsum_pbit n = true) in H.
        assert (Hn : n = (2 * altsum_phalf n)%nat) by exact (IH1 H).
        change (altsum_phalf (Datatypes.S (Datatypes.S n)))
          with (Datatypes.S (altsum_phalf n)).
        lia. }
  intro n. intro H. apply (fst (Hadj n) H).
Qed.

Lemma altsum_podd_eq : forall n : nat,
  altsum_pbit n = false -> n = (2 * altsum_phalf n + 1)%nat.
Proof.
  assert (Hadj : forall n : nat,
    And (altsum_pbit n = false -> n = (2 * altsum_phalf n + 1)%nat)
        (altsum_pbit (Datatypes.S n) = false ->
         Datatypes.S n = (2 * altsum_phalf (Datatypes.S n) + 1)%nat)).
  { induction n as [| n IH].
    - split; intro H.
      + discriminate.
      + reflexivity.
    - destruct IH as [IH1 IH2]. split.
      + exact IH2.
      + intro H.
        change (altsum_pbit n = false) in H.
        assert (Hn : n = (2 * altsum_phalf n + 1)%nat) by exact (IH1 H).
        change (altsum_phalf (Datatypes.S (Datatypes.S n)))
          with (Datatypes.S (altsum_phalf n)).
        lia. }
  intro n. intro H. apply (fst (Hadj n) H).
Qed.

(* ============================================================ *)
(* 件 2：S1 主件定义——交错尾和（符号经 bool 累加器递归吸收）        *)
(* ============================================================ *)

Fixpoint altsum_acc (sg : bool) (f : nat -> Q) (k n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S m => (if sg then f k else Qopp (f k))
                     + altsum_acc (negb sg) f (Datatypes.S k) m
  end.

Definition altsum (f : nat -> Q) (n : nat) : Q := altsum_acc true f 0%nat n.

(* 展开方程（反射引理）：单步剥项，符号逐层吸收 *)
Lemma altsum_acc_T : forall (f : nat -> Q) (k m : nat),
  altsum_acc true f k (Datatypes.S m) == f k + altsum_acc false f (Datatypes.S k) m.
Proof. intros f k m. simpl. ring. Qed.

Lemma altsum_acc_F : forall (f : nat -> Q) (k m : nat),
  altsum_acc false f k (Datatypes.S m) == Qopp (f k) + altsum_acc true f (Datatypes.S k) m.
Proof. intros f k m. simpl. ring. Qed.

Lemma altsum_acc_0_eq : forall (sg : bool) (f : nat -> Q) (k : nat),
  altsum_acc sg f k 0%nat == 0.
Proof. intros sg f k. exact (Qeq_refl 0). Qed.

(* 使用者展开方程：步长 2 的重组（相邻配对面） *)
Lemma altsum_skip2 : forall (f : nat -> Q) (m : nat),
  altsum f (Datatypes.S (Datatypes.S m)) == (f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat m.
Proof. intros f m. unfold altsum. rewrite altsum_acc_T. rewrite altsum_acc_F. ring. Qed.

(* 符号-奇偶对齐函数与盾引理：偶指标取 true、奇指标取 false *)
Definition altsum_sgp (k : nat) : bool := if Nat.even k then true else false.

Lemma altsum_even_2k : forall k : nat, Nat.even (2 * k)%nat = true.
Proof.
  intro k. induction k as [| k IH].
  - reflexivity.
  - replace (2 * Datatypes.S k)%nat
      with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
    exact IH.
Qed.

Lemma altsum_sgp_2k : forall k : nat, altsum_sgp (2 * k)%nat = true.
Proof. intro k. unfold altsum_sgp. rewrite altsum_even_2k. reflexivity. Qed.

Lemma altsum_sgp_2k1 : forall k : nat, altsum_sgp (2 * k + 1)%nat = false.
Proof.
  intro k. unfold altsum_sgp. induction k as [| k IH].
  - reflexivity.
  - replace (2 * Datatypes.S k + 1)%nat
      with (Datatypes.S (Datatypes.S (2 * k + 1)))%nat by lia.
    exact IH.
Qed.

(* ============================================================ *)
(* 件 3：S3 主件——三形夹板（偶起偶数项 ≥0；偶起奇数项 ≥0；           *)
(*       奇起偶数项 ≤0），归纳变元为项数 m，指标 k 全称于 IH         *)
(* ============================================================ *)

Lemma altsum_sandwich : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  forall k : nat,
  And (QleT' 0 (altsum_acc (altsum_sgp (2 * k)%nat) f (2 * k)%nat (2 * m)%nat))
  (And (QleT' 0 (f (2 * k)%nat
                 + altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * m)%nat))
       (QleT' (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * m)%nat) 0)).
Proof.
  intros f m H0 Hd.
  induction m as [| m IH].
  - intro k. split.
    + reflexivity.
    + split.
      * change (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * 0)%nat)
          with 0%Q.
        apply (qleT'_trans 0 (f (2 * k)%nat) (f (2 * k)%nat + 0)).
        -- exact (H0 (2 * k)%nat).
        -- apply qeq_leT'. ring.
      * change (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat (2 * 0)%nat)
          with 0%Q.
        reflexivity.
  - intro k. destruct (IH (Datatypes.S k)) as [IH1 [IH2 IH4]].
    rewrite (altsum_sgp_2k (Datatypes.S k)) in IH1.
    rewrite (altsum_sgp_2k1 (Datatypes.S k)) in IH2.
    rewrite (altsum_sgp_2k1 (Datatypes.S k)) in IH4.
    (* 奇起尾（2k+1 起，2m+2 项）的两次剥项方程 *)
    assert (Hp : altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
                   (2 * Datatypes.S m)%nat
                 == (Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
                    + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat).
    { rewrite altsum_sgp_2k1.
      replace (2 * Datatypes.S m)%nat with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
      rewrite altsum_acc_F.
      replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
      rewrite altsum_acc_T.
      replace (Datatypes.S (2 * Datatypes.S k))%nat with (2 * Datatypes.S k + 1)%nat by lia.
      ring. }
    assert (Hdk : QleT' (f (2 * Datatypes.S k)%nat) (f (2 * k + 1)%nat)).
    { replace (2 * Datatypes.S k)%nat with (Datatypes.S (2 * k + 1))%nat by lia.
      apply Hd. }
    assert (Hdk0 : QleT' (f (2 * k + 1)%nat) (f (2 * k)%nat)).
    { replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat by lia.
      apply Hd. }
    split.
    + (* W1：偶起偶数项 ≥ 0 = 相邻差对 + 偶起偶数项尾（k+1） *)
      assert (Hw1 : altsum_acc (altsum_sgp (2 * k)%nat) f (2 * k)%nat
                      (2 * Datatypes.S m)%nat
                    == (f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
                       + altsum_acc true f (2 * Datatypes.S k)%nat (2 * m)%nat).
      { rewrite (altsum_sgp_2k k).
        replace (2 * Datatypes.S k)%nat
          with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
        replace (2 * Datatypes.S m)%nat
          with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
        rewrite altsum_acc_T.
        replace (Datatypes.S (2 * k))%nat with (2 * k + 1)%nat by lia.
        rewrite altsum_acc_F.
        replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
        ring. }
      apply (qleT'_trans 0
        ((f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
         + altsum_acc true f (2 * Datatypes.S k)%nat (2 * m)%nat)).
      * apply altsum_qleT'_0_plus.
        -- apply (altsum_qleT'_ge_sub (f (2 * k + 1)%nat) (f (2 * k)%nat)).
           ++ exact Hdk0.
        -- exact IH1.
      * apply qeq_leT'. apply Qeq_sym. exact Hw1.
    + split.
      * (* W2：偶起奇数项 ≥ 0 = 相邻差对 + 偶起奇数项尾（k+1） *)
        assert (Hw2 : altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
                        (2 * Datatypes.S m)%nat
                      == Qopp (f (2 * k + 1)%nat)
                         + (f (2 * Datatypes.S k)%nat
                            + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat)).
        { rewrite (altsum_sgp_2k1 k).
          replace (2 * Datatypes.S m)%nat
            with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
          rewrite altsum_acc_F.
          replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
          rewrite altsum_acc_T.
          replace (Datatypes.S (2 * Datatypes.S k))%nat
            with (2 * Datatypes.S k + 1)%nat by lia.
          ring. }
        apply (qleT'_trans 0
          ((f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
           + (f (2 * Datatypes.S k)%nat
              + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat))).
        -- apply altsum_qleT'_0_plus.
           ++ apply (altsum_qleT'_ge_sub (f (2 * k + 1)%nat) (f (2 * k)%nat)).
              ** exact Hdk0.
           ++ exact IH2.
        -- apply (qleT'_trans
             ((f (2 * k)%nat + Qopp (f (2 * k + 1)%nat))
              + (f (2 * Datatypes.S k)%nat
                 + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat))
             (f (2 * k)%nat
              + (Qopp (f (2 * k + 1)%nat)
                 + (f (2 * Datatypes.S k)%nat
                    + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat)))).
           ++ apply qeq_leT'. ring.
           ++ apply qeq_leT'.
              apply (altsum_qplus_eq_compat (f (2 * k)%nat) (f (2 * k)%nat)
                (Qopp (f (2 * k + 1)%nat)
                 + (f (2 * Datatypes.S k)%nat
                    + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat))
                (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
                   (2 * Datatypes.S m)%nat)).
              ** apply Qeq_refl.
              ** apply Qeq_sym. exact Hw2.
      * (* W4：奇起偶数项 ≤ 0 = −f(2k+1) + 偶起奇数项尾（k+1），尾 ≤ f(2k+2) *)
        apply (qleT'_trans
          (altsum_acc (altsum_sgp (2 * k + 1)%nat) f (2 * k + 1)%nat
             (2 * Datatypes.S m)%nat)
          ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
           + altsum_acc false f (2 * Datatypes.S k + 1)%nat (2 * m)%nat)
          0).
        -- apply qeq_leT'. exact Hp.
        -- apply altsum_qleT'_plus_nonpos.
           ++ apply (qleT'_trans
                ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat))
                (f (2 * Datatypes.S k)%nat + Qopp (f (2 * k + 1)%nat)) 0).
              ** apply qeq_leT'. ring.
              ** apply altsum_qleT'_sub_le0. exact Hdk.
           ++ exact IH4.
Qed.

(* 偶项数（n = 2m）：交错和非负 *)
Lemma altsum_nonneg_even : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f (2 * m)%nat).
Proof.
  intros f m H0 Hd.
  assert (Hs := fst (altsum_sandwich f m H0 Hd 0%nat)).
  rewrite (altsum_sgp_2k 0%nat) in Hs.
  exact Hs.
Qed.

(* 奇项数（n = 2m+1）：交错和非负（末项 f(2m) 为正贡献） *)
Lemma altsum_nonneg_odd : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f (2 * m + 1)%nat).
Proof.
  intros f m H0 Hd.
  assert (Hp : altsum f (2 * m + 1)%nat == f 0%nat + altsum_acc false f 1%nat (2 * m)%nat).
  { unfold altsum. replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat by lia.
    rewrite altsum_acc_T. reflexivity. }
  apply (qleT'_trans 0 (f 0%nat + altsum_acc false f 1%nat (2 * m)%nat)
    (altsum f (2 * m + 1)%nat)).
  - assert (Hs := fst (snd (altsum_sandwich f m H0 Hd 0%nat))).
    rewrite (altsum_sgp_2k1 0%nat) in Hs.
    exact Hs.
  - apply qeq_leT'. apply Qeq_sym. exact Hp.
Qed.

(* 一般 n：Set 层数据分裂（pbit），逐支套用偶/奇形——S3 主件 *)
Lemma altsum_nonneg_leT : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f n).
Proof.
  intros f n H0 Hd. destruct (altsum_pbit n) eqn:Ep.
  - rewrite (altsum_peven_eq n Ep). apply altsum_nonneg_even; assumption.
  - rewrite (altsum_podd_eq n Ep). apply altsum_nonneg_odd; assumption.
Qed.

Lemma altsum_nonneg : forall (f : nat -> Q) (n : nat),
  (forall k, QleT 0 (f k)) ->
  (forall k, QleT (f (Datatypes.S k)) (f k)) ->
  QleT' 0 (altsum f n).
Proof.
  intros f n H0 Hd.
  apply (altsum_nonneg_leT f n).
  - intros k. apply altsum_QleT_to_QleT'. apply H0.
  - intros k. apply altsum_QleT_to_QleT'. apply Hd.
Qed.

(* ============================================================ *)
(* 件 4：上界伴件 altsum_le_head（交错和 ≤ 首项）                    *)
(*   支撑件：奇起任意项数尾 ≤ 0（相邻合取两步归纳）                  *)
(* ============================================================ *)

Lemma altsum_altacc_odd_le0 : forall (f : nat -> Q) (m : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' (altsum_acc false f (2 * 0 + 1)%nat m) 0.
Proof.
  intros f m H0 Hd.
  assert (Hadj : forall t : nat,
    And (forall k, QleT' (altsum_acc false f (2 * k + 1)%nat t) 0)
        (forall k, QleT' (altsum_acc false f (2 * k + 1)%nat (Datatypes.S t)) 0)).
  { induction t as [| t IH].
    - split.
      + intro k. reflexivity.
      + intro k.
        apply (qleT'_trans (altsum_acc false f (2 * k + 1)%nat 1%nat)
          (Qopp (f (2 * k + 1)%nat) + 0) 0).
        * apply qeq_leT'.
          rewrite altsum_acc_F.
          rewrite (altsum_acc_0_eq true f (Datatypes.S (2 * k + 1))).
          ring.
        * apply (qleT'_trans (Qopp (f (2 * k + 1)%nat) + 0)
            (Qopp (f (2 * k + 1)%nat)) 0).
          -- apply qeq_leT'. ring.
          -- apply altsum_qleT'_neg_le0. apply H0.
    - destruct IH as [IH1 IH2]. split.
      + exact IH2.
      + intro k.
        assert (Hp : altsum_acc false f (2 * k + 1)%nat
                       (Datatypes.S (Datatypes.S t))
                     == (Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
                        + altsum_acc false f (2 * Datatypes.S k + 1)%nat t).
        { rewrite altsum_acc_F.
          replace (Datatypes.S (2 * k + 1))%nat with (2 * Datatypes.S k)%nat by lia.
          rewrite altsum_acc_T.
          replace (Datatypes.S (2 * Datatypes.S k))%nat
            with (2 * Datatypes.S k + 1)%nat by lia.
          ring. }
        apply (qleT'_trans
          (altsum_acc false f (2 * k + 1)%nat (Datatypes.S (Datatypes.S t)))
          ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat)
           + altsum_acc false f (2 * Datatypes.S k + 1)%nat t)
          0).
        * apply qeq_leT'. exact Hp.
        * apply altsum_qleT'_plus_nonpos.
          -- apply (qleT'_trans
               ((Qopp (f (2 * k + 1)%nat) + f (2 * Datatypes.S k)%nat))
               (f (2 * Datatypes.S k)%nat + Qopp (f (2 * k + 1)%nat)) 0).
             ++ apply qeq_leT'. ring.
             ++ apply altsum_qleT'_sub_le0.
                replace (2 * Datatypes.S k)%nat with (Datatypes.S (2 * k + 1))%nat by lia.
                apply Hd.
          -- apply IH1.
    }
  apply (fst (Hadj m) 0%nat).
Qed.

(* S3 伴件：交错和 ≤ 首项（任意 n） *)
Lemma altsum_le_head : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QleT' (altsum f n) (f 0%nat).
Proof.
  intros f n H0 Hd. destruct n as [| m].
  - apply (qleT'_trans (altsum f 0%nat) 0 (f 0%nat)).
    + change (altsum f 0%nat) with 0%Q. reflexivity.
    + exact (H0 0%nat).
  - assert (Hp : altsum f (Datatypes.S m) == f 0%nat + altsum_acc false f 1%nat m).
    { unfold altsum. rewrite altsum_acc_T. reflexivity. }
    apply (qleT'_trans (altsum f (Datatypes.S m)) (f 0%nat + 0) (f 0%nat)).
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * exact (altsum_altacc_odd_le0 f m H0 Hd).
    + apply qeq_leT'. ring.
Qed.

(* ============================================================ *)
(* 件 5：S4 加分——严格版与 f0−f1 下界细化                           *)
(* ============================================================ *)

(* 偶指标起（2k 起）任意项数尾 ≥ 0（pbit 分裂：偶数项用 W1、奇数项剥    *)
(* 一项后用 W2） *)
Lemma altsum_altacc_evenstart_pos : forall (f : nat -> Q) (k m : nat),
  (forall j, QleT' 0 (f j)) ->
  (forall j, QleT' (f (Datatypes.S j)) (f j)) ->
  QleT' 0 (altsum_acc true f (2 * k)%nat m).
Proof.
  intros f k m H0 Hd. destruct (altsum_pbit m) eqn:Ep.
  - rewrite (altsum_peven_eq m Ep).
    assert (Hs := fst (altsum_sandwich f (altsum_phalf m) H0 Hd k)).
    rewrite (altsum_sgp_2k k) in Hs.
    exact Hs.
  - rewrite (altsum_podd_eq m Ep).
    replace (2 * altsum_phalf m + 1)%nat with (Datatypes.S (2 * altsum_phalf m))%nat by lia.
    assert (Hp : altsum_acc true f (2 * k)%nat (Datatypes.S (2 * altsum_phalf m))
                 == f (2 * k)%nat + altsum_acc false f (Datatypes.S (2 * k))%nat
                      (2 * altsum_phalf m)%nat).
    { rewrite altsum_acc_T. reflexivity. }
    apply (qleT'_trans 0
      (f (2 * k)%nat + altsum_acc false f (Datatypes.S (2 * k))%nat
         (2 * altsum_phalf m)%nat)
      (altsum_acc true f (2 * k)%nat (Datatypes.S (2 * altsum_phalf m)))).
    + assert (Hs := fst (snd (altsum_sandwich f (altsum_phalf m) H0 Hd k))).
      rewrite (altsum_sgp_2k1 k) in Hs.
      replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat in Hs by lia.
      exact Hs.
    + apply qeq_leT'. apply Qeq_sym. exact Hp.
Qed.

(* 严格版：首对严格递减（f1 <T f0）且 n ≥ 2 ⟹ 交错和严格正 *)
Lemma altsum_pos_strict : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  QltT (f 1%nat) (f 0%nat) -> (2 <= n)%nat ->
  QltT 0 (altsum f n).
Proof.
  intros f n H0 Hd Hlt Hn. destruct n as [|[|m]].
  - lia.
  - lia.
  - destruct m as [| m'].
    + (* n = 2：交错和 == f0 − f1 > 0 *)
      assert (Hp : altsum f 2%nat == f 0%nat + Qopp (f 1%nat)).
      { unfold altsum. rewrite altsum_acc_T. rewrite altsum_acc_F.
        rewrite (altsum_acc_0_eq true f 2%nat). ring. }
      apply (qeq_ltT (f 0%nat + Qopp (f 1%nat)) (altsum f 2%nat)).
      * apply Qeq_sym. exact Hp.
      * apply altsum_qltT_sub_pos. exact Hlt.
    + (* n ≥ 3：严格首对 + 非负尾 *)
      assert (Hp : altsum f (Datatypes.S (Datatypes.S (Datatypes.S m')))
                   == (f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat (Datatypes.S m')).
      { unfold altsum. rewrite altsum_acc_T. rewrite altsum_acc_F. ring. }
      apply (qeq_ltT
        ((f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat (Datatypes.S m'))
        (altsum f (Datatypes.S (Datatypes.S (Datatypes.S m'))))).
      * apply Qeq_sym. exact Hp.
      * apply altsum_strict_plus_le.
        -- apply altsum_qltT_sub_pos. exact Hlt.
        -- exact (altsum_altacc_evenstart_pos f 1%nat (Datatypes.S m') H0 Hd).
Qed.

(* 奇偶细化（真方向）：n ≥ 1 ⟹ f0 − f1 ≤ 交错和。
   【规格「奇 n 时 altsum ≤ f0 − f1」修正】该方向数学上不成立：
   反例 f ≡ 1（常数列满足非负递减）时 altsum f 3 = 1 > 0 = f0 − f1。
   真细化是下界：交错和 ≥ f0 − f1（对一切 n ≥ 1，含偶 n）。 *)
Lemma altsum_ge_pair0 : forall (f : nat -> Q) (n : nat),
  (forall k, QleT' 0 (f k)) ->
  (forall k, QleT' (f (Datatypes.S k)) (f k)) ->
  (1 <= n)%nat ->
  QleT' (f 0%nat + Qopp (f 1%nat)) (altsum f n).
Proof.
  intros f n H0 Hd Hn. destruct n as [| m].
  - lia.
  - destruct m as [| m'].
    + (* n = 1：交错和 == f0 ≥ f0 − f1 *)
      assert (Hp : altsum f 1%nat == f 0%nat + 0).
      { unfold altsum. rewrite altsum_acc_T.
        rewrite (altsum_acc_0_eq false f 1%nat). reflexivity. }
      apply (qleT'_trans (f 0%nat + Qopp (f 1%nat)) (f 0%nat + 0) (altsum f 1%nat)).
      * apply qleT'_plus_compat.
        -- apply qleT'_refl.
        -- apply altsum_qleT'_neg_le0. apply H0.
      * apply qeq_leT'. apply Qeq_sym. exact Hp.
    + (* n ≥ 2：交错和 == (f0 − f1) + 偶起尾，尾 ≥ 0 *)
      assert (Hp : altsum f (Datatypes.S (Datatypes.S m'))
                   == (f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat m').
      { unfold altsum. rewrite altsum_acc_T. rewrite altsum_acc_F. ring. }
      apply (qleT'_trans (f 0%nat + Qopp (f 1%nat))
        ((f 0%nat + Qopp (f 1%nat)) + altsum_acc true f 2%nat m')
        (altsum f (Datatypes.S (Datatypes.S m')))).
      * apply (qleT'_trans (f 0%nat + Qopp (f 1%nat)) ((f 0%nat + Qopp (f 1%nat)) + 0) _).
        -- apply qeq_leT'. ring.
        -- apply (qleT'_plus_compat (f 0%nat + Qopp (f 1%nat))
                    (f 0%nat + Qopp (f 1%nat)) 0%Q
                    (altsum_acc true f 2%nat m')).
           ++ apply qleT'_refl.
           ++ exact (altsum_altacc_evenstart_pos f 1%nat m' H0 Hd).
      * apply qeq_leT'. apply Qeq_sym. exact Hp.
Qed.

(* ============================================================ *)
(* 件 6：S2 具体例暖身（n ≤ 3，递减条件下逐例计算闭合）              *)
(* ============================================================ *)

(* 常值列 (1#2)：两项交错 1/2 − 1/2 == 0，非负平凡成立 *)
Example altsum_ex_2 : QleT' 0 (altsum (fun _ => (1#2)%Q) 2).
Proof. unfold QleT'. exact (@id_refl _ true). Qed.

(* 常值列 (2#1)：三项交错 2 − 2 + 2 == 2 > 0 *)
Example altsum_ex_3 : QltT 0 (altsum (fun _ => (2#1)%Q) 3).
Proof. unfold QltT. exact (@id_refl _ true). Qed.

(* 常值列 (3#1)：单项 3 ≥ 0 *)
Example altsum_ex_1 : QleT' 0 (altsum (fun _ => (3#1)%Q) 1).
Proof. unfold QleT'. exact (@id_refl _ true). Qed.

(* 具体递减列 f = 3, 2, 1：三项交错 3 − 2 + 1 == 2 > 0（S4 实例） *)
Example altsum_ex_dec3 : QltT 0 (altsum (fun k => (3#1)%Q + Qopp ((Z.of_nat k # 1)%Q)) 3).
Proof. unfold QltT. exact (@id_refl _ true). Qed.
