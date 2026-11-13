(* ============================================================ UpReqPadeQLeg —— 使命行：Q 层序定律肢：有理层的序与自然数比值单调。
   主件：pql_pos_den_pos 与 pql_qlt0_eq_r / pql_nat_ratio_mono 有理序定律族。
   依赖：无显式 Require 面（自足件）。
   构造性注记：零 Require Psatz（Lia 即足）、零外加假设语句（公理面声明）。
   编译配方：Rocq 9.1 直调（COQLIB/ROCQLIB 钉 9.1 库根），
   coqc -q -Q . "" <件名>.v，cpu_guard 分档执行。
   ============================================================ *)
(* 补充注记：Padé nia 战术位 → 自建 Q 单调肢                         *)
(* 公理面声明：本件零 Require Psatz（Lia 即足）、零外加假设语句；      *)
(*   前缀 pql_ 全库防撞。                                            *)
(* 覆盖三族（实测 12 活位点）：              *)
(*   族 A：Qeq→Qlt 传桥（7 位点）= Sign/Lower/BetaPos 的               *)
(*     *_qlt0_eq_r（3 处同形）+ Lower cpl_qlt_eq_l/cpl_qlt_eq_sr +     *)
(*     Finale cpf_qlt_eq_l/cpf_qlt_eq_r。基肢 = pql_qlt0_eq_r，        *)
(*     双向肢 = pql_qlt_eq_l / pql_qlt_eq_r。                         *)
(*   族 B：Q 加法严格桥（3 位点）= Finale cpf_qlt_add_r /              *)
(*     cpf_qle_lt_add / cpf_qlt_le_add。                              *)
(*   族 C：Z 层系数比单调 Nat 肢（2 位点）= DenPos pdp_R_ge_1 /        *)
(*     DenPos12 pdq_R_ge_2 的 cbn 后 Z 目标，原 nia 位。               *)
(* 证法：destruct 全构造子 + 端点 cbn [Qnum Qden] 后，乘法单调/非负     *)
(*   显式装配（Z.mul_le_mono_nonneg_r / Z.mul_lt_mono_pos_r /          *)
(*   Z.mul_nonneg_nonneg）+ lia 线性完成——零非线性反射依赖，            *)
(*   即不引入 Psatz/micromega 环境闭包。                                *)
(* 坑记：Q_scope 开启下 %Z 内的 == 仍解析为 Qeq（Z 面必须写 =）；       *)
(*   9.0 本环境无 Z.mul_le_mono_l/r 与 Z.mul_le_mono 四参通形，        *)
(*   可用形是非负前提三参 Z.mul_le_mono_nonneg_l/r 与 iff 形           *)
(*   Z.mul_le_mono_pos_l/r / Z.mul_lt_mono_pos_l/r；Z_le_gt_dec        *)
(*   在 ZArith 命名空间（QArith 不透出，须显式 Require）。             *)
(* 双先例：UpReqPadeTailPos.v（Lia Setoid 形零 nia 实证）+             *)
(*   UpReqPadeBetaPos.v pbp_qfact_mono（自建单调先例）。               *)

From Stdlib Require Import QArith.QArith Arith.Arith Lia ZArith.

Local Open Scope Q_scope.
Local Open Scope Z_scope.

(* 正分母正性（Qden 是 positive，显式钉定，不依赖 zify 隐式） *)
Lemma pql_pos_den_pos : forall d : positive, (0 < Z.pos d)%Z.
Proof. exact Pos2Z.is_pos. Qed.

(* ============================================================ *)
(* 族 A 基肢：Qeq 右传（0 起点）：a == b ⟹ 0 < a ⟹ 0 < b               *)
(*   Z 面：na·db = nb·da ∧ 1 ≤ na ⊢ 0 < nb（反证 + 乘单调）。          *)
(* ============================================================ *)
Lemma pql_qlt0_eq_r : forall a b : Q, a == b -> Qlt 0 a -> Qlt 0 b.
Proof.
  intros a b Hab Ha.
  destruct a as [na da]. destruct b as [nb db].
  unfold Qeq in Hab. unfold Qlt in Ha |- *.
  cbn [Qnum Qden] in Hab, Ha |- *.
  pose proof (pql_pos_den_pos da) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (pql_pos_den_pos db) as Hdb.
  (* Ha/goal 中的 *1 与 *0 由 lia 线性归一：得 1 <= na，目标 0 < nb *)
  assert (Hna : (1 <= na)%Z) by lia.
  (* 主等式：na * db = nb * da（注意：Q_scope 下 == 是 Qeq，Z 面写 =） *)
  assert (Hmul : (na * Z.pos db = nb * Z.pos da)%Z) by exact Hab.
  assert (Hdb0 : (0 <= Z.pos db)%Z) by lia.
  (* 反证：nb <= 0 则 nb*da <= 0，与 na*db >= 1*db >= 1 矛盾 *)
  destruct (Z_le_gt_dec nb 0) as [Hn0 | Hn0].
  - exfalso.
    pose proof (Z.mul_le_mono_nonneg_r nb 0 (Z.pos da) Hda0 Hn0) as Hneg.
    pose proof (Z.mul_le_mono_nonneg_r 1 na (Z.pos db) Hdb0 Hna) as Hpos.
    lia.
  - lia.
Qed.

(* 族 A 右传肢：a == b ⟹ c < a ⟹ c < b
   Z 面：nc·da < na·dc，na·db = nb·da ⊢ nc·db < nb·dc
   （两边乘 db 正数，na·dc·db = nb·dc·da 换形，再消 da）。 *)
Lemma pql_qlt_eq_r : forall a b c : Q, a == b -> Qlt c a -> Qlt c b.
Proof.
  intros a b c Hab Hlt.
  destruct a as [na da]. destruct b as [nb db]. destruct c as [nc dc].
  unfold Qeq in Hab. unfold Qlt in Hlt |- *.
  cbn [Qnum Qden] in Hab, Hlt |- *.
  pose proof (pql_pos_den_pos da) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (pql_pos_den_pos db) as Hdb.
  pose proof (pql_pos_den_pos dc) as Hdc.
  (* 换形恒等式（ring 只收恒等肢） *)
  assert (E1 : (na * Z.pos dc * Z.pos db = (na * Z.pos db) * Z.pos dc)%Z) by ring.
  assert (E2 : (nc * Z.pos da * Z.pos db = (nc * Z.pos db) * Z.pos da)%Z) by ring.
  assert (E3 : ((nb * Z.pos da) * Z.pos dc = nb * Z.pos dc * Z.pos da)%Z) by ring.
  rewrite Hab in E1.
  rewrite E3 in E1.
  (* Hlt 两边乘 db > 0 *)
  assert (Hm : (nc * Z.pos da * Z.pos db < na * Z.pos dc * Z.pos db)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (Z.pos db) (nc * Z.pos da) (na * Z.pos dc) Hdb)).
    lia. }
  rewrite E2 in Hm. rewrite E1 in Hm.
  (* Hm : (nc*db)*da < nb*dc*da，消正因子 da *)
  destruct (Z_le_gt_dec (nb * Z.pos dc) (nc * Z.pos db)) as [Hbad | Hgood].
  - exfalso.
    pose proof (Z.mul_le_mono_nonneg_r (nb * Z.pos dc) (nc * Z.pos db) (Z.pos da) Hda0 Hbad) as Hc.
    lia.
  - lia.
Qed.

(* 族 A 左传肢：a == b ⟹ a < c ⟹ b < c
   Z 面：na·dc < nc·da，na·db = nb·da ⊢ nb·dc < nc·db（副本同法）。 *)
Lemma pql_qlt_eq_l : forall a b c : Q, a == b -> Qlt a c -> Qlt b c.
Proof.
  intros a b c Hab Hlt.
  destruct a as [na da]. destruct b as [nb db]. destruct c as [nc dc].
  unfold Qeq in Hab. unfold Qlt in Hlt |- *.
  cbn [Qnum Qden] in Hab, Hlt |- *.
  pose proof (pql_pos_den_pos da) as Hda.
  assert (Hda0 : (0 <= Z.pos da)%Z) by lia.
  pose proof (pql_pos_den_pos db) as Hdb.
  pose proof (pql_pos_den_pos dc) as Hdc.
  assert (E1 : (na * Z.pos dc * Z.pos db = (na * Z.pos db) * Z.pos dc)%Z) by ring.
  assert (E2 : (nc * Z.pos da * Z.pos db = (nc * Z.pos db) * Z.pos da)%Z) by ring.
  assert (E3 : ((nb * Z.pos da) * Z.pos dc = nb * Z.pos dc * Z.pos da)%Z) by ring.
  assert (Hm : (na * Z.pos dc * Z.pos db < nc * Z.pos da * Z.pos db)%Z).
  { apply (proj1 (Z.mul_lt_mono_pos_r (Z.pos db) (na * Z.pos dc) (nc * Z.pos da) Hdb)).
    lia. }
  (* Hm 两端换形到同一单调乘法框：nb·dc·da < nc·db·da *)
  assert (T1 : (na * Z.pos dc * Z.pos db = nb * Z.pos dc * Z.pos da)%Z).
  { transitivity ((na * Z.pos db) * Z.pos dc).
    - ring.
    - rewrite Hab. ring. }
  assert (T2 : (nc * Z.pos da * Z.pos db = nc * Z.pos db * Z.pos da)%Z) by ring.
  rewrite T1, T2 in Hm.
  (* 消正因子 da：iff 形 Z.mul_lt_mono_pos_r 反向一跳直达目标 *)
  apply (proj2 (Z.mul_lt_mono_pos_r (Z.pos da) (nb * Z.pos dc) (nc * Z.pos db) Hda)).
  exact Hm.
Qed.

(* ============================================================ *)
(* 族 B 加法严格桥三件                                                *)
(* ============================================================ *)

(* Qlt 0 b ⟹ a < a + b
   Q 层装配：Qplus_lt_r （iff 形）+ (a+0)==a 环换 + 左传肢。 *)
Lemma pql_qlt_add_r : forall a b : Q, Qlt 0 b -> Qlt a (a + b)%Q.
Proof.
  intros a b Hb.
  assert (Ht : Qlt (a + 0)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_r 0 b a)); exact Hb).
  assert (Heq : (a + 0)%Q == a%Q) by ring.
  exact (pql_qlt_eq_l (a + 0)%Q a (a + b)%Q Heq Ht).
Qed.

(* Qle 0 a ⟹ Qlt 0 b ⟹ 0 < a + b
   Q 层装配：Qplus_lt_r + 左传腵 + Qle_lt_trans。 *)
Lemma pql_qle_lt_add : forall a b : Q, Qle 0 a -> Qlt 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  assert (Ht : Qlt (a + 0)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_r 0 b a)); exact Hb).
  assert (Heq : (a + 0)%Q == a%Q) by ring.
  assert (Hlt2 : Qlt a (a + b)%Q)
    by exact (pql_qlt_eq_l (a + 0)%Q a (a + b)%Q Heq Ht).
  exact (Qle_lt_trans 0%Q a (a + b)%Q Ha Hlt2).
Qed.

(* Qlt 0 a ⟹ Qle 0 b ⟹ 0 < a + b（副本件，Qplus_lt_l 形） *)
Lemma pql_qlt_le_add : forall a b : Q, Qlt 0 a -> Qle 0 b -> Qlt 0 (a + b)%Q.
Proof.
  intros a b Ha Hb.
  assert (Ht : Qlt (0 + b)%Q (a + b)%Q)
    by (apply (proj2 (Qplus_lt_l 0 a b)); exact Ha).
  assert (Heq : (0 + b)%Q == b%Q) by ring.
  assert (Hlt2 : Qlt b (a + b)%Q)
    by exact (pql_qlt_eq_l (0 + b)%Q b (a + b)%Q Heq Ht).
  exact (Qle_lt_trans 0%Q b (a + b)%Q Hb Hlt2).
Qed.

(* ============================================================ *)
(* 族 C 系数比单调 Nat/Z 肢（DenPos / DenPos12 原nia 位形状）           *)
(*   数学核：k < n ⟹ S(n−S k) ≤ S(2n−S k)·S k                          *)
(*     （链：X ≤ 2X ≤ 2Y ≤ Y·S k）；k=0 时 Y = 2X lia 直解。            *)
(* ============================================================ *)
Lemma pql_nat_ratio_mono2 :
  forall n k : nat, (k < n)%nat ->
    (2 * Z.of_nat (S (n - S k)) <= Z.of_nat (S (2 * n - S k)) * Z.of_nat (S k))%Z.
Proof.
  intros n k Hk.
  assert (H1 : (Z.of_nat (S (n - S k)) <= Z.of_nat (S (2 * n - S k)))%Z) by lia.
  destruct k as [| k'].
  - lia.
  - assert (H2 : (Z.of_nat (S (2 * n - S (S k'))) * 2
                  <= Z.of_nat (S (2 * n - S (S k'))) * Z.of_nat (S (S k')))%Z).
    { apply (Z.mul_le_mono_nonneg_l 2%Z (Z.of_nat (S (S k')))
               (Z.of_nat (S (2 * n - S (S k'))))); lia. }
    assert (H3 : (Z.of_nat (S (n - S (S k'))) * 2
                  <= Z.of_nat (S (2 * n - S (S k'))) * 2)%Z).
    { apply (Z.mul_le_mono_nonneg_r (Z.of_nat (S (n - S (S k'))))
               (Z.of_nat (S (2 * n - S (S k')))) 2%Z); lia. }
    lia.
Qed.

Lemma pql_nat_ratio_mono :
  forall n k : nat, (k < n)%nat ->
    (Z.of_nat (S (n - S k)) <= Z.of_nat (S (2 * n - S k)) * Z.of_nat (S k))%Z.
Proof.
  intros n k Hk.
  assert (H1 : (Z.of_nat (S (n - S k))
                <= 2 * Z.of_nat (S (n - S k)))%Z) by lia.
  apply Z.le_trans with (2 * Z.of_nat (S (n - S k)))%Z.
  - exact H1.
  - apply pql_nat_ratio_mono2. exact Hk.
Qed.

Print Assumptions pql_pos_den_pos.
