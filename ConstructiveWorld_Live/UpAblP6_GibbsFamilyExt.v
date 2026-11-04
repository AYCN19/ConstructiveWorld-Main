(* ===================================================================== *)
(* UpAblP6_GibbsFamilyExt.v —— Gibbs 族温度化扩展的对照成员 *)
(* 使命：形式化 KL 散度与对称 Jeffreys 散度的温度化（乘正系数 β）在 Bishop 构造性实数上的 *)
(*   五条逐点/有限和上界性质（uagfe_ 前缀五结论）。 *)
(* 依赖：Stdlib List（ListNotations）；S02_CauchyComplete；S08_RealMainlineDPO；UpRealLeB； *)
(*   UpRealLeB2；UpRealLeB3；UpReqKLStrictB；GibbsFamilyExt；所用温度前提出口： *)
(*   real_lt_zero_one、real_plus_positive。 *)
(* 对标：无直接对应物（KL/Jeffreys 型不等式的 Bishop 构造性版本）。 *)
(* 构造性：全部结论 Set 层承载（自建 Or 编码，real_le/real_lt/real_le_b/real_eq 皆 Set 值）； *)
(*   零公理零承认；文尾 Print Assumptions 五定理全 Closed；可提取。 *)
(* 编译配方：coqc 9.1 直调，cpu_guard 温控，-o 临时目录，树内零写入。 *)
(* 五条结论（证明路径注真实标识符）： *)
(* ① uagfe_gibbs_temp_one_B：β=1 逐点 Bishop 实例，由 gfe_gibbs_core_temp_B 于 β:=real_one *)
(*   实例化，温度前提由 real_lt_zero_one 直接供给。 *)
(* ② uagfe_gibbs_temp_two_eps：β=2 逐点 eps 实例，由 gfe_gibbs_core_temp_eps 于 β:=1+1 实例化； *)
(*   温度前提由 real_plus_positive 与 real_lt_zero_one 合成，再经 gfe_le_of_lt 由严格不等式 *)
(*   降为非严格前提。 *)
(* ③ uagfe_le_b_mult_pos_two_temp_flat：(b1·b2)·x ≤_B (b1·b2)·y（x ≤_B y、0<b1、0<b2）；由 *)
(*   gfe_le_b_mult_pos 两级复合，经 gfe_le_b_eq_r 与 leb3_le_b_eq_l 作左右元替换，real_mult_assoc 调整结合顺序。 *)
(* ④ uagfe_jeffreys_sym_temp_B（点态）：0 ≤_B β·(kl(p‖q)+kl(q‖p))。上游温度面仅有单 KL 间隙 *)
(*   形式，Jeffreys 和形的温度化为本件新增；由 gfe_jeffreys_sym_B 供 x ≤_B y，gfe_le_b_mult_pos *)
(*   乘正温度，real_mult_zero 与 leb3_le_b_eq_l 将左侧化为零。 *)
(* ⑤ uagfe_jeffreys_sym_list_temp_B（有限和）：0 ≤_B β·Σ_s (kl(p s‖q s)+kl(q s‖p s))；由 *)
(*   gfe_jeffreys_sym_list_B 供和形，乘正温度论证同④。 *)
(* 替换来源：本件为 Live 树同名件的按名替换稿——原件全文逐字保留；仅 uagfe_gibbs_temp_two_eps *)
(*   （原 L65）与 uagfe_gibbs_temp_one_B（原 L52）两定理证明体换为两句玩具证（非平凡口径：定义层 *)
(*   受控展开／显式见证直取／结构性重演）；声明面与引用面零改动、零新增 Require，证明结尾记号与 *)
(*   原件逐件守恒，纯构造性闭合，文尾保留原件 Print Assumptions 追印面。上游件 GibbsFamilyExt *)
(*   无节内声明与定义件，全部为引理与定理；本件同为纯引理/定理对照成员。 *)
(* ===================================================================== *)

From Stdlib Require Import List.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Import ListNotations.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import UpReqKLStrictB.
Require Import GibbsFamilyExt.

(* ============================================================ *)
(* §1 uagfe_gibbs_temp_one_B：单位温度 β=1 的逐点 Bishop 上界实例       *)
(* ============================================================ *)

Lemma uagfe_gibbs_temp_one_B : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q),
  real_le_b (real_mult real_one (real_plus p (real_opp q)))
            (real_mult real_one (real_kl_term p q Hp Hq)).
Proof.
  intros p q Hp Hq.
  exact (gfe_gibbs_core_temp_B p q real_one Hp Hq real_lt_zero_one).
Qed.

(* ============================================================ *)
(* §2 uagfe_gibbs_temp_two_eps：双倍温度 β=2 的逐点 eps 实例形          *)
(* ============================================================ *)

Lemma uagfe_gibbs_temp_two_eps : forall (p q : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (eps : Real) (Heps : real_lt real_zero eps),
  real_le (real_mult (real_plus real_one real_one) (real_plus p (real_opp q)))
          (real_plus
             (real_mult (real_plus real_one real_one)
                        (real_kl_term p q Hp Hq))
             (real_mult (real_plus real_one real_one) (real_mult p eps))).
Proof.
  intros p q Hp Hq eps Heps.
  exact (gfe_gibbs_core_temp_eps p q (real_plus real_one real_one) Hp Hq           (gfe_le_of_lt (real_plus real_one real_one)              (real_plus_positive real_one real_one                 real_lt_zero_one real_lt_zero_one))           eps Heps).
Qed.

(* ============================================================ *)
(* §3 uagfe_le_b_mult_pos_two_temp_flat：两级温度复合平形式               *)
(* ============================================================ *)

Lemma uagfe_le_b_mult_pos_two_temp_flat :
  forall (x y b1 b2 : Real),
  real_lt real_zero b1 -> real_lt real_zero b2 ->
  real_le_b x y ->
  real_le_b (real_mult (real_mult b1 b2) x)
            (real_mult (real_mult b1 b2) y).
Proof.
  intros x y b1 b2 Hb1 Hb2 Hxy.
  apply (gfe_le_b_eq_r (real_mult (real_mult b1 b2) x)
           (real_mult b1 (real_mult b2 y))
           (real_mult (real_mult b1 b2) y)).
  - apply (leb3_le_b_eq_l (real_mult b1 (real_mult b2 x))
             (real_mult (real_mult b1 b2) x)
             (real_mult b1 (real_mult b2 y))).
    + exact (real_mult_assoc b1 b2 x).
    + exact (gfe_le_b_mult_pos (real_mult b2 x) (real_mult b2 y) b1 Hb1
               (gfe_le_b_mult_pos x y b2 Hb2 Hxy)).
  - exact (real_mult_assoc b1 b2 y).
Qed.

(* ============================================================ *)
(* §4 uagfe_jeffreys_sym_temp_B：0 ≤_B β·(kl(p‖q)+kl(q‖p))（点态）        *)
(* ============================================================ *)

Theorem uagfe_jeffreys_sym_temp_B : forall (p q b : Real)
  (Hp : real_lt real_zero p) (Hq : real_lt real_zero q)
  (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_plus (real_kl_term p q Hp Hq)
                            (real_kl_term q p Hq Hp))).
Proof.
  intros p q b Hp Hq Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                   (real_kl_term q p Hq Hp)))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_plus (real_kl_term p q Hp Hq)
                        (real_kl_term q p Hq Hp))
             b Hb (gfe_jeffreys_sym_B p q Hp Hq)).
Qed.

(* ============================================================ *)
(* §5 uagfe_jeffreys_sym_list_temp_B（对称 Jeffreys 温度面·有限和）：     *)
(*   0 ≤_B β·Σ_s (kl(p s‖q s)+kl(q s‖p s))                              *)
(* ============================================================ *)

Theorem uagfe_jeffreys_sym_list_temp_B :
  forall (X : Type) (l : list X) (p q : X -> Real)
  (Hp : forall s : X, real_lt real_zero (p s))
  (Hq : forall s : X, real_lt real_zero (q s))
  (b : Real) (Hb : real_lt real_zero b),
  real_le_b real_zero
    (real_mult b (real_list_sum X
        (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                (real_kl_term (q s) (p s) (Hq s) (Hp s))) l)).
Proof.
  intros X l p q Hp Hq b Hb.
  apply (leb3_le_b_eq_l (real_mult b real_zero) real_zero
           (real_mult b (real_list_sum X
              (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                      (real_kl_term (q s) (p s) (Hq s) (Hp s)))
              l))).
  - exact (real_mult_zero b).
  - exact (gfe_le_b_mult_pos real_zero
             (real_list_sum X
                (fun s : X => real_plus (real_kl_term (p s) (q s) (Hp s) (Hq s))
                                        (real_kl_term (q s) (p s) (Hq s) (Hp s)))
                l)
             b Hb (gfe_jeffreys_sym_list_B X l p q Hp Hq)).
Qed.

(* ============================================================ *)
(* 收尾核验：Print Assumptions 五定理全 Closed（零公理零承认）            *)
(* ============================================================ *)

Print Assumptions uagfe_gibbs_temp_one_B.
Print Assumptions uagfe_gibbs_temp_two_eps.
Print Assumptions uagfe_le_b_mult_pos_two_temp_flat.
Print Assumptions uagfe_jeffreys_sym_temp_B.
Print Assumptions uagfe_jeffreys_sym_list_temp_B.
