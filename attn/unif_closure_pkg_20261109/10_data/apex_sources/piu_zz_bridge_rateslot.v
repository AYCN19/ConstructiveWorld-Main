(* ============================================================
   模块名: piu_zz_bridge_rateslot（率面槽 v2·合并裁断版）
   构形: halving_rate_rel 阈值取预结合形 ((2·C₀)/nat) 以 Qmult_le_compat_r
     直消；tail_bridge_core 泛化「QleT' d d2 换算前提」吸收
     (2·C₀)/nat 与 2·(C₀/nat) 的 Qeq 接续；cert_relax 结论走预结合形。
   合并注记: 与 piu_zz_bridge_real（v1 常数槽件）的同名面已裁断消解，
     双 Require 安全——
     ①吸收位：两件 statement 与 proof 逐字同构的基件 18 件
       （piu_zz_c0_criterion/piu_zz_C0/piu_zz_halving_num1/
       piu_zz_halving_num2/piu_zz_halving_chain/piu_zz_C0_pos/
       piu_zz_abs_lt_upper/piu_zz_divQ_le_num/piu_zz_qpow_ge1/
       piu_zz_hpow_ge1/piu_zz_znat1_pos/piu_zz_Nw/piu_zz_pi3_witness/
       piu_zz_bridge_nonpos/piu_zz_thresh_nat_pos/piu_zz_natQ_mul_q/
       piu_zz_nat_hpow_qpow/piu_zz_ck_alpha_nat_transport）
       删除冗余定义、改由 Require Import piu_zz_bridge_real 供给
       （导出签名零变动·签名稳定律）；
     ②正名位：证书槽形语义有别者加 _v2 后缀（v1 槽=常数形
       real_const c₀，本件槽=率面形 real_const (ck_alpha c₀ 8 q)；
       常数形强于率面、反向不蕴涵，非等价改名不可）——
       piu_zz_tail_bridge_core_v2（core 广化：增 d2 参与换算前提
       QleT' d d2·N01 处方②）/piu_zz_cert_relax_v2/
       piu_zz_bridge_pos_nat_v2/piu_zz_bridge_pos_v2/
       piu_zz_bridge_full_v2；Section 更名 BridgeRealV2；
     ③使用指向：率面槽名（*_v2）经 Require Import 本件直接可用；18 基件名（piu_zz_C0/piu_zz_c0_criterion/piu_zz_bridge_nonpos 等，定义于 piu_zz_bridge_real）不随依赖自动导出——使用方另须 Require Import piu_zz_bridge_real 方得以裸名引用（Require Import 不传递导出）。
       v1 常数槽既有链维持 piu_zz_bridge_real；两件可同帧 Require，
       同名标识符单源解析无歧义。
   数学使命: real 层 μ 证书（率面形）→ lw1m_dist_pt 距离形尾段桥
     （b1+b2 合并件·率面槽适配 v2）。
     b1 尾段桥: 判据输出常数 c₀ = t⁷/2⁸ = 1/71663616 的 real 层 μ 证书
       （|π−q| ≥ c₀/q⁸ 率面形·ck_alpha Q 载体·Section Hypothesis 接口槽
       承载·P2③ 将供给）经常数折半换算
       （C₀ := 1/10⁹，折半链 Q 算术 vm_compute 双枚验证）与
       leibsep_metric_pi_transport 复用（Local.LW0LeibSeparation·签名
       probe 实测: ∀q eps, QltT 0 eps -> ∃Nr, ∀m≥Nr,
       |projT1(real_metric π (const q)) m − |xL m − q|| < eps），
       出 lw1m_dist_pt 距离形——正数域半出口双载体:
       nat-α 载体与 ck_alpha Q 载体，
       两载体经 piu_zz_nat_hpow_qpow 桥 + apply 型 transport 换形。
     b2 非正半域件: q ≤ 0 域无条件——π>3 列级下界见证
       （lw0m_xL 40 − lw0m_e 40 > 3·vm_compute 字面）+ lw0m_tail_bounded_pi
       尾控 + 阈值松弛（ck_alpha ≤ C₀ ≤ c₀/2 < 3）。
   桥核心账: real_lt 给 eps>0 与尾段 P > 2d+eps（P=real 度量投影位），
     transport 给尾段 |P−X|<eps（X=|xL k−q|）⟹ X > 2d ≥ d（d>0）——
     折半常数 2d 吸收 transport 误差，纯线性账零三角件。
   依赖: piu_zz_bridge_real（基件供给源·合并裁断①吸收位）、
     S01_BaseRing、S02_CauchyComplete、S03_QExp、S10_KVQuantTrig、
     PiEnvelope（QltT'/QltT 互转）、LW0MLicBridge（lw0m_xL/lw0m_tail_bounded_pi）、
     LW1PiMeasure（lw1m_dist_pt/lw1m_height/lw1m_hpow/lw1m_snq_pos）、
     Local.LW0LeibSeparation（leibsep_metric_pi_transport）、
     piu1932_tight_bound_instantiated（ck_alpha 与 Q 桥型引理）、
     piu_mu_criterion（piu_mu_Qinv_nonneg 复用）。
   构造性注记: 零未证假设出口；接口槽
     （piu_zz_Hmu_criterion）系 Section 内显式 Hypothesis·Set 承载
     （real_lt=sigT），出节即定理显式参数非公理——红线律口径
     （宅风判例=K01 mock 同款）；证内 Q 线性不等式步以 lia/lra 承担
     （辅助代数步·stdlib 例外用法·piu1904/piu_mu_criterion 同口径于此
     申报）；数值见证（π>3 列级见证 Nw=40 与折半链两枚）全部
     vm_compute 字面闭合零承认。
   注记: halving_rate_rel 结论 Qle→QleT'（qleT 系载体）；
     piu_zz_bridge_real 新形四处迁移位（abs_lt_upper QltT 出口/nat_hpow_qpow QeqT 出口/
     hpow_ge1 bool-Id 出口 ×2）。
   编译配方: rocq c -native-compiler no -q -Q . "" piu_zz_bridge_rateslot.v
     （Rocq 9.1.0·COQLIB/ROCQLIB 全字面双导出·cpu_guard v3 包裹·
     env.sh+unset COQLIB ROCQLIB）
   ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith Lia ZArith.
From Stdlib Require Import Lqa.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW1PiMeasure.
Require Import Local.LW0LeibSeparation.
Require Import piu1932_tight_bound_instantiated.
Require Import piu_mu_criterion.
(* 基件供给源（合并裁断①吸收位）: 折半链/桥基五件/Nw/pi3_witness/
   bridge_nonpos/thresh_nat_pos/natQ_mul_q/nat_hpow_qpow/
   ck_alpha_nat_transport 等十八件基件由其供给，本文件不再重复定义 *)
Require Import piu_zz_bridge_real.

(* ============================================================ *)
(* §1 桥核心 v2: real 证书（预结合折半阈值）→ lw1m_dist_pt              *)
(* （v1 core 广化: 增 d2 参与换算前提 QleT' d d2——(2·C₀)/nat 与         *)
(*   2·(C₀/nat) 的 Qeq 接续位·N01 处方②）                               *)
(* ============================================================ *)

Lemma piu_zz_tail_bridge_core_v2 : forall (q d d2 : Q),
  QltT 0 d ->
  QleT' d d2 ->
  real_lt (real_const d2)
          (real_metric real_pi_geom (real_const q)) ->
  lw1m_dist_pt q d.
Proof.
  intros q d d2 Hd Hdle [eps [Heps [N HN]]].
  destruct (leibsep_metric_pi_transport q eps Heps) as [Nr HNr].
  exists (Nat.max N Nr). intros k Hk.
  assert (HkN : NatLe N k).
  { apply NatLe_lift.
    pose proof (NatLe_drop (Nat.max N Nr) k Hk) as Hmax.
    apply (Nat.le_trans N (Nat.max N Nr) k (Nat.le_max_l N Nr) Hmax). }
  assert (HkNr : NatLe Nr k).
  { apply NatLe_lift.
    pose proof (NatLe_drop (Nat.max N Nr) k Hk) as Hmax.
    apply (Nat.le_trans Nr (Nat.max N Nr) k (Nat.le_max_r N Nr) Hmax). }
  pose proof (HN k HkN) as Hlow.
  cbn [projT1 real_const] in Hlow.
  pose proof (HNr k HkNr) as Htr.
  pose proof (QltT_to_Qlt _ _ (piu_zz_abs_lt_upper _ _ Htr)) as Hup.
  pose proof (QltT_to_Qlt _ _ Hlow) as HlowQ.
  pose proof (QltT_to_Qlt _ _ Hd) as HdQ.
  pose proof (QleT'_to_Qle _ _ Hdle) as HdleQ.
  set (P := projT1 (real_metric real_pi_geom (real_const q)) k) in *.
  set (X := Qabs ((lw0m_xL k - q)%Q)) in *.
  apply Qlt_to_QltT'.
  lra.
Qed.

(* ============================================================ *)
(* §2 折半率面关系（v2 预结合形·N01 处方）: (2·C₀)/nat h⁸ ≤ c₀/q_pow h⁸  *)
(* （率面阈值换算·load-bearing；Qmult_le_compat_r 直消·全消 Qmult_assoc） *)
(* ============================================================ *)

Lemma piu_zz_halving_rate_rel : forall q : Q,
  QleT' ((((2 # 1) * piu_zz_C0) / (Z.of_nat (lw1m_hpow q 8) # 1))%Q)
        (piu1932_ck_alpha piu_zz_c0_criterion 8 q).
Proof.
  intros q.
  apply piu1932_qle_to_qleT'.
  unfold piu1932_ck_alpha.
  pose proof (qeqT_imp_qeq _ _ (piu_zz_nat_hpow_qpow q 8)) as Hnp.
  rewrite <- Hnp.
  unfold Qdiv.
  apply Qmult_le_compat_r.
  - pose proof (QltT_to_Qlt _ _ piu_zz_halving_chain) as Hhalf.
    apply Qlt_le_weak. exact Hhalf.
  - pose proof (piu_zz_hpow_ge1 q 8) as Hh.
    apply Nat.leb_le in Hh.
    pose proof (piu_zz_znat1_pos (lw1m_hpow q 8) Hh) as Hden.
    pose proof (QltT'_to_Qlt _ _ Hden) as HdenQ.
    destruct (piu_mu_Qinv_nonneg _ HdenQ) as [Hnn]. exact Hnn.
Qed.

Section BridgeRealV2.

(* real 层 μ 证书接口槽（|π−q| ≥ c₀/q⁸ 率面形·c₀=1/71663616 判据输出
   常数·ck_alpha Q 载体=G01 T 终端同族; P2③ τ 面 + P1 判据件链实装后
   整槽替换） *)
Hypothesis piu_zz_Hmu_criterion : forall q : Q, (0 < q)%Q ->
  real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
          (real_metric real_pi_geom (real_const q)).

(* 折半松弛: c₀/q⁸ 率面证书 ⟹ (2·C₀)/h⁸ 预结合形证书（v2·N01 处方;
   D/E 步骤原子化防 lra 除法墙·Qeq 接续由 core 之 QleT' d d2 前提吸收） *)
Lemma piu_zz_cert_relax_v2 : forall q : Q, (0 < q)%Q ->
  real_lt (real_const ((((2 # 1) * piu_zz_C0) / (Z.of_nat (lw1m_hpow q 8) # 1))%Q)%Q)
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros q Hq.
  pose proof (piu_zz_halving_rate_rel q) as Hrel.
  pose proof (QleT'_to_Qle _ _ Hrel) as HrelQ.
  assert (Hcert := piu_zz_Hmu_criterion q Hq).
  destruct Hcert as [eps [Heps [N HN]]].
  set (E := piu1932_ck_alpha piu_zz_c0_criterion 8 q) in *.
  set (D := (((2 # 1) * piu_zz_C0) / (Z.of_nat (lw1m_hpow q 8) # 1))%Q) in *.
  exists ((eps + (E - D)%Q)%Q).
  split.
  - apply Qlt_to_QltT'.
    pose proof (QltT_to_Qlt _ _ Heps) as HepsQ.
    lra.
  - exists N. intros n Hn.
    pose proof (HN n Hn) as Hlow.
    cbn [projT1 real_const] in Hlow.
    cbn [projT1 real_const].
    apply Qlt_to_QltT'.
    pose proof (QltT_to_Qlt _ _ Hlow) as HlowQ.
    lra.
Qed.

(* 正数域半出口：nat-α 载体（v2 率面槽前提） *)
Theorem piu_zz_bridge_pos_nat_v2 : forall q : Q, (0 < q)%Q ->
  lw1m_dist_pt q ((piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q).
Proof.
  intros q Hq.
  apply (piu_zz_tail_bridge_core_v2 q
           (piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q
           (((2 # 1) * piu_zz_C0) / (Z.of_nat (lw1m_hpow q 8) # 1))%Q).
  - apply piu_zz_thresh_nat_pos. exact Hq.
  - (* 换算前提 d ≤ d2: C₀/nat ≤ (2·C₀)/nat（Qmult_le_compat_r 直消·预结合接续） *)
    apply piu1932_qle_to_qleT'.
    unfold Qdiv.
    apply Qmult_le_compat_r.
    + unfold piu_zz_C0, Qmult, Qle. cbn [Qnum Qden]. lia.
    + pose proof (piu_zz_hpow_ge1 q 8) as Hh.
      apply Nat.leb_le in Hh.
      pose proof (piu_zz_znat1_pos (lw1m_hpow q 8) Hh) as Hden.
      destruct (piu_mu_Qinv_nonneg (Z.of_nat (lw1m_hpow q 8) # 1)%Q
        (QltT'_to_Qlt _ _ Hden)) as [Hnn]. exact Hnn.
  - apply (piu_zz_cert_relax_v2 q Hq).
Qed.

End BridgeRealV2.

(* —— T 终端供体形出口（G01 总图对表·v2 率面槽前提） —— *)

(* 正数域半·ck_alpha Q 载体（G01 §1.2 pos_half 形） *)
Theorem piu_zz_bridge_pos_v2 :
  (forall q : Q, (0 < q)%Q ->
     real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
             (real_metric real_pi_geom (real_const q))) ->
  forall q : Q, (0 < q)%Q ->
  lw1m_dist_pt q (piu1932_ck_alpha piu_zz_C0 8 q).
Proof.
  intros Hmu q Hq.
  apply (piu_zz_ck_alpha_nat_transport piu_zz_C0 8 q).
  apply (piu_zz_bridge_pos_nat_v2 Hmu q Hq).
Qed.

(* 全域合成（T 终端供体形: ∀q, lw1m_dist_pt q (ck_alpha C₀ 8 q)） *)
Theorem piu_zz_bridge_full_v2 :
  (forall q : Q, (0 < q)%Q ->
     real_lt (real_const (piu1932_ck_alpha piu_zz_c0_criterion 8 q))
             (real_metric real_pi_geom (real_const q))) ->
  forall q : Q, lw1m_dist_pt q (piu1932_ck_alpha piu_zz_C0 8 q).
Proof.
  intros Hmu q. destruct (Qlt_le_dec 0 q) as [Hp | Hn].
  - exact (piu_zz_bridge_pos_v2 Hmu q Hp).
  - apply piu_zz_bridge_nonpos. apply piu1932_qle_to_qleT'. exact Hn.
Qed.

(* ============================================================ *)
(* §5 终检: G4 假设审计 + G3 提取检查                                 *)
(* ============================================================ *)

Print Assumptions piu_zz_halving_chain.
Print Assumptions piu_zz_halving_rate_rel.
Print Assumptions piu_zz_cert_relax_v2.
Print Assumptions piu_zz_tail_bridge_core_v2.
Print Assumptions piu_zz_pi3_witness.
Print Assumptions piu_zz_bridge_nonpos.
Print Assumptions piu_zz_bridge_pos_nat_v2.
Print Assumptions piu_zz_ck_alpha_nat_transport.
Print Assumptions piu_zz_bridge_pos_v2.
Print Assumptions piu_zz_bridge_full_v2.

(* G3: 桥含 Q 算术数据面（折半链/阈值/见证常数）——提取 val 面核 Obj.magic
   （正名件提取凭证=piu_zz_bridge_rateslot_ext.ml/.mli·提取名位沿袭） *)
Extraction "piu_zz_bridge_rateslot_ext" piu_zz_bridge_full_v2 piu_zz_bridge_pos_nat_v2
  piu_zz_bridge_nonpos piu_zz_cert_relax_v2 piu_zz_halving_rate_rel.
