(* ============================================================
   模块名: piu_zz_bridge_real
   数学使命: real 层 μ 证书 → lw1m_dist_pt 距离形尾段桥（b1+b2 合并件）。
     b1 尾段桥: 判据输出常数 c₀ = t⁷/2⁸ = 1/71663616 的 real 层 μ 证书
       （Section Hypothesis 接口槽承载·P2③ 将供给）经常数折半换算
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
   依赖: S01_BaseRing、S02_CauchyComplete、S03_QExp、S10_KVQuantTrig、
     PiEnvelope（QltT'/QltT 互转）、LW0MLicBridge（lw0m_xL/lw0m_tail_bounded_pi）、
     LW1PiMeasure（lw1m_dist_pt/lw1m_height/lw1m_hpow/lw1m_snq_pos）、
     Local.LW0LeibSeparation（leibsep_metric_pi_transport）、
     piu1932_tight_bound_instantiated（ck_alpha 与 Q 桥型引理）、
     piu_mu_criterion（piu_mu_Qinv_nonneg 复用）。
   构造性注记: 零 Axiom/Admitted/Parameter/Conjecture/Abort；接口槽
     （piu_zz_Hmu_criterion）系 Section 内显式 Hypothesis·Set 承载
     （real_lt=sigT），出节即定理显式参数非公理——红线律口径
     （宅风判例=K01 mock 同款）；证内 Q 线性不等式步以 lia/lra 承担
     （辅助代数步·stdlib 例外用法·piu1904/piu_mu_criterion 同口径于此
     申报）；数值见证（π>3 列级见证 Nw=40 与折半链两枚）全部
     vm_compute 字面闭合零承认。
   编译配方: rocq c -native-compiler no -q -Q . "" piu_zz_bridge_real.v
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

(* ============================================================ *)
(* §0 统一常数（折半换算前后两端）                         *)
(* ============================================================ *)

(* 判据输出常数: c₀ = t⁷/2⁸ = 1/(6⁷·2⁸) = 1/71663616 *)
Definition piu_zz_c0_criterion : Q := (1 # 71663616)%Q.

(* 桥出口常数: C₀ = 1/10⁹（折半换算后 dist_pt 位） *)
Definition piu_zz_C0 : Q := (1 # 1000000000)%Q.

(* 数值样点一（G01 债务账字面恒等: c₀ = t⁷/2⁸ 字面） *)
Example piu_zz_halving_num1 :
  Qeq_bool piu_zz_c0_criterion (1 # (6 ^ 7 * 2 ^ 8))%Q = true.
Proof. vm_compute. reflexivity. Qed.

(* 数值样点二（折半裕度: 2·C₀ < c₀） *)
Example piu_zz_halving_num2 :
  Qlt_bool ((2 # 1) * piu_zz_C0)%Q piu_zz_c0_criterion = true.
Proof. vm_compute. reflexivity. Qed.

(* 折半链换算（load-bearing）: 2·C₀ < c₀ *)
Lemma piu_zz_halving_chain :
  QltT ((2 # 1) * piu_zz_C0)%Q piu_zz_c0_criterion.
Proof.
  assert (Hb : Qlt_bool ((2 # 1) * piu_zz_C0)%Q
                         piu_zz_c0_criterion = true)
    by (vm_compute; reflexivity).
  apply Qlt_to_QltT'. apply (proj1 (Z.ltb_lt _ _)). exact Hb.
Qed.

Lemma piu_zz_C0_pos : QltT' 0 piu_zz_C0.
Proof. apply Qlt_to_QltT'. unfold piu_zz_C0, Qlt. cbn [Qnum Qden]. lia. Qed.

(* ============================================================ *)
(* §1 桥基小件（abs 提取/除法松弛/幂下界）                            *)
(* ============================================================ *)

(* |u| < eps ⟹ u < eps（下界向直接引用 S02 现成 q_abs_gt_neg·
   QltT 包装件禁 destruct 改 pose proof；
   结论消解为 QltT Set 承载——S02 Qlt_bool bool-Id 载体，与前提同形） *)
Lemma piu_zz_abs_lt_upper : forall u eps : Q,
  QltT (Qabs u) eps -> QltT u eps.
Proof.
  intros u eps H.
  pose proof (QltT_to_Qlt _ _ H) as Hlt.
  destruct (Qlt_le_dec u 0) as [Hult | Huge0].
  - assert (Habs : Qabs u == - u)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hult).
    rewrite Habs in Hlt. apply Qlt_to_QltT. lra.
  - assert (Habs : Qabs u == u) by (apply Qabs_pos; exact Huge0).
    rewrite Habs in Hlt. apply Qlt_to_QltT. exact Hlt.
Qed.

(* 除法松弛: 0 ≤ C₀ ∧ 1 ≤ p ⟹ C₀/p ≤ C₀
   （stdlib 无 Qinv_le·改走 1·(/p) ≤ p·(/p) == 1 链） *)
Lemma piu_zz_divQ_le_num : forall C0 p : Q,
  QleT' 0 C0 -> QleT' 1 p -> QleT' (C0 / p) C0.
Proof.
  intros C0 p H0 Hp.
  pose proof (QleT'_to_Qle _ _ Hp) as HpQ.
  assert (Hplt : Qlt 0 p).
  { apply (Qlt_le_trans 0 1 p).
    - unfold Qlt. cbn [Qnum Qden]. lia.
    - exact HpQ. }
  assert (Hinv0 : Qle 0 (/ p)%Q)
    by (destruct (piu_mu_Qinv_nonneg p Hplt) as [Hnn]; exact Hnn).
  assert (Hinv1 : Qle (/ p)%Q 1).
  { assert (Hprod : (p * / p)%Q == 1).
    { apply Qmult_inv_r.
      intro Hz. apply (not_eq_sym (Qlt_not_eq 0 p Hplt)). exact Hz. }
    apply (Qle_trans _ ((1 * / p)%Q)).
    - rewrite Qmult_1_l. apply Qle_refl.
    - apply (Qle_trans _ ((p * / p)%Q)).
      + apply Qmult_le_compat_r.
        * exact HpQ.
        * exact Hinv0.
      + rewrite Hprod. apply Qle_refl. }
  apply piu1932_qle_to_qleT'.
  apply (Qle_trans _ (C0 * 1)%Q).
  - unfold Qdiv. apply Qmult_le_compat_nonneg.
    + split. exact (QleT'_to_Qle _ _ H0). apply Qle_refl.
    + split. exact Hinv0. exact Hinv1.
  - rewrite Qmult_1_r. apply Qle_refl.
Qed.

(* q_pow 下界: 1 ≤ h ⟹ 1 ≤ q_pow h n（结论消解为 QleT' bool-Id Set 承载） *)
Lemma piu_zz_qpow_ge1 : forall (h : Q) (n : nat),
  Qle 1 h -> QleT' 1 (q_pow h n).
Proof.
  intros h n Hh.
  assert (Hcore : Qle 1 (q_pow h n)).
  { assert (H01 : Qle 0 1) by (unfold Qle; cbn [Qnum Qden]; lia).
    induction n as [|n IH].
    - apply Qle_refl.
    - cbn [q_pow].
      apply (Qle_trans _ (1 * q_pow h n)%Q).
      + rewrite Qmult_1_l. exact IH.
      + apply Qmult_le_compat_nonneg.
        * split. exact H01. exact Hh.
        * split.
          -- apply (Qle_trans _ 1). exact H01. exact IH.
          -- apply Qle_refl. }
  apply Qle_to_QleT'. exact Hcore.
Qed.

(* lw1m_hpow nat 下界（阈值正性用；结论消解为 Nat.leb bool-Id Set 承载） *)
Lemma piu_zz_hpow_ge1 : forall (q : Q) (a : nat),
  Nat.leb 1 (lw1m_hpow q a) = true.
Proof.
  intros q a. apply Nat.leb_le.
  induction a as [|a IH].
  - cbn [lw1m_hpow]. lia.
  - cbn [lw1m_hpow].
    pose proof (NatLe_drop 2 (lw1m_height q) (lw1m_height_ge2 q)) as H2.
    pose proof (Nat.mul_le_mono 2 (lw1m_height q) 1 (lw1m_hpow q a) H2 IH) as Hm.
    lia.
Qed.

Lemma piu_zz_znat1_pos : forall n : nat,
  (1 <= n)%nat -> QltT' 0 ((Z.of_nat n # 1)%Q).
Proof.
  intros n Hn. apply Qlt_to_QltT'. unfold Qlt. cbn [Qnum Qden]. lia.
Qed.

(* ============================================================ *)
(* §2 b1 核心: real 证书（折半后阈值）→ lw1m_dist_pt                  *)
(* ============================================================ *)

Lemma piu_zz_tail_bridge_core : forall (q d : Q),
  QltT 0 d ->
  real_lt (real_const ((2 # 1) * d)%Q)
          (real_metric real_pi_geom (real_const q)) ->
  lw1m_dist_pt q d.
Proof.
  intros q d Hd [eps [Heps [N HN]]].
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
  set (P := projT1 (real_metric real_pi_geom (real_const q)) k) in *.
  set (X := Qabs ((lw0m_xL k - q)%Q)) in *.
  apply Qlt_to_QltT'.
  lra.
Qed.

(* ============================================================ *)
(* §3 b2 非正半域件（无条件·全 top-level）                            *)
(* ============================================================ *)

(* π>3 列级下界见证（lw0m_xL 40 − lw0m_e 40 的 vm_compute 字面） *)
Definition piu_zz_Nw : nat := 40%nat.

Lemma piu_zz_pi3_witness :
  QltT 3 ((lw0m_xL piu_zz_Nw - lw0m_e piu_zz_Nw)%Q).
Proof.
  assert (Hb : Qlt_bool 3 ((lw0m_xL piu_zz_Nw - lw0m_e piu_zz_Nw)%Q)
                 = true) by (vm_compute; reflexivity).
  apply Qlt_to_QltT'. apply (proj1 (Z.ltb_lt _ _)). exact Hb.
Qed.

Theorem piu_zz_bridge_nonpos : forall q : Q,
  QleT' q 0 -> lw1m_dist_pt q (piu1932_ck_alpha piu_zz_C0 8 q).
Proof.
  intros q Hq.
  pose proof (QleT'_to_Qle _ _ Hq) as Hq0.
  (* 阈值松弛: ck_alpha ≤ C₀ < 3 *)
  assert (HDle : QleT' (piu1932_ck_alpha piu_zz_C0 8 q) piu_zz_C0).
  { unfold piu1932_ck_alpha.
    apply (piu_zz_divQ_le_num piu_zz_C0
             (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) 8)).
    - exact piu_zz_C0_pos.
    - apply piu_zz_qpow_ge1.
      pose proof (NatLe_drop 2 (lw1m_height q) (lw1m_height_ge2 q)) as H2.
      unfold Qle. cbn [Qnum Qden]. lia. }
  pose proof (QleT'_to_Qle _ _ HDle) as HDleQ.
  assert (HC03 : Qlt piu_zz_C0 3).
  { unfold piu_zz_C0, Qlt. cbn [Qnum Qden]. lia. }
  assert (Hthr : Qlt (piu1932_ck_alpha piu_zz_C0 8 q) 3).
  { apply (Qle_lt_trans _ piu_zz_C0 3).
    - exact HDleQ.
    - exact HC03. }
  (* 尾段列下界: k ≥ Nw ⟹ xL k > xL Nw − e Nw > 3 *)
  exists piu_zz_Nw. intros k Hk.
  assert (HNw1 : (1 <= piu_zz_Nw)%nat) by (unfold piu_zz_Nw; lia).
  assert (Hkge : (piu_zz_Nw <= k)%nat).
  { pose proof (NatLe_drop piu_zz_Nw k Hk) as Hk0. lia. }
  pose proof (lw0m_tail_bounded_pi piu_zz_Nw k HNw1 Hkge) as Hwin.
  pose proof (QltT_to_Qlt _ _ Hwin) as HwinQ.
  assert (Hepos : Qlt 0 (lw0m_e piu_zz_Nw)).
  { assert (Hb : Qlt_bool 0 (lw0m_e piu_zz_Nw) = true)
      by (vm_compute; reflexivity).
    apply (proj1 (Z.ltb_lt _ _)). exact Hb. }
  pose proof (q_abs_gt_neg (lw0m_xL k - lw0m_xL piu_zz_Nw)%Q
                (lw0m_e piu_zz_Nw) Hepos HwinQ) as HwinL.
  pose proof (QltT_to_Qlt _ _ piu_zz_pi3_witness) as Hwit.
  assert (Hxk : Qlt 3 (lw0m_xL k)) by lra.
  apply Qlt_to_QltT'.
  apply (Qlt_trans _ 3).
  - exact Hthr.
  - assert (Habs : (Qabs (lw0m_xL k - q))%Q == (lw0m_xL k - q)%Q)
      by (apply Qabs_pos; lra).
    rewrite Habs. lra.
Qed.

(* ============================================================ *)
(* §4 b1 接口槽与正数域半（Section 出节显式参数·红线律口径）        *)
(* ============================================================ *)

Section BridgeReal.

(* real 层 μ 证书接口槽（|π−q| ≥ c₀/q⁸ 形·c₀=1/71663616 判据输出常数;
   P2③ τ 面 + P1 判据件经 dval 实装后整槽替换） *)
Hypothesis piu_zz_Hmu_criterion : forall q : Q, (0 < q)%Q ->
  real_lt (real_const piu_zz_c0_criterion)
          (real_metric real_pi_geom (real_const q)).

(* 折半松弛: c₀ 证书 ⟹ 2·(C₀/h⁸) 证书（D 步骤原子化防 lra 除法墙） *)
Lemma piu_zz_cert_relax : forall q : Q, (0 < q)%Q ->
  real_lt (real_const ((2 # 1) * (piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q)%Q)
          (real_metric real_pi_geom (real_const q)).
Proof.
  intros q Hq.
  assert (HDle : QleT' ((piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q)
                       piu_zz_C0).
  { apply (piu_zz_divQ_le_num piu_zz_C0
             ((Z.of_nat (lw1m_hpow q 8) # 1)%Q)).
    - exact piu_zz_C0_pos.
    - apply piu1932_qle_to_qleT'.
      pose proof (piu_zz_hpow_ge1 q 8) as Hh1.
      apply Nat.leb_le in Hh1.
      unfold Qle. cbn [Qnum Qden]. lia. }
  pose proof (QleT'_to_Qle _ _ HDle) as HDleQ.
  pose proof (QltT_to_Qlt _ _ piu_zz_halving_chain) as HhalfQ.
  remember ((piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q) as D eqn:HDdef.
  clear HDdef HDle.
  destruct (piu_zz_Hmu_criterion q Hq) as [eps [Heps [N HN]]].
  exists ((eps + (piu_zz_c0_criterion - (2 # 1) * D)%Q)%Q).
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

(* 阈值正性（nat-α 载体） *)
Lemma piu_zz_thresh_nat_pos : forall q : Q, (0 < q)%Q ->
  QltT 0 ((piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q).
Proof.
  intros q Hq. apply piu1932_div_pos.
  - exact (QltT'_to_Qlt _ _ piu_zz_C0_pos).
  - apply piu_zz_znat1_pos.
    apply Nat.leb_le.
    apply piu_zz_hpow_ge1.
Qed.

(* 正数域半出口：nat-α 载体 *)
Theorem piu_zz_bridge_pos_nat : forall q : Q, (0 < q)%Q ->
  lw1m_dist_pt q ((piu_zz_C0 / (Z.of_nat (lw1m_hpow q 8) # 1))%Q).
Proof.
  intros q Hq.
  apply (piu_zz_tail_bridge_core q).
  - apply piu_zz_thresh_nat_pos. exact Hq.
  - apply (piu_zz_cert_relax q Hq).
Qed.

End BridgeReal.

(* —— 载体换形（E01 §2.2 桥 + K01 判例 apply 型 transport·誊抄更名） —— *)

Lemma piu_zz_natQ_mul_q : forall m n : nat,
  QeqT (Z.of_nat (m * n) # 1)%Q
       ((Z.of_nat m # 1)%Q * (Z.of_nat n # 1)%Q).
Proof.
  intros m n. apply qeq_imp_qeqT. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* E01 §2.2 语句面逐字（更名 piu_zz_ 前缀防 P3 正件 Require 撞名；
   结论消解为 QeqT Set 承载——S02 Qcompare bool-Id 载体，
   使用位经 qeqT_imp_qeq 还原 == 面） *)
Lemma piu_zz_nat_hpow_qpow : forall (q : Q) (a : nat),
  QeqT (Z.of_nat (lw1m_hpow q a) # 1)%Q
       (q_pow ((Z.of_nat (lw1m_height q) # 1)%Q) a).
Proof.
  intros q a. apply qeq_imp_qeqT.
  induction a as [|a IH].
  - cbn [lw1m_hpow q_pow]. reflexivity.
  - cbn [lw1m_hpow q_pow].
    pose proof (qeqT_imp_qeq _ _ (piu_zz_natQ_mul_q (lw1m_height q)
                  (lw1m_hpow q a))) as Hmul.
    rewrite Hmul. rewrite IH. reflexivity.
Qed.

(* K01 判例 apply 型 transport（_probe_routeB_mock 绿证工艺誊抄） *)
Lemma piu_zz_ck_alpha_nat_transport : forall (C0 : Q) (a : nat) (q : Q),
  lw1m_dist_pt q ((C0 / (Z.of_nat (lw1m_hpow q a) # 1))%Q) ->
  lw1m_dist_pt q (piu1932_ck_alpha C0 a q).
Proof.
  intros C0 a q Hpt. destruct Hpt as [N HN].
  apply (existT _ N). intros k Hk. apply Qlt_to_QltT'.
  apply (Qle_lt_trans (piu1932_ck_alpha C0 a q)
                      (C0 / (Z.of_nat (lw1m_hpow q a) # 1))%Q
                      (Qabs (lw0m_xL k - q))).
  - unfold piu1932_ck_alpha.
    pose proof (qeqT_imp_qeq _ _ (piu_zz_nat_hpow_qpow q a)) as Hnp.
    rewrite <- Hnp.
    apply Qle_refl.
  - exact (QltT'_to_Qlt _ _ (HN k Hk)).
Qed.

(* —— T 终端供体形出口（G01 总图对表） —— *)

(* 正数域半·ck_alpha Q 载体（G01 §1.2 pos_half 形） *)
Theorem piu_zz_bridge_pos :
  (forall q : Q, (0 < q)%Q ->
     real_lt (real_const piu_zz_c0_criterion)
             (real_metric real_pi_geom (real_const q))) ->
  forall q : Q, (0 < q)%Q ->
  lw1m_dist_pt q (piu1932_ck_alpha piu_zz_C0 8 q).
Proof.
  intros Hmu q Hq.
  apply (piu_zz_ck_alpha_nat_transport piu_zz_C0 8 q).
  apply (piu_zz_bridge_pos_nat Hmu q Hq).
Qed.

(* 全域合成（T 终端供体形: ∀q, lw1m_dist_pt q (ck_alpha C₀ 8 q)） *)
Theorem piu_zz_bridge_full :
  (forall q : Q, (0 < q)%Q ->
     real_lt (real_const piu_zz_c0_criterion)
             (real_metric real_pi_geom (real_const q))) ->
  forall q : Q, lw1m_dist_pt q (piu1932_ck_alpha piu_zz_C0 8 q).
Proof.
  intros Hmu q. destruct (Qlt_le_dec 0 q) as [Hp | Hn].
  - exact (piu_zz_bridge_pos Hmu q Hp).
  - apply piu_zz_bridge_nonpos. apply piu1932_qle_to_qleT'. exact Hn.
Qed.

(* ============================================================ *)
(* §5 终检: G4 假设审计 + G3 提取检查                                 *)
(* ============================================================ *)

Print Assumptions piu_zz_halving_chain.
Print Assumptions piu_zz_cert_relax.
Print Assumptions piu_zz_tail_bridge_core.
Print Assumptions piu_zz_pi3_witness.
Print Assumptions piu_zz_bridge_nonpos.
Print Assumptions piu_zz_bridge_pos_nat.
Print Assumptions piu_zz_ck_alpha_nat_transport.
Print Assumptions piu_zz_bridge_pos.
Print Assumptions piu_zz_bridge_full.

(* G3: 桥含 Q 算术数据面（折半链/阈值/见证常数）——提取 val 面核 Obj.magic *)
Extraction "piu_zz_bridge_ext" piu_zz_bridge_full piu_zz_bridge_pos_nat
  piu_zz_bridge_nonpos piu_zz_cert_relax.
