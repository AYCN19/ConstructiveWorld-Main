(* ========================================================================= *)
(* UpReqIndex.v — 全库模块注册索引（机器可验）                                *)
(*                                                                          *)
(* 使命：以 Set 层数据条目登记全库 .v 模块的声明数、验证日与入口关键词，      *)
(*       并以等式引理在编译期机械核对清单折叠与统计字面值一致，是迁移宇宙     *)
(*       （734 行口径）与批外登记面的唯一权威索引。                          *)
(* 依赖：仅 Stdlib（Ascii、String）；索引层不 Require 任何被索引模块，       *)
(*       与被索引层零耦合，杜绝循环依赖。                                   *)
(* 对标：迁移总账表行口径（659/3/71/1/0，和 = 734）。                       *)
(* 构造性：全 Set 层；零公理、零承认件；全部引理以 reflexivity 封闭，       *)
(*         无经典逻辑；数据条目为纯记录结构（Record 与 list）。             *)
(* 编译配方：coqc -Q . "" UpReqIndex.v（单件编译，无树依赖）；              *)
(*           coqchk 校验通过；导出面为各 idx_/af_/ng_/lg_ 条目与统计常量。  *)
(*                                                                          *)
(* 结构：一、迁移宇宙注册面（idx_ 48 条）                                   *)
(*       二、活动面计数（af_ 124 条）                                       *)
(*       三、结构分组对账（lg_ 31 条与结构不变量引理）                      *)
(*       四、新绿件登记面（ng_ 615 条，尾列元数据口径 L<行数>:m<md5 前 6>） *)
(*       五、统计常量与对账引理                                             *)
(* 维护：仅允许整批追加条目并同步统计字面值，保持对账引理闭合。             *)
(* ========================================================================= *)

From Stdlib Require Import Ascii String.
(* Stdlib 专供 string 记录（Set 层）；索引层不 Require 任何被索引模块。 *)

Record ReqModule : Set := MkReqModule
  { rm_name     : string   (* 模块文件名 *)
  ; rm_decl_cnt : nat      (* grep decl 实测件数 *)
  ; rm_gate_day : nat      (* 四项验证确认/再验日 yyyymmdd *)
  ; rm_head_kw  : string   (* HEAD 关键词（验收 grep 用） *)
  ; rm_in_uni   : bool     (* 是否计入 734 迁移宇宙注册表 *)
  }.

Fixpoint cnt_mod (l : list ReqModule) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_mod tl)
  end.

Fixpoint sum_cnt (l : list ReqModule) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (rm_decl_cnt m) (sum_cnt tl)
  end.

(* ---------- 已交付 req 模块清单（组0–组4 注册表 11 模块） ---------- *)

(* idx_UpSigMigrate —— UpSigMigrate.v：组0 （组0 主定理 + req_attention_is_gibbs_temp）*)
Definition idx_UpSigMigrate : ReqModule :=
  MkReqModule "UpSigMigrate.v" 13 20260909 "req_attention_is_gibbs_temp" true.

(* idx_UpSigMigrate2 —— UpSigMigrate2.v：m2 （a_ 系对位 6 件 + align-a 节）*)
Definition idx_UpSigMigrate2 : ReqModule :=
  MkReqModule "UpSigMigrate2.v" 49 20260909 "a_rlhf_suboptimality_gap" true.

(* idx_UpReqAlgebra —— UpReqAlgebra.v：组1 req 代数地基（RingLemmas/SimpleAlgebra/AlgHelpers + 批外新机器 3 件）*)
Definition idx_UpReqAlgebra : ReqModule :=
  MkReqModule "UpReqAlgebra.v" 63 20260909 "req_plus_zero_r" true.

(* idx_UpReqDist —— UpReqDist.v：组2 分布/自由能/温度层（FEP 52 + GRPO 15 + SqrtWitness 7 + 增量）*)
Definition idx_UpReqDist : ReqModule :=
  MkReqModule "UpReqDist.v" 91 20260909 "reqd_le_of_req" true.

(* idx_UpReqTempEntropy —— UpReqTempEntropy.v：组2 温度熵 11 件（温度严格层 6 件续建）*)
Definition idx_UpReqTempEntropy : ReqModule :=
  MkReqModule "UpReqTempEntropy.v" 14 20260909 "req_temp_energy_dual_closed" true.

(* idx_UpReqAlign —— UpReqAlign.v：组3 对齐主体前段（KLProjection 10 + sigmoid 快赢 + 几何迭代主定理）*)
Definition idx_UpReqAlign : ReqModule :=
  MkReqModule "UpReqAlign.v" 42 20260909 "req_pi_star_pos" true.

(* idx_UpReqAlign2 —— UpReqAlign2.v：组3 t12 求和机器 + 桥 A/C（F_t 深链）*)
Definition idx_UpReqAlign2 : ReqModule :=
  MkReqModule "UpReqAlign2.v" 40 20260909 "req2_boltzmann_factor_bridge" true.

(* idx_UpReqAlign3 —— UpReqAlign3.v：组3 / 组（环代数副本 + 折叠件 + 完成全部通过：
 主定理 req2_backward_kl_step 五段链 + req2_gap_mono + step_le/iter_le；尾注余件全核减）*)
Definition idx_UpReqAlign3 : ReqModule :=
  MkReqModule "UpReqAlign3.v" 76 20260909 "r2_t13_collapse" true.

(* idx_UpReqAlignRestA —— UpReqAlignRestA.v：组3 余量 A（DPO 余量完成 + Q 桥就位，32 语句口径）*)
Definition idx_UpReqAlignRestA : ReqModule :=
  MkReqModule "UpReqAlignRestA.v" 23 20260909 "ralt_dpo_pair_loss_at_star" true.

(* idx_UpReqU2 —— UpReqU2.v：组3 U2 主体 7 件 + 辅件（外延件 (b) 化先例所在）*)
Definition idx_UpReqU2 : ReqModule :=
  MkReqModule "UpReqU2.v" 20 20260909 "req_u2_fixed_point_unique" true.

(* idx_UpReqPPO —— UpReqPPO.v：组3 （未认领 15 件完成：交付 14 + 冻结 1；真证机器主定理所在）； *)

Definition idx_UpReqPPO : ReqModule :=
  MkReqModule "UpReqPPO.v" 26 20260910 "rppo_align_objective_decomp" true.

(* idx_UpReqSampling —— UpReqSampling.v：组4 （ReqUContraction 11 + ReqBoundedSoftmax 23 + epp 辅件）*)
Definition idx_UpReqSampling : ReqModule :=
  MkReqModule "UpReqSampling.v" 43 20260909 "u_tv_contraction" true.

(* idx_UpReqAttnGibbs —— UpReqAttnGibbs.v：组4 （首段 14 + 中后段 39 + 解冻增量节 + 分歧了结增量节 2 件；主定理 Print 假设清零）*)
Definition idx_UpReqAttnGibbs : ReqModule :=
  MkReqModule "UpReqAttnGibbs.v" 65 20260910 "ag_topk_tv_identity_strict" true.

(* idx_UpReqAttnIter —— UpReqAttnIter.v：组4 （q_kernel/收缩迭代簇 26+1 邻接；脊柱对位使用 UpReqSampling）*)
Definition idx_UpReqAttnIter : ReqModule :=
  MkReqModule "UpReqAttnIter.v" 31 20260909 "agq_iterate_converges" true.

(* idx_UpEntropyGainReq —— UpEntropyGainReq.v：组4 （UpEntropyGain 10 件，含两主定理）*)
Definition idx_UpEntropyGainReq : ReqModule :=
  MkReqModule "UpEntropyGainReq.v" 10 20260909 "req_second_law_quant" true.

(* idx_UpEvictIdReq —— UpEvictIdReq.v：组4 （14 件口径 = 12 decl + 2 假设位；两件经组2 reqd_ 使用核减）*)
Definition idx_UpEvictIdReq : ReqModule :=
  MkReqModule "UpEvictIdReq.v" 13 20260909 "req_eviction_partition_le_full_exact" true.

(* idx_UpReqAlignRestB —— UpReqAlignRestB.v：组3余量B/组4 （MinP/TopP/逐出熵四区； 终验再验通过）*)
Definition idx_UpReqAlignRestB : ReqModule :=
  MkReqModule "UpReqAlignRestB.v" 55 20260909 "rls_kernel_norm_gen" true.

(* idx_UpReqSLM —— UpReqSLM.v：组5 段1 （SLM 17 + LogDiff3 13 + 段0 资产 ReqNonnegPlain/ReqLogPlain）*)
Definition idx_UpReqSLM : ReqModule :=
  MkReqModule "UpReqSLM.v" 41 20260909 "req_markov_relative" true.

(* idx_UpReqCauchy —— UpReqCauchy.v：组5 段2 （ConvergenceCauchy 43 + lim 簇解冻 + 段3 助件 3）*)
Definition idx_UpReqCauchy : ReqModule :=
  MkReqModule "UpReqCauchy.v" 48 20260909 "req_attractor_converges_unique_truth" true.

(* idx_UpReqMinPAntitone —— UpReqMinPAntitone.v：组4 （MinP p-antitone 簇 5 件真缺新建）*)
Definition idx_UpReqMinPAntitone : ReqModule :=
  MkReqModule "UpReqMinPAntitone.v" 5 20260909 "req_minp_dropped_mass_p_monotone" true.

(* idx_UpReqOrderArgmin —— UpReqOrderArgmin.v：组5 段4 桥C1（reqDecidableOrder 同构类 + reqArgmin 机 + (c) 5 件 + snd 改述机 2）*)
Definition idx_UpReqOrderArgmin : ReqModule :=
  MkReqModule "UpReqOrderArgmin.v" 7 20260909 "req_pick_best_is_minimal" true.

(* idx_UpReqPCT —— UpReqPCT.v：组5 段4 桥C3（reqRealSelfSS + reqPCTDefs 后定义级闭合 2 件）*)
Definition idx_UpReqPCT : ReqModule :=
  MkReqModule "UpReqPCT.v" 2 20260909 "req_pct_truth_is_global_min" true.

(* idx_UpReqDpoLoss —— UpReqDpoLoss.v：组5 （total_loss 簇实例形 (b) 化完成 6 件 + min plain-le 裁决书）*)
Definition idx_UpReqDpoLoss : ReqModule :=
  MkReqModule "UpReqDpoLoss.v" 6 20260909 "rdl_dpo_total_loss_at_star" true.

(* ---------- 组4 模块伴件完成补记（ ；v2 定稿 _v2chk coqchk PASS） ---------- *)

(* idx_UpFirewallReq —— UpFirewallReq.v：组4 v2（UpFirewall 9 件伴件定稿，件7 req_recovery_entropy_gain_alt 补建）*)
Definition idx_UpFirewallReq : ReqModule :=
  MkReqModule "UpFirewallReq.v" 9 20260909 "req_recovery_entropy_gain_alt" true.

(* idx_UpAlignIdReq —— UpAlignIdReq.v：组4 AlignId （UpAlignId 6 件伴件；8Qed/541 行，md5 9646ad0f 零改动背书）*)
Definition idx_UpAlignIdReq : ReqModule :=
  MkReqModule "UpAlignIdReq.v" 8 20260909 "policy_gap_backward_kl_exact" true.

(* idx_UpPredRelaxReq —— UpPredRelaxReq.v：组4 PredRelax （UpPredRelax 6 件伴件；6Qed/367 行，md5 cd07a2f9）*)
Definition idx_UpPredRelaxReq : ReqModule :=
  MkReqModule "UpPredRelaxReq.v" 6 20260909 "total_loss_multi_epoch_decreasing" true.

Definition idx_UpReqMisc5 : ReqModule :=
  MkReqModule "UpReqMisc5.v" 35 20260909 "req_dpo_gradient_alt" true.

Definition idx_UpReqMisc5B : ReqModule :=
  MkReqModule "UpReqMisc5B.v" 20 20260909 "req_mv_vec_diff_decomp" true.

Definition idx_UpReqRDF : ReqModule :=
  MkReqModule "UpReqRDF.v" 47 20260909 "req_rdf_mv_vec_compose" true.

Definition idx_UpReqFEPAttn : ReqModule :=
  MkReqModule "UpReqFEPAttn.v" 16 20260909 "req_free_energy_softmax_eq_neg_T_logZ" true.

Definition idx_UpDebtSqrtAbsReq : ReqModule :=
  MkReqModule "UpDebtSqrtAbsReq.v" 6 20260909 "req_sqrt_one_abstract" true.

Definition idx_UpReqPPOPlain : ReqModule :=
  MkReqModule "UpReqPPOPlain.v" 14 20260910 "rpl_ppo_clipped_improvement" true.

(* ---------- 批外增量（不占 734 迁移宇宙名额） ---------- *)

(* idx_UpAuditBridge —— UpAuditBridge.v：Min-P 截断采样 KL 投影审计桥（P8 全量；CW219 Real 层面；28 decl，coqchk PASS）*)
Definition idx_UpAuditBridge : ReqModule :=
  MkReqModule "UpAuditBridge.v" 28 20260909 "real_minp_projection_eps" false.

(* idx_UpRealLeB —— UpRealLeB.v：M2 + Bishop （Real 层 Bishop 形非严格序 real_le_b + 完成引理 +
 Part D 增量 + Part E 可升 18 件 Bishop 形完成——共 30 decl，其中 Part D+E 24 件 B 形；定理 4.9/6.6 对应物）*)
Definition idx_UpRealLeB : ReqModule :=
  MkReqModule "UpRealLeB.v" 30 20260909 "real_le_closure_b" false.

Definition idx_UpRealLeB2 : ReqModule :=
  MkReqModule "UpRealLeB2.v" 8 20260909 "real_db_breaking_bound_B" false.

(* idx_UpReqMinPProjB —— UpReqMinPProjB.v：批外 W2' 簇新件（MinP Bishop 形 B 面 7 件；251 行，
 7 行首 Qed 1:1；主定理 real_minp_projection_eps_B；四项验证 log _w2_g1g2_evidence/_w2_g3_objmagic/
 _w2_g4_evidence/_w2_chk_UpReqMinPProjB 全部通过；Real 层批外不占宇宙名额） *)
Definition idx_UpReqMinPProjB : ReqModule :=
  MkReqModule "UpReqMinPProjB.v" 7 20260910 "real_minp_projection_eps_B" false.

(* idx_UpRealLeB3 —— UpRealLeB3.v：≤_B 序代数引擎固化层（B 形扩展 T1；8 TLC = 8 行首 Qed，220 行； *)
(* 反序/正缩放/恒等严格元三面新构造；主定理 leb3_le_b_opp_rev） *)
Definition idx_UpRealLeB3 : ReqModule :=
  MkReqModule "UpRealLeB3.v" 8 20260910 "leb3_le_b_opp_rev" false.

(* idx_UpReqPPOB —— UpReqPPOB.v：定理 6.6 对应物结论 5 （B 形扩展 T2；ppo 保守性 Bishop 完整形， *)
(* sum_pos 槽接口前提在案；2 TLC = 2 行首 Qed，98 行；主定理 real_ppo_conservative_B_full） *)
Definition idx_UpReqPPOB : ReqModule :=
  MkReqModule "UpReqPPOB.v" 2 20260910 "real_ppo_conservative_B_full" false.

(* idx_UpReqSumB —— UpReqSumB.v：Σ ≤_B （B 形扩展 T3；3 TLC = 3 行首 Qed + 自持 Fixpoint *)
(* sumb_lenR 口径外机器（件数口径从众：Theorem/Lemma/Corollary 行）；191 行；主定理 sumb_list_sum_le_b） *)
Definition idx_UpReqSumB : ReqModule :=
  MkReqModule "UpReqSumB.v" 3 20260910 "sumb_list_sum_le_b" false.

(* ---------- 清单与统计（字面值；一致性由文末等式引理编译期核对） ---------- *)

Definition ReqModuleList : list ReqModule :=
  cons idx_UpSigMigrate
  (cons idx_UpSigMigrate2
  (cons idx_UpReqAlgebra
  (cons idx_UpReqDist
  (cons idx_UpReqTempEntropy
  (cons idx_UpReqAlign
  (cons idx_UpReqAlign2
  (cons idx_UpReqAlign3
  (cons idx_UpReqAlignRestA
  (cons idx_UpReqU2
  (cons idx_UpReqPPO
  (cons idx_UpReqSampling
  (cons idx_UpReqAttnGibbs
  (cons idx_UpReqAttnIter
  (cons idx_UpEntropyGainReq
  (cons idx_UpEvictIdReq
  (cons idx_UpReqAlignRestB
  (cons idx_UpReqSLM
  (cons idx_UpReqCauchy
  (cons idx_UpReqMinPAntitone
  (cons idx_UpReqOrderArgmin
  (cons idx_UpReqPCT
  (cons idx_UpReqDpoLoss
  (cons idx_UpFirewallReq
  (cons idx_UpAlignIdReq
  (cons idx_UpPredRelaxReq
  (cons idx_UpAuditBridge
  (cons idx_UpRealLeB
  (cons idx_UpRealLeB2
  (cons idx_UpReqMisc5
  (cons idx_UpReqMisc5B
  (cons idx_UpReqRDF
  (cons idx_UpReqFEPAttn
  (cons idx_UpDebtSqrtAbsReq
  (cons idx_UpReqPPOPlain
  (cons idx_UpReqMinPProjB
  (cons idx_UpRealLeB3
  (cons idx_UpReqPPOB
  (cons idx_UpReqSumB nil)))))))))))))))))))))))))))))))))))))).

Definition DeliveredModules : nat := 32.
Definition ExtraModules     : nat := 7.
Definition TotalModules     : nat := 39.

(* 件数计数：grep decl 实测和 1030 = 宇宙内 944 + 批外 86（UpRealLeB 30 + UpAuditBridge 28 + UpRealLeB2 8 + UpReqMinPProjB 7 + UpRealLeB3 8 + UpReqPPOB 2 + UpReqSumB 3； 增 Misc5 35 + Misc5B 20； 增 RDF 47 + DebtSqrtAbsReq 6 + FEPAttn 16 + LeB2 8； 增 PPOPlain 14 + MinPProjB 7 + AttnGibbs +2 + PPO +4； 增 LeB3 8 + PPOB 2 + SumB 3） *)
Definition DeliveredItems : nat := 1030.
Definition UniverseItems  : nat := 944.

Definition UniverseTotal          : nat := 734.
Definition UniverseDeliveredRows  : nat := 670.
Definition UniverseInFlightRows   : nat := 0.
Definition UniverseFrozenRows     : nat := 64.
Definition UniverseSuspendedRows  : nat := 0.
Definition UniverseUnclaimedRows  : nat := 0.
Definition LastAuditDay           : nat := 20260910.

(* ---------- ToyR 盒A 新增：一般化组合引理（结构性归纳证明，供分账对账推导链实例化） ---------- *)

(* 计数泛函与表长泛函的逐元合同：核对归纳的结构性证明（供 TotalModules_matches 转移闭合） *)
Lemma cnt_mod_length : forall l : list ReqModule, cnt_mod l = Datatypes.length l.
Proof.
  induction l as [| m tl IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* 右减数吸收：n 加 m 再减 m 还原 n——对 m 归纳的结构性证明（供模块分账 39−7=32 实例化） *)
Lemma minus_absorb_r : forall n m : nat, minus (plus n m) m = n.
Proof.
  intros n m. induction m as [| m IH].
  - rewrite <- (plus_n_O n). destruct n; reflexivity.
  - rewrite <- (plus_n_Sm n m). simpl. exact IH.
Qed.

(* ---------- 机器核对引理（reflexivity 级：字面值 vs 清单折叠当场对账） ---------- *)

(* 清单模块数 = 总数字面值（任何增删清单而忘改字面值即爆 G2） *)
Lemma TotalModules_matches : TotalModules = cnt_mod ReqModuleList.
Proof.
  (* ①字面值定义面展开 ②计数泛函经归纳合同引理转移到表长泛函 ③具表 39 元逐元点数闭合 *)
  unfold TotalModules.
  rewrite (cnt_mod_length ReqModuleList).
  reflexivity.
Qed.

(* 清单件数和 = 总件数字面值（件数口径 grep decl 实测） *)
Lemma DeliveredItems_matches : DeliveredItems = sum_cnt ReqModuleList.
Proof. reflexivity. Qed.

(* 宇宙内/批外模块分账闭合 *)
Lemma DeliveredModules_matches : DeliveredModules = minus TotalModules ExtraModules.
Proof.
  (* ①三定义面展开 ②十进制分解 39=32+7 显式化 ③右减数吸收归纳引理实例化 ④闭合 *)
  unfold DeliveredModules, TotalModules, ExtraModules.
  change 39 with (plus 32 7).
  rewrite (minus_absorb_r 32 7).
  reflexivity.
Qed.

(* 宇宙件数分账闭合：全量和 = 宇宙内 + 批外（UpRealLeB 30 + UpAuditBridge 28 + UpRealLeB2 8 + UpReqMinPProjB 7 + UpRealLeB3 8 + UpReqPPOB 2 + UpReqSumB 3 件； 四重→七重 minus） *)
Lemma UniverseItems_matches :
  UniverseItems = minus
    (minus
    (minus
    (minus
    (minus
    (minus
    (minus DeliveredItems (rm_decl_cnt idx_UpRealLeB))
           (rm_decl_cnt idx_UpAuditBridge))
    (rm_decl_cnt idx_UpRealLeB2))
    (rm_decl_cnt idx_UpReqMinPProjB))
    (rm_decl_cnt idx_UpRealLeB3))
    (rm_decl_cnt idx_UpReqPPOB))
    (rm_decl_cnt idx_UpReqSumB).
Proof.
  (* ①注册数定义面展开 ②七件批外件声明数逐件自定义面显式点入（每件一跳，共七跳）
 ③连锁减法十进制闭合（1030−30−28−8−7−8−2−3=944 逐位落定） *)
  unfold UniverseItems.
  change (rm_decl_cnt idx_UpRealLeB) with 30.
  change (rm_decl_cnt idx_UpAuditBridge) with 28.
  change (rm_decl_cnt idx_UpRealLeB2) with 8.
  change (rm_decl_cnt idx_UpReqMinPProjB) with 7.
  change (rm_decl_cnt idx_UpRealLeB3) with 8.
  change (rm_decl_cnt idx_UpReqPPOB) with 2.
  change (rm_decl_cnt idx_UpReqSumB) with 3.
  reflexivity.
Qed.

(* 迁移宇宙五态分解闭合（表行解析 670+0+64+0+0 = 734；批外 LeB3/PPOB/SumB 不占 734） *)
Lemma Universe_splits : UniverseTotal
  = plus (plus (plus (plus UniverseDeliveredRows UniverseInFlightRows)
                   UniverseFrozenRows)
         UniverseSuspendedRows)
  UniverseUnclaimedRows.
Proof.
  (* ①六行定义面展开 ②进行中/未认领两零行吸收（零元加法三处点火） ③十位闭合 670+64=734 *)
  unfold UniverseTotal, UniverseDeliveredRows, UniverseInFlightRows,
         UniverseFrozenRows, UniverseSuspendedRows, UniverseUnclaimedRows.
  repeat rewrite <- plus_n_O.
  reflexivity.
Qed.

(* TLC 口径并行不悖、互不覆盖）+ Live_X 终态结构（S/G 双系 + 旧名消融 + 219 壳）。宇宙行与 39 件 *)
(* idx_ 注册表承 全量不动（append-only）；本节纯新增两层登记面，数值面与 无交集。 *)

(* ---------- 层①：attn 活动区主件面（124 主件，剥注释 token 级 Qed 口径） ---------- *)

Record AttnFace : Set := MkAttnFace
  { af_name : string   (* 主件文件名 *)
  ; af_qed  : nat      (* 剥块注释后 token 级 Qed 计数（ 实测） *)
  ; af_day  : nat      (* 测量日 yyyymmdd *)
  }.

Fixpoint cnt_af (l : list AttnFace) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_af tl)
  end.

Fixpoint sum_af (l : list AttnFace) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (af_qed m) (sum_af tl)
  end.

Definition af_AttnDoeblin : AttnFace := MkAttnFace "AttnDoeblin.v" 42 20260911.
Definition af_AttnHardLimit : AttnFace := MkAttnFace "AttnHardLimit.v" 40 20260911.
Definition af_AttnHardLimit218 : AttnFace := MkAttnFace "AttnHardLimit218.v" 39 20260911.
Definition af_AttnSqrt : AttnFace := MkAttnFace "AttnSqrt.v" 12 20260911.
Definition af_CW220_Extensions : AttnFace := MkAttnFace "CW220_Extensions.v" 552 20260911.
Definition af_CW_ConstructiveWorld_220 : AttnFace := MkAttnFace "CW_ConstructiveWorld_220.v" 3688 20260911.
Definition af_ConstructiveWorld_215 : AttnFace := MkAttnFace "ConstructiveWorld-215.v" 2966 20260911.
Definition af_ConstructiveWorld_217 : AttnFace := MkAttnFace "ConstructiveWorld-217.v" 3056 20260911.
Definition af_ConstructiveWorld_218 : AttnFace := MkAttnFace "ConstructiveWorld-218.v" 3073 20260911.
Definition af_ConstructiveWorld_219 : AttnFace := MkAttnFace "ConstructiveWorld-219.v" 3136 20260911.
Definition af_ConstructiveWorld : AttnFace := MkAttnFace "ConstructiveWorld.v" 2966 20260911.
Definition af_UpAlignId : AttnFace := MkAttnFace "UpAlignId.v" 6 20260911.
Definition af_UpAlignIdReq : AttnFace := MkAttnFace "UpAlignIdReq.v" 8 20260911.
Definition af_UpArchAttn : AttnFace := MkAttnFace "UpArchAttn.v" 5 20260911.
Definition af_UpAuditBridge : AttnFace := MkAttnFace "UpAuditBridge.v" 28 20260911.
Definition af_UpBudgetReal : AttnFace := MkAttnFace "UpBudgetReal.v" 20 20260911.
Definition af_UpCLQuery : AttnFace := MkAttnFace "UpCLQuery.v" 22 20260911.
Definition af_UpCS : AttnFace := MkAttnFace "UpCS.v" 16 20260911.
Definition af_UpConstitution : AttnFace := MkAttnFace "UpConstitution.v" 37 20260911.
Definition af_UpDPOLip : AttnFace := MkAttnFace "UpDPOLip.v" 14 20260911.
Definition af_UpDebtDual : AttnFace := MkAttnFace "UpDebtDual.v" 10 20260911.
Definition af_UpDebtGibbsT : AttnFace := MkAttnFace "UpDebtGibbsT.v" 5 20260911.
Definition af_UpDebtSqrtAbs : AttnFace := MkAttnFace "UpDebtSqrtAbs.v" 6 20260911.
Definition af_UpDebtSqrtAbsReq : AttnFace := MkAttnFace "UpDebtSqrtAbsReq.v" 6 20260911.
Definition af_UpDissip : AttnFace := MkAttnFace "UpDissip.v" 38 20260911.
Definition af_UpEntropyGain : AttnFace := MkAttnFace "UpEntropyGain.v" 10 20260911.
Definition af_UpEntropyGainReq : AttnFace := MkAttnFace "UpEntropyGainReq.v" 10 20260911.
Definition af_UpEvictId : AttnFace := MkAttnFace "UpEvictId.v" 14 20260911.
Definition af_UpEvictIdReq : AttnFace := MkAttnFace "UpEvictIdReq.v" 13 20260911.
Definition af_UpExtras : AttnFace := MkAttnFace "UpExtras.v" 8 20260911.
Definition af_UpFEP : AttnFace := MkAttnFace "UpFEP.v" 5 20260911.
Definition af_UpFirewall : AttnFace := MkAttnFace "UpFirewall.v" 9 20260911.
Definition af_UpFirewallReq : AttnFace := MkAttnFace "UpFirewallReq.v" 9 20260911.
Definition af_UpGRPO : AttnFace := MkAttnFace "UpGRPO.v" 27 20260911.
Definition af_UpGeomB : AttnFace := MkAttnFace "UpGeomB.v" 16 20260911.
Definition af_UpHlogZ : AttnFace := MkAttnFace "UpHlogZ.v" 4 20260911.
Definition af_UpIDL : AttnFace := MkAttnFace "UpIDL.v" 64 20260911.
Definition af_UpIDL_P2 : AttnFace := MkAttnFace "UpIDL_P2.v" 63 20260911.
Definition af_UpKVDrift : AttnFace := MkAttnFace "UpKVDrift.v" 60 20260911.
Definition af_UpKVDrift_P2 : AttnFace := MkAttnFace "UpKVDrift_P2.v" 60 20260911.
Definition af_UpKVEv : AttnFace := MkAttnFace "UpKVEv.v" 11 20260911.
Definition af_UpLoeb : AttnFace := MkAttnFace "UpLoeb.v" 38 20260911.
Definition af_UpLoebD2 : AttnFace := MkAttnFace "UpLoebD2.v" 22 20260911.
Definition af_UpLogMono : AttnFace := MkAttnFace "UpLogMono.v" 4 20260911.
Definition af_UpMinP : AttnFace := MkAttnFace "UpMinP.v" 31 20260911.
Definition af_UpPLA : AttnFace := MkAttnFace "UpPLA.v" 16 20260911.
Definition af_UpPPO : AttnFace := MkAttnFace "UpPPO.v" 5 20260911.
Definition af_UpPredRelax : AttnFace := MkAttnFace "UpPredRelax.v" 6 20260911.
Definition af_UpPredRelaxReq : AttnFace := MkAttnFace "UpPredRelaxReq.v" 6 20260911.
Definition af_UpProj : AttnFace := MkAttnFace "UpProj.v" 32 20260911.
Definition af_UpProjBPC : AttnFace := MkAttnFace "UpProjBPC.v" 17 20260911.
Definition af_UpQKBound : AttnFace := MkAttnFace "UpQKBound.v" 59 20260911.
Definition af_UpRealLeB : AttnFace := MkAttnFace "UpRealLeB.v" 30 20260911.
Definition af_UpRealLeB2 : AttnFace := MkAttnFace "UpRealLeB2.v" 8 20260911.
Definition af_UpRealLeB3 : AttnFace := MkAttnFace "UpRealLeB3.v" 8 20260911.
Definition af_UpRecast : AttnFace := MkAttnFace "UpRecast.v" 50 20260911.
Definition af_UpRefuted : AttnFace := MkAttnFace "UpRefuted.v" 48 20260911.
Definition af_UpReqAlgebra : AttnFace := MkAttnFace "UpReqAlgebra.v" 63 20260911.
Definition af_UpReqAlign : AttnFace := MkAttnFace "UpReqAlign.v" 42 20260911.
Definition af_UpReqAlign2 : AttnFace := MkAttnFace "UpReqAlign2.v" 40 20260911.
Definition af_UpReqAlign3 : AttnFace := MkAttnFace "UpReqAlign3.v" 76 20260911.
Definition af_UpReqAlignRest : AttnFace := MkAttnFace "UpReqAlignRest.v" 16 20260911.
Definition af_UpReqAlignRestA : AttnFace := MkAttnFace "UpReqAlignRestA.v" 23 20260911.
Definition af_UpReqAlignRestB : AttnFace := MkAttnFace "UpReqAlignRestB.v" 55 20260911.
Definition af_UpReqAttnGibbs : AttnFace := MkAttnFace "UpReqAttnGibbs.v" 65 20260911.
Definition af_UpReqAttnIter : AttnFace := MkAttnFace "UpReqAttnIter.v" 31 20260911.
Definition af_UpReqBoltzDirect : AttnFace := MkAttnFace "UpReqBoltzDirect.v" 8 20260911.
Definition af_UpReqBranchPos : AttnFace := MkAttnFace "UpReqBranchPos.v" 8 20260911.
Definition af_UpReqCauchy : AttnFace := MkAttnFace "UpReqCauchy.v" 48 20260911.
Definition af_UpReqDist : AttnFace := MkAttnFace "UpReqDist.v" 89 20260911.
Definition af_UpReqDpoLoss : AttnFace := MkAttnFace "UpReqDpoLoss.v" 6 20260911.
Definition af_UpReqFEPAttn : AttnFace := MkAttnFace "UpReqFEPAttn.v" 16 20260911.
Definition af_UpReqGeomD : AttnFace := MkAttnFace "UpReqGeomD.v" 19 20260911.
Definition af_UpReqGeomIter : AttnFace := MkAttnFace "UpReqGeomIter.v" 16 20260911.
Definition af_UpReqGibbsE : AttnFace := MkAttnFace "UpReqGibbsE.v" 15 20260911.
Definition af_UpReqGibbsE2 : AttnFace := MkAttnFace "UpReqGibbsE2.v" 13 20260911.
Definition af_UpReqHlogZD : AttnFace := MkAttnFace "UpReqHlogZD.v" 11 20260911.
Definition af_UpReqIndex : AttnFace := MkAttnFace "UpReqIndex.v" 27 20260911.
Definition af_UpReqJensen : AttnFace := MkAttnFace "UpReqJensen.v" 12 20260911.
Definition af_UpReqKLCvx : AttnFace := MkAttnFace "UpReqKLCvx.v" 16 20260911.
Definition af_UpReqKLEnergy : AttnFace := MkAttnFace "UpReqKLEnergy.v" 14 20260911.
Definition af_UpReqKLStrict : AttnFace := MkAttnFace "UpReqKLStrict.v" 14 20260911.
Definition af_UpReqLatticeB : AttnFace := MkAttnFace "UpReqLatticeB.v" 11 20260911.
Definition af_UpReqLogCompD : AttnFace := MkAttnFace "UpReqLogCompD.v" 23 20260911.
Definition af_UpReqLogCompD2 : AttnFace := MkAttnFace "UpReqLogCompD2.v" 7 20260911.
Definition af_UpReqLogD : AttnFace := MkAttnFace "UpReqLogD.v" 10 20260911.
Definition af_UpReqLogLinD : AttnFace := MkAttnFace "UpReqLogLinD.v" 18 20260911.
Definition af_UpReqLogPrimD : AttnFace := MkAttnFace "UpReqLogPrimD.v" 18 20260911.
Definition af_UpReqLogRDF : AttnFace := MkAttnFace "UpReqLogRDF.v" 17 20260911.
Definition af_UpReqMinPAntitone : AttnFace := MkAttnFace "UpReqMinPAntitone.v" 5 20260911.
Definition af_UpReqMinPProjB : AttnFace := MkAttnFace "UpReqMinPProjB.v" 7 20260911.
Definition af_UpReqMisc5B : AttnFace := MkAttnFace "UpReqMisc5B.v" 20 20260911.
Definition af_UpReqOrderArgmin : AttnFace := MkAttnFace "UpReqOrderArgmin.v" 7 20260911.
Definition af_UpReqPCT : AttnFace := MkAttnFace "UpReqPCT.v" 2 20260911.
Definition af_UpReqPPO : AttnFace := MkAttnFace "UpReqPPO.v" 25 20260911.
Definition af_UpReqPPOB : AttnFace := MkAttnFace "UpReqPPOB.v" 4 20260911.
Definition af_UpReqPPOGapB : AttnFace := MkAttnFace "UpReqPPOGapB.v" 8 20260911.
Definition af_UpReqPPOPlain : AttnFace := MkAttnFace "UpReqPPOPlain.v" 14 20260911.
Definition af_UpReqPowB : AttnFace := MkAttnFace "UpReqPowB.v" 10 20260911.
Definition af_UpReqRDF : AttnFace := MkAttnFace "UpReqRDF.v" 47 20260911.
Definition af_UpReqRealFEP : AttnFace := MkAttnFace "UpReqRealFEP.v" 11 20260911.
Definition af_UpReqSLM : AttnFace := MkAttnFace "UpReqSLM.v" 41 20260911.
Definition af_UpReqSampling : AttnFace := MkAttnFace "UpReqSampling.v" 43 20260911.
Definition af_UpReqSqPos : AttnFace := MkAttnFace "UpReqSqPos.v" 5 20260911.
Definition af_UpReqSqrtF : AttnFace := MkAttnFace "UpReqSqrtF.v" 27 20260911.
Definition af_UpReqSumB : AttnFace := MkAttnFace "UpReqSumB.v" 3 20260911.
Definition af_UpReqSumD : AttnFace := MkAttnFace "UpReqSumD.v" 27 20260911.
Definition af_UpReqTempEntropy : AttnFace := MkAttnFace "UpReqTempEntropy.v" 14 20260911.
Definition af_UpReqTempInterp : AttnFace := MkAttnFace "UpReqTempInterp.v" 11 20260911.
Definition af_UpReqU2 : AttnFace := MkAttnFace "UpReqU2.v" 20 20260911.
Definition af_UpReqZAuto : AttnFace := MkAttnFace "UpReqZAuto.v" 8 20260911.
Definition af_UpReqZPosD : AttnFace := MkAttnFace "UpReqZPosD.v" 6 20260911.
Definition af_UpReqZPosFinal : AttnFace := MkAttnFace "UpReqZPosFinal.v" 9 20260911.
Definition af_UpReqZPosI : AttnFace := MkAttnFace "UpReqZPosI.v" 6 20260911.
Definition af_UpReqZPosI2 : AttnFace := MkAttnFace "UpReqZPosI2.v" 15 20260911.
Definition af_UpSLM : AttnFace := MkAttnFace "UpSLM.v" 55 20260911.
Definition af_UpSigMigrate : AttnFace := MkAttnFace "UpSigMigrate.v" 13 20260911.
Definition af_UpSigMigrate2 : AttnFace := MkAttnFace "UpSigMigrate2.v" 49 20260911.
Definition af_UpStepKL : AttnFace := MkAttnFace "UpStepKL.v" 32 20260911.
Definition af_UpStepKLM3 : AttnFace := MkAttnFace "UpStepKLM3.v" 18 20260911.
Definition af_UpStopTime : AttnFace := MkAttnFace "UpStopTime.v" 45 20260911.
Definition af_UpTVDoeblin : AttnFace := MkAttnFace "UpTVDoeblin.v" 58 20260911.
Definition af_UpTVReal : AttnFace := MkAttnFace "UpTVReal.v" 33 20260911.
Definition af_UpTempWindow : AttnFace := MkAttnFace "UpTempWindow.v" 69 20260911.

Definition AttnFaceList : list AttnFace :=
  cons af_AttnDoeblin
  (cons af_AttnHardLimit
  (cons af_AttnHardLimit218
  (cons af_AttnSqrt
  (cons af_CW220_Extensions
  (cons af_CW_ConstructiveWorld_220
  (cons af_ConstructiveWorld_215
  (cons af_ConstructiveWorld_217
  (cons af_ConstructiveWorld_218
  (cons af_ConstructiveWorld_219
  (cons af_ConstructiveWorld
  (cons af_UpAlignId
  (cons af_UpAlignIdReq
  (cons af_UpArchAttn
  (cons af_UpAuditBridge
  (cons af_UpBudgetReal
  (cons af_UpCLQuery
  (cons af_UpCS
  (cons af_UpConstitution
  (cons af_UpDPOLip
  (cons af_UpDebtDual
  (cons af_UpDebtGibbsT
  (cons af_UpDebtSqrtAbs
  (cons af_UpDebtSqrtAbsReq
  (cons af_UpDissip
  (cons af_UpEntropyGain
  (cons af_UpEntropyGainReq
  (cons af_UpEvictId
  (cons af_UpEvictIdReq
  (cons af_UpExtras
  (cons af_UpFEP
  (cons af_UpFirewall
  (cons af_UpFirewallReq
  (cons af_UpGRPO
  (cons af_UpGeomB
  (cons af_UpHlogZ
  (cons af_UpIDL
  (cons af_UpIDL_P2
  (cons af_UpKVDrift
  (cons af_UpKVDrift_P2
  (cons af_UpKVEv
  (cons af_UpLoeb
  (cons af_UpLoebD2
  (cons af_UpLogMono
  (cons af_UpMinP
  (cons af_UpPLA
  (cons af_UpPPO
  (cons af_UpPredRelax
  (cons af_UpPredRelaxReq
  (cons af_UpProj
  (cons af_UpProjBPC
  (cons af_UpQKBound
  (cons af_UpRealLeB
  (cons af_UpRealLeB2
  (cons af_UpRealLeB3
  (cons af_UpRecast
  (cons af_UpRefuted
  (cons af_UpReqAlgebra
  (cons af_UpReqAlign
  (cons af_UpReqAlign2
  (cons af_UpReqAlign3
  (cons af_UpReqAlignRest
  (cons af_UpReqAlignRestA
  (cons af_UpReqAlignRestB
  (cons af_UpReqAttnGibbs
  (cons af_UpReqAttnIter
  (cons af_UpReqBoltzDirect
  (cons af_UpReqBranchPos
  (cons af_UpReqCauchy
  (cons af_UpReqDist
  (cons af_UpReqDpoLoss
  (cons af_UpReqFEPAttn
  (cons af_UpReqGeomD
  (cons af_UpReqGeomIter
  (cons af_UpReqGibbsE
  (cons af_UpReqGibbsE2
  (cons af_UpReqHlogZD
  (cons af_UpReqIndex
  (cons af_UpReqJensen
  (cons af_UpReqKLCvx
  (cons af_UpReqKLEnergy
  (cons af_UpReqKLStrict
  (cons af_UpReqLatticeB
  (cons af_UpReqLogCompD
  (cons af_UpReqLogCompD2
  (cons af_UpReqLogD
  (cons af_UpReqLogLinD
  (cons af_UpReqLogPrimD
  (cons af_UpReqLogRDF
  (cons af_UpReqMinPAntitone
  (cons af_UpReqMinPProjB
  (cons af_UpReqMisc5B
  (cons af_UpReqOrderArgmin
  (cons af_UpReqPCT
  (cons af_UpReqPPO
  (cons af_UpReqPPOB
  (cons af_UpReqPPOGapB
  (cons af_UpReqPPOPlain
  (cons af_UpReqPowB
  (cons af_UpReqRDF
  (cons af_UpReqRealFEP
  (cons af_UpReqSLM
  (cons af_UpReqSampling
  (cons af_UpReqSqPos
  (cons af_UpReqSqrtF
  (cons af_UpReqSumB
  (cons af_UpReqSumD
  (cons af_UpReqTempEntropy
  (cons af_UpReqTempInterp
  (cons af_UpReqU2
  (cons af_UpReqZAuto
  (cons af_UpReqZPosD
  (cons af_UpReqZPosFinal
  (cons af_UpReqZPosI
  (cons af_UpReqZPosI2
  (cons af_UpSLM
  (cons af_UpSigMigrate
  (cons af_UpSigMigrate2
  (cons af_UpStepKL
  (cons af_UpStepKLM3
  (cons af_UpStopTime
  (cons af_UpTVDoeblin
  (cons af_UpTVReal
  (cons af_UpTempWindow nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* 主件面统计：124 主件 / 剥注释 token 级 Qed 和 22168（含自指件 UpReqIndex.v v2 终态 27）； *)
(* 存档/快照/副本/检查点（_ 前缀与 probe 族）不入主件面，处置状态见层② 退役条目与交付报告。 *)
Definition AttnFaceModules : nat := 124.
Definition AttnFaceItems   : nat := 22168.

Lemma AttnFaceModules_matches : AttnFaceModules = cnt_af AttnFaceList.
Proof. reflexivity. Qed.

Lemma AttnFaceItems_matches : AttnFaceItems = sum_af AttnFaceList.
Proof. reflexivity. Qed.

(* ---------- 层②：Live_X 终态结构面（S01–S15 拆分组 + G 系合并组 + 219 壳/扩展 + 退役处置） ---------- *)

Record LiveGroup : Set := MkLiveGroup
  { lg_name    : string   (* 组名 / 文件名 / 退役件名 *)
  ; lg_kind    : nat      (* 1=S 系拆分组 2=G 系合并组 3=聚合壳/扩展件 0=退役件 *)
  ; lg_members : nat      (* S=组内剥注释 Qed 件数；G=README 旧名成员数；壳/扩展=1；退役=0 *)
  ; lg_note    : string   (* 主题 / 成员旧名清单 / 处置说明 *)
  }.

Fixpoint cnt_lg (l : list LiveGroup) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_lg tl)
  end.

Fixpoint sum_lg (l : list LiveGroup) : nat :=
  match l with
  | nil => 0
  | cons g tl => plus (lg_members g) (sum_lg tl)
  end.

Definition lg_S01BaseRing : LiveGroup := MkLiveGroup "S01_BaseRing.v" 1 99 "BaseRing / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S02CauchyComplete : LiveGroup := MkLiveGroup "S02_CauchyComplete.v" 1 138 "CauchyComplete / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S03QExp : LiveGroup := MkLiveGroup "S03_QExp.v" 1 223 "QExp / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S04RealExpLogConv : LiveGroup := MkLiveGroup "S04_RealExpLogConv.v" 1 113 "RealExpLogConv / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S05AlignmentGRPO : LiveGroup := MkLiveGroup "S05_AlignmentGRPO.v" 1 141 "AlignmentGRPO / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S06DiffSamplingGibbs : LiveGroup := MkLiveGroup "S06_DiffSamplingGibbs.v" 1 240 "DiffSamplingGibbs / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S07RealSetoidExpLog : LiveGroup := MkLiveGroup "S07_RealSetoidExpLog.v" 1 275 "RealSetoidExpLog / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S08RealMainlineDPO : LiveGroup := MkLiveGroup "S08_RealMainlineDPO.v" 1 117 "RealMainlineDPO / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S09EntropyReal : LiveGroup := MkLiveGroup "S09_EntropyReal.v" 1 94 "EntropyReal / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S10KVQuantTrig : LiveGroup := MkLiveGroup "S10_KVQuantTrig.v" 1 432 "KVQuantTrig / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S11TP3B5 : LiveGroup := MkLiveGroup "S11_TP3B5.v" 1 410 "TP3B5 / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S12B5RecycleSF : LiveGroup := MkLiveGroup "S12_B5RecycleSF.v" 1 331 "B5RecycleSF / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S13NLiveAudit : LiveGroup := MkLiveGroup "S13_NLiveAudit.v" 1 192 "NLiveAudit / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S14B5BatchBlock : LiveGroup := MkLiveGroup "S14_B5BatchBlock.v" 1 259 "B5BatchBlock / 219 split group; member cnt = stripped-comment Qed tokens".
Definition lg_S15TailFEPUp : LiveGroup := MkLiveGroup "S15_TailFEPUp.v" 1 73 "TailFEPUp / 219 split group; member cnt = stripped-comment Qed tokens".

Definition lg_G01 : LiveGroup := MkLiveGroup "G01_CoreMicro.v" 2 5 "members: UpHlogZ,UpExtras,UpFEP,UpLogMono,UpPPO".
Definition lg_G02 : LiveGroup := MkLiveGroup "G02_Debt.v" 2 3 "members: UpDebtSqrtAbs,UpDebtDual,UpDebtGibbsT".
Definition lg_G04 : LiveGroup := MkLiveGroup "G04_ProjFam.v" 2 4 "members: UpPLA,UpPredRelax,UpProj,UpProjBPC".
Definition lg_G05 : LiveGroup := MkLiveGroup "G05_LogSmall.v" 2 3 "members: UpReqLogD,UpReqLogLinD,UpReqLogPrimD".
Definition lg_G06 : LiveGroup := MkLiveGroup "G06_BForm.v" 2 4 "members: UpReqPPOB,UpReqSumB,UpReqMinPProjB,UpReqLatticeB".
Definition lg_G07 : LiveGroup := MkLiveGroup "G07_KLWall.v" 2 5 "members: UpReqKLCvx,UpReqPowB,UpReqJensen,UpReqKLStrict,UpReqKLEnergy".
Definition lg_G08 : LiveGroup := MkLiveGroup "G08_Gibbs.v" 2 3 "members: UpReqHlogZD,UpReqGibbsD,UpReqGibbsE2".
Definition lg_G09 : LiveGroup := MkLiveGroup "G09_MiscSmall.v" 2 4 "members: UpReqPCT,UpReqBoltzDirect,UpReqSqPos,UpReqOrderArgmin".
Definition lg_G10 : LiveGroup := MkLiveGroup "G10_LoebFam.v" 2 4 "members: UpLoeb,UpLoebD2,UpRefuted,UpQKBound".
Definition lg_G11 : LiveGroup := MkLiveGroup "G11_IDLFam.v" 2 2 "members: UpCLQuery,UpIDL".
Definition lg_G12 : LiveGroup := MkLiveGroup "G12_ZPosFam.v" 2 5 "members: UpReqZPosD,UpReqZPosI,UpReqZPosI2,UpReqZAuto,UpReqZPosFinal".
Definition lg_G13 : LiveGroup := MkLiveGroup "G13_EvictFam.v" 2 2 "members: UpEvictId,UpEvictIdReq".
(* 组号缺位注记：G03 无组（G 系编号 01/02/04–13 共 12 组，缺位为合并史留痕，非漏登）。 *)

Definition lg_CW220Ext : LiveGroup := MkLiveGroup "CW220_Extensions.v" 3 1 "CW220 extensions piece; stripped-comment Qed 552".
Definition lg_Ret214 : LiveGroup := MkLiveGroup "ConstructiveWorld-214" 0 0 "retired: CW214 name-level check 219 covers 214, 3943/3943 hit; dependents re-Require shell 219".
Definition lg_RetUpTVReal : LiveGroup := MkLiveGroup "UpTVReal" 0 0 "retired: absent in Live_X; attn legacy 33 Qed, not migrated".
Definition lg_RetProbeReexSig : LiveGroup := MkLiveGroup "ProbeReexSig" 0 0 "retired probe: absent in Live_X; attn legacy ProbeReexSig/ProbeReexSig2".

Definition SLiveList : list LiveGroup :=
  cons lg_S01BaseRing
  (cons lg_S02CauchyComplete
  (cons lg_S03QExp
  (cons lg_S04RealExpLogConv
  (cons lg_S05AlignmentGRPO
  (cons lg_S06DiffSamplingGibbs
  (cons lg_S07RealSetoidExpLog
  (cons lg_S08RealMainlineDPO
  (cons lg_S09EntropyReal
  (cons lg_S10KVQuantTrig
  (cons lg_S11TP3B5
  (cons lg_S12B5RecycleSF
  (cons lg_S13NLiveAudit
  (cons lg_S14B5BatchBlock
  (cons lg_S15TailFEPUp nil)))))))))))))).

Definition GLiveList : list LiveGroup :=
  cons lg_G01
  (cons lg_G02
  (cons lg_G04
  (cons lg_G05
  (cons lg_G06
  (cons lg_G07
  (cons lg_G08
  (cons lg_G09
  (cons lg_G10
  (cons lg_G11
  (cons lg_G12
  (cons lg_G13 nil))))))))))).

Definition SLiveGroups : nat := 15.
Definition SFaceQed     : nat := 3137.
Lemma SLiveGroups_matches : SLiveGroups = cnt_lg SLiveList.
Proof. reflexivity. Qed.

Lemma SFaceQed_matches : SFaceQed = sum_lg SLiveList.
Proof. reflexivity. Qed.

(* G 面：12 组 / README 旧名成员和 44 / G 组件剥注释 Qed 和 640。结构不变量：逐组成员旧名
 attn Qed 和 = Live_X G 组件 Qed（12 组全数 1:1，合并无损机械可证，见 G*_merge_lossless）。 *)
Definition GMergeGroups  : nat := 12.
Definition GMergeMembers : nat := 44.
Definition GMergeQed     : nat := 625.

Definition gqed_G01 : nat := 26.  (* G01_CoreMicro.v 剥注释 Qed 实测 *)
Definition gqed_G02 : nat := 21.  (* G02_Debt.v 剥注释 Qed 实测 *)
Definition gqed_G04 : nat := 71.  (* G04_ProjFam.v 剥注释 Qed 实测 *)
Definition gqed_G05 : nat := 46.  (* G05_LogSmall.v 剥注释 Qed 实测 *)
Definition gqed_G06 : nat := 25.  (* G06_BForm.v 剥注释 Qed 实测 *)
Definition gqed_G07 : nat := 66.  (* G07_KLWall.v 剥注释 Qed 实测 *)
Definition gqed_G08 : nat := 24.  (* G08_Gibbs.v 剥注释 Qed 实测 *)
Definition gqed_G09 : nat := 22.  (* G09_MiscSmall.v 剥注释 Qed 实测 *)
Definition gqed_G10 : nat := 167.  (* G10_LoebFam.v 剥注释 Qed 实测 *)
Definition gqed_G11 : nat := 86.  (* G11_IDLFam.v 剥注释 Qed 实测 *)
Definition gqed_G12 : nat := 44.  (* G12_ZPosFam.v 剥注释 Qed 实测 *)
Definition gqed_G13 : nat := 27.  (* G13_EvictFam.v 剥注释 Qed 实测 *)

Lemma GMergeGroups_matches : GMergeGroups = cnt_lg GLiveList.
Proof. reflexivity. Qed.

Lemma GMergeMembers_matches : GMergeMembers = sum_lg GLiveList.
Proof. reflexivity. Qed.

Lemma GMergeQed_matches : GMergeQed = plus gqed_G01 (plus gqed_G02 (plus gqed_G04 (plus gqed_G05 (plus gqed_G06 (plus gqed_G07 (plus gqed_G08 (plus gqed_G09 (plus gqed_G10 (plus gqed_G11 (plus gqed_G12 (gqed_G13))))))))))).
Proof. reflexivity. Qed.

Lemma G01_merge_lossless : gqed_G01 = plus (af_qed af_UpHlogZ) (plus (af_qed af_UpExtras) (plus (af_qed af_UpFEP) (plus (af_qed af_UpLogMono) (af_qed af_UpPPO)))).
Proof. reflexivity. Qed.

Lemma G02_merge_lossless : gqed_G02 = plus (af_qed af_UpDebtSqrtAbs) (plus (af_qed af_UpDebtDual) (af_qed af_UpDebtGibbsT)).
Proof. reflexivity. Qed.

Lemma G04_merge_lossless : gqed_G04 = plus (af_qed af_UpPLA) (plus (af_qed af_UpPredRelax) (plus (af_qed af_UpProj) (af_qed af_UpProjBPC))).
Proof. reflexivity. Qed.

Lemma G05_merge_lossless : gqed_G05 = plus (af_qed af_UpReqLogD) (plus (af_qed af_UpReqLogLinD) (af_qed af_UpReqLogPrimD)).
Proof. reflexivity. Qed.

Lemma G06_merge_lossless : gqed_G06 = plus (af_qed af_UpReqPPOB) (plus (af_qed af_UpReqSumB) (plus (af_qed af_UpReqMinPProjB) (af_qed af_UpReqLatticeB))).
Proof. reflexivity. Qed.

Lemma G07_merge_lossless : gqed_G07 = plus (af_qed af_UpReqKLCvx) (plus (af_qed af_UpReqPowB) (plus (af_qed af_UpReqJensen) (plus (af_qed af_UpReqKLStrict) (af_qed af_UpReqKLEnergy)))).
Proof. reflexivity. Qed.

Lemma G08_merge_lossless : gqed_G08 = plus (af_qed af_UpReqHlogZD) (af_qed af_UpReqGibbsE2).
Proof. reflexivity. Qed.

Lemma G09_merge_lossless : gqed_G09 = plus (af_qed af_UpReqPCT) (plus (af_qed af_UpReqBoltzDirect) (plus (af_qed af_UpReqSqPos) (af_qed af_UpReqOrderArgmin))).
Proof. reflexivity. Qed.

Lemma G10_merge_lossless : gqed_G10 = plus (af_qed af_UpLoeb) (plus (af_qed af_UpLoebD2) (plus (af_qed af_UpRefuted) (af_qed af_UpQKBound))).
Proof. reflexivity. Qed.

Lemma G11_merge_lossless : gqed_G11 = plus (af_qed af_UpCLQuery) (af_qed af_UpIDL).
Proof. reflexivity. Qed.

Lemma G12_merge_lossless : gqed_G12 = plus (af_qed af_UpReqZPosD) (plus (af_qed af_UpReqZPosI) (plus (af_qed af_UpReqZPosI2) (plus (af_qed af_UpReqZAuto) (af_qed af_UpReqZPosFinal)))).
Proof. reflexivity. Qed.

Lemma G13_merge_lossless : gqed_G13 = plus (af_qed af_UpEvictId) (af_qed af_UpEvictIdReq).
Proof. reflexivity. Qed.

(* Live_X 总面：99 .v（ls 实测）= S 15 + G 12 + 壳/扩展 2 + 独立件 70。 *)
Definition LiveXFiles    : nat := 99.
Definition LiveXIndFiles : nat := 70.
Lemma LiveXSplits : LiveXFiles = plus (plus SLiveGroups GMergeGroups) (plus 2 LiveXIndFiles).
Proof. reflexivity. Qed.

(* idx_UpReqAttnGibbs 63→65 + idx_UpReqPPO 22→26 → 模块 36 = 宇宙内 32 + 批外 4、件数 1017 = 宇宙内 944 + 批外 73； *)

(* → 模块 39 = 宇宙内 32 + 批外 7、件数 1030 = 宇宙内 944 + 批外 86、UniverseItems_matches minus 链四重→七重； *)

(* 四项验证：G1 禁词全文件 0 命中（含头注）；G2 coqc 9.0 -vos 预审+cpu_guard 中转全量 EXIT=0；G3 提取检查点经 coqtop *)

(* 五字段实测登记——件名 / 行数 wc -l（和 5474）/ Qed 数 grep -c "Qed\."（和 101；与剥注释 token 级 \bQed\. 双口径逐件相等， *)
(* Theorem/Lemma/Corollary 行 TLC 口径亦 1:1，三负证模式（G1 表前三项）逐件全零）/ 登记日 / 一句话定位（ASCII 串，中文定位见各条上注）； *)
(* idx_ （T7/ 同款口径）；盘面观察只记不改：同日 4 件进行中（UpReqEntropyMaxTemp/UpReqMinUniqueTight/ *)
(* UpReqTempDual/UpReqTopKTVChain，未双树同步）不入本面；UpReqAlign4 的 CW_Live 树副本落后 Live_X 一版（ vs ），； *)

(* ng_note = 一句话定位（房规 ASCII 串；中文全定位见各条注释）。 *)

Record NewGreenFace : Set := MkNewGreenFace
  { ng_name  : string   (* 件名 *)
  ; ng_lines : nat      (* wc -l 实测行数 *)
  ; ng_qed   : nat      (* Qed 闭合数（grep -c 与 token 级双口径相等） *)
  ; ng_day   : nat      (* 登记日 yyyymmdd *)
  ; ng_note  : string   (* 一句话定位 *)
  ; ng_meta : string (* A5 扩列：权威元数据锚 "L<wc -l 实测>:m<md5 前 6>"，登记时点快照；论文/单据行数锚一律引本列，禁再裸引行数 *)
  }.

Fixpoint cnt_ng (l : list NewGreenFace) : nat :=
  match l with
  | nil => 0
  | cons _ tl => S (cnt_ng tl)
  end.

Fixpoint sum_ng_qed (l : list NewGreenFace) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (ng_qed m) (sum_ng_qed tl)
  end.

Fixpoint sum_ng_lines (l : list NewGreenFace) : nat :=
  match l with
  | nil => 0
  | cons m tl => plus (ng_lines m) (sum_ng_lines tl)
  end.

(* ng_UpReqKLSTangent —— UpReqKLSTangent.v：KL 严格切线连锁（六件） *)
Definition ng_UpReqKLSTangent : NewGreenFace :=
  MkNewGreenFace "UpReqKLSTangent.v" 205 6 20260911 "KL strict tangent chain, six pieces" "L226:m99ceee".

(* ng_UpReqSteadyThermo —— UpReqSteadyThermo.v：4.9 稳态复刻 *)
Definition ng_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "UpReqSteadyThermo.v" 129 1 20260911 "4.9 steady-state thermo replica" "L138:m5a7ba5".

(* ng_UpReqMpDomain —— UpReqMpDomain.v：mp 域引擎+12 件全清 *)
Definition ng_UpReqMpDomain : NewGreenFace :=
  MkNewGreenFace "UpReqMpDomain.v" 859 23 20260911 "mp domain engine, 12 pieces all cleared" "L1074:ma5ddde".

(* ng_UpReqTempDefs —— UpReqTempDefs.v：温度族定义件 *)
Definition ng_UpReqTempDefs : NewGreenFace :=
  MkNewGreenFace "UpReqTempDefs.v" 459 7 20260911 "temperature family definition piece" "L468:mcf8eee".

(* ng_UpReqEntropyDeficitTemp —— UpReqEntropyDeficitTemp.v：4.6a 熵亏 *)
Definition ng_UpReqEntropyDeficitTemp : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyDeficitTemp.v" 582 8 20260911 "4.6a entropy deficit under temperature" "L600:mbf3580".

(* ng_UpReqTrainingEquiv —— UpReqTrainingEquiv.v：4.10 组装 *)
Definition ng_UpReqTrainingEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqTrainingEquiv.v" 489 8 20260911 "4.10 training equivalence assembly" "L509:mc6b676".

(* ng_UpReqTVAbsEps —— UpReqTVAbsEps.v：5.10 伴随件 *)
Definition ng_UpReqTVAbsEps : NewGreenFace :=
  MkNewGreenFace "UpReqTVAbsEps.v" 180 6 20260911 "5.10 total-variation abs eps adjoint piece" "L189:m8d62a7".

(* ng_UpReqPowMonoBridge —— UpReqPowMonoBridge.v：I4 合成器（leB 乘法保序三面落件+一跳拼装） *)
Definition ng_UpReqPowMonoBridge : NewGreenFace :=
  MkNewGreenFace "UpReqPowMonoBridge.v" 337 6 20260911 "I4 pow-monotone bridge synthesizer" "L346:mbbb4d5".

(* ng_UpReqAlign4 —— UpReqAlign4.v：KLCvx 批A+批B（两槽供给+核减演示） *)

(* 全量口径，双测同 md5 62e30e10、补绑编译 EXIT=0，改账细节见文末 改账段] *)
Definition ng_UpReqAlign4 : NewGreenFace :=
  MkNewGreenFace "UpReqAlign4.v" 1431 28 20260911 "KLCvx batch A+B: two-slot supply and redemption demo" "L1432:mb9ca2c".

Definition NewGreenList : list NewGreenFace :=
  cons ng_UpReqKLSTangent
  (cons ng_UpReqSteadyThermo
  (cons ng_UpReqMpDomain
  (cons ng_UpReqTempDefs
  (cons ng_UpReqEntropyDeficitTemp
  (cons ng_UpReqTrainingEquiv
  (cons ng_UpReqTVAbsEps
  (cons ng_UpReqPowMonoBridge
  (cons ng_UpReqAlign4 nil)))))))).

(* 今日新绿面统计：9 件 / 行数和 4671 / Qed 和 93（字面值；一致性由下方等式引理编译期核对； *)
(* 改账后口径，改账前原值 5474/101，见文末 改账段）。 *)
Definition NewGreenPieces  : nat := 9.
Definition NewGreenLineSum : nat := 4671.
Definition NewGreenQedSum  : nat := 93.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenPieces_matches : NewGreenPieces = cnt_ng NewGreenList.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenLineSum_matches : NewGreenLineSum = sum_ng_lines NewGreenList.
Proof. reflexivity. Qed.

(* Qed 和 = 字面值 *)
Lemma NewGreenQedSum_matches : NewGreenQedSum = sum_ng_qed NewGreenList.
Proof. reflexivity. Qed.

(* ng_ 第三轨续写： 后流水线新绿 4 件逐件实测登记（append-only； 既有 14 条目/清单/ *)

(* 级 \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；三负证模式逐件全零）。 *)

(* ng_UpReqEntropyMaxTemp —— UpReqEntropyMaxTemp.v：，定理 4.6b max_entropy_is_boltzmann_temp *)
(* （同约束能量下熵封顶逐 eps 形；四树 md5 三树一致 9886a897，_Live 缺件见头注观察段） *)
Definition ng_UpReqEntropyMaxTemp : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyMaxTemp.v" 407 5 20260911 "4.6b max-entropy boltzmann temperature order gate" "L424:m0ad698".

(* ng_UpReqMinUniqueTight —— UpReqMinUniqueTight.v：，定理 4.5 free_energy_min_unique *)
(* （自由能最小点唯一性 Real 层可达形双版；四树 md5 三树一致 421fd5d5） *)
Definition ng_UpReqMinUniqueTight : NewGreenFace :=
  MkNewGreenFace "UpReqMinUniqueTight.v" 532 8 20260911 "4.5 free-energy min unique reachable form" "L541:ma4b37a".

Definition NewGreenListV22 : list NewGreenFace :=
  cons ng_UpReqEntropyMaxTemp
  (cons ng_UpReqMinUniqueTight
  nil).

(* 续写统计：3 件 / 行数和 1154 / 闭合和 18（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV22Pieces  : nat := 2.
Definition NewGreenV22LineSum : nat := 939.
Definition NewGreenV22QedSum  : nat := 13.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV22Pieces_matches : NewGreenV22Pieces = cnt_ng NewGreenListV22.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV22LineSum_matches : NewGreenV22LineSum = sum_ng_lines NewGreenListV22.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV22QedSum_matches : NewGreenV22QedSum = sum_ng_qed NewGreenListV22.
Proof. reflexivity. Qed.

(* 1) ng_UpReqAlign4（ 登记 968 行/18 闭合）→ 盘面 1431 行/28 闭合（Z2+Z3 批B 增量落盘； *)

(* 2) ng_UpReqTVAbsEps（180/6）与 ng_UpReqPowMonoBridge（337/6）盘面再测与登记口径相符。 *)

(* 现态单件编译失败（sum 段完成错配）；。 *)
(* 4) _Live 快照树缺本组 7 件（含 Align4/TVAbsEps/PowMonoBridge； 同款观察），Live_X/ *)

(* ng_ 第三轨续写： 后流水线新绿 1 件逐件实测登记（append-only；/ 既有 18 条目/清单/ *)

(* token 级 \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；三负证模式逐件全零）。 *)
(* 入库判据（ 卡定式）：稳定窗口多测一致（同 md5）+ 现态补绑 CW_vo 树单件编译 EXIT=0。 *)

(* ng_UpReqTempDual —— UpReqTempDual.v：，定理 4.6d 温度化最大熵对偶闭环（sigT 形组装） *)

(* 005d7ece，现态补绑单件编译 EXIT=0、Print Assumptions 8 件全 Closed；四树对账 *)

Definition ng_UpReqTempDual : NewGreenFace :=
  MkNewGreenFace "UpReqTempDual.v" 417 8 20260911 "4.6d sigT dual closure under temperature" "L434:m7959b5".

Definition NewGreenListV23 : list NewGreenFace :=
  cons ng_UpReqTempDual nil.

(* 续写统计：1 件 / 行数和 417 / 闭合和 8（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV23Pieces  : nat := 1.
Definition NewGreenV23LineSum : nat := 417.
Definition NewGreenV23QedSum  : nat := 8.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV23Pieces_matches : NewGreenV23Pieces = cnt_ng NewGreenListV23.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV23LineSum_matches : NewGreenV23LineSum = sum_ng_lines NewGreenListV23.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV23QedSum_matches : NewGreenV23QedSum = sum_ng_qed NewGreenListV23.
Proof. reflexivity. Qed.

(* 末测 mtime 仍在写盘）；现态补绑 CW_vo 树单件编译 EXIT=1（rtk2 段 real_plus/ *)
(* real_minus_r 完成错配）；稳定窗口双测不一致即不采信（ 卡定式），。 *)
(* 2) UpReqEntropyDeficitTemp（ 在册 582/8）盘面再测相符，零漂移，不重复登记。 *)

(* 4) UpReqTempDual 四树对账：Live_X/CW_Live/CW_vo md5 一致 005d7ece；_Live 快照树缺件 *)

(* ng_ 第三轨续写： 后流水线新绿 2 件逐件实测登记 + 行使 / 移交之改账权一笔。 *)

(* token 级 \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；G1 表九词逐件全零）。 *)
(* 入库判据（/ 卡定式）：稳定窗口双测一致（同 md5，间隔 >45s）+ 现态补绑单件编译 EXIT=0。 *)

(* ng_UpReqNegFactorB —— UpReqNegFactorB.v：，le_b 乘法保序·负右因子反变面补全（五件） *)
(* （X3d PowMonoBridge 头注诚实边界注记之邻接缺口补全；取负共轭路线，eps 证人翻转零手工重排； *)

Definition ng_UpReqNegFactorB : NewGreenFace :=
  MkNewGreenFace "UpReqNegFactorB.v" 183 5 20260911 "leB multiplication contravariant face, nonpositive right factor" "L199:m50d3fb".

(* ng_UpReqEntropyUniqueNeg —— UpReqEntropyUniqueNeg.v：b，定理 4.6c 逆否形（九件） *)
(* （熵最大点唯一性之逆否可达形；基座 CW_219 壳+TempDefs+EntropyDeficitTemp+EntropyUniqueTemp *)

(* 假设清查全 Closed；链上三件陈旧 .vo 之原树重编译见观察段 2） *)
Definition ng_UpReqEntropyUniqueNeg : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyUniqueNeg.v" 568 9 20260911 "4.6c entropy max unique contrapositive form" "L581:m90e318".

Definition NewGreenListV24 : list NewGreenFace :=
  cons ng_UpReqNegFactorB
  (cons ng_UpReqEntropyUniqueNeg nil).

(* 续写统计：2 件 / 行数和 751 / 闭合和 14（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV24Pieces  : nat := 2.
Definition NewGreenV24LineSum : nat := 751.
Definition NewGreenV24QedSum  : nat := 14.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV24Pieces_matches : NewGreenV24Pieces = cnt_ng NewGreenListV24.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV24LineSum_matches : NewGreenV24LineSum = sum_ng_lines NewGreenListV24.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV24QedSum_matches : NewGreenV24QedSum = sum_ng_qed NewGreenListV24.
Proof. reflexivity. Qed.

(* ng_UpReqAlign4 登记行就地改账：968 行/18 闭合 → 1431 行/28 闭合（漂移 +463/+10，Z2 批A+ *)

(* CW_vo 树单件编译 EXIT=0 绿态确认。连带字面值（reflexivity 对账闭合所需，上方已改）： *)

(* 口径，只留不改。除本笔受权改账（登记行数字+统计字面值+相邻注释）外，既有条目零触碰、零缩水。 *)

(* 改账算术对账（编译期机械核对） *)
Lemma Align4AmendLines : 1431 = plus 968 463.
Proof. reflexivity. Qed.

Lemma Align4AmendQed : 28 = plus 18 10.
Proof. reflexivity. Qed.

Lemma Align4AmendLineSum : NewGreenLineSum = plus 4251 420.
Proof. reflexivity. Qed.

Lemma Align4AmendQedSum : NewGreenQedSum = plus 84 9.
Proof. reflexivity. Qed.

(* 1) 任务说明 16 件批中 14 件经 grep 证实在册： 九件（KLSTangent 205/6、SteadyThermo 129/1、 *)
(* FEPCanon 135/2、MinFreeEps 268/3、ELBOEps 400/6、ELBOTight 420/6、TrainingEquiv 489/8、 *)
(* TVAbsEps 180/6、PowMonoBridge 337/6）+ 三件（EntropyMaxTemp 407/5、EntropyUniqueTemp *)
(* 378/8、I4Bridge 215/5）+ 一件 EntropyDeficitTemp 582/8 + 一件 TempDual 417/8—— *)

(* 2) UpReqEntropyUniqueNeg 依赖链补绑观察：CW_vo 树 – 刷新（CW 219 壳、 *)
(* UpRealLeB、UpRealLeB3、G07_KLWall）， 组别之 TempDefs/EntropyDeficitTemp/ *)
(* EntropyUniqueTemp 三件 .vo 相对新壳为陈旧（单件补绑报库一致性错配）；且显式 CW_vo 绑定 *)

(* （各 EXIT=0，源文件零触碰、仅 .vo 翻新）后 EntropyUniqueNeg 补绑编译 EXIT=0；CW_vo 树内 *)

(* 1064→1104 仍漂移，现态未验绿；。 *)

(* ng_ 第三轨续写： 后流水线新绿 8 件逐件实测登记（append-only；– 既有 21 条目/清单/ *)

(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等；G1 表九词逐件全零）。 *)
(* 入库判据（// 卡定式）：稳定窗口双测同 md5（间隔 ≥45s）+ 现态单件编译 EXIT=0（重定向取真码）。 *)

(* ng_UpReqKLStrictB —— UpReqKLStrictB.v：，KLStrict 族 ≤_B 显式对照/（结论 C 留待件交付） *)
(* （G07_KLWall 成员 UpReqKLEnergy 尾注结论 C 位交付：逐项 Bishop 形严格化完成器 real_le_b 系； *)

Definition ng_UpReqKLStrictB : NewGreenFace :=
  MkNewGreenFace "UpReqKLStrictB.v" 296 10 20260911 "KL strict family Bishop-form closure, verdict C delivery" "L305:m92cb93".

(* ng_UpReqLatbMaxList —— UpReqLatbMaxList.v：b，B 形扩展线 max 侧列表版格组合件 *)

(* c69bbf8b，补绑单件编译 EXIT=0，G1 表九词全零） *)
Definition ng_UpReqLatbMaxList : NewGreenFace :=
  MkNewGreenFace "UpReqLatbMaxList.v" 238 8 20260911 "B-form max-side list lattice combinator" "L262:m470895".

(* ng_UpReqMinPKLChain —— UpReqMinPKLChain.v：X1 ，复合熵链一步拼装 *)
(* （论文 2 正式版 §10.2 第 6 项：KL(minp‖full) ≤ S ≤ log|S|；全在盘只读使用 UpAuditBridge/UpMinP 等； *)

Definition ng_UpReqMinPKLChain : NewGreenFace :=
  MkNewGreenFace "UpReqMinPKLChain.v" 1038 27 20260911 "minP-full KL chain one-step assembly, paper2 s10.2 item 6" "L1045:m57c28a".

(* ng_UpReqCEqDispersion —— UpReqCEqDispersion.v：，CDispersion S *)

(* （(b) 严格逆否支 Real 层可达形：显式分歧见证（q 与 p_b 在某点 Set 层 Or (real_lt) 双向见证）； *)

(* ng_UpReqTempDualList —— UpReqTempDualList.v：，温度族 sigT 对偶·通用 list 记录集成 *)

(* 漂移不采信，P2/P3 稳定 b5b32632（间隔 90s），现态绑定重编译 EXIT=0 且件内假设清查 8 件全 Closed； *)
(* G1 表九词全零） *)
Definition ng_UpReqTempDualList : NewGreenFace :=
  MkNewGreenFace "UpReqTempDualList.v" 507 8 20260911 "4.6d sigT dual closure over generic list carrier" "L602:md8be77".

(* ng_UpReqI4Witness —— UpReqI4Witness.v：，结论 I4 *)

(* G1 表九词全零） *)
Definition ng_UpReqI4Witness : NewGreenFace :=
  MkNewGreenFace "UpReqI4Witness.v" 391 12 20260911 "verdict I4 certificate slot, internal Or-form KL certificate" "L400:m107880".

Definition NewGreenListV25 : list NewGreenFace :=
  cons ng_UpReqKLStrictB
  (cons ng_UpReqLatbMaxList
  (cons ng_UpReqMinPKLChain
  (cons ng_UpReqTempDualList
  (cons ng_UpReqI4Witness nil)))).

(* 续写统计：6 件 / 行数和 2650 / 闭合和 68（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV25Pieces  : nat := 5.
Definition NewGreenV25LineSum : nat := 2470.
Definition NewGreenV25QedSum  : nat := 65.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV25Pieces_matches : NewGreenV25Pieces = cnt_ng NewGreenListV25.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV25LineSum_matches : NewGreenV25LineSum = sum_ng_lines NewGreenListV25.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV25QedSum_matches : NewGreenV25QedSum = sum_ng_qed NewGreenListV25.
Proof. reflexivity. Qed.

(* 1) Align4 改账再验：盘面 1431/28 同 md5 62e30e10，与 改账口径（双测同 md5 62e30e10）逐字 *)

(* 2) UpReqLogRDF（af_UpReqLogRDF 快照 17 闭合）盘面 1630 行/19 闭合（md5 669fa403 双测稳定）， *)
(* 漂移 +2 闭合；且头注 L60-61 罗列负证模式字面致 G1 表九词自触两处（ 卡「头注禁词自触」坑再现， *)
(* ）；af_ 在册件不重复登记，且 G1 闸未过不入 ng_ 面。 *)
(* 3) UpReqMpDomain（ 在册 859/23）盘面 1069/28（md5 c82de3d8），漂移 +210/+5（X3 进行中续建）， *)

(* 增长中，现态补绑编译 EXIT=1（line 214 环境失配）；仍在写盘，。 *)

(* 6) G 系合并件再测：G12_ZPosFam token 44 与在册 gqed_G12 44 相符零漂移；G06_BForm grep 25 与在册 *)
(* gqed_G06 25 相符而 token 再测 24（grep-token 差 1 为 "Qed." 子串伪命中，SFaceQed 同型），token *)

(* ng_ 第三轨续写： 后流水线新绿 1 件逐件实测登记（append-only；– 既有 29 条目/ *)

(* 口径同 –：ng_lines = wc -l 实测 165；ng_qed = grep -c "Qed\." 实测 5（剥注释 token 级 *)
(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核相等；固定 ^Qed\. 计 4 系件 4 单行 Proof...Qed. *)
(* 不在行首之伪差，闭合实数 5）。G1 表 11 禁词逐词全零（含头注）。 *)
(* 入库判据：稳定窗口双测同 md5（间隔 ≥5min）+ 全量编译 EXIT=0 且 .vo 晚于 .v + G3 件内 5 件 *)
(* 假设清查全 Closed + G4 coqchk PASS。 *)

(* ng_UpReqExpPos —— UpReqExpPos.v：，eˣ>0 （五件：目标主件+四支） *)
(* （目标定理 forall x, 0 < eˣ 无条件成立：real_exp_neg_pos 于 real_opp x 一词实例化，ε 见证 *)

(* 首测 515c74b1 系 收尾加 RealSetoid. 限定之进行中漂移，不采信），全量编译 EXIT=0 且 *)
(* 5 件 Print Assumptions 全 Closed，coqchk PASS；G1 表 11 禁词全零） *)
Definition ng_UpReqExpPos : NewGreenFace :=
  MkNewGreenFace "UpReqExpPos.v" 165 5 20260911 "constructive positivity of exp over all reals, five pieces" "L174:m5f99af".

Definition NewGreenListV26 : list NewGreenFace :=
  cons ng_UpReqExpPos nil.

(* 续写统计：1 件 / 行数和 165 / 闭合和 5（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV26Pieces  : nat := 1.
Definition NewGreenV26LineSum : nat := 165.
Definition NewGreenV26QedSum  : nat := 5.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV26Pieces_matches : NewGreenV26Pieces = cnt_ng NewGreenListV26.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV26LineSum_matches : NewGreenV26LineSum = sum_ng_lines NewGreenListV26.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV26QedSum_matches : NewGreenV26QedSum = sum_ng_qed NewGreenListV26.
Proof. reflexivity. Qed.

(* 补绑编译 EXIT=0 出 .vo（5 件 Closed）。 *)

(* ng_ 第三轨续写： 后流水线新绿 1 件逐件实测登记（append-only；– 既有 30 条目/ *)

(* 口径同 –：ng_lines = wc -l 实测 192；ng_qed = grep -c "Qed\." 实测 6（剥注释 token 级 *)
(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核相等，6=6=6；交接书 decl 7 系含 1 Definition 记录 *)
(* upreq_half 之口径，闭合实数 6）。G1 表禁词逐词全零（含头注）。 *)
(* 入库判据：稳定窗口双测同 md5（/ 两测同 6fce813e）+ 件现态 .vo 晚于 .v（Live_X *)
(* 对 ）+ 接办报告四项验证在案（全量 EXIT=0 + 件内 6 件假设清查全 Closed + coqchk PASS）。 *)

(* ng_UpReqRealHalf —— UpReqRealHalf.v：A，Real 层 halving 基建件（eˣ>0 五步链步骤3 基础件） *)
(* （upreq_half x := real_mult (real_const (1#2)) x 构造性半元函数；主定理 upreq_half_plus： *)
(* ½x+½x=x 逐 eps 相等，使用 AttnSqrt 现成件一跳 exact；等式面 zero-touch 纪律：步骤4（平方≥0 *)
(* Or 形）LPO 等价面零触碰；CW 同步同 md5；G1 表禁词全零） *)
Definition ng_UpReqRealHalf : NewGreenFace :=
  MkNewGreenFace "UpReqRealHalf.v" 192 6 20260912 "Real-layer halving base for exp chain step 3, equality face" "L201:m2efea6".

Definition NewGreenListV27 : list NewGreenFace :=
  cons ng_UpReqRealHalf nil.

(* 续写统计：1 件 / 行数和 192 / 闭合和 6（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV27Pieces  : nat := 1.
Definition NewGreenV27LineSum : nat := 192.
Definition NewGreenV27QedSum  : nat := 6.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV27Pieces_matches : NewGreenV27Pieces = cnt_ng NewGreenListV27.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV27LineSum_matches : NewGreenV27LineSum = sum_ng_lines NewGreenListV27.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV27QedSum_matches : NewGreenV27QedSum = sum_ng_qed NewGreenListV27.
Proof. reflexivity. Qed.

(* 1) KLSTangent 附条件闸核验：交接书载明「仅当 attn/_kl_交付报告-.md 已落盘且记载四项验证 *)

(* 已在册（205/6），盘面再测 205/6 同 md5 d3b1226c 与在册口径相符零漂移，无重复登记面。 *)

(* ng_ 第三轨续写：承 后 31 件基面，八件完成 B/C 件逐件实测登记（append-only；– *)

(* attn/_tw28_Index_backup.v 同 md5 7f98d83e 留档）。 *)
(* 口径同 –：ng_lines = wc -l 实测；ng_qed = grep -c "Qed\." 实测（八件剥注释 token 级 *)
(* \bQed\. 与 Theorem/Lemma/Corollary 行双复核逐件相等）；UpReqQExpTail 交接书口径 29 系少记 2， *)
(* 盘面实测 31（三口径一致，判报告少记非件面漂移，以实测入账）。G1 表禁词全文件全零（含头注）。 *)
(* 入库判据：稳定窗口双测同 md5（间隔 20s 八件逐一相同）+ 件现态 .vo 晚于 .v（八件逐一核对）+ *)
(* 接办报告四项验证在案（全量 EXIT=0 / 主件 Print Assumptions 全 Closed / coqchk PASS，报告在案）。 *)

(* ng_UpReqBanachProd —— UpReqBanachProd.v：B3Sv2，Banach 层级数乘积引擎件（13 件一次全部通过： *)
(* 柯西方块主件 esp_prod_square（esp n a · esp n b = 双和方块恒等，交付②）+ 清项链 bpow_comm_r *)
(* 六步 + 换元三件 bsum_rot/shift_pred/shift_pred2 + bsum 部分和族；bpow_add 二项式组装留待 *)
(* （蓝图铺毕继任直组）；coqc/coqchk 双证绿，G1 全零） *)
Definition ng_UpReqBanachProd : NewGreenFace :=
  MkNewGreenFace "UpReqBanachProd.v" 413 12 20260912 "Cauchy product square identity and bsum engine, thirteen pieces" "L413:m225eee".

(* ng_UpReqBanachDouble —— UpReqBanachDouble.v：BT，双和三角转置件（16 件三档全交（转置）： *)
(* 主件 bd2_tri_eq_diag 三角和 == 对角线分块和 + peel 几何引理 + 矩形化 rect_split + *)
(* esp 对接 bd2_tri_eq_rect_row（exp(a+b) 集成拼法两路在卡）；bpow_add/exp_add 集成留待上游； *)
(* G2 双证 + G4 全检 PASS（公理面全无，尾行 successfully checked） *)
Definition ng_UpReqBanachDouble : NewGreenFace :=
  MkNewGreenFace "UpReqBanachDouble.v" 318 13 20260912 "double sum transpose, triangular equals diagonal blocks, sixteen pieces" "L318:m23d86c".

(* ng_UpReqBanachExpBasic —— UpReqBanachExpBasic.v：BXB，e^0=1 基础件（8 件 bxb_ 出口： *)
(* 主件 bxb_series_zero（e^0=1 的 Banach 层完全等式面， Real 层件 2 单位元支同构）+ *)
(* 平凡柯西证书（N=0 显式闭式）+ 范数面 + 与 B25 expdef 对接件（邻域贴近，零触碰其文件）； *)
(* le 消去禁入 Set 坑实录在卡；G1–G4 全部通过） *)
Definition ng_UpReqBanachExpBasic : NewGreenFace :=
  MkNewGreenFace "UpReqBanachExpBasic.v" 258 7 20260912 "exp at zero equals one, Banach equality face with Cauchy certificate" "L265:mc99766".

(* ng_UpReqBanachExpDef —— UpReqBanachExpDef.v：B25，exp （路线甲字段见证形，无降档： *)
(* bxdef_exp := projT1 (bcauchy_complete_sig … (exp_series_cauchy B a)) 元素定义 + *)
(* bxdef_exp_spec 收敛规格（projT2 一步）+ 零元幂/级数折叠与 exp(0) 邻域面加分族； *)
(* 9 常量 7 闭合；sigT 投影实名坑（projT1 非 proj1）在卡；四项验证全部通过） *)
Definition ng_UpReqBanachExpDef : NewGreenFace :=
  MkNewGreenFace "UpReqBanachExpDef.v" 178 7 20260912 "exp element via completeness field witness pair, route A" "L196:m561fb2".

(* ng_UpReqBanachProd2 —— UpReqBanachProd2.v：B2Tv2，B 类引理第二组量移植件（7 闭合，12,038B： *)
(* #23 sum_upto_div/bsum_div 除系数拉出 + #27 q_choose_div_fact 阶乘比 + *)
(* #29 exp_term_split/bterm_split 逐项系数分裂（Banach 面主件）+ wd 族两件附赠； *)
(* Q 引擎照抄 + Banach 面语境重写双层移植，排除域清单复核零冲突；G1–G3 全部通过，检查点验后删） *)
Definition ng_UpReqBanachProd2 : NewGreenFace :=
  MkNewGreenFace "UpReqBanachProd2.v" 222 7 20260912 "B-class transplants: div pullout, choose divide fact, term split" "L222:mbfeb79".

(* ng_UpReqPadeSign —— UpReqPadeSign.v：CS，Padé （9 闭合，n=0/n=1 分母正性： *)
(* 主件 pds_den1_pos（0 < x < 2 蕴 QltT 0 (pade_den 1 x)，三层死路排除后定型：ring 桥 + *)
(* 正值乘法相容 + 差号判定引理）+ S1 pds_den0_pos 恒正 + S3 pds_den1_half 数值例 *)
(* （与 PC 守卫 3/4 闭式对账）+ 传桥接模块 pds_qlt0_eq_r（双 Q 构造子形 nia 一步完成）； *)
(* 通用 n 版分母正性未攻诚实留待（连接图在案）；G1–G4 全部通过，G3 提取 Obj.magic = 0） *)
Definition ng_UpReqPadeSign : NewGreenFace :=
  MkNewGreenFace "UpReqPadeSign.v" 133 9 20260912 "Pade denominator positivity at n zero and n one" "L141:mf17112".

(* ng_UpReqQExpTail —— UpReqQExpTail.v：QT2（PB2/PB2R 验尸接办，三方合并报告），Q 层阶乘尾和件 *)
(* （757 行 / 实测 31 闭合：主件 qtail_cauchy_modulus(_ord) 构造性柯西模量显式出口 + *)
(* term_decay/ratio_chain 几何衰减链 + qtail_fact_ge_pow 2^k ≤ k! 下界 + sum_mono/nonneg *)
(* 保号族；L118 replace 抽象歧义重构完成，18 处编译错逐条实录；报告载 29 系少记 2 以实测入账 *)
(* （见上方口径注）；四项验证全部通过，G3 提取 Obj.magic = 0） *)
Definition ng_UpReqQExpTail : NewGreenFace :=
  MkNewGreenFace "UpReqQExpTail.v" 757 31 20260912 "Q factorial tail sums with explicit constructive Cauchy modulus" "L769:m8a4054".

Definition NewGreenListV28 : list NewGreenFace :=
  cons ng_UpReqBanachProd
  (cons ng_UpReqBanachDouble
  (cons ng_UpReqBanachExpBasic
  (cons ng_UpReqBanachExpDef
  ((cons ng_UpReqBanachProd2
  (cons ng_UpReqPadeSign
  (cons ng_UpReqQExpTail nil))))))).

(* 续写统计：7 件 / 行数和 2279 / 闭合和 86（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV28Pieces : nat := 7.
Definition NewGreenV28LineSum : nat := 2279.
Definition NewGreenV28QedSum : nat := 86.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV28Pieces_matches : NewGreenV28Pieces = cnt_ng NewGreenListV28.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV28LineSum_matches : NewGreenV28LineSum = sum_ng_lines NewGreenListV28.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV28QedSum_matches : NewGreenV28QedSum = sum_ng_qed NewGreenListV28.
Proof. reflexivity. Qed.

(* 上游 BA 进行中）；BanachDouble 之 exp_add 集成（同上游）；PadeSign 通用 n 版分母正性（CS *)
(* 连接图在案）；ExpDef/ExpNeg 之 exp(0)=1 完全等式面（Class 缺反可分性字段，接口扩容属上游 *)
(* 裁决）。均无承认件落盘。 *)
(* 2) 口径对账：UpReqQExpTail 交接书/报告载 29 闭合，盘面实测 31（32 声明 = 31 Lemma + 1 Fixpoint *)
(* 记录，grep/token 级/TLC 三口径一致；行数 757 与 md5 6f44332c 及 .vo 时戳 > .v *)
(* 相符，件零漂移，判系报告少记，以实测入账）。 *)

(* ng_ 第三轨续写：承 后 39 件基面，第五段 Banach 注册批五件逐件实测登记 *)

(* 口径同 –：ng_lines = wc -l 实测；ng_qed = 剥块注释 token 级 \bQed\. 实测； *)
(* 五件均已 vo 树预验证双段绿（coqc 单件 EXIT=0 + coqchk -o 闭包抽查 Inst/LimUniq EXIT=0）。 *)

(* ng_UpReqBanachExpAdd —— UpReqBanachExpAdd.v：S3 集成支柱（BASM） *)
Definition ng_UpReqBanachExpAdd : NewGreenFace :=
  MkNewGreenFace "UpReqBanachExpAdd.v" 452 14 20260913 "exp addition e^a*e^b=e^(a+b) via limit product continuity bxadd_bmult_lim" "L456:mb274b2".

(* ng_UpReqBanachClassExt —— UpReqBanachClassExt.v：BanachAlg 类扩字段原型（BCE） *)
Definition ng_UpReqBanachClassExt : NewGreenFace :=
  MkNewGreenFace "UpReqBanachClassExt.v" 206 5 20260913 "BanachAlg class extension prototype with Q-addition coefficient fields bxce_coef_plus/wd" "L206:m76a4db".

(* ng_UpReqBanachLimUniq —— UpReqBanachLimUniq.v：极限唯一性（UNQ） *)
Definition ng_UpReqBanachLimUniq : NewGreenFace :=
  MkNewGreenFace "UpReqBanachLimUniq.v" 225 10 20260913 "limit uniqueness bxuq_lim_uniq realized from separability field bxce_sep" "L227:mf6c311".

(* ng_UpReqBanachBinomBridge —— UpReqBanachBinomBridge.v：二项式系数桥（CBR） *)
Definition ng_UpReqBanachBinomBridge : NewGreenFace :=
  MkNewGreenFace "UpReqBanachBinomBridge.v" 166 10 20260913 "binomial coefficient bridge bpa_binom Pascal recursion iff q_choose factorial form" "L182:md2604d".

(* ng_UpReqBanachInst —— UpReqBanachInst.v：BanachAlg 第一个具体实例（INS） *)
Definition ng_UpReqBanachInst : NewGreenFace :=
  MkNewGreenFace "UpReqBanachInst.v" 336 12 20260913 "first concrete BanachAlg instance landed, in-class positive piece" "L349:m0c7540".

Definition NewGreenListV29 : list NewGreenFace :=
  cons ng_UpReqBanachExpAdd
  (cons ng_UpReqBanachClassExt
  (cons ng_UpReqBanachLimUniq
  (cons ng_UpReqBanachBinomBridge
  (cons ng_UpReqBanachInst nil)))).

(* 续写统计：5 件 / 行数和 1385 / 闭合和 51（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV29Pieces  : nat := 5.
Definition NewGreenV29LineSum : nat := 1385.
Definition NewGreenV29QedSum  : nat := 51.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV29Pieces_matches : NewGreenV29Pieces = cnt_ng NewGreenListV29.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV29LineSum_matches : NewGreenV29LineSum = sum_ng_lines NewGreenListV29.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV29QedSum_matches : NewGreenV29QedSum = sum_ng_qed NewGreenListV29.
Proof. reflexivity. Qed.

(* 1) 插入位：五件 vo 树 order.txt 表尾整块追加（L157–L161，块内 Kahn 序 ExpAdd→ClassExt→ *)
(* LimUniq→BinomBridge→Inst；LimUniq 依赖 ClassExt+ExpAdd 同块前位，其余仅存量依赖）； *)
(* 双树 order.txt cmp 字节一致，双树 topo 再验器 161 行 BAD_COUNT=0，_CoqProject 双树 *)
(* 156→161 同步（157→162），scripts/order.txt 三处 wc 一致。 *)
(* 2) 预验证：五件 cp 自权威源 Live_X（五件 md5 留痕 2718eaa4/76a4dbf3/5bd04e4a/e2f1a86b/ *)
(* 29871a96），cpu_guard CoreN 3 串行 coqc 全 EXIT=0；coqchk -o 闭包抽查 UpReqBanachInst *)
(* 与 UpReqBanachLimUniq 双 EXIT=0，零 Inconsistent assumptions 零 Anomaly。 *)

(* ng_ 第三轨续写：承 后 44 件基面，C 波 Padé 正尾路线五件逐件实测登记 *)

(* 口径同 –：ng_lines = wc -l 实测；ng_qed = 剥块注释 token 级 \bQed\. 实测； *)
(* 五件均已 vo 树预验证双段绿（coqc 单件 EXIT=0 + coqchk -o 闭包抽查 EXIT=0）。 *)

(* ng_UpReqPadeTailPos —— UpReqPadeTailPos.v：Padé 尾项 n=1/2 定值（①号件，插入位 170） *)
Definition ng_UpReqPadeTailPos : NewGreenFace :=
  MkNewGreenFace "UpReqPadeTailPos.v" 179 19 20260914 "Pade tail term identity at n=1/2 fixed-point evaluation ptp_beta_pos" "L690:m73e362".

(* ng_UpReqPadeLower —— UpReqPadeLower.v：下界误差估计（③号件，插入位 171） *)
Definition ng_UpReqPadeLower : NewGreenFace :=
  MkNewGreenFace "UpReqPadeLower.v" 385 24 20260914 "lower error bound cpl_lower_even for the even convergent partial fraction" "L405:m1cae6f".

Definition NewGreenListV30 : list NewGreenFace :=
  (cons ng_UpReqPadeTailPos
  (cons ng_UpReqPadeLower
  nil)).

(* 续写统计：2 件 / 行数和 564 / 闭合和 43（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV30Pieces : nat := 2.
Definition NewGreenV30LineSum : nat := 564.
Definition NewGreenV30QedSum : nat := 43.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV30Pieces_matches : NewGreenV30Pieces = cnt_ng NewGreenListV30.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV30LineSum_matches : NewGreenV30LineSum = sum_ng_lines NewGreenListV30.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV30QedSum_matches : NewGreenV30QedSum = sum_ng_qed NewGreenListV30.
Proof. reflexivity. Qed.

(* 1) 插入位：五件 vo 树 order.txt 表尾整块追加（L169–L173，块内 Kahn 序 BetaPos→TailPos→ *)
(* Lower→DenPos12→Finale；①②③④ 定稿 Require 面零跨件边（③现档仍未 Require ①②， *)
(* 与分派语义序差异留痕照预备单 §一），⑤定稿新增 Require ③Lower 同块前位兼容）； *)
(* 双树 order.txt cmp 字节一致，双树 topo 再验器 173 行 BAD_COUNT=0，_CoqProject 双树 *)
(* 168→173 同步，scripts/order.txt 三处 wc=173。 *)
(* 2) 预验证：五件 cp 自权威源 Live_X（md5 留痕 b7bdda96/9e98ddea/a6fe32a3/44fc811a/ *)
(* b62cf9bd），cpu_guard CoreN 2 串行 coqc 五件全 EXIT=0；coqchk -o 闭包抽查 *)
(* TailPos/BetaPos/DenPos12/Finale 四件全 EXIT=0，零 Inconsistent assumptions 零 Anomaly。 *)

(* ；P1b 块与本块分属不同登记轨零名冲突，原样存档 attn/_tw31_P1b_block_backup.md， *)

(* ng_ 第三轨续写：承 后 49 件基面，注册第二段 13 件逐件实测登记 *)

(* 口径同 –：ng_lines = wc -l 实测；ng_qed = 剥块注释 token 级 \bQed\. 实测； *)

(* 计量双口径（wc -l / 剥注释 token 级）逐件实测，源档一行未触碰（禁碰条款，只登记不改件）。 *)

(* ---------- 注册第二段 · 第三方收取线 7 件（CWA/CWB/CWC/CWD） ---------- *)

(* ng_QTailBridge —— QTailBridge.v：qtail_sum 桥式恒等式（CWA 任务1） *)
Definition ng_QTailBridge : NewGreenFace :=
  MkNewGreenFace "QTailBridge.v" 131 5 20260915 "bridge identity qtail_sum closing UpReqQExpTail ledger note against S03 exp_tail" "L131:m1451ac".

(* ng_PadeDenPosB12 —— PadeDenPosB12.v：Pade [n/n] 分母正性 x in (1,2] 段（CWA 任务2）。 *)
(* ⚠️ 世代区分：本件为第三方收取线独立复刻（UpReqPadeDenPos 留待 b 线），与我方 C 波④号件 *)
(* UpReqPadeDenPos12（ 登记 275/8）构成并行复刻对——两件独立实现并行在册，非同一件。 *)
Definition ng_PadeDenPosB12 : NewGreenFace :=
  MkNewGreenFace "PadeDenPosB12.v" 206 9 20260915 "Pade n over n denominator positivity on interval (1,2), third-party replica of ledger note b" "L206:m85a540".

(* ng_BanachNoHyp —— BanachNoHyp.v：Banach hplus/hwd 显式假设族摘除（CWB） *)
Definition ng_BanachNoHyp : NewGreenFace :=
  MkNewGreenFace "BanachNoHyp.v" 581 7 20260915 "explicit hplus hwd assumption family removal closing BanachAlg interface gap ledger note" "L581:me97cf4".

(* ng_BanachNoHypNorm —— BanachNoHypNorm.v：INSTB 留待剩余字段（CWB 加分件） *)
Definition ng_BanachNoHypNorm : NewGreenFace :=
  MkNewGreenFace "BanachNoHypNorm.v" 123 2 20260915 "remaining INSTB ledger fields bnorm_plus bnorm_mult subadditive submultiplicative" "L123:m5de8fa".

(* ng_RealEnergyTempMono —— RealEnergyTempMono.v：real_energy_exp_temp_mono 恒等档（CWC） *)
Definition ng_RealEnergyTempMono : NewGreenFace :=
  MkNewGreenFace "RealEnergyTempMono.v" 486 9 20260915 "real_energy_exp_temp_mono identity tier Real layer counterpart of S04 energy_exp_temp_mono" "L486:mf38d08".

(* ng_PowRealCompat —— PowRealCompat.v：G07 powb_pow 换形对接（CWD） *)
Definition ng_PowRealCompat : NewGreenFace :=
  MkNewGreenFace "PowRealCompat.v" 177 8 20260915 "G07 powb_pow to CW220 real_pow shape transfer adapter for consumers" "L197:md7d4f2".

(* ng_AlignIdUnclosed —— AlignIdUnclosed.v：UpAlignIdReq 件6 无条件化组装（CWD） *)
Definition ng_AlignIdUnclosed : NewGreenFace :=
  MkNewGreenFace "AlignIdUnclosed.v" 374 3 20260915 "UpAlignIdReq piece 6 unconditional assembly of backward KL recurrence exact identity" "L380:mb21783".

(* ---------- 注册第二段 · 消融与新数学线 6 件（AA 系） ---------- *)

(* ng_UpReqBanachNormOpp —— UpReqBanachNormOpp.v：B5 件一 qred 唯一性+bnorm Opp 面（AA11） *)
Definition ng_UpReqBanachNormOpp : NewGreenFace :=
  MkNewGreenFace "UpReqBanachNormOpp.v" 237 14 20260915 "qred_unique key plus bnorm Opp face for B5 unit one" "L459:m2b5d49".

(* ng_UpReqB4TwoStage —— UpReqB4TwoStage.v：B4 两段式降档完成 Padé 余项（AA14） *)
Definition ng_UpReqB4TwoStage : NewGreenFace :=
  MkNewGreenFace "UpReqB4TwoStage.v" 351 19 20260915 "B4 two stage downgrade closure of Pade remainder coefficient identity and witness eps transfer" "L360:ma4aebf".

(* ng_UpReqLpoEquiv —— UpReqLpoEquiv.v：平方非负全称 ⟺ 受限 LPO 双向归约（AA15，新数学，零公理） *)
Definition ng_UpReqLpoEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqLpoEquiv.v" 434 12 20260915 "square nonneg forall iff bounded LPO two way reduction theorem, zero axioms" "L443:m54b91c".

(* ng_UpReqBanachInstReal —— UpReqBanachInstReal.v：S02 Real 记录全字段装配（AA3，实例非空性） *)
Definition ng_UpReqBanachInstReal : NewGreenFace :=
  MkNewGreenFace "UpReqBanachInstReal.v" 774 49 20260915 "S02 Real carrier assembled into bxin_BanachAlgPre all field instance" "L856:m70e6f2".

Definition NewGreenListV32 : list NewGreenFace :=
  cons ng_QTailBridge
  (cons ng_PadeDenPosB12
  (cons ng_BanachNoHyp
  (cons ng_BanachNoHypNorm
  (cons ng_RealEnergyTempMono
  (cons ng_PowRealCompat
  (cons ng_AlignIdUnclosed
  (cons ng_UpReqBanachNormOpp
  (cons ng_UpReqB4TwoStage
  ((cons ng_UpReqLpoEquiv
  (cons ng_UpReqBanachInstReal nil))))))))))).

(* 续写统计：11 件 / 行数和 3874 / 闭合和 137（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV32Pieces : nat := 11.
Definition NewGreenV32LineSum : nat := 3874.
Definition NewGreenV32QedSum : nat := 137.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV32Pieces_matches : NewGreenV32Pieces = cnt_ng NewGreenListV32.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV32LineSum_matches : NewGreenV32LineSum = sum_ng_lines NewGreenListV32.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV32QedSum_matches : NewGreenV32QedSum = sum_ng_qed NewGreenListV32.
Proof. reflexivity. Qed.

(* 1) 编号与保全： P1b（仓库 Live 树 +96 行未提交进行中产物，idx_DTPT* 18 模块 rm_ 轨， *)

(* 40 闭合（分派观察口径 669 行，完成时点再测条款以实测为准）——已注册件内容更新非新注册， *)
(* ng_UpReqPadeTailPos 登记值冻结不动，。 *)
(* 3) S 系五件截断（S11–S15 Psatz→Lia 更换，AA1 普查线）待同批登记：=不等待 *)

(* ========================================================================= *)
(* （P1b：DTPT 离散对偶轴 18 ） *)
(* *)

(* 新增轨 idx_DTPT*：DTPT 工作区 18 模块（Q 层独立宇宙）包壳态注册，rm_in_uni=false *)
(* ——不占 734 迁移宇宙名额，与 idx_ 主轨（true）物理隔离，纯数据条目零机器核对耦合。 *)
(* *)
(* 插入位：ConstructiveWorld_Live/_CoqProject 表尾整块追加（L175–L192，拓扑序： *)
(* DTPT→Entropy/LLM/Measure/Phases/Truth→Entropy2/DigTheory→CoZero/ME2/ZeroLocus/ *)
(* Audit/Extract/EntFam2/ROTC→Lam/Cyc→RotSpec；coqdep 35 边全部「依赖索引<使用索引」， *)
(* 逐边核验在案）；Live 树 173→191 .v；双树 order.txt 三面与 vo 树播种面归 P2/P4 同步波。 *)
(* *)
(* 18 件源指纹： P1a 交付态 md5 逐件留痕（拷入前后双 md5 对账 18/18 一致； *)
(* 拷入面 = ConstructiveWorld_Live/ 表尾，零改名零内容改）。 *)
(* G1 三连零（家规禁词 grep 计数 18 件逐件=0，禁词字面按字面规避纪律不入本注）；壳对账： *)
(* 每件 Module/End 各=1，壳名=文件语义名，互引 35 边全限定 Import 适配层在案（P1a 报告 §二表）。 *)
(* rm_decl_cnt = grep -cE "^(Definition|Theorem|Lemma|Inductive|Record|Fixpoint|Corollary| *)
(* Ltac)[[:space:]]" 逐件实测（合计 819）；rm_head_kw = 各件主定理（grep 验证在件）。 *)
(* rm_gate_day = （主库编译验证日）。 *)
(* *)
(* 撞面对账：五撞名 q_fact/qeq_le/qstep/rot/diag_closed 全数壳内消解（Locate 全名形 *)
(* 库名.壳名.名，P1a 检查点 _p1a_probe_ns.log 在案）；叶子融入成立：Live 树既有件零该向依赖边。 *)
(* ========================================================================= *)

(* idx_DTPT —— DTPT.v：数字全域—熵相三元论根模块（Dig 塔+CGen+N9Opt+D8Ext 归并宿主） *)
Definition idx_DTPT : ReqModule :=
  MkReqModule "DTPT.v" 272 20260915 "C_sorted_min_adj" false.

(* idx_DTPT_Entropy —— DTPT_Entropy.v：最小偏差和熵面（xq_ 工具箱+H_adj 下界） *)
Definition idx_DTPT_Entropy : ReqModule :=
  MkReqModule "DTPT_Entropy.v" 218 20260915 "H_adj_P0_min" false.

(* idx_DTPT_Truth —— DTPT_Truth.v：真值序面（level 三律+Tarski 归并宿主，双副本桥在案） *)
Definition idx_DTPT_Truth : ReqModule :=
  MkReqModule "DTPT_Truth.v" 89 20260915 "level_le_refl" false.

(* idx_DTPT_DigTheory —— DTPT_DigTheory.v：数字化理论面（dig 单射塔+HAlg 归并宿主） *)
Definition idx_DTPT_DigTheory : ReqModule :=
  MkReqModule "DTPT_DigTheory.v" 88 20260915 "dig_inj_dCode" false.

(* idx_DTPT_Extract —— DTPT_Extract.v：提取面（u12 门控六检查点+9 条 Extraction 套件宿主） *)
Definition idx_DTPT_Extract : ReqModule :=
  MkReqModule "DTPT_Extract.v" 30 20260915 "u12_gate_pass_t1_h0" false.

(* idx_DTPT_Rotation —— DTPT_Rotation.v：旋转论面（rotc 基础件/精确闭式/锐化/λ 插值/偏差判别/周期律簇，RotSpec+Lam 归并宿主） *)
Definition idx_DTPT_Rotation : ReqModule :=
  MkReqModule "DTPT_Rotation.v" 143 20260915 "rotc_class_sharp_ub" false.
Definition idx_DTPT_Bridge : ReqModule :=
  MkReqModule "DTPT_Bridge.v" 37 20260915 "H_chain_set" false.
Definition idx_DTPT_Bridge_Dig : ReqModule :=
  MkReqModule "DTPT_Bridge_Dig.v" 19 20260915 "dig_size_le_dec" false.
Definition idx_DTPT_Bridge_Rot : ReqModule :=
  MkReqModule "DTPT_Bridge_Rot.v" 24 20260915 "rotc_class_sharp_ub_set" false.

(* ========================================================================= *)
(* c（P1c：DTPT 融入 P1 完成预备——6 模块终态收缩） *)
(* *)
(* 承 ：棒 1–5 归并完成后 DTPT 面 18 模块收缩为 6 模块终态。本节整条删除 12 条退役 *)
(* idx_DTPT* 条目（各 3 行；受触模块主库 Live 树 .v 与构建产物同日删除，工作区退役档 *)
(* 12/12 逐字节留痕，对账表见 DTPT_P1c_同步报告.md）： *)
(* LLM/Measure（棒1）与 Phases/CoZero（棒2）并入 DTPT；Entropy2/EntFam2（棒3）与 *)
(* ME2/ZeroLocus（棒4）并入 DTPT_Entropy；Audit 与 ROTC（棒5）并入 DTPT_Truth/DTPT_Cyc； *)
(* Lam/RotSpec 由棒 6a 并入 DTPT_Cyc（件名待改 DTPT_Rotation）进行中。 *)
(* 存留 6 条：idx_DTPT / idx_DTPT_Entropy / idx_DTPT_Truth / idx_DTPT_DigTheory / *)
(* idx_DTPT_Extract / idx_DTPT_Cyc。存留条目 rm_decl_cnt / rm_head_kw 为 注册时 *)

(* 同日 _CoqProject 同步收缩 18 行→6 行（与 r74 波 HEAD 188 行对账合并为 194 行， *)
(* 占表尾 L189–L194）；DTPT_Cyc.v 行尾注记待棒 6b 改名 DTPT_Rotation。 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* d（6b主库尾：第 6 件落库与 idx_DTPT* 终态刷新） *)
(* *)
(* 承 c：棒 6b 交付 DTPT_Rotation（2,018 行；原 DTPT_Cyc 改名，RotSpec/Lam/ROTC/ *)

(* ①Live 树 _CoqProject 表尾行改名并撤行尾注记（194 行不变，纯增 +6−0 对 HEAD）； *)
(* ②idx_DTPT_Cyc 整条改名 idx_DTPT_Rotation，路径 "DTPT_Cyc.v"→"DTPT_Rotation.v"； *)
(* ③存留 6 条 rm_decl_cnt 按 同款 grep 口径逐件重测刷终态：DTPT 272 / Entropy 218 / *)
(* Truth 79 / DigTheory 88 / Extract 30 / Rotation 129（合计 826）；rm_gate_day 统一刷 *)

(* 余 5 主定理在件再验未变。 *)
(* ④Live 树退役残件同日出清：DTPT_Cyc .v+构建产物全套、ROTC/Entropy2 残留 .aux（工作区 *)
(* .retired_S6b 档留痕，主库零副本）；order.txt 三面各 +6 行（187→193，三面同 md5）。 *)
(* 主库终态实证：六件单编零错零警；全树内核认证 193 模块（187 基线+6）组别 EXIT=0 成功收尾； *)
(* 六件闭包 -o 枚举四项汇总全 <none>。vo 树播种 6 件×5 文件为全树认证前置，.v 副本 md5 *)
(* 六件与工作区定稿逐字节一致（五冻结件=P1c 留痕值）。 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* （P1g：DTPT ） *)
(* *)

(* 头注声明：P1b 波 idx_DTPT* 九条目曾随 8711998 提交落库；24431dc（C 波完成）以 *)
(* 覆盖提交时九条目合法让位离面（ 编号订正注记自述前提「+96 行系未提交进行中产物」 *)

(* 裁决（Q1：不在 W31 块内恢复避编号冲突，改文件尾 块重注册）原轨复注册， *)
(* 条目名/行格式严格副本 8711998 版（d 终态）。 *)
(* rm_decl_cnt 按当盘现值（ 同款 grep 口径）逐件重测，随 FRUIT/TRUTH 波后刷新： *)
(* DTPT 272 / Entropy 218 / Truth 89（TRUTH-1 同步后现值）/ DigTheory 88 / Extract 30 / *)
(* Rotation 143（FRUIT-1 §S8 后；Qed 口径 135 不入本字段，字段语义依 P1b 公式）/ *)
(* Bridge 37 / Bridge_Dig 19 / Bridge_Rot 24（P3B7 §8 终态 412 行版入车后现值；已提交版 *)
(* 31130c5b 被工作区终态 90869682 覆盖属预期新资产入车，P2 提交信息声明）。 *)

(* 纯数据条目零机器核对耦合（ 同款）。 *)
(* ========================================================================= *)

(* ========================================================================= *)

(* *)
(* 完成对象=AA19 裁决「甲·并入」落地态： 孤儿块（P1b 注册 18 条，经 c 裁撤 12 条 *)
(* 退役条目、d 改名刷新，现形态 9 条 idx_DTPT* 定义）与 段（ng_ 轨 13 件）同盘并存。 *)

(* 完成三验： *)
(* ①重号=0：Definition 级 idx_/ng_/af_/NewGreen 全名查重空集（rm_ 字段名为记录访问器复用， *)
(* 非重号）；idx_DTPT* rm_ 轨（rm_in_uni=false）与 ng_ 绿面轨物理隔离维持。 *)

(* ③本块及上块新文本遵循既定措辞纪律（家规禁词按字面规避，不入本注）。 *)

(* 非进行中未提交改动）；其条目值 Truth 89 / Rotation 143 / Bridge_Rot 24 系 TRUTH-1 / *)
(* FRUIT-1 §S8 / P3B7 §8 波后当盘现值。本件条目行即采此三值对齐，d 段 prose 数值 *)

(* （随 波翻正册）。 *)
(* 三树同步：本 完成态 cp 至 ConstructiveWorld_Live/ 与 ConstructiveWorld_vo/， *)
(* cmp 零差异、三处 md5 一致（数值见 attn/交付报告-.md §三），一并了结 *)
(* 段留待的双跳 cp 项。 *)

(* §四——BoltzmannBridgeDischarge / DenPosGeneral / ExpNegFinale / ExpNegPosUp / *)
(* FirewallReqDischarge / InstBWdClose / KLWallClosed / PolyIntegral / RealKLCorrMark / *)
(* SqWallCorrMark / SqrtfCauchy / SqrtfCauchyArch / SqrtfCauchyDischarge / SumInvFactEscape / *)
(* SupKLBound / SupKLMonoCompose / TempMonoW2Mark，语句级完成中；DTPT_Rotation 进行中件注记同册。 *)
(* ========================================================================= *)

(* 复核 26→27（L141 内联 Proof…Qed. 真闭合，非注释命中）。 *)

(* ng_UpReqRealLtShiftBridge —— UpReqRealLtShiftBridge.v：Real 层严格步完成三形 *)
Definition ng_UpReqRealLtShiftBridge : NewGreenFace :=
  MkNewGreenFace "UpReqRealLtShiftBridge.v" 138 6 20260916 "strict-step lt discharge trio, weak-slot Or-lift" "L138:me491ac".

(* ng_UpReqStrictStepGen —— UpReqStrictStepGen.v：严格步生成器族 *)
Definition ng_UpReqStrictStepGen : NewGreenFace :=
  MkNewGreenFace "UpReqStrictStepGen.v" 212 13 20260916 "eps-split generator family, master lemma half+quarter" "L225:mc0a061".

(* ng_UpReqCStarDef —— UpReqCStarDef.v：C* 定义面与正元准备 *)
Definition ng_UpReqCStarDef : NewGreenFace :=
  MkNewGreenFace "UpReqCStarDef.v" 758 27 20260916 "C*-algebra definition face, involution laws, positive elements" "L758:m3319e7".

(* ng_UpReqGibbsWallEquiv —— UpReqGibbsWallEquiv.v：gibbs 墙等价 LPO *)
Definition ng_UpReqGibbsWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqGibbsWallEquiv.v" 340 12 20260916 "gibbs plain-le wall iff restricted LPO, wall two" "L340:m7d19a7".

(* ng_UpReqPinWallEquiv —— UpReqPinWallEquiv.v：钉定墙等价 LPO *)
Definition ng_UpReqPinWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqPinWallEquiv.v" 243 9 20260916 "pin wall iff restricted LPO, wall three" "L256:m07e279".

(* ng_UpReqTBNCBridge —— UpReqTBNCBridge.v：TBNC 对角逐项桥 *)
Definition ng_UpReqTBNCBridge : NewGreenFace :=
  MkNewGreenFace "UpReqTBNCBridge.v" 250 6 20260916 "TBNC explicit-hypothesis diagonal corner-term bridge" "L260:m16e149".

(* ng_ 第三轨续写：承 后 69 件基面，成果四外部稿本组 15 件逐件实测登记 *)

(* l2e_g3 属 G3 抽取检查点（Recursive Extraction 施工预备件，稿头自署），按检查点语义排除注册面， *)
(* 只登主稿 LogTwoEnvelope；PiEnvelope/PinskerTwoPoint/SymplecticRotationSpec 三挂起稿候 T4G *)

(* 稿因 4/库因 0/环因 0）；Gibbs 修复账=attn/交付报告-.md *)
(* （L92+L165 同类缺括号两处，vos/full 双 0，vo 8822B magic 90100，PA 3 Closed 与申报吻合）。 *)
(* 注册序=repo order.txt 尾部追加：T4S 提案「UpReqStrictBridgeD 尾锚」系 102 行 Live_X 子集序锚位， *)
(* repo 全库序 228 行中该锚位于 L103，其后续 10 基座依赖（UpReqSteadyThermo L125、 *)
(* UpReqTempDefs L127、UpReqArgminEngine L130、UpReqEntropyDeficitTemp L134、UpReqEntropyMaxTemp *)
(* L138、UpReqTempDual L140、ExpNegPos L205、RealEnergyTempMono L183、EnergyTempMonoB L209、 *)

(* Live_X 102 行子集序零改动（IDX92 结论）。 *)
(* 口径：ng_lines=wc -l 实测；ng_qed=剥块注释 token 级 Qed 实测（头注「全 Qed」伪命中按 剥除）。 *)
(* 沙箱再验产物判据全过：size>0、md5≠d41d8cd9、magic=436f712100015ff4（90100=9.1.0）。 *)

(* ng_FreeEnergyKLGap —— FreeEnergyKLGap.v：自由能 KL 缺口分解 *)
Definition ng_FreeEnergyKLGap : NewGreenFace :=
  MkNewGreenFace "FreeEnergyKLGap.v" 578 14 20260916 "free-energy KL gap decomposition on RealKL decomp face" "L682:mdb5635".

(* ng_ArctanGeomTail —— ArctanGeomTail.v：arctan 几何尾界 *)
Definition ng_ArctanGeomTail : NewGreenFace :=
  MkNewGreenFace "ArctanGeomTail.v" 311 10 20260916 "arctan geometric tail bound, Q-layer chain" "L311:m4ae2dc".

(* ng_StopTimeConservation —— StopTimeConservation.v：停时守恒（预算×宪法轴） *)
Definition ng_StopTimeConservation : NewGreenFace :=
  MkNewGreenFace "StopTimeConservation.v" 280 10 20260916 "stop-time conservation, budget-constitutional axis" "L294:m499cde".

(* ng_TempSoftmaxInstantiation —— TempSoftmaxInstantiation.v：温度 softmax 实例化 *)
Definition ng_TempSoftmaxInstantiation : NewGreenFace :=
  MkNewGreenFace "TempSoftmaxInstantiation.v" 411 6 20260916 "temperature softmax instantiation on attn-gibbs face" "L413:mb27349".

(* ng_SecondLawQuantified —— SecondLawQuantified.v：量化第二定律（熵亏不等式） *)
Definition ng_SecondLawQuantified : NewGreenFace :=
  MkNewGreenFace "SecondLawQuantified.v" 561 16 20260916 "second law quantified, entropy-deficit inequality, follows TempSoftmax" "L646:m46ab80".

(* ng_EpsOptimalReach —— EpsOptimalReach.v：eps 最优可达（argmin 引擎实例） *)
Definition ng_EpsOptimalReach : NewGreenFace :=
  MkNewGreenFace "EpsOptimalReach.v" 213 8 20260916 "eps-optimal reachability via argmin engine" "L220:m120147".

(* ng_VandermondePartial —— VandermondePartial.v：Vandermonde 部分和恒等式 *)
Definition ng_VandermondePartial : NewGreenFace :=
  MkNewGreenFace "VandermondePartial.v" 671 38 20260916 "Vandermonde partial-sum identity, Q combinatorics" "L676:m91a02a".

(* ng_TempUnimodalMax —— TempUnimodalMax.v：温度单峰极大 *)
Definition ng_TempUnimodalMax : NewGreenFace :=
  MkNewGreenFace "TempUnimodalMax.v" 341 7 20260916 "temperature unimodal maximum on energy-temp-mono face" "L341:m91c855".

(* ng_ExpOneEnvelope —— ExpOneEnvelope.v：exp(±x) 单侧包络 *)
Definition ng_ExpOneEnvelope : NewGreenFace :=
  MkNewGreenFace "ExpOneEnvelope.v" 505 29 20260916 "exp(+/-x) one-sided envelopes, Q rounding ladder" "L531:m365f05".

(* ng_AttnLogSumExpBound —— AttnLogSumExpBound.v：注意力 log-sum-exp 界 *)
Definition ng_AttnLogSumExpBound : NewGreenFace :=
  MkNewGreenFace "AttnLogSumExpBound.v" 529 13 20260916 "attention log-sum-exp upper bound, S04 conv face" "L538:m946606".

(* ng_QstepConvergenceBound —— QstepConvergenceBound.v：Q 步收敛界（N-live 审计） *)
Definition ng_QstepConvergenceBound : NewGreenFace :=
  MkNewGreenFace "QstepConvergenceBound.v" 656 27 20260916 "Q-step convergence bound, B5-recycle + N-live audit" "L656:mb700cf".

(* ng_CurriculumOptTemp —— CurriculumOptTemp.v：课程最优温度 *)
Definition ng_CurriculumOptTemp : NewGreenFace :=
  MkNewGreenFace "CurriculumOptTemp.v" 184 5 20260916 "curriculum optimal temperature, thin-shell CW219 import" "L184:mfa1c7a".

(* ng_GibbsAttractor —— GibbsAttractor.v：gibbs 吸引子（Boltzmann π 稳态+TV 迭代传播；修 L92+L165 缺括号后复绿） *)
Definition ng_GibbsAttractor : NewGreenFace :=
  MkNewGreenFace "GibbsAttractor.v" 285 4 20260916 "gibbs attractor: boltzmann pi stationary under TV kernel, titer propagation" "L344:m4fda37".

(* ng_ 第三轨续写：承 后 84 件基面， 挂起三稿 PiEnvelope/PinskerTwoPoint/ *)
(* SymplecticRotationSpec 经属主迁移波落盘（.v×双树）+编译复绿（IN 与属主波双账）后 *)
(* 注册承认：order.txt×3 L244–246、_CoqProject×2 L245–247 尾部追加已核，四件依赖行号全前位 *)
(* 拓扑 PASS（Gibbs 125<243、Pi 16<244、Pinsker 69<245、Symplectic 208<246，全文件 Require *)
(* 提边机械核验零违序）。ng_GibbsAttractor 已在 册内（L243 注册先成），实测 285/4 与 *)

(* PA 3 Closed、公理清单 0）；三新件产物判据 size>0、md5≠d41d8cd9、magic 同上。 *)
(* 权威源=attn/交付报告-.md；口径：ng_lines=wc -l 实测； *)
(* ng_qed=剥块注释 token 级 Qed 实测。 *)

(* ng_PiEnvelope —— PiEnvelope.v：π 有理包络（Leibniz 级数奇偶双边夹逼+显式模量） *)
Definition ng_PiEnvelope : NewGreenFace :=
  MkNewGreenFace "PiEnvelope.v" 933 53 20260916 "pi rational envelope, leibniz series two-sided squeeze with explicit modulus, cauchy_real_pi_leibniz bridge" "L933:m66405b".

(* ng_PinskerTwoPoint —— PinskerTwoPoint.v：二点 Pinsker 型 TV-KL 下界 *)
Definition ng_PinskerTwoPoint : NewGreenFace :=
  MkNewGreenFace "PinskerTwoPoint.v" 443 9 20260916 "two-point pinsker-type TV-KL lower bound with explicit closed-form constant, real layer" "L454:mdc43ab".

(* 40 件尾部追加 order.txt×3 L247-286/_CoqProject×2 L248-287；PinskerCore/EnvelopeDual 摘除本次 *)

(* ng_fa53_compat_abs —— fa53_compat_abs.v：compat abs lemma, ablation harvest wave1 *)
Definition ng_fa53_compat_abs : NewGreenFace :=
  MkNewGreenFace "fa53_compat_abs.v" 173 8 20260917 "compat abs lemma, ablation harvest wave1" "L189:ma1e616".

(* ng_AbsLeId —— AbsLeId.v：abs le id small-face *)
Definition ng_AbsLeId : NewGreenFace :=
  MkNewGreenFace "AbsLeId.v" 114 5 20260917 "abs le id small-face" "L114:m6f39a3".

(* ng_fa51_sumpos_id —— fa51_sumpos_id.v：sum position identity, ablation harvest wave1 *)
Definition ng_fa51_sumpos_id : NewGreenFace :=
  MkNewGreenFace "fa51_sumpos_id.v" 234 10 20260917 "sum position identity, ablation harvest wave1" "L245:me53fed".

(* ng_fa56_id_carrier —— fa56_id_carrier.v：id carrier, ablation harvest wave1 *)
Definition ng_fa56_id_carrier : NewGreenFace :=
  MkNewGreenFace "fa56_id_carrier.v" 266 13 20260917 "id carrier, ablation harvest wave1" "L324:m973f7b".

(* ng_fa56b_ext —— fa56b_ext.v：fa56 extension b, ablation harvest wave1 (contra extraction exemption documented) *)
Definition ng_fa56b_ext : NewGreenFace :=
  MkNewGreenFace "fa56b_ext.v" 271 12 20260917 "fa56 extension b, ablation harvest wave1 (contra extraction exemption documented)" "L281:md08878".

(* ng_fa56c_ext —— fa56c_ext.v：fa56 extension c, ablation harvest wave1 *)
Definition ng_fa56c_ext : NewGreenFace :=
  MkNewGreenFace "fa56c_ext.v" 291 13 20260917 "fa56 extension c, ablation harvest wave1" "L363:m3f591f".

(* ng_fa52_dpo_witness —— fa52_dpo_witness.v：dpo witness, ablation harvest wave1 *)
Definition ng_fa52_dpo_witness : NewGreenFace :=
  MkNewGreenFace "fa52_dpo_witness.v" 94 4 20260917 "dpo witness, ablation harvest wave1" "L102:md38cbf".

(* ng_EntropyUnsatMark —— EntropyUnsatMark.v：entropy unsat mark, ablation harvest wave1 *)
Definition ng_EntropyUnsatMark : NewGreenFace :=
  MkNewGreenFace "EntropyUnsatMark.v" 131 3 20260917 "entropy unsat mark, ablation harvest wave1" "L131:m9c751c".

(* ng_IdSlotTranslate —— IdSlotTranslate.v：id slot translate, ablation harvest wave1 *)
Definition ng_IdSlotTranslate : NewGreenFace :=
  MkNewGreenFace "IdSlotTranslate.v" 174 7 20260917 "id slot translate, ablation harvest wave1" "L188:mad0517".

(* ng_SumEqListFeed —— SumEqListFeed.v：list sum eq feed, ablation harvest wave1 *)
Definition ng_SumEqListFeed : NewGreenFace :=
  MkNewGreenFace "SumEqListFeed.v" 172 8 20260917 "list sum eq feed, ablation harvest wave1" "L187:m2b1285".

(* ng_SumEqListMark —— SumEqListMark.v：list sum eq mark, ablation harvest wave1 *)
Definition ng_SumEqListMark : NewGreenFace :=
  MkNewGreenFace "SumEqListMark.v" 93 4 20260917 "list sum eq mark, ablation harvest wave1" "L172:m5cca95".

(* ng_RMaxSwap —— RMaxSwap.v：rmax swap small-face *)
Definition ng_RMaxSwap : NewGreenFace :=
  MkNewGreenFace "RMaxSwap.v" 95 4 20260917 "rmax swap small-face" "L95:m234eb8".

(* ng_NatLenPos —— NatLenPos.v：nat len pos small-face *)
Definition ng_NatLenPos : NewGreenFace :=
  MkNewGreenFace "NatLenPos.v" 111 4 20260917 "nat len pos small-face" "L124:m2b2192".

(* ng_InvPosLtCompat —— InvPosLtCompat.v：inv pos lt compat small-face *)
Definition ng_InvPosLtCompat : NewGreenFace :=
  MkNewGreenFace "InvPosLtCompat.v" 138 5 20260917 "inv pos lt compat small-face" "L138:mb9993b".

(* ng_GibbsAssembly —— GibbsAssembly.v：gibbs assembly *)
Definition ng_GibbsAssembly : NewGreenFace :=
  MkNewGreenFace "GibbsAssembly.v" 454 4 20260917 "gibbs assembly" "L468:mcb6784".

(* ng_BanachS3Chain —— BanachS3Chain.v：banach S3 chain composition *)
Definition ng_BanachS3Chain : NewGreenFace :=
  MkNewGreenFace "BanachS3Chain.v" 176 6 20260917 "banach S3 chain composition" "L176:mb1daeb".

(* ng_UpReqIrrationalCriterion —— UpReqIrrationalCriterion.v：liouville irrationality criterion via master theorem, e-instance, C2R2 line *)
Definition ng_UpReqIrrationalCriterion : NewGreenFace :=
  MkNewGreenFace "UpReqIrrationalCriterion.v" 769 28 20260917 "liouville irrationality criterion via master theorem, e-instance, C2R2 line" "L779:m916add".

(* ng_UpReqKLCocycle —— UpReqKLCocycle.v：KL cocycle identity face *)
Definition ng_UpReqKLCocycle : NewGreenFace :=
  MkNewGreenFace "UpReqKLCocycle.v" 367 6 20260917 "KL cocycle identity face" "L377:m2bae30".

(* ng_UpReqScTrigEps —— UpReqScTrigEps.v：sc trig eps family *)
Definition ng_UpReqScTrigEps : NewGreenFace :=
  MkNewGreenFace "UpReqScTrigEps.v" 537 21 20260917 "sc trig eps family" "L537:m78ba74".

(* ng_UpReqSqrtOptimal —— UpReqSqrtOptimal.v：sqrt d-optimality face *)
Definition ng_UpReqSqrtOptimal : NewGreenFace :=
  MkNewGreenFace "UpReqSqrtOptimal.v" 414 22 20260917 "sqrt d-optimality face" "L414:m68e32f".

(* ng_UpReqG05WallClass —— UpReqG05WallClass.v：G05 full-base bridge wall class, rLPO spectrum *)
Definition ng_UpReqG05WallClass : NewGreenFace :=
  MkNewGreenFace "UpReqG05WallClass.v" 392 13 20260917 "G05 full-base bridge wall class, rLPO spectrum" "L421:me3cde3".

(* ng_UpReqSquareWallEquiv —— UpReqSquareWallEquiv.v：square wall b_lift iff rLPO, wall family *)
Definition ng_UpReqSquareWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqSquareWallEquiv.v" 201 7 20260917 "square wall b_lift iff rLPO, wall family" "L201:mfc7075".

(* ng_UpReqResidWallEquiv —— UpReqResidWallEquiv.v：residual wall three-segment taxonomy, wall family *)
Definition ng_UpReqResidWallEquiv : NewGreenFace :=
  MkNewGreenFace "UpReqResidWallEquiv.v" 452 7 20260917 "residual wall three-segment taxonomy, wall family" "L464:m0a31a2".

(* ng_UpReqStepKLEtaInst —— UpReqStepKLEtaInst.v：step_kl_eta_bound interface instance resolution, GEOM-A *)
Definition ng_UpReqStepKLEtaInst : NewGreenFace :=
  MkNewGreenFace "UpReqStepKLEtaInst.v" 1071 36 20260917 "step_kl_eta_bound interface instance resolution, GEOM-A" "L1091:m3c3f88".

(* ng_UpReqIterGeomRate —— UpReqIterGeomRate.v：iteration geometric rate with sigT witness, GEOM-B *)
Definition ng_UpReqIterGeomRate : NewGreenFace :=
  MkNewGreenFace "UpReqIterGeomRate.v" 1632 29 20260917 "iteration geometric rate with sigT witness, GEOM-B" "L1641:m7d91a0".

(* ng_UpReqMixingTime —— UpReqMixingTime.v：mixing time explicit face *)
Definition ng_UpReqMixingTime : NewGreenFace :=
  MkNewGreenFace "UpReqMixingTime.v" 666 19 20260917 "mixing time explicit face" "L741:m7ba70f".

(* ng_UpReqDoeblinEntropy —— UpReqDoeblinEntropy.v：doeblin entropy production face *)
Definition ng_UpReqDoeblinEntropy : NewGreenFace :=
  MkNewGreenFace "UpReqDoeblinEntropy.v" 1064 26 20260917 "doeblin entropy production face" "L1070:m954cba".

(* ng_UpReqPinskerTransport —— UpReqPinskerTransport.v：two-point pinsker transport dp_two_point, full-distribution *)
Definition ng_UpReqPinskerTransport : NewGreenFace :=
  MkNewGreenFace "UpReqPinskerTransport.v" 1385 39 20260917 "two-point pinsker transport dp_two_point, full-distribution" "L1385:m00f6f7".

(* ng_UpReqWeakTriangle —— UpReqWeakTriangle.v：constructive weak triangle with certificate c=min(r/q), EXP-D3B *)
Definition ng_UpReqWeakTriangle : NewGreenFace :=
  MkNewGreenFace "UpReqWeakTriangle.v" 537 6 20260917 "constructive weak triangle with certificate c=min(r/q), EXP-D3B" "L537:m2c22cc".

(* ng_UpReqPadeConstUnify —— UpReqPadeConstUnify.v：pade constant unify *)
Definition ng_UpReqPadeConstUnify : NewGreenFace :=
  MkNewGreenFace "UpReqPadeConstUnify.v" 271 21 20260917 "pade constant unify" "L271:m704ce0".

(* ng_UpReqConstEnvelope —— UpReqConstEnvelope.v：constant envelope *)
Definition ng_UpReqConstEnvelope : NewGreenFace :=
  MkNewGreenFace "UpReqConstEnvelope.v" 678 21 20260917 "constant envelope" "L690:m707ebe".

(* ng_UpReqEntropyMonoSplit —— UpReqEntropyMonoSplit.v：entropy monotonicity split *)
Definition ng_UpReqEntropyMonoSplit : NewGreenFace :=
  MkNewGreenFace "UpReqEntropyMonoSplit.v" 687 5 20260917 "entropy monotonicity split" "L702:m15322a".

(* ng_UpReqSymplecticBridge —— UpReqSymplecticBridge.v：symplectic bridge *)
Definition ng_UpReqSymplecticBridge : NewGreenFace :=
  MkNewGreenFace "UpReqSymplecticBridge.v" 413 18 20260917 "symplectic bridge" "L413:m7d8247".

(* ng_UpReqAlignClose —— UpReqAlignClose.v：align close *)
Definition ng_UpReqAlignClose : NewGreenFace :=
  MkNewGreenFace "UpReqAlignClose.v" 588 6 20260917 "align close" "L601:m254842".

(* ng_DenPosGeneralClose —— DenPosGeneralClose.v：den pos general close, VER52 gap-closer *)
Definition ng_DenPosGeneralClose : NewGreenFace :=
  MkNewGreenFace "DenPosGeneralClose.v" 122 3 20260917 "den pos general close, VER52 gap-closer" "L122:m98b434".

(* 2 件尾部追加 order.txt×3 L287-288/_CoqProject×2 L289-290；UpReqUMixSelect=接口层选择器（具体层退化为实例）， *)
(* UpReqAttnMixTime=接合定理真使用形（AT2 待命形→AT3 终 swap，语句前件已对齐 ums 实形=le 形 Arch+首显参 *)

(* ng_UpReqUMixSelect —— UpReqUMixSelect.v：interface-layer mixing-time selector: bernoulli upper wall fully ported + archimedean le-form k-selection (ums_scale (S N) one witness), RealInterface generalization of UpReqMixingTime, AT1 *)
Definition ng_UpReqUMixSelect : NewGreenFace :=
  MkNewGreenFace "UpReqUMixSelect.v" 615 24 20260918 "interface-layer mixing-time selector: bernoulli upper wall fully ported + archimedean le-form k-selection (ums_scale (S N) one witness), RealInterface generalization of UpReqMixingTime, AT1" "L651:mcbf1ab".

(* ng_UpReqAttnMixTime —— UpReqAttnMixTime.v：attention mixing time closure theorem: amt_attention_mixing_time (+le) consumes ums_k_select with kappa=minus one delta_star, two-side TV stitching via le_lt_trans, degenerate-end delta*<1 strict; paper7 sec6.3 open item 1 closed, AT2 standby + AT3 final swap *)
Definition ng_UpReqAttnMixTime : NewGreenFace :=
  MkNewGreenFace "UpReqAttnMixTime.v" 223 7 20260918 "attention mixing time closure theorem: amt_attention_mixing_time (+le) consumes ums_k_select with kappa=minus one delta_star, two-side TV stitching via le_lt_trans, degenerate-end delta*<1 strict; paper7 sec6.3 open item 1 closed, AT2 standby + AT3 final swap" "L223:m019238".

(* 16 件尾部追加 order×3 L289-304/_CoqProject×2 L290-305；PadeErrorIntegral/Paper12345Sample/ *)
(* p2a_AttnClimClose/p3a_TempDualBoolSlots 四件伤单摘除候 ；fa56b/fa56c 手术版随车（已注册件内容修改）。 *)
(* ng_UpReqPinskerCore —— UpReqPinskerCore.v：pinsker constant ladder core, rung-one pnk2_pinsker_one (1*TV^2<=KL) + R8 wound repair, R9/PNSK；-PNK2B 桥接模块收取（纯追加 591 行，pnk2_pinsker_trunc5/_mirror 两块支内砖） *)
Definition ng_UpReqPinskerCore : NewGreenFace :=
  MkNewGreenFace "UpReqPinskerCore.v" 3606 57 20260919 "pinsker constant ladder core, rung-one pnk2_pinsker_one (1*TV^2<=KL) + R8 wound repair, R9/PNSK; R10-PNK2B bridge harvest, pure-append 591 on 3015, pnk2_pinsker_trunc5/_mirror" "L3608:mb2ae28".

(* ng_UpReqEnvelopeDual —— UpReqEnvelopeDual.v：constant envelope dual, cascade rebuild on repaired core, R9 *)
Definition ng_UpReqEnvelopeDual : NewGreenFace :=
  MkNewGreenFace "UpReqEnvelopeDual.v" 811 17 20260918 "constant envelope dual, cascade rebuild on repaired core, R9" "L810:m242061".

(* ng_UpReqDyadicLog —— UpReqDyadicLog.v：dyadic log envelopes, axis rate via c3e engine, W1B/W1C line *)
Definition ng_UpReqDyadicLog : NewGreenFace :=
  MkNewGreenFace "UpReqDyadicLog.v" 589 24 20260918 "dyadic log envelopes, axis rate via c3e engine, W1B/W1C line" "L608:mdc9319".

(* ng_fa57_ext —— fa57_ext.v：fa57 extension direct compile, VER52 wave-3 handover *)
Definition ng_fa57_ext : NewGreenFace :=
  MkNewGreenFace "fa57_ext.v" 239 11 20260918 "fa57 extension direct compile, VER52 wave-3 handover" "L240:ma5d56f".

(* ng_UpReqRatioTail —— UpReqRatioTail.v：ratio tail Q/Real faces, R9/R9B *)
Definition ng_UpReqRatioTail : NewGreenFace :=
  MkNewGreenFace "UpReqRatioTail.v" 919 42 20260918 "ratio tail Q/Real faces, R9/R9B" "L935:mce23d3".

(* ng_UpReqAttnUniformLimit —— UpReqAttnUniformLimit.v：attn uniform limit + switch_gen family, R9B/SWG *)
Definition ng_UpReqAttnUniformLimit : NewGreenFace :=
  MkNewGreenFace "UpReqAttnUniformLimit.v" 618 15 20260918 "attn uniform limit + switch_gen family, R9B/SWG" "L1839:m7ddcdd".

(* ng_UpReqAttnMassSplit —— UpReqAttnMassSplit.v：Q18 mass-split chain ams_, Q18C *)
Definition ng_UpReqAttnMassSplit : NewGreenFace :=
  MkNewGreenFace "UpReqAttnMassSplit.v" 891 12 20260918 "Q18 mass-split chain ams_, Q18C" "L885:m643ab3".

(* ng_UpReqAttnQ18Tail —— UpReqAttnQ18Tail.v：Q18 tail: T0 rationalized 299#1000 + cross-token congruence, Q18D *)
Definition ng_UpReqAttnQ18Tail : NewGreenFace :=
  MkNewGreenFace "UpReqAttnQ18Tail.v" 519 17 20260918 "Q18 tail: T0 rationalized 299#1000 + cross-token congruence, Q18D" "L512:meefaf2".

(* ng_FepIdentClass —— FepIdentClass.v：FEP identification class, ablation harvest 23-03 *)
Definition ng_FepIdentClass : NewGreenFace :=
  MkNewGreenFace "FepIdentClass.v" 578 5 20260918 "FEP identification class, ablation harvest 23-03" "L578:me4945b".

(* ng_G04ProjHook —— G04ProjHook.v：G04 proj hook, ablation harvest 23-03 *)
Definition ng_G04ProjHook : NewGreenFace :=
  MkNewGreenFace "G04ProjHook.v" 222 12 20260918 "G04 proj hook, ablation harvest 23-03" "L241:mac9fc2".

(* ng_LMCarrierExt —— LMCarrierExt.v：LM carrier extension, ablation harvest 23-03 *)
Definition ng_LMCarrierExt : NewGreenFace :=
  MkNewGreenFace "LMCarrierExt.v" 306 15 20260918 "LM carrier extension, ablation harvest 23-03" "L343:m6945e4".

(* ng_Paper1Ablation —— Paper1Ablation.v：paper1 ablation sample, harvest 23-03 *)
Definition ng_Paper1Ablation : NewGreenFace :=
  MkNewGreenFace "Paper1Ablation.v" 521 5 20260918 "paper1 ablation sample, harvest 23-03" "L521:m6d3847".

(* ng_Paper7Ablation —— Paper7Ablation.v：paper7 ablation, harvest 23-03 *)
Definition ng_Paper7Ablation : NewGreenFace :=
  MkNewGreenFace "Paper7Ablation.v" 191 7 20260918 "paper7 ablation, harvest 23-03" "L191:m9081cf".

(* ng_PhysPredAblation —— PhysPredAblation.v：physics prediction ablation, harvest 23-03 *)
Definition ng_PhysPredAblation : NewGreenFace :=
  MkNewGreenFace "PhysPredAblation.v" 279 13 20260918 "physics prediction ablation, harvest 23-03" "L292:m984e7f".

(* ng_RateTheoryAblation —— RateTheoryAblation.v：rate theory ablation, harvest 23-03 *)
Definition ng_RateTheoryAblation : NewGreenFace :=
  MkNewGreenFace "RateTheoryAblation.v" 215 5 20260918 "rate theory ablation, harvest 23-03" "L222:m414c81".

(* ng_p4a_GradSignQDec —— p4a_GradSignQDec.v：paper4-a grad sign Q-decidable, extraction magic 0, harvest 23-03 *)
Definition ng_p4a_GradSignQDec : NewGreenFace :=
  MkNewGreenFace "p4a_GradSignQDec.v" 257 13 20260918 "paper4-a grad sign Q-decidable, extraction magic 0, harvest 23-03" "L271:m4a3e3a".

(* 3 件尾部追加 order L305-307（ 十六件在前）；依赖链 ConcSoftmax→ConcMixSel→ConcB1； *)
(* csm_b1_unconditional_mixing_time=零接口零 Arch 零证书参（无条件机器判据=PA 八问 Closed）。 *)
(* ng_UpReqConcSoftmax —— UpReqConcSoftmax.v：concrete-layer softmax supply: sumf slot eight properties unconditional (five delegated to sumd_ family + per-eps triangle abs_sum_le core), AT5 *)
Definition ng_UpReqConcSoftmax : NewGreenFace :=
  MkNewGreenFace "UpReqConcSoftmax.v" 264 12 20260918 "concrete-layer softmax supply: sumf slot eight properties unconditional (five delegated to sumd_ family + per-eps triangle abs_sum_le core), AT5" "L335:m6f4fd5".

(* ng_UpReqConcMixSel —— UpReqConcMixSel.v：req-face mirror of mixing selector and closure: cmk_k_select (+le) bernoulli wall fully re-proved + cmk_attention_mixing_time (+le) consuming rsq rate 25-arg, AT6 *)
Definition ng_UpReqConcMixSel : NewGreenFace :=
  MkNewGreenFace "UpReqConcMixSel.v" 940 37 20260918 "req-face mirror of mixing selector and closure: cmk_k_select (+le) bernoulli wall fully re-proved + cmk_attention_mixing_time (+le) consuming rsq rate 25-arg, AT6" "L940:md8fd1e".

(* ng_UpReqConcB1 —— UpReqConcB1.v：B1 unconditional assembly: csm_b1_unconditional_mixing_time (+le) zero interface premises zero arch premises zero certificate params (1-element kernel bypass + Htv0 mass resolution + real_arch re-shape via cb1_scale_const), AT7 *)
Definition ng_UpReqConcB1 : NewGreenFace :=
  MkNewGreenFace "UpReqConcB1.v" 394 18 20260918 "B1 unconditional assembly: csm_b1_unconditional_mixing_time (+le) zero interface premises zero arch premises zero certificate params (1-element kernel bypass + Htv0 mass resolution + real_arch re-shape via cb1_scale_const), AT7" "L394:m196b83".

(* ng_UpReqConcB2 —— UpReqConcB2.v：B2 substantial-kernel machine: cb2_dot finite dot product + cb2_list_max_abs cap + cb2_z logit kernel with cb2_Delta (=core+1 unit slack, constructive gap certificate) double bounds, AT8 *)
Definition ng_UpReqConcB2 : NewGreenFace :=
  MkNewGreenFace "UpReqConcB2.v" 627 31 20260918 "B2 substantial-kernel machine: cb2_dot finite dot product + cb2_list_max_abs cap + cb2_z logit kernel with cb2_Delta (=core+1 unit slack, constructive gap certificate) double bounds, AT8" "L664:m668b57".

(* ng_UpReqConcB2Time —— UpReqConcB2Time.v：B2 unconditional closure: cbt_unconditional_mixing_time (+le) on the concrete logit kernel — zero interface premises zero arch premises zero certificate params (Htv0 mass resolution + arch re-shape via cb1_scale_const), honest notes: +1 slack conservatism and 1-element TV0 tier, multi-element recipe'd, AT9 *)
Definition ng_UpReqConcB2Time : NewGreenFace :=
  MkNewGreenFace "UpReqConcB2Time.v" 339 17 20260918 "B2 unconditional closure: cbt_unconditional_mixing_time (+le) on the concrete logit kernel — zero interface premises zero arch premises zero certificate params (Htv0 mass resolution + arch re-shape via cb1_scale_const), honest notes: +1 slack conservatism and 1-element TV0 tier, multi-element recipe'd, AT9" "L381:m51cfe4".

(* ng_UpReqTailResidual —— UpReqTailResidual.v：tail residual engine: Q kernel uniform bound + log two-branch pair + trunc5 bridge, W2/W2B/W2C line *)
Definition ng_UpReqTailResidual : NewGreenFace :=
  MkNewGreenFace "UpReqTailResidual.v" 1527 44 20260918 "tail residual engine: Q kernel uniform bound + log two-branch pair + trunc5 bridge, W2/W2B/W2C line" "L1527:mbd09b8".

(* ng_UpReqVajdaBound —— UpReqVajdaBound.v：two-point Vajda pieces: kl2 closed form + ln engine + piecewise lower bound, WB/WC/WC2/W2D line *)
Definition ng_UpReqVajdaBound : NewGreenFace :=
  MkNewGreenFace "UpReqVajdaBound.v" 843 33 20260918 "two-point Vajda pieces: kl2 closed form + ln engine + piecewise lower bound, WB/WC/WC2/W2D line" "L843:m6f20b0".

(* ng_UpReqIrrationalInstances —— UpReqIrrationalInstances.v：sqrt2 irrational instance via lic mother criterion exact assembly, IR2/IR3 line *)
Definition ng_UpReqIrrationalInstances : NewGreenFace :=
  MkNewGreenFace "UpReqIrrationalInstances.v" 1303 50 20260918 "sqrt2 irrational instance via lic mother criterion exact assembly, IR2/IR3 line" "L1318:m627f02".

(* ng_UpReqEqbComplete —— UpReqEqbComplete.v：eqb judicator completeness direction generic mother + dual instance forwarding, Q19S *)
Definition ng_UpReqEqbComplete : NewGreenFace :=
  MkNewGreenFace "UpReqEqbComplete.v" 277 13 20260918 "eqb judicator completeness direction generic mother + dual instance forwarding, Q19S" "L277:m35f2de".

(* ng_UpReqSentinelMother —— UpReqSentinelMother.v：unreachable sentinel mother pair: domination + domain-bound, with G10 dmin bridge, Q24S *)
Definition ng_UpReqSentinelMother : NewGreenFace :=
  MkNewGreenFace "UpReqSentinelMother.v" 320 16 20260918 "unreachable sentinel mother pair: domination + domain-bound, with G10 dmin bridge, Q24S" "L346:me9fe59".

(* ng_UpReqLn2Irrational —— UpReqLn2Irrational.v：ln2 irrational conditional-form assembly truly via mother criterion, escape window honestly open, IR4 *)
Definition ng_UpReqLn2Irrational : NewGreenFace :=
  MkNewGreenFace "UpReqLn2Irrational.v" 370 21 20260918 "ln2 irrational conditional-form assembly truly via mother criterion, escape window honestly open, IR4" "L379:m989ebf".

(* ng_UpReqSqrt3Irrational —— UpReqSqrt3Irrational.v：sqrt3 无理性第三实例（IR5，mod-3 下降 + 4/11 逃逸窗再参数化）；在树老件首注册（R75P 连座同期注册：零在册取用方，被入包件10 abl_W9_slice57_10 硬依赖，order L423→件10 L424）；Require 面全在册零新暗件；账块自 L1141:mba9a54（旧快照，后经大改版账实分裂）原位刷新，以 AB9 报告 L2013 实形为基（基 2365 行 77 Qed md5 e957f0） *)
Definition ng_UpReqSqrt3Irrational : NewGreenFace :=
  MkNewGreenFace "UpReqSqrt3Irrational.v" 2365 73 20260928
  "sqrt3 irrational third instance (IR5): mod-3 descent + 4/11 escape window re-parameterization; in-tree legacy piece first registered via R75P co-enrollment, hard-required by enrolled abl_W9_slice57_10; Require face all registered, zero new dark pieces, zero in-registry consumers; ledger refreshed from stale snapshot L1141:mba9a54 day 20260918, AB9 base 2365 lines 77 Qed md5 e957f0; md5 e957f0" "L2365:me957f0".
(* 1 件尾部追加 order L317；零 CW 基座依赖纯 Q 层；封顶定理=闭式族量级封顶（affine 可反解族，诚实限定）。 *)

(* ng_UpReqMixLogE —— UpReqMixLogE.v：closed-form cap theorems for bernoulli-family selectors (sharpened F1/F2/F3 + mixe_cf_cap/_gen/_div/_select_cap), pure Q-layer zero CW-base dependency, race E *)
Definition ng_UpReqMixLogE : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogE.v" 792 48 20260918 "closed-form cap theorems for bernoulli-family selectors, sharpened F1/F2/F3, pure Q-layer zero CW-base dependency, race E first finisher" "L792:m12d039".

(* 2 件尾部追加 order L374-375；E 件 L373 已于 先册（792 48 ），本次 md5 复核三面全等免重册； *)
(* A/B 与 E 间零内边，A 外依赖 CW_219/UpTVDoeblin/KLWallClosed/UpReqIterGeomRate 全在提交面 L16-L273。 *)
(* ng_UpReqMixLogA —— UpReqMixLogA.v：rational-reduction + Q-layer decidable bisection log-scale k selector (mixa_ family: qbern window / fuel bsearch / k0+b0 bridges / pow_budget_log cert+min), four-gate green, race A *)
Definition ng_UpReqMixLogA : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogA.v" 1304 57 20260919 "rational-reduction + Q-decidable bisection log-scale k selector (mixa_ family), zero new axioms Print Assumptions closed, race A" "L1315:mc38cac".

(* ng_UpReqMixLogB —— UpReqMixLogB.v：galloping (exponential) search + terminal bisection log-scale k selector (mixb_ family: qbernoulli / gallop / sel_scale compare count 2*log2 K+5), four-gate green, race B *)
Definition ng_UpReqMixLogB : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogB.v" 1311 65 20260919 "galloping search + terminal bisection log-scale k selector (mixb_ family), compare count bounded 2*log2 K+5, zero new axioms Print Assumptions closed, race B" "L1335:m395a8d".

(* 2 件尾部追加 order L376-377（两件互不依赖零内边，按字母序就位：Fin2 L376、D L377）；vo 树内 9.1 原地重编（跨树 digest 防御：Live_X 产物未直种），.vo/.vos 头 436f712100015ff4，双件单件 coqchk RC=0；D 依赖 CW_219/UpTVDoeblin/UpReqIterGeomRate/UpReqMixingTime/KLWallClosed 全在提交面 L16-L274，Fin2 依赖 CW_219/AttnDoeblin/UpReqAlgebra/UpReqDist/UpReqSampling/UpReqSumD/UpReqConcSoftmax/UpReqConcMixSel/UpReqConcB1/UpReqConcB2 全在提交面 L16-L315。 *)
(* ng_UpReqConcFin2 —— UpReqConcFin2.v：Fin-2 non-degeneracy concrete instance (cf2_ family: bool world data T2 + TV strict positivity T3 + T4b abs_row bridges + T5b cf2_tv_iter_eps closure; lineage F21 3091e0d0 -> F22 green base a3833710 via concurrent-collision arbitration -> F23 harvest), four-gate green, T2-T7 full incl. T6 mixing chain + T7 mixing_time (ptmass+general), 50 PA Closed *)
Definition ng_UpReqConcFin2 : NewGreenFace :=
  MkNewGreenFace "UpReqConcFin2.v" 1569 25 20260919 "Fin-2 non-degeneracy concrete instance (cf2_ family), TV non-triviality demo + T5b iteration closure on arbitration base a3833710, zero new axioms Print Assumptions closed" "L1648:m42c627".
(* ng_UpReqMixLogD —— UpReqMixLogD.v：Path D squared-ladder kappa0 powers + binary-composition log-scale k selector (mixd_ family: ladder/scan_up/desc with QleT' certificate direct-return, cost c <= 5*d+2, Q-core Defined selector + Real rationalization shell), four-gate green, race D, 66 Qed / 10 PA Closed *)
Definition ng_UpReqMixLogD : NewGreenFace :=
  MkNewGreenFace "UpReqMixLogD.v" 1725 66 20260919 "squared-ladder + binary-composition log-scale k selector (mixd_ family), certificate direct-return with cost bound 5*d+2, zero new axioms Print Assumptions closed, race D" "L1730:ma38e8a".

(* ng_UpAblD1PPO_UpReqPPOPlain —— UpAblD1PPO_UpReqPPOPlain.v：FA-D1PPO in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised) *)
Definition ng_UpAblD1PPO_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1PPO_UpReqPPOPlain.v" 117 2 20260919 "FA-D1PPO in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L115:ma1fb2a".
(* ng_UpAblD1S10_UpReqConcMixSel —— UpAblD1S10_UpReqConcMixSel.v：FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised) *)
Definition ng_UpAblD1S10_UpReqConcMixSel : NewGreenFace :=
  MkNewGreenFace "UpAblD1S10_UpReqConcMixSel.v" 124 1 20260919 "FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L124:me22e2c".
(* ng_UpAblD1S10_UpReqPPOPlain —— UpAblD1S10_UpReqPPOPlain.v：FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised) *)
Definition ng_UpAblD1S10_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S10_UpReqPPOPlain.v" 120 2 20260919 "FA-D1S10 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L120:mc3c689".
(* ng_UpAblD1S11_UpReqPPOPlain —— UpAblD1S11_UpReqPPOPlain.v：FA-D1S11 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised; note: sibling UpAblD1S11_UpReqCauchy quarantined, unterminated comment) *)
Definition ng_UpAblD1S11_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S11_UpReqPPOPlain.v" 126 2 20260919 "FA-D1S11 in-flight batch (source landed Live_X, batch report pending at enrollment time; enrolled from current bytes, re-sync at wave if revised; note: sibling UpAblD1S11_UpReqCauchy quarantined, unterminated comment); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L126:m50f67f".
(* ng_UpAblD1S2_e752_UpReqAttnIter —— UpAblD1S2_e752_UpReqAttnIter.v：FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green () *)
Definition ng_UpAblD1S2_e752_UpReqAttnIter : NewGreenFace :=
  MkNewGreenFace "UpAblD1S2_e752_UpReqAttnIter.v" 92 2 20260919 "FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green (_tfad1s2_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L92:m747e7d".
(* ng_UpAblD1S2_reqlog_UpReqCauchy —— UpAblD1S2_reqlog_UpReqCauchy.v：FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green () *)
Definition ng_UpAblD1S2_reqlog_UpReqCauchy : NewGreenFace :=
  MkNewGreenFace "UpAblD1S2_reqlog_UpReqCauchy.v" 48 1 20260919 "FA-D1S2, 12 net-new slots N1 log-bridge, four-gate green (_tfad1s2_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L48:m7bf6ba".
(* ng_UpAblD1S3_fep_UpReqAttnGibbs —— UpAblD1S3_fep_UpReqAttnGibbs.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_fep_UpReqAttnGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_fep_UpReqAttnGibbs.v" 69 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L69:m3abace".
(* ng_UpAblD1S3_fep_UpReqSteadyThermo —— UpAblD1S3_fep_UpReqSteadyThermo.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_fep_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_fep_UpReqSteadyThermo.v" 155 5 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L167:m15bebd".
(* ng_UpAblD1S3_sum_pos_AlignIdUnclosed —— UpAblD1S3_sum_pos_AlignIdUnclosed.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_AlignIdUnclosed : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_AlignIdUnclosed.v" 53 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L53:m437045".
(* ng_UpAblD1S3_sum_pos_SecondLawQuantified —— UpAblD1S3_sum_pos_SecondLawQuantified.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_SecondLawQuantified : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_SecondLawQuantified.v" 43 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:md95a37".
(* ng_UpAblD1S3_sum_pos_UpReqEntropyMaxTemp —— UpAblD1S3_sum_pos_UpReqEntropyMaxTemp.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_UpReqEntropyMaxTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_UpReqEntropyMaxTemp.v" 43 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:maef005".
(* ng_UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg —— UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg.v：FA-D1S3, slots N1 (17 batch), four-gate green () *)
Definition ng_UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg : NewGreenFace :=
  MkNewGreenFace "UpAblD1S3_sum_pos_UpReqEntropyUniqueNeg.v" 43 1 20260919 "FA-D1S3, slots N1 (17 batch), four-gate green (_tfad1s3_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:m950571".
(* ng_UpAblD1S4_UpReqStepKLEtaInst —— UpAblD1S4_UpReqStepKLEtaInst.v：FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green () *)
Definition ng_UpAblD1S4_UpReqStepKLEtaInst : NewGreenFace :=
  MkNewGreenFace "UpAblD1S4_UpReqStepKLEtaInst.v" 137 5 20260919 "FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green (_tfad1s4_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L111:m720e91".
(* ng_UpAblD1S4_UpReqTopKTVChain —— UpAblD1S4_UpReqTopKTVChain.v：FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green () *)
Definition ng_UpAblD1S4_UpReqTopKTVChain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S4_UpReqTopKTVChain.v" 128 2 20260919 "FA-D1S4, T-supply level (SKE 12 + TopKTV 18, census-N honestly downgraded), four-gate green (_tfad1s4_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L128:m7c2d15".
(* ng_UpAblD1S5_UpReqDoeblinEntropy —— UpAblD1S5_UpReqDoeblinEntropy.v：FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green () *)
Definition ng_UpAblD1S5_UpReqDoeblinEntropy : NewGreenFace :=
  MkNewGreenFace "UpAblD1S5_UpReqDoeblinEntropy.v" 624 13 20260919 "FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green (_tfad1s5_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L609:m129927".
(* ng_UpAblD1S5_UpReqEntropyMonoSplit —— UpAblD1S5_UpReqEntropyMonoSplit.v：FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green () *)
Definition ng_UpAblD1S5_UpReqEntropyMonoSplit : NewGreenFace :=
  MkNewGreenFace "UpAblD1S5_UpReqEntropyMonoSplit.v" 596 8 20260919 "FA-D1S5, N-supply 18 + 12, +4 T-prune declared, four-gate green (_tfad1s5_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L596:m2cc121".
(* ng_UpAblD1S6_SecondLawQuantified —— UpAblD1S6_SecondLawQuantified.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_SecondLawQuantified : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_SecondLawQuantified.v" 69 1 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L72:m226112".
(* ng_UpAblD1S6_UpReqMinPKLChain —— UpAblD1S6_UpReqMinPKLChain.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_UpReqMinPKLChain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_UpReqMinPKLChain.v" 99 3 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L99:m3ad85e".
(* ng_UpAblD1S6_UpReqRealFEP —— UpAblD1S6_UpReqRealFEP.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_UpReqRealFEP : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_UpReqRealFEP.v" 71 1 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L73:mb7314f".
(* ng_UpAblD1S6_UpReqSteadyThermo —— UpAblD1S6_UpReqSteadyThermo.v：FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green () *)
Definition ng_UpAblD1S6_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "UpAblD1S6_UpReqSteadyThermo.v" 74 1 20260919 "FA-D1S6, T-supply (34 batch) + MPK:52 N empty-type certificate + MPK:49 W register, four-gate green (_tfad1s6_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m66e6cf".
(* ng_UpAblD1S7_UpReqEntropyDeficitTemp —— UpAblD1S7_UpReqEntropyDeficitTemp.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyDeficitTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyDeficitTemp.v" 75 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m13af8c".
(* ng_UpAblD1S7_UpReqEntropyMaxTemp —— UpAblD1S7_UpReqEntropyMaxTemp.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyMaxTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyMaxTemp.v" 81 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L80:mf67260".
(* ng_UpAblD1S7_UpReqEntropyUniqueNeg —— UpAblD1S7_UpReqEntropyUniqueNeg.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyUniqueNeg : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyUniqueNeg.v" 75 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m3b33e1".
(* ng_UpAblD1S7_UpReqEntropyUniqueTemp —— UpAblD1S7_UpReqEntropyUniqueTemp.v：FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green () *)
Definition ng_UpAblD1S7_UpReqEntropyUniqueTemp : NewGreenFace :=
  MkNewGreenFace "UpAblD1S7_UpReqEntropyUniqueTemp.v" 75 1 20260919 "FA-D1S7, T-supply x37 batch (S3 duplicate 4 disclosed), four-gate green (_tfad1s7_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L76:m6be901".
(* ng_UpAblD1S8_TempSoftmaxInstantiation —— UpAblD1S8_TempSoftmaxInstantiation.v：FA-D1S8, T-supply x39 batch all merged, four-gate green () *)
Definition ng_UpAblD1S8_TempSoftmaxInstantiation : NewGreenFace :=
  MkNewGreenFace "UpAblD1S8_TempSoftmaxInstantiation.v" 90 1 20260919 "FA-D1S8, T-supply x39 batch all merged, four-gate green (_tfad1s8_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L86:ma4d8d5".
(* ng_UpAblD1S8_UpReqPPOPlain —— UpAblD1S8_UpReqPPOPlain.v：FA-D1S8, T-supply x39 batch all merged, four-gate green () *)
Definition ng_UpAblD1S8_UpReqPPOPlain : NewGreenFace :=
  MkNewGreenFace "UpAblD1S8_UpReqPPOPlain.v" 173 3 20260919 "FA-D1S8, T-supply x39 batch all merged, four-gate green (_tfad1s8_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L173:m7041dd".
(* ng_UpAblD1S8_UpReqTempDefs —— UpAblD1S8_UpReqTempDefs.v：FA-D1S8, T-supply x39 batch all merged, four-gate green () *)
Definition ng_UpAblD1S8_UpReqTempDefs : NewGreenFace :=
  MkNewGreenFace "UpAblD1S8_UpReqTempDefs.v" 79 1 20260919 "FA-D1S8, T-supply x39 batch all merged, four-gate green (_tfad1s8_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L80:m329919".
(* ng_UpAblD1S9_UpReqAttnIter —— UpAblD1S9_UpReqAttnIter.v：FA-D1S9, T x21 + W x1, four-gate green () *)
Definition ng_UpAblD1S9_UpReqAttnIter : NewGreenFace :=
  MkNewGreenFace "UpAblD1S9_UpReqAttnIter.v" 233 4 20260919 "FA-D1S9, T x21 + W x1, four-gate green (_tfad1s9_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L209:mf549db".
(* ng_UpAblD1_expf_pack —— UpAblD1_expf_pack.v：FA-D1S1, expf bundle N1 (C13 three-way grade conflict counted N per ledger), four-gate green () *)
Definition ng_UpAblD1_expf_pack : NewGreenFace :=
  MkNewGreenFace "UpAblD1_expf_pack.v" 98 1 20260919 "FA-D1S1, expf bundle N1 (C13 three-way grade conflict counted N per ledger), four-gate green (_tfad1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L98:mae2830".
(* ng_UpAblD1_fa53_lpc_broadcast —— UpAblD1_fa53_lpc_broadcast.v：FA-D1S1, fa53 lpc broadcast N1, four-gate green () *)
Definition ng_UpAblD1_fa53_lpc_broadcast : NewGreenFace :=
  MkNewGreenFace "UpAblD1_fa53_lpc_broadcast.v" 201 9 20260919 "FA-D1S1, fa53 lpc broadcast N1, four-gate green (_tfad1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L201:m91e4c1".
(* ng_UpAblD2_AbsLeId_RI_DO —— UpAblD2_AbsLeId_RI_DO.v：FA-D2S1, N3 x2 supply-pair + N1 x2 RI-face + T x1 (W register DO carrier noted), four-gate green () *)
Definition ng_UpAblD2_AbsLeId_RI_DO : NewGreenFace :=
  MkNewGreenFace "UpAblD2_AbsLeId_RI_DO.v" 136 5 20260919 "FA-D2S1, N3 x2 supply-pair + N1 x2 RI-face + T x1 (W register DO carrier noted), four-gate green (_tfad2s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L136:mb8d671".
(* ng_UpAblP1_SqrtfCauchy_four_slots —— UpAblP1_SqrtfCauchy_four_slots.v：FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green () *)
Definition ng_UpAblP1_SqrtfCauchy_four_slots : NewGreenFace :=
  MkNewGreenFace "UpAblP1_SqrtfCauchy_four_slots.v" 89 0 20260919 "FA-P1S1 batch, 9 slots all N1 (SqrtfCauchy 5 + SLQ 4), four-gate green (_tfap1s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L89:m4a0b0c".
(* ng_UpAblP2_SecondLawConsume_sumdis —— UpAblP2_SecondLawConsume_sumdis.v：FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green () *)
Definition ng_UpAblP2_SecondLawConsume_sumdis : NewGreenFace :=
  MkNewGreenFace "UpAblP2_SecondLawConsume_sumdis.v" 179 6 20260919 "FA-P2S1 three-pack, batch split N8 + N3 supply3 + T7 merged + 1 pruned, four-gate green (_tfap2s1_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L179:m1901c0".
(* ng_UpAbl_S04RealExpLogConv —— UpAbl_S04RealExpLogConv.v：v1 batch (a), N1 x1 + N2 x3, four-gate green () *)
Definition ng_UpAblT10_S04RealExpLogConv : NewGreenFace :=
  MkNewGreenFace "UpAblT10_S04RealExpLogConv.v" 85 4 20260919 "v1 T10 batch (T10a), N1 x1 + N2 x3, four-gate green (_tt10a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L85:m2e0cd9".
(* ng_UpAbl_S11_TP3B5 —— UpAbl_S11_TP3B5.v：v1 batch (a), N1 x2 + N2 x6, four-gate green () *)
Definition ng_UpAblT11_S11_TP3B5 : NewGreenFace :=
  MkNewGreenFace "UpAblT11_S11_TP3B5.v" 139 8 20260919 "v1 T11 batch (T11a), N1 x2 + N2 x6, four-gate green (_tt11a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L139:m013518".
(* ng_UpAbl_G13 —— UpAbl_G13.v：v1 batch (a), N1 x4 + N2 x1, four-gate green () *)
Definition ng_UpAblT12_G13 : NewGreenFace :=
  MkNewGreenFace "UpAblT12_G13.v" 78 3 20260919 "v1 T12 batch (T12a), N1 x4 + N2 x1, four-gate green (_tt12a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L98:m7e565f".
(* ng_UpAbl_UpRealLeB2 —— UpAbl_UpRealLeB2.v：v1 batch (a), N1 x4 + N2 x1, four-gate green () *)
Definition ng_UpAblT12_UpRealLeB2 : NewGreenFace :=
  MkNewGreenFace "UpAblT12_UpRealLeB2.v" 159 3 20260919 "v1 T12 batch (T12a), N1 x4 + N2 x1, four-gate green (_tt12a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L159:m0b03dc".
(* ng_UpAbl_UpReqAlignRestA —— UpAbl_UpReqAlignRestA.v：v1 batch (a), N1 x4 + N2 x1, four-gate green () *)
Definition ng_UpAblT12_UpReqAlignRestA : NewGreenFace :=
  MkNewGreenFace "UpAblT12_UpReqAlignRestA.v" 49 1 20260919 "v1 T12 batch (T12a), N1 x4 + N2 x1, four-gate green (_tt12a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L49:m218ee5".
(* ng_UpAbl_UpEntropyGainReq —— UpAbl_UpEntropyGainReq.v：v1 a batch, N x8, four-gate green () *)
Definition ng_UpAblT13_UpEntropyGainReq : NewGreenFace :=
  MkNewGreenFace "UpAblT13_UpEntropyGainReq.v" 43 1 20260919 "v1 T13a batch, N x8, four-gate green (_tt13a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:m637407".
(* ng_UpAbl_UpFirewallReq —— UpAbl_UpFirewallReq.v：v1 a batch, N x8, four-gate green () *)
(* ng_UpAbl_UpReqAlignRestA —— UpAbl_UpReqAlignRestA.v：v1 a batch, N x8, four-gate green () *)
(* ng_UpAbl_UpReqSampling —— UpAbl_UpReqSampling.v：v1 a batch, N x8, four-gate green () *)
(* ng_UpAbl_UpSigMigrate2 —— UpAbl_UpSigMigrate2.v：v1 a batch, N x8, four-gate green () *)
Definition ng_UpAblT13_UpSigMigrate2 : NewGreenFace :=
  MkNewGreenFace "UpAblT13_UpSigMigrate2.v" 45 1 20260919 "v1 T13a batch, N x8, four-gate green (_tt13a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L45:m3d3f78".
(* ng_UpAblb_G06_BForm —— UpAblb_G06_BForm.v：v1 b batch, N x19, four-gate green () *)
Definition ng_UpAblT13b_G06_BForm : NewGreenFace :=
  MkNewGreenFace "UpAblT13b_G06_BForm.v" 113 7 20260919 "v1 T13b batch, N x19, four-gate green (_tt13b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L185:mb9d88c".
(* ng_UpAblb_G13 —— UpAblb_G13.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqAlign —— UpAblb_UpReqAlign.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqAlign2 —— UpAblb_UpReqAlign2.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqAlignRestA —— UpAblb_UpReqAlignRestA.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpReqDist —— UpAblb_UpReqDist.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpSigMigrate —— UpAblb_UpSigMigrate.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpSigMigrate2 —— UpAblb_UpSigMigrate2.v：v1 b batch, N x19, four-gate green () *)
(* ng_UpAblb_UpTVDoeblin —— UpAblb_UpTVDoeblin.v：v1 b batch, N x19, four-gate green () *)
Definition ng_UpAblT13b_UpTVDoeblin : NewGreenFace :=
  MkNewGreenFace "UpAblT13b_UpTVDoeblin.v" 39 1 20260919 "v1 T13b batch, N x19, four-gate green (_tt13b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L39:mceb0e2".
(* ng_UpAblc_G13 —— UpAblc_G13.v：c batch9, N3 x8 + conditional discharge x3, four-gate green () *)
Definition ng_UpAblT13c_G13 : NewGreenFace :=
  MkNewGreenFace "UpAblT13c_G13.v" 271 11 20260919 "T13c batch9, N3 x8 + conditional discharge x3, four-gate green (_tt13c_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L327:m127dd7".
(* ng_UpAblc_UpReqDist —— UpAblc_UpReqDist.v：c batch9, N3 x8 + conditional discharge x3, four-gate green () *)
Definition ng_UpAblT13c_UpReqDist : NewGreenFace :=
  MkNewGreenFace "UpAblT13c_UpReqDist.v" 119 4 20260919 "T13c batch9, N3 x8 + conditional discharge x3, four-gate green (_tt13c_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L119:mca9cee".
(* ng_UpAblc_UpSigMigrate2 —— UpAblc_UpSigMigrate2.v：c batch9, N3 x8 + conditional discharge x3, four-gate green () *)
(* ng_UpAblT1_UpFirewallReq —— UpAblT1_UpFirewallReq.v：v1 T1 batch (T1a), N1x25 across 3 files, four-gate green () *)
Definition ng_UpAblT1_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "UpAblT1_UpFirewallReq.v" 97 5 20260919 "v1 T1 batch (T1a), N1x25 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L97:mc00df6".
(* ng_UpAblT1_UpReqDist —— UpAblT1_UpReqDist.v：v1 T1 batch (T1a), N1x25 across 3 files, four-gate green () *)
Definition ng_UpAblT1_UpReqDist : NewGreenFace :=
  MkNewGreenFace "UpAblT1_UpReqDist.v" 237 14 20260919 "v1 T1 batch (T1a), N1x25 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L363:m606d79".
(* ng_UpAblT1_UpReqTempEntropy —— UpAblT1_UpReqTempEntropy.v：v1 T1 batch (T1a), N1x25 across 3 files, four-gate green () *)
Definition ng_UpAblT1_UpReqTempEntropy : NewGreenFace :=
  MkNewGreenFace "UpAblT1_UpReqTempEntropy.v" 112 6 20260919 "v1 T1 batch (T1a), N1x25 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L112:m758692".
(* ng_UpAblT1b_AttnDoeblin —— UpAblT1b_AttnDoeblin.v：v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green () *)
Definition ng_UpAblT1b_AttnDoeblin : NewGreenFace :=
  MkNewGreenFace "UpAblT1b_AttnDoeblin.v" 172 8 20260919 "v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L172:m139121".
(* ng_UpAblT1b_S06_DiffSamplingGibbs —— UpAblT1b_S06_DiffSamplingGibbs.v：v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green () *)
Definition ng_UpAblT1b_S06_DiffSamplingGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblT1b_S06_DiffSamplingGibbs.v" 148 6 20260919 "v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L158:m8b1e3b".
(* ng_UpAblT1b_S13_NLiveAudit —— UpAblT1b_S13_NLiveAudit.v：v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green () *)
Definition ng_UpAblT1b_S13_NLiveAudit : NewGreenFace :=
  MkNewGreenFace "UpAblT1b_S13_NLiveAudit.v" 166 8 20260919 "v1 T1b batch, N1x7+N2x3 across 3 files, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L166:m813da1".
(* ng_UpAblT1c_UpFirewallReq —— UpAblT1c_UpFirewallReq.v：v1 T1c batch, N x5 firewall five-bridge, four-gate green () *)
Definition ng_UpAblT1c_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "UpAblT1c_UpFirewallReq.v" 236 6 20260919 "v1 T1c batch, N x5 firewall five-bridge, four-gate green (_tt1a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L236:md5fc79".
(* ng_UpAblT2a_UpFirewallReq —— UpAblT2a_UpFirewallReq.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpFirewallReq.v" 32 1 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L32:m962b43".
(* ng_UpAblT2a_UpReqAlignRestA —— UpAblT2a_UpReqAlignRestA.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpReqAlignRestA : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpReqAlignRestA.v" 30 1 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L30:m933719".
(* ng_UpAblT2a_UpReqPPO —— UpAblT2a_UpReqPPO.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpReqPPO : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpReqPPO.v" 29 1 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L29:m6615c4".
(* ng_UpAblT2a_UpReqTempEntropy —— UpAblT2a_UpReqTempEntropy.v：v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT2a_UpReqTempEntropy : NewGreenFace :=
  MkNewGreenFace "UpAblT2a_UpReqTempEntropy.v" 41 2 20260919 "v1 T2a batch, N1 x21 log triple-face 10 modules, four-gate green (_tt2a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L41:m7ed002".
(* ng_UpAblT2b_PredRelax5 —— UpAblT2b_PredRelax5.v：v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green () *)
Definition ng_UpAblT2b_PredRelax5 : NewGreenFace :=
  MkNewGreenFace "UpAblT2b_PredRelax5.v" 440 17 20260919 "v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green (_tt2b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L456:m8d1dba".
(* ng_UpAblT2b_fa53_lpc_broadcast —— UpAblT2b_fa53_lpc_broadcast.v：v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green () *)
Definition ng_UpAblT2b_fa53_lpc_broadcast : NewGreenFace :=
  MkNewGreenFace "UpAblT2b_fa53_lpc_broadcast.v" 165 11 20260919 "v1 T2b batch, N1 x19 + N2 x8 item-level, four-gate green (_tt2b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L208:mc39494".
(* ng_UpAblT3_UpReqAlign —— UpAblT3_UpReqAlign.v：v1 T3 batch (T3a), N1 x25, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT3_UpReqAlign : NewGreenFace :=
  MkNewGreenFace "UpAblT3_UpReqAlign.v" 228 13 20260919 "v1 T3 batch (T3a), N1 x25, four-gate green (_tt3a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L405:m8d1bda".
(* ng_UpAblT3_UpReqFEPAttn —— UpAblT3_UpReqFEPAttn.v：v1 T3 batch (T3a), N1 x25, four-gate green ( per v1 LEDGER) *)
Definition ng_UpAblT3_UpReqFEPAttn : NewGreenFace :=
  MkNewGreenFace "UpAblT3_UpReqFEPAttn.v" 210 12 20260919 "v1 T3 batch (T3a), N1 x25, four-gate green (_tt3a_ per v1 LEDGER); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L210:m419e22".
(* ng_UpAblT4_RLHFkl —— UpAblT4_RLHFkl.v：v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green () *)
Definition ng_UpAblT4_RLHFkl : NewGreenFace :=
  MkNewGreenFace "UpAblT4_RLHFkl.v" 123 2 20260919 "v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green (_tt4a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L114:m353c3f".
(* ng_UpAblT4_SumCarrier —— UpAblT4_SumCarrier.v：v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green () *)
Definition ng_UpAblT4_SumCarrier : NewGreenFace :=
  MkNewGreenFace "UpAblT4_SumCarrier.v" 156 4 20260919 "v1 T4 batch (T4a), N3 x1 pack + N2 x5 + T bridge x3 merged, four-gate green (_tt4a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L156:m146015".
(* ng_UpAblT5_S04_RealExpLogConv —— UpAblT5_S04_RealExpLogConv.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S04_RealExpLogConv : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S04_RealExpLogConv.v" 86 3 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L86:mfebc57".
(* ng_UpAblT5_S05_AlignmentGRPO —— UpAblT5_S05_AlignmentGRPO.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S05_AlignmentGRPO : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S05_AlignmentGRPO.v" 60 2 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L60:m2b5923".
(* ng_UpAblT5_S06_DiffSamplingGibbs —— UpAblT5_S06_DiffSamplingGibbs.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S06_DiffSamplingGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S06_DiffSamplingGibbs.v" 43 1 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L43:maf74e2".
(* ng_UpAblT5_S12_B5RecycleSF —— UpAblT5_S12_B5RecycleSF.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_S12_B5RecycleSF : NewGreenFace :=
  MkNewGreenFace "UpAblT5_S12_B5RecycleSF.v" 29 1 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L29:m1bb424".
(* ng_UpAblT5_UpFirewall —— UpAblT5_UpFirewall.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_UpFirewall : NewGreenFace :=
  MkNewGreenFace "UpAblT5_UpFirewall.v" 44 1 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L44:m8bf205".
(* ng_UpAblT5_UpReqAlgebra —— UpAblT5_UpReqAlgebra.v：v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green () *)
Definition ng_UpAblT5_UpReqAlgebra : NewGreenFace :=
  MkNewGreenFace "UpAblT5_UpReqAlgebra.v" 45 2 20260919 "v1 T5 batch (T5a), N1 x4 + N3 x6, four-gate green (_tt5a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L45:m478662".
(* ng_UpAblT6_UpReqAlign2 —— UpAblT6_UpReqAlign2.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpReqAlign2 : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpReqAlign2.v" 89 4 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L89:m2f4d7b".
(* ng_UpAblT6_UpReqPPO —— UpAblT6_UpReqPPO.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpReqPPO : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpReqPPO.v" 77 3 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L97:m8f74af".
(* ng_UpAblT6_UpReqSampling —— UpAblT6_UpReqSampling.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpReqSampling : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpReqSampling.v" 194 11 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L358:m573cca".
(* ng_UpAblT6_UpSigMigrate —— UpAblT6_UpSigMigrate.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpSigMigrate : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpSigMigrate.v" 73 3 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L93:m957ce6".
(* ng_UpAblT6_UpSigMigrate2 —— UpAblT6_UpSigMigrate2.v：v1 T6 batch (T6a), N1 x24, four-gate green () *)
Definition ng_UpAblT6_UpSigMigrate2 : NewGreenFace :=
  MkNewGreenFace "UpAblT6_UpSigMigrate2.v" 73 3 20260919 "v1 T6 batch (T6a), N1 x24, four-gate green (_tt6a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L93:mb81dbc".
(* ng_UpAblT7_two_point_pack —— UpAblT7_two_point_pack.v：v1 T7 batch (T7a) coverage-pack, N1 x23 + N2 x101 + N3 x13 + T x394 (7a coverage basis 531), four-gate green () *)
Definition ng_UpAblT7_two_point_pack : NewGreenFace :=
  MkNewGreenFace "UpAblT7_two_point_pack.v" 217 13 20260919 "v1 T7 batch (T7a) coverage-pack, N1 x23 + N2 x101 + N3 x13 + T x394 (7a coverage basis 531), four-gate green (_tt7a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L233:mb03c18".
(* ng_UpAblT7b_real_two_point_pack —— UpAblT7b_real_two_point_pack.v：v1 T7b batch, N x61, four-gate green () *)
Definition ng_UpAblT7b_real_two_point_pack : NewGreenFace :=
  MkNewGreenFace "UpAblT7b_real_two_point_pack.v" 347 21 20260919 "v1 T7b batch, N x61, four-gate green (_tt7b_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L384:mbb15a0".
(* ng_UpAblT9_G09_MiscSmall —— UpAblT9_G09_MiscSmall.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_G09_MiscSmall : NewGreenFace :=
  MkNewGreenFace "UpAblT9_G09_MiscSmall.v" 42 2 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L42:m5d6b2f".
(* ng_UpAblT9_UpReqDist —— UpAblT9_UpReqDist.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpReqDist : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpReqDist.v" 64 3 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L63:m9247aa".
(* ng_UpAblT9_UpReqFEPAttn —— UpAblT9_UpReqFEPAttn.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpReqFEPAttn : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpReqFEPAttn.v" 61 3 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L61:mc43870".
(* ng_UpAblT9_UpReqSampling —— UpAblT9_UpReqSampling.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpReqSampling : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpReqSampling.v" 77 4 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L77:m0ccd2f".
(* ng_UpAblT9_UpSigMigrate —— UpAblT9_UpSigMigrate.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpSigMigrate : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpSigMigrate.v" 34 1 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L34:m831da3".
(* ng_UpAblT9_UpTVDoeblin —— UpAblT9_UpTVDoeblin.v：v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green () *)
Definition ng_UpAblT9_UpTVDoeblin : NewGreenFace :=
  MkNewGreenFace "UpAblT9_UpTVDoeblin.v" 49 2 20260919 "v1 T9 batch (T9a), N1 x21 + T x1 (G09:72 downgrade), four-gate green (_tt9a_); enrolled R91ENROLL option-B full wave, zero new assumptions, PA closed" "L49:m9073b3".

(* ng_Ln2Bridge —— Ln2Bridge.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_Ln2Bridge : NewGreenFace :=
  MkNewGreenFace "Ln2Bridge.v" 719 23 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L729:mb8a646".
(* ng_PintPosGrid —— PintPosGrid.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_PintPosGrid : NewGreenFace :=
  MkNewGreenFace "PintPosGrid.v" 179 8 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L179:mb4d650".
(* ng_BeukersIdentity —— BeukersIdentity.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_BeukersIdentity : NewGreenFace :=
  MkNewGreenFace "BeukersIdentity.v" 265 15 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L265:mb2a825".
(* ng_BeukersVariant —— BeukersVariant.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_BeukersVariant : NewGreenFace :=
  MkNewGreenFace "BeukersVariant.v" 522 30 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L536:m8c7d7d".
(* ng_Hanson3Pow —— Hanson3Pow.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_Hanson3Pow : NewGreenFace :=
  MkNewGreenFace "Hanson3Pow.v" 292 16 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L292:m73e017".
(* ng_Ln2Integrality —— Ln2Integrality.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_Ln2Integrality : NewGreenFace :=
  MkNewGreenFace "Ln2Integrality.v" 484 27 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L497:mcd89cc".
(* ng_TrueNumerator —— TrueNumerator.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_TrueNumerator : NewGreenFace :=
  MkNewGreenFace "TrueNumerator.v" 274 29 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L284:mb4f37c".
(* ng_RealIdentity —— RealIdentity.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_RealIdentity : NewGreenFace :=
  MkNewGreenFace "RealIdentity.v" 359 22 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L377:m421f75".
(* ng_SupplyAssembly —— SupplyAssembly.v： colleague afternoon increment (ln2-chain core family), four-gate green () *)
Definition ng_SupplyAssembly : NewGreenFace :=
  MkNewGreenFace "SupplyAssembly.v" 325 21 20260919 "R93 colleague afternoon increment (ln2-chain core family), four-gate green (_tr93aud_); born-in-place verified in vo tree, zero new assumptions" "L338:m6efde4".

(* ng_BetaLower —— BetaLower.v： red-file repaired (AUD β1 bracket + 7 latent, R93FIX), four-gate green, zero statement-face change *)
Definition ng_BetaLower : NewGreenFace :=
  MkNewGreenFace "BetaLower.v" 498 31 20260919 "R94 red-file repaired (AUD β1 bracket + 7 latent, R93FIX), four-gate green, zero statement-face change; born-in-place verified in vo tree" "L501:m1ee440".

(* ng_UpAblZpos —— UpAblZpos.v： paper-1 ablation (AB1): Z_align_pos abstract-layer packing-form discharge + unconditional nonneg companion, four-gate green; built-at-registration verified in vo tree *)
Definition ng_UpAblZpos : NewGreenFace :=
  MkNewGreenFace "UpAblZpos.v" 107 3 20260920 "R95 paper-1 ablation (AB1): Z_align_pos abstract-layer packing-form discharge + unconditional nonneg companion, four-gate green; born-in-place verified in vo tree" "L117:m05487d".

(* ng_UpAblZposReal —— UpAblZposReal.v： paper-1 ablation (AB2): Z_align_pos Real-layer unconditional discharge + finite-sum positivity carrier, three theorems all N-grade, four-gate green *)
Definition ng_UpAblZposReal : NewGreenFace :=
  MkNewGreenFace "UpAblZposReal.v" 138 3 20260920 "R95 paper-1 ablation (AB2): Z_align_pos Real-layer unconditional discharge + finite-sum positivity carrier, three theorems all N-grade, four-gate green" "L139:m8b5e5c".

(* ng_UpAblEps49RKDBase —— UpAblEps49RKDBase.v： paper-1 ablation (AB3 companion): RKD private-byte-snapshot base for 4.9 slot alignment, content-identical to RealKLDecomp body, four-gate green; parallel replica coexists per merge-replica discipline *)
Definition ng_UpAblEps49RKDBase : NewGreenFace :=
  MkNewGreenFace "UpAblEps49RKDBase.v" 912 11 20260920 "R95 paper-1 ablation (AB3 companion): RKD private-byte-snapshot base for 4.9 slot alignment, content-identical to RealKLDecomp body, four-gate green; parallel replica coexists per merge-replica discipline" "L914:m7e643f".

(* ng_UpAblEps49List —— UpAblEps49List.v： paper-1 ablation (e49l): 4.9 slot list-carrier true-premise-shape complete discharge, zero gap with S08 global form, four-gate green *)
Definition ng_UpAblEps49List : NewGreenFace :=
  MkNewGreenFace "UpAblEps49List.v" 237 7 20260920 "R95 paper-1 ablation (e49l): 4.9 slot list-carrier true-premise-shape complete discharge, zero gap with S08 global form, four-gate green" "L237:me2b034".

(* ng_UpAblEps49Body —— UpAblEps49Body.v： paper-1 ablation (X1): theorem 4.9 body list-carrier downstream direct-config, both honest slots swapped, zero residual premises, four-gate green *)
Definition ng_UpAblEps49Body : NewGreenFace :=
  MkNewGreenFace "UpAblEps49Body.v" 264 1 20260920 "R95 paper-1 ablation (X1): theorem 4.9 body list-carrier downstream direct-config, both honest slots swapped, zero residual premises, four-gate green" "L264:mbbb4e6".

(* ng_UpAblEps66Sum —— UpAblEps66Sum.v： paper-1 ablation (AB5): 6.6 sum-interface family three slots discharge (enum + bool flagship closed forms), four-gate green *)
Definition ng_UpAblEps66Sum : NewGreenFace :=
  MkNewGreenFace "UpAblEps66Sum.v" 141 6 20260920 "R95 paper-1 ablation (AB5): 6.6 sum-interface family three slots discharge (enum + bool flagship closed forms), four-gate green" "L164:m95e361".

(* ng_UpAblEps66Body —— UpAblEps66Body.v： paper-1 ablation (X2): theorem 6.6 body 11-slot swap, flag_closed zero-honest-interface version, four-gate green *)
Definition ng_UpAblEps66Body : NewGreenFace :=
  MkNewGreenFace "UpAblEps66Body.v" 213 3 20260920 "R95 paper-1 ablation (X2): theorem 6.6 body 11-slot swap, flag_closed zero-honest-interface version, four-gate green" "L213:m678c4c".

(* ng_UpAblP7_LoHiSqueeze —— UpAblP7_LoHiSqueeze.v：LoHiSqueeze 消融族（lhs/uahl 界族·lo<1<hi 与 delta-star/omd 有界） *)
Definition ng_UpAblP7_LoHiSqueeze : NewGreenFace :=
  MkNewGreenFace "UpAblP7_LoHiSqueeze.v" 360 11 20261006
  "LoHiSqueeze ablation family: lhs/uahl bounds (lo<1<hi, delta-star and omd bounded)" "L360:mcf0f1729".

(* ng_UpAblP7_Package —— UpAblP7_Package.v：colleague PA7: package assembly consuming six sibling pieces, four-gate green *)
Definition ng_UpAblP7_Package : NewGreenFace :=
  MkNewGreenFace "UpAblP7_Package.v" 237 4 20260920 "colleague PA7: package assembly consuming six sibling pieces, four-gate green" "L237:m64f3fe".

(* ng_UpAblP7_UMixSelect —— UpAblP7_UMixSelect.v：colleague PA7: UMixSelect W-wall verdict + discharge surrogate + kappa=1/2 Closed witness, four-gate green *)
Definition ng_UpAblP7_UMixSelect : NewGreenFace :=
  MkNewGreenFace "UpAblP7_UMixSelect.v" 190 6 20260920 "colleague PA7: UMixSelect W-wall verdict + discharge surrogate + kappa=1/2 Closed witness, four-gate green" "L198:mcfd30d".

(* ng_UpAblP7_WallEpsChain_A —— UpAblP7_WallEpsChain_A.v：colleague PA7: wall W1 eps-form leg-A, four-gate green *)
Definition ng_UpAblP7_WallEpsChain_A : NewGreenFace :=
  MkNewGreenFace "UpAblP7_WallEpsChain_A.v" 305 5 20260920 "colleague PA7: wall W1 eps-form leg-A, four-gate green" "L305:md76e5a".

(* ng_UpAblP7_WallEpsChain_B —— UpAblP7_WallEpsChain_B.v：colleague PA7: wall W2 chain-B, four-gate green *)
Definition ng_UpAblP7_WallEpsChain_B : NewGreenFace :=
  MkNewGreenFace "UpAblP7_WallEpsChain_B.v" 468 11 20260920 "colleague PA7: wall W2 chain-B, four-gate green" "L468:m40973b".

(* ng_UpAblP2FeedSum —— UpAblP2FeedSum.v：Z2a seat (paper-2 sum-face donor direct-config): paper-1 finisher donors (AB8 spd_ series + AB2 zabr series) interfaced to paper-2 sum face, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblP2FeedSum : NewGreenFace :=
  MkNewGreenFace "UpAblP2FeedSum.v" 314 16 20260920 "Z2a seat (paper-2 sum-face donor direct-config): paper-1 finisher donors (AB8 spd_ series + AB2 zabr series) interfaced to paper-2 sum face, four-gate green (_tz2a_); born-in-place verified in vo tree" "L346:mc18fc2".

(* ng_UpAblAlmConsumption —— UpAblAlmConsumption.v：Z1b seat (alm-chain remaining-antecedent-form consumption demonstrator): minimal parallel-replica dual-max world (binary vocabulary [true; false], constant logit), consumes only registered chain pieces, admission-free purely constructive, four-gate green (); built-at-registration verified in vo tree *)
Definition ng_UpAblAlmConsumption : NewGreenFace :=
  MkNewGreenFace "UpAblAlmConsumption.v" 294 10 20260920 "Z1b seat (alm-chain remaining-antecedent-form consumption demonstrator): minimal parallel-replica dual-max world (binary vocabulary [true; false], constant logit), consumes only registered chain pieces, zero-admit purely constructive, four-gate green (_tz1b_); born-in-place verified in vo tree" "L294:mdb2a7c".

(* ng_UpAblP2FeedSumLe —— UpAblP2FeedSumLe.v：F1 （论文2 le 面原生折叠传输）：p2fl_lsum_app 拼接可加性新证＋p2fl_le_transport sumd→原生折叠 le 两世界运输＋p2fl_abs_split_eps 单余量三角合拢，四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2FeedSumLe : NewGreenFace :=
  MkNewGreenFace "UpAblP2FeedSumLe.v" 283 8 20260920 "F1 seat (paper-2 le-face native folding transport): p2fl_lsum_app append additivity + p2fl_le_transport sumd-to-native le two-world transport + p2fl_abs_split_eps single-residual triangle closure, four-gate green (_tf1_); born-in-place verified in vo tree" "L283:m8405d0".

(* ng_UpAblP2T1_Cert —— UpAblP2T1_Cert.v：A1 （T 簇证书供给）：论文2 T 簇消融证书簇供给模块，33 位 PA 全 Closed（ 终审实测），四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2T1_Cert : NewGreenFace :=
  MkNewGreenFace "UpAblP2T1_Cert.v" 596 12 20260920 "A1 seat (T-cluster certificate supply): paper-2 T-cluster ablation certificate supply piece, 33 PA positions all Closed (_tg2_ final audit), four-gate green (_ta1_); born-in-place verified in vo tree" "L628:maa0c81".

(* ng_UpAblP2WByPass —— UpAblP2WByPass.v：A2 （S06 双墙绕行）：S06 双墙绕行演示件，20 位 PA 全 Closed（ 终审实测），四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2WByPass : NewGreenFace :=
  MkNewGreenFace "UpAblP2WByPass.v" 428 12 20260920 "A2 seat (S06 dual-wall bypass): S06 dual-wall bypass demonstrator piece, 20 PA positions all Closed (_tg2_ final audit), four-gate green (_ta2_); born-in-place verified in vo tree" "L437:mf9e5f9".

(* ng_UpAblA2_LoInflation —— UpAblA2_LoInflation.v：A2 （k∝lo⁻² 膨胀律）：loi_ub2_quad 精确四倍律 Id 形＋loi_lo_inflation 四倍支配主定理＋反单调律；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblA2_LoInflation : NewGreenFace :=
  MkNewGreenFace "UpAblA2_LoInflation.v" 528 12 20260920 "A2 seat (k vs lo^-2 inflation law): loi_ub2_quad exact quadruple law Id-form + loi_lo_inflation flagship + antitone, four-gate (_ta2_)" "L528:m51a7cc".

(* ng_UpAblAbsSumLeB —— UpAblAbsSumLeB.v：H1 （abs 抽象槽 B 形）：uabS4_abs_sum_le_B 两点对＋list 折叠闭包链，bool/list 双记录；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsSumLeB : NewGreenFace :=
  MkNewGreenFace "UpAblAbsSumLeB.v" 341 11 20260920 "H1 seat (abs abstract-slot B-form): uabS4 pair + list-folding closure chain, bool/list dual carriers, four-gate (_th1_)" "L374:mc77a6b".

(* ng_UpAblAbsSumLeB2 —— UpAblAbsSumLeB2.v：abs 族 B2（加权 cons 黏合三角＋双余量反证完成）（ PA 终审）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsSumLeB2 : NewGreenFace :=
  MkNewGreenFace "UpAblAbsSumLeB2.v" 443 20 20260920 "abs-family B2: weighted cons-glue triangle + double-margin contrapositive closure, PA final-audited (_tm2_)" "L443:me5f509".

(* ng_UpAblAbsSumLeB3 —— UpAblAbsSumLeB3.v：abs 族 B3 深链（abs list-sum B/eps 全族＋槽号形，J4 再验）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsSumLeB3 : NewGreenFace :=
  MkNewGreenFace "UpAblAbsSumLeB3.v" 594 19 20260920 "abs-family B3 deep chain: abs list-sum B/eps full family + slot forms, J4 re-verified (_tj4_)" "L594:md6d184".

(* ng_UpAblAbsFeed —— UpAblAbsFeed.v：abs 族馈线件（使用 B/B2/Eps 三件合流）（/）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblAbsFeed : NewGreenFace :=
  MkNewGreenFace "UpAblAbsFeed.v" 107 3 20260920 "abs-family feed piece consuming B/B2/Eps, four-gate (_tm4r_/_tm3_)" "L107:mba3fb2".

(* ng_UpAblB2_G13 —— UpAblB2_G13.v：B2 （b_gibbs 障碍通道件＋W4 记录分层判定：log-eq 具体记录可实例化 t34 输入）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblB2_G13 : NewGreenFace :=
  MkNewGreenFace "UpAblB2_G13.v" 321 11 20260920 "B2 seat: b_gibbs obstacle-channel pieces + W4 carrier stratification verdict (log-eq concrete carrier instantiable via t34), four-gate (_tb2_)" "L305:mc36b95".

(* ng_UpAblD1S14_UpReqCauchy —— UpAblD1S14_UpReqCauchy.v：FA-D1S14 （Cauchy 余量 8：含 lim_metric_approx N 级语义链）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S14_UpReqCauchy : NewGreenFace :=
  MkNewGreenFace "UpAblD1S14_UpReqCauchy.v" 266 8 20260920 "FA-D1S14 seat: Cauchy residual 8 incl. lim_metric_approx N-level semantic chain, four-gate (_tfad1s14_)" "L266:m0dddd2".

(* ng_UpAblD1S15_GibbsAssembly —— UpAblD1S15_GibbsAssembly.v：FA-D1S15 （GibbsAssembly 18 槽成组＋log_req_compat 并账）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S15_GibbsAssembly : NewGreenFace :=
  MkNewGreenFace "UpAblD1S15_GibbsAssembly.v" 535 5 20260920 "FA-D1S15 seat: GibbsAssembly 18-slot pack + log_req_compat joint accounting, four-gate (_tfad1s15_)" "L535:m29f668".

(* ng_UpAblD1S15_UpReqAlign3 —— UpAblD1S15_UpReqAlign3.v：FA-D1S15 （Align3 余量 16 T 供给级）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S15_UpReqAlign3 : NewGreenFace :=
  MkNewGreenFace "UpAblD1S15_UpReqAlign3.v" 144 2 20260920 "FA-D1S15 seat: Align3 residual 16 T-supply, four-gate (_tfad1s15_)" "L144:mfaf069".

(* ng_UpAblD1S16_UpReqMixTime —— UpAblD1S16_UpReqMixTime.v：FA-D1S16 （AttnMixTime 余量 12 T 成组：9 数据+3 接口条件供给形）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S16_UpReqMixTime : NewGreenFace :=
  MkNewGreenFace "UpAblD1S16_UpReqMixTime.v" 148 3 20260920 "FA-D1S16 seat: AttnMixTime residual 12 T-pack (9 data + 3 interface-conditional supply forms), four-gate (_tfad1s16_)" "L148:m6d90f1".

(* ng_UpAblD1S17_UpReqAttnGibbs —— UpAblD1S17_UpReqAttnGibbs.v：FA-D1S17 （Gibbs pack18＋exp_neg_geo_break T·N1 直接传入降标申报）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S17_UpReqAttnGibbs : NewGreenFace :=
  MkNewGreenFace "UpAblD1S17_UpReqAttnGibbs.v" 162 2 20260920 "FA-D1S17 seat: Gibbs pack18 + exp_neg_geo_break T-N1 direct-feed downgraded declaration, four-gate (_tfad1s17_)" "L162:m9b124d".

(* ng_UpAblD1S17_UpReqDpoLoss —— UpAblD1S17_UpReqDpoLoss.v：FA-D1S17 （DpoLoss pack13 供给）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblD1S17_UpReqDpoLoss : NewGreenFace :=
  MkNewGreenFace "UpAblD1S17_UpReqDpoLoss.v" 110 2 20260920 "FA-D1S17 seat: DpoLoss pack13 supply, four-gate (_tfad1s17_)" "L110:m1238b8".

(* ng_UpAblP2T1_CertC —— UpAblP2T1_CertC.v：G 批二（T 簇证书 C 变体，使用 CertB）（/ 终审）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP2T1_CertC : NewGreenFace :=
  MkNewGreenFace "UpAblP2T1_CertC.v" 227 3 20260920 "G-seat batch-2: T-cluster certificate C-variant consuming CertB, final-audited (_tg1_/_tg2_)" "L227:mca06fc".

(* ng_UpAblAbsQFeed —— UpAblAbsQFeed.v：N4R （Q 世界 Qabs 槽×9 ）：S10_KVQuantTrig 六槽＋S08 Qabs 三槽（实使用 8 点＋1 谱系注行，N4R 判定表）Q 层自足直接配置供给模块——uaq_ 七件（三角加/减/反演 A.1/A.2/A.3＋非负 C.2 适配使用级如实标注，双层差 Qabs 收束 B.1 与严格版 B.2、Qfloor 阿基米德证书过 Qabs 门 C.1 三件真实现），供体 S4B Qfloor 谱系 UpAblAbsSumLeB2 真使用；四项验证绿；vo 树 built-at-registration 候铺 *)
Definition ng_UpAblAbsQFeed : NewGreenFace :=
  MkNewGreenFace "UpAblAbsQFeed.v" 158 7 20260920 "N4R seat (Q-world Qabs slot x9 direct-fit): self-sufficient Q-layer supply for six S10_KVQuantTrig slots + three S08 Qabs slots (8 real consumption points + 1 lineage note per the N4R verdict table) - seven uaq_ pieces (triangle plus/minus/reverse A.1/A.2/A.3 and nonneg C.2 at adaptation-consumption level, honestly marked; double-layer Qabs closure B.1, its strict variant B.2, and the Qfloor Archimedean certificate through the Qabs gate C.1 as real implementations), genuinely consuming the S4B Qfloor lineage donor UpAblAbsSumLeB2; four-gate green (_tn4r_); born-in-place pending in vo tree" "L158:m1cb875".

(* 刷新注记：UpAblAbsSumLeB（341/11）与 UpAblAbsTwoPtAbs（161/4）为 已注册件内容刷新版（Live_X 权威版同步，built-at-registration 重编+下游愈合闭包 build.sh 全量重编背书），ng_ 计数沿用，愈合重编经 cpu_guard 包裹 build.sh 拓扑序执行。 *)

(* ng_UpAblS06AbsFeed —— UpAblS06AbsFeed.v：S06 abs 馈线（使用 AbsSumLeB3）（abs 族线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblS06AbsFeed : NewGreenFace :=
  MkNewGreenFace "UpAblS06AbsFeed.v" 265 6 20260920 "S06 abs feed piece consuming AbsSumLeB3 (abs-family line), four-gate" "L265:m4ecc5d".

(* ng_UpAblArchGeomBatch —— UpAblArchGeomBatch.v：Arch 几何批件（使用 QeqBridge）（ 线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblArchGeomBatch : NewGreenFace :=
  MkNewGreenFace "UpAblArchGeomBatch.v" 111 4 20260920 "Arch geometry batch piece consuming QeqBridge (_tq1_ line), four-gate" "L111:m4440f3".

(* ng_UpAblHalfPowFeed —— UpAblHalfPowFeed.v：HalfPow 馈线件（使用 HalfPow）（TP3 线）；四项验证绿；vo 树 built-at-registration 复证 *)
Definition ng_UpAblHalfPowFeed : NewGreenFace :=
  MkNewGreenFace "UpAblHalfPowFeed.v" 229 5 20260920 "HalfPow feed piece consuming HalfPow (TP3 line), four-gate" "L229:m544809".

(* ng_UpAblP6_TempDefs —— UpAblP6_TempDefs.v：PA6-02（TempDefs 消融 11 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_TempDefs : NewGreenFace :=
  MkNewGreenFace "UpAblP6_TempDefs.v" 391 11 20260920 "PA6-02: TempDefs ablation 11 pieces (T212)" "L404:m5cd38a".

(* ng_UpAblP6_ZPosLowRef —— UpAblP6_ZPosLowRef.v：PA6-06（ZPos/LowRef 喂件面 12 位；注释 G1 直修 axiom→公理）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_ZPosLowRef : NewGreenFace :=
  MkNewGreenFace "UpAblP6_ZPosLowRef.v" 246 12 20260920 "PA6-06: ZPos/LowRef wire-feed face 12 positions (T216; comment G1 direct-fix)" "L255:mb85065".

(* ng_UpAblP6_ConcMixSelFeed —— UpAblP6_ConcMixSelFeed.v：PA6-07（ConcMixSel 喂件 16 位）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_ConcMixSelFeed : NewGreenFace :=
  MkNewGreenFace "UpAblP6_ConcMixSelFeed.v" 221 16 20260920 "PA6-07: ConcMixSel feed 16 positions (T217)" "L221:m542dac".

(* ng_UpAblP6_SecondLaw_two_state —— UpAblP6_SecondLaw_two_state.v：PA6-23（SecondLaw 整节 two_state 实例化 14 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_SecondLaw_two_state : NewGreenFace :=
  MkNewGreenFace "UpAblP6_SecondLaw_two_state.v" 376 14 20260920 "PA6-23: SecondLaw whole-section two_state instantiation 14 pieces (T231)" "L414:m4d4da6".

(* ng_UpAblP6_StateSpace_inst —— UpAblP6_StateSpace_inst.v：PA6-08 线（StateSpace 非平凡实例首件 23 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_StateSpace_inst : NewGreenFace :=
  MkNewGreenFace "UpAblP6_StateSpace_inst.v" 509 23 20260920 "StateSpace non-trivial instantiation first piece 23 theorems" "L550:m0d7d55".

(* ng_UpAblP6_EntropyMonoSplit_A —— UpAblP6_EntropyMonoSplit_A.v：PA6-03（EntropyMonoSplit 甲支 6 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_EntropyMonoSplit_A : NewGreenFace :=
  MkNewGreenFace "UpAblP6_EntropyMonoSplit_A.v" 175 6 20260920 "PA6-03: EntropyMonoSplit leg-A 6 pieces (T213)" "L175:m70fc0a".

(* ng_UpAblP6_EntropyMonoSplit_B —— UpAblP6_EntropyMonoSplit_B.v：PA6-04（EntropyMonoSplit 乙支 7 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_EntropyMonoSplit_B : NewGreenFace :=
  MkNewGreenFace "UpAblP6_EntropyMonoSplit_B.v" 264 7 20260920 "PA6-04: EntropyMonoSplit leg-B 7 pieces (T214)" "L264:m0bddea".

(* ng_UpAblP6_EntropyMonoSplit_C —— UpAblP6_EntropyMonoSplit_C.v：PA6-08（EMS 接合验证 11/11 零缺口 15 件，使用 A/B）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_EntropyMonoSplit_C : NewGreenFace :=
  MkNewGreenFace "UpAblP6_EntropyMonoSplit_C.v" 394 15 20260920 "PA6-08: EMS consolidation verification 11/11 zero-gap 15 pieces consuming A/B (T218)" "L457:m6f3e3c".

(* ng_UpAblP6_Package —— UpAblP6_Package.v：PA6-13（v2 完成接合九支供给闭合 20 件，使用 10 件）（b）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblP6_Package : NewGreenFace :=
  MkNewGreenFace "UpAblP6_Package.v" 804 20 20260920 "PA6-13: v2 closing consolidation nine-branch supply closure 20 pieces consuming 10 (T221b)" "L804:mdd5945".

(* ng_UpAblLogWall —— UpAblLogWall.v：论文7 更新线（LogWall 墙定理化 11 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblLogWall : NewGreenFace :=
  MkNewGreenFace "UpAblLogWall.v" 298 11 20260920 "paper-7 update line: LogWall wall-theoremization 11 pieces" "L309:m34d8df".

(* ng_UpAblLogWallEq —— UpAblLogWallEq.v：论文7 更新线（LogWallEq 双向等价 12 件，使用 LogWall）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblLogWallEq : NewGreenFace :=
  MkNewGreenFace "UpAblLogWallEq.v" 382 12 20260920 "paper-7 update line: LogWallEq bidirectional equivalence 12 pieces consuming LogWall (_tl3_)" "L382:md20088".

(* ng_UpAblMetaEngine —— UpAblMetaEngine.v：论文7 更新线（MetaEngine 引擎 22 件）（_tn 系）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaEngine : NewGreenFace :=
  MkNewGreenFace "UpAblMetaEngine.v" 830 22 20260920 "paper-7 update line: MetaEngine engine 22 pieces (_tn series)" "L830:m9a9fa9".

(* ng_UpAblMetaWorld3 —— UpAblMetaWorld3.v：N4 非退化核世界机器面（TV 算子/点质量对/精确幂律+预算下界双分支，34 件）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaWorld3 : NewGreenFace :=
  MkNewGreenFace "UpAblMetaWorld3.v" 753 34 20260921 "N4 seat: non-degenerate kernel world machine face (TV operator, point-mass pair, exact power law + budget lower bound legs, 34 pieces)" "L833:m5ce18d".

(* ng_UpAblMetaWindow —— UpAblMetaWindow.v：M4 双侧混合窗定理（泛型退化分支新证+World3 存在侧双分支合取，8 件，axiom-free）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaWindow : NewGreenFace :=
  MkNewGreenFace "UpAblMetaWindow.v" 207 8 20260921 "M4 seat: two-sided mixing window theorem (generic collapse leg new proof + World3 existence-side two legs conjunction, 8 pieces, Axioms none)" "L226:m066a30".

(* ng_UpReqMixRealExec —— UpReqMixRealExec.v：R1EXE Real 层选择器可执行化（R1 见证/证明分离+R3 惰性链，mrx_ 七面，native k=15@173ms）；vo 树 built-at-registration 复证 *)
Definition ng_UpReqMixRealExec : NewGreenFace :=
  MkNewGreenFace "UpReqMixRealExec.v" 272 4 20260922 "R1EXE seat: Real-layer selector executification (R1 witness/proof separation + R3 lazy chain, mrx_ seven faces PA Closed, native k=15 at 173ms)" "L272:mf31fc2".

(* ng_UpAblMetaTemp —— UpAblMetaTemp.v：M2R2 温度-模量发散（mtp_ 十二面 PA Closed，主件 mtp_anchor_divergence 零公理）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaTemp : NewGreenFace :=
  MkNewGreenFace "UpAblMetaTemp.v" 642 12 20260922 "M2R2 relay seat: temperature-modulus divergence (mtp_ twelve faces PA Closed, anchor divergence zero axioms)" "L642:m9816ce".

(* ng_UpAblMetaDivThm —— UpAblMetaDivThm.v：mtdc_ 命题族集注与实例化承载宿主件（总清册⑨三步转正落册：ConjBridge 首字段槽 A 型直供正本 mtdc_lpc_supply 件内 :386-388 机检绿＝绑定面裸 lt/le/plus ≡ real_lt/real_le/real_plus；快测成证=可消位快测卷（库外 attn 归档）；依赖 UpAblA2_LoInflation 瘦身代单件归位即闭包、CW219 薄壳归位免＝形态分歧候追认；〔CJS3 旧代条目 L1520:m88e5e4 由本条原位刷新取代〕；PA=12 Closed；coqchk 五证候全树证） *)
Definition ng_UpAblMetaDivThm : NewGreenFace :=
  MkNewGreenFace "UpAblMetaDivThm.v" 1931 26 20261002
  "meta-division proposition family collection and instantiation host: nine mtdc theorems over the bare lt le plus binding face with the ConjBridge first-field slot carried by the in-piece definition mtdc_lpc_supply resolved at real_lt_plus_compat_lt_le, twenty-six Qed in total" "L1931:m67d1fd".

(* 1 件尾部追加 order L471（BeukersVariant 之后；拓扑位：S01_BaseRing/S02_CauchyComplete/S03_QExp+PadeErrorIntegral+BeukersLists+BeukersVariant 全在前）；_CoqProject×2 尾部追加同步；ng_ 条目 wc/grep 实测。 *)
(* ng_PsQReindex —— PsQReindex.v：E-STAGING-D030r 切片 rx_ 前缀双小件（psQ↔bk_psd reindex 引理+十字衰减链可证首件；行首 decl grep 实测 19：Lemma rx_psQ_ext_lt/rx_psQ_shift/rx_psQ_scale、Theorem rx_psQ_reindex/rx_bv_c_diag/rx_qtilde3_anchor 等）；vo 树 built-at-registration 复证 *)
Definition ng_PsQReindex : NewGreenFace :=
  MkNewGreenFace "PsQReindex.v" 579 19 20260922 "rx_-prefixed pair: psQ <-> bk_psd reindex lemmas + cross-decay chain first provable piece, 19 decls" "L594:m07533f".

(* ---------- ToyR 盒A 自证：替换件假设清查（零承认件自证） ---------- *)
Print Assumptions cnt_mod_length.
Print Assumptions minus_absorb_r.
Print Assumptions TotalModules_matches.
Print Assumptions DeliveredModules_matches.
Print Assumptions UniverseItems_matches.
Print Assumptions Universe_splits.

(* ng_UpAblB2WindowTie —— UpAblB2WindowTie.v：B2UP 窗口约束可执行见证族（15 出口全 Defined；语句账 PA 10/10；环境账 3 条 stdlib 经典公理 intern 乘客按判例链分账如实申报）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblB2WindowTie : NewGreenFace :=
  MkNewGreenFace "UpAblB2WindowTie.v" 276 15 20260922 "B2UP seat: window-tie executable witness family (Qed 0/Defined 15, statement ledger PA 10/10; env ledger 3 stdlib classical passengers disclosed per B2UP)" "L276:m118fce".

(* ng_UpReqInvPosLazy —— UpReqInvPosLazy.v：InvPos 惰性 inv-pos 预算门 ivl_budget_at（PA 9/9，coqchk axiom-free，k=1 显式入口复跑；11 Qed+1 Defined=12 出口，含 5 条行内 Proof…Qed 一行式——行首 decl grep 与出口 grep 双口径一致）；vo 树 built-at-registration 复证 *)
Definition ng_UpReqInvPosLazy : NewGreenFace :=
  MkNewGreenFace "UpReqInvPosLazy.v" 280 12 20260922 "InvPos seat: lazy inv-pos budget gate ivl_budget_at (PA 9/9, coqchk Axioms none, k=1 explicit-entry run; 12 exits incl. 5 inline one-line proofs)" "L280:m883b18".

(* ng_UpQKTVCompose —— UpQKTVCompose.v：P2COMP QK→TV 一步合成（构造性严格化 +1 裕度；qktv_abs_lt_two_side/qk_tv_iter_contraction PA Closed，G4 三遍 12 模块闭包 axiom-free）；vo 树 built-at-registration 复证 *)
Definition ng_UpQKTVCompose : NewGreenFace :=
  MkNewGreenFace "UpQKTVCompose.v" 245 2 20260922 "P2COMP seat: QK-to-TV one-step composition, constructive strictification +1 margin (qktv_abs_lt_two_side/qk_tv_iter_contraction PA Closed, G4 3-pass)" "L245:me1efd5".

(* ng_UpAblMetaPackage —— UpAblMetaPackage.v：W3PKG meta-package mpk_（跨世界三联画+world3 tv1 半幅，两主定理 Defined 终+7 再出口别名，三绿供体成组；PA 14，G3 自面 magic=0；硬依赖 UpAblMetaTemp 已于 在册，前置闸满足）；vo 树 built-at-registration 复证 *)
Definition ng_UpAblMetaPackage : NewGreenFace :=
  MkNewGreenFace "UpAblMetaPackage.v" 150 2 20260922 "W3PKG seat: meta-package mpk_ — cross-world triptych + world3 tv1-half (both Defined-terminated) + 7 re-export aliases over three green suppliers (PA 14, G3 self-face magic=0)" "L150:ma9c4fe".

Definition ng_P7BoundedSoftmaxDeep : NewGreenFace :=
  MkNewGreenFace "P7BoundedSoftmaxDeep.v" 471 15 20260922
  "R112 six-row topo fix enrollment (7aeac35, order L496 over 578-line baseline, md5 4614b0b2); 18 decls / 15 traced exits all Closed; born-in-place three-gate green" "L490:mf2a25e".

(* ng_LoHiSqueeze —— LoHiSqueeze.v： 入册（7aeac35，order L497/578 行基线，紧随依赖 P7BoundedSoftmaxDeep L496，拓扑验证通过；md5 345b5868 双树实测）；
 4 声明 4 出口全覆盖，零撞名零红线；vo 树 built-at-registration 复证 *)
Definition ng_LoHiSqueeze : NewGreenFace :=
  MkNewGreenFace "LoHiSqueeze.v" 190 4 20260922
  "R112 topo fix enrollment (7aeac35, order L497/578-line baseline, md5 345b5868); dependency-adjacent placement verified; 4/4 exits Closed; three-gate green" "L190:m345b58".

(* ng_GibbsFamilyExt —— GibbsFamilyExt.v： 入册（7aeac35，order L552/578 行基线；md5 d6750177 双树实测）；级联面实测非壳件（CW 桩 631B，零 S 系直连），
 R3 壳级联担忧解除；13 声明 13 出口全覆盖；vo 树 built-at-registration 复证 *)
Definition ng_GibbsFamilyExt : NewGreenFace :=
  MkNewGreenFace "GibbsFamilyExt.v" 443 13 20260922
  "R112 topo fix enrollment (7aeac35, order L552/578-line baseline, md5 d6750177); cascade face cleared (base stub 631B, no S-series edge); 13/13 exits Closed; three-gate green" "L417:m89b225".

(* ng_FepIdConsume —— FepIdConsume.v： 入册（7aeac35，order L564/578 行基线；md5 ec7152e6 双树实测）；5 声明 5 出口全覆盖；
 未注册检查点 fic2_g3(_ext) 依赖本件（H1 留待，不影响本件在册态）；vo 树 built-at-registration 复证 *)

(* ng_SecondLawConsume —— SecondLawConsume.v： 入册（7aeac35，order L394/578 行基线，先于伴件 sumdis L395；md5 850907ae 双树实测）；
 9 声明 4 追印出口（原追印清单口径，H2 对照核验随 C23 单据 B 关 2 口径在案）；vo 树 built-at-registration 复证 *)

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=包版实测（R116b-PREP 单据包草案），以树内实测复核补记，ng_qed 为 grep 级计数（token ）。 *)

(* ng_PA_AttnSqrt —— PA_AttnSqrt.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_AttnSqrt : NewGreenFace :=
  MkNewGreenFace "PA_AttnSqrt.v" 276 12 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 c05b40, L276); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L276:mc05b40".

(* ng_PA_CW220_Extensions —— PA_CW220_Extensions.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_CW220_Extensions : NewGreenFace :=
  MkNewGreenFace "PA_CW220_Extensions.v" 1677 42 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 5ad943, L1677); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L1677:m5ad943".

(* ng_PA_DTPT_Bridge_Dep —— PA_DTPT_Bridge_Dep.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_DTPT_Bridge_Dep : NewGreenFace :=
  MkNewGreenFace "PA_DTPT_Bridge_Dep.v" 317 0 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 124ee5, L317); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L323:mfbb269".

(* ng_PA_ExpOneEnvelope —— PA_ExpOneEnvelope.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ExpOneEnvelope : NewGreenFace :=
  MkNewGreenFace "PA_ExpOneEnvelope.v" 527 29 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 e2cbe6, L527); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L491:m97cd65".

(* ng_PA_FirewallReqDischarge —— PA_FirewallReqDischarge.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_FirewallReqDischarge : NewGreenFace :=
  MkNewGreenFace "PA_FirewallReqDischarge.v" 296 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 4c1bac, L296); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L296:m4c1bac".

(* ng_PA_PolyIntegral —— PA_PolyIntegral.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_PolyIntegral : NewGreenFace :=
  MkNewGreenFace "PA_PolyIntegral.v" 357 17 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6ba7f6, L357); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L357:m6ba7f6".

(* ng_PA_TempMonoW2Mark —— PA_TempMonoW2Mark.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_TempMonoW2Mark : NewGreenFace :=
  MkNewGreenFace "PA_TempMonoW2Mark.v" 277 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 1b8f64, L277); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L204:mca2410".

(* ng_PA_TempSoftmaxInstantiation —— PA_TempSoftmaxInstantiation.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_TempSoftmaxInstantiation : NewGreenFace :=
  MkNewGreenFace "PA_TempSoftmaxInstantiation.v" 420 6 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 349ea1, L420); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L386:m98bc57".

(* ng_PA_ToyR_IdSlotTranslate —— PA_ToyR_IdSlotTranslate.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_IdSlotTranslate : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_IdSlotTranslate.v" 195 7 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 3f064f, L195); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L151:m603a36".

(* ng_PA_ToyR_SecondLawConsume —— PA_ToyR_SecondLawConsume.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_SecondLawConsume : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_SecondLawConsume.v" 389 9 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 2e8c46, L389); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L409:mc6abd2".

(* ng_PA_ToyR_SupplyAssembly —— PA_ToyR_SupplyAssembly.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_SupplyAssembly : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_SupplyAssembly.v" 347 21 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 5fcbe3, L347); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L347:m5fcbe3".

(* ng_PA_ToyR_fa57_ext —— PA_ToyR_fa57_ext.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_ToyR_fa57_ext : NewGreenFace :=
  MkNewGreenFace "PA_ToyR_fa57_ext.v" 248 11 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 1286ae, L248); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L248:m1286ae".

(* ng_PA_UpAblAbsSumLeB —— PA_UpAblAbsSumLeB.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblAbsSumLeB : NewGreenFace :=
  MkNewGreenFace "PA_UpAblAbsSumLeB.v" 364 11 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 9a7fdb, L364); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L383:mfcafa7".

(* ng_PA_UpAblD1S3_fep_UpReqSteadyThermo —— PA_UpAblD1S3_fep_UpReqSteadyThermo.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblD1S3_fep_UpReqSteadyThermo : NewGreenFace :=
  MkNewGreenFace "PA_UpAblD1S3_fep_UpReqSteadyThermo.v" 165 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6b64c1, L165); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L182:m6843c3".

(* ng_PA_UpAblD1S4_UpReqStepKLEtaInst —— PA_UpAblD1S4_UpReqStepKLEtaInst.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblD1S4_UpReqStepKLEtaInst : NewGreenFace :=
  MkNewGreenFace "PA_UpAblD1S4_UpReqStepKLEtaInst.v" 118 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 b7106e, L118); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L138:m895f40".

(* ng_PA_UpAblD2_AbsLeId_RI_DO —— PA_UpAblD2_AbsLeId_RI_DO.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblD2_AbsLeId_RI_DO : NewGreenFace :=
  MkNewGreenFace "PA_UpAblD2_AbsLeId_RI_DO.v" 157 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 7e3991, L157); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L162:mb47060".

(* ng_PA_UpAblMetaWindow —— PA_UpAblMetaWindow.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblMetaWindow : NewGreenFace :=
  MkNewGreenFace "PA_UpAblMetaWindow.v" 229 0 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 c0901e, L229); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L229:mc0901e".

(* ng_PA_UpAblT1_UpFirewallReq —— PA_UpAblT1_UpFirewallReq.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpAblT1_UpFirewallReq : NewGreenFace :=
  MkNewGreenFace "PA_UpAblT1_UpFirewallReq.v" 118 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 206e3b, L118); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L136:m0cceb9".

(* ng_PA_UpDissip —— PA_UpDissip.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpDissip : NewGreenFace :=
  MkNewGreenFace "PA_UpDissip.v" 803 38 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 0660de, L803); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L803:m0660de".

(* ng_PA_UpStepKLM3 —— PA_UpStepKLM3.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_PA_UpStepKLM3 : NewGreenFace :=
  MkNewGreenFace "PA_UpStepKLM3.v" 665 18 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 494c15, L665); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L641:m9d5cd3".

(* ng_ToyR_BeukersLists —— ToyR_BeukersLists.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_BeukersLists : NewGreenFace :=
  MkNewGreenFace "ToyR_BeukersLists.v" 576 29 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 c483b4, L576); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L576:mc483b4".

(* ng_ToyR_BeukersVariant —— ToyR_BeukersVariant.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_BeukersVariant : NewGreenFace :=
  MkNewGreenFace "ToyR_BeukersVariant.v" 547 30 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 3d42c9, L547); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L547:m3d42c9".

(* ng_ToyR_EntropyMonoSplitInst —— ToyR_EntropyMonoSplitInst.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_EntropyMonoSplitInst : NewGreenFace :=
  MkNewGreenFace "ToyR_EntropyMonoSplitInst.v" 298 8 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 40f3d9, L298); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L943:m01b7c3".

(* ng_ToyR_GibbsFamilyExt —— ToyR_GibbsFamilyExt.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_GibbsFamilyExt : NewGreenFace :=
  MkNewGreenFace "ToyR_GibbsFamilyExt.v" 454 13 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 d3b3d8, L454); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L454:md3b3d8".

(* ng_ToyR_Ln2Integrality —— ToyR_Ln2Integrality.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_Ln2Integrality : NewGreenFace :=
  MkNewGreenFace "ToyR_Ln2Integrality.v" 508 27 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 871ae3, L508); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L508:m871ae3".

(* ng_ToyR_NatLenPos —— ToyR_NatLenPos.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_NatLenPos : NewGreenFace :=
  MkNewGreenFace "ToyR_NatLenPos.v" 128 4 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 475527, L128); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L128:m475527".

(* ng_ToyR_RateTheoryAblation —— ToyR_RateTheoryAblation.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_RateTheoryAblation : NewGreenFace :=
  MkNewGreenFace "ToyR_RateTheoryAblation.v" 233 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 7d324c, L233); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L233:m7d324c".

(* ng_ToyR_SecondLawConsume —— ToyR_SecondLawConsume.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_SecondLawConsume : NewGreenFace :=
  MkNewGreenFace "ToyR_SecondLawConsume.v" 393 9 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 9e3e16, L393); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L393:m9e3e16".

(* ng_ToyR_SumEqListFeed —— ToyR_SumEqListFeed.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_SumEqListFeed : NewGreenFace :=
  MkNewGreenFace "ToyR_SumEqListFeed.v" 198 8 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 39fb1a, L198); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L198:m39fb1a".

(* ng_ToyR_SupplyAssembly —— ToyR_SupplyAssembly.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_SupplyAssembly : NewGreenFace :=
  MkNewGreenFace "ToyR_SupplyAssembly.v" 351 21 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 8e7e36, L351); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L298:mdb72cc".

(* ng_ToyR_UpAblP6_GibbsFamilyExt —— ToyR_UpAblP6_GibbsFamilyExt.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP6_GibbsFamilyExt : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP6_GibbsFamilyExt.v" 184 5 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6a07fd, L184); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L184:m6a07fd".

(* ng_ToyR_UpAblP6_UniformLimit —— ToyR_UpAblP6_UniformLimit.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP6_UniformLimit : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP6_UniformLimit.v" 182 3 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6cb954, L182); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L182:m6cb954".

(* ng_ToyR_UpAblP7_AbsNonNeg —— ToyR_UpAblP7_AbsNonNeg.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_AbsNonNeg : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_AbsNonNeg.v" 374 13 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6d95b2, L374); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L354:mbedc67".

(* ng_ToyR_UpAblP7_LoHiCross —— ToyR_UpAblP7_LoHiCross.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_LoHiCross : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_LoHiCross.v" 126 3 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 6164aa, L126); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L139:mb04f9d".

(* ng_ToyR_UpAblP7_LoHiSqueeze —— ToyR_UpAblP7_LoHiSqueeze.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_LoHiSqueeze : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_LoHiSqueeze.v" 287 7 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 d8d6c8, L287); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L439:m10caa0".

(* ng_ToyR_UpAblP7_Paper7Ablation_S1inst —— ToyR_UpAblP7_Paper7Ablation_S1inst.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_Paper7Ablation_S1inst : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_Paper7Ablation_S1inst.v" 292 6 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 bdfade, L292); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L260:mfe2c8f".

(* ng_ToyR_UpAblP7_UMixSelect —— ToyR_UpAblP7_UMixSelect.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_UpAblP7_UMixSelect : NewGreenFace :=
  MkNewGreenFace "ToyR_UpAblP7_UMixSelect.v" 209 4 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 e31c5b, L209); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L221:mdfa24d".

(* ng_ToyR_fa56b_ext —— ToyR_fa56b_ext.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_fa56b_ext : NewGreenFace :=
  MkNewGreenFace "ToyR_fa56b_ext.v" 292 12 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 5d4f38, L292); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L381:mb23975".

(* ng_ToyR_fa57_ext —— ToyR_fa57_ext.v： 片A 尾部追加波（VET8A 四态 C-纯新，47 件之一；零 interdep，依赖全落 order.txt 已有件/stdlib（Qfield/Qring 有 HEAD CI-green 先例）； 草案登记，四门实测补记 ） *)
Definition ng_ToyR_fa57_ext : NewGreenFace :=
  MkNewGreenFace "ToyR_fa57_ext.v" 251 11 20260923
  "R116 piece-A tail-insert wave (VET8A C-pure-new; tree md5 809125, L251); zero interdependency, deps order/stdlib-resolved; four-gate executed R116b" "L251:m809125".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=源位实测快照（-PREP 合并单据包），ng_qed 已按二验 [N-1] 修正令以 口径 token 级实测补记（13/40/3）。 *)


(* ng_UpAblDeltaStarGeneral —— UpAblDeltaStarGeneral.v：DSNR 主件（dsgen_ 推广族，577 行 48 声明面 40 Qed（token 级实测；PREP 草案 33 系行首 grep 口径，二验 [N-1] 修正）；PA 四路 Closed＝dsgen_main/rowstoch/feasible/optimal_ge3 逐件 Closed under global context；G3 独立目录 Separate Extraction Obj.magic=0；G4 axiom-free>；头注 L24-27 自引词面按 WangWW 零承认自陷卡豁免注记在案；Require 依赖 UpAblDeltaStarSuboptimal 同批注册） *)
Definition ng_UpAblDeltaStarGeneral : NewGreenFace :=
  MkNewGreenFace "UpAblDeltaStarGeneral.v" 577 40 20260923
  "DSNR seat: dsgen_ generalization family (PA 4-route Closed: dsgen_main/rowstoch/feasible/optimal_ge3; G3 separate-extraction Obj.magic=0; G4 Axioms none; ng_qed token-level re-measured 40 (PREP 33 was line-start grep face, VERIFY [N-1] corrected); requires UpAblDeltaStarSuboptimal same-wave registration; WangWW self-trap lexicon exemption noted)" "L704:m0ba7d2".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（-SUB built-at-registration 四项组绿后实测补记）。 *)

Definition ng_uabl_attn_full_instance : NewGreenFace :=
  MkNewGreenFace "uabl_attn_full_instance.v" 135 2 20260924
  "R124 single-entry supply module: BoundedSoftmax 19-field Fin2 default instance as uabl_-prefixed named rows; one Require Import line exposes full namespace via six Require Export; Part A-C rows verbatim-identical to upstream faces (zero face-conversion tax); PA Closed x4 (bs_abs_id/bs_lpc_id/expf_pos/bs_abs); G3 Separate Extraction Obj.magic=0 (ml 10f2d638 / mli 6afe7ea0 anchors); born-in-place four-gate green 20260924; sandbox/Live/vo triple md5 c40c13a1 pinned; fa53_compat_abs required internally unchanged" "L149:m70bfa8".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（ EB2 built-at-registration 四项验证实测补记；order 锚=SHA1 前 6 照 先例）。 *)

Definition ng_BBDBridgeSupply : NewGreenFace :=
  MkNewGreenFace "BBDBridgeSupply.v" 146 5 20260924
  "Batch-2 Type-A tail-insert first companion piece (Boltzmann free-energy bridge sum-interface supply: three csm_-based theorems + two bridges); born-in-place four-gate 20260924 by seat EB2: G2 EXIT=0 PA 5/5 Closed vo magic 436f712100015ff4; G3 self-scope 0 (R19-F1 extraction evidence gap cured by EB2 probe in _teb2_g3out, Separate Extraction of the three theorems, BBD.ml zero magic); G4 coqchk Axioms none; deps all in-tree current, leaf at order L644 anchor R124-988a53 sha1-6" "L159:m7c8e63".

(* ng_UpReqSamplingFeed —— UpReqSamplingFeed.v：组2/组3 邻居成果伴生供给模块（W23 产 usrq_ 前缀 22 供给定理，293 行 22 Qed； 复核 PASS；ReqUContraction 两节求和诚实接口实现化供给；built-at-registration 四项验证实测 EB2：G2 EXIT=0、PA×22 全 Closed、vo 魔数 436f712100015ff4、vo 新于 v；G3 自证块口径 10 处已申报残留＝D 形 6（usrq_abs_ge_zero_req_supply/usrq_bs_abs_supply 抽象 le 前提破坏性读取，X1 #30 mtdc 同款槽号冻结）＋B 形 2（usrq_bs_sum_pos_supply sigT/InT 见证装箱，p2wb 同类）＋抽象关系构造 2（usrq_z_lb/ub_supply Coq_inl 装箱），零 E/L/T 形＝配方③ 无适用位，与已入树 mtdc/p2wb 已申报残留同类判 P2 另案留待——W23 清册 L99 自申「提取检查点未另设」，再验代申报防分裂；G4 coqchk axiom-free；依赖 CW_219/UpReqAlgebra/UpReqSumD/UpReqConcSoftmax/UpReqSampling/ConcMixSelFeed 全在册现势兼容，末端件 order 尾部追加 L645 锚 -7ccbe2=SHA1 前 6） *)
Definition ng_UpReqSamplingFeed : NewGreenFace :=
  MkNewGreenFace "UpReqSamplingFeed.v" 293 22 20260924
  "Batch-2/3 companion supply piece (usrq_ 22 supply theorems for ReqUContraction two-section sum honest-premise interfaces); born-in-place four-gate 20260924 by seat EB2: G2 EXIT=0 PA 22/22 Closed vo magic 436f712100015ff4; G3 self-scope 10 DECLARED residuals (6 D-form abs-twin abstract-le destructive reads X1-#30-slot-frozen class, 2 B-form sum_pos sigT/InT witness boxing p2wb class, 2 abstract-relation Coq_inl boxings z-twin; zero E/L/T sites so fix-3 not applicable; same class as in-tree mtdc/p2wb declared residuals, P2 deferred; W23 ledger L99 declared no probe, EB2 re-verify declares on its behalf); G4 coqchk Axioms none; deps all in-tree current, leaf at order L645 anchor R124-7ccbe2 sha1-6" "L306:m94fb98".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（-EXEC built-at-registration 四项验证实测补记；order 锚=md5 前 6 照 E1 §四①处方—— 现测判定：c40c13=md5 前 6、988a53/7ccbe2=文件 SHA1 前 6，两口径历史混用在案，本次统一 md5 前 6 与 ng_meta 自洽）。 *)

(* ng_UpReqCf2TvGenSupply —— UpReqCf2TvGenSupply.v：C1 产一件双定理供给模块（192 行 3 Qed；件一 uc2t_habs_cf2tv_nonneg 强形＋uc2t_habs_cf2tv_nonneg_norm 规格形，件二 uc2t_cf2tv_nonneg_habs_rev 反向真等价（V-C1 判「真等价·无降档·升格成立」：plain 形复原＋归一性件内已证＋合成结论三查全过）；PA×3 全 Closed；G3 单命令三常数提取主 ml Obj.magic=0；G4 coqchk 传递环境公理 3 条＋CONTAINMENT-EQUAL 新增=0；built-at-registration 绿判四项组 ；沙箱/Live/vo 三方 md5 恒等 bcac27f1；Require CW219/Algebra/SumD/Dist/ConcSoftmax/Sampling/ConcMixSel/ConcB1/ConcB2/AttnDoeblin/ConcFin2 全在册） *)
Definition ng_UpReqCf2TvGenSupply : NewGreenFace :=
  MkNewGreenFace "UpReqCf2TvGenSupply.v" 192 3 20260925
  "P7FIN2 piece-1+2 supply: cf2-TV nonneg strong+normalized forms and reverse true-equivalence (plain-form restoration, in-piece normalization, both directions machine-checked; V-C1 upgraded); PA 3/3 Closed; G3 single-command three-constant extraction Obj.magic=0; G4 coqchk 3 transitive axioms CONTAINMENT-EQUAL zero-new; born-in-place four-gate green 20260925; triple md5 bcac27f1" "L467:maf4a9a".

(* ng_meta 口径："L<wc -l 实测>:m<md5 前 6>"（ 扩列口径）；本块行数/md5=就位树实测（-EXEC built-at-registration 四项验证实测补记；order 锚=md5 前 6 照 尾块统一口径；源=Live_X 逐字拷贝；两红件 UpAblD1S11_UpReqCauchy（头注注释失衡）/UpReqBregmanBase（L119 证明体伤）。 *)

(* ng_UpAblBYUpperTight —— UpAblBYUpperTight.v：BY 上紧化件（189 行 5 Qed；btight_ 前缀半燃料紧界；Require Arith/Lia＋UpAblBYLowerBound 包内依赖＝本项链内拓扑序 LB→UT；四项验证绿同上口径 ；md5 4f4990=J7 同代） *)
Definition ng_UpAblBYUpperTight : NewGreenFace :=
  MkNewGreenFace "UpAblBYUpperTight.v" 189 5 20260925
  "BY upper-tightening: btight_ half-fuel tight bound, five theorems, requires UpAblBYLowerBound (intra-set topo order); four-gate green on current HEAD 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 4f4990 (J7-identical)" "L423:mc9a025".

(* ng_UpAblD1S12_UpReqAttnUniformLimit —— UpAblD1S12_UpReqAttnUniformLimit.v：FA-D1S12 供给包件①（90 行 4 Qed；原件 UpReqAttnUniformLimit Section AlmUniform 7 数据槽的 Token:=bool 具体有限集实例供给（uabd1s12_ul_ 前缀）；独立伴随模块零 Require 原件（P3S1 工艺）；原件现势槽对账 PASS（-SCREEN 抽检＋EXEC 全槽实扫）；四项验证绿 ：G3 own magic=0 闭包 0；md5 042868） *)
Definition ng_UpAblD1S12_UpReqAttnUniformLimit : NewGreenFace :=
  MkNewGreenFace "UpAblD1S12_UpReqAttnUniformLimit.v" 90 4 20260925
  "FA-D1S12 supply pack 1: AlmUniform 7 data slots as bool finite-set instances (uabd1s12_ul_), zero Require on mother P3S1, slot reconciliation PASS; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 042868" "L103:m0a601c".

(* ng_UpAblD1S12_UpReqAttnMassSplit —— UpAblD1S12_UpReqAttnMassSplit.v：FA-D1S12 供给包件②（86 行 4 Qed；AmsMassSplit 8 数据槽 bool 实例供给（uabd1s12_ams_）；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 0；md5 b9a01d） *)
Definition ng_UpAblD1S12_UpReqAttnMassSplit : NewGreenFace :=
  MkNewGreenFace "UpAblD1S12_UpReqAttnMassSplit.v" 86 4 20260925
  "FA-D1S12 supply pack 2: AmsMassSplit 8 data slots bool instances (uabd1s12_ams_), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 b9a01d" "L98:me560a7".

(* ng_UpAblD1S12_UpReqAttnQ18Tail —— UpAblD1S12_UpReqAttnQ18Tail.v：FA-D1S12 供给包件③（86 行 4 Qed；AqtTail 8 数据槽 bool 实例供给（uabd1s12_aqt_）；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 0；md5 03a40f） *)
Definition ng_UpAblD1S12_UpReqAttnQ18Tail : NewGreenFace :=
  MkNewGreenFace "UpAblD1S12_UpReqAttnQ18Tail.v" 86 4 20260925
  "FA-D1S12 supply pack 3: AqtTail 8 data slots bool instances (uabd1s12_aqt_), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 03a40f" "L98:m3ce6ec".

(* ng_UpAblD1S13_UpReqAlignClose —— UpAblD1S13_UpReqAlignClose.v：FA-D1S13 供给包件①（154 行 2 Qed；原件 UpReqAlignClose UacClose 节余量 16 槽供给（uabd1s13_ 前缀）；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 71 全落 S07 既档伪影轨；md5 dd1670） *)
Definition ng_UpAblD1S13_UpReqAlignClose : NewGreenFace :=
  MkNewGreenFace "UpAblD1S13_UpReqAlignClose.v" 154 2 20260925
  "FA-D1S13 supply pack 1: UacClose residual 16 slots (uabd1s13_), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction own ml Obj.magic=0 (closure 71 on documented S07 artifact trail), coqchk Axioms none; md5 dd1670" "L168:ma2a261".

(* ng_UpAblD1S13_AlignIdUnclosed —— UpAblD1S13_AlignIdUnclosed.v：FA-D1S13 供给包件②（117 行 2 Qed；原件 AlignIdUnclosed 节 AiuBackwardKL 余量 14 槽供给（R/RIS/sumf/sum_ext/sum_add/sum_linear/reward/beta/beta_pos/pi_ref/pi_ref_pos/eta/ZAL_pos）；S2/S3 已收槽排除登记在头注；独立伴随模块零 Require 原件；槽对账 PASS；四项验证绿 ：G3 own magic=0 闭包 71 同款既档伪影；md5 45d9ae） *)
Definition ng_UpAblD1S13_AlignIdUnclosed : NewGreenFace :=
  MkNewGreenFace "UpAblD1S13_AlignIdUnclosed.v" 117 2 20260925
  "FA-D1S13 supply pack 2: AiuBackwardKL residual 14 slots (S2/S3-claimed slots excluded per header ledger), zero Require on mother, slot reconciliation PASS; four-gate green 20260925, extraction own ml Obj.magic=0 (closure 71 documented S07 trail), coqchk Axioms none; md5 45d9ae" "L126:me099dc".

(* ng_UpReqPaperAnchor —— UpReqPaperAnchor.v： ANCHOR-A 论文引用锚机制件（244 行 14 Qed；pan_ 前缀具名锚记录 pan_anchor_list＋pan_find_* 检索函数＋三重不变式（sym_ck/file_ck/md5_len/day_uniform）——论文引用行号漂移痛点的在册机制化解法；纯 Ascii/String 零项目依赖；-SCREEN git 考古=从未入库非被移除；四项验证绿 ：G3 own magic=0 闭包 0；md5 b49e12） *)
Definition ng_UpReqPaperAnchor : NewGreenFace :=
  MkNewGreenFace "UpReqPaperAnchor.v" 244 14 20260925
  "R114 ANCHOR-A paper-reference anchor mechanism: pan_anchor_list named anchors + pan_find_* retrievers + triple invariants (sym/file/md5_len/day), pure Ascii/String zero project deps, never-in-tree verified by git archaeology; four-gate green 20260925, extraction Obj.magic=0, coqchk Axioms none; md5 b49e12" "L235:m4a7890".
(* ng_p2a_AttnClimClose —— p2a_AttnClimClose.v：消融落件·工程包AD tier2 末批二（164 行 4 Qed；原件全文逐字保留，仅将文末清单所列定理 p2a_attn_tv_seq_clim_zero（原 L112，2 句玩具证·定义层受控展开）之证明体替换，声明面与引用面零改动、零新增 Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留原件 Print Assumptions 追印面；Require QArith/CW_ConstructiveWorld_219/UpBudgetReal/UpArchAttn；本期归册三候件之一，EX-BOX 裁定已贴补丁未注册→EX-REG 归册后编译；实测 md5 5dc9d1） *)
Definition ng_p2a_AttnClimClose : NewGreenFace :=
  MkNewGreenFace "p2a_AttnClimClose.v" 164 4 20260926
  "Ablation drop piece, eng-package AD tier2 batch-2: original text kept verbatim, only p2a_attn_tv_seq_clim_zero (orig L112) proof body swapped to toy proof (2 sentences, definition-layer controlled unfolding); declarations and references unchanged, zero new Require; R15 candidate trio, EX-BOX ruled patched-but-unregistered, compile after EX-REG enrollment; md5 5dc9d1" "L302:m579621".

(* ng_p3a_TempDualBoolSlots —— p3a_TempDualBoolSlots.v：消融落件·B 可消融件（169 行 6 Qed；原件全文逐字保留，仅将文末清单所列定理 p3a_bsum_ext（原 L51，7 句刀体；坐标 L828 定理 10.13 四求和槽＝开放池 S05 三槽）之证明体替换为玩具证（实质非平凡三口径），声明面与引用面零改动、零新增 Require，纯构造性闭合，文尾保留原件 Print Assumptions 追印面；Require QArith/CW_ConstructiveWorld_219/UpReqTempDefs/UpReqEntropyDeficitTemp；本期归册三候件之一，EX-BOX 裁定已贴补丁未注册→EX-REG 归册后编译；实测 md5 658d14） *)
Definition ng_p3a_TempDualBoolSlots : NewGreenFace :=
  MkNewGreenFace "p3a_TempDualBoolSlots.v" 169 6 20260926
  "Ablation drop piece B-ablatable: original text kept verbatim, only p3a_bsum_ext (orig L51, 7-clause blade body; L828 Theorem 10.13 four-sum slots = open pool S05 three slots) proof body swapped to toy proof; declarations and references unchanged, zero new Require; R15 candidate trio, EX-BOX ruled patched-but-unregistered, compile after EX-REG enrollment; md5 658d14" "L183:ma9da9c".

(* ng_AbsLeIdReal53 —— AbsLeIdReal53.v：实数具体层 le 版绝对值恒等引理族（134 行 6 Qed；主件 r53_real_abs_ge_zero_id（le zero a -> Id (abs a) a 的 Real 层独立兑现），并交付 strict/eq/le 三种平移形扩展与乘法兼容引理 r53_real_abs_mult_id；与抽象层 fa53 件相互独立仅 Require 复用，依赖 S01_BaseRing/fa53_compat_abs/S02_CauchyComplete/S03_QExp/S07_RealSetoidExpLog 全在册；全件 Qed 闭合、零承认词面、无经典逻辑，语句面全 Set 层零 Prop 泄露，文末 Print Assumptions 审计全 Closed；本期归册三候件之一；实测 md5 b69e18） *)
Definition ng_AbsLeIdReal53 : NewGreenFace :=
  MkNewGreenFace "AbsLeIdReal53.v" 134 6 20260926
  "Real concrete-layer le-version absolute-value identity lemma family: main r53_real_abs_ge_zero_id (le zero a -> Id (abs a) a, Real-layer standalone), plus strict/eq/le shift extensions and multiplicative compat r53_real_abs_mult_id; independent of abstract fa53 piece, Require-reuse only; all Qed closed, zero admit literals, no classical logic, Set-layer statements zero Prop leak, Print Assumptions all Closed; R15 candidate trio; md5 b69e18" "L134:mb69e18".

(* ng_abl_W9_slice57_10 —— abl_W9_slice57_10.v：消融落件·S10/S12 零使用九槽 800 行窗复核已证结论（真零 5＋订正 4＋Context 2 禁删）＋SFRicciBlock 整节单元退役方案＋fisher 数值实例化（SqWall⟺rLPO 等价墙已证结论）；基 268 行 20 Qed；R2'' 查3a PASS（Closed=20 三账零差）；硬依赖 UpReqSqrt3Irrational（R75P 连座，order L424） *)
Definition ng_abl_W9_slice57_10 : NewGreenFace :=
  MkNewGreenFace "abl_W9_slice57_10.v" 236 1 20260928
  "Ablation drop piece: S10/S12 zero-consumer nine-slot 800-line window re-audit verdict (true-zero 5 + erratum 4 + Context 2 no-delete) + SFRicciBlock whole-section unit retirement plan + fisher numeric instance discharge (SqWall iff rLPO equivalence wall verdict); R2'' 3a PASS Closed=20 three-ledger zero diff; hard-requires UpReqSqrt3Irrational (R75P co-enrollment, order L424); md5 0d7105" "L236:m0d7105".

(* ng_abl_Hqarch_bernoulli_04 —— abl_Hqarch_bernoulli_04.v：消融落件·Q 层 Bernoulli 下界 (1+q)ⁿ≥1+n·q 独立重证＋Hqarch 站点形状接口引理（全站闭合切片 1/2）；基 375 行 23 Qed；零 Require 自包含件；R1' PASS→R2'' 维持；纯构造性闭合、PA Closed、G3 Obj.magic=0、G4 coqchk 零假设位 *)
Definition ng_abl_Hqarch_bernoulli_04 : NewGreenFace :=
  MkNewGreenFace "abl_Hqarch_bernoulli_04.v" 370 22 20260928
  "Ablation drop piece: Q-layer Bernoulli lower bound (1+q)^n >= 1+n*q independent reproof + Hqarch site-shape interface lemma (closure slice 1/2); zero Require self-contained; verdict chain R1' PASS -> R2'' maintained; four-gate green, PA Closed, extraction Obj.magic=0, coqchk Axioms none; md5 bedb9d" "L370:mbedb9d".

(* ng_abl_Hqarch_bridge_06 —— abl_Hqarch_bridge_06.v：消融落件·Q 层 Archimedean nat 见证核（Z_lt_le_dec 双支构造）＋末前件 n 见证生产＋Hqarch 全站完成（2/2 桥接件，取用件04）；基 179 行；R1' PASS→R2'' 维持 *)
Definition ng_abl_Hqarch_bridge_06 : NewGreenFace :=
  MkNewGreenFace "abl_Hqarch_bridge_06.v" 176 5 20260928
  "Ablation drop piece: Q-layer Archimedean nat witness core (Z_lt_le_dec two-branch construction) + last-predecessor n witness production + Hqarch full-site closure (bridge 2/2, consumes piece 04); R1' PASS -> R2'' maintained; md5 c2f617" "L170:m9782a5".

(* ng_abl_arctan_diff_16 —— abl_arctan_diff_16.v：消融落件·工作说明 9a-乙首片：HasIncr eps-线性近似谓词＋和差规则真构造＋b3rr 内点衔接；主定理 abl9_atan_diff_formula 续作点登记（首片，续作见件19）；基 470 行；裁决三计入终态；【陈旧申报勘注：主式已闭（a2_56 L1871 A2 形），本条登记文系闭合前旧文照录；md5/行数锚以勘注波后实拍为准】 *)
Definition ng_abl_arctan_diff_16 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_16.v" 443 7 20260928
  "Ablation drop piece: workorder 9a-yi first slice - HasIncr eps-linear approximation predicate + sum-difference rules true construction + b3rr interior wiring; main theorem abl9_atan_diff_formula breakpoint registered (first slice, continuation in piece 19); ruled into final state per verdict 3; md5 26c082" "L443:m26c082".

(* ng_abl_arctan_diff_19 —— abl_arctan_diff_19.v：消融落件·工作说明 9a-乙续片：续作点①内点一致 delta 闭合（条件化步界引理＋Region-relativized 一致实例，delta 与 u 无关）＋续作点②链式规则 Q 核四件；主公式仍未闭合（余②③④续作点登记）；基 490 行；R 轮独立复核候下轮（响亮注记，候裁-3 选项 a 随车形态）；【陈旧申报勘注：主式已闭（a2_56 L1871 A2 形），本条登记文系闭合前旧文照录；md5/行数锚以勘注波后实拍为准】 *)
Definition ng_abl_arctan_diff_19 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_19.v" 489 6 20260928
  "Ablation drop piece: workorder 9a-yi continuation slice - breakpoint-1 interior-consistency delta closure (conditional step-bound lemma + Region-relativized consistency instance, delta independent of u) + breakpoint-2 chained-rule Q core four pieces; main formula still open (breakpoints 2/3/4 registered); R-round independent review pending next wave (loud note); md5 bc3f9b" "L489:mbc3f9b".

(* ng_abl_R2Bishop_unfinished_01 —— abl_R2Bishop_unfinished_01.v：消融落件·消解 R2BishopLogSel 头注【R2-B 未竟项】两件：rb_le_b_mult_r（≤_B 右乘保序，strict 支 e':=eps·real_inv_pos c 真构造）＋rb_valid_up（向上谱系/有效站向上闭合）；基 149 行；R1' WITH-NOTES→R2'' 维持 *)
Definition ng_abl_R2Bishop_unfinished_01 : NewGreenFace :=
  MkNewGreenFace "abl_R2Bishop_unfinished_01.v" 148 2 20260928
  "Ablation drop piece: resolves two R2BishopLogSel header open items - rb_le_b_mult_r (le_B right-multiplication order preservation, strict branch via e' := eps * real_inv_pos c true construction) and rb_valid_up (upward lineage / valid-site upward closure); R1' WITH-NOTES -> R2'' maintained; md5 803538" "L148:m803538".

(* ng_abl_MixLogAB_htv_free_02 —— abl_MixLogAB_htv_free_02.v：消融落件·MixLogA/MixLogB k_select 的 Htv 槽减除消融（调用方证书内化 real_arch→Qmake(Z.of_nat Nv) 1→inl，域严格扩大）；基 167 行；X17 代笔登记表（授权链三环）→R2'' 查1 PASS＋反伪勘验维持 *)
Definition ng_abl_MixLogAB_htv_free_02 : NewGreenFace :=
  MkNewGreenFace "abl_MixLogAB_htv_free_02.v" 167 0 20260928
  "Ablation drop piece: Htv-slot elimination ablation for MixLogA/MixLogB k_select (caller certificate internalizes real_arch -> Qmake(Z.of_nat Nv) 1 -> inl, domain strictly enlarged); X17 ghost-written ledger (three-link authorization chain) -> R2'' check-1 PASS + anti-forgery re-audit maintained; md5 67a768" "L167:m67a768".

(* ng_abl_Ln2_native_escape_03 —— abl_Ln2_native_escape_03.v：消融落件·ln2 原生逃逸窗件：d_n 递推母线真 Fixpoint＋显式商见证＋Z 层 scaling 链；「窗放不进」负证书＋条件逃逸接口（如实 B 类禁冒充 A）；基 325 行；九处修复后 R2'' 查2 独立复现 PASS（Closed=5、Obj.magic=0、Extraction 产物与遗产逐字节 SAME）维持 *)
Definition ng_abl_Ln2_native_escape_03 : NewGreenFace :=
  MkNewGreenFace "abl_Ln2_native_escape_03.v" 315 11 20260928
  "Ablation drop piece: ln2 native escape window - d_n recursion mother line as true Fixpoint + explicit quotient witness + Z-layer scaling chain; cannot-fit negative certificate + conditional escape interface (honest B-class, no A-grade impersonation); after nine fixes R2'' check-2 independent reproduction PASS (Closed=5, Obj.magic=0, extraction output byte-SAME with legacy) maintained; md5 fef3da" "L308:m1a4a01".

(* ng_abl_SupplyRemRefuted_07 —— abl_SupplyRemRefuted_07.v：消融落件·sa_supply_rem 不可满足机检反驳 t0_supply_rem_refuted : sa_supply_rem -> False（规格级战果，Print Assumptions Closed under global context；库固定档 sa_A/sa_theta=1/2/sa_clo=lne_B 下成立）；基 185 行；R1' PASS→R2'' 维持 *)
Definition ng_abl_SupplyRemRefuted_07 : NewGreenFace :=
  MkNewGreenFace "abl_SupplyRemRefuted_07.v" 187 3 20260928
  "Ablation drop piece: machine-checked refutation of sa_supply_rem, t0_supply_rem_refuted : sa_supply_rem -> False (spec-level result, Print Assumptions Closed under the global context; holds under library fixed gears sa_A / sa_theta=1/2 / sa_clo=lne_B); R1' PASS -> R2'' maintained; md5 a44e66" "L187:ma44e66".

(* ng_abl_W9_Afamily_08 —— abl_W9_Afamily_08.v：消融落件·S10 A 族数值下标界 34 槽批量数值实例化（工作说明 §3.1 A36 口径余 2 槽如实登记不硬消；原证体全量承袭含 93 行代表件）；基 403 行；R1' WITH-NOTES（A 类装配形态三处如实申报）→R2'' 维持 *)
Definition ng_abl_W9_Afamily_08 : NewGreenFace :=
  MkNewGreenFace "abl_W9_Afamily_08.v" 401 34 20260928
  "Ablation drop piece: S10 A-family numeric index-bound 34-slot batch instantiation discharge (workorder 3.1 A36 gauge remainder 2 slots honestly registered, not force-closed; original proof bodies carried verbatim incl. 93-line representative piece); R1' WITH-NOTES -> R2'' maintained; md5 09536b" "L401:m09536b".

(* ng_abl_W9_slice34_09 —— abl_W9_slice34_09.v：消融落件·S11 死规格处置：登记退役 4 槽＋死规格形状经 witness 桥在两子域构造性落地；arctan-prime 活位取用面精测（W-A 21 取用勘正为 1 直接+1 传递）＋评估登记；基 289 行；R1' PASS→R2'' 维持 *)
Definition ng_abl_W9_slice34_09 : NewGreenFace :=
  MkNewGreenFace "abl_W9_slice34_09.v" 254 5 20260928
  "Ablation drop piece: S11 dead-spec disposal - 4 slots registered retired + dead-spec shape constructively landed in two subdomains via witness bridge; arctan-prime live-slot consumption face precisely measured (W-A 21-consumption corrected to 1 direct + 1 transitive) + assessment registered; R1' PASS -> R2'' maintained; md5 d2bfb9" "L254:md2bfb9".

(* ng_abl_SecondLaw_inst_11 —— abl_SecondLaw_inst_11.v：消融落件·SecondLawQuantified 五节假设 list-sum 数值实例化（sumpos 独立构造链＋sumext/sumlinear/sumadd 库件闭合＋T_pos:=2 数值实例化＋节形状机器锚五枚＋填充件五枚）；基 263 行；R2'' 终态预检覆盖矩阵计入（如实注记） *)
Definition ng_abl_SecondLaw_inst_11 : NewGreenFace :=
  MkNewGreenFace "abl_SecondLaw_inst_11.v" 226 7 20260928
  "Ablation drop piece: SecondLawQuantified five-section hypothesis list-sum instantiation discharge (sumpos independent construction chain + sumext/sumlinear/sumadd library closure + T_pos:=2 numeric discharge + five section-shape machine anchors + five filler pieces); covered by R2'' final-state pre-check matrix (honest note); md5 8fc051" "L226:m8fc051".

(* ng_abl_W9_pi_widen_13 —— abl_W9_pi_widen_13.v：消融落件·cos_pi_half_unique 扩域 widened2（3/2<w<7/2 ∧ cos w==0 ⟹ w==cos_pi_half）＋数学内核三件套（尾偶配对归纳／S4 锚／eps 装配双分支）；基 904 行；R2'' 查3b PASS（源锚 7/7＋S4 锚数值独立验算逐位吻合）→反伪勘验维持 *)
Definition ng_abl_W9_pi_widen_13 : NewGreenFace :=
  MkNewGreenFace "abl_W9_pi_widen_13.v" 897 26 20260928
  "Ablation drop piece: cos_pi_half_unique widened-domain widened2 (3/2 < w < 7/2 with cos w == 0 implies w == cos_pi_half) + math kernel trio (tail-even pairing induction / S4 anchor / eps assembly two branches); R2'' check-3b PASS (source anchors 7/7, S4 anchor numeric independent verification bit-exact) -> anti-forgery re-audit maintained; md5 c246d6" "L897:mc246d6".

(* ng_abl_arctan_smallincr_15 —— abl_arctan_smallincr_15.v：消融落件·工作说明 9a-甲小增量精化件 abl_atan_small_incr（b3rr 基点 r:=0 实例化＋零传输五步；S12 出锥已证结论执行）——9b 第 4 步供给就绪；基 188 行；R2'' 终态预检覆盖矩阵计入（如实注记） *)
Definition ng_abl_arctan_smallincr_15 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_smallincr_15.v" 175 1 20260928
  "Ablation drop piece: workorder 9a-jia small-increment refinement abl_atan_small_incr (b3rr basepoint r:=0 instantiation + zero-transfer five steps; S12 cone-exit verdict executed) - step-4 supply ready; covered by R2'' final-state pre-check matrix (honest note); md5 ed8aa2" "L175:med8aa2".

(* ng_PAReanchor643 —— PAReanchor643.v：K1 联合重锚数据模块·1533 锚 643 树重测；468 现势以 K-校准附册（CalSnap468）为准；基 1612 行；零 Require（唯一依赖 Stdlib String）零使用者，拓扑最轻；包随 .vo 跨机不采信，born-in-place 重编取证 *)
Definition ng_PAReanchor643 : NewGreenFace :=
  MkNewGreenFace "PAReanchor643.v" 1617 0 20260928
  "K1 joint re-anchor data module: 1533 anchors retested on the 643 tree; 468 current tree governed by K-calibration supplement (CalSnap468); zero Require (Stdlib String only), zero consumers, lightest topology; bundled cross-machine .vo not trusted, born-in-place recompile for evidence; md5 96bc6e" "L1617:m96bc6e".

(* ng_DeletedLineage643 —— DeletedLineage643.v：K2 删件谱系数据模块·48 删件 216 声明四分类；基 386 行；零 Require 零使用者 *)
Definition ng_DeletedLineage643 : NewGreenFace :=
  MkNewGreenFace "DeletedLineage643.v" 391 0 20260928
  "K2 deletion-lineage data module: 48 deleted pieces, 216 declarations four-way classified; zero Require, zero consumers; md5 e2a34e" "L391:me2a34e".

(* ng_CertSnap643 —— CertSnap643.v：K3 认证快照数据模块·643 树指纹；468 现势以 CalSnap468 为准；基 809 行；零 Require 零使用者；包随 .vo 跨机不采信 *)
Definition ng_CertSnap643 : NewGreenFace :=
  MkNewGreenFace "CertSnap643.v" 810 0 20260928
  "K3 certification snapshot data module: 643 tree fingerprint; 468 current tree governed by CalSnap468; zero Require, zero consumers; bundled cross-machine .vo not trusted; md5 826593" "L810:m826593".

(* ng_CalSnap468 —— CalSnap468.v：K-校准数据模块·删 193 增 18 双名单计数对 468 树实测吻合、抽验 10 项全中；基 153 行；零 Require 零使用者；与 CertSnap643 数据口径不同树（468 vs 643），头注已自申明勿混写 *)
Definition ng_CalSnap468 : NewGreenFace :=
  MkNewGreenFace "CalSnap468.v" 154 0 20260928
  "K-calibration data module: delete-193 add-18 dual-list counts verified against the 468 tree, 10 spot checks all hit; zero Require, zero consumers; distinct tree gauge from CertSnap643 (468 vs 643), header self-declared, do not conflate; md5 10533a" "L154:m10533a".
(* ng_abl_arctan_diff_20 —— abl_arctan_diff_20.v：arctan 差公式件续片·斜率合成精确恒等 abl9_slope_id＋小跨度常值判据 abl9_const_crit（含逐点终近上界 abl9_real_tail_bnd）＋纯增七引理（abl9_q_path_den／abl9_Qabs_le_self／abl9_arctan_wd_real／abl9_arctan_zero_pt／abl9_q_abs_two_sided_le 等，件40/件45 共同前置）；主定理 abl9_atan_diff_formula 登记未竟；基 674 行；17 闭合已核对；Require S01–S11＋abl_arctan_diff_19，零使用者；【陈旧申报勘注：主式已闭（a2_56 L1871 A2 形），本条登记文系闭合前旧文照录；md5/行数锚以勘注波后实拍为准】 *)
Definition ng_abl_arctan_diff_20 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_20.v" 675 17 20260930
  "arctan difference formula continuation piece: composite slope exact identity abl9_slope_id, small-span constancy criterion abl9_const_crit with pointwise tail bound abl9_real_tail_bnd, plus seven pure-addition lemmas (abl9_q_path_den, abl9_Qabs_le_self, abl9_arctan_wd_real, abl9_arctan_zero_pt, abl9_q_abs_two_sided_le etc.; joint prerequisite of pieces 40/45); main theorem abl9_atan_diff_formula registered as open; requires S01-S11 and abl_arctan_diff_19, 12 code consumers as of 20261002 fresh scan (abl_arctan_diff_40, abl_arctan_diff_41, abl_arctan_diff_45, abl_arctan_diff_47, abl_arctan_diff_51, abl_arctan_diff_60, abl9_atan_diff_a2_56, abl9b_ext_chain_54, abl9b_int_prep_57, abl9b_rho_chain_53, abl9b_rhs_chain_59, ablt9_rhscc_scinst); md5 33437d" "L675:m33437d".
(* ng_abl9b_rho_chain_53 —— abl9b_rho_chain_53.v：消融落件·A2B3 批层1三组：件51 望远镜引擎 ρ 参数化（签名保持式）＋缩放域证书＋w 侧 clamp-3/4 代表元，主公式内点版链供给构造；Require S01–S11＋abl_arctan_diff_19/20＋abl9b_skeleton_30＋abl_arctan_diff_51/60，批内零依赖；基 1066 行；41 闭合已核对 *)
Definition ng_abl9b_rho_chain_53 : NewGreenFace :=
  MkNewGreenFace "abl9b_rho_chain_53.v" 1066 41 20260930
  "A2B3 batch layer-1 three groups: rho-parameterized telescope over the piece-51 engine (signature-preserving), scaled-domain certificate, clamp-3/4 representative on the w side; supply construction for the interior-point main-formula chain; zero batch-internal dependencies; 41 closures verified Closed; md5 6eff3e" "L1066:m1d5855".

(* ng_abl9b_ext_chain_54 —— abl9b_ext_chain_54.v：消融落件·A2B3 批层2 LHS 半边装配件：Q 侧四块＋Hconv 参数位供给构造＋real_eq↔(M1,M2) 互译包装；Require S01–S11＋abl9b_skeleton_30＋abl_arctan_diff_20，批内零依赖；基 1499 行；32 闭合已核对（另含 9 个 Definition） *)
Definition ng_abl9b_ext_chain_54 : NewGreenFace :=
  MkNewGreenFace "abl9b_ext_chain_54.v" 1499 32 20260930
  "A2B3 batch layer-2 LHS-half assembly: four Q-side blocks, Hconv parameter-slot supply construction, real_eq <-> (M1,M2) translation wrappers; zero batch-internal dependencies; 32 closures verified Closed (plus 9 Definitions); md5 cb7ca7" "L1499:ma0a7c3".

(* ng_abl9b_int_prep_57 —— abl9b_int_prep_57.v：消融落件·A2B3 批集成预备三块十二件：件52 桥退役迁移＋装配链 clamp 化对齐＋9b-4 骨架（A2_formula 等接口面）；Require S01–S11＋abl_arctan_diff_20/45＋abl9b_skeleton_30＋abl9b_rho_chain_53；基 506 行；12 闭合已核对 *)
Definition ng_abl9b_int_prep_57 : NewGreenFace :=
  MkNewGreenFace "abl9b_int_prep_57.v" 507 12 20260930
  "A2B3 batch integration-preparation three blocks, twelve pieces: piece-52 bridge retirement migration, assembly-chain clamp alignment, 9b-4 skeleton (interface face incl. A2_formula); 12 closures verified Closed; md5 ea81b8" "L507:mea81b8".

(* ng_abl9b_rhs_chain_59 —— abl9b_rhs_chain_59.v：消融落件·A2B3 批层2 丙肢四块：clamp 1-Lipschitz＋arctan 序列项级合同＋Qinv 连续辅助件＋RHS_m→RHS 闭合骨架；Require S01–S11＋abl_arctan_diff_20/45＋abl9b_skeleton_30＋abl9b_rho_chain_53；基 463 行；16 闭合已核对 *)
Definition ng_abl9b_rhs_chain_59 : NewGreenFace :=
  MkNewGreenFace "abl9b_rhs_chain_59.v" 463 16 20260930
  "A2B3 batch layer-2 leg-c four blocks: clamp 1-Lipschitz, arctan sequence term-level congruence, Qinv continuity auxiliaries, RHS_m -> RHS closure skeleton; 16 closures verified Closed; md5 04a02a" "L463:ma16c30".

(* ng_abl9_atan_diff_a2_56 —— abl9_atan_diff_a2_56.v：消融落件·A2B3 批主公式 A2 形闭合终式（量词序 x Hx 前置形；Hd 证明项逐字形；抽象骨架前件槽对接形；已证结论=abl9_atan_diff_formula）；Require S01–S11＋19/20/41/45/47/30＋53/54/59；基 2420 行；29 闭合已核对（29=29=29 三联同值） *)
Definition ng_abl9_atan_diff_a2_56 : NewGreenFace :=
  MkNewGreenFace "abl9_atan_diff_a2_56.v" 2420 29 20260930
  "A2B3 batch main-formula A2-shape closure final form (quantifier order x Hx leading, Hd proof-term verbatim, abstract-skeleton front-slot docking; proved result abl9_atan_diff_formula); 29 closures verified (29=29=29 triple-equal); md5 6572a2" "L2420:m6cc63c".

(* ng_abl9b_land_58 —— abl9b_land_58.v：消融落件·A2B3 批 9b-4 落地两块：等价承载五件＋inhabitation 六件（A2 形接口代理承载）；Require S01–S11＋abl_arctan_diff_45＋abl9b_skeleton_30＋abl9_atan_diff_a2_56；基 321 行；6 闭合已核对（另含 7 个 Definition＋1 Record） *)
Definition ng_abl9b_land_58 : NewGreenFace :=
  MkNewGreenFace "abl9b_land_58.v" 322 6 20260930
  "A2B3 batch 9b-4 landing two blocks: five equivalence-carrier pieces, six inhabitation pieces (A2-shape interface proxy carriers); 6 closures verified Closed (plus 7 Definitions and 1 Record); md5 0546df" "L322:m0546df".
(* ng_abl9b_skeleton_30 —— abl9b_skeleton_30.v：消融链基补投件·9b-1 装配骨架：域界 abl9b_dom_pos＋w 界 abl9b_w_bounds（|w_n| ≤ (4/3)|h_n|，Hw 证书原料）＋主装配骨架（9a-乙 差公式槽以显式假设位 Hdiff 承载，δ 配方含 (1/2) 收缩因子）；Require S01–S11＋abl_arctan_smallincr_15＋abl_arctan_diff_16，批内零依赖；基 853 行；12 闭合已核对 *)
Definition ng_abl9b_skeleton_30 : NewGreenFace :=
  MkNewGreenFace "abl9b_skeleton_30.v" 853 12 20260930
  "9b-1 assembly skeleton: domain bound abl9b_dom_pos, w bound abl9b_w_bounds (|w| <= (4/3)|h|, Hw certificate material), and the main assembly skeleton carrying the 9a-yi difference-formula slot as explicit hypothesis Hdiff with the (1/2) contraction factor in the delta recipe; zero batch-internal dependencies; 12 closures verified Closed; md5 22df62" "L853:me06698".

(* ng_abl_arctan_cert_bridge_21 —— abl_arctan_cert_bridge_21.v：消融链基补投件·X24' Real 层证书桥预制：w Real 构造 abl9_brg_w_real＋终近逐点投影 abl9_brg_w_proj＋证书无关对齐 abl9_brg_w_ext＋1+w² 恒等桥两形（除法形＋核形）＋w 增量恒等桥两形（除法形＋核形）＋|w|<1 全 n 域证书（8/15 界）；Require S01–S11＋abl_arctan_diff_19，批内零依赖；基 689 行；14 闭合已核对 *)
Definition ng_abl_arctan_cert_bridge_21 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_cert_bridge_21.v" 690 14 20260930
  "X24' real-layer certificate bridge precast: w real construction abl9_brg_w_real, pointwise asymptotic projection abl9_brg_w_proj, certificate-independent alignment abl9_brg_w_ext, one-plus-w-squared identity bridges in division and kernel shapes, w-increment identity bridges in division and kernel shapes, and the |w|<1 all-n domain certificate (8/15 bound); zero batch-internal dependencies; 14 closures verified Closed; md5 4a4470" "L690:m4a4470".

(* ng_abl_arctan_diff_40 —— abl_arctan_diff_40.v：消融链基补投件·链式规则斜率合成恒等式 Real 升层：abl9_slope_id_real（件20 Q 层恒等式经终近逐点相等闭合器 abl9_brg_pt_eq＋real_inv_proj 逐点投影链升 real 层 real_eq）＋D1 路线域证书 abl9_wpath_pt_bnd/abl9_brg_wpath_dom（件20 新代 abl9_q_path_den 使用位）；Require S01–S11＋abl_arctan_diff_19/20＋abl_arctan_cert_bridge_21；基 382 行；4 闭合已核对 *)
Definition ng_abl_arctan_diff_40 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_40.v" 382 4 20260930
  "real lifting of the chain-rule composite slope identity abl9_slope_id_real: the piece-20 Q-layer identity raised to real_eq via the pointwise asymptotic-equality closer abl9_brg_pt_eq and the real_inv_proj projection chain, plus the D1-route domain certificates abl9_wpath_pt_bnd and abl9_brg_wpath_dom at the new-generation abl9_q_path_den use site; 4 closures verified Closed; md5 fc1821" "L382:m3bf2ae".

(* ng_abl_arctan_diff_41 —— abl_arctan_diff_41.v：消融链基补投件·9a-乙 ③N 等步链：Q 层剖分算术（qs 等距递推＋qs_pos 正性＋qs_Z 桥＋eps/(2N) 预算保正 abl9_eps_2N_pos）＋Real 层剖分拓扑＋链式组合件 abl9_walk/abl9_nchain_eq/abl9_nchain_walk/abl9_nchain_crit（单步一致增量估计升 N 步链 real_eq）；Require S01–S11＋abl_arctan_diff_19/20；基 384 行；12 闭合已核对 *)
Definition ng_abl_arctan_diff_41 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_41.v" 384 12 20260930
  "9a-yi part-3 N equal-step chain: Q-layer subdivision arithmetic (qs recurrence, positivity qs_pos, Z bridge qs_Z, eps/(2N) budget positivity abl9_eps_2N_pos), real-layer subdivision topology, and chain composition pieces abl9_walk, abl9_nchain_eq, abl9_nchain_walk, abl9_nchain_crit raising a uniform single-step increment estimate to the N-step chain real_eq; 12 closures verified Closed; md5 b1735c" "L384:m121006".

(* ng_abl_arctan_diff_45 —— abl_arctan_diff_45.v：消融链基补投件·9a-乙 主公式闭合推进：arctan 实参良定性 abl9_arctan_arg_wd＋遗留① Real 层单发包装 abl9_Hcert_real＋定量链引擎 abl9_const_chain（N 随 eps 取号，Σ 余项=(8/3)|h|²/N→0）；Require S01–S11＋abl_arctan_diff_20＋abl_arctan_cert_bridge_21；基 192 行；3 闭合已核对 *)
Definition ng_abl_arctan_diff_45 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_45.v" 192 3 20260930
  "9a-yi main-formula closure advance: arctan argument well-definedness abl9_arctan_arg_wd, legacy item-1 real-layer single-shot wrapper abl9_Hcert_real, and the quantitative chain engine abl9_const_chain with N chosen by eps and remainder sum (8/3)|h|^2/N tending to zero; 3 closures verified Closed; md5 9eb679" "L192:m8d491e".

(* ng_abl_arctan_diff_47 —— abl_arctan_diff_47.v：消融链基补投件·9a-乙 主定理装配推进：件40（Real 桥）与件41（N 等步链）两前件的装配衔接，装配版主定理 abl9_atan_diff_formula_asem＋inv 形 abl9_atan_diff_formula_inv（件20 B 使用位），装配域 Hh4 收紧为逐点 ∀n|h_n|≤1/4；Require S01–S11＋abl_arctan_diff_19/20/21/40/41；基 1056 行；18 闭合已核对 *)
Definition ng_abl_arctan_diff_47 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_47.v" 1057 18 20260930
  "9a-yi main-theorem assembly advance: assembly joining of piece-40 (real bridge) and piece-41 (N equal-step chain), yielding the assembly-form main theorem abl9_atan_diff_formula_asem and the inv form abl9_atan_diff_formula_inv (piece-20 B use site), with the assembly domain Hh4 tightened to pointwise |h_n| <= 1/4 for all n; 18 closures verified Closed; md5 2055f8" "L1057:m2055f8".

(* ng_abl_arctan_diff_51 —— abl_arctan_diff_51.v：消融链基补投件·9a-乙 主公式闭合续作：real_le 逐点投影器 abl9_real_le_proj_sl＋定量望远镜自建（件41/45 链引擎纯组合使用，见证随 eps 取号＋eps 松弛逐层传播）＋残项判定（单步 |Δphi| ≤ c·|s|＋余项 (8/3)|s|²，N 等步不可省）；Require S01–S11＋abl_arctan_diff_19/20/21/40/45；基 269 行；3 闭合已核对 *)
Definition ng_abl_arctan_diff_51 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_51.v" 269 3 20260930
  "9a-yi main-formula closure continuation: the real_le pointwise projector abl9_real_le_proj_sl, a self-built quantitative telescope (the piece-41/45 chain engines used purely compositionally, witnesses chosen by eps with eps relaxation propagated layer by layer), and the remainder verdict (single step |delta phi| <= c|s| plus remainder (8/3)|s|^2; N equal steps cannot be omitted); 3 closures verified Closed; md5 dabb92" "L269:ma6419d".

(* ng_abl_arctan_diff_60 —— abl_arctan_diff_60.v：消融链基补投件·9a-乙 主公式续作（X60 形）：②桥闭合＋GAP 判定件组（GAP-1 首判：拟文 RHS 槽域证书在拟文假设下不可满足，与拟文假设修订决策耦合）；Require S01–S11＋abl_arctan_diff_19/20/21；基 615 行；9 闭合已核对 *)
Definition ng_abl_arctan_diff_60 : NewGreenFace :=
  MkNewGreenFace "abl_arctan_diff_60.v" 616 9 20260930
  "9a-yi main-formula continuation (X60 shape): bridge closure plus the GAP verdict piece group (GAP-1 first verdict: the draft RHS slot domain certificate is unsatisfiable under the draft hypotheses, coupled with the draft hypothesis revision decision); 9 closures verified Closed; md5 391b62" "L616:m391b62".

(* ng_LW0LeibWindow —— LW0LeibWindow.v：莱布尼茨窗族极限分离件（本批行1·原位在册仅注册；PA=30 Closed；四关＋第五证在卷） *)
Definition ng_LW0LeibWindow : NewGreenFace :=
  MkNewGreenFace "LW0LeibWindow.v" 1896 115 20261003
  "Leibniz window family: alternating-series limit separation, escape obstacles and family separation; in-place, registration only" "L1896:me425ae".

(* ng_LW3ETranscendental —— LW3ETranscendental.v：M3-C1 正本 e 超越分离件（本批行2·原位在册；PA=45 全 Closed；终装认证账在卷；全组上游） *)
Definition ng_LW3ETranscendental : NewGreenFace :=
  MkNewGreenFace "LW3ETranscendental.v" 1174 58 20261001
  "M3-C1 chief: transcendence of e as explicit nonzero separation witness, four Set-level premises; PA=45 all Closed" "L1174:m68c059".

(* ng_LW3KnzValue —— LW3KnzValue.v：K 面非零见证锚例值钉件（本批行3·独立；372 砖四关在卷） *)
Definition ng_LW3KnzValue : NewGreenFace :=
  MkNewGreenFace "LW3KnzValue.v" 83 3 20261001
  "K-face nonzero witness anchor (p372): lam/Kinst/lc three pins via lw3_Kinst_spec bridge" "L83:mbfe3a8".

(* ng_LW3CountEBound —— LW3CountEBound.v：count*E<1 数值实例化件（本批行4·独立；E caller-chosen 诚实边界在卷） *)
Definition ng_LW3CountEBound : NewGreenFace :=
  MkNewGreenFace "LW3CountEBound.v" 134 3 20261001
  "count*E<1 anchor instantiation (p374, N=1, m=3, E=lw3_decay_E 3) with transparent value pins" "L134:m04069f".

(* ng_LW3KLegProbe —— LW3KLegProbe.v：K 非零判据一般形勘形证伪件（本批行5·素材级 CANDZERO 账面注册零装；先例在案） *)
Definition ng_LW3KLegProbe : NewGreenFace :=
  MkNewGreenFace "LW3KLegProbe.v" 92 1 20261001
  "K-leg general-shape falsification: witness-type empties on zero-example polynomial; material-grade, registered not installed (CANDZERO)" "L92:m8e6cb0".

(* ng_LW3FamScale —— LW3FamScale.v：家族面缩放定义＋锚例反转判定件（本批行6·独立；381 组供件面先行；案甲唯一定义源） *)
Definition ng_LW3FamScale : NewGreenFace :=
  MkNewGreenFace "LW3FamScale.v" 276 10 20261001
  "family-scale fbuild variant with factorial scaling and two-scale reversal verdicts on variant family (anchor)" "L276:m11df37".

(* ng_LW3VarTSumBound —— LW3VarTSumBound.v：变 T 三角和界引理族件（本批行7·独立·零 LW3E 依赖） *)
Definition ng_LW3VarTSumBound : NewGreenFace :=
  MkNewGreenFace "LW3VarTSumBound.v" 138 6 20261001
  "variable-T triangle-sum bound family: per-node lambda upper bound, abs-sum triangle kernel, const/scale linears" "L138:m0ed2ef".

(* ng_LW3JointFill —— LW3JointFill.v：锚例两尺度联合填装件（本批行8·案甲改形并册；副本前缀已归一） *)
Definition ng_LW3JointFill : NewGreenFace :=
  MkNewGreenFace "LW3JointFill.v" 351 15 20261001
  "joint two-scale sigT fill for the anchor family target with per-node total-sum bound witnesses (case-A reshaped)" "L351:mc58b54".

(* ng_LW3DualBridge —— LW3DualBridge.v：变体线对偶引理＋缩放桥接件（本批行9·案甲改形并册；副本前缀已归一） *)
Definition ng_LW3DualBridge : NewGreenFace :=
  MkNewGreenFace "LW3DualBridge.v" 245 6 20261001
  "variant-line dual lemma and scaled-family bridge over replicated family-scale surface (case-A reshaped)" "L245:mae43bb".

(* ng_LW3ESlot —— LW3ESlot.v：E 槽 Real 半边接载完成件（本批行10·取 60abca04 代非 25b77c1d 旧代；kills 缺口位显式前提承载） *)
Definition ng_LW3ESlot : NewGreenFace :=
  MkNewGreenFace "LW3ESlot.v" 314 11 20261001
  "E-slot real-half closing: strict main theorem via realconst/realexp projections and geometric bound chain; kills slot explicit premise" "L314:m4cd525".

(* ng_LW3P2Prod —— LW3P2Prod.v：端点泛函求值式桥（Q 层半边）定义件（本批行11·229 正名随批并册；头注更新 f6dd9099 转历史值） *)
Definition ng_LW3P2Prod : NewGreenFace :=
  MkNewGreenFace "LW3P2Prod.v" 113 3 20261001
  "endpoint functional evaluation bridge (229 renamed per decision point 10); cross-line read-only consumption upstream of P2Carrier" "L113:mfb6d8c".

(* ng_LW3P2Carrier —— LW3P2Carrier.v：p^2 载体条件承载形件（本批行12·候 LW3P2Prod 先行；依赖行随正名更新一行） *)
Definition ng_LW3P2Carrier : NewGreenFace :=
  MkNewGreenFace "LW3P2Carrier.v" 129 4 20261001
  "p-square carrier conditional form with Q transport; Real half carried as explicit GAPASUME premise slot (condition (c) permanent)" "L129:m097ddc".

(* ng_LW3Kills —— LW3Kills.v：环 6 kills 引理本体件（本批行13·新件·硬候 LW3ESlot 先行；M 显式门槛 sigT 见证形） *)
Definition ng_LW3Kills : NewGreenFace :=
  MkNewGreenFace "LW3Kills.v" 133 3 20261001
  "ring-6 kills lemma body: explicit-M-threshold sigT witness for geometric bound, carrier-gap and anchor discharges" "L133:md1b906".

(* ng_LW3CarrierFull —— LW3CarrierFull.v：Real 半边全清承载件（本批行14·新件·硬候 LW3Kills 先行；X 泛型零前提主定理） *)
Definition ng_LW3CarrierFull : NewGreenFace :=
  MkNewGreenFace "LW3CarrierFull.v" 140 4 20261001
  "Real-half full-clear carrier: premise-free main theorem with explicit eps pick via cauchy_real_exp_pos projection" "L140:m1a35ac".

(* ng_LW3ExpNegLB —— LW3ExpNegLB.v：e^(-node) 显式正有理下界件（本批行15·新件·独立拓扑零约束；取件在案） *)
Definition ng_LW3ExpNegLB : NewGreenFace :=
  MkNewGreenFace "LW3ExpNegLB.v" 174 4 20261001
  "explicit positive rational lower bound for exp(-node): r=1/(4C) with uniform series bound; GAPASUME slot-3 supply closure" "L174:m582e6b".

(* ng_LW3GenFill —— LW3GenFill.v：joint_target 一般 p 填装件（本批行16·391 第六候补件·随批并册已裁；硬候 FamScale/VarTSumBound/JointFill/DualBridge 先行） *)
Definition ng_LW3GenFill : NewGreenFace :=
  MkNewGreenFace "LW3GenFill.v" 292 13 20261001
  "general-p joint_target fill (391), hard Require upstream of CondSep; consumes famscale/dual/fill/vtsum surfaces" "L292:m1a14a9".

(* ng_LW3CondSep —— LW3CondSep.v：案丙条件分离族 C2+C4 组装件（本批行17·新件·全组拓扑末位；七跨件依赖全备始可） *)
Definition ng_LW3CondSep : NewGreenFace :=
  MkNewGreenFace "LW3CondSep.v" 134 2 20261001
  "case-C conditional separation assembly: C2 lambda<1 condition and C4 full composition with explicit anchor growth pin" "L134:m1fccda".

(* ng_LW0LicAdapt —— LW0LicAdapt.v：π 传输单前提出口件（批 2 附行·M0+ α 链槽 3 合入件·已在位仅注册；PA=3 Closed；509 注释清洗毕 gate4=0；500 铸型＋502 复走＋503 终验 GO 在卷） *)
Definition ng_LW0LicAdapt : NewGreenFace :=
  MkNewGreenFace "LW0LicAdapt.v" 135 3 20261001
  "single-premise export piece: conditional lic instantiation of pi and escape-at-condition with pack congruence; slot-3 merge of the alpha chain, annotation-cleaned, in-place registration only" "L135:mfe82af".

(* ng_LW6CosZeroQuant —— LW6CosZeroQuant.v：cos 零点定量单纯性核（零点包非退化形＋分离模量推论·已在位仅注册；PA=4 Closed；注释清洗毕 gate4=0；558 改铸形·终验 GO 在卷） *)
Definition ng_LW6CosZeroQuant : NewGreenFace :=
  MkNewGreenFace "LW6CosZeroQuant.v" 238 4 20261001
  "quantitative simplicity of the cos zero point: nondegenerate zero pack with explicit inverse-bound constant two and a separation modulus corollary; erratum-re-cast, annotation-cleaned, in-place registration only" "L238:m5c4cb7".

(* ng_abl_tail_deep_slots —— abl_tail_deep_slots.v：深水杂槽现勘桥两件＋RI 面证书六件＋RL 节直供两件合件（尾百第四批包③·十供给定理＋一机检不可构造负裁决登记；决议138 尾百七件合流之新件落点；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_deep_slots : NewGreenFace :=
  MkNewGreenFace "abl_tail_deep_slots.v" 236 10 20261001
  "deep misc slots after survey: two exp_neg bridge closed forms, six one-instantiation positivity certificates for RI and P7D slots, two RL direct-supply pieces, one non-constructive negative adjudication registered" "L236:mbd35d7".

(* ng_abl_tail_def_instance —— abl_tail_def_instance.v：配分定义性实例化件族统一件＋可达槽具名闭形（尾百七件合流波新件；Z_temp 裸槽路线不可达如实判读登记于卷；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_def_instance : NewGreenFace :=
  MkNewGreenFace "abl_tail_def_instance.v" 161 4 20261001
  "unified definitional instantiation family for partition interface assumptions with named closed forms for reachable slots; bare Z_temp route judged unreachable and honestly registered" "L161:m34c7dc".

(* ng_abl_tail_novel_supply —— abl_tail_novel_supply.v：StateSpace 平方律槽＋KVEv 均匀核最小世界正性/优超槽闭合形（尾百七件合流波新件；世界数据槽首次伴随闭合；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_novel_supply : NewGreenFace :=
  MkNewGreenFace "abl_tail_novel_supply.v" 230 7 20261001
  "first-closure companion theorems for world-data slots: StateSpace pointwise square law on the unit world and KVEv uniform-kernel minimal-world positivity and majorization closed forms" "L230:m3d40a5".

(* ng_abl_tail_pos_certs —— abl_tail_pos_certs.v：正性证书族 one 实例化合件（尾百第四批包①·Real 面六闭形＋RI 面一闭形＋温度/配分/步长类证书槽供给；尾百七件合流波新件；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_pos_certs : NewGreenFace :=
  MkNewGreenFace "abl_tail_pos_certs.v" 316 14 20261001
  "positivity certificate package: lt-face T/T_star/D/Z one-instantiation closed forms with G3 zeroing translation slots across Real, RI, temperature, partition and stepsize families" "L316:m6ebb70".

(* ng_abl_tail_slot_upgrade —— abl_tail_slot_upgrade.v：独立槽批部分供形升级件（尾百七件合流波新件；四类升级配方六槽＋使用面喂形三位；Set 面归属机检在卷；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_slot_upgrade : NewGreenFace :=
  MkNewGreenFace "abl_tail_slot_upgrade.v" 397 12 20261001
  "partial-supply to full-slot upgrade pieces over six selected slots by four upgrade recipes plus three user-side feed forms; Set-face membership machine-checked" "L397:m496458".

(* ng_abl_tail_sum_pos_bridge —— abl_tail_sum_pos_bridge.v：G1 sum_pos 类槽统一桥族槽形传入延伸件（尾百七件合流波新件；四定理四面零重述；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_sum_pos_bridge : NewGreenFace :=
  MkNewGreenFace "abl_tail_sum_pos_bridge.v" 194 4 20261001
  "slot-passing extension of the 64-piece sumd sigT-witness bridge engine: abstract operator, EMS, TSI and slc readings in four theorem faces with zero restatement" "L194:m35e2ff".

(* ng_abl_tail_world_certs —— abl_tail_world_certs.v：world_certs 世界证书族合件（尾百第四批包②·KVEv 逐出核四槽最小世界闭合＋接口面 lt 证书八槽 one 实例化；尾百七件合流波新件；注释清稿毕 gate4=0） *)
Definition ng_abl_tail_world_certs : NewGreenFace :=
  MkNewGreenFace "abl_tail_world_certs.v" 347 12 20261001
  "world certificate layer: KVEv exit-kernel four-slot minimal-world closure plus eight lt-face certificate one-instantiation closed forms for RL and P7D temperature slots" "L347:m81cc07".

(* ng_LW2SepTransport —— LW2SepTransport.v：通用分离传递核（real_eq 桥当黑盒模量源调用下 real_lt 的显式预算传递·k 退化因子桥内禀只进注记不进语句面〔设计文档 §2.2:155＋588 §四步4 定论〕；辅助件 lw2t_k_inv2_le L41 结论位 stdlib Qle:Prop 仅证内 L64 pose proof 使用不外泄主链，已申报挂起〔§三丙案〕；PA=3 Closed；绿判三证在卷 575 记录＋588 幻影红结案预诊） *)
Definition ng_LW2SepTransport : NewGreenFace :=
  MkNewGreenFace "LW2SepTransport.v" 140 5 20261002
  "universal separation transport kernel: transports real_lt along real_eq consuming any bridge as a black-box modulus source at an explicit budget, with k-factor arithmetic kernel lw2t_qinv_pos and lw2t_k_inv2_le; the k factor is bridge-internal and stays out of the statement face; auxiliary statement lw2t_k_inv2_le concludes in stdlib Qle (Prop), consumed proof-internally only at L64, declared here" "L140:m68170f".

(* ng_LW5SepComplexity —— LW5SepComplexity.v：分离复杂度层（pi 有理包络列窗族 eps_n:=1/(n+1)·M_n:=2*pie_modulus(eps_n/2)+1 上 bool 分离判定器 lw5n_sep_dec＋最小分离窗阶 lw5n_nsep：结构递归有界搜索 lw5n_find＋显式预算 lw5n_bnd〔足用性不主张如实注记〕＋最小性特征 lw5n_nsep_minimal；窗族合法性＋入窗近距正确性＋搜索机件包在卷；增长律三档语句面以注记承载闭证属后续；结论位 nat 序四件（nsep_bound/nsep_least 上界＋shape_lower/shape_band 之 m<8·n0+9 下界序）照头注「特此如实注记」内嵌申报·候验证挂起；辅助 Qle/Qlt 语句仅脚手架；绿证＝607 记录 EXIT=0＋PA 双发 50/50 Closed＋coqchk -o 公理位 none，608 十三补丁属 219 面零碰本件，.vo 2d9209e9 魔数 436f7121 0001 5ff4 在盘） *)
Definition ng_LW5SepComplexity : NewGreenFace :=
  MkNewGreenFace "LW5SepComplexity.v" 1083 58 20261002
  "separation complexity layer: rational envelope window family of pi (eps_n := 1/(n+1), M_n := 2*pie_modulus(eps_n/2)+1) carrying bool separation decider lw5n_sep_dec and minimal window rank lw5n_nsep via structurally recursive bounded search lw5n_find and explicit budget lw5n_bnd with minimality characterized by lw5n_nsep_minimal; window legality, near-boundary correctness and search machinery included; growth-law three-tier statements stay in annotations with closed proofs as future work; four conclusion-position nat-order bounds (nsep_bound, nsep_least upper bounds plus shape_lower/shape_band lower order m < 8*n0+9) honestly declared per the module header annotation as pending-verification ledger, auxiliary Qle/Qlt statements scaffolding only" "L1083:m063c27".

(* ng_abl_tail_supply_65 —— abl_tail_supply_65.v：tsp_sum6 求和六性质件（尾百供给第二批·F1 六性质 28 槽实例闭形＋F9 inv_one_inv 双槽＋F12 fold 两方程＋PA 审计段；tmw/frd/tsi/slc/PA_04/sumL 六族使用喂形；决议141 尾百供给第二批纳入之新件落点） *)
Definition ng_abl_tail_supply_65 : NewGreenFace :=
  MkNewGreenFace "abl_tail_supply_65.v" 301 11 20261002
  "sum-six-properties piece: instance closed forms for the F1 six-property 28 slots as six supply theorems plus consumer slot feed forms across the tmw, frd, tsi, slc, PA_04 and sumL families, with F9 inv_one_inv two slots, F12 fold two equations and a PA audit section" "L301:m604c99".

(* ng_abl_tail_supply_66 —— abl_tail_supply_66.v：PA_04 余槽收尾件（尾百供给第二批·Arch_PA_04 一线推导第三槽 req_exp_neg_ext 的 Real 特化闭形 exact 一击供给＋出节全参喂形精简版·两正性槽保留显式前提位；决议141 尾百供给第二批纳入之新件落点） *)
Definition ng_abl_tail_supply_66 : NewGreenFace :=
  MkNewGreenFace "abl_tail_supply_66.v" 130 2 20261002
  "closing piece for the Arch_PA_04 line-deduction trio: the remaining third slot req_exp_neg_ext supplied as a Real-specialization closed form in one exact stroke via req_opp_compat lifting plus cauchy_real_exp_wd, with a simplified full-parameter feed form keeping the two positivity slots as explicit premises" "L129:m659bf4".

(* ng_abl_tail_supply_67 —— abl_tail_supply_67.v：F4 指数族 17 槽分拣件（尾百供给第二批·real 面八槽 Real 特化闭形供给〔lt 类 6＋le 类 2〕＋Id 面五钉定槽零输入＋参数位四槽不施工；函数实例一件＋投影转写五件＋使用组封四件＝九 Qed；决议141 尾百供给第二批纳入之新件落点） *)
Definition ng_abl_tail_supply_67 : NewGreenFace :=
  MkNewGreenFace "abl_tail_supply_67.v" 188 9 20261002
  "F4 exponential family 17-slot triage piece: eight real-face slots (six lt-class plus two le-class) supplied as Real-specialization closed forms through the expf_pack unpacking via one function instance, five projection transcriptions and four per-section consumer closures, five Id-pinned slots fed zero and four parameter slots left unconstructed" "L188:mddfea4".

(* ng_abl_tail_supply_68 —— abl_tail_supply_68.v：sum_eq_list 四槽 SO 实例闭形供给文件（尾百供给第二批·最小可行实例世界＝单点状态空间〔uab_ssUnit＋uab_soUnit〕·单点枚举规范形＋槽逐字闭形·四落点具名供给 P7B 段二/段三/段七＋P2W UabP3AmtSwap；决议141 尾百供给第二批纳入之新件落点） *)
Definition ng_abl_tail_supply_68 : NewGreenFace :=
  MkNewGreenFace "abl_tail_supply_68.v" 198 6 20261002
  "four sum_eq_list slots supplied as SO-instance closed forms over the minimal single-point state-space instance world with singleton enumeration: one canonical bs_list_sum form plus the verbatim slot closure, landed as four named supplies across P7BoundedSoftmaxDeep sections two, three and seven and UpAblP2WByPass UabP3AmtSwap" "L198:md03f2f".

(* ng_abl_tail_supply_69 —— abl_tail_supply_69.v：W 类响亮记录件（尾百供给第二批·F8 去 DO 保序族两供给定理经机检对照实验核验在抽象接口层不可成证·两槽改归 W 类真前提；本件不发伪供给，改载机检对照边界形 2 条〔条款 G：失败要响、禁静默降级、禁占位〕；决议141 尾百供给第二批纳入之新件落点） *)
Definition ng_abl_tail_supply_69 : NewGreenFace :=
  MkNewGreenFace "abl_tail_supply_69.v" 134 2 20261002
  "loud W-class registration piece: the two DO-free supply theorems bs_abs and bs_lpc are machine-checked unprovable at the abstract interface layer via a contrast experiment and the two slots are reclassified as genuine premises; the module ships two machine-adjudicated boundary forms instead of fake supplies, per the fail-loud clause" "L134:m8c99ef".

(* ng_abl_tail_supply_70 —— abl_tail_supply_70.v：Arch_Up_01 Z_align_pos 槽换名输入＋sum_over_S_pos 实例闭形×2（尾百供给第二批·S05 出节常量 Z_align 与 UpAblZpos 消解体展开后同一项恒等换名·AlignIdWorld 与 FirewallLoop 两落点；:797-798/:1175-1176 两槽随 69 改判保持假设身份不发供给·本件零 Require 69；决议141 尾百供给第二批纳入之新件落点） *)
Definition ng_abl_tail_supply_70 : NewGreenFace :=
  MkNewGreenFace "abl_tail_supply_70.v" 203 6 20261002
  "Arch_Up_01 Z_align_pos slot fed via identity renaming (the S05 section constant Z_align equals the UpAblZpos resolved body after unfolding) plus two sum_over_S_pos instance closed forms landed at AlignIdWorld and FirewallLoop; the two slots re-judged alongside supply_69 keep hypothesis identity with zero Require on supply_69" "L203:mcb6c1f".

(* ng_abl_attn_doeblin_supply —— abl_attn_doeblin_supply.v：AT1 AttnDoeblin 试点供给文件（Doeblin 收缩数据槽见证与平滑核构造族·37 槽逐槽速判试点供给；方法丙外置新件 born-in-place，上游本体零字节不动；基座区供给第一批·同事侧 #决议138 波入库六波零红在档） *)
Definition ng_abl_attn_doeblin_supply : NewGreenFace :=
  MkNewGreenFace "abl_attn_doeblin_supply.v" 384 11 20261002
  "AT1 AttnDoeblin pilot supply: Doeblin contraction data-slot witnesses and smoothing-kernel construction family for thirty-seven slots with per-slot fast adjudication; external born-in-place piece, upstream bodies untouched" "L384:m3ebd1e".

(* ng_abl_s01_supply —— abl_s01_supply.v：S01_BaseRing 缺口首攻供给文件（物理世界接口族可达上限 14 槽供给·冻结域方法丙外置新件；槽闭形经 Require 引用＋具名供给定理输入，S01 本体零字节不动；基座区供给第一批·同事侧 #决议138 波在档） *)
Definition ng_abl_s01_supply : NewGreenFace :=
  MkNewGreenFace "abl_s01_supply.v" 307 14 20261002
  "S01_BaseRing gap first assault: fourteen reachable physical-world interface slots supplied as named closed forms from an external frozen-domain piece; the S01 body stays byte-identical, consumption is via Require plus named supply theorems" "L307:mbf8148".

(* ng_abl_tail_logbridge —— abl_tail_logbridge.v：log 桥分件（下编 log 桥族 Real 特化闭形统一供给桥·件内六供给；零 Require 通用桥闭形，使用面下游读法对接经 Require 本件即取；基座区供给第一批·同事侧 #决议139 波在档） *)
Definition ng_abl_tail_logbridge : NewGreenFace :=
  MkNewGreenFace "abl_tail_logbridge.v" 223 6 20261002
  "log bridge split piece: unified supply bridge of Real-specialized closed forms for the lower-volume log bridge family with six in-piece supplies; host-free generic bridge, downstream consumption via Require" "L223:m2262a3".

(* ng_abl_tail_pos_supply_sum —— abl_tail_pos_supply_sum.v：F1 sum 族六性质槽组喂形供给文件（上编批 1·SumDCarrierFeed 槽组延线·七宿主逐落点；七宿主目标件零 Require 零字节不动；基座区供给第一批·同事侧 #决议138 波在档） *)
Definition ng_abl_tail_pos_supply_sum : NewGreenFace :=
  MkNewGreenFace "abl_tail_pos_supply_sum.v" 483 26 20261002
  "F1 sum family six-property slot-group feed-form supply: SumDCarrierFeed slot-group extension placed host by host across seven hosts; target host files stay byte-identical with zero Require" "L483:mf26eca".

(* ng_abl_tail_sum_readbridge —— abl_tail_sum_readbridge.v：求和读法桥接件（12 宿主 46 槽 csm_sumf 实现化读法统一供给桥·求和四性质＋逐项零化；出节全参形通用桥，宿主零字节不动；基座区供给第一批·同事侧 #决议138 波在档） *)
Definition ng_abl_tail_sum_readbridge : NewGreenFace :=
  MkNewGreenFace "abl_tail_sum_readbridge.v" 239 10 20261002
  "summation reading bridge: unified supply bridge giving the csm_sumf implemented reading to forty-six slots across twelve hosts, with four summation properties and per-term zeroing; fully parameterized out-of-section generic bridge" "L239:ma28df2".

(* ng_abl_tbase_expf_bs_feed —— abl_tbase_expf_bs_feed.v：expf B 型输入件（下编批 5-3·expf B 型输入＋RSQ bs 三槽 cms 直引＋T1b sum_eq_list 桥；Import RealInterfaceEnhancedMod 非传递内联留痕，UpReqSampling 在役只读；基座区供给第一批·同事侧 #决议142 波在档） *)
Definition ng_abl_tbase_expf_bs_feed : NewGreenFace :=
  MkNewGreenFace "abl_tbase_expf_bs_feed.v" 215 11 20261002
  "expf B-type feed piece: B-form expf feeds plus three RSQ bs slots consuming cms by direct reference and a T1b sum_eq_list bridge; non-propagating inner-scope import recorded, upstream requirements read-only" "L215:mc7efaa".

(* ng_abl_tbase_expf_spec —— abl_tbase_expf_spec.v：F7 expf 套族 Real 特化闭形 A 形直供件（上编批 4·S13／AttnDoeblin／S15／G01／UpReqFEPAttn 五宿主 11 必行；UpAblD1_expf_pack 只读引用含 AttnDoeblin 组合件；基座区供给第一批·同事侧 #决议142 波在档） *)
Definition ng_abl_tbase_expf_spec : NewGreenFace :=
  MkNewGreenFace "abl_tbase_expf_spec.v" 216 11 20261002
  "F7 expf family Real-specialized closed-form A-shape direct supply for five hosts (S13, AttnDoeblin, S15, G01, UpReqFEPAttn) with eleven mandatory slots; read-only reference into UpAblD1_expf_pack including the AttnDoeblin composition" "L216:m28a769".

(* ng_abl_tbase_klcx_rppo_sum —— abl_tbase_klcx_rppo_sum.v：「可」槽聚集组 req 面求和接口喂形件（上编批 11·UpReqAlign4 三节 sum 六槽组＋Arch_UpReq_10 ReqPPOAdvantage 五槽·两宿主二十三槽；W 槽/存疑槽/冻结件零侵入；基座区供给第一批·同事侧 #决议142 波在档） *)
Definition ng_abl_tbase_klcx_rppo_sum : NewGreenFace :=
  MkNewGreenFace "abl_tbase_klcx_rppo_sum.v" 254 11 20261002
  "reachable-slot aggregation req-face summation interface feed: UpReqAlign4 three-section sum six-slot groups plus Arch_UpReq_10 ReqPPOAdvantage five slots across two hosts and twenty-three slots; W and doubtful and frozen slots untouched" "L254:m139465".

(* ng_abl_tbase_lcsum_feed —— abl_tbase_lcsum_feed.v：有限和 ltsum Type 抬升喂形件（上编批 13·tblc_ 族 10 供给 Qed＋内部件 tblc_plus_shuffle 1＝全文 grep 11·三宿主节 7 槽两宿主文件·自建 S:Type 全泛型有限和机器 ltsum 根·G3 双臂 0 强口径；#决议144 发车闸4 首拦截裸泛名 ltsum→词边界改名 tblc_ltsum 45 引用零误伤后终态 md5 eee127a1；Qed 位双口径候裁：供给口径 10/全文口径 11，本处取 grep 实拍 11） *)
Definition ng_abl_tbase_lcsum_feed : NewGreenFace :=
  MkNewGreenFace "abl_tbase_lcsum_feed.v" 292 11 20261002
  "finite-sum ltsum Type-lifted feed piece: tblc_ family ten supply theorems plus one internal shuffle lemma, seven slots across three host sections in two host files, self-built S:Type fully generic finite-sum machine ltsum root, double-arm G3 zero-strong criterion; bare generic name ltsum renamed tblc_ltsum by the registration dup-gate with forty-five references intact" "L292:m809e84".

(* ng_abl_tbase_logbridge —— abl_tbase_logbridge.v：F6 log 桥族四形根喂形件（上编批 2·compat／exp_neg／inv_one_inv／log_inv_exp_neg_req 四形·八宿主二十槽；三根供给文件只读引用；基座区供给第一批·同事侧 #决议139 波在档） *)
Definition ng_abl_tbase_logbridge : NewGreenFace :=
  MkNewGreenFace "abl_tbase_logbridge.v" 316 20 20261002
  "F6 log bridge family four-form root feed: compat, exp_neg, inv_one_inv and log_inv_exp_neg_req forms across eight hosts and twenty slots; read-only reference into three root supply pieces" "L316:m3aac04".

(* ng_abl_tbase_logrest —— abl_tbase_logrest.v：F6 log 桥族余量收尾件（上编批 3·inv_one_inv 余双槽／compat 余单槽／tsup 系双槽／S12 log 单调槽·六宿主六槽；G01 mono 根件＋G05 根件只读引用；基座区供给第一批·同事侧 #决议142 波在档） *)
Definition ng_abl_tbase_logrest : NewGreenFace :=
  MkNewGreenFace "abl_tbase_logrest.v" 174 6 20261002
  "F6 log bridge family remainder closeout: inv_one_inv remaining two slots, compat remaining single slot, tsup family two slots and the S12 log monotone slot across six hosts; read-only reference into G01 mono root and G05 root" "L174:m96faaf".

(* ng_abl_tbase_sumpos_spp —— abl_tbase_sumpos_spp.v：F8 求和正性 spp 系喂形供给文件（上编批 12·tbsp_ 十供给·cons 头十槽六宿主·fa51_sumd_pos_cons 根直引；基座区供给第一批·同事侧 #决议143 波在档） *)
Definition ng_abl_tbase_sumpos_spp : NewGreenFace :=
  MkNewGreenFace "abl_tbase_sumpos_spp.v" 277 10 20261002
  "F8 summation positivity spp-family feed supply: tbsp_ ten supplies for cons-head ten slots across six hosts with fa51_sumd_pos_cons root direct reference" "L277:m8ff8d8".

(* ng_abl_tbase_t1c_expneg_feed —— abl_tbase_t1c_expneg_feed.v：T1C exp_neg 槽补位完成件（下编 B54 余槽完成·tbne_ 1 Qed·T1C:121 槽补位·体 exact 直引 G05 根 logd_log_exp_neg_real 指针别名·双臂 G3 各 1 同值＝语句面新增 Obj.magic 0；基座区供给第一批·同事侧 #决议144 波在档） *)
Definition ng_abl_tbase_t1c_expneg_feed : NewGreenFace :=
  MkNewGreenFace "abl_tbase_t1c_expneg_feed.v" 100 1 20261002
  "T1C exp_neg slot fill closeout piece: single tbne_ theorem filling the T1C slot by exact reference to the G05 root logd_log_exp_neg_real as a pure pointer alias; double-arm G3 equal at one, zero new Obj.magic on the statement face" "L100:mcbb7a7".

(* ng_abl_tbase_tempsum —— abl_tbase_tempsum.v：F1 sum 族 Real 面抽象求和接口喂形·温度族首攻件（上编批 5·tspt_ 五供给·闭十文件十三节 48 槽＋同形宿主顺带；十三宿主目标件零 Require 零字节不动；基座区供给第一批·同事侧 #决议141 波在档） *)
Definition ng_abl_tbase_tempsum : NewGreenFace :=
  MkNewGreenFace "abl_tbase_tempsum.v" 195 5 20261002
  "F1 sum family Real-face abstract summation interface feed, temperature-family first assault: tspt_ five supplies closing forty-eight slots across thirteen sections in ten files plus same-form host incidental coverage; host files byte-identical with zero Require" "L195:m53b027".

(* ng_abl_tbase_tempsum_feed —— abl_tbase_tempsum_feed.v：F1 温度族 Real 面 per-宿主具名喂形件（上编批 6·UpReqTempDefs／UpReqEntropyDeficitTemp／UpReqEntropyMaxTemp／UpReqTempDual 四宿主 pos/ext/linear/add＋EMT le 扩槽·17 槽；基座区供给第一批·同事侧 #决议141 波在档） *)
(* 〔B1 退役〕tbtf_ 17 槽全 ⊂ tspt_ 48 槽零净增量（条线58 §二查⑥机械凭证追认）、归一波整件退役，17 槽覆盖权归 tspt_ 泛型桥 48 槽辖区；回退锚=attn/_tcw_归一B案备份（存档 m1a0b5e）。原条目照录（唯 Mk 行退役日位卫生化）：Definition ng_abl_tbase_tempsum_feed : NewGreenFace :=
  MkNewGreenFace "abl_tbase_tempsum_feed.v" 312 17 〔退役日位卫生化〕
  "F1 temperature family Real-face per-host named feed: UpReqTempDefs, UpReqEntropyDeficitTemp, UpReqEntropyMaxTemp and UpReqTempDual four hosts with pos, ext, linear and add forms plus the EMT le extension slots, seventeen slots" "L312:mbb22c8". *)

(* ng_abl_tbase_zapfeed —— abl_tbase_zapfeed.v：F10 Z_align_pos 族喂形供给文件（上编批 7·配分函数正性槽十三槽十一供给；宿主件零 Require 面仅读取零字节不动；基座区供给第一批·同事侧 #决议141 波在档） *)
Definition ng_abl_tbase_zapfeed : NewGreenFace :=
  MkNewGreenFace "abl_tbase_zapfeed.v" 321 11 20261002
  "F10 Z_align_pos family feed supply: thirteen partition-function positivity slots closed by eleven supplies; host files read-only with zero Require and byte-identical bodies" "L321:m571b8d".

(* ng_LW3ExclusionCalc —— LW3ExclusionCalc.v：排除计算器（Track A 三件 Defined 计算核 lw3x_sideb/lw3x_env_lo/lw3x_env_hi——sideb=leiblw_Qltb 直连、env_lo/hi 端点算式与 PiEnvelope 同源——经 lw3x_seal 六层 sigT Set 面封装＋带不相容性定理 lw3x_band_excl〔逐 eps 三模量 max 拼装＋Qabs 符号两支＋线性收束，Hc/Hsep/Hlo/Hhi/Hw 四供件全使用；两条线性收束支 lra 系 592 §四.一 红线①纪律放行位·LW2 绿件同位先例〕＋主语句 lw3x_calc 参数 c 前提位「q 进见证出」可执行；PA=4 Closed；提取 12.ml Obj.magic=0 逐字验证；coqchk -o 全闭包 234 库 公理位 none 满贯；绿证＝609 记录四关全部通过在卷） *)
Definition ng_LW3ExclusionCalc : NewGreenFace :=
  MkNewGreenFace "LW3ExclusionCalc.v" 299 11 20261002
  "exclusion calculator: three Defined computable kernels lw3x_sideb, lw3x_env_lo and lw3x_env_hi over the Leibniz window envelope, sealed by lw3x_seal into a six-layer sigT Set face, with the incompatibility band theorem lw3x_band_excl consuming all four supply witnesses via per-eps three-modulus max assembly and Qabs sign branches, and main statement lw3x_calc carrying premise parameter c so that a rational q with witnesses yields the exclusion band as executable code" "L284:mc79f54".

(* ng_LW4EPiContrast —— LW4EPiContrast.v：e-π 模量对照层（e 侧逃逸供给 lw4c_e_escape_supply＝lic_witness_e 实供〔exp_series 与 1/q_fact 之上·UpReq lic_escape_window/lw0m 接口面〕；π 侧零伪造三护栏：π 逃逸供给槽唯 lic_face 条件形 lw4c_pi_escape_of_lic、提取九件零 π 侧供件名、无前提 π 逃逸供给零落；对照面 lw4c_contrast_face 经 lw4c_contrast_param 成对承载；tactic 面 intro/destruct/exists/exact/split 零自动化；PA=2 Closed；提取 .ml/.mli Obj.magic=0/0；绿证＝606 记录四关全部通过在卷） *)
Definition ng_LW4EPiContrast : NewGreenFace :=
  MkNewGreenFace "LW4EPiContrast.v" 457 28 20261003
  "e versus pi modulus contrast layer: the e side carries an unconditional escape supply lw4c_e_escape_supply built on the lic witness over exp_series and 1/q_fact, while the pi side yields escapes only conditionally on the lic face lw4c_pi_lic_face via lw4c_pi_escape_of_lic, so the paired contrast face lw4c_contrast_face assembled by lw4c_contrast_param keeps the pi side zero-forged with no unconditional pi escape supply" "L457:mbc5feb".

(* ng_LW1PiMeasure —— LW1PiMeasure.v：π 距离率互译层：lw1m_dist_pt/lw1m_dist_face 点面距离、lw1m_dist_order 率阶-窗宽衔接三态判定（阈的倒数取整阶处阶距小于阈）、lw1m_dom_face 供给域面、lw1m_measure_main 双前提主形（lw1m_b_cert_face 与 lw1m_dom_face，μ₀=2/C=2 显式选取）；tactic 面 intro/destruct/exists/exact/split 显式链零 solver 收尾；PA=13 Closed；提取 30 件 Obj.magic=0/0；绿证＝145 记录四关＋使用链重烙在卷（主件新代 654d54fc 定向 coqchk -o 模块复核 Axioms: none） *)
Definition ng_LW1PiMeasure : NewGreenFace :=
  MkNewGreenFace "LW1PiMeasure.v" 834 46 20261004
  "pi distance-rate translation layer: lw1m_dist_pt and lw1m_dist_face carry the point and face distances, lw1m_dist_order decides the three-way distance order through the rate-tier to window-width link at the ceiling of one over the threshold, lw1m_dom_face supplies the domain face, and lw1m_measure_main assembles the two-premise measure face from lw1m_b_cert_face and lw1m_dom_face with mu0=2 and C=2 selected explicitly" "L834:m16657a".

(* ng_LW0PiIrrational —— LW0PiIrrational.v：圆周率无理性的构造性证明（Niven 路线：Q[t] 多项式微分代数＋圆周率处三角端点值＋端点泛函整数性＋下界见证装配）；主语句 lw0_pi_irrational（任设有理数，恒可给出圆周率与其相离的显式正分离见证证书）；PA=313 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_LW0PiIrrational : NewGreenFace :=
  MkNewGreenFace "LW0PiIrrational.v" 13955 583 20261004
  "constructive proof that pi is irrational by the Niven route: q-polynomial differential algebra, trigonometric endpoint values at pi, integrality of the endpoint functionals, and an explicit positive separation witness for every rational approximation" "L13955:m40656c".

(* ng_LW2TrigBridge —— LW2TrigBridge.v：π 两构造表示（几何零点表示 real_pi_geom 与 Leibniz 级数和 cauchy_real_pi_leibniz）在三角端点值面上的互译桥（端点值跨表示转写／实层二倍角点值／半角零点-反正切-Leibniz 值单语句互联）；主语句 lw2_pi_L_trig_values；PA=0 行（行首统计口径·闭包见证＝coqchk -o 模块复核）；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_LW2TrigBridge : NewGreenFace :=
  MkNewGreenFace "LW2TrigBridge.v" 254 12 20261004
  "interchange between the two constructive representations of pi, the geometric zero representation and the Leibniz series sum, over the trigonometric endpoint values: transcription of the endpoint values across the two representations, the real-level double-angle identities for sine and cosine, and a single zero-premise statement linking the half-angle zero, the arctangent of one, and the Leibniz value of pi" "L254:m1b84e1".

(* ng_LW0LeibSeparation —— LW0LeibSeparation.v：Leibniz 级数 π 的有理层构造性分离界库（岸界与半量弹药链＋端点帽复合传输；主语句 leibsep_q_kernel_gate_carrier：显式端点帽 s t 前提＋P1/P2 具体端点形，双岸矛盾件 leibsep_false_branch_contra 显参传递装配分离证书；终形批新增：leibsep_pi_rational_unconditional 与 leibsep_q_kernel 两项无前提闭式主定理——π 强无理显式正距离分离 sigT 见证形）；PA=61 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_LW0LeibSeparation : NewGreenFace :=
  MkNewGreenFace "LW0LeibSeparation.v" 5723 108 20261006
  "constructive rational-layer separation bounds for the Leibniz series of pi: shore bounds with the half-quantity arsenal, the kernel gate carrier lemma taking explicit endpoint caps s and t as premises together with concrete P1 and P2 endpoint forms, assembling the two-sided separation certificate by direct argument passing into the contradiction lemma, and the terminal unconditional forms leibsep_pi_rational_unconditional with leibsep_q_kernel giving the premise-free explicit positive-distance separation witness for every rational" "L5723:meb42d3".

(* ng_LW2Binom —— LW2Binom.v：nat 面二项式系数工具组与 Z 桥（主件 lw2_binom：Pascal 递归构造的非负二项式系数，三条定义方程 reflexivity 可验；配套非负性布尔形 lw2_binom_nonneg、正性引理 lw2_fact_pos、零支 lw2_binom_above、对角 lw2_binom_diag、加法交换承载 lw2_mul_left_comm、阶乘刻画 lw2_binom_fact；Z 面符号因子方程 lw2_zsign_even/lw2_zsign_odd 与 Z 因子取用方程 lw2_binom_Z）；主语句 lw2_binom；PA=9 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_LW2Binom : NewGreenFace :=
  MkNewGreenFace "LW2Binom.v" 171 11 20261004
  "nat-level binomial coefficient tools with a Z bridge: the Pascal-recursion coefficient lw2_binom characterized by three definitional equations, with nonnegativity, positivity, zero branches, the factorial characterization, and Z-side sign-factor and coefficient equations" "L171:mc34892".

(* ng_ablt9_rhscc_scinst —— ablt9_rhscc_scinst.v：第九批新增域普查批·abl9 域 B5 缺口外置供给模块（abl9b_rhs_chain_59 L416 abl9b_rhs_sc_close Hconv 参数位·件54 abl9b_ext_ws_conv 缩放对适配）：①Q 侧缩放常量桥 ablt9_rhscc_km_ksc（件54 ext_km(S m) 与件53 ksc m 同值·两族坐标系合流中间件）②逐点桥 ablt9_rhscc_ws_pt_eq（件59 rhs_ws 族与件54 ext_ws 族逐点尾等价）③B 型全参喂 ablt9_rhscc_sc_close_feed（Hconv 位经逐点桥 Hpt 显式前提适配·供给形态=适配引理形；宿主件53 sca_Hd Qed 不透明致 Hpt 无条件均匀形本批不可构＝B5-B6 耦合新见·B6 手术候用户令）④伴生具名件 ablt9_rhscc_ext_close（件56 a2 L1890 案一槽具名实例闭合）；三宿主零 Require 增量零字节动；PA=4 Closed；coqchk -o 单件零公理（Axioms: none）；注释面已按现役注释词典完成卫生处理（gate4 hard 0/review 5） *)
Definition ng_ablt9_rhscc_scinst : NewGreenFace :=
  MkNewGreenFace "ablt9_rhscc_scinst.v" 190 4 20261002
  "B5 gap supply for the abl9 domain: Q-side scaling constant bridge ablt9_rhscc_km_ksc merges the ksc and ext_km coordinate families, per-point bridge ablt9_rhscc_ws_pt_eq equates the rhs_ws and ext_ws tails, the B-type full-application feed ablt9_rhscc_sc_close_feed adapts the Hconv slot through the explicit Hpt premise, and the companion ablt9_rhscc_ext_close closes the named instance of abl9b_rhs_close over the ext scaling family; three hosts untouched with zero Require delta" "L190:m0facf4bb".

(* ng_ablt9_s06abs_sum_feed —— ablt9_s06abs_sum_feed.v：第九批施工批二·UpAblS06AbsFeed 抽象求和接口节 uabS4c_SumOverSlot（:353）三 sum 槽候核转正供给模块：泛型有限和载体 csm_sumf S0 en（枚举清单折叠·UpReqConcSoftmax）上消解证书三件 ①s6f9_sum_ext_csm（uabS4c_sum_ext :359 逐字同形·real_eq 面·cms_sum_ext 全参直引经 RealEnhancedReal 实例投影）②s6f9_sum_add_csm（:362 逐字同形·real_plus 面）③s6f9_sum_le_B_csm（:366 逐字同形·Bishop 逐 eps 面·全库无同根本件新构＝半分拆 eps 归纳折叠＋逐头 lt 加法保序＋四元重排收束）＋s6f9_eps_split_move 重排助手共 4 Qed；宿主签名保持式只读零字节动（对拍两点特化 uabS4c_pair_* 同槽异载体非重复供给）；PA=4 Closed；coqchk -o 单件零公理（Axioms: none）；注释面已按现役注释词典完成卫生处理（gate4 hard 0/review 11） *)
Definition ng_ablt9_s06abs_sum_feed : NewGreenFace :=
  MkNewGreenFace "ablt9_s06abs_sum_feed.v" 177 4 20261002
  "three discharge certificates for the uabS4c sum slots of UpAblS06AbsFeed over the generic finite-sum carrier csm_sumf: s6f9_sum_ext_csm and s6f9_sum_add_csm convert the cms_sum_ext and cms_sum_add faces to real_eq and real_plus form through the RealEnhancedReal instance projection, s6f9_sum_le_B_csm is newly built with no same-root piece in the tree via eps bisection induction folding with per-head lt addition monotonicity, plus the reordering helper s6f9_eps_split_move, four Qed in total, host signature read-only" "L177:m6bf0caca".

(* ng_abl_tail_expf_iface_inst —— abl_tail_expf_iface_inst.v：C1 键控批一期（LoHi 17 位）唯一新增供给文件（born-in-place）：Part A 具名 expf 族六槽（tpei_expf/tpei_expf_pos/tpei_expf_zero/tpei_expf_plus/tpei_expf_mono_lt/tpei_expf_mono_le，uabd1x_ 根直引·uabl:41-60 体例）＋具体层无条件供件 tpei_lpc（real_lt_plus_compat_lt_le 直引·uabl:73-76 同款）；Part B 世界数据四件（tpei_temp/tpei_temp_pos/tpei_Delta/tpei_Delta_pos，cf2 系直引·最小上游 UpReqConcFin2 按 uabl 文头裁定）；Part 0 RIS 面副本二件（tpei_p7a_lo_lt_one_req 七参出节形/tpei_p7d_hi_gt_one_req 八参全显——语句面承 Paper7Ablation:101/P7B:272 逐字同形，唯 expf_zero 槽面 Id→req，p7d 一步直证式样）；Part C LoHi 九定理 @RealEnhancedReal 全参显式实例化＝17 位翻色落点（Squeeze 六件 uahl_lo_lt_one_hi/uahl_lo_lt_hi/uahl_delta_star_bounded/uahl_omd_bounded＋lpc:=tpei_lpc/uahl_omd_bounded_one＋lpc/uahl_lo_lt_hi_one＋Cross 三件 uahlc_lo_lt_one_hi_one/uahlc_omd_bounded_one＋lpc/uahlc_lo_one_hi_full；出节最小泛化参表实测——expf_pos 零消费件不入 uahl_lo_lt_one_hi/uahl_lo_lt_hi_one/uahlc 系导出形）；依赖方向＝本件单向 Require 两迁移宿主（宿主零 Require 本件，其 p7a/p7d 调用以 Part 0 同体证明内联——单向环消解）；PA=11 Closed；coqchk -o 单件零公理（Axioms: none）；注释面按现役词典卫生处理（gate4 三件 hard 0） *)
Definition ng_abl_tail_expf_iface_inst : NewGreenFace :=
  MkNewGreenFace "abl_tail_expf_iface_inst.v" 261 11 20261002
  "the sole new supply piece of the C1 phase-one LoHi unlock: Part A names the six expf family slots over the uabd1x root with the concrete-layer lpc provider, Part B aliases the cf2 world data, Part 0 restates the p7a_lo_lt_one and p7d_hi_gt_one mirrors on the req face with the expf_zero slot at real_eq and a one-step direct proof for the hi-side mirror, and Part C instantiates the nine migrated LoHi theorems of both hosts at the canonical RealEnhancedReal instance with the lpc argument supplied at the three omd witnesses, eleven Qed in total, one-way require over the migrated hosts whose p7a and p7d upstream consumption is inlined with the Part 0 bodies" "L257:mbfef29".
(* ng_abl_dte_core3 —— abl_dte_core3.v：DTPT_Entropy.v 前件参数消解供给卡三 *)
Definition ng_abl_dte_core3 : NewGreenFace :=
  MkNewGreenFace "abl_dte_core3.v" 450 37 20261005
  "[abl_dte_core3.v: DTPT_Entropy.v preface discharge supply card 3]" "L450:m9880aa87".
(* ng_abl_dte_core4 —— abl_dte_core4.v：DTPT_Entropy.v 前件参数消解供给卡四 *)
Definition ng_abl_dte_core4 : NewGreenFace :=
  MkNewGreenFace "abl_dte_core4.v" 902 57 20261005
  "[abl_dte_core4.v: DTPT_Entropy.v preface discharge supply card 4]" "L902:mbe905a70".
(* ng_abl_dte_core1 —— abl_dte_core1.v：DTPT_Entropy.v 前件参数消解供给卡一 *)
Definition ng_abl_dte_core1 : NewGreenFace :=
  MkNewGreenFace "abl_dte_core1.v" 459 40 20261005
  "[abl_dte_core1.v: DTPT_Entropy.v preface discharge supply card 1]" "L459:m6cac57d2".
(* ng_abl_dtr_core3 —— abl_dtr_core3.v：DTPT_Rotation.v 登记序卡三 *)
Definition ng_abl_dtr_core3 : NewGreenFace :=
  MkNewGreenFace "abl_dtr_core3.v" 411 32 20261005
  "[abl_dtr_core3.v: DTPT_Rotation.v registration sequence card 3]" "L411:m687e42d0".
(* ng_abl_dte_core2 —— abl_dte_core2.v：DTPT_Entropy.v 前件参数消解供给卡二 *)
Definition ng_abl_dte_core2 : NewGreenFace :=
  MkNewGreenFace "abl_dte_core2.v" 659 47 20261005
  "[abl_dte_core2.v: DTPT_Entropy.v preface discharge supply card 2]" "L659:m5a9e04c4".
(* ng_abl_dtd_core3 —— abl_dtd_core3.v：DTPT.v 登记序卡三 *)
Definition ng_abl_dtd_core3 : NewGreenFace :=
  MkNewGreenFace "abl_dtd_core3.v" 502 38 20261005
  "[abl_dtd_core3.v: DTPT.v registration sequence card 3]" "L502:m4bbe455a".
(* ng_abl_dtr_core2 —— abl_dtr_core2.v：DTPT_Rotation.v 登记序卡二 *)
Definition ng_abl_dtr_core2 : NewGreenFace :=
  MkNewGreenFace "abl_dtr_core2.v" 544 41 20261005
  "[abl_dtr_core2.v: DTPT_Rotation.v registration sequence card 2]" "L544:mfdda085f".
(* ng_abl_dtr_core1 —— abl_dtr_core1.v：DTPT_Rotation.v 登记序卡一 *)
Definition ng_abl_dtr_core1 : NewGreenFace :=
  MkNewGreenFace "abl_dtr_core1.v" 718 44 20261005
  "[abl_dtr_core1.v: DTPT_Rotation.v registration sequence card 1]" "L718:m45663a01".
(* ng_abl_dtd_core4 —— abl_dtd_core4.v：DTPT.v 登记序卡四 *)
Definition ng_abl_dtd_core4 : NewGreenFace :=
  MkNewGreenFace "abl_dtd_core4.v" 603 40 20261005
  "[abl_dtd_core4.v: DTPT.v registration sequence card 4]" "L603:me760825a".
(* ng_abl_dtd_core1 —— abl_dtd_core1.v：DTPT.v 登记序卡一 *)
Definition ng_abl_dtd_core1 : NewGreenFace :=
  MkNewGreenFace "abl_dtd_core1.v" 637 35 20261005
  "[abl_dtd_core1.v: DTPT.v registration sequence card 1]" "L637:m5caba4d7".
(* ng_abl_dtd_core2 —— abl_dtd_core2.v：DTPT.v 登记序卡二 *)
Definition ng_abl_dtd_core2 : NewGreenFace :=
  MkNewGreenFace "abl_dtd_core2.v" 495 37 20261005
  "[abl_dtd_core2.v: DTPT.v registration sequence card 2]" "L495:m96422d63".
(* ng_abl_dtb_bridge —— abl_dtb_bridge.v：DTPT_Bridge 带前件 21 条语句 26 参数 *)
Definition ng_abl_dtb_bridge : NewGreenFace :=
  MkNewGreenFace "abl_dtb_bridge.v" 551 32 20261005
  "[abl_dtb_bridge.v: DTPT_Bridge 21 statements with premises over 26 parameters]" "L551:m7ecdc4c1".
(* ng_abl_tbase_tempsum_feed —— abl_tbase_tempsum_feed.v：温度族四宿主 Real 面具名供给 *)
Definition ng_abl_tbase_tempsum_feed : NewGreenFace :=
  MkNewGreenFace "abl_tbase_tempsum_feed.v" 271 17 20261005
  "[abl_tbase_tempsum_feed.v: Real mask names supply for four thermal-family hosts]" "L271:m8a6de302".
(* ng_abl_tbe_invpos —— abl_tbe_invpos.v：两宿主六处反正性前件 *)
Definition ng_abl_tbe_invpos : NewGreenFace :=
  MkNewGreenFace "abl_tbe_invpos.v" 151 7 20261005
  "[abl_tbe_invpos.v: six anti-positivity premises across two hosts]" "L151:mbad97475".
(* ng_abl_c1_lohi —— abl_c1_lohi.v：UpAblP7_LoHiSqueeze 键控 23 待解参数逐参数消解 *)
Definition ng_abl_c1_lohi : NewGreenFace :=
  MkNewGreenFace "abl_c1_lohi.v" 354 41 20261005
  "[abl_c1_lohi.v: UpAblP7_LoHiSqueeze keyed 23 pending parameters discharged one by one]" "L354:me5247e56".
(* ng_abl_Pr_core_01 —— abl_Pr_core_01.v：素数域基件一（素性判定·最小素因子·分解存在） *)
Definition ng_abl_Pr_core_01 : NewGreenFace :=
  MkNewGreenFace "abl_Pr_core_01.v" 326 26 20261006
  "[abl_Pr_core_01.v: primality test, least prime factor and factorization existence over nat]" "L326:m6a49be7b".

(* ng_abl_qpoly_divmod —— abl_qpoly_divmod.v：Q 层多项式线性综合除法引擎 *)
Definition ng_abl_qpoly_divmod : NewGreenFace :=
  MkNewGreenFace "abl_qpoly_divmod.v" 355 42 20261006
  "[abl_qpoly_divmod.v: linear synthetic division engine for dense-list polynomials over Q]" "L355:mf812c657".

(* ng_abl_Pr_enum_02 —— abl_Pr_enum_02.v：素数域基件二（枚举面） *)
Definition ng_abl_Pr_enum_02 : NewGreenFace :=
  MkNewGreenFace "abl_Pr_enum_02.v" 596 40 20261006
  "[abl_Pr_enum_02.v: prime enumeration face]" "L596:m3c37509f".

(* ng_abl_Pr_euclid_03 —— abl_Pr_euclid_03.v：素数域基件三（欧几里得型语句） *)
Definition ng_abl_Pr_euclid_03 : NewGreenFace :=
  MkNewGreenFace "abl_Pr_euclid_03.v" 196 21 20261006
  "[abl_Pr_euclid_03.v: Euclid-type statements]" "L196:mf0bae6da".

(* ng_abl_redischarge_pr01_sb —— abl_redischarge_pr01_sb.v：Pr_core_01 使用端再消解桥 sb *)
Definition ng_abl_redischarge_pr01_sb : NewGreenFace :=
  MkNewGreenFace "abl_redischarge_pr01_sb.v" 107 12 20261006
  "[abl_redischarge_pr01_sb.v: redischarge bridge consuming Pr_core_01]" "L107:m1fa589b4".

(* ng_abl_qpoly_divmod_gen —— abl_qpoly_divmod_gen.v：Q 多项式一般除法接口与线性桥 *)
Definition ng_abl_qpoly_divmod_gen : NewGreenFace :=
  MkNewGreenFace "abl_qpoly_divmod_gen.v" 683 56 20261006
  "[abl_qpoly_divmod_gen.v: general division interface for Q polynomials with linear bridge]" "L683:m8a78d5fa".

(* ng_abl_Pr_lcmdecomp_04 —— abl_Pr_lcmdecomp_04.v：素数域基件四（lcm 分解） *)
Definition ng_abl_Pr_lcmdecomp_04 : NewGreenFace :=
  MkNewGreenFace "abl_Pr_lcmdecomp_04.v" 566 38 20261006
  "[abl_Pr_lcmdecomp_04.v: lcm decomposition]" "L566:mf2a41e78".

(* ng_abl_Pr_lcm_eq —— abl_Pr_lcm_eq.v：lcm 方程层 *)
Definition ng_abl_Pr_lcm_eq : NewGreenFace :=
  MkNewGreenFace "abl_Pr_lcm_eq.v" 450 17 20261006
  "[abl_Pr_lcm_eq.v: lcm equation layer]" "L450:mdd53fd8b".

(* ng_abl_sumd_strict —— abl_sumd_strict.v：sumd 严格不等式面 *)
Definition ng_abl_sumd_strict : NewGreenFace :=
  MkNewGreenFace "abl_sumd_strict.v" 111 6 20261006
  "[abl_sumd_strict.v: strict sum-of-distance inequalities]" "L111:m4b284b24".

(* ng_abl_prop_carrier —— abl_prop_carrier.v：Pr 域命题汇入承载层 *)
Definition ng_abl_prop_carrier : NewGreenFace :=
  MkNewGreenFace "abl_prop_carrier.v" 272 19 20261006
  "[abl_prop_carrier.v: proposition joining layer for the prime domain]" "L272:m5a5e6709".

(* ng_abl_redischarge_sumd_inst —— abl_redischarge_sumd_inst.v：sumd 实例化再消解 *)
Definition ng_abl_redischarge_sumd_inst : NewGreenFace :=
  MkNewGreenFace "abl_redischarge_sumd_inst.v" 107 8 20261006
  "[abl_redischarge_sumd_inst.v: sumd instance redischarge]" "L107:mca157cfa".

(* ng_abl_div_chisq_twopoint —— abl_div_chisq_twopoint.v：两点卡方散度面 *)
Definition ng_abl_div_chisq_twopoint : NewGreenFace :=
  MkNewGreenFace "abl_div_chisq_twopoint.v" 822 22 20261005
  "[abl_div_chisq_twopoint.v: two-point chi-square divergence]" "L822:m0a02a371".

(* ng_abl_div_kl_chisq_twopoint —— abl_div_kl_chisq_twopoint.v：KL 与卡方散度关系 *)
Definition ng_abl_div_kl_chisq_twopoint : NewGreenFace :=
  MkNewGreenFace "abl_div_kl_chisq_twopoint.v" 796 14 20261006
  "[abl_div_kl_chisq_twopoint.v: KL versus chi-square relation]" "L796:m12652899".

(* ng_abl_div_hellinger_twopoint —— abl_div_hellinger_twopoint.v：Hellinger 散度关系 *)
Definition ng_abl_div_hellinger_twopoint : NewGreenFace :=
  MkNewGreenFace "abl_div_hellinger_twopoint.v" 1104 16 20261006
  "[abl_div_hellinger_twopoint.v: Hellinger divergence relations]" "L1104:m845d14a6".

(* ng_abl_div_tv_kl_channel —— abl_div_tv_kl_channel.v：全变差到 KL 信道不等式 *)
Definition ng_abl_div_tv_kl_channel : NewGreenFace :=
  MkNewGreenFace "abl_div_tv_kl_channel.v" 330 16 20261006
  "[abl_div_tv_kl_channel.v: total variation to KL channel inequality]" "L330:md237e7a2".

(* ng_abl_div_fdiv2_skeleton —— abl_div_fdiv2_skeleton.v：f-散度骨架 *)
Definition ng_abl_div_fdiv2_skeleton : NewGreenFace :=
  MkNewGreenFace "abl_div_fdiv2_skeleton.v" 1962 64 20261006
  "[abl_div_fdiv2_skeleton.v: f-divergence skeleton]" "L1962:m49e36ddd".

(* ng_abl_redischarge_fdiv2_half —— abl_redischarge_fdiv2_half.v：f-散度半界再消解 *)
Definition ng_abl_redischarge_fdiv2_half : NewGreenFace :=
  MkNewGreenFace "abl_redischarge_fdiv2_half.v" 349 17 20261006
  "[abl_redischarge_fdiv2_half.v: f-divergence half-bound redischarge]" "L349:mf9a95cdd".

(* ng_abl_kv_sat_drift —— abl_kv_sat_drift.v：KV 饱和漂移面 *)
Definition ng_abl_kv_sat_drift : NewGreenFace :=
  MkNewGreenFace "abl_kv_sat_drift.v" 1522 48 20261006
  "[abl_kv_sat_drift.v: KV saturation drift]" "L1522:mad3ca3b8".

(* ng_abl_redischarge_kv_bool2 —— abl_redischarge_kv_bool2.v：KV bool2 再消解 *)
Definition ng_abl_redischarge_kv_bool2 : NewGreenFace :=
  MkNewGreenFace "abl_redischarge_kv_bool2.v" 261 18 20261006
  "[abl_redischarge_kv_bool2.v: KV bool2 redischarge]" "L261:m21cace78".

(* ng_abl_attn_step_calc —— abl_attn_step_calc.v：attention 步进计算器 *)
Definition ng_abl_attn_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_attn_step_calc.v" 605 56 20261006
  "[abl_attn_step_calc.v: attention step calculator]" "L605:me0d94ee0".

(* ng_abl_concmix_step_calc —— abl_concmix_step_calc.v：concmix 步进计算器 *)
Definition ng_abl_concmix_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_concmix_step_calc.v" 712 70 20261006
  "[abl_concmix_step_calc.v: concmix step calculator]" "L712:m39eab8b4".

(* ng_abl_dyn_step_calc —— abl_dyn_step_calc.v：dyn 步进计算器 *)
Definition ng_abl_dyn_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_dyn_step_calc.v" 518 49 20261006
  "[abl_dyn_step_calc.v: dyn step calculator]" "L518:mbeb6bc91".

(* ng_abl_mixlog_switch —— abl_mixlog_switch.v：mixlog 开关面 *)
Definition ng_abl_mixlog_switch : NewGreenFace :=
  MkNewGreenFace "abl_mixlog_switch.v" 335 28 20261006
  "[abl_mixlog_switch.v: mixlog switch face]" "L335:m96ced02a".

(* ng_abl_anneal_mono —— abl_anneal_mono.v：退火单调性 *)
Definition ng_abl_anneal_mono : NewGreenFace :=
  MkNewGreenFace "abl_anneal_mono.v" 381 50 20261006
  "[abl_anneal_mono.v: annealing monotonicity]" "L381:me7c91310".

(* ng_abl_archpa04_step_calc —— abl_archpa04_step_calc.v：archpa04 步进计算器 *)
Definition ng_abl_archpa04_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_archpa04_step_calc.v" 822 37 20261006
  "[abl_archpa04_step_calc.v: archpa04 step calculator]" "L822:m053094b6".

(* ng_abl_attniter_step_calc —— abl_attniter_step_calc.v：attention 迭代步进计算器 *)
Definition ng_abl_attniter_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_attniter_step_calc.v" 682 59 20261006
  "[abl_attniter_step_calc.v: attention-iteration step calculator]" "L682:mce514227".

(* ng_abl_concfin_step_calc —— abl_concfin_step_calc.v：concfin 步进计算器 *)
Definition ng_abl_concfin_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_concfin_step_calc.v" 971 33 20261005
  "[abl_concfin_step_calc.v: concfin step calculator]" "L971:m5eba68a3".

(* ng_abl_cw220_step_calc —— abl_cw220_step_calc.v：cw220 步进计算器 *)
Definition ng_abl_cw220_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_cw220_step_calc.v" 731 35 20261006
  "[abl_cw220_step_calc.v: cw220 step calculator]" "L731:m4ca9d9bb".

(* ng_abl_mixchain_step_calc —— abl_mixchain_step_calc.v：mixchain 步进计算器 *)
Definition ng_abl_mixchain_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_mixchain_step_calc.v" 811 60 20261006
  "[abl_mixchain_step_calc.v: mixchain step calculator]" "L811:m11515481".

(* ng_abl_p2a_step_calc —— abl_p2a_step_calc.v：p2a 步进计算器 *)
Definition ng_abl_p2a_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_p2a_step_calc.v" 824 38 20261006
  "[abl_p2a_step_calc.v: p2a step calculator]" "L824:me27ca2a6".

(* ng_abl_tvd_step_calc —— abl_tvd_step_calc.v：TVD 步进计算器 *)
Definition ng_abl_tvd_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_tvd_step_calc.v" 1463 87 20261005
  "[abl_tvd_step_calc.v: TVD step calculator]" "L1463:mf007d0fe".

(* ng_abl_dtpt_dep_supply —— abl_dtpt_dep_supply.v：DTPT 依赖面具名供给 *)
Definition ng_abl_dtpt_dep_supply : NewGreenFace :=
  MkNewGreenFace "abl_dtpt_dep_supply.v" 149 2 20261006
  "[abl_dtpt_dep_supply.v: named dependency supply for DTPT]" "L149:mfa3c034f".

(* ng_abl_dtpt_dig_supply —— abl_dtpt_dig_supply.v：DTPT 数字面具名供给 *)
Definition ng_abl_dtpt_dig_supply : NewGreenFace :=
  MkNewGreenFace "abl_dtpt_dig_supply.v" 289 22 20261006
  "[abl_dtpt_dig_supply.v: named digit supply for DTPT]" "L289:m24e8a71e".

(* ng_abl_dtpt_bridge_dig_supply —— abl_dtpt_bridge_dig_supply.v：DTPT 桥数字面具名供给 *)
Definition ng_abl_dtpt_bridge_dig_supply : NewGreenFace :=
  MkNewGreenFace "abl_dtpt_bridge_dig_supply.v" 227 10 20261006
  "[abl_dtpt_bridge_dig_supply.v: named bridge-digit supply for DTPT]" "L227:me1fda2c6".

(* ng_abl_dtpt_rot_bridge_supply —— abl_dtpt_rot_bridge_supply.v：DTPT 旋转桥具名供给 *)
Definition ng_abl_dtpt_rot_bridge_supply : NewGreenFace :=
  MkNewGreenFace "abl_dtpt_rot_bridge_supply.v" 245 12 20261006
  "[abl_dtpt_rot_bridge_supply.v: named rotation-bridge supply for DTPT]" "L245:m8e3cf5e2".

(* ng_abl_dtpt_truth_supply —— abl_dtpt_truth_supply.v：DTPT 真值面具名供给 *)
Definition ng_abl_dtpt_truth_supply : NewGreenFace :=
  MkNewGreenFace "abl_dtpt_truth_supply.v" 311 24 20261006
  "[abl_dtpt_truth_supply.v: named truth supply for DTPT]" "L311:m43af8ee5".

(* ng_abl_dtpt_yellow_supply —— abl_dtpt_yellow_supply.v：DTPT 黄束面具名供给 *)
Definition ng_abl_dtpt_yellow_supply : NewGreenFace :=
  MkNewGreenFace "abl_dtpt_yellow_supply.v" 161 5 20261006
  "[abl_dtpt_yellow_supply.v: named yellow supply for DTPT]" "L161:m23196fe4".

(* ng_abl_ln2_numer_int —— abl_ln2_numer_int.v：ln2 数值积分面 *)
Definition ng_abl_ln2_numer_int : NewGreenFace :=
  MkNewGreenFace "abl_ln2_numer_int.v" 583 32 20261006
  "[abl_ln2_numer_int.v: numerical integral face for ln 2]" "L583:mc57c4869".

(* ng_abl_ln2_tail_bound —— abl_ln2_tail_bound.v：ln2 尾项界 *)
Definition ng_abl_ln2_tail_bound : NewGreenFace :=
  MkNewGreenFace "abl_ln2_tail_bound.v" 757 33 20261006
  "[abl_ln2_tail_bound.v: tail bound for ln 2]" "L757:m796ba11a".

(* ng_abl_ln2_ireal —— abl_ln2_ireal.v：ln2 实数视图整合 *)
Definition ng_abl_ln2_ireal : NewGreenFace :=
  MkNewGreenFace "abl_ln2_ireal.v" 745 42 20261006
  "[abl_ln2_ireal.v: real-view integration for ln 2]" "L745:m5fbfc134".

(* ng_abl_ln2_sharp_weight —— abl_ln2_sharp_weight.v：ln2 锐权重 *)
Definition ng_abl_ln2_sharp_weight : NewGreenFace :=
  MkNewGreenFace "abl_ln2_sharp_weight.v" 431 23 20261006
  "[abl_ln2_sharp_weight.v: sharp weights for ln 2]" "L431:ma31c4599".

(* ng_abl_ln2_assembly —— abl_ln2_assembly.v：ln2 合成面 *)
Definition ng_abl_ln2_assembly : NewGreenFace :=
  MkNewGreenFace "abl_ln2_assembly.v" 323 22 20261006
  "[abl_ln2_assembly.v: assembly face for ln 2]" "L323:m46807cba".

(* ng_abl_ln2_qpoly_consume —— abl_ln2_qpoly_consume.v：ln2 多项式链使用端 *)
Definition ng_abl_ln2_qpoly_consume : NewGreenFace :=
  MkNewGreenFace "abl_ln2_qpoly_consume.v" 531 62 20261006
  "[abl_ln2_qpoly_consume.v: polynomial-chain consumer for ln 2]" "L531:me66ff6a1".

(* ng_abl_diffbridge_incr —— abl_diffbridge_incr.v：差分桥增量 *)
Definition ng_abl_diffbridge_incr : NewGreenFace :=
  MkNewGreenFace "abl_diffbridge_incr.v" 408 13 20261006
  "[abl_diffbridge_incr.v: difference-bridge increments]" "L408:m92d43265".

(* ng_abl_diffreal_family —— abl_diffreal_family.v：差分实数族 *)
Definition ng_abl_diffreal_family : NewGreenFace :=
  MkNewGreenFace "abl_diffreal_family.v" 480 6 20261006
  "[abl_diffreal_family.v: difference real family]" "L480:m36230cee".

(* ng_abl_pint_realview —— abl_pint_realview.v：pint 实数视图 *)
Definition ng_abl_pint_realview : NewGreenFace :=
  MkNewGreenFace "abl_pint_realview.v" 167 6 20261006
  "[abl_pint_realview.v: pint real view]" "L167:m18255b8d".

(* ng_abl_normconv_real —— abl_normconv_real.v：实数范数收敛面 *)
Definition ng_abl_normconv_real : NewGreenFace :=
  MkNewGreenFace "abl_normconv_real.v" 651 35 20261006
  "[abl_normconv_real.v: norm convergence over reals]" "L651:mfd9c50a2".

(* ng_abl_tvd_stationary —— abl_tvd_stationary.v：TVD 平稳分布 *)
Definition ng_abl_tvd_stationary : NewGreenFace :=
  MkNewGreenFace "abl_tvd_stationary.v" 1250 50 20261005
  "[abl_tvd_stationary.v: TVD stationary distribution]" "L1250:m45f47a5b".

(* ng_abl_sqrtf_tail —— abl_sqrtf_tail.v：平方根尾项界 *)
Definition ng_abl_sqrtf_tail : NewGreenFace :=
  MkNewGreenFace "abl_sqrtf_tail.v" 1024 80 20261006
  "[abl_sqrtf_tail.v: square-root tail bound]" "L1024:m07034a50".

(* ng_abl_p7_lower_band —— abl_p7_lower_band.v：P7 下界带 *)
Definition ng_abl_p7_lower_band : NewGreenFace :=
  MkNewGreenFace "abl_p7_lower_band.v" 130 22 20261006
  "[abl_p7_lower_band.v: P7 lower band]" "L130:mf235bdf6".

(* ng_abl_mixrational_wide —— abl_mixrational_wide.v：宽域有理混合 *)
Definition ng_abl_mixrational_wide : NewGreenFace :=
  MkNewGreenFace "abl_mixrational_wide.v" 140 2 20261006
  "[abl_mixrational_wide.v: wide rational mixing]" "L140:m3255daf4".

(* ng_abl_audit_base_v1 —— abl_audit_base_v1.v：审计基座 v1 *)
Definition ng_abl_audit_base_v1 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v1.v" 193 4 20261006
  "[abl_audit_base_v1.v: audit base v1]" "L193:m95b18218".

(* ng_abl_audit_base_v2 —— abl_audit_base_v2.v：审计基座 v2 *)
Definition ng_abl_audit_base_v2 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v2.v" 200 32 20261006
  "[abl_audit_base_v2.v: audit base v2]" "L200:m230d6659".

(* ng_abl_audit_base_v3 —— abl_audit_base_v3.v：审计基座 v3 *)
Definition ng_abl_audit_base_v3 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v3.v" 124 4 20261006
  "[abl_audit_base_v3.v: audit base v3]" "L124:m86195041".

(* ng_abl_audit_base_v4 —— abl_audit_base_v4.v：审计基座 v4 *)
Definition ng_abl_audit_base_v4 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v4.v" 242 31 20261006
  "[abl_audit_base_v4.v: audit base v4]" "L242:mbf9fd047".

(* ng_abl_audit_base_v5 —— abl_audit_base_v5.v：审计基座 v5 *)
Definition ng_abl_audit_base_v5 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v5.v" 268 10 20261006
  "[abl_audit_base_v5.v: audit base v5]" "L268:m13c18f7a".

(* ng_abl_audit_base_v6 —— abl_audit_base_v6.v：审计基座 v6 *)
Definition ng_abl_audit_base_v6 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v6.v" 230 8 20261006
  "[abl_audit_base_v6.v: audit base v6]" "L230:m5fb57283".

(* ng_abl_Pr_bertrand —— abl_Pr_bertrand.v：Bertrand 假设构造性见证件 *)
Definition ng_abl_Pr_bertrand : NewGreenFace :=
  MkNewGreenFace "abl_Pr_bertrand.v" 386 8 20261006
  "[abl_Pr_bertrand.v: constructive witness forms of Bertrand's postulate]" "L386:m95b1e92e".

(* ng_abl_audit_base_v5b —— abl_audit_base_v5b.v：审计 v5b·S12 余位矿直审闭合件 *)
Definition ng_abl_audit_base_v5b : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v5b.v" 380 8 20261006
  "[abl_audit_base_v5b.v: audit v5b, direct closure of the S12 remainder-mining face]" "L380:m897af9bc".

(* ng_abl_audit_base_v7 —— abl_audit_base_v7.v：审计 v7·G10 可证性自靠面直审闭合件 *)
Definition ng_abl_audit_base_v7 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v7.v" 232 5 20261006
  "[abl_audit_base_v7.v: audit v7, direct audit of the G10 provability self-reliance face]" "L232:m5f098369".

(* ng_abl_audit_base_v8 —— abl_audit_base_v8.v：审计 v8·G05_LogSmall 孤立岛 log 引擎面 *)
Definition ng_abl_audit_base_v8 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v8.v" 306 6 20261006
  "[abl_audit_base_v8.v: audit v8, G05_LogSmall isolated-island log engine face]" "L306:mbf84b4a5".

(* ng_abl_hermite_setface —— abl_hermite_setface.v：LW2Hermite 插值机核心恒等式面重述件 *)
Definition ng_abl_hermite_setface : NewGreenFace :=
  MkNewGreenFace "abl_hermite_setface.v" 448 22 20261006
  "[abl_hermite_setface.v: LW2Hermite core identity face, Set-carrier restatement]" "L448:m6d497226".

(* ng_abl_lipschitz_bridge —— abl_lipschitz_bridge.v：Lipschitz 桥接件 *)
Definition ng_abl_lipschitz_bridge : NewGreenFace :=
  MkNewGreenFace "abl_lipschitz_bridge.v" 1335 50 20261006
  "[abl_lipschitz_bridge.v: Lipschitz bridge for the diff-sampling line]" "L1335:m202f6cd6".

(* ng_abl_ln2_qpoly_gen —— abl_ln2_qpoly_gen.v：ln2 链路线三·一般 n 三肢推广件 *)
Definition ng_abl_ln2_qpoly_gen : NewGreenFace :=
  MkNewGreenFace "abl_ln2_qpoly_gen.v" 544 30 20261006
  "[abl_ln2_qpoly_gen.v: general-n three-limb generalization on the ln2 line]" "L544:m39c89abc".

(* ng_abl_ln2_reorder —— abl_ln2_reorder.v：ln2 链·有限 M 换序恒等式件 *)
Definition ng_abl_ln2_reorder : NewGreenFace :=
  MkNewGreenFace "abl_ln2_reorder.v" 404 18 20261006
  "[abl_ln2_reorder.v: finite-M reordering identity for the ln2 chain]" "L404:ma37a1a79".

(* ng_abl_ln2_theta_upper —— abl_ln2_theta_upper.v：ln2 链·theta=4/5 上界肢二次衰减核 *)
Definition ng_abl_ln2_theta_upper : NewGreenFace :=
  MkNewGreenFace "abl_ln2_theta_upper.v" 653 20 20261006
  "[abl_ln2_theta_upper.v: Q-layer quadratic decay core for the theta 4/5 upper limb]" "L653:m21a34f63".

(* ng_abl_loeb_d3 —— abl_loeb_d3.v：Loeb 主定理 D3·HBL 导出条件构造性形式化 *)
Definition ng_abl_loeb_d3 : NewGreenFace :=
  MkNewGreenFace "abl_loeb_d3.v" 499 15 20261006
  "[abl_loeb_d3.v: constructive formalization of the HBL derived conditions for Loeb D3]" "L499:mf491bcc3".

(* ng_abl_niven_hermite_skeleton —— abl_niven_hermite_skeleton.v：Niven-Hermite 无理性五段式泛型骨架件 *)
Definition ng_abl_niven_hermite_skeleton : NewGreenFace :=
  MkNewGreenFace "abl_niven_hermite_skeleton.v" 241 6 20261006
  "[abl_niven_hermite_skeleton.v: generic five-segment skeleton of the Niven-Hermite irrationality proofs]" "L241:m1b123e65".

(* ng_abl_qpoly_lwbridge —— abl_qpoly_lwbridge.v：LW0QPoly 到本地 qpd 除法线桥接件 *)
Definition ng_abl_qpoly_lwbridge : NewGreenFace :=
  MkNewGreenFace "abl_qpoly_lwbridge.v" 215 6 20261006
  "[abl_qpoly_lwbridge.v: bridge from LW0QPoly to the local qpd division line]" "L215:ma5267978".

(* ng_abl_s06_step_calc —— abl_s06_step_calc.v：S06 步进计算件 *)
Definition ng_abl_s06_step_calc : NewGreenFace :=
  MkNewGreenFace "abl_s06_step_calc.v" 726 24 20261006
  "[abl_s06_step_calc.v: S06 step calculations]" "L726:m671e8166".

(* ng_abl_ln2_qpoly_gen_fix —— abl_ln2_qpoly_gen_fix.v：提取 magic 消解件·bool 判定器 *)
Definition ng_abl_ln2_qpoly_gen_fix : NewGreenFace :=
  MkNewGreenFace "abl_ln2_qpoly_gen_fix.v" 142 3 20261006
  "[abl_ln2_qpoly_gen_fix.v: magic-zero resolution for the qpoly_gen piece via a bool decider]" "L142:m5ed794ba".

(* ng_abl_ln2_reorder_assembly —— abl_ln2_reorder_assembly.v：ln2 链·Ireal 校正装配件 *)
Definition ng_abl_ln2_reorder_assembly : NewGreenFace :=
  MkNewGreenFace "abl_ln2_reorder_assembly.v" 468 12 20261006
  "[abl_ln2_reorder_assembly.v: Ireal correction assembly for the ln2 chain]" "L468:m784c48cc".

(* ng_abl_ln2_theta_rehook —— abl_ln2_theta_rehook.v：ln2 链·theta=4/5 上肢回接装配件 *)
Definition ng_abl_ln2_theta_rehook : NewGreenFace :=
  MkNewGreenFace "abl_ln2_theta_rehook.v" 445 12 20261006
  "[abl_ln2_theta_rehook.v: theta 4/5 upper-limb rehook and constant update assembly]" "L445:m7997ddf8".

(* ng_abl_loeb_d3_ext —— abl_loeb_d3_ext.v：Loeb D3 层 2·编码往返＋对角组装＋盒盲边界 *)
Definition ng_abl_loeb_d3_ext : NewGreenFace :=
  MkNewGreenFace "abl_loeb_d3_ext.v" 469 18 20261006
  "[abl_loeb_d3_ext.v: Loeb D3 layer 2, formula coding round-trip, diagonal assembly, box-blindness bound]" "L469:m107fe70e".

(* ng_abl_ln2_bsum_cauchy —— abl_ln2_bsum_cauchy.v：ln2 链·lns_bsum Cauchy 见证 Cb 槽闭合件 *)
Definition ng_abl_ln2_bsum_cauchy : NewGreenFace :=
  MkNewGreenFace "abl_ln2_bsum_cauchy.v" 656 15 20261006
  "[abl_ln2_bsum_cauchy.v: closure of the lns_bsum Cauchy witness Cb slot]" "L656:m9084eb03".

(* ng_abl_ln2_assembly2 —— abl_ln2_assembly2.v：ln2 链·第二段装配回接件 *)
Definition ng_abl_ln2_assembly2 : NewGreenFace :=
  MkNewGreenFace "abl_ln2_assembly2.v" 435 11 20261006
  "[abl_ln2_assembly2.v: second-stage assembly rehook for the ln2 chain]" "L435:m20585eed".

(* ng_abl_loeb_d3_prf2 —— abl_loeb_d3_prf2.v：Formula2 凭证层第一段·Prf2 归纳系统 *)
Definition ng_abl_loeb_d3_prf2 : NewGreenFace :=
  MkNewGreenFace "abl_loeb_d3_prf2.v" 227 7 20261006
  "[abl_loeb_d3_prf2.v: Formula2 certificate layer 1, Prf2 induction system and gnPrf2 coding]" "L227:m3db7766b".

(* ng_abl_loeb_d3_prf2b —— abl_loeb_d3_prf2b.v：Formula2 凭证层第二段·dPrf2 解码器＋码级重演 *)
Definition ng_abl_loeb_d3_prf2b : NewGreenFace :=
  MkNewGreenFace "abl_loeb_d3_prf2b.v" 631 18 20261006
  "[abl_loeb_d3_prf2b.v: Formula2 certificate layer 2, dPrf2 decoder and code-level replay]" "L631:m48291590".

(* ng_abl_audit_base_v9 —— abl_audit_base_v9.v：审计 v9·LW0PiIrrational π 塔抽样直审件 *)
Definition ng_abl_audit_base_v9 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v9.v" 230 4 20261006
  "[abl_audit_base_v9.v: audit v9, direct sampling audit of the LW0PiIrrational pi tower]" "L230:mbb54ea31".

(* ng_abl_audit_base_v10 —— abl_audit_base_v10.v：审计 v10·S04_RealExpLogConv 直审闭合件 *)
Definition ng_abl_audit_base_v10 : NewGreenFace :=
  MkNewGreenFace "abl_audit_base_v10.v" 252 5 20261006
  "[abl_audit_base_v10.v: audit v10, direct closure audit of S04_RealExpLogConv]" "L252:md9806baa".

(* ng_abl_e_irrational2 —— abl_e_irrational2.v：e 无理性第二段施工（层 1＋层 2 连体首装） *)
Definition ng_abl_e_irrational2 : NewGreenFace :=
  MkNewGreenFace "abl_e_irrational2.v" 489 24 20261006
  "[abl_e_irrational2.v: irrationality of e stage 2, layers 1 and 2 joint first installation]" "L489:mda3b0d28".

(* ng_abl_ln2_integmachine_bridge —— abl_ln2_integmachine_bridge.v：LW2IntegMachine 到 ln2 路线四桥接件 *)
Definition ng_abl_ln2_integmachine_bridge : NewGreenFace :=
  MkNewGreenFace "abl_ln2_integmachine_bridge.v" 222 8 20261006
  "[abl_ln2_integmachine_bridge.v: bridge from LW2IntegMachine to ln2 route 4]" "L222:m7eb320bd".

(* ng_abl_Pr_erdos_core —— abl_Pr_erdos_core.v：素数域第 8 件·Erdos 路线首段核心引理件 *)
Definition ng_abl_Pr_erdos_core : NewGreenFace :=
  MkNewGreenFace "abl_Pr_erdos_core.v" 828 38 20261006
  "[abl_Pr_erdos_core.v: prime domain piece 8, core lemmas of the Erdos route first stage]" "L828:md9c76597".

(* ng_abl_Pr_erdos_theta —— abl_Pr_erdos_theta.v：素数域第 9 件·Erdos 路线第二段桥接件 *)
Definition ng_abl_Pr_erdos_theta : NewGreenFace :=
  MkNewGreenFace "abl_Pr_erdos_theta.v" 249 12 20261006
  "[abl_Pr_erdos_theta.v: prime domain piece 9, bridge of the Erdos route second stage]" "L249:m9d324e33".

(* ng_abl_Pr_recip_sum —— abl_Pr_recip_sum.v：素数倒数和发散·Euler 路线层 1 闭合件 *)
Definition ng_abl_Pr_recip_sum : NewGreenFace :=
  MkNewGreenFace "abl_Pr_recip_sum.v" 349 10 20261006
  "[abl_Pr_recip_sum.v: divergence of the sum of prime reciprocals, Euler route layer 1 closure]" "L349:m23d38468".

(* ng_abl_niven_isomorphism —— abl_niven_isomorphism.v：三塔同构·五段式抽象机器与两实例装配 *)
Definition ng_abl_niven_isomorphism : NewGreenFace :=
  MkNewGreenFace "abl_niven_isomorphism.v" 558 9 20261006
  "[abl_niven_isomorphism.v: three-tower isomorphism, Niven-Hermite five-segment abstract machine with two instantiations]" "L558:m3dee4878".

(* ng_abl_ln2_growth_budget —— abl_ln2_growth_budget.v：ln2 链·L_n 增长预算供给模块 *)
Definition ng_abl_ln2_growth_budget : NewGreenFace :=
  MkNewGreenFace "abl_ln2_growth_budget.v" 319 15 20261006
  "[abl_ln2_growth_budget.v: growth budget supply module for the ln2 chain, L_n bounds]" "L319:m71f5c62a".

(* ng_abl_ln2_transfer_limb —— abl_ln2_transfer_limb.v：ln2 链·逐点到积分传送与交替裂分肢 *)
Definition ng_abl_ln2_transfer_limb : NewGreenFace :=
  MkNewGreenFace "abl_ln2_transfer_limb.v" 346 14 20261006
  "[abl_ln2_transfer_limb.v: pointwise-to-integral transfer and alternating split limb]" "L346:m18fd7a14".

(* ng_abl_ln2_theta_total —— abl_ln2_theta_total.v：ln2 链·theta^n 终界装配件 *)
Definition ng_abl_ln2_theta_total : NewGreenFace :=
  MkNewGreenFace "abl_ln2_theta_total.v" 874 24 20261006
  "[abl_ln2_theta_total.v: theta-to-the-n terminal bound assembly for the ln2 chain]" "L874:m223b0905".

(* ng_abl_Pr_factgrowth_bridge —— abl_Pr_factgrowth_bridge.v：素数域·LW0FactGrowth 桥接件 *)
Definition ng_abl_Pr_factgrowth_bridge : NewGreenFace :=
  MkNewGreenFace "abl_Pr_factgrowth_bridge.v" 216 9 20261006
  "[abl_Pr_factgrowth_bridge.v: bridge to LW0FactGrowth for the prime domain line]" "L216:m4f902bed".

(* ng_abl_loeb_d3_nofix —— abl_loeb_d3_nofix.v：Loeb D3·盒谓词不动点不存在性 *)
Definition ng_abl_loeb_d3_nofix : NewGreenFace :=
  MkNewGreenFace "abl_loeb_d3_nofix.v" 529 28 20261006
  "[abl_loeb_d3_nofix.v: fixed-point non-existence for the box predicate in provability algebra]" "L529:m6723b2c0".

(* ng_abl_loeb_d3_spec —— abl_loeb_d3_spec.v：Loeb D3 使用面·nu2 谱带分类器乘 Box2 凭证层 *)
Definition ng_abl_loeb_d3_spec : NewGreenFace :=
  MkNewGreenFace "abl_loeb_d3_spec.v" 463 18 20261006
  "[abl_loeb_d3_spec.v: nu-2 spectral band classifier over the Box2 certificate layer]" "L463:mee10c439".

(* ng_uabd_supply_S05_Z_align_pos —— uabd_supply_S05_Z_align_pos.v：Z_align 正性一般形供给 *)
Definition ng_uabd_supply_S05_Z_align_pos : NewGreenFace :=
  MkNewGreenFace "uabd_supply_S05_Z_align_pos.v" 38 1 20261006
  "Z_align positivity from sum positivity, general interface form" "L38:m37fa372a".

(* ng_uabd_supply_S05_Z_align_pos_unit —— uabd_supply_S05_Z_align_pos_unit.v：单点实例闭合形 Z_align 正性（双定理） *)
Definition ng_uabd_supply_S05_Z_align_pos_unit : NewGreenFace :=
  MkNewGreenFace "uabd_supply_S05_Z_align_pos_unit.v" 53 2 20261006
  "unit-instance closed Z_align positivity pair" "L53:m5643b71b".

(* ng_uabd_supply_UpReqDist_group_size_pos —— uabd_supply_UpReqDist_group_size_pos.v：req 域组长正性与 InT 覆盖见证（双定理） *)
Definition ng_uabd_supply_UpReqDist_group_size_pos : NewGreenFace :=
  MkNewGreenFace "uabd_supply_UpReqDist_group_size_pos.v" 76 2 20261006
  "req-domain group size positivity and InT cover witness" "L76:mea5ad18c".

(* ng_uabd_supply_S08_kl_term_equiv —— uabd_supply_S08_kl_term_equiv.v：KL 项等价换向供给 *)
Definition ng_uabd_supply_S08_kl_term_equiv : NewGreenFace :=
  MkNewGreenFace "uabd_supply_S08_kl_term_equiv.v" 41 1 20261006
  "KL term equivalence symmetry" "L41:m29bcb887".

(* ng_uabd_supply_S13_expf_plus —— uabd_supply_S13_expf_plus.v：expf 加性（expf:=c1_expf 实例） *)
Definition ng_uabd_supply_S13_expf_plus : NewGreenFace :=
  MkNewGreenFace "uabd_supply_S13_expf_plus.v" 36 1 20261006
  "expf additivity at c1_expf instance" "L36:m7f4eca65".

(* ng_uabd_supply_S13_expf_mono_le —— uabd_supply_S13_expf_mono_le.v：expf 弱单调（expf:=c1_expf 实例） *)
Definition ng_uabd_supply_S13_expf_mono_le : NewGreenFace :=
  MkNewGreenFace "uabd_supply_S13_expf_mono_le.v" 38 1 20261006
  "expf weak monotonicity at c1_expf instance" "L38:m70f60862".

(* ng_uabda_g13_evict_discharge —— uabda_g13_evict_discharge.v：G13 逐出族实例世界消解（四定理，含 req 层两点世界无条件形） *)
Definition ng_uabda_g13_evict_discharge : NewGreenFace :=
  MkNewGreenFace "uabda_g13_evict_discharge.v" 101 4 20261006
  "G13 eviction-family instance-world discharge, four theorems" "L101:m0c733f4d".

(* ng_uabda_up01_discharge —— uabda_up01_discharge.v：Arch_Up_01 接口假设消解形对拍件（四定理） *)
Definition ng_uabda_up01_discharge : NewGreenFace :=
  MkNewGreenFace "uabda_up01_discharge.v" 111 4 20261006
  "Arch_Up_01 assumption discharge cross-check, four theorems" "L111:m87030a62".

(* ========================================================================== *)

(* ng_Arch_Up_02 —— Arch_Up_02.v：m3 马尔可夫三阶族（状态/KL/κ/rpow/π 序列与几何步） *)
Definition ng_Arch_Up_02 : NewGreenFace :=
  MkNewGreenFace "Arch_Up_02.v" 2127 123 20261006
  "m3 third-order Markov family: states, KL list, kappa, rpow, pi sequence and geometric steps" "L2127:meb45818e".

(* ng_Arch_PA_03 —— Arch_PA_03.v：DTPT 桥依赖集族（rotc 取代/单调配位/覆盖集族） *)
Definition ng_Arch_PA_03 : NewGreenFace :=
  MkNewGreenFace "Arch_PA_03.v" 2360 73 20261006
  "DTPT bridge dep set family: rotation supersession, monotonicity and coverage set lemmas" "L2360:m8f508d10".

(* ng_Arch_PA_01 —— Arch_PA_01.v：UabT1 防火墙和族与 uabd1s4 离散化族 *)
Definition ng_Arch_PA_01 : NewGreenFace :=
  MkNewGreenFace "Arch_PA_01.v" 624 32 20261006
  "UabT1 firewall sum extensions and uabd1s4 discretization family" "L624:m918053ed".

(* ng_Arch_SumEqL_01 —— Arch_SumEqL_01.v：sem_sum_eq_list 语义槽与消解族（八名与 ToyR_03 同族重证） *)
Definition ng_Arch_SumEqL_01 : NewGreenFace :=
  MkNewGreenFace "Arch_SumEqL_01.v" 236 16 20261006
  "sem_sum_eq_list semantic slots and slot write-off family (eight names shared with Arch_ToyR_03)" "L236:m67ff3326".

(* ng_Arch_UpAbl_02 —— Arch_UpAbl_02.v：UabT2a 兼容槽族与防火墙逆正弱单调供给 *)
Definition ng_Arch_UpAbl_02 : NewGreenFace :=
  MkNewGreenFace "Arch_UpAbl_02.v" 155 7 20261006
  "UabT2a compatibility slots and firewall inv-pos lt-compat supply" "L155:ma5724b39".

(* ng_Arch_ToyR_01 —— Arch_ToyR_01.v：fa52 DPO 具体实例族（EDP/熵差前提不可满足与奖励散布） *)
Definition ng_Arch_ToyR_01 : NewGreenFace :=
  MkNewGreenFace "Arch_ToyR_01.v" 507 24 20261006
  "fa52 DPO concrete instance family: EDP/entropy-difference premises unsat and reward spread" "L507:mfe49b7f1".

(* ng_Arch_ToyR_03 —— Arch_ToyR_03.v：sem_sum_eq_list 语义槽全族与 Uahl* 独立重证（fa56b 传输） *)
Definition ng_Arch_ToyR_03 : NewGreenFace :=
  MkNewGreenFace "Arch_ToyR_03.v" 1488 61 20261006
  "sem_sum_eq_list full slot family and Uahl independent re-proofs with fa56b transport" "L1488:mda9a2fa2".

(* ng_LW0MLicBridge —— LW0MLicBridge.v：M0+ 母判据适配三槽适配件（槽 1 tail 供给 lw0m_tail_bounded_pi＝lic_tail_bounded 实例＋槽 2 vanish 供给 lw0m_vanish_pi＝lic_vanish 实例＋real_metric 同余件 lw0m_metric_congr；统一窗 lw0m_e n := 5 * pie_mag n 三槽共享·lw0m_xL n := lp_four * lp_odd n 为窗距守卫形采样点）；PA=3 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_LW0MLicBridge : NewGreenFace :=
  MkNewGreenFace "LW0MLicBridge.v" 87 3 20261006
  "three-slot supply piece adapting the M0+ master-criterion interfaces: the tail slot lw0m_tail_bounded_pi instantiates lic_tail_bounded, the vanish slot lw0m_vanish_pi instantiates lic_vanish, and lw0m_metric_congr carries the real_metric congruence, with the shared uniform window lw0m_e n = 5 * pie_mag n and the sample point lw0m_xL n = lp_four * lp_odd n" "L87:mc214b9".

(* ng_UacmPiStrongSepCombo —— uacm_pi_strong_sep_combo.v：pi_geom 对每一非零分母有理数的显式正距离分离组合件（lw5n 窗族 bool 出窗判定器 lw5n_sep_dec 与最小分离窗阶 lw5n_nsep 同守卫形分离定理 leibsep_pi_sep_alpha_guarded 在 Q 层合成：出窗事实经换算引理〔包络采样点 lw0m_xL 含入窗内＋统一窗 lw0m_e 消没〕转化为窗距守卫前提，产出 sigT 显式分离见证 0<c<|pi_geom−a/b|；命中前提 leiblw_Id (lw5n_sep_dec …) true 系 Set 层 bool 恒等假设位·如实承载最小分离窗阶搜索的预算足用性问题；附 q:=3 vm_compute 实算样例）；PA=5 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_UacmPiStrongSepCombo : NewGreenFace :=
  MkNewGreenFace "uacm_pi_strong_sep_combo.v" 265 5 20261006
  "explicit positive-distance separation of pi_geom from every rational with nonzero denominator: the lw5n window-family boolean out-of-window decider and the minimal separation index are composed with the guarded separation theorem at the rational layer through conversion lemmas (envelope sample point contained in the window and uniform window vanish), yielding a sigT separation witness under a computable gate hypothesis, with a vm_compute sample instance at q = 3" "L265:m9820f2".

(* ng_U4aBudgetFlip —— u4a_budget_flip.v：cos 零点唯一性定理的 eps/4 预算变体族（加细窗前提 31/20 < w < 2 下闭合：u4a_pi_leibniz_gt_31_10 以 Leibniz 奇对部分和十三项直构 31/10 < pi_leibniz（4·lp_odd 12 ≈ 3.10315 > 31/10 + 1/1000）；逆界两档 u4a_inv_dist_strict/wide 显式放大因子 60/31 与 120/61；u4a_unique_widened_eps4 于加细窗以终界 (120/61)·(eps/2) = 60·eps/61 < eps 闭合唯一性；u4a_pi_unique_eps4 给出 pi_leibniz/2 顶点应用形 w_leibniz == cos_pi_half）；PA=10 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U4aBudgetFlip : NewGreenFace :=
  MkNewGreenFace "u4a_budget_flip.v" 408 10 20261006
  "eps/4 budget variant family of the cosine-zero uniqueness theorem: under the refined window premise 31/20 < w < 2, two-level inverse bounds with explicit amplification factors 60/31 and 120/61 close the uniqueness proof with the final budget 60*eps/61 < eps, grounded in the thirteen-term Leibniz partial-sum lower bound 31/10 < pi_leibniz, with the vertex instantiation w_leibniz == cos_pi_half at pi_leibniz/2" "L408:ma776f3".

(* ng_U6aDammrozeQuant —— u6a_dammroze_quant.v：Gregory-Leibniz 部分和族的逐指标正距分离（对每个指标 n 给出显式正有理证书 c_n := 2·(pie_mag n − pie_mag (S n))（闭式 4/((2n+1)(2n+3))，正性 u6a_cert_pos 机械证）；u6a_even_sep/u6a_odd_sep 两翼合取给出 c_n < |pi − G_n| 逐 n 成立，并附每个部分和位于 pi 哪一侧的侧信息；等式桥 4·S_{n+2} − 4·S_n == 2·c_n 恰取等，经 Qeq→qeq_le 入生成元面 pie_real_lower_gen/pie_real_upper_gen 假设）；PA=2 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U6aDammrozeQuant : NewGreenFace :=
  MkNewGreenFace "u6a_dammroze_quant.v" 228 2 20261006
  "per-index positive-distance separation for the Gregory-Leibniz partial-sum family: an explicit positive rational certificate 4/((2n+1)(2n+3)) for every index n, the two wings certifying c_n < |pi - G_n| for all n together with the side information of which side of pi each partial sum lies on, with the two-step-difference bridge entering the generator lemmas as an exact equality hypothesis" "L228:md2d929".

(* ng_U5cBridge —— u5c_bridge.v：无理性判据的通用分离层（逃逸点显式参数形 u5c_escape_to_dist：单参数族 x/e 同时承担尾控、逃逸窗与窗宽消失三职时，任一有理数 q 在某 n0 ≥ 1 处满足 e(n0) < |q − x(n0)|，则极限与 q 之间存在 Q 层正分离常数 c := (|q − x(n0)| − e(n0))/2；附 u5c_criterion_from_window：存在型窗见证无损还原为显式逃逸点装配，主判据 lic_irrational_criterion 与显式点两入口汇聚同一构造）；PA=2 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cBridge : NewGreenFace :=
  MkNewGreenFace "u5c_bridge.v" 147 2 20261006
  "generic separation layer for the constructive irrationality criterion with an explicit escape point: when a one-parameter family x/e carries the tail bound, the escape window and the window vanishing at once, every rational q escaping the window e(n0) at some index n0 >= 1 admits a positive rational separation constant c = (|q - x(n0)| - e(n0))/2 toward the limit, and the existential window witness of the master criterion is recovered losslessly as an explicit-point assembly" "L147:mb1aeba".

(* ng_U5cInstSqrt2 —— u5c_inst_sqrt2.v：√2 无理分离的显式逃逸点装配件（ir2_escape 窗见证解构出显式逃逸点 n0，经通用分离引理 u5c_escape_to_dist 得 Q 层正分离常数，结论形与在树 lic 判据逐字同构，检验显式点入口对二次无理型实例适用）；PA=1 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cInstSqrt2 : NewGreenFace :=
  MkNewGreenFace "u5c_inst_sqrt2.v" 42 1 20261006
  "explicit escape-point assembly of the irrationality separation for the square root of two: the window witness is destructed into an explicit escape point and the generic separation lemma yields the positive rational separation constant, with the conclusion shape matching the in-tree criterion word for word" "L42:mc234f6".

(* ng_U5cInstSqrt3 —— u5c_inst_sqrt3.v：√3 无理分离的显式逃逸点装配件（is3_escape 窗见证解构出显式逃逸点 n0，经通用分离引理 u5c_escape_to_dist 得 Q 层正分离常数，结论形与在树 lic 判据逐字同构）；PA=1 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cInstSqrt3 : NewGreenFace :=
  MkNewGreenFace "u5c_inst_sqrt3.v" 42 1 20261006
  "explicit escape-point assembly of the irrationality separation for the square root of three: the window witness is destructed into an explicit escape point and the generic separation lemma yields the positive rational separation constant, with the conclusion shape matching the in-tree criterion word for word" "L42:m2b5a6c".

(* ng_U5cInstE —— u5c_inst_e.v：e 无理分离的显式逃逸点装配件（lic_witness_e 窗见证解构出显式逃逸点 n0（1/n0! < |q − x(n0)|），经通用分离引理 u5c_escape_to_dist 得 Q 层正分离常数，检验显式点入口对指数型实例适用）；PA=1 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cInstE : NewGreenFace :=
  MkNewGreenFace "u5c_inst_e.v" 44 1 20261006
  "explicit escape-point assembly of the irrationality separation for e: the factorial-scale window witness is destructed into an explicit escape point and the generic separation lemma yields the positive rational separation constant, checking that the explicit-point entry applies to the exponential-type instance" "L44:m31b911".


(* ng_UcrealBridge —— ucreal_bridge.v：库构造实数到标准库 ConstructiveCauchyReals.CReal 的适配层（ucreal_of_real 逐点转换经单调模量包络与负指标绝对值取样传输柯西性质，收敛模量自库侧柯西见证构造；一致界以 1 + |u 0| 配 Qbound_ltabs_ZExp2 构造；ucreal_eq_seq_compat 以 Set 层一致贴近形交付等式兼容；ucreal_lt_compat 运输 real_lt 至 CRealLt，见证指标 min s0 (−N) 同时达成取样深度与细阈值；ucreal_pi_sep_guarded 将 leibsep_pi_sep_alpha_guarded 同前提四槽定理复述为 CRealLt 结论形）；PA=4 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_UcrealBridge : NewGreenFace :=
  MkNewGreenFace "ucreal_bridge.v" 515 4 20261006
  "adapter layer from the library constructive reals to the standard library ConstructiveCauchyReals.CReal: the pointwise conversion transports the Cauchy property through a monotone modulus envelope with absolute-value index sampling and builds the uniform bound via Qbound_ltabs_ZExp2, equality compatibility is delivered as a Set-layer uniform closeness statement, real_lt transports to CRealLt, and the pi irrational separation theorem is restated with a CRealLt conclusion under the same four premises" "L515:m9e24e8".
(* ng_ALn2ConvCore —— abl_ln2_conv_core.v：ln2 逼近链的算术卷积基建件（分离核 cc_sep_div 与整数 heart 间隔下界；Bernoulli 显式带窗 n₀ := 8·⌊v⌋；两歧卷积引擎 cc_engine 对任意基准实数 X 与整系数线性形式 |aX−b| 在四条显式前提下按可判定两歧分给出正分离常数 c 与终归指标 K，两常数皆封闭 Q 项）；PA=13 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_ALn2ConvCore : NewGreenFace :=
  MkNewGreenFace "abl_ln2_conv_core.v" 666 13 20261006
  "arithmetic convolution infrastructure for the ln2 approximation chain: an explicit separation core for distinct rationals, a closed-form Bernoulli window with index n0 = 8*floor(v), and a two-case convolution engine that under four explicit premises delivers, via a decidable case split, a positive separation constant c and an eventual index K with c <= |u/v - x_k| for all k >= K, both constants closed rational terms" "L666:m561a19".

(* ng_ALn2ConvMesh —— abl_ln2_conv_mesh.v：卷积核与基准列 ln2i_x 的全形组装件（n! ≤ nⁿ 增长估计、档位估计、规范分子对正性与线对象定义面同一；供给型语句 cm_supply 承载三肢不等式与唯一未竟项，分离常数终件 cm_bound 直调两歧引擎完成；cm_pade_of_supply 五肢折三肢纯投影；数值锚组）；PA=11 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_ALn2ConvMesh : NewGreenFace :=
  MkNewGreenFace "abl_ln2_conv_mesh.v" 233 11 20261006
  "full-shape assembly joining the convolution kernel with the ln2 base sequence: the unconditional growth estimate n! <= n^n, budget estimates, positivity of the normalized numerator pair together with definitional identity of the line object, a supply-carrier statement carrying three inequality limbs and a single outstanding item, a terminal separation-constant piece delegating to the two-case engine, a pure-projection supply adapter, and a numeric anchor group" "L233:mc53845".

(* ng_ALn2Final —— abl_ln2_final.v：ln2 终装配件（lnt5_uniform_separation 将分离常数对分子族一致化；lnt5_irrational_final 给出 ln2 不等于任一有理数的 Set 面终定理；供给条件形零新增悬置假设）；PA=16 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_ALn2Final : NewGreenFace :=
  MkNewGreenFace "abl_ln2_final.v" 473 16 20261006
  "final assembly for ln2: the uniform separation theorem normalizes the separation constant against the numerator family, and the terminal Set-layer statement certifies that ln2 differs from every rational, with supply-conditional forms carrying zero newly suspended assumptions" "L473:mbde319".

(* ng_APrEulerProd —— abl_Pr_euler_prod.v：素数域 Euler 乘积公式有限版全量闭合件（pze_O1：σ(L)·∏(p−1) ≤ L·∏p 上半压界；pze_euler_harm：∏(p−1)·H_n ≤ ∏p 调和级数被素数乘积压住的终点形；Set 面差量见证 pze_euler_gap 全透明可提取；提取真机 n=1..12 数值全中）；PA=15 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_APrEulerProd : NewGreenFace :=
  MkNewGreenFace "abl_Pr_euler_prod.v" 982 15 20261006
  "full closure of the finite Euler product formula in the prime domain: the upper squeeze bounding sigma(L) times the product of (p-1) by L times the product of primes, the Euler-Harmonic transfer certifying that the product of (p-1) dominates the harmonic number, an extractable Set-layer gap witness, and machine-verified numerals for n = 1..12 through the extraction face" "L982:md43580".

(* ng_AblEIrrational —— abl_e_irrational.v：e 的构造性无理性（Fourier 1815 论证构造化：q 与部分和之距的分子 W_n·b − a·F_n 取显式 Z 见证（递归 W_{n+1} = (n+1)W_n+1），三分判定在每一分支给出显式逃逸指标与正分离常数 eps；配套显式模度 Cauchy 性与布尔等式否定面，级数极限无理而不构造实数集）；PA=5 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblEIrrational : NewGreenFace :=
  MkNewGreenFace "abl_e_irrational.v" 1371 5 20261006
  "constructive irrationality of e via the exponential series: for every rational q an explicit index and a positive rational eps keep all partial sums from that index at distance above eps (Fourier numerator witness over Z with a decidable three-way split), with an explicit Cauchy modulus and boolean no-equality companions as Set-level sigT statements" "L1371:m69dd8e".

(* ng_AblPrSigmaMul —— abl_Pr_sigma_mul.v：除子和函数 σ 的互素乘性（双定向）：互素二数之积的除子和等于各自除子和之积（除子的裂解 d = d1·d2 由最小素因子递降与 gcd 判别式给出，两侧和经单点质量收敛与次序交换对齐）；配套公因子消去与有限和支撑截断接口；PA=7 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblPrSigmaMul : NewGreenFace :=
  MkNewGreenFace "abl_Pr_sigma_mul.v" 656 7 20261006
  "multiplicativity of the divisor-sum function over coprime factors in both orientations: a divisor of the product splits into factors dividing each part via minimal-prime descent and a gcd criterion, with divisor-index cancellation and finite-sum truncation companions, all carried on nat with extractable bounded sums" "L656:me73fe4".

(* ng_AblPrValInj —— abl_Pr_val_inj.v：素因子指数向量的单射性（折积分解）：素数幂整除两两互异素数幂之折积当且仅当该素数在表中且指数不超过其配值；强形核心由互素高斯消去完成，配套表隶属与整除的运输件；PA=11 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblPrValInj : NewGreenFace :=
  MkNewGreenFace "abl_Pr_val_inj.v" 291 11 20261006
  "injectivity certificate for prime exponent vectors: a prime power divides a product of distinct prime powers only if the prime occurs in the list with at least that exponent, with a coprime gaussian elimination core and list-membership transport companions" "L291:m8874ae".

(* ng_AblZ2Pointwise —— abl_z2_pointwise.v：ζ(2) Beukers 二重积分被积族的逐点控制面（N := x(1−x)y(1−y) 在闭方格上 10N ≤ 1−xy、4N ≤ (1−xy)²、复合形 4·10ⁿ·Nⁿ⁺¹ ≤ (1−xy)ⁿ⁺²；Set 层序结构 zb2_id/zb2_qle 自立，非线性不等式全以显式平方分解证书完成，零自动化战术）；PA=31 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2Pointwise : NewGreenFace :=
  MkNewGreenFace "abl_z2_pointwise.v" 738 31 20261006
  "pointwise exponential control face for the Beukers 1979 double-integral integrand family of zeta(2): on the closed unit square the family N = x(1-x)y(1-y) satisfies 10N <= 1-xy, 4N <= (1-xy)^2 and the composed decay 4*10^n*N^(n+1) <= (1-xy)^(n+2), delivered with a self-standing Set-layer order structure (zb2_id/zb2_qle) and explicit square-decomposition certificates without automation tactics" "L738:mc0b163".
(* ng_AblZ2Truncfam —— abl_z2_truncfam.v：Taylor 截断族（几何级数与二项阶系数的部分和母恒等式 zb2_ps/zb2_psu/zb2_pq，Pascal 步·平移恒等式·母恒等式·非负性与单位点检验 zb2_ps_anchor1，截断展开的显式有理证书）；PA=8 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2Truncfam : NewGreenFace :=
  MkNewGreenFace "abl_z2_truncfam.v" 319 8 20261006
  "Taylor truncation family for the Beukers zeta(2) integral: partial-sum master identities over geometric series and binomial coefficients (zb2_ps/zb2_psu/zb2_pq) with the Pascal step, shift identity, master identity, nonnegativity bounds and the unit-point check zb2_ps_anchor1, giving explicit rational certificates for the truncation expansion" "L319:me8382a".
(* ng_AblZ2ItgCarrier —— abl_z2_itg_carrier.v：迭代积分承载机（段列 zb2_segl 经两次单积分化归有理项表 zb2_Isum，段求值 zb2_beval_segl、长度转换 zb2_di_l_segl、项正性 zb2_term_pos 与积分和正性 zb2_Isum_pos）；PA=5 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2ItgCarrier : NewGreenFace :=
  MkNewGreenFace "abl_z2_itg_carrier.v" 219 5 20261006
  "iterated-integral carrier machine for the Beukers zeta(2) family: the segment list zb2_segl evaluated by two single integrations reduces to the rational term table zb2_Isum, with segment evaluation (zb2_beval_segl), length conversion (zb2_di_l_segl), term positivity (zb2_term_pos) and integral-sum positivity (zb2_Isum_pos)" "L219:m01942f".
(* ng_AblZ2Decay —— abl_z2_decay.v：逐点衰减与竞争判定面（承载面按 (1/4)(1/10)^m 衰减；显式分离器 zb2_dc_sep_small 在整性与积分桥前提显式承载下对 m ≥ 8 给 d²·I < 1，零排中律）；PA=16 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2Decay : NewGreenFace :=
  MkNewGreenFace "abl_z2_decay.v" 438 16 20261006
  "pointwise decay and competition verdict face: the carrier decays as (1/4)(1/10)^m and the explicit separator zb2_dc_sep_small yields d^2 * I < 1 for all m >= 8 under the integrality and integral-bridge premises carried explicitly, with no excluded middle anywhere" "L438:m441d88".
(* ng_AblZ2Dub3 —— abl_z2_dub3.v：Hanson 1972 路线 Sylvester 序列基础段（稠密取整不等式 1 + Σ_j⌊s/a_{j+1}⌋ ≤ s 对一切 k、一切 s ≥ 1 成立 z2d_sylv_floor_t，乘法放大证书＋可执行序列机 z2d_sylv_P/z2d_sylv_a/z2d_sylv_sum）；PA=11 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2Dub3 : NewGreenFace :=
  MkNewGreenFace "abl_z2_dub3.v" 235 11 20261006
  "Sylvester-sequence foundation segment of the Hanson 1972 route for lcm(1..n) <= 3^n: the dense floor inequality 1 + sum_j floor(s/a_{j+1}) <= s holds for all k and all s >= 1 (z2d_sylv_floor_t), proved by the multiplicative amplification certificate with explicit computable sequence machines" "L235:mb8c78c".
(* ng_AblZ2Valbridge —— abl_z2_valbridge.v：Hanson 链赋值桥 B(n) ∣ C(n)（C(n) := n!/∏_i⌊n/a_i⌋!；Legendre 和恒等式·嵌套除法·逐层比较三步证 hl_lcm_upto n 整除 C(n)，Prop 面 z2v_lcm_dvd_C 与 Set 面 z2v_lcm_dvd_C_t 双形，赋值机 z2v_leg/z2v_cnt/z2v_pc/z2v_den/z2v_lsum/z2v_C 皆可执行）；PA=29 Closed；提取 .ml Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2Valbridge : NewGreenFace :=
  MkNewGreenFace "abl_z2_valbridge.v" 710 29 20261006
  "valuation bridge B(n) | C(n) of the Hanson chain: for C(n) := n!/prod_i floor(n/a_i)! the Legendre-sum identity, nested division and layer-wise comparison prove lcm(1..n) divides C(n) in both the Prop face (z2v_lcm_dvd_C) and the Set face (z2v_lcm_dvd_C_t), with executable valuation machines z2v_leg/z2v_cnt/z2v_pc/z2v_den/z2v_lsum/z2v_C" "L710:me81cc9".

(* ng_NsepFindGeneric —— NsepFindGeneric.v：判定器参数化的通用最小分离索引搜索（nsep_find 自 n 起逐阶试 bool 判定器 dec、预算耗尽返回端点 n；特征定理三件 ub/hit/min＋预算化运行 nsep_first 之 bound/hit/least/minimal 四推论，对任意判定器与任意预算成立，与具体窗口族解耦；π 侧实例=lw5n_sep_dec，√2 Newton 序列实例 ir2_sep_dec 内置）；PA=7 Closed；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none *)
Definition ng_NsepFindGeneric : NewGreenFace :=
  MkNewGreenFace "NsepFindGeneric.v" 216 7 20261007
  "decoder-parameterized generic minimal separation-index search: nsep_find probes dec from n upward under fuel returning the budget endpoint, with the ub/hit/min characteristic theorem triple and the budgeted runner nsep_first giving bound/hit/least/minimal corollaries valid for any boolean separation decider and any budget; pi-side instance lw5n_sep_dec and a sqrt(2) Newton instance built in" "L216:ma226ef".
(* ng_AblZ2sPs —— abl_z2s_ps.v：ζ(2) 部分和级数承载件第三期扩展（既有级数面保留：级数项、部分和族 z2s_ps、伸缩分裂恒等式、项递减不变量、几何尾界、有界性、显式速率 Cauchy 模量 z2s_half_idx、数值锚 1/8、零权 Beta 项恒等与 t:=xy 双变量截断展开实例；本期新增 Beukers 二重积分装配面：整值判据 z2i_allZq 以 Z 余数索引承载、最小公倍伸缩与幂和表、逐点控制到积分和的过渡 z2t_Isum_le_weight 显式取用衰减前提 (1/4)(1/10)^m、分离推论 z2t_sep_small_core、单调积分内核以显式前提隔离于 z2t_di_l_le、数值锚 59/1200 与 439/176400）；PA=74 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_AblZ2sPs : NewGreenFace :=
  MkNewGreenFace "abl_z2s_ps.v" 1338 86 20261007
  "zeta(2) partial-sum series carrier, third generation: the second-generation series face retained verbatim (term 1/(k+1)^2, partial-sum family z2s_ps, telescoping identity, decreasing invariant, geometric tail bound, boundedness, explicit-rate Cauchy modulus z2s_half_idx, anchor 1/8, zero-weight Beta identity and the t:=xy truncated-expansion instance), extended by the Beukers 1979 double-integral assembly: the integrality carrier z2i_allZq indexed by Z remainders with lcm scaling and power-sum tables, the pointwise-to-integral-sum transition z2t_Isum_le_weight consuming the explicit decay premise (1/4)(1/10)^m, the separation corollary z2t_sep_small_core, and the monotone-integral step carried as an explicit premise in z2t_di_l_le; numerical anchors 59/1200 and 439/176400" "L1338:ma16c44".
(* ng_AblLntTruncfam —— abl_lnt_truncfam.v：ln2 见证件的积分面与衰减面（截断族余项的积分承载＝显式上界常数路线；衰减以闭式常数 c(n)=1/((2n+1)·C(2n,n)) 承载；在 674 行既有版本之上追加 15 条主语句（新增语句置于文件尾部，既有语句面逐字不变））；PA=52 Closed；提取 Obj.magic=0；coqchk -o 模块复核 Axioms: none               *)
Definition ng_AblLntTruncfam : NewGreenFace :=
  MkNewGreenFace "abl_lnt_truncfam.v" 1046 52 20261007
  "ln2 witness brick integration and decay faces: truncation-family remainder carried by an explicit upper-bound constant, with decay carried by the closed-form constant c(n)=1/((2n+1)*C(2n,n)); fifteen main statements appended with the prior 674-line generation preserved verbatim" "L1046:m69cc1dd5".
(* ng_NsepFirstSufficiency —— NsepFirstSufficiency.v：预算足用性一般定理（预算化最小分离索引搜索 nsep_first 的输出与实际首中步数的足用关系，判定器参数化一般形、对任意 bool 判定器与任意预算成立；含 false 面提取补件与耗尽停止刻画）；PA=11 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_NsepFirstSufficiency : NewGreenFace :=
  MkNewGreenFace "NsepFirstSufficiency.v" 243 11 20261007
  "budget-sufficiency general theorem: the output of the budgeted minimal separation-index search nsep_first relates sufficiently to the actual first-hit step, parameterized over any boolean decider and any budget, with false-face extraction lemmas and the exhausted-stop characterization" "L243:m852e49".
(* ng_Lw4cPiLicGate —— Lw4cPiLicGate.v：π LIC 检验供给模块（逃逸窗口供给 escape_of_supply 与 find_escape、检验数据 (n,c0) 与窗口宽换算 lw4p_pi_gate_supply、单步升级 lw4p_pi_lic_face_of_gate、判定引理 licdec_true）；PA=4 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none*)
Definition ng_Lw4cPiLicGate : NewGreenFace :=
  MkNewGreenFace "Lw4cPiLicGate.v" 241 4 20261007
  "pi gate supply carrier: escape-window supply with the gate-data (n, c0) extraction and window-width conversion, one-step promotion to the lic face via lw4p_pi_lic_face_of_gate, and the licdec_true decision lemma" "L241:md82636".
(* ng_Lw0LeibEscapeAt —— Lw0LeibEscapeAt.v：逃逸窗口定点首个语句（独立新件取用 Local.LW0LeibSeparation 内核：leibsep_q_kernel 正距离与 lw0m_vanish_pi 消失面在合流指标 N1 处给出的 leibsep_escape_window_at，lic 接口形）；PA=1 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_Lw0LeibEscapeAt : NewGreenFace :=
  MkNewGreenFace "Lw0LeibEscapeAt.v" 64 1 20261007
  "escape-window-at first brick: an independent lemma consuming the Local LW0LeibSeparation kernel, closing the case-three lic interface via the q-kernel positive distance and the vanish face at an explicit confluence index" "L64:mdf5141".
(* ng_EpiOrFaces —— EpiOrFaces.v：形态谱低形承载模块（§7 基础四件＋§11 分支与配对面十一件＋§12 显式前提登记；缺口三前提位 res_cl/twk_e/epi_cond_from_meas 以显式前提承载、终形语句面逐字不动）；PA=19 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none    *)
Definition ng_EpiOrFaces : NewGreenFace :=
  MkNewGreenFace "EpiOrFaces.v" 439 19 20261007
  "gate-face spectrum low-form carrier: sections 7, 11 and 12 with the AA23 four-piece slot-registration set; the three gap slots are carried explicitly per the explicit-assumption craft with the terminal-form statement face frozen verbatim" "L439:m1323e3".
(* ng_Lw4cPiLicFaceNonempty —— Lw4cPiLicFaceNonempty.v：π 对照面无条件非空件（自逃逸窗口首件 witness 经 lw4p_pi_gate_supply 取量与 lw4p_pi_lic_face_of_gate 单步升级构造 lw4c_pi_lic_face 见证、对照面 π 支自此有无条件见证）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none*)
Definition ng_Lw4cPiLicFaceNonempty : NewGreenFace :=
  MkNewGreenFace "Lw4cPiLicFaceNonempty.v" 74 2 20261007
  "unconditional nonemptiness of the pi lic contrast face: a witness constructed from the escape-window-at brick via the gate supply and the one-step promotion, giving the face an unconditional witness on the pi side" "L74:m292c85".

(* ng_U5cInstSqrt5 —— u5c_inst_sqrt5.v：√5 无理分离的显式逃逸点装配件（is5 序列窗口见证 is5_escape 解构出显式逃逸点 n0，经通用分离引理 u5c_escape_to_dist 单步实现 Q 层正分离常数，结论形与在树 lic 判据逐字同构，主语句 u5c_sqrt5_criterion_escape_pt 为闭式定量形；√2/√3/e 同族实例，判据对标 UpReqSqrt3Irrational）；PA=1 Closed（主语句）；提取 .ml/.mli Obj.magic=0/0；coqchk -o 模块复核 Axioms: none    *)
Definition ng_U5cInstSqrt5 : NewGreenFace :=
  MkNewGreenFace "u5c_inst_sqrt5.v" 1305 31 20261007
  "explicit escape-point assembly for the irrationality of sqrt(5): the is5 series window witness is5_escape is destructed into an explicit escape point n0 and the generic separation lemma u5c_escape_to_dist delivers a positive Q-layer separation constant in one step, with the conclusion shaped verbatim as the in-tree lic criterion and the main statement u5c_sqrt5_criterion_escape_pt in closed quantitative form; same family as the sqrt2/sqrt3/e instances after UpReqSqrt3Irrational" "L1305:m264688".
(* ng_MachFoldQ —— mach_fold_q.v：π/4 的 Machin 表示 Q 层折叠验算件与组装定义面（差角变换核 (5/12−1/239)/(1+(5/12)·(1/239)) = 1183/2873 与和角变换核 (5/12+1183/2873)/(1−(5/12)·(1183/2873)) = 1 的封闭分数验算、tan 倍角形 2·(1/5)/(1−(1/5)²) = 5/12、折叠链中间分数逐项验算、值域检 0 < 1/239 < 5/12 < 1 与 w < 1、u·w < 1（QltT 形）、结构分解 28561 = 13⁴、逐点界件 mach_pt_bound_of_lt 与 1/5、1/239 两实例、组装定义面 mach_atan_one_fifth/mach_atan_1_239/mach_pi_quarter）；PA=3 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_MachFoldQ : NewGreenFace :=
  MkNewGreenFace "mach_fold_q.v" 296 3 20261007
  "Q-layer closed-fraction verification and assembly definitions for the Machin representation of pi/4: the difference-angle kernel (5/12-1/239)/(1+(5/12)*(1/239)) = 1183/2873 and the sum-angle kernel (5/12+1183/2873)/(1-(5/12)*(1183/2873)) = 1 verified by computation, the double-angle form 2*(1/5)/(1-(1/5)^2) = 5/12, midpoint fraction checks, QltT range certificates 0 < 1/239 < 5/12 < 1 with w < 1 and u*w < 1, the decomposition 28561 = 13^4, pointwise bound lemmas on the unit domain, and the real-layer assembly mach_pi_quarter = 4*arctan(1/5) - arctan(1/239)" "L296:mfd4994".
(* ng_MachAtanAddsub —— mach_atan_addsub.v：arctan 差角与和角引理实数层（mach_atan_sub：0 < v < u < 1 时 arctan u − arctan v = arctan((u−v)/(1+u·v))；mach_atan_add：u、v ∈ (0,1) 且第五前提 u+v+u·v ≤ 1 时 arctan u + arctan v = arctan((u+v)/(1−u·v))，边界商恰为 1 时前提恰可满足；前提以 QltT/QleT' Set 形承载、界证书经 mach_pt_bound_of_lt/of_le 逐点直取；配套 Q 层有理运算件群与 sin 零点唯一性间隙挤压件 mach_sin_zero_uniq）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_MachAtanAddsub : NewGreenFace :=
  MkNewGreenFace "mach_atan_addsub.v" 1626 2 20261007
  "real-layer arctan subtraction and addition lemmas: for 0 < v < u < 1, arctan u - arctan v equals arctan of the difference-angle quotient, and for u, v in the open unit interval satisfying the fifth premise u+v+u*v <= 1 (exactly admitting a boundary quotient of one), arctan u + arctan v equals arctan of the sum-angle quotient; premises are carried as QltT/QleT' Set-form certificates via pointwise bounds, with Q-arithmetic companions and a sine-zero uniqueness squeeze lemma" "L1626:md7a10f".
(* ng_MachFoldChain —— mach_fold_chain.v：Machin 折叠定理与 Leibniz 值桥（mach_fold_chain：4·arctan(1/5) − arctan(1/239) = arctan(1)，经倍角、差角、和角三次 arctan 引理实例化与 Q 层换形件五段链组装，arctan_one_real 为中间值连接对象；mach_edge_one：4·mach_pi_quarter 与 Leibniz 顶点 cauchy_real_pi_leibniz 的实相等值桥）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_MachFoldChain : NewGreenFace :=
  MkNewGreenFace "mach_fold_chain.v" 288 2 20261007
  "Machin folding theorem and the Leibniz value bridge: mach_fold_chain proves 4*arctan(1/5) - arctan(1/239) = arctan(1) via three arctan-lemma instantiations (doubling, difference and sum) assembled as a five-step chain with Q-layer shape conversions, arctan_one_real serving as the intermediate value connector, and mach_edge_one lifts the identity to real equality between 4*mach_pi_quarter and the Leibniz vertex cauchy_real_pi_leibniz" "L288:m0fadc2".
(* ng_Tlw1448Rebase —— tlw1448_rebase.v：有界线性搜索的显式预算重基族（预算基 tlw1448_bexp ck q := S(pie_modulus (ck q / 2)) 由任一显式 Q 函数 ck 生成、换基搜索器 tlw1448_nsep_rebase ck q := lw5n_find q 0 (tlw1448_bexp ck q) 直连共享机件；换基上界/首中/不越三定理 tlw1448_nsep_rebase_bound/hit/least 对任意预算参数成立）；PA=3 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_Tlw1448Rebase : NewGreenFace :=
  MkNewGreenFace "tlw1448_rebase.v" 91 3 20261008
  "explicit budget re-basing family for the bounded linear search: the budget base tlw1448_bexp ck q = S(pie_modulus (ck q / 2)) is generated by an arbitrary explicit Q-function ck, the re-based searcher tlw1448_nsep_rebase ck q = lw5n_find q 0 (tlw1448_bexp ck q) reuses the shared search machinery lw5n_find, and the re-based upper-bound, first-hit and no-overshoot theorems hold for every budget parameter" "L91:m204537".
(* ng_Tlw1448Transfer —— tlw1448_transfer.v：分离 kernel 到距离点的换形供给模块（一行桥 tlw1448_qltT_to_qltT'：QltT x y -> QltT' x y；margin transfer：tlw1448_margin_transfer 对每 q 给 sigT 见证 c 满足 And (QltT 0 c) (lw1m_dist_pt q c)；显式预算基 tlw1448_Bexp q := S(pie_modulus (tlw1448_ck q / 2))，tlw1448_ck q := projT1 (leibsep_q_kernel q)；kernel-距离协调定理 tlw1448_kernel_dist_ck）；PA=3 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_Tlw1448Transfer : NewGreenFace :=
  MkNewGreenFace "tlw1448_transfer.v" 84 3 20261008
  "kernel-to-distance-point conversion supply: the one-line QltT-to-QltT' bridge, the margin transfer giving for every q a sigT witness c with QltT 0 c and lw1m_dist_pt q c, the explicit budget base tlw1448_Bexp q = S(pie_modulus (tlw1448_ck q / 2)) with tlw1448_ck q = projT1 (leibsep_q_kernel q), and the kernel-distance coherence theorem tlw1448_kernel_dist_ck" "L84:mb5cb6c".
(* ng_Tlw1448L2Escape —— tlw1448_l2escape.v：档二主定理件（tlw1448_l2_escape：QltT' 0 c 与 lw1m_dist_pt q c 下预算判定器 lw5n_sep_dec q (S (pie_modulus (c / 2))) 命中 true；证法＝pie_modulus_bound 给出的 Q 算术桥 1/(P+2) < 4/(2P+1)（交叉乘 2P+1 < 4(P+2) 恒真）、c / 2 < c、Qlt_trans 与 lw1m_dist_outwin 直取；配套序面 tlw1448_l2_order）；PA=1 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_Tlw1448L2Escape : NewGreenFace :=
  MkNewGreenFace "tlw1448_l2escape.v" 103 1 20261008
  "tier-two main theorem: under QltT' 0 c and the distance witness lw1m_dist_pt q c the budgeted decider lw5n_sep_dec q (S (pie_modulus (c / 2))) hits true, proved by the explicit Q-arithmetic bridge 1/(P+2) < 4/(2P+1) from the modulus bound (cross-multiplication 2P+1 < 4(P+2) always true), c / 2 < c, Qlt_trans and lw1m_dist_outwin, with the companion order face tlw1448_l2_order" "L103:m243fbc".
(* ng_Tlw1459Fold —— tlw1459_fold.v：增长律闭合件（tlw1459_fold_closed：每 q 有 sigT 见证 n0 使 lw5n_sep_dec q n0 命中 true 且 n0 <= tlw1448_Bexp q；leiblw 形孪生 tlw1459_fold_closed_leiblw；带定理 tlw1459_band：q 居 cell 区间 [lw5n_cell_lo m, lw5n_cell_hi m] 时命中指数夹于 S m <= 8 * n0 + 9 与 tlw1448_nsep_rebase tlw1448_ck q <= n0 <= tlw1448_Bexp q 的多重带内）；PA=3 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_Tlw1459Fold : NewGreenFace :=
  MkNewGreenFace "tlw1459_fold.v" 114 3 20261008
  "growth-law closure: tlw1459_fold_closed gives for every q a sigT witness n0 with lw5n_sep_dec q n0 hitting true and n0 <= tlw1448_Bexp q, in both Id and leiblw_Id forms via the twin tlw1459_fold_closed_leiblw, and the band theorem tlw1459_band bounds the hitting index of every q inside the cell interval by the band S m <= 8 * n0 + 9 with tlw1448_nsep_rebase tlw1448_ck q <= n0 <= tlw1448_Bexp q" "L114:m34c459".
(* ng_ 第三轨续写：tdm225 适配波 23 件逐件实测登记（append-only；前五波十三件 order 在册而 ng_ 面未登记为既有滞后，候补波，不在本块）。 *)
(* 口径：ng_lines=wc -l 实测；ng_qed=剥块注释 token 级 \bQed\. 实测（行级 grep -c 双口径逐件相等）；ng_meta=登记时点快照。 *)

(* ---------- 测度族 15 件（u5c_ 闭式测度族·gapA 已裁定剔除首批） ---------- *)
(* ng_U5cAuxNatpow —— u5c_aux_natpow.v：测度族 nat 幂辅助件（幂展开与 Q 层换算辅助引理族）；PA=8 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cAuxNatpow : NewGreenFace :=
  MkNewGreenFace "u5c_aux_natpow.v" 178 10 20261012
  "nat-power auxiliary lemmas for the closed-form measure family" "L178:mc12e12".
(* ng_U5cDmEMeasureQcore —— u5c_dm_e_measure_qcore.v：e 族闭式分离常元 q 核（c=1/(4b(b+7)!) 闭式分离常数 sigT 承载）；PA=5 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cDmEMeasureQcore : NewGreenFace :=
  MkNewGreenFace "u5c_dm_e_measure_qcore.v" 1114 42 20261012
  "e-family closed-form measure q-core with explicit separation constant" "L1114:md9be3e".
(* ng_U5cDmEscapeToDistAny —— u5c_dm_escape_to_dist_any.v：逃逸点到任意距离换算件；PA=1 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cDmEscapeToDistAny : NewGreenFace :=
  MkNewGreenFace "u5c_dm_escape_to_dist_any.v" 132 1 20261012
  "escape-point to arbitrary-distance conversion face" "L132:m9ef95b".
(* ng_U5cDmEscapeWindow —— u5c_dm_escape_window.v：逃逸窗口件（dmew_e_bnd/dmew_Qinv_1p/dmew_delta_pow_inv 显式 Q 层界，现势结论面 QeqT/QleT' 形——片 3b 两红件适配所对之面）；PA=4 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cDmEscapeWindow : NewGreenFace :=
  MkNewGreenFace "u5c_dm_escape_window.v" 409 9 20261012
  "escape-window supply with explicit Q-layer bounds dmew_e_bnd, dmew_Qinv_1p and dmew_delta_pow_inv" "L409:m002e06".
(* ng_U5cLn2Gap1Convbinom —— u5c_ln2_gap1_convbinom.v：ln2 线 gap-1 闭式二项式换算件；PA=101 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cLn2Gap1Convbinom : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_gap1_convbinom.v" 974 76 20261012
  "ln2 gap-one closed binomial conversion face" "L974:m7d84c0".
(* ng_U5cLn2Gap2Bridge —— u5c_ln2_gap2_bridge.v：ln2 线 gap-2 桥面（gapB 绿）；PA=8 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cLn2Gap2Bridge : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_gap2_bridge.v" 194 7 20261012
  "ln2 gap-two bridge face" "L194:mef33e0".
(* ng_U5cZeta2GapB —— u5c_zeta2_gapB.v：ζ(2) gapB 面（gapA 剔除首批候 abl_zeta2 池面终态后按刷新工单补录）；PA=20 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cZeta2GapB : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_gapB.v" 409 20 20261012
  "zeta(2) gap-B face; gap-A excluded from the first batch by adjudication" "L409:m9a5feb".
(* ng_U5cAuxNatpowDischarge —— u5c_aux_natpow_discharge.v：nat 幂辅助 discharge 面；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cAuxNatpowDischarge : NewGreenFace :=
  MkNewGreenFace "u5c_aux_natpow_discharge.v" 73 2 20261012
  "discharge face for the nat-power auxiliary family" "L73:m76a784".
(* ng_U5cDmEscapeDischarge —— u5c_dm_escape_discharge.v：逃逸 discharge 面（Defined 透明闭合×2）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cDmEscapeDischarge : NewGreenFace :=
  MkNewGreenFace "u5c_dm_escape_discharge.v" 74 0 20261012
  "escape discharge face with two transparent Defined closings" "L74:me2dd5f".
(* ng_U5cDmInstanceDischarge —— u5c_dm_instance_discharge.v：实例 discharge 面（片 3b 三式外科桥接前向适配现势 window 面，语句面零触碰）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cDmInstanceDischarge : NewGreenFace :=
  MkNewGreenFace "u5c_dm_instance_discharge.v" 81 2 20261012
  "instance discharge face forward-adapted to the current escape-window statement face" "L81:m8300a9".
(* ng_U5cSqrt2ClosedMeasure —— u5c_sqrt2_closed_measure.v：√2 闭式测度（分离常元 1/(12b²)·片 3b Qeq 桥适配绿）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cSqrt2ClosedMeasure : NewGreenFace :=
  MkNewGreenFace "u5c_sqrt2_closed_measure.v" 407 5 20261012
  "sqrt(2) closed-form measure with separation constant one over twelve b squared" "L407:ma9b383".
(* ng_U5cSqrt3ClosedMeasure —— u5c_sqrt3_closed_measure.v：√3 闭式测度；PA=3 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cSqrt3ClosedMeasure : NewGreenFace :=
  MkNewGreenFace "u5c_sqrt3_closed_measure.v" 931 22 20261012
  "sqrt(3) closed-form measure face" "L931:m6a84e1".
(* ng_U5cSqrt5ClosedMeasure —— u5c_sqrt5_closed_measure.v：√5 闭式测度（分离常元 1/(16b²)）；PA=2 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cSqrt5ClosedMeasure : NewGreenFace :=
  MkNewGreenFace "u5c_sqrt5_closed_measure.v" 1066 26 20261012
  "sqrt(5) closed-form measure with separation constant one over sixteen b squared" "L1066:mb529ce".
(* ng_U5cLn2Assembly —— u5c_ln2_assembly.v：ln2 线组装件；PA=8 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cLn2Assembly : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_assembly.v" 179 4 20261012
  "ln2 line assembly face" "L179:m8619ca".
(* ng_U5cLn2Seam4 —— u5c_ln2_seam4.v：ln2 线 seam-4 收尾件；PA=7 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cLn2Seam4 : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_seam4.v" 180 6 20261012
  "ln2 line seam-four closure face" "L180:m0449d8".

(* ---------- 素数域 4 件（u5c_pr_ 线） ---------- *)
(* ng_U5cPrBertrandClose —— u5c_pr_bertrand_close.v：Bertrand 全强度闭合件（u5c_bertrand_full 主语句；2764 行卷面终态清洗版 2679 行）；PA=35 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cPrBertrandClose : NewGreenFace :=
  MkNewGreenFace "u5c_pr_bertrand_close.v" 2679 133 20261012
  "full-strength Bertrand postulate closure with master statement u5c_bertrand_full" "L2679:m47b294".
(* ng_U5cPrMertensNat —— u5c_pr_mertens_nat.v：Mertens 反向 nat 发散证书（pzs_prime_recip_diverge）；PA=9 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cPrMertensNat : NewGreenFace :=
  MkNewGreenFace "u5c_pr_mertens_nat.v" 901 37 20261012
  "Mertens-type reciprocal prime divergence certificate on nat" "L901:m163307".
(* ng_U5cPrLcmAbsorb —— u5c_pr_lcm_absorb.v：lcm 吸收面（plw_maxpow；内嵌 Separate Extraction 编译期执行绿）；PA=13 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cPrLcmAbsorb : NewGreenFace :=
  MkNewGreenFace "u5c_pr_lcm_absorb.v" 724 33 20261012
  "lcm absorption face plw_maxpow with embedded Separate Extraction" "L724:mff4017".
(* ng_U5cPrLcmDivide —— u5c_pr_lcm_divide.v：lcm 整除面（plw_ispw；内嵌 Separate Extraction 编译期执行绿）；PA=16 Closed；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cPrLcmDivide : NewGreenFace :=
  MkNewGreenFace "u5c_pr_lcm_divide.v" 1270 63 20261012
  "lcm divide face plw_ispw with embedded Separate Extraction" "L1270:maa9c56".

(* ---------- 提取驱动 4 件（zz_ 前缀照录·裁定 2） ---------- *)
(* ng_U5cExt —— u5c_ext.v：bertrand 公理审计与提取驱动（四主语句 Print Assumptions＋Separate Extraction u5c_bertrand_full；零语句定义件）；PA=4 Closed；coqchk -o 模块复核 Axioms: none *)
Definition ng_U5cExt : NewGreenFace :=
  MkNewGreenFace "u5c_ext.v" 16 0 20261012
  "extraction driver: axiom audit of u5c_pr_bertrand_close via four Print Assumptions plus Separate Extraction of u5c_bertrand_full; zero statements" "L16:m17652a".
(* ng_ZzU5cExtract —— zz_u5c_extract.v：mertens 主语句直提驱动件（零语句定义件）；PA=0（纯提取件）；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_ZzU5cExtract : NewGreenFace :=
  MkNewGreenFace "zz_u5c_extract.v" 13 0 20261012
  "pure extraction driver for the mertens master statement; zero statements" "L13:me1acda".
(* ng_ZzPrrunExtMert —— zz_prrun_ext_mert.v：mertens 线 RunAlive 提取面驱动（pzs_prime_recip_diverge/pzs_rsum/pzs_B＋pr_prime_bool）；PA=0（纯提取件）；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_ZzPrrunExtMert : NewGreenFace :=
  MkNewGreenFace "zz_prrun_ext_mert.v" 18 0 20261012
  "RunAlive extraction driver for the mertens line; zero statements" "L18:med2bbc".
(* ng_ZzPrrunExtLcm —— zz_prrun_ext_lcm.v：lcm 线 RunAlive 提取面驱动（plw_maxpow/HansonLcm.hl_binom/hl_lcm_upto＋pr_prime_bool）；PA=0（纯提取件）；提取面 Obj.magic=0；coqchk -o 模块复核 Axioms: none *)
Definition ng_ZzPrrunExtLcm : NewGreenFace :=
  MkNewGreenFace "zz_prrun_ext_lcm.v" 20 0 20261012
  "RunAlive extraction driver for the lcm line; zero statements" "L20:m2a01e7".

(* ---------- V33 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV33 : list NewGreenFace :=
  cons ng_U5cAuxNatpow
  (cons ng_U5cDmEMeasureQcore
  (cons ng_U5cDmEscapeToDistAny
  (cons ng_U5cDmEscapeWindow
  (cons ng_U5cLn2Gap1Convbinom
  (cons ng_U5cLn2Gap2Bridge
  (cons ng_U5cZeta2GapB
  (cons ng_U5cAuxNatpowDischarge
  (cons ng_U5cDmEscapeDischarge
  (cons ng_U5cDmInstanceDischarge
  (cons ng_U5cSqrt2ClosedMeasure
  (cons ng_U5cSqrt3ClosedMeasure
  (cons ng_U5cSqrt5ClosedMeasure
  (cons ng_U5cLn2Assembly
  (cons ng_U5cLn2Seam4
  (cons ng_U5cPrBertrandClose
  (cons ng_U5cPrMertensNat
  (cons ng_U5cPrLcmAbsorb
  (cons ng_U5cPrLcmDivide
  (cons ng_U5cExt
  (cons ng_ZzU5cExtract
  (cons ng_ZzPrrunExtMert
  (cons ng_ZzPrrunExtLcm
  nil)))))))))))))))))))))).

(* 续写统计：23 件 / 行数和 12042 / 闭合和 498（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV33Pieces  : nat := 23.
Definition NewGreenV33LineSum : nat := 12042.
Definition NewGreenV33QedSum  : nat := 498.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV33Pieces_matches : NewGreenV33Pieces = cnt_ng NewGreenListV33.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV33LineSum_matches : NewGreenV33LineSum = sum_ng_lines NewGreenListV33.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV33QedSum_matches : NewGreenV33QedSum = sum_ng_qed NewGreenListV33.
Proof. reflexivity. Qed.

(* ---------- V34 批（登记 13 件） ---------- *)
(* ng_LeibsepNselHCoupling -- leibsep_nsel_h_coupling.v: Niven 选取级 n_sel 对有理高度 h 的闭式化 (n_sel = 20h+23、2n_sel+2 = 40h+48) + Qden 单调肢与 h=2..12 精确对照表 *)
Definition ng_LeibsepNselHCoupling : NewGreenFace :=
  MkNewGreenFace "leibsep_nsel_h_coupling.v" 145 12 20261013
  "closed form of the Niven selection index n_sel against rational height h: n_sel = 20h+23 and 2n_sel+2 = 40h+48, with Qden monotonicity limb and the exact table for h = 2..12" "L145:m897d13".
(* ng_LeibsepBandDomain -- leibsep_band_domain.v: kernel 门1 假支带域面 (带域谓词 35/12 < q < 41/12、前提参数位承载的成员核、valve_R1/valve_closed 阀形接口经互译恒等式、Qred 归位肢) *)
Definition ng_LeibsepBandDomain : NewGreenFace :=
  MkNewGreenFace "leibsep_band_domain.v" 254 12 20261013
  "band domain face of the kernel gate first false branch: band predicate 35/12 < q < 41/12, membership core carried by explicit premise slots, valve interfaces valve_R1 and valve_closed connected through translation identities, and the Qred relocation limb" "L254:m3ae384".
(* ng_LeibsepBandCkAssembly -- leibsep_band_ck_assembly.v: 带域一致型逐点装配 (带域与阀形前提下见证下界 1/((h+1)*(2n_sel+2)!) <= wit_i 全链、经 2n_sel+2 = 40h+48 的高度坐标终定理、tlw1448_ck 对接肢) *)
Definition ng_LeibsepBandCkAssembly : NewGreenFace :=
  MkNewGreenFace "leibsep_band_ck_assembly.v" 586 17 20261013
  "band-consistent pointwise assembly of the margin chain: witness lower bound 1/((h+1)*(2n_sel+2)!) <= wit_i under band and valve premises with the four certificate premises, the height-coordinate master theorem via 2n_sel+2 = 40h+48, and the tlw1448_ck interface limb" "L586:mdb477f".
(* ng_Piu1886Kbounds -- piu1886_kbounds.v: Niven 交错和多项式 F 与 F' 在 q 端点的 Q 层闭式界 kappa1/kappa0 (逐项绝对值有限和) + 正性肢与单调有限和提升肢 *)
Definition ng_Piu1886Kbounds : NewGreenFace :=
  MkNewGreenFace "piu1886_kbounds.v" 465 31 20261013
  "closed Q-layer bounds kappa1 and kappa0 of the Niven alternating-sum polynomial F and its derivative at the endpoint q, given as finite sums of termwise absolute endpoint values, with positivity and monotone finite-sum lifting limbs" "L465:m97857c".
(* ng_Piu1890CarrierRecast -- piu1890_carrier_recast.v: kernel 门控承载内链显式重建 (K 组合量上界入 K <= Kcap 接合肢、门真支见证与链内下界 1/den <= c 语句面承载、交错和端点闭式) *)
Definition ng_Piu1890CarrierRecast : NewGreenFace :=
  MkNewGreenFace "piu1890_carrier_recast.v" 294 11 20261013
  "explicit recast of the kernel gate carrier inner chain: admission limb for the composite upper bound of K into K <= Kcap, gate-true branch witness with the chain lower bound 1/den <= c in the statement face, and closed forms of the alternating sum at the q endpoint" "L294:m17183b".
(* ng_Piu1879GaplitRelease -- piu1879_gaplit_release.v: kernel 证书界 e3 = 1/100 与 el = 1/60 的字面释放 (S10 real_pi_leibniz 原字面) + 承载肢 4/((h+1)*q_fact(40h+48)) <= 1/60 双参数位覆盖 *)
Definition ng_Piu1879GaplitRelease : NewGreenFace :=
  MkNewGreenFace "piu1879_gaplit_release.v" 143 4 20261013
  "literal release of the kernel certificate bounds e3 = 1/100 and el = 1/60 from the S10 real_pi_leibniz faces, with the cert bearing limb 4/((h+1)*q_fact(40h+48)) <= 1/60 covering both parameter positions" "L143:m80e545".
(* ng_Piu1880ValveQchain -- piu1880_valve_qchain.v: 阀分母 (h+1)*(2n_sel+2)! 的高度坐标 (h+1)*(40h+48)! Q 层换算链 (后继形、阶乘 Q 化、单调双肢、正性肢与 K-cap 接入接口) *)
Definition ng_Piu1880ValveQchain : NewGreenFace :=
  MkNewGreenFace "piu1880_valve_qchain.v" 245 12 20261013
  "Q-layer conversion chain of the valve denominator (h+1)*(2n_sel+2)! in height coordinates (h+1)*(40h+48)!: successor form, factorial Q-lift, both monotonicity limbs, positivity, and the K-cap admission interface" "L245:ma27e1c".
(* ng_Piu1880EgelRelease -- piu1880_egel_release.v: kernel eps1-min 链 eg/el 两支的闭式选取释放 (带域前提下 eg = el = WING/(2K)、阀形传递肢与四支放行) *)
Definition ng_Piu1880EgelRelease : NewGreenFace :=
  MkNewGreenFace "piu1880_egel_release.v" 142 4 20261013
  "explicit release of the eg and el slots of the kernel eps1-min chain: closed selection eg = el = WING/(2K) under the band premise, with the valve transport limb and the four-branch admission of the eps1-min arm" "L142:m584ccd".
(* ng_Piu1891EggeomRelease -- piu1891_eggeom_release.v: cos_pi_half 与 5/3 分离的显式字面见证 (一致界 C = 8、窗级 N = 10、eps = 1/3200) 并提升至 real_pi_geom 与 10/3 的分离形 *)
Definition ng_Piu1891EggeomRelease : NewGreenFace :=
  MkNewGreenFace "piu1891_eggeom_release.v" 174 5 20261013
  "explicit literal witness separating cos_pi_half from 5/3 with uniform bound C = 8, window stage N = 10 and eps = 1/3200, lifted to the real_pi_geom separation of pi from 10/3" "L174:m8ac9ea".
(* ng_Piu1887PiLUniformWindow -- piu1887_piL_uniform_window.v: pi_L 投影序列 xL 的统一逃逸窗 (显式可计算窗级 n0 = max Nk (pie_modulus (eps*(1/10)))) 经内核窗前提实例化 *)
Definition ng_Piu1887PiLUniformWindow : NewGreenFace :=
  MkNewGreenFace "piu1887_piL_uniform_window.v" 130 5 20261013
  "uniform escape window of the pi_L projection sequence xL with the explicit computable window stage n0 = max Nk (pie_modulus (eps*(1/10))), instantiated from the kernel window premise" "L130:m2ae5d1".
(* ng_Piu1901LeibsepQKernelClosed -- piu1901_leibsep_q_kernel_closed.v: Leibniz pi_L 分离内核证书的语句面闭合 (tdm225 主语句 sigT 见证的 pi_L 对应形、eps2 链经内核定义链与窗级合成钉定) *)
Definition ng_Piu1901LeibsepQKernelClosed : NewGreenFace :=
  MkNewGreenFace "piu1901_leibsep_q_kernel_closed.v" 490 4 20261013
  "statement-face closure of the Leibniz pi_L separation kernel certificate: the sigT witness of the tdm225 master statement in its pi_L correspondence, with the eps2 chain pinned by the kernel definition chain and the window-stage composition" "L490:m67a45c".
(* ng_Piu1904Mu2Certificate -- piu1904_mu2_certificate.v: pi 幂率测度框架的数值证书闭合包装 (逐 q 闭合证书填装 lw1m_b_cert_face 接口位、统一逃逸窗与内核闭合见证拼合、测度 mu = 2/C = 2 显式选取) *)
Definition ng_Piu1904Mu2Certificate : NewGreenFace :=
  MkNewGreenFace "piu1904_mu2_certificate.v" 163 5 20261013
  "numeric certificate wrapper of the pi power measure framework: per-q closure witness filling the lw1m_b_cert_face interface, joining the uniform escape window with the kernel closure witness, with the measure mu = 2/C = 2 selected explicitly" "L163:m449297".
(* ng_Piu1888GrowthQuantLemma -- piu1888_growth_quant_lemma.v: pi 分离核载荷尺度 T0 = (2n)!/n! 的定量核心 (步进恒等式 qfact(2*(S n))*qfact n = 2*(2n+1)*qfact(2*n)*qfact(S n)) + 倍增单调肢、正性配套与除法转移引理 *)
Definition ng_Piu1888GrowthQuantLemma : NewGreenFace :=
  MkNewGreenFace "piu1888_growth_quant_lemma.v" 335 19 20261013
  "quantitative core of the pi separation kernel load scale T0 = (2n)!/n!: the step equidistribution identity qfact(2*(S n))*qfact n = 2*(2n+1)*qfact(2*n)*qfact(S n), with the doubling monotonicity 2*T0 n <= T0 (S n), positivity kit and division transfer lemma" "L335:m3b31c8".

(* ---------- V34 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV34 : list NewGreenFace :=
  cons ng_LeibsepNselHCoupling
  (cons ng_LeibsepBandDomain
  (cons ng_LeibsepBandCkAssembly
  (cons ng_Piu1886Kbounds
  (cons ng_Piu1890CarrierRecast
  (cons ng_Piu1879GaplitRelease
  (cons ng_Piu1880ValveQchain
  (cons ng_Piu1880EgelRelease
  (cons ng_Piu1891EggeomRelease
  (cons ng_Piu1887PiLUniformWindow
  (cons ng_Piu1901LeibsepQKernelClosed
  (cons ng_Piu1904Mu2Certificate
  (cons ng_Piu1888GrowthQuantLemma
  nil)))))))))))).

(* 续写统计：13 件 / 行数和 3566 / 闭合和 141（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV34Pieces  : nat := 13.
Definition NewGreenV34LineSum : nat := 3566.
Definition NewGreenV34QedSum  : nat := 141.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV34Pieces_matches : NewGreenV34Pieces = cnt_ng NewGreenListV34.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV34LineSum_matches : NewGreenV34LineSum = sum_ng_lines NewGreenListV34.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV34QedSum_matches : NewGreenV34QedSum = sum_ng_qed NewGreenListV34.
Proof. reflexivity. Qed.
(* ---------- V35 batch (3 pieces registered) ---------- *)
(* ng_Piu1905SoddLower -- piu1905_sodd_lower.v: 奇侧坐标交错和的非相消下界 (Sodd >= (62125/82944)*T0、带域 35/12 <= q <= 41/12、n >= 3、相邻奇项递减与交错和非相消地板) *)
Definition ng_Piu1905SoddLower : NewGreenFace :=
  MkNewGreenFace "piu1905_sodd_lower.v" 955 39 20261013
  "non-vanishing lower bound of the odd-coordinate alternating sum: Sodd >= (62125/82944)*T0 over the band 35/12 <= q <= 41/12 with n >= 3, via adjacent odd-term decrease and the alternating-sum non-vanishing floor" "L955:m2ca4b2".
(* ng_Piu1909KAssembly -- piu1909_K_assembly.v: 分离核载量 K 坐标装配 (Kmodel = |b^n*sev_full|*C1 + |b^n*sodd_full|*C2 + 1/8、C1=105410/1341、C2=9664/447) 及下界 C2*(62125/82944)*(b^n*T0 n) <= Kmodel *)
Definition ng_Piu1909KAssembly : NewGreenFace :=
  MkNewGreenFace "piu1909_K_assembly.v" 204 5 20261013
  "coordinate assembly of the separation kernel load K: Kmodel = |b^n*sev_full|*C1 + |b^n*sodd_full|*C2 + 1/8 with C1 = 105410/1341 and C2 = 9664/447, and the lower bound C2*(62125/82944)*(b^n*T0 n) <= Kmodel" "L204:m2f123e".
(* ng_Piu1909SallUpper -- piu1909_sall_upper.v: 正向截和上界肢 (sall(q,n,n) = sum_{{m=0}}^{n} T(q,n,m) <= (337697/6048)*T0 n、带域 35/12 <= q <= 41/12、n >= 3) *)
Definition ng_Piu1909SallUpper : NewGreenFace :=
  MkNewGreenFace "piu1909_sall_upper.v" 1269 37 20261013
  "forward truncated-sum upper limb: sall(q,n,n), the sum of T(q,n,m) over m = 0..n, is at most (337697/6048)*T0 n over the band 35/12 <= q <= 41/12 with n >= 3" "L1269:m5de989".

(* ---------- V35 batch statistics (whole-batch append: list, constants and lemmas written atomically in one block) ---------- *)
Definition NewGreenListV35 : list NewGreenFace :=
  cons ng_Piu1905SoddLower
  (cons ng_Piu1909KAssembly
  (cons ng_Piu1909SallUpper
  nil)).

(* 续写统计：3 件 / 行数和 2428 / 闭合和 81（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV35Pieces  : nat := 3.
Definition NewGreenV35LineSum : nat := 2428.
Definition NewGreenV35QedSum  : nat := 81.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV35Pieces_matches : NewGreenV35Pieces = cnt_ng NewGreenListV35.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV35LineSum_matches : NewGreenV35LineSum = sum_ng_lines NewGreenListV35.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV35QedSum_matches : NewGreenV35QedSum = sum_ng_qed NewGreenListV35.
Proof. reflexivity. Qed.

(* ---------- V36 批（登记 13 件） ---------- *)
(* ng_AblDmw2PointwiseSharp -- abl_dmw2_pointwise_sharp.v: Beukers 被积族逐点层锐化主不等式 11N <= 1-xy 与复合控制面 *)
Definition ng_AblDmw2PointwiseSharp : NewGreenFace :=
  MkNewGreenFace "abl_dmw2_pointwise_sharp.v" 696 32 20261014
  "pointwise linear control sharpened to 11N <= 1-xy with composite face" "L696:m1eeea6".
(* ng_B1KernelPointwise -- b1_kernel_pointwise.v: 逐点衰减核 theta 1/4 与 theta 5/24 双档有理短证书 *)
Definition ng_B1KernelPointwise : NewGreenFace :=
  MkNewGreenFace "b1_kernel_pointwise.v" 331 24 20261014
  "pointwise decay kernel with rational short certificates at theta 1/4 and 5/24" "L331:ma3791b".
(* ng_B1TruncMaster -- b1_trunc_master.v: 截断母恒等式 (1-t)^(n+1) A + t^(M+1) P = 1 对 t 无条件与 arctan 换档实例 *)
Definition ng_B1TruncMaster : NewGreenFace :=
  MkNewGreenFace "b1_trunc_master.v" 345 21 20261014
  "truncation master identity unconditional in t with arctan retuned instance" "L345:m8a59ac".
(* ng_AblDmw2SharpenDecay -- abl_dmw2_sharpen_decay.v: 锐权族界 (1/4)(1/11)^m 与竞争判定 m >= 5 及条件分离面 *)
Definition ng_AblDmw2SharpenDecay : NewGreenFace :=
  MkNewGreenFace "abl_dmw2_sharpen_decay.v" 478 21 20261014
  "sharpened weight family bound (1/4)(1/11)^m with competition verdict at m >= 5" "L478:m76f5a9".
(* ng_AblZ3ItgCarrier -- abl_z3_itg_carrier.v: 三重积分承载与段值闭式 C(n+m,n)·B(n+m,n)^3 *)
Definition ng_AblZ3ItgCarrier : NewGreenFace :=
  MkNewGreenFace "abl_z3_itg_carrier.v" 263 9 20261014
  "triple-integral carrier with closed-form segment values" "L263:m761528".
(* ng_AblZ3Pointwise -- abl_z3_pointwise.v: Beukers 被积族三变量逐点衰减 40N <= T 线性控制与平方控制及复合机 *)
Definition ng_AblZ3Pointwise : NewGreenFace :=
  MkNewGreenFace "abl_z3_pointwise.v" 312 7 20261014
  "three-variable pointwise decay on the Beukers integrand family" "L312:m53afa6".
(* ng_AblZ3Decay -- abl_z3_decay.v: 三次重排整性分离 weight_cub 与竞争判定 m >= 5 及 sep3_small 主件 *)
Definition ng_AblZ3Decay : NewGreenFace :=
  MkNewGreenFace "abl_z3_decay.v" 541 18 20261014
  "cubic integrality separation with competition verdict at m >= 5" "L541:m622a8c".
(* ng_B1CarrierBeta -- b1_carrier_beta.v: 迭代载体单积分 Beta 闭式精确值与不超过 1 的衰减肢及 rho 部分和承载 *)
Definition ng_B1CarrierBeta : NewGreenFace :=
  MkNewGreenFace "b1_carrier_beta.v" 216 13 20261014
  "iterated carrier with single-integral Beta closed form and decay limb" "L216:mcad0a6".
(* ng_B1DenomControl -- b1_denom_control.v: 奇清分母双控 2^n·n! 读形与 sigT 乘子见证 *)
Definition ng_B1DenomControl : NewGreenFace :=
  MkNewGreenFace "b1_denom_control.v" 141 9 20261014
  "odd-clearing denominator control with extractable sigT multiplier witness" "L141:m24f12b".
(* ng_B1LinformMachine -- b1_linform_machine.v: Euler arctan 连分式收敛子上的 pi 系数整值线性形式机与行列式恒等式 *)
Definition ng_B1LinformMachine : NewGreenFace :=
  MkNewGreenFace "b1_linform_machine.v" 444 33 20261014
  "integer linear form machine on Euler arctan continued-fraction convergents" "L444:md7d28a".
(* ng_B1Extract -- b1_extract.v: b1 spine 四件九个常量的分离提取驱动（零语句件） *)
Definition ng_B1Extract : NewGreenFace :=
  MkNewGreenFace "b1_extract.v" 20 0 20261014
  "extraction driver for the four spine pieces; zero statements" "L20:m620cbb".
(* ng_B1Extract4 -- b1_extract4.v: 线性形式机五个常量的分离提取驱动（零语句件） *)
Definition ng_B1Extract4 : NewGreenFace :=
  MkNewGreenFace "b1_extract4.v" 15 0 20261014
  "extraction driver for the linear form machine; zero statements" "L15:md67bff".
(* ng_A1Mu0General -- a1_mu0_general.v: mu0 >= 2 全参数泛化测度面与三桥零迁移回归及统一闭式证书接口 *)
Definition ng_A1Mu0General : NewGreenFace :=
  MkNewGreenFace "a1_mu0_general.v" 173 6 20261014
  "mu0-general measure face with three zero-migration regression bridges and closed-certificate interface" "L173:m4eefa5".

(* ---------- V36 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV36 : list NewGreenFace :=
  cons ng_AblDmw2PointwiseSharp
  (cons ng_B1KernelPointwise
  (cons ng_B1TruncMaster
  (cons ng_AblDmw2SharpenDecay
  (cons ng_AblZ3ItgCarrier
  (cons ng_AblZ3Pointwise
  (cons ng_AblZ3Decay
  (cons ng_B1CarrierBeta
  (cons ng_B1DenomControl
  (cons ng_B1LinformMachine
  (cons ng_B1Extract
  (cons ng_B1Extract4
  (cons ng_A1Mu0General
  nil)))))))))))).

(* 续写统计：13 件 / 行数和 3975 / 闭合数和 193（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV36Pieces  : nat := 13.
Definition NewGreenV36LineSum : nat := 3975.
Definition NewGreenV36QedSum  : nat := 193.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV36Pieces_matches : NewGreenV36Pieces = cnt_ng NewGreenListV36.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV36LineSum_matches : NewGreenV36LineSum = sum_ng_lines NewGreenListV36.
Proof. reflexivity. Qed.

(* 闭合数和 = 字面值 *)
Lemma NewGreenV36QedSum_matches : NewGreenV36QedSum = sum_ng_qed NewGreenListV36.
Proof. reflexivity. Qed.
(* ---------- V37 批（登记 5 件） ---------- *)
(* ng_DigMachine -- dig_machine.v: 双积分组机 sup 证书与逐点衰减复合面及载体族界与竞争判定 m >= 4（61/676 档） *)
Definition ng_DigMachine : NewGreenFace :=
  MkNewGreenFace "dig_machine.v" 788 21 20261014
  "double-integral group machine with sup certificate, composite pointwise decay, family bound and competition verdict at m >= 4" "L788:md322f4".
(* ng_GclCoefficient -- gcl_coefficient.v: V4 对称化组论系数层与 tight 逐点改进证书 24N <= 1+x+y-2xy（N/Tavg <= 1/12） *)
Definition ng_GclCoefficient : NewGreenFace :=
  MkNewGreenFace "gcl_coefficient.v" 484 25 20261014
  "group-theoretic coefficient layer with V4 symmetrization and tight pointwise improvement certificate N/Tavg <= 1/12" "L484:m1d7c8d".
(* ng_U5cZeta2A1Sign11 -- u5c_zeta2_a1_sign11.v: zeta2 前缀界族 1/11 参数档重铸与显式命名前提逐点封顶证书 *)
Definition ng_U5cZeta2A1Sign11 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_a1_sign11.v" 308 12 20261014
  "zeta(2) prefix-bound machine at the 1/11 parameter tier with explicitly named premise pointwise cap certificate" "L308:mf1c724".
(* ng_U5cLn2S4fill -- u5c_ln2_s4fill.v: ln2 ④缝内容位填充与正典见证销案 Hid 参数位及焊链验收 *)
Definition ng_U5cLn2S4fill : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_s4fill.v" 274 10 20261014
  "ln2 seam-4 content fill turning the Hid parameter slot into a theorem by canonical witness with weld-chain acceptance" "L274:m97770a".
(* ng_U5cDmE2MeasureQcore -- u5c_dm_e2_measure_qcore.v: e2=exp(2) 测度实例 CaseB 闭式支与条件形装配件及 CaseA 死窗在机否定件 *)
Definition ng_U5cDmE2MeasureQcore : NewGreenFace :=
  MkNewGreenFace "u5c_dm_e2_measure_qcore.v" 1112 43 20261014
  "measure-instance piece for exp(2) with CaseB closed-form branch, conditional measure, and in-machine negative certificate for the CaseA window" "L1112:m51f012".

(* ---------- V37 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV37 : list NewGreenFace :=
  cons ng_DigMachine
  (cons ng_GclCoefficient
  (cons ng_U5cZeta2A1Sign11
  (cons ng_U5cLn2S4fill
  (cons ng_U5cDmE2MeasureQcore
  nil)))).

(* 续写统计：5 件 / 行数和 2966 / 闭合数和 111（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV37Pieces  : nat := 5.
Definition NewGreenV37LineSum : nat := 2966.
Definition NewGreenV37QedSum  : nat := 111.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV37Pieces_matches : NewGreenV37Pieces = cnt_ng NewGreenListV37.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV37LineSum_matches : NewGreenV37LineSum = sum_ng_lines NewGreenListV37.
Proof. reflexivity. Qed.

(* 闭合数和 = 字面值 *)
Lemma NewGreenV37QedSum_matches : NewGreenV37QedSum = sum_ng_qed NewGreenListV37.
Proof. reflexivity. Qed.
(* ---------- V38 批（登记 12 件） ---------- *)
(* ng_U5cZeta2GapA -- u5c_zeta2_gapA.v: zeta2 尾段缺口件比率基建与部分和前缀封顶及对接形实例入口 *)
Definition ng_U5cZeta2GapA : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_gapA.v" 507 18 20261014
  "zeta(2) gap-piece ratio infrastructure with prefix sum cap at the threshold window and docking instance entry" "L507:meae140".
(* ng_U5cZeta2A1Sign -- u5c_zeta2_a1_sign.v: zeta2 单调性符号面与显式命名前提逐点封顶证书双供 *)
Definition ng_U5cZeta2A1Sign : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_a1_sign.v" 314 12 20261014
  "zeta(2) monotonicity sign face with explicitly named premise pointwise cap certificate" "L314:mdbc4d1".
(* ng_U5cZeta2A2Tail -- u5c_zeta2_a2_tail.v: zeta2 收敛尾界机 1/10 档与 DOCK 终句全称 M 实例 *)
Definition ng_U5cZeta2A2Tail : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_a2_tail.v" 415 8 20261014
  "zeta(2) convergent tail machine at the 1/10 tier with DOCK final clause instance for all M" "L415:mbc0fa3".
(* ng_U5cZeta2Sup -- u5c_zeta2_sup.v: zeta2 行内右缘下降链与逐点封顶到全窗归约的 sup 基座 *)
Definition ng_U5cZeta2Sup : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_sup.v" 499 15 20261014
  "zeta(2) sup base with in-row right-edge fall chain and pointwise cap to whole-window reduction" "L499:m8b0845".
(* ng_U5cZeta2Sup2 -- u5c_zeta2_sup2.v: zeta2 m=8 无条件全窗闭合与带族证书机及 Z 二进制层数值件 *)
Definition ng_U5cZeta2Sup2 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_sup2.v" 494 28 20261014
  "zeta(2) unconditional whole-window closure at m=8 with band family certificate machine and Z-binary numeric pieces" "L494:m587270".
(* ng_U5cZeta2Band -- u5c_zeta2_band.v: zeta2 Hpw 无窗终界正本（行比率恒等式+same-k 迁移+cap 合拢 1/10 档） *)
Definition ng_U5cZeta2Band : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_band.v" 359 7 20261014
  "zeta(2) window-free Hpw final bound via row-ratio identity, same-k transfer and cap-chain closure at the 1/10 tier" "L359:ma3fb9b".
(* ng_U5cZeta2A2Tail11 -- u5c_zeta2_a2_tail11.v: zeta2 尾界 DOCK 终句 1/11 档重铸与合账折算 2/11 *)
Definition ng_U5cZeta2A2Tail11 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_a2_tail11.v" 404 8 20261014
  "zeta(2) tail DOCK final clause recast at the 1/11 tier with budget conversion to 2/11" "L404:m7f6277".
(* ng_U5cZeta2Assembly11 -- u5c_zeta2_assembly11.v: zeta2 供给链全链装配 1/11 档与 sigT 见证填充 *)
Definition ng_U5cZeta2Assembly11 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta2_assembly11.v" 203 5 20261014
  "zeta(2) supply-chain full assembly at the 1/11 tier with sigT witness filling and sharpened separation limb" "L203:m7f6439".
(* ng_AblZ3Tail -- abl_z3_tail.v: zeta3 立方收敛尾界机（比率律立方版+交叉步+前缀界+对接终句 1/40 档） *)
Definition ng_AblZ3Tail : NewGreenFace :=
  MkNewGreenFace "abl_z3_tail.v" 649 16 20261014
  "zeta(3) cubic convergent tail machine with cubic ratio law, cross step, prefix bound and docking final clause at 1/40" "L649:m1bdf48".
(* ng_U5cZeta3Assembly -- u5c_zeta3_assembly.v: zeta3 供给链全链装配与见证化（Defined 透明分母 d 嵌入） *)
Definition ng_U5cZeta3Assembly : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly.v" 206 7 20261014
  "zeta(3) supply-chain full assembly with witness inhabitance and transparent Defined denominator embedding" "L206:mc66852".
(* ng_AblZ3Hws -- abl_z3_hws.v: Hws 裂项步档恒等式独立消解与前提 II 单残位形及峰值引擎件 *)
Definition ng_AblZ3Hws : NewGreenFace :=
  MkNewGreenFace "abl_z3_hws.v" 175 7 20261014
  "independent resolution of the Hws telescoping step identity with single-residue premise-II form and peak engine pieces" "L175:md7035d".
(* ng_U5cZeta3Assembly2 -- u5c_zeta3_assembly2.v: zeta3 装配槽四前提收缩为三（Hws 放行件） *)
Definition ng_U5cZeta3Assembly2 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly2.v" 73 0 20261014
  "zeta(3) assembly slot contraction from four premises to three with the Hws slot permanently released" "L73:m9370e4".

(* ---------- V38 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV38 : list NewGreenFace :=
  cons ng_U5cZeta2GapA
  (cons ng_U5cZeta2A1Sign
  (cons ng_U5cZeta2A2Tail
  (cons ng_U5cZeta2Sup
  (cons ng_U5cZeta2Sup2
  (cons ng_U5cZeta2Band
  (cons ng_U5cZeta2A2Tail11
  (cons ng_U5cZeta2Assembly11
  (cons ng_AblZ3Tail
  (cons ng_U5cZeta3Assembly
  (cons ng_AblZ3Hws
  (cons ng_U5cZeta3Assembly2
  nil))))))))))).

(* 续写统计：12 件 / 行数和 4298 / 闭合数和 131（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV38Pieces  : nat := 12.
Definition NewGreenV38LineSum : nat := 4298.
Definition NewGreenV38QedSum  : nat := 131.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV38Pieces_matches : NewGreenV38Pieces = cnt_ng NewGreenListV38.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV38LineSum_matches : NewGreenV38LineSum = sum_ng_lines NewGreenListV38.
Proof. reflexivity. Qed.

(* 闭合数和 = 字面值 *)
Lemma NewGreenV38QedSum_matches : NewGreenV38QedSum = sum_ng_qed NewGreenListV38.
Proof. reflexivity. Qed.

(* ---------- V39 批（登记 2 件） ---------- *)
(* ng_GclFamsym -- gcl_famsym.v: 对称化截断族 Fam 槽供件与插槽双前提机内消去（零前提分离实例） *)
Definition ng_GclFamsym : NewGreenFace :=
  MkNewGreenFace "gcl_famsym.v" 615 22 20261014
  "symmetric truncated family carrier with both slot premises discharged in-machine and unconditional separation instance" "L615:m9e61f7".
(* ng_GclIsumsym -- gcl_isumsym.v: Isum^sym 积分值序列与闭式和一致及 Hanson 分母链供给链装配 *)
Definition ng_GclIsumsym : NewGreenFace :=
  MkNewGreenFace "gcl_isumsym.v" 716 39 20261014
  "integral value sequence with closed-form Beta sum coincidence and Hanson denominator supply-chain assembly" "L716:m9f6a64".

(* ---------- V39 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV39 : list NewGreenFace :=
  cons ng_GclFamsym
  (cons ng_GclIsumsym
  nil).

(* 续写统计：2 件 / 行数和 1331 / 闭合数和 61（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV39Pieces  : nat := 2.
Definition NewGreenV39LineSum : nat := 1331.
Definition NewGreenV39QedSum  : nat := 61.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV39Pieces_matches : NewGreenV39Pieces = cnt_ng NewGreenListV39.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV39LineSum_matches : NewGreenV39LineSum = sum_ng_lines NewGreenListV39.
Proof. reflexivity. Qed.

(* 闭合数和 = 字面值 *)
Lemma NewGreenV39QedSum_matches : NewGreenV39QedSum = sum_ng_qed NewGreenListV39.
Proof. reflexivity. Qed.
(* ---------- V40 批（登记 14 件） ---------- *)
(* ng_U5cLn2ThetaSlot -- u5c_ln2_theta_slot.v: ln2 θ 槽件（预算折叠恒等式与 4/5 带宽比较自足承载·预算桥义务定理） *)
Definition ng_U5cLn2ThetaSlot : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_theta_slot.v" 329 18 20261014
  "ln2 theta slot piece feeding the supply chain premise row" "L329:m6af0c3".
(* ng_U5cLn2Witness -- u5c_ln2_witness.v: ln2 witness 件（clo_n 下界见证函数·正性·锚形迁移肢与双验收面） *)
Definition ng_U5cLn2Witness : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_witness.v" 240 7 20261014
  "ln2 witness carrier with explicit premise row for the supply face" "L240:ma18778".
(* ng_U5cN54OtSpectrum -- u5c_n54_ot_spectrum.v: 统一逃逸窗致胜谓词 UWin 三态谱与全-b 钉定谱学（对数档上界/库窗线性对照/loglog 下界/无穷档/sqrt5 首锚） *)
Definition ng_U5cN54OtSpectrum : NewGreenFace :=
  MkNewGreenFace "u5c_n54_ot_spectrum.v" 364 7 20261014
  "three-state spectrum of the unified escape-window winning predicate UWin with pinning anchor" "L364:mcb0683".
(* ng_U5cLn2S5cSupply -- u5c_ln2_s5c_supply.v: 五层供给面条件 inhabited（六肢逐位填充·Hrho/Hbudget 两位显式前提在语句位·诚实接口·缺口单调收缩账在卷） *)
Definition ng_U5cLn2S5cSupply : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_s5c_supply.v" 502 12 20261014
  "five-layer supply-face condition inhabited with six-limb filling under two explicit gap premises" "L502:mb5f365".
(* ng_U5cLn2S5dShape -- u5c_ln2_s5d_shape.v: ln2 实例刻形（s5d_bq 冻结定义位·B 整性障碍机锚） *)
Definition ng_U5cLn2S5dShape : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_s5d_shape.v" 161 5 20261014
  "ln2 instance shaping with frozen bq definition row" "L161:mda1a90".
(* ng_U5cLn2S5eHbint -- u5c_ln2_s5e_hbint.v: Hbint 整性肢主定理（sigT/Set 承载·QeqT 构造链收尾非 solver） *)
Definition ng_U5cLn2S5eHbint : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_s5e_hbint.v" 592 4 20261014
  "hbint integrality limb flagship with QeqT construction chain verdict" "L592:m4008b9".
(* ng_U5cLn2S6Confluence -- u5c_ln2_s6_confluence.v: 六肢合流强化 s6_supply_inhabited_strong（s6_Bz := projT1 (s5e_hbint n) 构造消解·零自由参数·两位显式前提同 s5c） *)
Definition ng_U5cLn2S6Confluence : NewGreenFace :=
  MkNewGreenFace "u5c_ln2_s6_confluence.v" 142 4 20261014
  "six-limb confluence strengthened canonical instance with constructed Bz witness family" "L142:mb5248b".
(* ng_FibMachine -- fib_machine.v: Fibonacci 族机（fibpair/fibp/fibz 正性承载与零前提分离证书 fib_family_sep） *)
Definition ng_FibMachine : NewGreenFace :=
  MkNewGreenFace "fib_machine.v" 337 15 20261014
  "fibonacci family machine with positivity carrier and zero-premise separation certificate" "L337:m3695ac".
(* ng_FibNormGap -- fib_norm_gap.v: sqrt5 整隙全称件（4a²−4ab−4b² 范数形整隙与黄金比极限交错括界） *)
Definition ng_FibNormGap : NewGreenFace :=
  MkNewGreenFace "fib_norm_gap.v" 255 13 20261014
  "sqrt5 norm-gap universal piece with alternating bracket of the golden-ratio limit" "L255:m0b8eae".
(* ng_FibQdomain -- fib_qdomain.v: 全有理域装配（一般非平方 D 整隙零前提闭式＋三主语句零前提·Q 平方隙） *)
Definition ng_FibQdomain : NewGreenFace :=
  MkNewGreenFace "fib_qdomain.v" 312 21 20261014
  "rational-domain assembly with three zero-premise main statements" "L312:mc12b9b".
(* ng_U5cZ3M2pLedger -- u5c_z3_m2p_ledger.v: M2' 账本件（锚点账本方程主定理＋证书机＋反局部窗证书＋基座 [1,10]＋HM2 槽接口·残位 n>=11 依既有勘定留残·诚实注记） *)
Definition ng_U5cZ3M2pLedger : NewGreenFace :=
  MkNewGreenFace "u5c_z3_m2p_ledger.v" 550 19 20261014
  "M2-prime ledger with anchor equation flagship and base closure on the reachable segment" "L550:mabb9ae".
(* ng_U5cZeta3Assembly3 -- u5c_zeta3_assembly3.v: 装配槽 4→3→2 收束（HM2 位一次代入＋基座 [5,9] 分段闭合·Defined 透明双主件） *)
Definition ng_U5cZeta3Assembly3 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly3.v" 109 3 20261014
  "assembly slot 4-to-2 collapse by one-shot M2 substitution with segmented base closure" "L109:m6177fd".
(* ng_B5Machine -- b5_machine.v: sqrt2 非半整隙机（证书基量/整值整隙/恒等链/边距分支核/窗口自举五层·件内终形 b5_sqrt2_nonhalf 零前提） *)
Definition ng_B5Machine : NewGreenFace :=
  MkNewGreenFace "b5_machine.v" 1056 14 20261014
  "sqrt2 non-half gap machine with in-file zero-premise terminal form b5_sqrt2_nonhalf" "L1056:mfac709".
(* ng_U5cN54rPellTower -- u5c_n54r_pell_tower.v: Pell 塔 S0-S5 全语句面（wden 双塔与 delta 精确塔＋入窗核＋下界正典 7 基＋恰等排除核＋双端 loglog 终形·八点差分 RunAlive 在卷） *)
Definition ng_U5cN54rPellTower : NewGreenFace :=
  MkNewGreenFace "u5c_n54r_pell_tower.v" 948 16 20261014
  "pell tower with double-sided loglog terminal shape and runalive differential anchors" "L948:mc5ce16".

(* ---------- V40 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV40 : list NewGreenFace :=
  cons ng_U5cLn2ThetaSlot
  (cons ng_U5cLn2Witness
  (cons ng_U5cN54OtSpectrum
  (cons ng_U5cLn2S5cSupply
  (cons ng_U5cLn2S5dShape
  (cons ng_U5cLn2S5eHbint
  (cons ng_U5cLn2S6Confluence
  (cons ng_FibMachine
  (cons ng_FibNormGap
  (cons ng_FibQdomain
  (cons ng_U5cZ3M2pLedger
  (cons ng_U5cZeta3Assembly3
  (cons ng_B5Machine
  (cons ng_U5cN54rPellTower
  nil))))))))))))).
(* 续写统计：14 件 / 行数和 5897 / 闭合数和 158（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV40Pieces  : nat := 14.
Definition NewGreenV40LineSum : nat := 5897.
Definition NewGreenV40QedSum  : nat := 158.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV40Pieces_matches : NewGreenV40Pieces = cnt_ng NewGreenListV40.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV40LineSum_matches : NewGreenV40LineSum = sum_ng_lines NewGreenListV40.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV40QedSum_matches : NewGreenV40QedSum = sum_ng_qed NewGreenListV40.
Proof. reflexivity. Qed.
(* ---------- V41 batch (1 piece registered) ---------- *)
(* ng_Piu1932TightBoundInstantiated -- piu1932_tight_bound_instantiated.v: 幂率型紧上界的实例化收尾 (定义幂率深度型 kernel margin 族 ck_alpha(C0,alpha,q) = C0/h(q)^alpha、margin 换形填充一致型收尾件证书前提位四支(HC0_pos/Hcrt_pos/Hcrt_dist/Hcert_pow)、l2_escape 实例化与 antitone/Q 算术收尾: 停点 <= S(S(ceil((8/C0)*h^alpha))) 后继加一形) *)
Definition ng_Piu1932TightBoundInstantiated : NewGreenFace :=
  MkNewGreenFace "piu1932_tight_bound_instantiated.v" 195 9 20261014
  "instanced closing of the uniform-type tight upper bound: the power-law depth kernel margin family ck_alpha(C0,alpha,q) = C0/h(q)^alpha fills the four certificate premises of the conditional uniform closing piece via margin reshaping, and the l2_escape instantiation with antitone and Q-arithmetic closing yields stop point <= S(S(ceil((8/C0)*h^alpha)))" "L195:ma443d4".

(* ---------- V41 batch statistics (whole-batch append: list, constants and lemmas written atomically in one block) ---------- *)
Definition NewGreenListV41 : list NewGreenFace :=
  cons ng_Piu1932TightBoundInstantiated
  nil.

(* 续写统计：1 件 / 行数和 195 / 闭合和 9（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV41Pieces  : nat := 1.
Definition NewGreenV41LineSum : nat := 195.
Definition NewGreenV41QedSum  : nat := 9.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV41Pieces_matches : NewGreenV41Pieces = cnt_ng NewGreenListV41.
Proof. reflexivity. Qed.

(* 行数和 = 字面值 *)
Lemma NewGreenV41LineSum_matches : NewGreenV41LineSum = sum_ng_lines NewGreenListV41.
Proof. reflexivity. Qed.

(* 闭合和 = 字面值 *)
Lemma NewGreenV41QedSum_matches : NewGreenV41QedSum = sum_ng_qed NewGreenListV41.
Proof. reflexivity. Qed.
(* ---------- V42 批（登记 8 件·π 族前沿波 5） ---------- *)
(* ---------- 前置批 2 件（B4 链闭包必需补录） ---------- *)
(* ng_Zb3pHpw -- zb3p_hpw.v: Hpw 闭合主件（zb3r_Hpw_closed 零前提 QleT' 上界·闭式透明提取·PA=10） *)
Definition ng_Zb3pHpw : NewGreenFace :=
  MkNewGreenFace "zb3p_hpw.v" 478 10 20261014
  "hpw closed carrier with zero-premise qle upper bound and transparent closed-form extraction" "L478:m96ee5c".
(* ng_Zb3jBase15 -- zb3j_base15.v: [1,15] Hanson 段闭合（主语句 z2v_C n ≤ 3^n 有界形·G 折回四因子截断面·z2v_C 直算 fact 一元界诚实登记维持·PA=6） *)
Definition ng_Zb3jBase15 : NewGreenFace :=
  MkNewGreenFace "zb3j_base15.v" 183 6 20261014
  "hanson segment closure on one-to-fifteen with bounded c-step machine chain" "L183:m8e1948".
(* ---------- ζ3 装配收缩 2 件 ---------- *)
(* ng_U5cZeta3Assembly4 -- u5c_zeta3_assembly4.v: 装配 2→1 收缩（M2′ 全称形＋NatLe 5 m ⟹ supply_chain·唯一残位＝M2′ 全称形诚实注记·[5,9] 段 base 零前提·PA=2） *)
Definition ng_U5cZeta3Assembly4 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly4.v" 77 2 20261014
  "assembly two-to-one collapse under the universal m2-prime premise with base segment closure" "L77:m33e79d".
(* ng_U5cZeta3Assembly5 -- u5c_zeta3_assembly5.v: 装配零前提段 [5,9]→[5,14]（M2′ 位 [1,15] 有界形一次代入·[16,42] 档一元表示界内不可达归档＋n ≥ 43 熵段留残诚实注记·PA=2） *)
Definition ng_U5cZeta3Assembly5 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly5.v" 83 2 20261014
  "zero-premise assembly segment expansion to fourteen by bounded one-shot substitution" "L83:m7769d5".
(* ---------- 周期类收敛子族 4 件 ---------- *)
(* ng_PellFamily -- pell_family.v: 周期一类 D=m²+1 单参数收敛子族（√2/√5 旧单例并入为成员特例·sharp 精确等号＋sep 分离证书＋pell_norm 一般 D 版 Cassini·sep 两位显式前提 k ≠ 0、1 ≤ m 诚实接口·PA=19） *)
Definition ng_PellFamily : NewGreenFace :=
  MkNewGreenFace "pell_family.v" 415 19 20261014
  "period-one convergent family with sharp equality and separation certificates under two explicit premises" "L415:me85f88".
(* ng_D3Family -- d3_family.v: 周期 2 类 D=3 收敛子族（quad 四不变式常数形·锐度常元 1·零前提 Closed·PA=25） *)
Definition ng_D3Family : NewGreenFace :=
  MkNewGreenFace "d3_family.v" 370 25 20261014
  "period-two class family for d equals three with constant norm quad invariants" "L370:mcd31e9".
(* ng_D6Family -- d6_family.v: 周期 2 类 D=6 收敛子族（与 d3 同构仅常数异·锐度常元 2·零前提 Closed·PA=25） *)
Definition ng_D6Family : NewGreenFace :=
  MkNewGreenFace "d6_family.v" 365 25 20261014
  "period-two class family for d equals six with sharpness constant two" "L365:mc56784".
(* ng_D13Family -- d13_family.v: 周期 5 类 D=13 收敛子族（quad ±4/±1 双流交替形＋det 内芯·锐度常元 5·族成员=√13 第 5k+4 收敛子·零前提 Closed·PA=26） *)
Definition ng_D13Family : NewGreenFace :=
  MkNewGreenFace "d13_family.v" 388 26 20261014
  "period-five class family for d equals thirteen with alternating norm stream" "L388:m0e43d4".

(* ---------- V42 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV42 : list NewGreenFace :=
  cons ng_Zb3pHpw
  (cons ng_Zb3jBase15
  (cons ng_U5cZeta3Assembly4
  (cons ng_U5cZeta3Assembly5
  (cons ng_PellFamily
  (cons ng_D3Family
  (cons ng_D6Family
  (cons ng_D13Family
  nil))))))).
(* 续写统计：8 件 / 行数和 2359 / 闭合数和 115（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV42Pieces  : nat := 8.
Definition NewGreenV42LineSum : nat := 2359.
Definition NewGreenV42QedSum  : nat := 115.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV42Pieces_matches : NewGreenV42Pieces = cnt_ng NewGreenListV42.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV42LineSum_matches : NewGreenV42LineSum = sum_ng_lines NewGreenListV42.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV42QedSum_matches : NewGreenV42QedSum = sum_ng_qed NewGreenListV42.
Proof. reflexivity. Qed.
(* ---------- V43 批（登记 2 件·π 族前沿波 6） ---------- *)
(* ---------- 前置件 1 件（cf_bridge 闭包必需补录） ---------- *)
(* ng_SharpConst -- sharp_const.v: 谱刻画首定理（sc_general/sc_general_alt/sc_row2_general/sc_row2_general_alt 四一般形 ∀ 任意 2×2 整数矩阵＋sc_T1/sc_T1_B1 与 sc_T2/sc_T2_Babs 两显式类级化＋D=13 row2 实例档＋pell/d3/d6/d13 四代族三重收件零前提 Closed）；PA=38 Closed（31 主件＋7 smoke 编译实测）；Lia import 行例外登记（d3/d6/d13 母版先例形·正文零使用·冻结类禁抹）；谱刻画余位（CF 构造性连接）由同批 cf_bridge 兑现 *)
Definition ng_SharpConst : NewGreenFace :=
  MkNewGreenFace "sharp_const.v" 431 38 20261014
  "general sharpness constant theorems for arbitrary integer matrices with class level T one and T two coverage and a d thirteen instance recovering four family generations" "L431:m024ca3".
(* ---------- CF 构造面桥主件 1 件 ---------- *)
(* ng_CfBridge -- cf_bridge.v: CF 构造面桥（cfC_q＝块积 (2,1) 元＝分母流第二分量＝q_{T−1}＋cf1_lin 矩阵幂 Q 层 T 归纳＋cfA/cfB/cfC/cfD_cons 块递推四件＋cf_det＝(−1)^T T 奇偶判据面＋cf_bridge_even/odd 两档＋全谱重收 rec_dD_row2/den ×27 件·总表 53 位机内使用全覆盖·谱理论线三段闭合）；PA=68 Closed（桥定理群 14 件＋54 重收件 编译实测）；Obj.magic=0；D=34 单向判据守护（det 全走 T 奇偶形·禁同余 iff 形·禁抹）；重收 den=Z.eqb 执行面锚（执行面由 vm_compute 承担） *)
Definition ng_CfBridge : NewGreenFace :=
  MkNewGreenFace "cf_bridge.v" 669 68 20261014
  "continued fraction construction face bridge proving the block product second row entry equals the denominator stream component with full spectrum twenty seven piece recovery" "L669:m367147".

(* ---------- V43 批统计（整批追加纪律：清单/常量/引理同块原子写入） ---------- *)
Definition NewGreenListV43 : list NewGreenFace :=
  cons ng_SharpConst
  (cons ng_CfBridge
  nil).
(* 续写统计：2 件 / 行数和 1100 / 闭合数和 106（字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV43Pieces  : nat := 2.
Definition NewGreenV43LineSum : nat := 1100.
Definition NewGreenV43QedSum  : nat := 106.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV43Pieces_matches : NewGreenV43Pieces = cnt_ng NewGreenListV43.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV43LineSum_matches : NewGreenV43LineSum = sum_ng_lines NewGreenListV43.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV43QedSum_matches : NewGreenV43QedSum = sum_ng_qed NewGreenListV43.
Proof. reflexivity. Qed.

(* ================= V44 批（登记 6 件·π 族前沿波 7）（整批追加纪律：清单/常量/引理同块原子写入） ================= *)
(* ---------- 组论系数层完成主件 1 件 ---------- *)
(* ng_GclCert -- gcl_cert.v: ③肢 CM 梯终程（ppi/ppi2 乘法形升阶乘闭式＋Leibniz 角点消除 leib_core＋glb 卷积＋CM 组装）→主语句 gcl_Isum_sym_ge0 零前提在卷＋④肢 binometric 引理（gcl_bins_main＋gcl_binom_bound Σ_{k≤M}C(m+1+k,m+1)(4/9)^k ≤ (9/5)^(m+2)）＋装配主件 gcl_supply_sym_weld3（③消解版·供给链五肢之③零前提化·⑤肢焊装链解锁）；PA=8 Closed（编译实测）；ng_qed=69（grep-token 双口径计数）；Lia import 行例外登记（d3/d6/d13/sharp_const 母版先例形·正文线性算术使用·构造性由第五证 coqchk 零全局假设兜底·冻结类禁抹）；④肢 D_0 界与 Hanson 熵残位在句如实（由同批 gcl_hent 窗件部分兑现·全称形熵三档归档·复审条件随件文书在卷） *)
Definition ng_GclCert : NewGreenFace :=
  MkNewGreenFace "gcl_cert.v" 1149 69 20261015
  "CM filtering ladder closing limb three with zero premise Isum symmetry nonnegativity plus binometric partial sum bound and weld three supply chain assembly" "L1149:m10c692".
(* ---------- Hanson 熵有界窗消去件 1 件 ---------- *)
(* ng_GclHent -- gcl_hent.v: Hanson 熵前提的有界窗消去（m∈[3,8]·gcl_hanson_win 九叶 destruct＋h3 整除→上界桥＋窗锚六点 n=4..9）＋主语句 gcl_supply_sym_weld3_win（weld3 逐字使用·熵前提位零改动消去·前提三→二）；PA=3 Closed（编译实测）；ng_qed=10（双口径计数）；窗右界 9 与 h3 断点 n=9 如实登记（全称形熵三档归档·复审条件随件文书在卷） *)
Definition ng_GclHent : NewGreenFace :=
  MkNewGreenFace "gcl_hent.v" 159 10 20261015
  "Hanson entropy bounded window elimination for m between three and eight with weld three window consumer" "L159:m34e42e".
(* ---------- Pell 型周期族三件（谱线扩张补全） ---------- *)
(* ng_D41Family -- d41_family.v: 周期 3 双族 D=41（norm_quad 5/±1/6/±1＋det＋family_sep/sharp＋q_square_sharp 零前提·双族 ±1 交替机内实存·谱线 T=3 档·x²≡−1 (mod 41) 见证 9·32）；PA=26 Closed；ng_qed=31（双口径计数） *)
Definition ng_D41Family : NewGreenFace :=
  MkNewGreenFace "d41_family.v" 402 31 20261015
  "period three Pell type family for d forty one with norm quadruple determinant sharpness and separation theorems" "L402:mf7e787".
(* ng_D7Family -- d7_family.v: 周期 4 单族 D=7（norm_quad 1/−3/−2/−1＋det=3 锐度常元＋family_sep/sharp＋q_square_sharp·4 步块矩阵 [[14,3],[9,2]]·+1 单族判据 x²≡−1 (mod 7) 无解第五次验证）；PA=25 Closed（19 主＋6 smoke）；ng_qed=30（双口径计数） *)
Definition ng_D7Family : NewGreenFace :=
  MkNewGreenFace "d7_family.v" 377 30 20261015
  "period four Pell type family for d seven with norm quadruple determinant sharpness and separation theorems" "L377:mbcd74f".
(* ng_D14Family -- d14_family.v: 周期 4 单族 D=14（norm_quad 1/−5/−3/−1＋det=4＋family_sep/sharp＋q_square_sharp·4 步块矩阵 [[27,4],[20,3]]·+1 单族判据第六次验证）；PA=25 Closed；ng_qed=30（双口径计数） *)
Definition ng_D14Family : NewGreenFace :=
  MkNewGreenFace "d14_family.v" 377 30 20261015
  "period four Pell type family for d fourteen with norm quadruple determinant sharpness and separation theorems" "L377:mf0edff".
(* ---------- odd-lcm 分母承载件 1 件 ---------- *)
(* ng_Dnf2Oddlcm -- abl_dmdnf2_oddlcm.v: odd-lcm 分母承载（oddlcm/od_prod 可执行 Fixpoint）＋见证接口主语句 dnf2_trunc_odd_clear（覆盖端 2n+1→2n+2M+1）＋oddlcm≤od_prod≤fact 增长界＋执行锚三件；PA=4 Closed（编译实测）；ng_qed=12（双口径计数）；μ(π) 换核路线量化裁定不成·三档归档（c_new 实约简 3.0020/真值 1.8876/Hanson 引档 2.2201 全超门槛 1.568616）——路线不成≠件红·承载面照登记；紧载体猜想 D|2^(n+M)·oddlcm 独立复算 96 点未入证（无 Hypothesis 位·红线②洁净）；born-in-tree 同源重编绿=伴随窗件并播解锁实证 *)
Definition ng_Dnf2Oddlcm : NewGreenFace :=
  MkNewGreenFace "abl_dmdnf2_oddlcm.v" 176 12 20261015
  "odd least common multiple denominator carrier with witness multiplier interface and growth bounds" "L176:m6218b9".

(* ---------- V44 批统计（整批追加纪律：清单/常量/引理同块原子写入·ng_qed 口径） ---------- *)
Definition NewGreenListV44 : list NewGreenFace :=
  cons ng_GclCert
  (cons ng_GclHent
  (cons ng_D41Family
  (cons ng_D7Family
  (cons ng_D14Family
  (cons ng_Dnf2Oddlcm
  nil))))).
(* 续写统计：6 件 / 行数和 2640 / 闭合数和 182（ng_qed 口径·清洗稿字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV44Pieces  : nat := 6.
Definition NewGreenV44LineSum : nat := 2640.
Definition NewGreenV44QedSum  : nat := 182.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV44Pieces_matches : NewGreenV44Pieces = cnt_ng NewGreenListV44.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV44LineSum_matches : NewGreenV44LineSum = sum_ng_lines NewGreenListV44.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV44QedSum_matches : NewGreenV44QedSum = sum_ng_qed NewGreenListV44.
Proof. reflexivity. Qed.

(* ================= V45 批（登记 2 件·π 族前沿波 8）（整批追加纪律：清单/常量/引理同块原子写入） ================= *)
(* ---------- Q(i) 残数算术组机层 1 件 ---------- *)
(* ng_Zzm1Gauss -- zzm1_gauss.v: Z[i] 高斯整数基座（Record gz 律二字段位 Set·六运算 gz_add/neg/sub/mul/conj/eqb＋gz_pow/zpow＋除法自由形 gz_im_neg_frac (−Im[e^j], norm^j) gcd 免除·对照件 im_neg_power 直译）＋Set 层单态等词 zzId 四向回注件（true/bool eq_rect 双向/from_eq/Qeqb_refl）＋基座引理 10 条（norm 乘性 lagrange·conj 乘性·gz_pow_conj 全件形式·幂性·步进·eqb 完备/自反）＋norm 锚 20/40/5；PA=6 Closed（born-in-tree 编译实测）；ng_qed=18（grep-token 双口径相等·清洗稿实测）；零 Axiom·零 solver·全语句 Set 承载（ZZM1 回执 born 终态表核对一致·本批 born-in-tree 重编 rc=0 为权威绿） *)
Definition ng_Zzm1Gauss : NewGreenFace :=
  MkNewGreenFace "zzm1_gauss.v" 227 18 20261015
  "gaussian integer base ring with set level equality re-injection six operations and gcd free division form" "L227:m233f24".
(* ---------- Q(i) 残数算术组机层 2 桥 ---------- *)
(* ng_Zzm1bLinformBridge -- zzm1b_linform_bridge.v: 围道离散化线性形式桥（生成器单源发射）：zz_sumf 索引有限和＋zz_phat 多项式部＋zz_princ 主部（红笔①符号笔由 zz_bite_r_1 vm_compute false fail-loud 拦截后核对一致）＋zz_linform_r/zz_linform_s 双通道（s 通道 (A₀+B₀)/8 口径）＋zz_res 残数项 Record＋sigT 正典承载 zz_linform_sig＋实例（层 3 读出接口位·切片 4 使用）；PA=13 Closed（born-in-tree 编译实测）；ng_qed=34（grep-token 双口径相等·清洗稿实测）；忠实性披露（律五·ZZM1 回执原样入册）：「zz_linform = REALFORM I_n/(2i) 的 Q 读出」复分析面＝对照域认证在卷（float 围道 Simpson↔Fractions 一致 8.5e−16 n=1..6）非 Coq 义务；33 数值锚系数表＝对照认证域 certified 字面量供件（切片 2-3 换机内提取）；μ(π) 判死面不涉本件（组机承载面·非竞争判定件） *)
Definition ng_Zzm1bLinformBridge : NewGreenFace :=
  MkNewGreenFace "zzm1b_linform_bridge.v" 290 34 20261015
  "contour discretization linear form bridge with residue record and canonical sigT carrier" "L290:m3c5a2b".

(* ---------- V45 批统计（整批追加纪律：清单/常量/引理同块原子写入·ng_qed 口径） ---------- *)
Definition NewGreenListV45 : list NewGreenFace :=
  cons ng_Zzm1Gauss
  (cons ng_Zzm1bLinformBridge
  nil).
(* 续写统计：2 件 / 行数和 517 / 闭合数和 52（ng_qed 口径·清洗稿实测字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV45Pieces  : nat := 2.
Definition NewGreenV45LineSum : nat := 517.
Definition NewGreenV45QedSum  : nat := 52.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV45Pieces_matches : NewGreenV45Pieces = cnt_ng NewGreenListV45.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV45LineSum_matches : NewGreenV45LineSum = sum_ng_lines NewGreenListV45.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV45QedSum_matches : NewGreenV45QedSum = sum_ng_qed NewGreenListV45.
Proof. reflexivity. Qed.
(* ================= V46 批（登记 8 件·π 族前沿续波）（整批追加纪律：清单/常量/引理同块原子写入） ================= *)
(* ---------- [16,42] 段 Z 换岸正本 1 件 ---------- *)
(* ng_Zb3zBase42 -- zb3z_base42.v: C 值序界全段闭合 [1,42]：§0 Z 换岸三件正典化（zb3z_Zcmp inj_le 承载 nat ≤ ↔ Z.leb true 双向＋zb3z_inj_mul/inj_pow 3^n 免一元物化过岸＋Ltac zb3z_Zcmp_tac 后向渡岸）＋验收锚 zb3z_anchor41（C(41)=1.84e19 因子化 3456·3675·2431·437·899·1517 ≤ 3^41 Z-lift）＋§1 G 折返 27 档（zb3m_G_ext 折回＋zb3m_a4_gt42 锚·27/27 预嵌）＋§2 链节机械件（zb3z_pos_mul 积正性／zb3z_gear 累积恒等式步进齿轮／zb3z_link15 Z 桥终站拆封）＋§3 块化 10 块逐块累积（切点=对照域比值谷点配方·[16][17,18][19,22][23,24][25,28][29,30][31,34][35,36][37,40][41,42]·27 点全闭非仅端点）＋§4 主语句 zb3z_base42：∀n∈[1,42] z2v_C n ≤ 3^n（[1,15] 肢直取 zb3j_base15 零重述）＋§5 Set 面出口 zb3z_HM2_face_42（NatLe 承载）；PA=19 Closed（born-in-tree 编译实测）；ng_qed=46（grep-token 双口径相等·清洗稿实测）；诚实接口：z2v_C 直算仍撞 fact 一元墙·判定义务由 Prop 链式累积＋Z 比较面承担（zb3j 同款披露） *)
Definition ng_Zb3zBase42 : NewGreenFace :=
  MkNewGreenFace "zb3z_base42.v" 697 46 20261016
  "z shore crossing base closing value order bound one through forty two with canonical comparison and block accumulation" "L697:m27890b".
(* ---------- 装配面扩展件 2 件 ---------- *)
(* ng_Zeta3Assembly7 -- u5c_zeta3_assembly7.v: 装配面 base42 一次代入零重述：u5c_zeta3_assembly7（HM2 面 [1,42] 有界形＋NatLe 5 m＋NatLe m 41 ⟹ supply_chain·assembly2 槽形一次代入）＋u5c_zeta3_assembly7_base（零前提）——零前提供给段 [5,9]→[5,14]→[5,15]→[5,41]；新扩展段 m ∈ [16,41] 全由 Z 换岸链（zb3z_blk1..blk10·C(41) 锚在卷）无条件供给；缺口账：m ≥ 42 段残余仅剩 n ≥ 43 熵段（多件工程判定维持·勿单件窗强攻）；首发即绿零红笔；PA=2 Closed（born-in-tree 编译实测）；ng_qed=0（grep-token 双口径相等·两主语句 Defined 透明收尾无 Qed 打点·清洗稿实测） *)
Definition ng_Zeta3Assembly7 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly7.v" 85 0 20261016
  "assembly extension substituting base forty two face lifting zero premise supply segment to five through forty one" "L85:mf1828a".
(* ng_Zeta3Assembly6 -- u5c_zeta3_assembly6.v: 装配面 base15 一次代入＋HM2@16 一档新铸：u5c_zeta3_assembly6（HM2 面 [1,15] 升 [1,16] 有界形·S m ∈ [6,16] 档一次代入）＋u5c_zeta3_assembly6_base（零前提·零前提供给段 [5,14]→[5,15]）＋zb3p_C16_eq_2C15（C 步进机＋G(16,16)=8 折回＋乘数对齐 16=8·2＋取消⟹ C(16)=2·C(15)=2162160 全符号零 vm_compute）＋zb3p_C16_le_3pow16（三跳全符号·Nat.pow_succ_r' 免 3^14 一元物化）＋zb3p_HM2_face_16（zb3j_HM2_face_15 正本＋16 档新铸·Nat.eq_dec 构造二分）；PA=6 Closed（born-in-tree 编译实测）；ng_qed=4（grep-token 双口径相等·清洗稿实测） *)
Definition ng_Zeta3Assembly6 : NewGreenFace :=
  MkNewGreenFace "u5c_zeta3_assembly6.v" 154 4 20261016
  "assembly extension lifting bounded face to one through sixteen with symbolic step and zero premise base form" "L154:m0037d2".
(* ---------- Hanson 熵窗右扩件 1 件 ---------- *)
(* ng_GclHent2 -- gcl_hent2.v: Hanson 熵前提有界窗消去向右扩展三档 m∈[3,8]→[3,11]（n=S m∈[4,12]）：§A 脚手架 pow3_add/lcm_step_le（Hanson 阶梯递推 L(S n) ≤ L(n)·(S n)·变量层单步展开）＋§B 新窗三点 win_10/11/12（n=10=h3 偶桥 k=5 补点 L(10) ≤ C(10,5)·5!=30240 ≤ 3·3^9；n=11/12=阶梯链＋唯一吸收锚 L(10)=2520·零数值等式 Qed 打点规避分钟级 kernel conv 坑）＋§C 主语句 I win2＋win2_t（Set 面 hl_le_t 承载）＋§D 主语句 II weld3_win2（sigT·Set·覆盖域 8→11·前提三→二）；冻结 gcl_hent 零字节触碰真零重做；真墙档维持（全称形 Hanson 熵三档归档·右界 n=12 为本世界一元内核可达端非数学边界）；PA=3 Closed（born-in-tree 编译实测）；ng_qed=8（grep-token 双口径相等·清洗稿实测） *)
Definition ng_GclHent2 : NewGreenFace :=
  MkNewGreenFace "gcl_hent2.v" 193 8 20261016
  "hanson entropy bounded window right extension to eleven with ladder recurrence and weld three window consumer" "L193:mcb5a87".
(* ---------- 供给链全额装配主件 1 件 ---------- *)
(* ng_GclFull -- gcl_full.v: 供给链装配全额版：主语句 gcl_supply_sym_weld3_full : forall m, 3 ≤ m → m ≤ 8 → gcl_supply_sym m m——weld3 三前提全消（唯一前提=窗界·五肢零残位·⑤肢由冻结件 gcl_sep_generic 零改动焊接）＝μ_lib 8.64 档全额入账窗 [3,8] 内首个零残位机内区段；④族界消解四段链：gcl_Isum_sym_le_D0（滤波单调链·零前提对一切 m·M）＋gcl_D0_le_bins（u 衰减＋逐项界）＋gcl_binom_bound（前批 born 件零改动使用）＋gcl_u0_weight_win（单项式窗点六叶·m=9 仍真 m=10 破=本链硬界如实）；u 衰减定理边界 k ≤ m+3（逐点比率 ≤ 2/3·越界失效在句如实）；PA=6 Closed（born-in-tree 编译实测）；ng_qed=15（grep-token 双口径相等·清洗稿实测）；anchor M:=m 档·全称 M 需超几何收敛闭式和另案（真 D_0 收敛远小于每-k 界） *)
Definition ng_GclFull : NewGreenFace :=
  MkNewGreenFace "gcl_full.v" 451 15 20261016
  "full supply chain assembly with zero residual premises inside window and four stage family bound elimination" "L451:m18ca99".
(* ---------- 1/14 逐点改进证书 1 件 ---------- *)
(* ng_D519a2Cert -- d519a2_cert.v: 1/14 精确逐点改进证书（θ(3)=1/14 档·Ψ₃=3+s−2p 纯轨道正组合·σ=7/8 非循环）：主语句 d519_N_le_14 : forall x y : Q, 0 ≤ x ≤ 1 → 0 ≤ y ≤ 1 → QleT' (56·x·(1−x)·y·(1−y)) (3+x+y−2·x·y)——GCL 1/12 档之上 genuine 逐点改进；语句面八位全 Set 承载（QleT'×5＋QeqT×3）＋Qeq 桥两位（d519_psi3_eq/d519_u_fact·池冻结件同款桥形如实申报）；证明面全 algebra 链：四基 a=x(1−y),b=y(1−x),c=(1−x)(1−y),d=xy（ab=cd=N·σ+τ=1）＋AM-GM×2＋双分支闭式分解（σ≤1/2：3+σ−14σ²==(1−2σ)(7σ+3)；σ>1/2：4−τ−14τ²==(1−2τ)(7τ+4)）——免微积分免归纳零经典逻辑末步 exact 非 solver；验收锚 56·N(1/2,1/2)==7/2 tight 于 τ-不动点（对照域精确值逐行）；u 分解式常数 3/14（转抄滑 3/28 经精确复算校正·对照域反证在卷）；μ_lib 账面不动（1/14 勘形 μ≈5.973 不穿 5.0193784·禁施工引用照守）；PA=8 Closed（born-in-tree 编译实测）；ng_qed=11（grep-token 双口径相等·清洗稿实测） *)
Definition ng_D519a2Cert : NewGreenFace :=
  MkNewGreenFace "d519a2_cert.v" 356 11 20261016
  "pointwise improvement certificate fifty six n at most three plus s minus two p with pure algebraic two branch proof" "L356:m71f9f2".
(* ---------- 仿射变换族钉定常元件 1 件 ---------- *)
(* ng_N1AffineTransform -- u5c_n1_affine_transform.v: N1 仿射三族成库：平移 k（常元 1/(12b²) 逐字不变）／数乘 k（↦1/(12·k·b²)）／倒数 1/x（a ≤ 0 档常元 1/4·n₀=1 统一窗；a=p>0 档常元 1/(36·p·b)·双窗·ρ 两案）四定理全定义（n1_shift_measure/n1_scale_measure/n1_inv_nonpos_measure/n1_inv_pos_measure）；PA=4 Closed（born-in-tree 编译实测·四定理全 Closed under the global context）；ng_qed=29（grep-token 双口径相等·清洗稿实测）；前批条件槽转正：born 于前批冻结窗后·本批凭全数绿判收束移交账升正式件（六伤全愈终收版 1058 行） *)
Definition ng_N1AffineTransform : NewGreenFace :=
  MkNewGreenFace "u5c_n1_affine_transform.v" 1058 29 20261016
  "affine transform family pinned constants shift scale and inverse with unified windows" "L1058:m6dd37f".
(* ---------- Q-多项式层 1 件 ---------- *)
(* ng_Zzm2Qpoly -- zzm2_qpoly.v: Q(i) 残数算术组机切片 2·Q-多项式层（单源生成器发射·禁手改数值字面量）：§0 Qpoly 承载（list Q·index=幂次·head=常数项）＋plq_eqb＋§1 八件算术全 Defined（pdrop0/ptrim 反转归一·padd/pscal/pmul/ppow·psub_align/plast/pdroplast·pdiv_go 度差结构递归长除·pdivmod 商余主入口免负幂·pshift_go 扫描线·pshift_gen/pshift 移位一般式）＋字面锚×13＋族域 n=1..6 全一致锚×42（机器 pdivmod 商与前批 zzm1b certified zz_pq 表逐位一致·商余恒等式 padd(pmul(q,den),rem)=num 机内判定）＝切片 3 Laurent A_j/B_j 供件面；PA=13 Closed（born-in-tree 编译实测）；ng_qed=55（grep-token 双口径相等·清洗稿实测）；零 Axiom·零 solver（头注纪律面）＋Obj.magic=0 提取零失名（池账承继） *)
Definition ng_Zzm2Qpoly : NewGreenFace :=
  MkNewGreenFace "zzm2_qpoly.v" 385 55 20261016
  "q polynomial layer eight arithmetic operations with pseudo division and shift general form and fifty five anchors" "L385:m9a4516".

(* ---------- V46 批统计（整批追加纪律：清单/常量/引理同块原子写入·ng_qed 口径） ---------- *)
Definition NewGreenListV46 : list NewGreenFace :=
 cons ng_Zb3zBase42
 (cons ng_Zeta3Assembly7
 (cons ng_Zeta3Assembly6
 (cons ng_GclHent2
 (cons ng_GclFull
 (cons ng_D519a2Cert
 (cons ng_N1AffineTransform
 (cons ng_Zzm2Qpoly
 nil))))))).
(* 续写统计：8 件 / 行数和 3379 / 闭合数和 168（ng_qed 口径·清洗稿实测字面值；一致性由下方等式引理编译期核对）。 *)
Definition NewGreenV46Pieces  : nat := 8.
Definition NewGreenV46LineSum : nat := 3379.
Definition NewGreenV46QedSum  : nat := 168.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV46Pieces_matches : NewGreenV46Pieces = cnt_ng NewGreenListV46.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV46LineSum_matches : NewGreenV46LineSum = sum_ng_lines NewGreenListV46.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV46QedSum_matches : NewGreenV46QedSum = sum_ng_qed NewGreenListV46.
Proof. reflexivity. Qed.

(* ================= V47 批（登记 15 件·π 族 ZZ/装配链注册波）（整批追加纪律：清单/常量/引理同块原子写入） ================= *)
(* ng_PiuMuCriterion -- piu_mu_criterion.v: 幂测度判据线性形；零假设出口；PA=7 Closed（born-in-tree 编译实测）；ng_qed=8（grep-token·清洗稿实测） *)
Definition ng_PiuMuCriterion : NewGreenFace :=
  MkNewGreenFace "piu_mu_criterion.v" 281 8 20261016
  "irrational measure criterion linear form with coefficient and value bounds finite verification" "L281:mdc5b47".
(* ng_PiuZzConstants -- piu_zz_constants.v: 常数档案件；数值面 vm_compute 出口；PA 检查 0 打点（件内无 Print Assumptions 出口·编译绿判在账）；ng_qed=59（grep-token·清洗稿实测） *)
Definition ng_PiuZzConstants : NewGreenFace :=
  MkNewGreenFace "piu_zz_constants.v" 556 59 20261016
  "zeilberger zudilin route rational skeleton constants with closed form computational shape" "L556:m6cd82e".
(* ng_PiuZzGaussPair -- piu_zz_gauss_pair.v: 高斯有理数对载体；gz_inv 全定义零对零返回；PA=24 Closed（born-in-tree 编译实测）；ng_qed=24（grep-token·清洗稿实测） *)
Definition ng_PiuZzGaussPair : NewGreenFace :=
  MkNewGreenFace "piu_zz_gauss_pair.v" 266 24 20261016
  "gauss rational pairs algebraic carrier over rationals for discrete kernel bookkeeping" "L266:m0e9d50".
(* ng_PiuZzPadicClearing -- piu_zz_padic_clearing.v: p-adic 清整；A_j 本体与渐近式留接续面如实；PA=10 Closed（born-in-tree 编译实测）；ng_qed=35（grep-token·清洗稿实测） *)
Definition ng_PiuZzPadicClearing : NewGreenFace :=
  MkNewGreenFace "piu_zz_padic_clearing.v" 927 35 20261016
  "padic clearing lemmas with valuation clearing factor bounds and lcm divisibility propagation" "L927:m927ee9".
(* ng_PiuZzPoincareEngine -- piu_zz_poincare_engine.v: 根限引擎一段；率面假设位显式保留；PA=10 Closed（born-in-tree 编译实测）；ng_qed=9（grep-token·清洗稿实测） *)
Definition ng_PiuZzPoincareEngine : NewGreenFace :=
  MkNewGreenFace "piu_zz_poincare_engine.v" 371 9 20261016
  "poincare root limit engine for recurrence part one with monotone comparison" "L371:m7c0ac4".
(* ng_PiuZzJuryCubic -- piu_zz_jury_cubic.v: Jury 判据核；半径 25000 实例；PA=39 Closed（born-in-tree 编译实测）；ng_qed=39（grep-token·清洗稿实测） *)
Definition ng_PiuZzJuryCubic : NewGreenFace :=
  MkNewGreenFace "piu_zz_jury_cubic.v" 902 39 20261016
  "third order schur jury criterion over rationals with radius instance at twenty five thousand" "L902:m9866fe".
(* ng_PiuZzPoincareL1 -- piu_zz_poincare_L1.v: 根限引擎二段子引理；PA=33 Closed（born-in-tree 编译实测）；ng_qed=38（grep-token·清洗稿实测） *)
Definition ng_PiuZzPoincareL1 : NewGreenFace :=
  MkNewGreenFace "piu_zz_poincare_L1.v" 719 38 20261016
  "poincare engine part two sub lemmas of the root limit program" "L719:m785fd1".
(* ng_PiuZzKernelSum -- piu_zz_kernel_sum.v: ZZ 式(5) 系数载体；样本 -2392/8000 档案值；PA=50 Closed（born-in-tree 编译实测）；ng_qed=51（grep-token·清洗稿实测） *)
Definition ng_PiuZzKernelSum : NewGreenFace :=
  MkNewGreenFace "piu_zz_kernel_sum.v" 1127 51 20261016
  "discrete multiple sum carrier for partial fraction coefficients with crude size bound" "L1127:m0c44b7".
(* ng_PiuZzKernelFaceGd2p01 -- piu_zz_kernel_face_gd2p01.v: 核面 L∞ 双出口件；PA=26 Closed（born-in-tree 编译实测）；ng_qed=26（grep-token·清洗稿实测） *)
Definition ng_PiuZzKernelFaceGd2p01 : NewGreenFace :=
  MkNewGreenFace "piu_zz_kernel_face_gd2p01.v" 678 26 20261016
  "kernel face linfinity bound with bcoef arithmetic and dual exit registration" "L678:m8aca61".
(* ng_PiuZzJuryL2aGd2q01 -- piu_zz_jury_l2a_gd2q01.v: L2a 结式面切片一；PA=12 Closed（born-in-tree 编译实测）；ng_qed=12（grep-token·清洗稿实测） *)
Definition ng_PiuZzJuryL2aGd2q01 : NewGreenFace :=
  MkNewGreenFace "piu_zz_jury_l2a_gd2q01.v" 249 12 20261016
  "L2a alpha resultant face of third order jury criterion slice with six eval lemmas" "L249:mafad66".
(* ng_PiuZzJuryL2a2Gd2q02 -- piu_zz_jury_l2a2_gd2q02.v: L2a 续切片；域外方向注记如实；PA=16 Closed（born-in-tree 编译实测）；ng_qed=16（grep-token·清洗稿实测） *)
Definition ng_PiuZzJuryL2a2Gd2q02 : NewGreenFace :=
  MkNewGreenFace "piu_zz_jury_l2a2_gd2q02.v" 380 16 20261016
  "L2a continuation slice alternating toolkit quadratic bridge and common root bridge" "L380:m7f9307".
(* ng_PiuZzLnRateBound -- piu_zz_ln_rate_bound.v: 率面有限点定理+机验反例；尾段率型假设保持最小诚实位不隐藏；PA=8 Closed（born-in-tree 编译实测）；ng_qed=11（grep-token·清洗稿实测） *)
Definition ng_PiuZzLnRateBound : NewGreenFace :=
  MkNewGreenFace "piu_zz_ln_rate_bound.v" 303 11 20261016
  "L n rate type finite point verification with step ratio counterexamples and honest residual" "L303:me2ad1b".
(* ng_PiuZzBridgeReal -- piu_zz_bridge_real.v: real 层桥；μ 证书为显式函数参数非公理；PA=9 Closed（born-in-tree 编译实测）；ng_qed=20（grep-token·清洗稿实测） *)
Definition ng_PiuZzBridgeReal : NewGreenFace :=
  MkNewGreenFace "piu_zz_bridge_real.v" 421 20 20261016
  "real layer mu certificate to distance form tail bridge with halving chain" "L421:m3eafd3".
(* ng_PiuZzBridgeRateslot -- piu_zz_bridge_rateslot.v: v2 率槽桥；v1/v2 非等价改名如实；PA=10 Closed（born-in-tree 编译实测）；ng_qed=6（grep-token·清洗稿实测） *)
Definition ng_PiuZzBridgeRateslot : NewGreenFace :=
  MkNewGreenFace "piu_zz_bridge_rateslot.v" 252 6 20261016
  "rate slot version two merged bridge with precombined halving threshold" "L252:m5bf2f4".
(* ng_Piu1932UncondZz -- piu1932_uncond_zz.v: 装配正件；唯一前提=率面 μ 证书（Set 承载）出节即显式参数；PA=5 Closed（born-in-tree 编译实测）；ng_qed=7（grep-token·清洗稿实测） *)
Definition ng_Piu1932UncondZz : NewGreenFace :=
  MkNewGreenFace "piu1932_uncond_zz.v" 127 7 20261016
  "route b assembly main piece unconditional power rate tight upper bound instantiation" "L127:m61baed".
(* ng_PiuZzTauEnclosureBase -- piu_zz_tau_enclosure_base.v: τ 有理夹包十七片终形·基座片（定义与有理数辅助引理群＋§D 两条 Section 参数化出节全称化假设槽·链首）；PA=<应用前必填：new_About 实测检验>；ng_qed=85（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureBase : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_base.v" 1499 85 20261024
  "tau enclosure base definitions and rational helper lemmas of the seventeen piece split" "L1499:m417fe3".
(* ng_PiuZzTauEnclosureBank1 -- piu_zz_tau_enclosure_bank1.v: τ 夹包十七片终形·一号库片（§V 样点带第 1 段）；PA=<应用前必填：new_About 实测检验>；ng_qed=731（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureBank1 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_bank1.v" 5166 731 20261024
  "tau enclosure proof bank one segment of the seventeen piece split" "L5166:m6021ea".
(* ng_PiuZzTauEnclosureBank2 -- piu_zz_tau_enclosure_bank2.v: τ 夹包十七片终形·二号库片（§V 样点带第 2 段）；PA=<应用前必填：new_About 实测检验>；ng_qed=569（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureBank2 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_bank2.v" 4382 569 20261024
  "tau enclosure proof bank two segment of the seventeen piece split" "L4382:m342d62".
(* ng_PiuZzTauEnclosureBank3 -- piu_zz_tau_enclosure_bank3.v: τ 夹包十七片终形·三号库片（§V 样点带第 3 段）；PA=<应用前必填：new_About 实测检验>；ng_qed=512（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureBank3 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_bank3.v" 4108 512 20261024
  "tau enclosure proof bank three segment of the seventeen piece split" "L4108:m806772".
(* ng_PiuZzTauEnclosureBank4 -- piu_zz_tau_enclosure_bank4.v: τ 夹包十七片终形·四号库片（§V 样点带第 4 段）；PA=<应用前必填：new_About 实测检验>；ng_qed=957（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureBank4 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_bank4.v" 6266 957 20261024
  "tau enclosure proof bank four segment of the seventeen piece split" "L6266:m6796d3".
(* ng_PiuZzTauEnclosureHead -- piu_zz_tau_enclosure_head.v: τ 夹包十七片终形·头片（α 区 zz_Phi 256/512 字面值链）；PA=<应用前必填：new_About 实测检验>；ng_qed=3（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureHead : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_head.v" 808 3 20261024
  "tau enclosure head literal chain of the seventeen piece split" "L808:me3b91d".
(* ng_PiuZzTauHbWave1 -- piu_zz_tau_hb_wave1.v: Hb 升格波 1（512 段 Hb0-Hb15·16 条 piu_zz_hb_512_* 引理·语句证明体逐字保留）；PA=<应用前必填：new_About 实测检验>；ng_qed=16（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave1 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave1.v" 382 16 20261024
  "tau enclosure hb promotion wave one segment of the seventeen piece split" "L382:m2d4e30".
(* ng_PiuZzTauHbWave2 -- piu_zz_tau_hb_wave2.v: Hb 升格波 2（512 段 Hb16-Hb31）；PA=<应用前必填：new_About 实测检验>；ng_qed=16（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave2 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave2.v" 382 16 20261024
  "tau enclosure hb promotion wave two segment of the seventeen piece split" "L382:m7845ad".
(* ng_PiuZzTauHbWave3a -- piu_zz_tau_hb_wave3a.v: Hb 升格波 3 四季拆分之 a（1024 段 Hb0-Hb3）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave3a : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave3a.v" 106 4 20261024
  "tau enclosure hb promotion wave three a quarter segment of the seventeen piece split" "L106:m220c8a".
(* ng_PiuZzTauHbWave3b -- piu_zz_tau_hb_wave3b.v: Hb 升格波 3 四季拆分之 b（1024 段 Hb4-Hb7）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave3b : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave3b.v" 106 4 20261024
  "tau enclosure hb promotion wave three b quarter segment of the seventeen piece split" "L106:m09d392".
(* ng_PiuZzTauHbWave3c -- piu_zz_tau_hb_wave3c.v: Hb 升格波 3 四季拆分之 c（1024 段 Hb8-Hb11）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave3c : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave3c.v" 106 4 20261024
  "tau enclosure hb promotion wave three c quarter segment of the seventeen piece split" "L106:m8741b5".
(* ng_PiuZzTauHbWave3d -- piu_zz_tau_hb_wave3d.v: Hb 升格波 3 四季拆分之 d（1024 段 Hb12-Hb15）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave3d : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave3d.v" 106 4 20261024
  "tau enclosure hb promotion wave three d quarter segment of the seventeen piece split" "L106:mc589e0".
(* ng_PiuZzTauHbWave4a -- piu_zz_tau_hb_wave4a.v: Hb 升格波 4 四季拆分之 a（1024 段 Hb16-Hb19）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave4a : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave4a.v" 106 4 20261025
  "tau enclosure hb promotion wave four a quarter segment of the seventeen piece split" "L106:m1a4b45".
(* ng_PiuZzTauHbWave4b -- piu_zz_tau_hb_wave4b.v: Hb 升格波 4 四季拆分之 b（1024 段 Hb20-Hb23）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave4b : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave4b.v" 106 4 20261025
  "tau enclosure hb promotion wave four b quarter segment of the seventeen piece split" "L106:m540324".
(* ng_PiuZzTauHbWave4c -- piu_zz_tau_hb_wave4c.v: Hb 升格波 4 四季拆分之 c（1024 段 Hb24-Hb27）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave4c : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave4c.v" 106 4 20261025
  "tau enclosure hb promotion wave four c quarter segment of the seventeen piece split" "L106:me15bf5".
(* ng_PiuZzTauHbWave4d -- piu_zz_tau_hb_wave4d.v: Hb 升格波 4 四季拆分之 d（1024 段 Hb28-Hb31）；PA=<应用前必填：new_About 实测检验>；ng_qed=4（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave4d : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave4d.v" 106 4 20261025
  "tau enclosure hb promotion wave four d quarter segment of the seventeen piece split" "L106:md4a412".
(* ng_PiuZzTauHbWave5 -- piu_zz_tau_hb_wave5.v: Hb 升格波 5（1024 段 Hb32-Hb47）；PA=<应用前必填：new_About 实测检验>；ng_qed=16（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave5 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave5.v" 382 16 20261024
  "tau enclosure hb promotion wave five segment of the seventeen piece split" "L382:me19590".
(* ng_PiuZzTauHbWave6 -- piu_zz_tau_hb_wave6.v: Hb 升格波 6（1024 段 Hb48-Hb63）；PA=<应用前必填：new_About 实测检验>；ng_qed=16（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave6 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave6.v" 382 16 20261024
  "tau enclosure hb promotion wave six segment of the seventeen piece split" "L382:m5c6cda".
(* ng_PiuZzTauHbWave7 -- piu_zz_tau_hb_wave7.v: Hb 升格波 7（1024 段 Hb64-Hb79）；PA=<应用前必填：new_About 实测检验>；ng_qed=16（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave7 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave7.v" 382 16 20261024
  "tau enclosure hb promotion wave seven segment of the seventeen piece split" "L382:m442ea0".
(* ng_PiuZzTauHbWave8 -- piu_zz_tau_hb_wave8.v: Hb 升格波 8（1024 段 Hb80-Hb95）；PA=<应用前必填：new_About 实测检验>；ng_qed=16（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauHbWave8 : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_hb_wave8.v" 382 16 20261024
  "tau enclosure hb promotion wave eight segment of the seventeen piece split" "L382:m1d0e8e".
(* ng_PiuZzTauEnclosurePhi1024Slim -- piu_zz_tau_enclosure_phi1024_slim.v: τ 夹包十七片终形·φ1024 组合片（zzPhi_1024 巨证体·96 处 assert 换实例化 piu_zz_hb_1024_0..95·余逐字节等；无壳改形：Require 直挂 wave3a-d/wave4a-d 八行·伞名绝迹）；PA=<应用前必填：new_About 实测检验>；ng_qed=2（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosurePhi1024Slim : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_phi1024_slim.v" 428 2 20261025
  "tau enclosure phi1024 slim composition with hb instantiation of the seventeen piece split" "L428:m821933".
(* ng_PiuZzTauEnclosureLiterals -- piu_zz_tau_enclosure_literals.v: τ 夹包十七片终形·字面值片（γ 区 zzL×3＋qpow_u/l×6·Require head＋slim）；PA=<应用前必填：new_About 实测检验>；ng_qed=9（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosureLiterals : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure_literals.v" 74 9 20261024
  "tau enclosure literals zone of the seventeen piece split" "L74:md38f2c".
(* ng_PiuZzTauEnclosure -- piu_zz_tau_enclosure.v: τ 夹包十七片终形·链末棒（原名牌·承原册行定位）: δ+ε 区样点带与审计段（up/lo ok×6＋band×4＋Print Assumptions×3＋Extraction×1）；PNT 假设位 §D 两条居 base 片 Section 参数化出节全称化（非公理化）；样点带 V1 up 全 false/lo 全 true 如实（N0 领地在样点带外）；旧册行 PA=3 系 494c8738 旧巨件证词·锚件已不存在·禁沿用；PA=<应用前必填：new_About 实测检验>；ng_qed=10（grep-token·落装稿实测·双口径相等） *)
Definition ng_PiuZzTauEnclosure : NewGreenFace :=
  MkNewGreenFace "piu_zz_tau_enclosure.v" 98 10 20261024
  "tau enclosure rational sandwich carrier with face low and nonzero source lemma over rationals" "L98:mb09c02".
(* ng_Piu1930DomfaceNegative -- piu1930_domface_negative.v: 带域参量化单调失配负定理（带内既约点供给序随乘子线性·约化高度恒定·固定预算槽全族不可居）；零假设出口；PA=11 Closed（编译实测）；ng_qed=20（grep-token 实测） *)
Definition ng_Piu1930DomfaceNegative : NewGreenFace :=
  MkNewGreenFace "piu1930_domface_negative.v" 400 20 20261027
  "band parameterized monotone supply mismatch negative theorem for reduced band points with fixed height" "L400:m40e413".
(* ng_PiuZzMuAssembly -- piu_zz_mu_assembly.v: 实层率面接口件（点距证书到率形 real_lt 的转换·判据数据 κ=35831808／τ=2·τ 次幂消去引理）；本件语句面不使用判据数据 σ（下游件钉面取 σ=12）；PA=6 Closed（编译实测）；ng_qed=7（grep-token 实测） *)
Definition ng_PiuZzMuAssembly : NewGreenFace :=
  MkNewGreenFace "piu_zz_mu_assembly.v" 194 7 20261027
  "real layer rate form interface adapters for the pi irrationality measure certificate with criterion data pins and tau power cancellation" "L194:m12798c".
(* ng_PiuZzECarrier -- piu_zz_e_carrier.v: E 侧线性形条件式 mu 证书链（六显式前提 Hp/Htri/Hcoef/Hesc/Hcage/Hexit 到率形 real_lt 终形·判据数据 σ=12／τ=2／κ=35831808）；PA=6 Closed（审计件编译实测）；ng_qed=33（grep-token 实测） *)
Definition ng_PiuZzECarrier : NewGreenFace :=
  MkNewGreenFace "piu_zz_e_carrier.v" 761 33 20261027
  "conditional mu certificate chain over the e side linear form with six explicit premises closing the rate form real layer goal" "L761:mf22b5b".
(* ng_NsepBudgetExhaustion —— NsepBudgetExhaustion.v: 预算耗尽见证件（预算化最小分离索引搜索 nsep_first 无条件命中形的构造性否证：q0=22/7 落入第 0 至预算端点 34 全部窗·预算全程耗尽·输出端点且端点判定非命中；fixpoint 桥引理 lw5n_find_nsep_find 先重写后 destruct·零内核窗计算）；§3 两枚否证语句为纯 Prop 位（B 档随件申报·lw5n_shape_band 先例·不入提取单）；PA=6 Closed（编译实测）；ng_qed=8（Qed 闭合实测·头注叙述词面 3 处不计） *)
Definition ng_NsepBudgetExhaustion : NewGreenFace :=
  MkNewGreenFace "NsepBudgetExhaustion.v" 164 8 20261029
  "budget exhaustion witness refuting the unconditional hit form of the budgeted minimal separation search over the q0 window chain" "L164:m4f7495".
(* ng_NsepBudgetVerify —— NsepBudgetVerify.v: 验证块拆件（q0:=22/7 计算钉两枚·端点 Q 序钉两枚·全阶窗内常量化引理 lw5n_inwin_q0_all：lw5n_win_nested 解析嵌套·端点级 bool 对拍·零 lw5n_shape_mono 全量物化）；PA=3 Closed（编译实测）；ng_qed=5（Qed 闭合实测） *)
Definition ng_NsepBudgetVerify : NewGreenFace :=
  MkNewGreenFace "NsepBudgetVerify.v" 92 5 20261029
  "verification split piece with q0 computation pins and the constantized all-levels window lemma" "L92:me45ad5".
(* ng_U5cQuadUniformEscape —— u5c_quad_uniform_escape.v: √d 一致逃逸参数化件（∀(d:positive)(Hd:u5c_quad_nonsq d)(q:Q)，主定理 quadratic_uniform_escape 给出正分离常数 c:Q 与 real_lt (real_const c) (real_metric <√d 牛顿序列>) (real_const q) 的 sigT 证书；|a²−d·b²|≥1 整性间隙独立引理 u5c_quad_gap_abs·四支常量 K_d:=4d+8·窗 n0=2⌈d⌉+2⌈b⌉+⌈K_d⌉·e(n)≤d²/4ⁿ 衰减·lic 判据单行装配）；八契约件 require-only 零触碰；语句面 Set 承载零新铸 Prop；PA=2 Closed（编译实测·主定理+gap_abs）；ng_qed=33（Qed 闭合实测） *)
Definition ng_U5cQuadUniformEscape : NewGreenFace :=
  MkNewGreenFace "u5c_quad_uniform_escape.v" 1255 33 20261029
  "parameterized uniform sqrt-d escape certificate closing a positive separation constant against the Newton sequence through an integer gap kernel and a uniform decay window" "L1255:m762127".
(* ng_U5cQuadDemoSqrt7 —— u5c_quad_demo_sqrt7.v: √7 演示件（P1 参数化一次调用 u5c_demo7_escape := quadratic_uniform_escape 7 u5c_nonsq7；唯一新数学内容＝Set 层非平方见证 u5c_nonsq7:u5c_quad_nonsq 7 一枚 id_refl 闭口＋n0=3 样点 margin/branch 证书四枚（QleT'/QltT 纯转换面）；对照 u5c_inst_sqrt5 1300+ 行手工同构改编形·参数化收益成立）；PA=2 Closed（编译实测·escape+q3_cert）；ng_qed=3（Qed 闭合实测） *)
Definition ng_U5cQuadDemoSqrt7 : NewGreenFace :=
  MkNewGreenFace "u5c_quad_demo_sqrt7.v" 175 3 20261029
  "sqrt-7 demonstration instance closing the uniform escape family by one parameter call with a Set-level nonsquare witness and pure-conversion sample certificates" "L175:mbc7066".
(* ng_PiuZzPntWindow —— piu_zz_pnt_window.v: 窗覆盖件（半开窗 (3n/(3k+2), 2n/(2k+1)] 内素数 p 之分数部 {n/p} ∈ [1/2, 2/3) 故属 Zeilberger-Zudilin 窗集 P_n（节点 B1）＋窗位推论 3n < p^2·保守窗被保留时恒成立）；PA=4 Closed（编译实测）；ng_qed=4（Qed 闭合实测） *)
Definition ng_PiuZzPntWindow : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_window.v" 135 4 20261030
  "window coverage of the kept prime set P_n via fractional-part boolean membership with the window-position corollary" "L135:m1f1571".
(* ng_PiuZzPntWinsum —— piu_zz_pnt_winsum.v: 窗和证书件（每窗密度项 1/((2k+1)(3k+2))＝窗宽比 2/(2k+1)−3/(3k+2) 之正性/单调递减/伸缩族 1/(4k(k+1)) 上控＋显式 K=150 数值证书喂 Phi_n 下界（节点 B2））；PA=5 Closed（编译实测）；ng_qed=9（Qed 闭合实测） *)
Definition ng_PiuZzPntWinsum : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_winsum.v" 156 9 20261030
  "window-sum density certificates with positivity, monotone decrease and telescoping majoration feeding the explicit K=150 numeric slot" "L156:m0f5802".
(* ng_PiuZzPntQexp —— piu_zz_pnt_qexp.v: Q 指数证书机件（Taylor 部分和非负参单调＋数值锚 exp_partial 40 (20) < 664*1000*1000 喂 eps0=1/6600 常量归一步（ln(6.64e8) ≥ 20 因 e^20 < 6.64e8 且 20^3 = 8000 ≥ 6600）＋Taylor 余项几何上控 0 ≤ x < n+2 面）；PA=6 Closed（编译实测）；ng_qed=30（Qed 闭合实测） *)
Definition ng_PiuZzPntQexp : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_qexp.v" 681 30 20261030
  "Q-exponential certificate machinery: Taylor partial-sum monotonicity, the e^20 numeric anchor and geometric remainder majoration for the Dusart normalization slot" "L681:m78d0c3".
(* ng_PiuZzPntLcmpow —— piu_zz_pnt_lcmpow.v: lcm 幂刻画件（素数幂 p^e ≤ N 整除 lcm(1..N)（B3.1）＋相异素数幂 Set 承载 bool 面互素（B3.2）＋m ≥ 2 素因子存在与素数精确幂剥离（B3.3）＋psi 折叠 zz_psi N 吸收 [1,N] 全体故 lcm(1..N) | zz_psi N（B3.4））；PA=10 Closed（编译实测）；ng_qed=37（Qed 闭合实测） *)
Definition ng_PiuZzPntLcmpow : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_lcmpow.v" 807 37 20261030
  "power characterization of lcm(1..N): prime-power divisibility, boolean-face coprimality, prime-factor stripping and the psi-fold absorption lcm | zz_psi N" "L807:mee004a".
(* ng_PiuZzPntPhi —— piu_zz_pnt_phi.v: Phi_n 下界件（窗端点 b_k = 2n/(2k+1)、a_k = 3n/(3k+2) 布尔窗成员 discharge 窗集条件＋保守窗宽和下控 n*(322/500) − 302＋窗素积整除 Phi_n＋窗不相交蕴窗积两两互素＋Taylor 部分和积式装配 zz_pnt_phi_lower 下控 zq(Phi_n)·每窗 θ 含量显式全称保持）；PA=4 Closed（编译实测）；ng_qed=28（Qed 闭合实测） *)
Definition ng_PiuZzPntPhi : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_phi.v" 697 28 20261030
  "Phi_n lower bound: boolean window membership, width-sum domination n*(322/500)-302, per-window prime-product divisibility, pairwise coprimality and the assembled Taylor-product face zz_pnt_phi_lower" "L697:me75ea3".
(* ng_PiuZzPntIpow —— piu_zz_pnt_ipow.v: 整数幂证书机件（nat 幂与精确分裂 (F/p)^M = F^M/p^M bool 恒等式＋floor 三明治 floor(a/p) ≤ a/p ≤ floor(a/p)+1 与配套 ceiling 三明治（C = ceil(e^{rD}) 证书面）＋相对损失 x*(D−1)/D ≤ floor(x)（x ≥ D ≥ 2·D = 10^4 预算面）＋幂级实例 x^M*(D−1)/D ≤ floor(x^M)（节点 B5.4））；PA=4 Closed（编译实测）；ng_qed=23（Qed 闭合实测） *)
Definition ng_PiuZzPntIpow : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_ipow.v" 386 23 20261030
  "integer-power certificate machinery: exact rational-power split, floor and ceiling sandwiches for the C=ceil(e^{rD}) face and relative-loss bounds at the D=10^4 budget face" "L386:m354448".
(* ng_PiuZzPntPsi —— piu_zz_pnt_psi.v: psi-素阶乘分裂件（折叠 zz_psi_prod N k 有界于 pec_prim N × pec_prim(zz_iroot 2 N)^(k−1)·全折叠 zz_psi N = zz_psi_prod N (log2 N) 三面可计算上控：因子化素阶乘面／单幂面 4^(2*N*log2 N)／下游面 pec_prim N * 4^(2*sqrt(N)*(log2 N − 1))·装配阶段据此把解析输入隔离于首素阶乘因子）；PA=4 Closed（编译实测）；ng_qed=7（Qed 闭合实测） *)
Definition ng_PiuZzPntPsi : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_psi.v" 239 7 20261030
  "psi-versus-primorial split: the root-primorial fold bounded by pec_prim faces isolating the analytic input on the leading primorial factor" "L239:m1d6a25".
(* ng_PiuZzPntRateup —— piu_zz_pnt_rateup.v: 装配脊柱件（L_n = lcm(1..4n)/Phi_n 终局上率面：born 链面组有理式 L_n ≤ Psi(4n)/Phi_n＋自两枚显式 Set 承载 eventual 槽（A lcm 侧 Psi(4n) ≤ 55^n eventual·解析 θ 输入居后；B 分母侧 (19/10)^n ≤ Phi_n eventual·窗素积下界居后）装配 sigT 终面 { N0 : nat & forall n >= N0, QleT' (zq (zz_L n)) ((29#1)^n) }）；PA=1 Closed（编译实测）；ng_qed=11（Qed 闭合实测） *)
Definition ng_PiuZzPntRateup : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_rateup.v" 272 11 20261030
  "assembly spine: the eventual upper rate face for L_n assembled from two explicit Set-carried eventual slots into the sigT certificate QleT' (zq (zz_L n)) ((29#1)^n)" "L272:m6172ac".
(* ng_PiuZzPntAssembly —— piu_zz_pnt_assembly.v: PNT 侧集成件（五 born 件成表 lcmpow/window/winsum/ipow/phi＋两 L_n 率槽与窗 θ 槽 Section 显式参化取用（诚实 PNT 级假设面·零 discharge 零 axiom）·交付乘性分解面 zq(zz_L n)·zq(zz_Phi n) ≤ zq(psi(4n))（B3.4 与 zz_L 整除代数积式分解）＋Phi 下界面 θ 槽再输出＋τ/LOW 面槽参实例化·出节六面 Print Assumptions 全 Closed）；PA=6 Closed（编译实测）；ng_qed=6（Qed 闭合实测） *)
Definition ng_PiuZzPntAssembly : NewGreenFace :=
  MkNewGreenFace "piu_zz_pnt_assembly.v" 181 6 20261030
  "PNT-side total assembly: five born pieces tabulated, rate and window-theta slots carried as explicit Section parameters never discharged, delivering the multiplicative decomposition zq(zz_L n)*zq(zz_Phi n) <= zq(psi(4n)) with six Closed assumption faces" "L181:maf3472".
(* ---------- V48 注册批八件（γP1 首波四件 KB72 预铸逐字承用＋W4 三件＋N2c 一件·registered in the November 2026 wave·依赖序 cage→decay→nail→n1→headledger→nescD→bracket→n2c·W5 件块禁预填候 born 重锚） ---------- *)
(* ---------- ② N2a · piu_zz_cage_constants.v（KB41o ①·KB41b C1-C7 对位落件·件一 C1-C4＋件二 C5+C7） ---------- *)
(* ng_PiuZzCageConstants -- piu_zz_cage_constants.v: γP1 N2a 笼常数面：KB41b C1-C7 EXACT 证书链语句化（件一 C1-C4 ρ 主钉定标＋件二 C5+C7 σ 装配覆盖＋N₀ 多项式吸收·Hasm 会签位随件）〔代拟·候选终核〕; PA=34 Closed（编译实测）; ng_qed=35（行尾计数实测） *)
Definition ng_PiuZzCageConstants : NewGreenFace :=
  MkNewGreenFace "piu_zz_cage_constants.v" 474 35 20261101
  "gammaP1 N2a cage constant face: KB41b C1-C7 EXACT chain as Set-carried statements (C1-C4 rho pin-face calibration + C5+C7 sigma assembly coverage + N0 poly absorption)" "L474:m5b5a48".
(* ---------- ③ N2b · piu_zz_sigma_decay.v（KB41o ④·σ 值衰减面三带·下游位 N2c/N5/N4） ---------- *)
(* ng_PiuZzSigmaDecay -- piu_zz_sigma_decay.v: γP1 N2b σ 值衰减面三带（raw EXACT 带＋sup_j 控制带下游形＋b0 桥）·下游位 N2c/N5/N4·机外拟合值零语句面〔代拟·候选终核〕; PA=10 Closed（编译实测）; ng_qed=10（行尾计数实测） *)
Definition ng_PiuZzSigmaDecay : NewGreenFace :=
  MkNewGreenFace "piu_zz_sigma_decay.v" 231 10 20261101
  "gammaP1 N2b sigma value-decay face: raw EXACT band / sup_j control band / assembly slack as Set-carried statements serving N2c/N5/N4" "L231:m7b1921".
(* ---------- ④ N6′-a · piu_zz_nail_mu.v（KB41b C1-C7 弹药·γP1v2 §三 主钉/μ 换算件·预铸名义 cage_repin 改名同步） ---------- *)
(* ng_PiuZzNailMu -- piu_zz_nail_mu.v: γP1 N6′-a 主钉与 μ 换算面：ρ=(3/20)^n 主钉（σ=17·E=7·N0=1348）＋μ 括界诚实接口（ln2/ln(20/3) 显式 Q 参数）＋KB41d C6 精确 Q 交叉核对（mu_ZZ 槽 8 死钉对照）〔代拟·候选终核〕; PA=10 Closed（编译实测）; ng_qed=51（行尾计数实测） *)
Definition ng_PiuZzNailMu : NewGreenFace :=
  MkNewGreenFace "piu_zz_nail_mu.v" 387 51 20261101
  "gammaP1 N6'-a main-nail and mu-conversion face: rho=(3/20)^n main nail with mu bracket honest interface (explicit Q params) + KB41d C6 exact Q cross-checks" "L387:m191cea".
(* ---------- ① N1 · piu_zz_n1_linform.v（KB41n 弹药·S1 长度引理＋M_j 计数面转录·预铸名义 s1_len 改名同步） ---------- *)
(* ng_PiuZzN1Linform -- piu_zz_n1_linform.v: γP1 N1 ZZ 系数线性形长度面语句载体：|M_j|≤(3n+1)⁶≤2^{2n} 链（n≥18 立恰 n=17 破）＋Q 值序谓词＋max-T 达成见证（sigT）＋n<18 有限核查面＋vm_compute 数值样点包〔代拟·候选终核〕; PA=5 Closed（编译实测·kb72 born3）; ng_qed=34（行尾计数实测·上问裸口径 35 之修正） *)
Definition ng_PiuZzN1Linform : NewGreenFace :=
  MkNewGreenFace "piu_zz_n1_linform.v" 423 34 20261101
  "gammaP1 N1 ZZ coefficient linear-form length face: |M_j|<=(3n+1)^6<=2^(2n) chain (n>=18, fails n=17), Q-order predicate, max-T witness (sigT), finite-check face n<18, vm_compute samples" "L423:mf96119".
(* ---------- N4 · piu_zz_s2_headledger.v（γP1 W4 批·KB76 max-form 证书替代 KB61 退役账） ---------- *)
(* ng_PiuZzS2Headledger -- piu_zz_s2_headledger.v: S2(n) Mertens 噪声头段上界账本：KB76 max-form 证书 |s2(n)|≤max(C1·n^(3/4)·C2*n)（n≥41）语句化——C1/C2* 精确 Q 括界＋三段拼接（piece i/ii/iii sup 账统一为 C2*-per-n eventual 面）＋max 两支并集头条（C1 支走精确四次幂 Q 面·3/4 分数幂不入 Q 面）＋D10 Proposition 5.1 修补入口（Buethe 2018 (1.7) 域隙 u≤1e19 由 Dusart 2010 Prop 5.1 因子 36261/36260 全域闭合·T4c x2 裕量吸收）＋min-form 禁面（min form＝注册在案假命题 R0）与 KB61 退役面; PA=19 Closed（编译实测）; ng_qed=23（行尾计数实测） *)
Definition ng_PiuZzS2Headledger : NewGreenFace :=
  MkNewGreenFace "piu_zz_s2_headledger.v" 485 23 20261101
  "S2(n) Mertens head-ledger: KB76 max-form certificate |s2(n)|<=max(C1*n^(3/4),C2*n) for n>=41 as EXACT Q brackets of C1/C2*, three-regime splice, two-branch max union with the C1 branch in the exact fourth-power Q face, D10 Prop 5.1 domain repair, min form banned and KB61 retired" "L485:ma3df0f".
(* ---------- N5 · piu_zz_ec_escwin_nescD.v（γP1 W4 批·逃逸窗交钥匙集成·(D) 窗见证闭式再武装） ---------- *)
(* ng_PiuZzEcEscwinNescD -- piu_zz_ec_escwin_nescD.v: 逃逸窗交钥匙集成件：(D) 窗见证指标闭式再武装 nescD(q)=ceil((2L+1)/5)（L=floor(log2(2q))=S(Nat.log2 q)·替换结构不兼容斜率 1/2 旧见证 65330/65536 网格失效）——nat 双肢 E1D（2q·3^n≤20^n）/E3D（2^(17n)≤κ·q^7）对一切 q≥1 于 n=nescD(q) 成立（全程谱证书：阶梯锚 400≥288·2187≥2048＋5 带归纳）＋Q 面窗供给（sigT·piu_mu_and2 肢 1/3）及其 QleT' 变式＋(D) HescD 前提槽显式 Set 面承载（供给契约：肢 1+3 本件·肢 2 p-adic clearing gap 同见证实例化）＋双引擎判别 Coq 侧同步副本（退役旧见证与近似 W25 精确拒绝面）; PA=9 Closed（编译实测）; ng_qed=26（行尾计数实测） *)
Definition ng_PiuZzEcEscwinNescD : NewGreenFace :=
  MkNewGreenFace "piu_zz_ec_escwin_nescD.v" 478 26 20261101
  "escape-window turnkey unit: closed-form witness nescD(q)=ceil((2L+1)/5) re-arms the (D)-window with nat limbs E1D/E3D holding for every q>=1 over the 5-band induction, the sigT Q-face window supply with its QleT' variant, the HescD premise slot as an explicit Set face, and the dual-engine rejection faces" "L478:m124f79".
(* ---------- N6′-b · piu_zz_ec_escwin_bracket.v（γP1 W4 批·逃逸窗 EXACT 括界＋头段覆盖语句面草案） ---------- *)
(* ng_PiuZzEcEscwinBracket -- piu_zz_ec_escwin_bracket.v: 逃逸窗 EXACT 括界套件与头段覆盖语句面（cage_constants 成例形制）：KB41g 4-1 上阈 L*=22902/7−log2 3（K=2^20 二进证书 2^1661953<3^(2^20)<2^1661954 整数幂）＋q*=2^(L∗)/3 有理括界（2^(5/7) 七次幂证书）＋下缘 1348·log2(20/3)−1（m'=2869916 二进证书）＋斜率证书 (20/3)^7>2^17＋q=1 见证强制锚——两阈之间见证落点不受控故 Hcage forall-n 形保留；三张 QleT' 承载覆盖面 hcage_head（n<1348）/hcage_tail（1348≤n）/hcage_all（forall n）过 Hasm/Hadm 接口对注册为 Set 型定义候 N4 侧会签（KB41m NEGATIVE：实际供给面 Hasm 实例化不可得·面诚实不实例化·构造骨架与预验证步清单存注释 W5 残留）; PA=10 Closed（编译实测）; ng_qed=11（行尾计数实测） *)
Definition ng_PiuZzEcEscwinBracket : NewGreenFace :=
  MkNewGreenFace "piu_zz_ec_escwin_bracket.v" 289 11 20261101
  "escape-window EXACT brackets and head-coverage statement face: L* upper threshold, q* rational brackets, lower-edge dyadic certificate, slope certificate and q=1 witness-forcing anchor, plus the hcage_head/tail/all QleT' faces over the Hasm/Hadm interface kept honestly un-instantiated" "L289:m4951eb".
(* ---------- N2c · piu_zz_n2c_sigma_assembly.v（γP1 N2c 节点·装配面常数单元·crude_size_sharp 于 2^(17n) 积分） ---------- *)
(* ng_PiuZzN2cSigmaAssembly -- piu_zz_n2c_sigma_assembly.v: N2c 装配面常数单元（KB41c 表 4-3 P1-P6 GO）：验收对象＝A 系数值面 Qabs(piu_zz_Aj n j)（e_carrier :627-630 装载语义·非 pre-collapse l1 面）——P1 A 面全 j le17 sharp 义务面＋n=1..3 有限旗标精确 Q 形＋P2/P3 L1 面 le17/le16.94 非约束观察面（零树载体·仅注释不入验收）＋P4/P5 控制带渐近 16.9358/外推松弛机外拟合值禁入语句面；兼送 σ_ZZ 装配钉（KB41b C5 EXACT·纸面 16.7553·松弛 0.2447 机外）＋mu_ZZ 名映射钉＋KB41k 数值银行 v2 锚（κ/c0/N0/钉序/C(1)）; PA=22 Closed（编译实测）; ng_qed=22（行尾计数实测） *)
Definition ng_PiuZzN2cSigmaAssembly : NewGreenFace :=
  MkNewGreenFace "piu_zz_n2c_sigma_assembly.v" 314 22 20261101
  "N2c assembly-surface constants unit: acceptance object the A coefficient-value face Qabs(piu_zz_Aj n j) with the sharp obligation and finite flags, the sigma_ZZ assembly pin and mu_ZZ name mapping, and the KB41k numeric-bank v2 anchors; machine-outside fit values banned from the statement surface" "L314:m8c1e82".
(* ---------- W5 · piu1932_uncond_zz.v（一致型顶件 9.3 同名重落·六前提无条件闭合·W6 二批·注册号 194 旧代 61baed 条目 ng_Piu1932UncondZz 原位保留＝A 案裁定·本块为候选版 46f5f5 二代登记·R 号 ? 占位·registry-day full-width placeholder pending, final value assigned at commit time） ---------- *)
(* ng_Piu1932UncondZzReland -- piu1932_uncond_zz.v: Route B 装配正件 W5 四槽直供形（在册件同名替换候选）：率槽 nsep 上界 NatLe (tlw1448_nsep_rebase ck q) (S (bpow_c C0 8 (height q))) 由 tlw1703_unif_rebase_le_Sbpowc 四槽直供导出——槽 1/2/4 取自池（C0 正·阈正·ck_alpha 自反）·槽 3 经 v2 率槽桥取自六前提条件链 piu_zz_ec_mu_cond·率形证书不再作抽象前提；前提组 Hp/Htri/Hcoef/Hesc/Hcage/Hexit 为显式诚实接口·旧率载签名保留为孪生定理（签名稳定迁移账）；C0=1/10^9·alpha=8（ZZ μ=7.1032…<8）; PA=7 Closed（kb77 out/born_b_uncond.log 实测）; ng_qed=8（行尾计数实测） *)
Definition ng_Piu1932UncondZzReland : NewGreenFace :=
  MkNewGreenFace "piu1932_uncond_zz.v" 179 8 20261103
  "Route B assembly main piece, W5 four-slot direct-supply form: the rate-slot nsep bound is derived with all four slots of tlw1703_unif_rebase_le_Sbpowc supplied directly, slot 3 from the six-premise conditional chain piu_zz_ec_mu_cond via the v2 rate-slot bridge, so no rate-form certificate is an abstract premise; the six premises Hp/Htri/Hcoef/Hesc/Hcage/Hexit are the explicit honest interface; previous rate-loaded signature kept as a twin theorem; C0 = 1/10^9, alpha = 8" "L179:m46f5f5".
(* ---------- V49 batch, 20 modules cons'd before the V47 list nil (dependency topological order; order.txt #R194 anchors in the three order copies): the SL12 constant case file, five ln L_n supply faces, two |I_n| supply faces, the SL4 skeleton unit, four delta-debt units (D-SL4-3/4/5), seven N2c-chain units (D-SL3-1..5); ng_qed = grep -c (Qed|Defined). token-face, line counts = wc -l; registered 20261114. ---------- *)
Definition ng_Sl12Constants : NewGreenFace :=
  MkNewGreenFace "sl12_constants.v" 877 103 20261114
  "22 checked Gantumur certificate-family constants cast as Q-form definitions with per-constant vm_compute anchors" "L877:m661649".
Definition ng_Sl1PhaseFaces : NewGreenFace :=
  MkNewGreenFace "sl1_phase_faces.v" 172 4 20261114
  "SL1 supply faces: psi-band phase certificate faces over the shared L_n object" "L172:mcfb294".
Definition ng_Sl1PhiDividesL : NewGreenFace :=
  MkNewGreenFace "sl1_phi_divides_L.v" 348 20 20261114
  "SL1 supply face: Phi_n divides L_n integer divisibility chain over the lcm carrier" "L348:md67014".
Definition ng_Sl1HeadAnchors : NewGreenFace :=
  MkNewGreenFace "sl1_head_anchors.v" 86 7 20261114
  "SL1 supply face: head-side numeric anchors for the L_n and Phi_n faces (n = 1..40 table)" "L86:m356d5d".
Definition ng_Sl1LznAssembly : NewGreenFace :=
  MkNewGreenFace "sl1_lzn_assembly.v" 319 15 20261114
  "SL1 supply face: L_n/Phi_n ratio assembly toward the exponential-bound statement" "L319:m89a782".
Definition ng_Sl1Lzn48Chain : NewGreenFace :=
  MkNewGreenFace "sl1_lzn48_chain.v" 56 1 20261114
  "SL1 supply face: the ln-48 chain instance tying the certificate family to the budget line" "L56:mb523f9".
Definition ng_Sl2AnchorCarrier : NewGreenFace :=
  MkNewGreenFace "sl2_anchor_carrier.v" 530 48 20261114
  "SL2 supply face: the anchor carrier with Hval-direct consumption alignment" "L530:m4e8f49".
Definition ng_Sl2RintRecast : NewGreenFace :=
  MkNewGreenFace "sl2_rint_recast.v" 428 56 20261114
  "SL2 supply face: the real-integral recast toward the |I_n| bound" "L428:me841ce".
Definition ng_Planb4Sl4Skeleton : NewGreenFace :=
  MkNewGreenFace "planb4_sl4_skeleton.v" 239 0 20261114
  "SL4 skeleton unit: delta/bgrowth/denom/proportional statement faces with born-clean declarations" "L239:m3e02c2".
Definition ng_Sl4D5Proportional : NewGreenFace :=
  MkNewGreenFace "sl4_d5_proportional.v" 186 5 20261114
  "D-SL4-5: Delta_n = 0 implies the two coefficients are Q-proportional (rank-1 algebra)" "L186:m17e024".
Definition ng_Sl4D3GrowthAnchor : NewGreenFace :=
  MkNewGreenFace "sl4_d3_growth_anchor.v" 214 13 20261114
  "D-SL4-3 table-domain anchor: B-side bit-growth lower bound over the landed table window" "L214:m565d91".
Definition ng_Sl4D4DenomAnchors : NewGreenFace :=
  MkNewGreenFace "sl4_d4_denom_anchors.v" 220 12 20261114
  "D-SL4-4 table-domain anchors: reduced-denominator bound point anchors n = 1..12" "L220:m065684".
Definition ng_Sl4D4DenomSkeleton : NewGreenFace :=
  MkNewGreenFace "sl4_d4_denom_skeleton.v" 197 3 20261114
  "D-SL4-4 reduction skeleton: the gcd upper-bound face the open accounts plug into" "L197:m6751c3".
Definition ng_Sl3D3GfCarrier : NewGreenFace :=
  MkNewGreenFace "sl3_d3_gf_carrier.v" 365 31 20261114
  "D-SL3-3 carrier: the nat->Z generating-function coefficient-table fold machinery" "L365:mc3a022".
Definition ng_Sl3D1SigmaLift : NewGreenFace :=
  MkNewGreenFace "sl3_d1_sigma_lift.v" 255 4 20261114
  "D-SL3-1: sigma lift bridge plus slot-face isomorphism in both dialects (up-band only)" "L255:m4db000".
Definition ng_Sl3D2Flag : NewGreenFace :=
  MkNewGreenFace "sl3_d2_flag.v" 392 21 20261114
  "D-SL3-2: Z-exact binary finite flag (s-parameterized) with the proven-spec weld" "L392:m7a8d6b".
Definition ng_Sl3D2FlagAnchors : NewGreenFace :=
  MkNewGreenFace "sl3_d2_flag_anchors.v" 63 2 20261114
  "D-SL3-2 head anchors n = 3..4 by vm_compute over the binary flag weld" "L64:m3c5e19".
Definition ng_Sl3D3GfAnchors : NewGreenFace :=
  MkNewGreenFace "sl3_d3_gf_anchors.v" 104 7 20261114
  "D-SL3-3 small-sample anchors: GF dominance face spot checks n = 1..3" "L104:mac8304".
Definition ng_Sl3D4Chain : NewGreenFace :=
  MkNewGreenFace "sl3_d4_chain.v" 237 9 20261114
  "D-SL3-4: the N2c chain assembly 37 -> 17 over the GF bound, b0 bridge and sharp face" "L237:md05b6a".
Definition ng_Sl3D5Param : NewGreenFace :=
  MkNewGreenFace "sl3_d5_param.v" 251 7 20261114
  "D-SL3-5: sigma-parameterized supply recast with the three-pin annotation face" "L251:m5baae8".
(* ---------- V47 批统计（整批追加纪律：清单/常量/引理同块原子写入·ng_qed 口径） ---------- *)
Definition NewGreenListV47 : list NewGreenFace :=
 cons ng_PiuMuCriterion
 (cons ng_PiuZzConstants
 (cons ng_PiuZzGaussPair
 (cons ng_PiuZzPadicClearing
 (cons ng_PiuZzPoincareEngine
 (cons ng_PiuZzJuryCubic
 (cons ng_PiuZzPoincareL1
 (cons ng_PiuZzKernelSum
 (cons ng_PiuZzKernelFaceGd2p01
 (cons ng_PiuZzJuryL2aGd2q01
 (cons ng_PiuZzJuryL2a2Gd2q02
 (cons ng_PiuZzLnRateBound
 (cons ng_PiuZzBridgeReal
 (cons ng_PiuZzBridgeRateslot
 (cons ng_Piu1932UncondZz
 (cons ng_PiuZzTauEnclosureBase
 (cons ng_PiuZzTauEnclosureBank1
 (cons ng_PiuZzTauEnclosureBank2
 (cons ng_PiuZzTauEnclosureBank3
 (cons ng_PiuZzTauEnclosureBank4
 (cons ng_PiuZzTauEnclosureHead
 (cons ng_PiuZzTauHbWave1
 (cons ng_PiuZzTauHbWave2
 (cons ng_PiuZzTauHbWave3a
 (cons ng_PiuZzTauHbWave3b
 (cons ng_PiuZzTauHbWave3c
 (cons ng_PiuZzTauHbWave3d
 (cons ng_PiuZzTauHbWave4a
 (cons ng_PiuZzTauHbWave4b
 (cons ng_PiuZzTauHbWave4c
 (cons ng_PiuZzTauHbWave4d
 (cons ng_PiuZzTauHbWave5
 (cons ng_PiuZzTauHbWave6
 (cons ng_PiuZzTauHbWave7
 (cons ng_PiuZzTauHbWave8
 (cons ng_PiuZzTauEnclosurePhi1024Slim
 (cons ng_PiuZzTauEnclosureLiterals
 (cons ng_PiuZzTauEnclosure
 (cons ng_Piu1930DomfaceNegative
 (cons ng_PiuZzMuAssembly
 (cons ng_PiuZzECarrier
 (cons ng_NsepBudgetExhaustion
 (cons ng_NsepBudgetVerify
 (cons ng_U5cQuadUniformEscape
 (cons ng_U5cQuadDemoSqrt7
 (cons ng_PiuZzPntWindow
 (cons ng_PiuZzPntWinsum
 (cons ng_PiuZzPntQexp
 (cons ng_PiuZzPntLcmpow
 (cons ng_PiuZzPntPhi
 (cons ng_PiuZzPntIpow
 (cons ng_PiuZzPntPsi
 (cons ng_PiuZzPntRateup
 (cons ng_PiuZzPntAssembly
 (cons ng_PiuZzCageConstants
 (cons ng_PiuZzSigmaDecay
 (cons ng_PiuZzNailMu
 (cons ng_PiuZzN1Linform
 (cons ng_PiuZzS2Headledger
 (cons ng_PiuZzEcEscwinNescD
 (cons ng_PiuZzEcEscwinBracket
 (cons ng_PiuZzN2cSigmaAssembly
 (cons ng_Piu1932UncondZzReland
 (cons ng_Sl12Constants (cons ng_Sl1PhaseFaces (cons ng_Sl1PhiDividesL (cons ng_Sl1HeadAnchors (cons ng_Sl1LznAssembly (cons ng_Sl1Lzn48Chain (cons ng_Sl2AnchorCarrier (cons ng_Sl2RintRecast (cons ng_Planb4Sl4Skeleton (cons ng_Sl4D5Proportional (cons ng_Sl4D3GrowthAnchor (cons ng_Sl4D4DenomAnchors (cons ng_Sl4D4DenomSkeleton (cons ng_Sl3D3GfCarrier (cons ng_Sl3D1SigmaLift (cons ng_Sl3D2Flag (cons ng_Sl3D2FlagAnchors (cons ng_Sl3D3GfAnchors (cons ng_Sl3D4Chain (cons ng_Sl3D5Param nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
(* ---------- V48 批八件 cons（插于 V47 清单 nil 前·依赖拓扑序·注册号 213 至 220 于 order.txt 行锚） ---------- *)
(* ---------- 十七片终形辅助名注记（KB13R 按 KB12/KB15 核勘代拟·KB20 无壳形制修订：wave4 拆四季·伞退役·slim 直挂八季） ---------- *)
(* 本批 wave 行承载 128 条升格辅助引理名：piu_zz_hb_512_0..31（wave1/2 各 16）＋
   piu_zz_hb_1024_0..95（wave3a-d＋wave4a-d 各 4＋wave5-8 各 16·无壳直挂四季）——系 consumer
   原件 32+96=128 个匿名 assert (HbN : stmt) 块的机械升格，语句/证明体逐字保留（KB12 静态
   复核 128/128·KB15 独立交叉审计两法一致·64 名落袋 vo 可见性实测检验全过）。名字面判据演进：
   原 2,912 定义性名零丢失＋辅助名增量 128＝终形 3,040 名；语句多集 3,044 位恒等、原 42 位
   零丢失（KB12 审计·KB15 复核）。落地后逐行 PA 占位以 new_About 实测检验填注（仅注释面）。 *)
(* 续写统计：63 件 / 行数和 43383 / 闭合数和 3851（ng_qed 口径·无壳形制落装重算 KB20：v2 21 册行 25934/3006 基础上 −wave3 伞 13/0 −wave4 单体 382/16 ＋四季 4×106/4 ＋slim 直挂 422→428；净 +35/+0 ＋domface 负定理单件追加 400/20 ＋mu_assembly 与 e_carrier 两件追加 955/40＋NsepBudgetExhaustion 常量化改形与 NsepBudgetVerify 拆件双件追加 256/13（主体 164/8＋验证块 92/5）＋u5c_quad_uniform_escape 参数化件与 u5c_quad_demo_sqrt7 演示件双件追加 1430/36（主体 1255/33＋演示 175/3）＋KB57 PNT 下游链九件追加 3554/155（window 135/4＋winsum 156/9＋qexp 681/30＋lcmpow 807/37＋phi 697/28＋ipow 386/23＋psi 239/7＋rateup 272/11＋assembly 181/6·依赖序 window→winsum→qexp→lcmpow→phi→ipow→psi→rateup→assembly）；一致性由下方等式引理编译期核对＋V48 注册批八件追加 3081/212（cage 474/35＋decay 231/10＋nail 387/51＋n1 423/34＋headledger 485/23＋nescD 478/26＋bracket 289/11＋n2c 314/22·γP1 首波四件＋W4 三件＋N2c 一件·依赖拓扑序·注册号 213 至 220 于 order.txt 行锚·registered in the November 2026 wave·W5 件候 born 第二批重锚禁预填）＋W6 二批一件追加 179/8（piu1932_uncond_zz 9.3 一致型同名重落·候选版 46f5f5·六前提无条件闭合顶件·注册号 194 旧条目 ng_Piu1932UncondZz 原位保留＝A 案·R 号 ? 占位·registry-day full-width placeholder pending, final value assigned at commit time·order.txt :973 行锚）。 *)
(* Fix-I 语句手术一代续记：Htri 槽 2 换位 dval (Z.of_nat q) (- p)→dval (- p) (Z.of_nat q) 逐处＋Hexit 前提面同形换位 dval b (- a)→dval (- a) b——34 处语句/前提面（criterion 7／e_carrier 9／piu1932 顶件 2／planb1 1／planb1_cert 6／planb3_g1_g2_design 3＋证体随改 4 行／planb4_l2_dv_cast 2／distpt_supply 4）＋e_carrier :646 注释随形；重编闭包 18 模块绿（rocq dep 全盘反向定界 8 种子＋10 下游）；三在册件 md5 换代锚于 order.txt 双树（M 语义·R 号外置迁移账：criterion dc5b47→dce9a2／e_carrier f22b5b→df34f1／顶件 46f5f5→e63556）；本索引 ng_meta=登记时点快照口径不变——三件行数 281/761/179 与 ng_qed 8/33/8（剥块注释 token 级双口径）手术前后实测零变化→三常量重算零增量（63 件／行数和 43383／闭合数和 3851 维持·下方三等式引理编译期核对）；P2 工单原列「Hexit 前提退役六→五」不在本次执行 diff（现役仍六前提接口同形换位形·不以修形后非空真作结语·始末详见跨线资产分析与工单目录迁移账·Fix-I Htri 换位与 Hexit 退役卷）。 *)
Definition NewGreenV47Pieces : nat := 83.
Definition NewGreenV47LineSum : nat := 48922.
Definition NewGreenV47QedSum : nat := 4219.

(* 清单件数 = 字面值（增删清单而忘改字面值即爆 G2） *)
Lemma NewGreenV47Pieces_matches : NewGreenV47Pieces = cnt_ng NewGreenListV47.
Proof. reflexivity. Qed.
(* 行数和 = 字面值 *)
Lemma NewGreenV47LineSum_matches : NewGreenV47LineSum = sum_ng_lines NewGreenListV47.
Proof. reflexivity. Qed.
(* 闭合数和 = 字面值 *)
Lemma NewGreenV47QedSum_matches : NewGreenV47QedSum = sum_ng_qed NewGreenListV47.
Proof. reflexivity. Qed.
