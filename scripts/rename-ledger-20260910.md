# CW220 合并轨源级改名清单（rename-ledger-20260910）

> Historical planning record (dated in filename). Preserved verbatim for provenance; current certification facts live in README.md section 2.

- 席位：合并轨命名空间修复席；裁决：**源级改名方案**（新库侧改名，基座/仓库已入库源只读为正名）
- 撞名宇宙：主会话 /tmp/collisions.txt 100 名（vs 基座）∪ 合并 34 模块闸门集 62 名（含模块互撞、Inductive 构造子 tid_refl/nle_n/nle_S/IOU_*、Record 投影/构造器）= **150 名去重**
- 改名落盘：attn 工作区 38 个 .v（定义+文件内引用+跨文件消费者重绑定；CW220_Extensions.v 内联副本同步）
- 改名后普查（_merge220_census.py：Module 隔离/Section 拍平、剥注释、构造子入账）：**vs 基座 A=0**；**合并闸门 B34=0**
- 行号说明：旧定义行号 = 改名前备份件（_merge220_renbak_20260910/）行号；词级替换不改行数

## 一、定义改名总表（旧名 | 新名 | 所在文件 | 定义类型 | 旧定义行号）

| 旧名 | 新名 | 所在文件 | 定义类型 | 旧定义行号 |
|---|---|---|---|---|
| sqrt_witness | dsq_sqrt_witness | UpDebtSqrtAbs.v | Definition | L35 |
| positive_dist | sigm_positive_dist | UpSigMigrate.v | Definition | L45 |
| boltzmann_dist | sigm_boltzmann_dist | UpSigMigrate.v | Definition | L46 |
| free_energy | sigm_free_energy | UpSigMigrate.v | Definition | L49 |
| normalized | sigm_normalized | UpSigMigrate.v | Definition | L52 |
| exp_pos_fn | sigm_exp_pos_fn | UpSigMigrate.v | Definition | L530 |
| partition_function_temp | sigm_partition_function_temp | UpSigMigrate.v | Definition | L531 |
| softmax_temp | sigm_softmax_temp | UpSigMigrate.v | Definition | L534 |
| boltzmann_factor | sigm_boltzmann_factor | UpSigMigrate.v | Definition | L537 |
| Z_thermo | sigm_Z_thermo | UpSigMigrate.v | Definition | L539 |
| boltzmann_dist_attn | sigm_boltzmann_dist_attn | UpSigMigrate.v | Definition | L541 |
| Z_aud | uab_Z_aud | UpAuditBridge.v | Definition | L72 |
| tid | rc_tid | UpRecast.v | Inductive | L53 |
| tid_refl | rc_tid_refl | UpRecast.v | ctor<tid> | L53 |
| tid_sym | rc_tid_sym | UpRecast.v | Definition | L55 |
| tid_trans | rc_tid_trans | UpRecast.v | Definition | L60 |
| tid_cong | rc_tid_cong | UpRecast.v | Definition | L67 |
| nle | rc_nle | UpRecast.v | Inductive | L74 |
| nle_n | rc_nle_n | UpRecast.v | ctor<nle> | L75 |
| nle_S | rc_nle_S | UpRecast.v | ctor<nle> | L76 |
| leb_refl_tid | rc_leb_refl_tid | UpRecast.v | Lemma | L87 |
| leb_S | rc_leb_S | UpRecast.v | Lemma | L92 |
| nle_lebF | rc_nle_lebF | UpRecast.v | Fixpoint | L104 |
| nle_leb | rc_nle_leb | UpRecast.v | Definition | L112 |
| nle_SS | rc_nle_SS | UpRecast.v | Lemma | L124 |
| nle_0 | rc_nle_0 | UpRecast.v | Lemma | L131 |
| nle_of_leb | rc_nle_of_leb | UpRecast.v | Lemma | L138 |
| nle_trans | rc_nle_trans | UpRecast.v | Lemma | L150 |
| nle_pred | rc_nle_pred | UpRecast.v | Lemma | L158 |
| nle_add_r | rc_nle_add_r | UpRecast.v | Lemma | L164 |
| tid | clq_tid | UpCLQuery.v | Inductive | L43 |
| tid_refl | clq_tid_refl | UpCLQuery.v | ctor<tid> | L43 |
| tid_sym | clq_tid_sym | UpCLQuery.v | Definition | L45 |
| tid_trans | clq_tid_trans | UpCLQuery.v | Definition | L50 |
| tid_cong | clq_tid_cong | UpCLQuery.v | Definition | L57 |
| tid_eq | clq_tid_eq | UpCLQuery.v | Lemma | L68 |
| nle | clq_nle | UpCLQuery.v | Inductive | L74 |
| nle_n | clq_nle_n | UpCLQuery.v | ctor<nle> | L75 |
| nle_S | clq_nle_S | UpCLQuery.v | ctor<nle> | L76 |
| leb_refl_tid | clq_leb_refl_tid | UpCLQuery.v | Lemma | L78 |
| leb_S | clq_leb_S | UpCLQuery.v | Lemma | L83 |
| nle_lebF | clq_nle_lebF | UpCLQuery.v | Fixpoint | L95 |
| nle_leb | clq_nle_leb | UpCLQuery.v | Definition | L103 |
| nle_0 | clq_nle_0 | UpCLQuery.v | Lemma | L115 |
| nle_SS | clq_nle_SS | UpCLQuery.v | Lemma | L122 |
| nle_of_leb | clq_nle_of_leb | UpCLQuery.v | Lemma | L130 |
| lebT | clq_lebT | UpCLQuery.v | Lemma | L143 |
| tid | slm_tid | UpSLM.v | Inductive | L53 |
| tid_refl | slm_tid_refl | UpSLM.v | ctor<tid> | L53 |
| tid_sym | slm_tid_sym | UpSLM.v | Definition | L55 |
| tid_trans | slm_tid_trans | UpSLM.v | Definition | L60 |
| tid_cong | slm_tid_cong | UpSLM.v | Definition | L67 |
| nle | slm_nle | UpSLM.v | Inductive | L74 |
| nle_n | slm_nle_n | UpSLM.v | ctor<nle> | L75 |
| nle_S | slm_nle_S | UpSLM.v | ctor<nle> | L76 |
| leb_refl_tid | slm_leb_refl_tid | UpSLM.v | Lemma | L92 |
| leb_S | slm_leb_S | UpSLM.v | Lemma | L97 |
| nle_lebF | slm_nle_lebF | UpSLM.v | Fixpoint | L109 |
| nle_leb | slm_nle_leb | UpSLM.v | Definition | L117 |
| nle_SS | slm_nle_SS | UpSLM.v | Lemma | L129 |
| nle_0 | slm_nle_0 | UpSLM.v | Lemma | L136 |
| nle_of_leb | slm_nle_of_leb | UpSLM.v | Lemma | L143 |
| lebT | slm_lebT | UpSLM.v | Lemma | L156 |
| nle_trans | slm_nle_trans | UpSLM.v | Lemma | L161 |
| nle_pred | slm_nle_pred | UpSLM.v | Lemma | L169 |
| nle_add_r | slm_nle_add_r | UpSLM.v | Lemma | L175 |
| nle_10_absurd | slm_nle_10_absurd | UpSLM.v | Lemma | L183 |
| zle_to_nle_S | slm_zle_to_nle_S | UpSLM.v | Lemma | L189 |
| to_nat_abs_pos | slm_to_nat_abs_pos | UpSLM.v | Lemma | L202 |
| real_pow_pos | bud_real_pow_pos | UpBudgetReal.v | Lemma | L68 |
| real_le_one_plus | bud_real_le_one_plus | UpBudgetReal.v | Lemma | L189 |
| boltzmann_factor | evict_boltzmann_factor | UpEvictId.v | Definition | L53 |
| Z_thermo | evict_Z_thermo | UpEvictId.v | Definition | L56 |
| boltzmann_dist_attn | evict_boltzmann_dist_attn | UpEvictId.v | Definition | L60 |
| evicted_transition | evict_evicted_transition | UpEvictId.v | Definition | L76 |
| evicted_partition | evict_evicted_partition | UpEvictId.v | Definition | L81 |
| evicted_boltzmann | evict_evicted_boltzmann | UpEvictId.v | Definition | L86 |
| db_breaking | evict_db_breaking | UpEvictId.v | Definition | L91 |
| evicted_partition_of | evict_evicted_partition_of | UpEvictId.v | Definition | L96 |
| real_partition_function_temp | gibbst_real_partition_function_temp | UpDebtGibbsT.v | Definition | L64 |
| real_partition_function_temp_pos | gibbst_real_partition_function_temp_pos | UpDebtGibbsT.v | Lemma | L67 |
| real_softmax_temp | gibbst_real_softmax_temp | UpDebtGibbsT.v | Definition | L75 |
| real_boltzmann_factor | gibbst_real_boltzmann_factor | UpDebtGibbsT.v | Definition | L139 |
| real_Z_thermo | gibbst_real_Z_thermo | UpDebtGibbsT.v | Definition | L143 |
| real_boltzmann_dist_attn | gibbst_real_boltzmann_dist_attn | UpDebtGibbsT.v | Definition | L148 |
| real_exp_neg_split | dpo_real_exp_neg_split | UpDPOLip.v | Lemma | L71 |
| redeem | dis_redeem | UpDissip.v | Definition | L620 |
| QId | st_QId | UpStopTime.v | Definition | L70 |
| Z_keep | kv_Z_keep | UpKVDrift.v | Definition | L67 |
| Z_keep_pos | kv_Z_keep_pos | UpKVDrift.v | Theorem | L127 |
| N_R | kv_N_R | UpKVDrift.v | Definition | L153 |
| N_R_pos | kv_N_R_pos | UpKVDrift.v | Theorem | L154 |
| U | kv_U | UpKVDrift.v | Definition | L158 |
| K_ev | kv_K_ev | UpKVDrift.v | Definition | L166 |
| tid | loeb_tid | UpLoeb.v | Inductive | L36 |
| tid_refl | loeb_tid_refl | UpLoeb.v | ctor<tid> | L36 |
| tid_sym | loeb_tid_sym | UpLoeb.v | Definition | L38 |
| tid_trans | loeb_tid_trans | UpLoeb.v | Definition | L43 |
| tid_cong | loeb_tid_cong | UpLoeb.v | Definition | L49 |
| tid_eq | loeb_tid_eq | UpLoeb.v | Lemma | L56 |
| ledger | loebd2_ledger | UpLoebD2.v | Definition | L222 |
| dotp | qkb_dotp | UpQKBound.v | Fixpoint | L255 |
| sql | qkb_sql | UpQKBound.v | Fixpoint | L261 |
| real_const_pos | qkb_real_const_pos | UpQKBound.v | Lemma | L357 |
| real_distrib_r | qkb_real_distrib_r | UpQKBound.v | Lemma | L377 |
| nat_to_R | qkb_nat_to_R | UpQKBound.v | Fixpoint | L416 |
| nat_to_R_pos | qkb_nat_to_R_pos | UpQKBound.v | Lemma | L432 |
| tid | refu_tid | UpRefuted.v | Inductive | L38 |
| tid_refl | refu_tid_refl | UpRefuted.v | ctor<tid> | L38 |
| tid_sym | refu_tid_sym | UpRefuted.v | Definition | L40 |
| tid_trans | refu_tid_trans | UpRefuted.v | Definition | L45 |
| tid_cong | refu_tid_cong | UpRefuted.v | Definition | L52 |
| nle | refu_nle | UpRefuted.v | Inductive | L69 |
| nle_n | refu_nle_n | UpRefuted.v | ctor<nle> | L70 |
| nle_S | refu_nle_S | UpRefuted.v | ctor<nle> | L71 |
| nle_10_absurd | refu_nle_10_absurd | UpRefuted.v | Lemma | L74 |
| nle_trans | refu_nle_trans | UpRefuted.v | Lemma | L79 |
| nle_0 | refu_nle_0 | UpRefuted.v | Lemma | L86 |
| nle_SS | refu_nle_SS | UpRefuted.v | Lemma | L93 |
| nle_add_r | refu_nle_add_r | UpRefuted.v | Lemma | L100 |
| iou | idl_iou | UpIDL.v | Inductive | L677 |
| IOU_NOPIN | idl_IOU_NOPIN | UpIDL.v | ctor<iou> | L678 |
| IOU_BAD | idl_IOU_BAD | UpIDL.v | ctor<iou> | L679 |
| IOU_REJ | idl_IOU_REJ | UpIDL.v | ctor<iou> | L680 |
| group_size | reqd_group_size | UpReqDist.v | Definition | L294 |
| positive_dist | reqd_positive_dist | UpReqDist.v | Definition | L1036 |
| normalized | reqd_normalized | UpReqDist.v | Definition | L1037 |
| boltzmann_dist | reqd_boltzmann_dist | UpReqDist.v | Definition | L1038 |
| free_energy | reqd_free_energy | UpReqDist.v | Definition | L1040 |
| entropy_dist | reqd_entropy_dist | UpReqDist.v | Definition | L1045 |
| energy_expectation | reqd_energy_expectation | UpReqDist.v | Definition | L1047 |
| cross_entropy | reqd_cross_entropy | UpReqDist.v | Definition | L1049 |
| temp_factor | alb_temp_factor | UpReqAlignRestB.v | Definition | L455 |
| partition_temp | alb_partition_temp | UpReqAlignRestB.v | Definition | L459 |
| markov_kernel | alb_markov_kernel | UpReqAlignRestB.v | Definition | L472 |
| max_markov_prob | alb_max_markov_prob | UpReqAlignRestB.v | Definition | L495 |
| minp_threshold | alb_minp_threshold | UpReqAlignRestB.v | Definition | L498 |
| minp_keep | alb_minp_keep | UpReqAlignRestB.v | Definition | L501 |
| minp_keep_dec | alb_minp_keep_dec | UpReqAlignRestB.v | Definition | L504 |
| minp_temp_sum | alb_minp_temp_sum | UpReqAlignRestB.v | Definition | L508 |
| minp_markov_kernel | alb_minp_markov_kernel | UpReqAlignRestB.v | Definition | L576 |
| minp_dropped_mass | alb_minp_dropped_mass | UpReqAlignRestB.v | Definition | L810 |
| topp_keep | alb_topp_keep | UpReqAlignRestB.v | Definition | L1044 |
| topp_keep_dec | alb_topp_keep_dec | UpReqAlignRestB.v | Definition | L1047 |
| topp_temp_sum | alb_topp_temp_sum | UpReqAlignRestB.v | Definition | L1051 |
| topp_markov_kernel | alb_topp_markov_kernel | UpReqAlignRestB.v | Definition | L1103 |
| combined_keep | alb_combined_keep | UpReqAlignRestB.v | Definition | L1127 |
| combined_keep_dec | alb_combined_keep_dec | UpReqAlignRestB.v | Definition | L1130 |
| combined_temp_sum | alb_combined_temp_sum | UpReqAlignRestB.v | Definition | L1141 |
| combined_markov_kernel | alb_combined_markov_kernel | UpReqAlignRestB.v | Definition | L1192 |
| NatLt_tk | alb_NatLt_tk | UpReqAlignRestB.v | Definition | L1217 |
| count_kernel_heavier | alb_count_kernel_heavier | UpReqAlignRestB.v | Fixpoint | L1222 |
| topk_keep | alb_topk_keep | UpReqAlignRestB.v | Definition | L1233 |
| topk_keep_dec | alb_topk_keep_dec | UpReqAlignRestB.v | Definition | L1236 |
| combined_topk_keep | alb_combined_topk_keep | UpReqAlignRestB.v | Definition | L1249 |
| combined_topk_keep_dec | alb_combined_topk_keep_dec | UpReqAlignRestB.v | Definition | L1252 |
| combined_topk_temp_sum | alb_combined_topk_temp_sum | UpReqAlignRestB.v | Definition | L1263 |
| combined_topk_markov_kernel | alb_combined_topk_markov_kernel | UpReqAlignRestB.v | Definition | L1318 |
| boltzmann_factor | evq_boltzmann_factor | UpEvictIdReq.v | Definition | L83 |
| Z_thermo | evq_Z_thermo | UpEvictIdReq.v | Definition | L86 |
| boltzmann_dist_attn | evq_boltzmann_dist_attn | UpEvictIdReq.v | Definition | L90 |
| evicted_transition | evq_evicted_transition | UpEvictIdReq.v | Definition | L109 |
| evicted_partition | evq_evicted_partition | UpEvictIdReq.v | Definition | L114 |
| evicted_boltzmann | evq_evicted_boltzmann | UpEvictIdReq.v | Definition | L119 |
| db_breaking | evq_db_breaking | UpEvictIdReq.v | Definition | L124 |
| evicted_partition_of | evq_evicted_partition_of | UpEvictIdReq.v | Definition | L129 |
| u_omd_pos_next | rsq_u_omd_pos_next | UpReqSampling.v | Lemma | L135 |
| u_r_kernel | rsq_u_r_kernel | UpReqSampling.v | Definition | L179 |
| u_r_nonneg | rsq_u_r_nonneg | UpReqSampling.v | Lemma | L183 |
| u_r_norm | rsq_u_r_norm | UpReqSampling.v | Lemma | L194 |
| u_tr_decomp | rsq_u_tr_decomp | UpReqSampling.v | Lemma | L238 |
| delta_absorb_u | rsq_delta_absorb_u | UpReqSampling.v | Lemma | L273 |
| u_step_decomp | rsq_u_step_decomp | UpReqSampling.v | Lemma | L293 |
| u_step_norm | rsq_u_step_norm | UpReqSampling.v | Lemma | L394 |
| u_abs_row | rsq_u_abs_row | UpReqSampling.v | Lemma | L461 |
| u_tv_contraction | rsq_u_tv_contraction | UpReqSampling.v | Lemma | L492 |
| u_titer | rsq_u_titer | UpReqSampling.v | Fixpoint | L646 |
| u_titer_norm | rsq_u_titer_norm | UpReqSampling.v | Lemma | L652 |
| u_tv_iter | rsq_u_tv_iter | UpReqSampling.v | Theorem | L662 |
| bs_list_sum | rsq_bs_list_sum | UpReqSampling.v | Fixpoint | L733 |
| exp_pos_fn | rsq_exp_pos_fn | UpReqSampling.v | Definition | L743 |
| bs_list_const_sum | rsq_bs_list_const_sum | UpReqSampling.v | Lemma | L783 |
| bs_list_le_const | rsq_bs_list_le_const | UpReqSampling.v | Lemma | L803 |
| bs_list_ge_const | rsq_bs_list_ge_const | UpReqSampling.v | Lemma | L835 |
| bs_nR_pos | rsq_bs_nR_pos | UpReqSampling.v | Lemma | L869 |
| bs_lo_pos | rsq_bs_lo_pos | UpReqSampling.v | Lemma | L882 |
| bs_hi_pos | rsq_bs_hi_pos | UpReqSampling.v | Lemma | L885 |
| bs_opp_lt | rsq_bs_opp_lt | UpReqSampling.v | Lemma | L889 |
| bs_lo_lt_hi | rsq_bs_lo_lt_hi | UpReqSampling.v | Lemma | L897 |
| bs_lo_hi_eq | rsq_bs_lo_hi_eq | UpReqSampling.v | Lemma | L907 |
| bs_delta_star_lt_one | rsq_bs_delta_star_lt_one | UpReqSampling.v | Lemma | L928 |
| bs_inv_hi_lo | rsq_bs_inv_hi_lo | UpReqSampling.v | Lemma | L935 |
| bs_factor_ge_lo | rsq_bs_factor_ge_lo | UpReqSampling.v | Lemma | L945 |
| bs_factor_le_hi | rsq_bs_factor_le_hi | UpReqSampling.v | Lemma | L953 |
| Zrow | rsq_Zrow | UpReqSampling.v | Definition | L961 |
| bs_Zrow_ge | rsq_bs_Zrow_ge | UpReqSampling.v | Lemma | L963 |
| bs_Zrow_le | rsq_bs_Zrow_le | UpReqSampling.v | Lemma | L973 |
| bs_Zrow_pos | rsq_bs_Zrow_pos | UpReqSampling.v | Lemma | L983 |
| bs_kernel | rsq_bs_kernel | UpReqSampling.v | Definition | L991 |
| bs_kernel_pos | rsq_bs_kernel_pos | UpReqSampling.v | Lemma | L994 |
| bs_kernel_nonneg | rsq_bs_kernel_nonneg | UpReqSampling.v | Lemma | L1002 |
| bs_kernel_row | rsq_bs_kernel_row | UpReqSampling.v | Lemma | L1007 |
| bs_Unif_norm | rsq_bs_Unif_norm | UpReqSampling.v | Lemma | L1030 |
| bs_minorization | rsq_bs_minorization | UpReqSampling.v | Lemma | L1074 |
| bounded_softmax_tv_contraction | rsq_bounded_softmax_tv_contraction | UpReqSampling.v | Theorem | L1140 |
| bounded_softmax_tv_iter | rsq_bounded_softmax_tv_iter | UpReqSampling.v | Theorem | L1153 |
| E_B_ent | req_rdf_E_B_ent | UpReqRDF.v | Definition | L1694 |
| Omega_total_ent | req_rdf_Omega_total_ent | UpReqRDF.v | Definition | L1695 |
| entropy_ent | req_rdf_entropy_ent | UpReqRDF.v | Definition | L1701 |
| iou_from | cwe_iou_from | CW220_Extensions.v | field<iou> | L13955 |
| iou_to | cwe_iou_to | CW220_Extensions.v | field<iou> | L13955 |
| iou_eps | cwe_iou_eps | CW220_Extensions.v | field<iou> | L13955 |
| iou_delta | cwe_iou_delta | CW220_Extensions.v | field<iou> | L13955 |
| iou_ref | cwe_iou_ref | CW220_Extensions.v | field<iou> | L13955 |
| dotp | cwe_dotp | CW220_Extensions.v | Fixpoint | L50 |
| sql | cwe_sql | CW220_Extensions.v | Fixpoint | L57 |
| sqrt_witness | cwe_sqrt_witness | CW220_Extensions.v | Definition | L577 |
| real_partition_function_temp | cwe_real_partition_function_temp | CW220_Extensions.v | Definition | L940 |
| real_partition_function_temp_pos | cwe_real_partition_function_temp_pos | CW220_Extensions.v | Lemma | L943 |
| real_softmax_temp | cwe_real_softmax_temp | CW220_Extensions.v | Definition | L951 |
| positive_dist | cwe_positive_dist | CW220_Extensions.v | Definition | L1455 |
| boltzmann_dist | cwe_boltzmann_dist | CW220_Extensions.v | Definition | L1456 |
| free_energy | cwe_free_energy | CW220_Extensions.v | Definition | L1459 |
| normalized | cwe_normalized | CW220_Extensions.v | Definition | L1462 |
| exp_pos_fn | cwe_exp_pos_fn | CW220_Extensions.v | Definition | L1940 |
| partition_function_temp | cwe_partition_function_temp | CW220_Extensions.v | Definition | L1941 |
| softmax_temp | cwe_softmax_temp | CW220_Extensions.v | Definition | L1944 |
| tid | cwe_tid | CW220_Extensions.v | Inductive | L7916 |
| tid_refl | cwe_tid_refl | CW220_Extensions.v | ctor<tid> | L7916 |
| tid_sym | cwe_tid_sym | CW220_Extensions.v | Definition | L7918 |
| tid_trans | cwe_tid_trans | CW220_Extensions.v | Definition | L7923 |
| tid_cong | cwe_tid_cong | CW220_Extensions.v | Definition | L7930 |
| nle | cwe_nle | CW220_Extensions.v | Inductive | L7937 |
| nle_n | cwe_nle_n | CW220_Extensions.v | ctor<nle> | L7938 |
| nle_S | cwe_nle_S | CW220_Extensions.v | ctor<nle> | L7939 |
| leb_refl_tid | cwe_leb_refl_tid | CW220_Extensions.v | Lemma | L7951 |
| leb_S | cwe_leb_S | CW220_Extensions.v | Lemma | L7956 |
| nle_lebF | cwe_nle_lebF | CW220_Extensions.v | Fixpoint | L7968 |
| nle_leb | cwe_nle_leb | CW220_Extensions.v | Definition | L7976 |
| nle_SS | cwe_nle_SS | CW220_Extensions.v | Lemma | L7988 |
| nle_0 | cwe_nle_0 | CW220_Extensions.v | Lemma | L7995 |
| nle_of_leb | cwe_nle_of_leb | CW220_Extensions.v | Lemma | L8002 |
| lebT | cwe_lebT | CW220_Extensions.v | Lemma | L8015 |
| nle_trans | cwe_nle_trans | CW220_Extensions.v | Lemma | L8021 |
| nle_pred | cwe_nle_pred | CW220_Extensions.v | Lemma | L8029 |
| nle_add_r | cwe_nle_add_r | CW220_Extensions.v | Lemma | L8035 |
| nle_10_absurd | cwe_nle_10_absurd | CW220_Extensions.v | Lemma | L8044 |
| zle_to_nle_S | cwe_zle_to_nle_S | CW220_Extensions.v | Lemma | L8050 |
| to_nat_abs_pos | cwe_to_nat_abs_pos | CW220_Extensions.v | Lemma | L8063 |
| tid_eq | cwe_tid_eq | CW220_Extensions.v | Lemma | L9706 |
| real_pow_pos | cwe_real_pow_pos | CW220_Extensions.v | Lemma | L10318 |
| real_le_one_plus | cwe_real_le_one_plus | CW220_Extensions.v | Lemma | L10439 |
| evicted_transition | cwe_evicted_transition | CW220_Extensions.v | Definition | L12566 |
| evicted_partition | cwe_evicted_partition | CW220_Extensions.v | Definition | L12571 |
| evicted_boltzmann | cwe_evicted_boltzmann | CW220_Extensions.v | Definition | L12576 |
| db_breaking | cwe_db_breaking | CW220_Extensions.v | Definition | L12581 |
| evicted_partition_of | cwe_evicted_partition_of | CW220_Extensions.v | Definition | L12586 |
| real_boltzmann_factor | cwe_real_boltzmann_factor | CW220_Extensions.v | Definition | L13004 |
| real_Z_thermo | cwe_real_Z_thermo | CW220_Extensions.v | Definition | L13008 |
| real_boltzmann_dist_attn | cwe_real_boltzmann_dist_attn | CW220_Extensions.v | Definition | L13013 |
| real_exp_neg_split | cwe_real_exp_neg_split | CW220_Extensions.v | Lemma | L13158 |
| iou | cwe_iou | CW220_Extensions.v | Record | L13954 |
| mk_iou | cwe_mk_iou | CW220_Extensions.v | ctor<iou> | L13954 |
| redeem | cwe_redeem | CW220_Extensions.v | Definition | L14218 |
| fep_partition_condition | ufep_fep_partition_condition | UpFEP.v | Lemma | L52 |
| fep_align | ufep_fep_align | UpFEP.v | Lemma | L60 |
| fep_F_ext | ufep_fep_F_ext | UpFEP.v | Lemma | L70 |
| attention_minimizes_free_energy_unique | ufep_attention_minimizes_free_energy_unique | UpFEP.v | Theorem | L84 |
| bs_kernel_row_is_softmax_temp | ufep_bs_kernel_row_is_softmax_temp | UpFEP.v | Theorem | L140 |
| fep_partition_condition | uex_fep_partition_condition | UpExtras.v | Lemma | L64 |
| fep_align | uex_fep_align | UpExtras.v | Lemma | L73 |
| fep_F_ext | uex_fep_F_ext | UpExtras.v | Lemma | L83 |

## 二、跨文件消费者引用位点（非定义者文件·按 Require 序绑定到被改模块）

| 文件 | 被改旧名 | 该文件改写处数 | 绑定到 |
|---|---|---|---|
| UpFirewallReq.v | entropy_dist | 1 | → 绑定模块新名 |
| UpIDL.v | nle | 5 | → 绑定模块新名 |
| UpIDL.v | nle_0 | 1 | → 绑定模块新名 |
| UpIDL.v | nle_S | 15 | → 绑定模块新名 |
| UpIDL.v | nle_leb | 4 | → 绑定模块新名 |
| UpIDL.v | nle_n | 6 | → 绑定模块新名 |
| UpIDL.v | tid | 97 | → 绑定模块新名 |
| UpIDL.v | tid_cong | 1 | → 绑定模块新名 |
| UpIDL.v | tid_eq | 47 | → 绑定模块新名 |
| UpIDL.v | tid_refl | 51 | → 绑定模块新名 |
| UpIDL.v | tid_sym | 1 | → 绑定模块新名 |
| UpIDL.v | tid_trans | 2 | → 绑定模块新名 |
| UpIDL_P2.v | nle | 5 | → 绑定模块新名 |
| UpIDL_P2.v | nle_0 | 2 | → 绑定模块新名 |
| UpIDL_P2.v | nle_S | 10 | → 绑定模块新名 |
| UpIDL_P2.v | nle_leb | 2 | → 绑定模块新名 |
| UpIDL_P2.v | nle_n | 5 | → 绑定模块新名 |
| UpIDL_P2.v | tid | 104 | → 绑定模块新名 |
| UpIDL_P2.v | tid_cong | 1 | → 绑定模块新名 |
| UpIDL_P2.v | tid_eq | 69 | → 绑定模块新名 |
| UpIDL_P2.v | tid_refl | 56 | → 绑定模块新名 |
| UpIDL_P2.v | tid_sym | 3 | → 绑定模块新名 |
| UpIDL_P2.v | tid_trans | 9 | → 绑定模块新名 |
| UpLoebD2.v | tid | 45 | → 绑定模块新名 |
| UpLoebD2.v | tid_cong | 1 | → 绑定模块新名 |
| UpLoebD2.v | tid_eq | 15 | → 绑定模块新名 |
| UpLoebD2.v | tid_refl | 9 | → 绑定模块新名 |
| UpLoebD2.v | tid_sym | 2 | → 绑定模块新名 |
| UpLoebD2.v | tid_trans | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | delta_absorb_u | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_abs_row | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_omd_pos_next | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_r_kernel | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_r_nonneg | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_r_norm | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_step_decomp | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_step_norm | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_titer | 1 | → 绑定模块新名 |
| UpReqAttnIter.v | u_titer_norm | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_tr_decomp | 2 | → 绑定模块新名 |
| UpReqAttnIter.v | u_tv_contraction | 4 | → 绑定模块新名 |
| UpReqAttnIter.v | u_tv_iter | 1 | → 绑定模块新名 |
| UpReqFEPAttn.v | normalized | 1 | → 绑定模块新名 |
| UpReqMinPAntitone.v | markov_kernel | 4 | → 绑定模块新名 |
| UpReqMinPAntitone.v | max_markov_prob | 4 | → 绑定模块新名 |
| UpReqMinPAntitone.v | minp_temp_sum | 1 | → 绑定模块新名 |
| UpReqMinPAntitone.v | partition_temp | 1 | → 绑定模块新名 |
| UpReqMinPAntitone.v | temp_factor | 5 | → 绑定模块新名 |
| UpReqMinPProjB.v | Z_aud | 2 | → 绑定模块新名 |
| UpReqSLM.v | markov_kernel | 1 | → 绑定模块新名 |
| UpReqSLM.v | partition_temp | 1 | → 绑定模块新名 |
| UpReqSLM.v | temp_factor | 1 | → 绑定模块新名 |
| UpReqSqPos.v | group_size | 8 | → 绑定模块新名 |
| UpReqTempEntropy.v | energy_expectation | 11 | → 绑定模块新名 |
| UpReqTempEntropy.v | entropy_dist | 29 | → 绑定模块新名 |
| UpReqTempEntropy.v | normalized | 9 | → 绑定模块新名 |
| UpReqTempEntropy.v | positive_dist | 11 | → 绑定模块新名 |
| UpReqZAuto.v | exp_pos_fn | 2 | → 绑定模块新名 |
| UpReqZAuto.v | partition_function_temp | 9 | → 绑定模块新名 |
| UpReqZAuto.v | softmax_temp | 1 | → 绑定模块新名 |
| UpReqZPosI.v | boltzmann_dist | 2 | → 绑定模块新名 |
| UpReqZPosI.v | positive_dist | 1 | → 绑定模块新名 |
| UpReqZPosI2.v | evicted_partition | 1 | → 绑定模块新名 |
| UpReqZPosI2.v | exp_pos_fn | 4 | → 绑定模块新名 |
| UpReqZPosI2.v | partition_function_temp | 2 | → 绑定模块新名 |

## 三、统计

- 定义改名处数：**272**（涉及 152 个不同旧名；构造子/投影计入）
- 连带引用改写：38 文件合计 **4029 行**（词级替换；明细 _merge220_rename_stats.json）
- 消费者重绑定处数（非定义者文件）：**65**
- 涉及文件数：**38**（含 CW220_Extensions.v 内联副本同步；备份 _merge220_renbak_20260910/ 为回滚点）

## 四、范围外登记（不改名，供论文线/后续会话知悉）

- AttnDoeblin.v / AttnHardLimit218.v / AttnSqrt.v / UpLogMono.v / UpStepKL.v：attn 遗留线（非 Up*/CW220_Extensions 改名域）；与基座同名=基座已内联其内容的垫片重影，.vo Import 遮蔽合法，合并轨不内联
- CW214KL_scan.v（仓库只读）：与基座行号对齐的同内容快照，.vo 依赖垫片
- UpIDL_P2.v：attn 实验件（引用 UpCLQuery），已随改名重绑定 clq_tid 系
- 受影响索引文件（一律未改）：releases/论文3-artifact-行号索引-20260909.md（旧名/旧行号）；releases/CW220_Extensions.v（仓库只读副本，待捆绑时与 attn 版对齐）；旧合并轨行号索引自本日起以 .bak 为准

## 五、重编四关状态表（38 改名件 + 13 陈旧闭包件 = 51 件；@2026-09-10）

| 文件 | G2 编译 | G2b Print Assumptions 旗舰 | G4 coqchk(-norec) | 备注 |
|---|---|---|---|---|
| UpDebtSqrtAbs.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpSigMigrate.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpAuditBridge.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpRecast.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpCLQuery.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpSLM.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpBudgetReal.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpArchAttn.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpConstitution.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpEvictId.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpDebtGibbsT.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpDPOLip.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpDissip.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpStopTime.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpKVDrift.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpLoeb.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpLoebD2.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpQKBound.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpRefuted.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpIDL.v | ❌EXIT=1 | — | — |  **已改未验**：G2 失败 L510 `variable z2 not found`（pin_P1_in_val，疑与 destruct 分支模式和 clq_tid 重绑定交互，待下会话定向排查） |
| UpReqDist.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqTempEntropy.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqAlignRestB.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpEvictIdReq.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqSampling.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqSLM.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqCauchy.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqMisc5.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqMisc5B.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqAttnIter.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqAttnGibbs.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqMinPAntitone.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpEntropyGainReq.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpFirewallReq.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqRDF.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqPPOPlain.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| CW220_Extensions.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqU2.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqFEPAttn.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqSqPos.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqSumD.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqZPosD.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqZPosI.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqBranchPos.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqZPosI2.v | ❌EXIT=1 | — | — |  限定名引用补改（UpSigMigrate.sigm_Z_thermo / UpEvictIdReq.evq_Z_thermo）后单独复验绿 |
| UpReqZAuto.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqLogLinD.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpExtras.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpFEP.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpIDL_P2.v | ✅ | — | EXIT=0 OK=1 | ✅  |
| UpReqMinPProjB.v | ✅ | — | EXIT=0 OK=1 | ✅  |

- G1 禁词（Axiom/Parameter/Conjecture/Admitted/admit 行首）：51 件全 0
- G3 提取探针（改名后跨模块常量 sigm_boltzmann_dist / qkb_dotp / uab_Z_aud）：magic=0、axiom 关键字=0（_merge220_g3probe 日志，已清理现场）
- 合并轨产物：GATE-OK（基座+34 逐名零撞名）· audit.awk DUP_ROOT=空 · DUP_MOD=空 · 结构 166S/10M/176E 栈平衡 · G1=0 · 全量 coqc 后台在飞

## 六、合并轨重生成与全量编译状态（截至 2026-09-10 12:20，硬截止交付）
- 产物：releases/CW_ConstructiveWorld_220.v 已重生成（136931 行，SHA1=3c8647707b465b7a61a6aa8ecdbe902ff3c51b19；旧件 .bak）；生成器 scripts/merge220.sh，撞名闸门 GATE-OK（基座+34 逐名零撞名）· audit.awk DUP_ROOT=空/DUP_MOD=空/结构 166S/10M/176E 平衡 · G1 禁词=0
- 全量编译（coqc 9.1，cpu_guard 后台）：**未收绿**。两次推进：①首跑到 L114300 暴露生成器剥 Require 正则漏 CW214KL_scan（已修复重生成）；②二跑到 **L116454**（UpMinP 块，~85%）停于 `IH 0` 的 0 被精灵化为 Q（flat 语境与 .vo 语境 Open/Bind Scope 差异；该区域旧 137085 行手拼件从未编译到达过，非本次改名回归——UpMinP 非改名件且 .vo 形态四关绿）。日志：releases/_merge220_compile.log
- 待下会话两件事：① UpIDL.v pin_P1_in_val L509-510 z2 引入模式修复（**Sep 8 06:19 预存缺陷**，_UpIDL.v.compile.log 同错实证，非改名回归；修后走四关）；② UpMinP 块 flat 语境 scope 漂移（块首补 Local Open Scope nat_scope 或 0%nat 标注），随后 merge220.sh 重生成 + 全量编译 + coqchk + G3 收口
