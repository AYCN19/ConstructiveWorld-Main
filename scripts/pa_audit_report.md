# Print Assumptions 全量批审计报告（pa_audit）

> Historical audit record (Print Assumptions full-tree batch report; the filename carries no date — the generation time is in the body below). Preserved verbatim for provenance; current certification facts live in README.md section 2.

- 生成时间：2026-09-11 02:18:55 +0800；总耗时：4847s（含 guard 热等待 85s（按 guard cooling 行计数 × CoolSec=5 估算））
- 脚本：scripts/pa_audit.sh（SHA1 `94ccaf54da059e3a04ea7bafd2d2a2533fdb9720`）；清单：scripts/pa_theorems.txt（193 条）
- 工具链：The Rocq Prover, version 9.0.1（Windows 走 9.0 完整路径 `C:/Rocq-Platform~9.0~2025.08/bin`，禁裸 PATH——9.1 coqchk 对 9.0 产物报 bad version 90001；CI ubuntu 走 setup 的 9.0）
- root：ConstructiveWorld_vo（/d/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo）；guard：LoadLimit=60 / CoreN=3（cpu_guard.ps1，root 外既定件）

## 总判定

- **Closed 193 / Fail 0 / EXEMPT(避让) 0，共 193 条**；覆盖模块 89 个（基座 CW_ConstructiveWorld_219 ＋ scripts/order.txt 全部 ＋ 清单所涉在树模块；避让剔除：UpMinP UpIDL ）
- 零承认 grep（行首口径 `Axiom|Admitted|Parameter|Conjecture|Abort`）：**89 个源文件扫描，命中 0**

## 编译动作（.vo 缺失或旧于 .v 方编译；一律 guard 包装 + 9.0 显式路径）

- 新编译 0：无
- 编译失败 1：UpReqTempInterp 
- 免编复用（.vo 不旧于 .v）88
- 避让未编（合并轨收口席修复中，跳编跳查）：UpMinP UpIDL 

## 逐定理结果（名字 | 所在模块 | Closed/Fail | 依赖 axiom 数）

| 名字 | 所在模块 | 结果 | 依赖 axiom 数 |
|---|---|---|---|
| free_energy_kl_decomp | CW_ConstructiveWorld_219 | Closed | 0 |
| gibbs_inequality | CW_ConstructiveWorld_219 | Closed | 0 |
| min_free_energy_is_boltzmann | CW_ConstructiveWorld_219 | Closed | 0 |
| pi_star_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| pi_star_normalized | CW_ConstructiveWorld_219 | Closed | 0 |
| free_energy_ext | CW_ConstructiveWorld_219 | Closed | 0 |
| ppo_conservative | CW_ConstructiveWorld_219 | Closed | 0 |
| exact_improvement_identity | CW_ConstructiveWorld_219 | Closed | 0 |
| kl_penalty_sufficient | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_total_loss_monotone | CW_ConstructiveWorld_219 | Closed | 0 |
| rlhf_free_energy_kl | CW_ConstructiveWorld_219 | Closed | 0 |
| rlhf_suboptimality_gap | CW_ConstructiveWorld_219 | Closed | 0 |
| rlhf_policy_improvement | CW_ConstructiveWorld_219 | Closed | 0 |
| ppo_surrogate_conservative | CW_ConstructiveWorld_219 | Closed | 0 |
| Z_rel_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| boltzmann_factor_bridge | CW_ConstructiveWorld_219 | Closed | 0 |
| reward_expand | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_backward_kl_step_le | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_kl_geom_iter | CW_ConstructiveWorld_219 | Closed | 0 |
| grpo_variance_identity | CW_ConstructiveWorld_219 | Closed | 0 |
| group_variance_identity | CW_ConstructiveWorld_219 | Closed | 0 |
| real_gibbs_inequality_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| real_dpo_loss_at_pi_star | CW_ConstructiveWorld_219 | Closed | 0 |
| real_rlhf_optimal_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| real_square_nonneg_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| real_log_differentiable | CW_ConstructiveWorld_219 | Closed | 0 |
| entropy_deficit_kl | CW_ConstructiveWorld_219 | Closed | 0 |
| entropy_temp_explicit | CW_ConstructiveWorld_219 | Closed | 0 |
| relative_entropy_temp_decomp | CW_ConstructiveWorld_219 | Closed | 0 |
| energy_exp_temp_mono | CW_ConstructiveWorld_219 | Closed | 0 |
| evidence_gap_kl | CW_ConstructiveWorld_219 | Closed | 0 |
| steady_state_boltzmann_attn | CW_ConstructiveWorld_219 | Closed | 0 |
| attention_tv_contraction | CW_ConstructiveWorld_219 | Closed | 0 |
| attention_iterate_converges | CW_ConstructiveWorld_219 | Closed | 0 |
| eviction_db_breaking_bound | CW_ConstructiveWorld_219 | Closed | 0 |
| top_k_tail_bound | CW_ConstructiveWorld_219 | Closed | 0 |
| tail_plus_kept_full | CW_ConstructiveWorld_219 | Closed | 0 |
| top_k_majorization | CW_ConstructiveWorld_219 | Closed | 0 |
| top_k_swap_no_gain | CW_ConstructiveWorld_219 | Closed | 0 |
| top_k_majorization_mem | CW_ConstructiveWorld_219 | Closed | 0 |
| topk_tv_identity_strict | CW_ConstructiveWorld_219 | Closed | 0 |
| minp_markov_kernel_normalized | CW_ConstructiveWorld_219 | Closed | 0 |
| minp_markov_kernel_keep_ge_full | CW_ConstructiveWorld_219 | Closed | 0 |
| minp_dropped_mass_le_inv_vocab_size | CW_ConstructiveWorld_219 | Closed | 0 |
| real_energy_lipschitz_scaled | CW_ConstructiveWorld_219 | Closed | 0 |
| real_boltzmann_upper | CW_ConstructiveWorld_219 | Closed | 0 |
| attention_step | CW_ConstructiveWorld_219 | Closed | 0 |
| db_breaking | CW_ConstructiveWorld_219 | Closed | 0 |
| cauchy_real_exp_zero | CW_ConstructiveWorld_219 | Closed | 0 |
| esq_eq_corr | CW_ConstructiveWorld_219 | Closed | 0 |
| exp_even_neg_nonneg | CW_ConstructiveWorld_219 | Closed | 0 |
| exp_even_neg_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| exp_partial_tail_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| cauchy_real_exp_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| cauchy_real_exp_plus | CW_ConstructiveWorld_219 | Closed | 0 |
| cauchy_real_exp_mono | CW_ConstructiveWorld_219 | Closed | 0 |
| real_cos_three_halves_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| real_sin_pos_lt_two | CW_ConstructiveWorld_219 | Closed | 0 |
| real_cos_strict_decr | CW_ConstructiveWorld_219 | Closed | 0 |
| real_cos_pi_half_zero | CW_ConstructiveWorld_219 | Closed | 0 |
| cos_pi_half_unique | CW_ConstructiveWorld_219 | Closed | 0 |
| real_pi_leibniz_lt_ten_thirds | CW_ConstructiveWorld_219 | Closed | 0 |
| real_pi_leibniz_between_tenthirds | CW_ConstructiveWorld_219 | Closed | 0 |
| real_sin_pi_half_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| real_sin_pi_half_one | CW_ConstructiveWorld_219 | Closed | 0 |
| real_pi_geom_gt_three | CW_ConstructiveWorld_219 | Closed | 0 |
| real_pi_geom_lt_ten_thirds | CW_ConstructiveWorld_219 | Closed | 0 |
| real_pi_geom_between | CW_ConstructiveWorld_219 | Closed | 0 |
| cos_pi_half_unique_widened | CW_ConstructiveWorld_219 | Closed | 0 |
| real_exp_deriv_eq_self | CW_ConstructiveWorld_219 | Closed | 0 |
| real_exp_diff_with_deriv_self | CW_ConstructiveWorld_219 | Closed | 0 |
| rs_add_sin | CW_ConstructiveWorld_219 | Closed | 0 |
| real_pi_geom | CW_ConstructiveWorld_219 | Closed | 0 |
| iterate_cauchy | CW_ConstructiveWorld_219 | Closed | 0 |
| iterate_lim_exists | CW_ConstructiveWorld_219 | Closed | 0 |
| grad_squeeze_zero | CW_ConstructiveWorld_219 | Closed | 0 |
| dynamics_converges | CW_ConstructiveWorld_219 | Closed | 0 |
| gradient_zero_neg_entropy_truth | CW_ConstructiveWorld_219 | Closed | 0 |
| gradient_zero_unique | CW_ConstructiveWorld_219 | Closed | 0 |
| unique_attractor | CW_ConstructiveWorld_219 | Closed | 0 |
| attractor_converges_unique_truth | CW_ConstructiveWorld_219 | Closed | 0 |
| rlhf_optimal | CW_ConstructiveWorld_219 | Closed | 0 |
| rlhf_optimal_unique | CW_ConstructiveWorld_219 | Closed | 0 |
| rlhf_optimal_value | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_kl_geom_step | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_backward_kl_step | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_backward_kl_step_beta | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_backward_kl_iter_le | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_gap_mono | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_gap_diff | CW_ConstructiveWorld_219 | Closed | 0 |
| policy_iter_norm | CW_ConstructiveWorld_219 | Closed | 0 |
| projected_distribution_minimizes_kl | CW_ConstructiveWorld_219 | Closed | 0 |
| ppo_is_decomp | CW_ConstructiveWorld_219 | Closed | 0 |
| clip_error_nonneg | CW_ConstructiveWorld_219 | Closed | 0 |
| ppo_clipped_improvement | CW_ConstructiveWorld_219 | Closed | 0 |
| real_step_kl_eta_bound_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_optimal | CW_ConstructiveWorld_219 | Closed | 0 |
| PropositionConvergenceCore.boltzmann_factor_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| attention_is_gibbs | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_loss_at_pi_star | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_reward_is_implicit | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_reward_recovers_up_to_baseline | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_reward_relative_exact | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_reward_diff_is_log_ratio_diff | CW_ConstructiveWorld_219 | Closed | 0 |
| real_dpo_loss_pi_star_bounded_both | CW_ConstructiveWorld_219 | Closed | 0 |
| real_dpo_reward_recovers_up_to_baseline | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_loss_iter_step_le | CW_ConstructiveWorld_219 | Closed | 0 |
| dpo_loss_iter_mono | CW_ConstructiveWorld_219 | Closed | 0 |
| ppo_monotonic_improvement | CW_ConstructiveWorld_219 | Closed | 0 |
| ppo_surrogate_raw_is_value_improvement | CW_ConstructiveWorld_219 | Closed | 0 |
| real_ppo_conservative_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| std_ppo_conservative | CW_ConstructiveWorld_219 | Closed | 0 |
| grpo_advantage_zero_mean | CW_ConstructiveWorld_219 | Closed | 0 |
| group_variance_le_raw_second_moment | CW_ConstructiveWorld_219 | Closed | 0 |
| real_grpo_advantage_zero_mean | CW_ConstructiveWorld_219 | Closed | 0 |
| UpExtras219.counter_ex_indicator_sum_two | CW_ConstructiveWorld_219 | Closed | 0 |
| UpExtras219.counter_ex_reward_sum_two_c | CW_ConstructiveWorld_219 | Closed | 0 |
| real_softplus_sigmoid_eq | CW_ConstructiveWorld_219 | Closed | 0 |
| real_sigmoid_deriv_mass_pos | CW_ConstructiveWorld_219 | Closed | 0 |
| real_dpo_logit_loss_decr | CW_ConstructiveWorld_219 | Closed | 0 |
| real_interp_Z_le_one_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| real_exp_two_point_cvx_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| real_amgm_pointwise_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| UpGRPO219.grpo_count_one | CW_ConstructiveWorld_219 | Closed | 0 |
| UpGRPO219.grpo_indicator_sum_one | CW_ConstructiveWorld_219 | Closed | 0 |
| UpGRPO219.grpo_uniform_mass | CW_ConstructiveWorld_219 | Closed | 0 |
| fep_align | CW_ConstructiveWorld_219 | Closed | 0 |
| gibbs_equality | CW_ConstructiveWorld_219 | Closed | 0 |
| free_energy_min_unique | CW_ConstructiveWorld_219 | Closed | 0 |
| max_entropy_is_boltzmann | CW_ConstructiveWorld_219 | Closed | 0 |
| elbo_lower_bound | CW_ConstructiveWorld_219 | Closed | 0 |
| elbo_tight | CW_ConstructiveWorld_219 | Closed | 0 |
| steady_state_boltzmann | CW_ConstructiveWorld_219 | Closed | 0 |
| training_equivalence | CW_ConstructiveWorld_219 | Closed | 0 |
| bs_minorization | CW_ConstructiveWorld_219 | Closed | 0 |
| u_tv_contraction | CW_ConstructiveWorld_219 | Closed | 0 |
| u_tv_iter | CW_ConstructiveWorld_219 | Closed | 0 |
| bounded_softmax_tv_contraction | CW_ConstructiveWorld_219 | Closed | 0 |
| bounded_softmax_tv_iter | CW_ConstructiveWorld_219 | Closed | 0 |
| eviction_steady_deviation | CW_ConstructiveWorld_219 | Closed | 0 |
| eviction_partition_monotone | CW_ConstructiveWorld_219 | Closed | 0 |
| eviction_partition_le_full | CW_ConstructiveWorld_219 | Closed | 0 |
| minp_markov_kernel_nonneg | CW_ConstructiveWorld_219 | Closed | 0 |
| real_attention_is_gibbs | CW_ConstructiveWorld_219 | Closed | 0 |
| real_steady_state_boltzmann_attn | CW_ConstructiveWorld_219 | Closed | 0 |
| real_top_k_majorization | CW_ConstructiveWorld_219 | Closed | 0 |
| real_boltzmann_diff_bound | CW_ConstructiveWorld_219 | Closed | 0 |
| real_db_breaking_bound_eps | CW_ConstructiveWorld_219 | Closed | 0 |
| real_minp_markov_kernel_normalized | CW_ConstructiveWorld_219 | Closed | 0 |
| e_sq_expand | CW_ConstructiveWorld_219 | Closed | 0 |
| o_sq_expand | CW_ConstructiveWorld_219 | Closed | 0 |
| iterate_cauchy_explicit_N | CW_ConstructiveWorld_219 | Closed | 0 |
| iterate_grad_abs_mono | CW_ConstructiveWorld_219 | Closed | 0 |
| real_cauchy_schwarz | UpCS | Closed | 0 |
| real_cauchy_schwarz_lt | UpCS | Closed | 0 |
| real_cauchy_schwarz_reversed_false | UpCS | Closed | 0 |
| qk_logits_bounded | UpQKBound | Closed | 0 |
| inner_sq_norm | UpQKBound | Closed | 0 |
| real_logit_bound_of_norm_bounds | UpQKBound | Closed | 0 |
| attention_iterate_converges_real | UpArchAttn | Closed | 0 |
| eviction_db_breaking_zero | UpEvictId | Closed | 0 |
| kv_drift_bound | UpKVDrift | Closed | 0 |
| kv_drift_bound_tv | UpKVDrift | Closed | 0 |
| temp_window_T_infty | CW220_Extensions | Closed | 0 |
| real_scale_temp_duality | CW220_Extensions | Closed | 0 |
| real_attention_is_gibbs_temp | UpDebtGibbsT | Closed | 0 |
| req_rlhf_optimal | UpReqAlign | Closed | 0 |
| req_rlhf_optimal_unique | UpReqAlign | Closed | 0 |
| req_policy_iter_kl_geom_step | UpReqAlign | Closed | 0 |
| req_policy_iter_kl_geom_iter | UpReqAlign | Closed | 0 |
| req2_backward_kl_step | UpReqAlign3 | Closed | 0 |
| r2_backward_kl_step_le | UpReqAlign3 | Closed | 0 |
| r2_rlhf_policy_improvement | UpReqAlign3 | Closed | 0 |
| r2_backward_kl_iter_le | UpReqAlign3 | Closed | 0 |
| req2_gap_mono | UpReqAlign3 | Closed | 0 |
| req_min_free_energy_is_boltzmann | UpReqDist | Closed | 0 |
| req_gibbs_inequality | UpReqDist | Closed | 0 |
| req_free_energy_kl_decomp | UpReqDist | Closed | 0 |
| req_group_variance_identity | UpReqDist | Closed | 0 |
| req_grpo_variance_identity | UpReqDist | Closed | 0 |
| req_entropy_temp_explicit | UpReqTempEntropy | Closed | 0 |
| req_relative_entropy_temp_decomp | UpReqTempEntropy | Closed | 0 |
| req_energy_exp_temp_mono | UpReqTempEntropy | Closed | 0 |
| req_attention_is_gibbs_temp | UpSigMigrate | Closed | 0 |
| req_attention_minimizes_free_energy_unique | UpReqFEPAttn | Closed | 0 |
| req_fep_partition_condition | UpReqFEPAttn | Closed | 0 |
| req_fep_partition_condition_logz | UpReqFEPAttn | Closed | 0 |
| geod_step_kl_eta_bound_eps | UpReqGeomD | Closed | 0 |
| rdl_dpo_total_loss_monotone | UpReqDpoLoss | Closed | 0 |
| real_rlhf_optimal_B | UpRealLeB | Closed | 0 |
| real_ppo_conservative_B | UpRealLeB | Closed | 0 |
| real_le_closure_b | UpRealLeB | Closed | 0 |
| rpl_ppo_clipped_improvement | UpReqPPOPlain | Closed | 0 |


## coqchk 汇总

coqchk（Rocq 9.0 工具链，-silent -o 输出假设清单；owner 模块合并单趟：CW_ConstructiveWorld_219,UpCS,UpQKBound,UpArchAttn,UpEvictId,UpKVDrift,CW220_Extensions,UpDebtGibbsT,UpReqAlign,UpReqAlign3,UpReqDist,UpReqTempEntropy,UpSigMigrate,UpReqFEPAttn,UpReqGeomD,UpReqDpoLoss,UpRealLeB,UpReqPPOPlain）：**PASS**（rc=0；成功行被 -silent 抑制，以 -o 假设清单段在场判定）。环境 Axioms 段条目数：3——`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`、`Stdlib.Reals.ClassicalDedekindReals.sig_not_dec`、`Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec`——均为 Stdlib 侧 axiom（经 Stdlib 内部传递链装入环境），非本库声明；本库 193 条逐件 Print Assumptions 全 Closed（见逐定理表），即被审常量对其零依赖。判定式与 9.0 -silent 行为差异及 Axioms 段原文见 scripts/_pa_work/coqchk_combined.log（log 尾 guard powershell 之 SetConsoleWindowTitle 无控制台异常为无害噪音，已从本节剔除）。

## 零承认 grep（行首口径）

- 扫描范围：覆盖集内 89 个 .v（词表：`^[[:space:]]*(Axiom|Admitted|Parameter|Conjecture|Abort)\b`；避让件不在扫）
- **命中 0**（与 attn\G1全库合规自查-20260910.md 的 L1 层 34/34 FAIL=0、《零公理审计口径说明》L1 一致）

## 漂移清单（论文-库命名漂移，逐条在案、不跳过）

| 论文名 | 库内现状 | 判定 |
|---|---|---|
| req_step_kl_eta_bound（论文1 §4.3.2 批3 同位桥件名） | 仓库树与 attn 均无此声明 | 命名漂移/待入库；近邻已入清单：real_step_kl_eta_bound_eps（基座219）、geod_step_kl_eta_bound_eps（UpReqGeomD） |
| r2_step_kl_weighted（论文1 UpReqAlign3 六件清单名） | 库内无声明 | 命名漂移；近邻 r2_step_kl_rearr（UpReqAlign3） |
| rppo_align_objective_advantage_decomp（论文1 快照锚，UpReqPPO） | 仓库树无；仅 attn 工作区在盘 | 轮 9 待入库面（非命名漂移），入库后补审 |
| attention_minimizes_free_energy（论文2 概念名） | 库内声明为 req_attention_minimizes_free_energy_unique（UpReqFEPAttn） | 已按库内正名入清单 |
| tv_doeblin_contraction / tv_doeblin_iter（论文2 定理 5.10） | 库内无声明（UpTVReal 存档件未并入模块化树） | 存档件未并入/命名漂移；双点 TV 收缩以基座 attention_tv_contraction 族与 UpReqSampling bounded_softmax_tv 族承载 |
| real_kl_sum_decomp（论文2 §Real 复刻清单定理 4.1 侧名） | 基座 .v 注释幻影：L43735 重复注释头嵌套未闭、定理文本被吞，.vo 零导出（CW214KL_scan 垫片同构同判） | 非真实声明（注释幻影），不入清单；承 probe_full.v 历史注记同判；定理 4.1 主承载 free_energy_kl_decomp 已入清单。论文侧引用该名处建议 camera-ready 前对表 |

## 覆盖边界（如实登记）

- **UpIDL / UpMinP：已知预存缺陷修复中（合并轨收口席），跳编跳查，修复入库后补审计**（本次 EXEMPT 口径；coqchk 合并趟环境内含其既有 .vo 属只读加载，非对其重认证）。
- UpReqTempInterp（order.txt 在列）：编译失败（coqc 类型错位，cauchy_real_exp 项；.vo 不存在，.v 为 2026-09-10 08:08 版）——非清单 owner、无 PA 探针定理，逐定理结果不受影响；零承认 grep 已含该文件（命中 0）；如实登记，修复入库后随全树重跑补覆盖。
- **attn 工作区轮 9 新件待入库后重跑**：attn 侧较新版本（2026-09-10 版 UpAuditBridge/UpBudgetReal/UpCLQuery/UpDPOLip/UpDebtGibbsT/UpDebtSqrtAbs 等、UpReqPPO 之 rppo_align_objective_advantage_decomp）未入库，不在本报告覆盖；入库后重跑本脚本即得全量新口径。
- UpReqAlign3.v、UpAlignIdReq.v 在仓库树有源有 .vo 但未列入 order.txt：前者为清单 owner 已并入覆盖，后者无清单定理未逐一探针（零承认 grep 已含）。
- CW214KL_scan.v / AttnHardLimit218.v 为基座内容只读垫片件（order.txt 在列、随编译面覆盖），其与基座重名系历史垫片设计；无清单定理取自该两件。
- req_free_energy_kl_decomp 在 UpReqDist/UpSigMigrate/UpSigMigrate2/CW220_Extensions 四处同名声明、req_attention_is_gibbs_temp 在 UpSigMigrate/CW220_Extensions 两处：清单取论文交付正名模块（UpReqDist / UpSigMigrate）；探针逐模块隔离 Require，无歧义。

## 谱系与复现

- 定理清单承 `演变\.ablation\sc2_parallel\sL_assumptions\probe_full.v`（81 条，基态 198/206 批量 CLEAN 链）＋论文1/2 头条族补录 85 条 ＋ req 系旗舰 27 条；断言/解析方式承同目录 assert_print_assumptions.ps1 / parse_pa_log.ps1 的 bash 化；负载闸承 `演变\.ablation\cpu_guard.ps1`（LoadLimit 与在飞席热并发自调）。
- 复现：仓库根执行 `bash scripts/pa_audit.sh --coqchk`（复用现成 .vo 可加 `--no-build`）。旁证 log 全量在 scripts/_pa_work/。
- 与旧基线差值：81 条旧口径（基态 198/206 CLEAN）→ 本报告 193 条；基座由单文件 198/206 迁至 219 模块树（`ConstructiveWorld_vo`，基座 CW_ConstructiveWorld_219 ＋ Up* 模块），旧口径 81 条全部保留并逐条重跑。
