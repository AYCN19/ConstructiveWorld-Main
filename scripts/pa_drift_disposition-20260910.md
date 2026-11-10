# pa_drift_disposition — PA 审计 6 漂移逐条处置（2026-09-10 深夜，主会话亲执）

> Historical planning record (dated in filename). Preserved verbatim except two body lines anglicized in place; file names, numbers and quoted fragments kept verbatim; current certification facts live in README.md section 2.

> Sources: pa_audit_report.md drift list + rename-ledger-20260910.md + two-tree grep/sed evidence (commands and outputs: see the reproduction section at the end of this file).

## 逐条处置

| # | 漂移名 | 根因定性 | 证据 | 处置提案 | 责任面 |
|---|---|---|---|---|---|
| 1 | `req_step_kl_eta_bound`（论文1 §4.3.2） | **论文引用名与库实名错位**：精确声明全两树零命中；仅子串命中（`req_step_kl_eta_bound_eps` 等 eps 后缀族，UpReqKLCvx/UpReqAlign/UpReqGeomD） | grep -E '^(Theorem\|Lemma\|Definition) 名\b' 两树=0 | 论文席对表：改引实名三选一（`real_step_kl_eta_bound_eps`@CW219 L113142 / Bishop 形 `real_step_kl_eta_bound_B`@UpRealLeB L437 / 无条件放电 `geod_policy_iter_kl_geom_step_eps`@UpReqGeomD L451），或库侧补同名桥件（不推荐，纯别名） | 论文席（相机就绪窗） |
| 2 | `r2_step_kl_weighted`（UpReqAlign3 六件名） | **同上类**：精确声明零命中，仅 UpReqAlign3.v 子串命中 | 同上 | 论文席对表：查 UpReqAlign3 六件实名后改引 | 论文席 |
| 3 | `rppo_align_objective_advantage_decomp` | **轮 9 待入库**：attn `UpReqIndex.v` L1219 `Lemma` 实存；repo 无（UpReqIndex 版本差） | grep 实证 | 轮 9 推送后自解，无需处置 | 推送链 |
| 4 | `attention_minimizes_free_energy` | **改名已闭环**：账本 L280 `attention_minimizes_free_energy_unique → ufep_attention_minimizes_free_energy_unique`（UpFEP.v L84），PA 已按正名入清单 | 账本行实证 | 无需处置 | — |
| 5 | `tv_doeblin_contraction`/`tv_doeblin_iter` | **UpTVReal/UpTVDoeblin 未并树**：attn 在盘（UpTVReal.v + UpTVDoeblin.v 在飞件），repo 无 | ls 两树 | 5.10 席注册后自解 | 合并轨收口→220 注册链 |
| 6 | **`real_kl_sum_decomp` 注释幻影（库级意外）** | **基座 L43735-43736 注释头整行重复**：Coq 注释可嵌套，内层 `(*` 吞闭合 → Theorem 本体+证明全部处于未闭合注释内 → .vo 零导出；而论文2 §9.2 Real 复刻清单引它作定理 4.1 侧承载 | sed L43730-43760 实摘：注释头两行逐字重复，后接完整 Theorem/Proof 文本 | **双提案**（见下） | 见下 |

## Drift 6 dual proposals (to be executed when opportune; no action taken here)

### (a) 基座修复提案（正式通道）
最小 diff = **删除 L43736 重复注释行（1 行）**。闭合链推演：删后外层 `(*`(L43735) 于 L43739 `*)` 正常闭合，Theorem 本体复活。代价评估：基座为正本冻结件——须走影子编译验证（单文件重编 ~40min）+ 下游全树重编（信任缓存下仅 .vo 时间戳失效面=基座直接消费者，估 87 模块重编）+ coqchk 全树。**建议排期**：与下一次基线升级（220 注册窗）捆绑执行，不单独开窗。
### (b) 论文侧对表提案（即时可做）
论文2 §9.2 Real 复刻清单中定理 4.1 侧承载名 `real_kl_sum_decomp` 改引 `free_energy_kl_decomp`（PA 清单在册 Closed），并加一句「熵侧和分解同见基座 B-8-8 区段（重导出排期中）」诚实注记。由论文 2 相机就绪窗执行。

## 复现命令
```bash
L="D:/ComplexAnalysis/ConstructiveWorld-Main/scripts/rename-ledger-20260910.md"
grep -nFf /tmp/drift6.txt "$L"                     # 账本命中（仅 L280 一条）
cd attn && grep -hnE "^(Theorem|Lemma) 名\b" *.v   # 精确声明核查（1/2 号=0，3 号=UpReqIndex L1219）
sed -n '43730,43745p' CW_ConstructiveWorld_219.v   # 幻影现场
```
