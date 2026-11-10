# 已合并存档 — 219 已收录模块甄别报告（2026-09-08）

> Historical planning record (the filename carries no date; the report date 2026-09-08 is in the title line). Preserved verbatim for provenance; current certification facts live in README.md section 2.

**甄别方法**：Python 声明级终审（模块顶层声明名 ∩ 219 源声明集，CR 清洗 + 全量正则）。
**教训**：初轮 shell comm 因 CRLF/CR 残留与 locale 全体失敏报假零——工具链交叉验证必做（本次由 boltzmann_dist_attn 单例矛盾揪出）。

## 已收录清单（9 件）
| 件 | 命中度 | 吸收形态 |
|---|---|---|
| AttnDoeblin.v | 48/48 声明级 | 逐字吸收 |
| AttnHardLimit218.v | 49/49 | 逐字吸收 |
| AttnSqrt.v | 12/12 | 逐字吸收 |
| UpFEP.v | 5/5 | 逐字吸收 |
| UpPPO.v | 6/6 | 逐字吸收 |
| UpStepKL.v | 35/35 | 逐字吸收 |
| UpLogMono.v | 4/4 | 逐字吸收 |
| UpGRPO.v | 改名 | 219 尾部 Module UpGRPO219（L113511，471 行） |
| UpExtras.v | 改名 | 219 尾部 Module UpExtras219（L113991，231 行） |

## 合并候选（32 件，留于上级目录）
零星命中均为根引用非根声明或 Section 变量遮蔽（单件内联探针 34/34 全绿实证无根碰撞）。
装配期真碰撞 2 簇：EvictId×SigMigrate（Z_thermo/boltzmann_dist_attn/boltzmann_factor→Module EvictId 隔离）、
DebtDual×DebtGibbsT（real_softmax_temp/real_partition_function_temp 系→Module DebtGibbsT 隔离）。
