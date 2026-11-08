# 先读 · 一致型实例化闭合包（20261109）

**目标**：把 π 一致型强无理的零前提实例化从 0/6 推到闭合（(B) 案·α=10 档）。条件闭合已 6/6 云端认证——本包只做实例化面。

**五步上手**
1. 包根运行 `python 50_toolkit/verify_pkg.py`（数据完整性）。
2. 读 `01_工单-一致型实例化闭合-20261109.md`（六 lane 任务书·估时·验收·红线）。
3. 复制 `50_toolkit/config.example.json`→`config.json` 填写，跑 `env_check.py`。
4. 按 §1 依赖链开工：L0（机械落位）起手→(L1∥L5)→L2→L3→L4→L6。
5. 每 lane 交回执（§6 格式）。

**目录**：01 工单｜10-data（(B) 白名单·KB41m/h 处方回执·路径A G1-G6 勘验·G-MU-01 工单·顶件与桥件源·L0 vo md5 参照）｜20-sources（沙箱 born 九件：planB 四件＋route_unif 供件坯/assembly/final）｜40-skills（cw-ci-sop/tail-supply）｜50-toolkit（verify/env_check/build/accept/gate4/cpu_guard/config 样板）。

**环境**：Rocq 9.3.0（.vo 魔数 90300）·Python ≥3.9·Windows（cpu_guard 为 PowerShell）。
**估时**：核心 48-72 席时（含 Hmu lane 52-80）·并发 2 席墙钟 ≈26-40h。
