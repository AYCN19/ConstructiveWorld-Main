# ConstructiveWorld — 构造性数学库（Rocq/Coq）

[![Main CI 9.3](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main/actions/workflows/coq93.yml/badge.svg?branch=main)](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main/actions/workflows/coq93.yml) [![Coq CI（9.1 炉·并存保留）](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main/actions/workflows/coq.yml/badge.svg?branch=main)](https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main/actions/workflows/coq.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23717747.svg)](https://doi.org/10.5281/zenodo.23717747)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

## 作者与贡献者（Authors）

| 作者 | ORCID |
|---|---|
| Baojun Wang | [0009-0001-4240-9045](https://orcid.org/0009-0001-4240-9045) |
| Guangzhao Zu | [0009-0006-7811-6638](https://orcid.org/0009-0006-7811-6638) |
| Wanlan Xia | [0009-0008-7359-044X](https://orcid.org/0009-0008-7359-044X) |
| Baiyuan Zeng | [0009-0005-9811-5598](https://orcid.org/0009-0005-9811-5598) |
| Zhinong Zhou | [0009-0001-3206-5824](https://orcid.org/0009-0001-3206-5824) |
| Xuefeng Gao | [0009-0007-9904-1599](https://orcid.org/0009-0007-9904-1599) |

> 📐 **构造世界结构志 / Architecture monograph**: [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) —— 八域全域地图 · 依赖分层拓扑（实测 9,571 边·最大深度 28） · 注册十波演进时间线 · 四支柱谱系 · 构造塔叙事（「构造一切可构造」：万物皆算法的类型论实现）。

本仓库是论文《π 的构造性强无理：零公理判据与显式搜索上界》（*Constructive Strong Irrationality of π*；预印本 [figshare DOI 10.6084/m9.figshare.34134429](https://doi.org/10.6084/m9.figshare.34134429)）的**主张面工件仓**（π_geom 顶点强无理分离定理 `leibsep_pi_rational_unconditional` 及其全部认证引用件；冻结面 tag `v1.0-pi-separation`，Zenodo DOI [10.5281/zenodo.23717747](https://doi.org/10.5281/zenodo.23717747)），同时是 ConstructiveWorld 构造性数学库的主干：全库在 Set 层以 `sigT` 显式见证给出存在型结论，不引入任何公理，且整链可提取。2026-11-07/08 全库于 Rocq 9.3.0 完成内核全闭包收官认证（GPG 签名 tag `GREEN-CERTIFIED-v1`，见 §2「认证发布面」）。

## 1. 库概述

- **Scale**: certification surface of **1021 modules** (content-addressed certification archive `scripts/gates/cw_attest.json`·schema `cw.attest/v1`, recast 2026-11-07 from the #9 green furnace; includes the `Local/` stem guard module `Local/LW0LeibSeparation.v`, full-closure `coqchk` recheck basis). The registration order `order.txt` is the library's authoritative reference surface (`ConstructiveWorld_Live/order.txt` currently 1070 lines, measured 2026-11-10; grows with registration, the current state prevails), one line per registered module, in the form `S01_BaseRing.v#R0-d66910`, where what follows `#` is the registration-batch fingerprint. In-tree source modules (1035 `.v`) and the deduplicated registration order (1035 modules) have a zero difference set (measured 2026-11-10); the artifact-tree registration order deduplicated to 1021 modules is the same set as the certification archive, and the 14 extra rows in the source-tree registration order are pending-wave registration rows (see the certification-chain note in §2). The main module `LW0PiIrrational.v` sits at :525 (batch fingerprint `#R150-40656c`).
- **纯构造性**：全库不使用 `Axiom`/`Admitted`/经典逻辑；内核级 `coqchk -o` 复核口径为 `Axioms: <none>`（最近一次全树云端落定：run #9，见 §2）。
- **Set 层 `sigT` 显式见证**：存在型结论一律给出可计算见证（有理数端点、近似根等），不停留于命题层。
- **可提取**：以 `Separate Extraction` 生成目标语言代码并机械检查 `Obj.magic` 计数为零（计数非零即示 Prop 层内容泄入提取面）。
- **「率即算法」范式**：可执行件（`Defined` 计算器）与其正确性证书（`Qed` 证明）同体共存——定理与程序是同一件东西的两面。
- **双支柱现状**：第一支柱为 π 的构造性强无理闭合（主件 `LW0PiIrrational.v`）；第二支柱为五常数族——√2、√3、e、ln 2 的构造性无理性分离件已批量在册（#R164 起，`u5c_*`／`abl_ln2_*` 件族），ζ(2) 无理性方向的 Beukers 法机械件族（整除/衰减/计数）已在册·闭式定理装配进行中（`abl_z2_*` 件族·#R167）。其通用逃逸窗判据引擎的标准化路线已定谳（2026-10-14 stdlib 维护者判定转介、2026-10-26 CoRN 侧同构判定）：引擎与 π 分离件现以**独立库 [rocq-pi-leibniz](https://github.com/hy7pc8gfmf-dotcom/rocq-pi-leibniz)** 发行（v1.0.4，已入官方 opam 索引，`opam install rocq-pi-leibniz`；Zenodo DOI 10.5281/zenodo.23656982）。
- **第三支柱·tau 封闭链（#R194 战役）**：τ 的上下界封闭链（`piu_zz_tau_enclosure` 件族）已按无壳 18 片终形落装（`8df6c9f`）：zzPhi_256／512／1024 上下界封闭，原巨件 128 个匿名断言块升格为独立引理 `piu_zz_hb_512_0..31`／`piu_zz_hb_1024_0..95`，内核级 `coqchk` 4 组并行全树复核 ALL_PASS 且 `Axioms: <none>`（本地双线实证；工程志见 §5。注：该役为 2026-10 的 9.1 代·4 组并行旧口径历史认证；现役认证引擎为 Rocq 9.3.0·14 路并行，见 §2）。
- **第四支柱·ZZ 测度路线（#R194–#R197 波）**：无理测度判据与速率形证书装配线（`piu_mu_criterion`／`piu_zz_mu_assembly` 等）；支柱谱系与现状见 [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) 图 ④。

## 2. 版本与认证记录

| 项 | 值 |
|---|---|
| Library version | `bf234b76` (`main` branch, measured 2026-11-10·incl. unif-closure L0/L1 registration waves; advances with registration) |
| CI certification | **Closing run #9** (Main CI 9.3·head `0ef0c40f`): **success**——`coqchk` full-tree 14 groups·1020-module parallel kernel recheck ALL_PASS·`Axioms: <none>`·gate2 mode=FULL (head commit 2026-11-06·`git log` measured; certification chain settled 2026-11-07/08, see the certification chain below). Delta furnace: run #12 (attempt 2) success——gate2 ATTEST branch verdict **ATTESTED_CLEAN** (first flight on 9.3); a full delta-furnace pass takes about 14.5 minutes (the old full-tree furnace was on the order of 11 hours). Current green anchor: run #25 (attempt 6), all steps green with zero red steps (Main CI 9.3, measured 2026-11-10) |
| 公理审计 | `coqchk -o` 全库复核，`Axioms: <none>`（CI 侧由 gate2 块状态机哨兵解析判定：全树炉走 FULL 分支，增量炉走 ATTEST 分支——#12 判词 `ATTESTED_CLEAN`） |
| Registration order | `ConstructiveWorld_Live/order.txt` currently 1070 lines (measured 2026-11-10); the main module `LW0PiIrrational.v` sits at :525 (batch fingerprint `#R150-40656c`) |
| 许可 | Apache-2.0（见 `LICENSE`） |

### 认证链（Rocq 9.3.0 收官，2026-11-07/08）

#9 绿炉（`0ef0c40f`：全树 1020 件·`coqchk` 14 组并行 ALL_PASS·`Axioms: <none>`·gate2 mode=FULL）→ ① **认证档案重铸** `e0dacd49`（`scripts/gates/cw_attest.json` 重铸为 1021 件·Rocq 9.3.0 指纹——commit message 自证 964→1021）→ ② **过渡件退役** `559d0147`（skip 收缴行与 gate2 ATT-MODE-OVERRIDE 块删除，炉恢复继承认证面）→ ③ **delta 炉正典** `0da56c9f`（认证面收编 `Local/` 茎→1021 件；`coqchk` 逻辑名点分转换；`-admit` 继承机械退役——delta 炉对变更件跑真查全闭包；全树 headline 1020→1021；W3-BACKSTOP 每 20 炉强制全树）→ run #12（attempt 2）`GATE2-GREEN verdict=ATTESTED_CLEAN`。三连均为零源码改动（各 commit message 自证 zero source changes；`git show --stat` 实测三连各仅触碰一个文件：档案／workflow／`parallel_chk.sh`）。

> Note: the artifact-tree registration order (1021 modules·deduplicated) is the same set as the certification archive; the `UpReqPadeConstUnify.v`/`UpReqSymplecticBridge.v` rows in the source-tree registration order (#R212-reland-20261104) are registered but not yet in the certification surface — pending-wave rows whose entry settles with the next green furnace. Since 2026-11-09 the unif-closure L0/L1 registration waves add 12 `planb*` rows (see ④ below), bringing the pending-wave rows to 14 in total (measured 2026-11-10).

④ Post-chain waves (measured 2026-11-10): (a) unif-closure registration waves - L0, seven files (four main modules plus three `_cert` companion modules), landed at `8ad12e3` (run #23, attempt 2, green); L1, five files, landed at `e21c1b4`, with the gate4 header repairs on the three planb4 files landed at `bf234b76` (run #25, attempt 6, green - every step green, zero red steps), the current `main` head and the current green anchor. (b) gamma archive wave - PR #1 merged at `925d454` (run #19, attempt 2, green): certified segment sources C1/C2/C3 with the certification dossier tracked under `attn/kbgamma_20261108/` (63 tracked files). (c) gate7 port - PR #4 merged; `scripts/gates/gate7_extract_run.py` and `scripts/gates/gate6_statement_census.py` are in the repository, while the workflow step awaits a Main-specific baseline before re-attachment (an earlier attachment at `42b25a6b` was reverted after a `FileNotFoundError` on the missing script); the active furnace currently contains no gate7 step. The 12 `planb*` modules of the two registration waves are registered in the source-tree `order.txt` and not yet in the certification archive `scripts/gates/cw_attest.json` (together with the two rows named in the note above: 14 pending-wave rows in total, measured 2026-11-10).

### 认证发布面（tag／Release／Zenodo）

- **GPG 签名 tag `GREEN-CERTIFIED-v1`**：钉收官提交 `0ef0c40f`（tag 对象体 `git cat-file` 实测：一致型云端收官六前提 6/6 闭合，`piu1932_uncond_zz` 于 1020 模块全树重认证面内 `Axioms: <none>`）。别名 tag `r-consistency-certified-v1` 指向同一提交（tag 体自述别名关系·Zenodo 铸版绑定件；`git rev-parse` 实测两 tag 同指 `0ef0c40f`）。
- **GitHub Release「Consistency Certified v1 (Rocq 9.3.0)」**：双资产 `coqchk-logs.zip`（3.9MB）＋`vo-trust-cache-windows-93.zip`（31.8MB）。
- **Zenodo**：记录绑定 tag `r-consistency-certified-v1`，webhook 自动铸版六作者（Wang／Zu／Xia／Zeng／Zhou／Gao·ORCID 全；concept DOI [10.5281/zenodo.23717747](https://doi.org/10.5281/zenodo.23717747)）。

### 「认证一次永久有效」的语义

指**增量继承语义**：已认证面内未变更的模块免列（ATTEST-SKIP 附表），不再逐炉重验——**不是跳过验证**：delta 炉对每个变更模块的完整闭包执行真 `coqchk` 内核复核，闭包外模块不参与加载；W3-BACKSTOP 每 20 炉强制全树复核兜底。

Continuous integration now runs on **Main CI 9.3** (`.github/workflows/coq93.yml`·self-hosted Windows certification job; the macOS job was removed by ruling on 2026-10-29 (Main CI is Windows-only; with concurrency compressed, a restored job means dual-machine re-verification), recorded faithfully at 9.3-furnace minting time as the base had no mac job block): gate1 poison-token guard → gate4 comment sentinel → gate3 cross-tree diff → vo trust-cache startup seeding (fail-open) → RAM guard (commit-headroom report) → full-tree compilation (thermal-guard wrapped·fingerprint skip·14-way Kahn layering) → tree-stats (six-dimension counts, artifact) → gate5 vo binary quarantine (token+digest blacklist v3_93·control-calibrated) → attest reconciliation (`cw_attest.json` archive hit→skip list·miss→send for inspection) → `coqchk` kernel recheck (14-way root-grouped parallel·tree-copy isolation boxing·bytecode machine flag `-bytecode-compiler yes`——`vm_compute` certificate recheck ≥30× speedup; the delta furnace checks only changed closures, W3-BACKSTOP forces a full tree every 20 runs) → vo trust-cache upload (artifact) → gate2 axiom sentinel (block state machine parses `coqchk` logs to decide `Axioms: <none>`; generational pin `Welcome to Chicken 9.3.0`·FULL/ATTEST dual branches) → `coqchk` logs upload (artifact). A delta furnace pass takes about 14.5 minutes (the old full-tree furnace was on the order of 11 hours). Sentinel scripts live in `scripts/gates/` (gate7 extraction-execution scripts in repository; the active furnace has no gate7 step - re-attachment awaits a Main-specific baseline, see certification-chain ④; step chain per `.github/workflows/coq93.yml` as of 2026-11-10); the parallel certification script is `scripts/parallel_chk.sh`; the previous-generation 9.1 furnace `.github/workflows/coq.yml` is kept alongside.

## 3. 环境前置

- **Rocq / Coq 9.3.0**（`rocq` 与 `coqchk` 已在此版本实测——2026-11-07/08 收官认证引擎；CI 炉 `.github/workflows/coq93.yml` 代际钉 `Welcome to Chicken 9.3.0`）。旧版未验证；更换验证环境后须重跑下方四步。
- **环境与工件声明**：库全部形式化内容在 Rocq 9.3.0（CI 炉 opam 构建工具链·OCaml 5.5.2——CI 钉二进制 `coqc -v` 实测）下开发并通过内核全闭包认证（`coqchk` 14 路并行，2026-11-07 run #9 绿炉）。上一代认证引擎为 Rocq 9.1.0（并存 9.1 炉 `.github/workflows/coq.yml` 保留）；Rocq 9.1 的已知内核 guard 族三漏洞（CVE-2026-72703／72704／72705，2026-10-26 oss-security 第三方披露）不在 9.3.0 中存在，故本文全部结论不受该漏洞族影响。
- 无外部 OCaml 依赖；提取产物为普通 OCaml 源码，仅作审计对象，不要求可编译执行环境。

## 4. 复现：四步验证

与论文 §6「四步命令形态」逐字一致。以下命令在 `ConstructiveWorld_vo/`（或 `ConstructiveWorld_Live/`）内执行；两树均采用 `-Q . ""` 扁平命名空间。全树驱动见 `.github/workflows/coq93.yml`（现役 9.3 炉；9.1 炉 `coq.yml` 并存保留）。

```sh
# ① 全量编译：按 order.txt 注册序逐件（本机直调；全树 driver 见库 README）
rocq compile -Q . "" S01_BaseRing.v
# ② 公理审计：**审计语句即源件内逐字书写的 `Print Assumptions <语句名>.` 命令**（例：S14_B5BatchBlock.v:14401-14402 对 `b5d1_Heps4` 与 `b5dE_zero_le_one` 各一条；主件 LW0PiIrrational.v :13925 对 `lw0_pi_irrational`），随编译自动复验，预期输出 Closed under the global context
#    （载体件 Arch_Banach_01.v 等的载体处 Print Assumptions 语句）
# ③ 提取审计：Separate Extraction 产出的 .ml 中 Obj.magic 计数应为零
coqtop -q -Q . "" <件>.v            # 内执行 Separate Extraction <语句>.
grep -c Obj.magic <件>.ml           # 预期 0
# ④ 内核复核：逻辑库名取自 <件>.glob 头部（-Q . "" 下的实际前缀），勿用文件名替代
coqchk -silent -Q . "" <逻辑库名>.<件名>
```

注意事项：

- 逻辑库名**不等于**文件名。例如 `S01_BaseRing.v` 的逻辑库名是 `FS01_BaseRing`（取自 `S01_BaseRing.glob` 第 2 行）。第 ④ 步若误用文件名，`coqchk` 将报库不存在。
- 第 ① 步按 `order.txt` 行序逐件执行即满足依赖序；单件失败先行解决再续。
- 第 ④ 步 CI 炉在 `coqchk` 上启用字节码机旗标 `-bytecode-compiler yes`（`scripts/parallel_chk.sh` 内置；`vm_compute` 证书复核 ≥30× 提速）；本机单件复核可不带该旗标。
- 四步覆盖注册面全部在册件，主件 `LW0PiIrrational.v` 已在注册序内，无须独立配方。

## 5. 第三支柱工程志：tau 封闭链（#R194 战役）

> 本章为 2026-10 的 #R194 战役工程志，成文于 Rocq 9.1 代·`coqchk` 4 组并行旧口径（历史保留）；现役认证引擎为 Rocq 9.3.0·14 路并行（见 §2），两代数字不可互代。

第三支柱的封闭链主件原为单体巨件 `piu_zz_tau_enclosure.v`（24,636 行，β 区单引理证明体 2,317 行）。consumer 片含 96 段 assertion 巨带与提取物化区，单体编译在 64GB 主机上两轮实证于物化区 95% 处 OOM——单体编译是死路，拆分是唯一出路。战役要点：

- **拆分工程学**：机械拆分以语句边界为上限；巨件内 128 个匿名 `assert (HbN : stmt)` 块升格为独立引理 `piu_zz_hb_512_0..31`／`piu_zz_hb_1024_0..95`（语句与证明体逐字保留、块间零依赖边）。
- **无壳形制**：禁用 Export 伞壳，实件直连；tail 片沿用原名牌 `piu_zz_tau_enclosure` 原位承接旧导入路径（`Require Export` head＋slim＋literals 三路传递覆盖 3,040 名面），全树零下游消费面不受扰动。
- **检查点化与并行农场**：各片独立进程检查点化——单片红只重编该片，无壳并行实测约 30min/片（单体约 30h）；CI 侧 `scripts/parallel_chk.sh` 按 4 组根分组装箱、树副本隔离并行认证。
- **零漂移名面**：定义性语句名面 2,912 名零丢失零改名＋128 辅助名入册＝终形 3,040 名；语句多集 3,044 位恒等；Tier-2 导入面全量单入口 Check 零错；提取差分双基线字节等同。
- **双线内核认证**：本地 `coqchk` 双线（沙箱双跑 10h15m＋主仓 4 组并行 10h23m）ALL_PASS、`Axioms: <none>` ×4、gate2 CLEAN。

落装世系：六片拆分 `10e14f9` → 五片先行认证波 `8205e21`（consumer 片因 OOM 风险缓装）→ consumer 无壳 18 片终形落装 `8df6c9f`（`order.txt` tau 区 5→23 行）。技术细节见各 commit message 与 `.github/workflows/coq93.yml` 步注。

## 6. 仓库布局

| 路径 | 内容 |
|---|---|
| `ConstructiveWorld_Live/` | Source tree: all-tree `.v` sources (1035 modules, measured 2026-11-10)+`order.txt` (currently 1070 lines)+`_CoqProject` (967 lines, `-Q . ""`)+`Local/` (guard module `Local/LW0LeibSeparation.v`, registration order :529) |
| `ConstructiveWorld_vo/` | 产物树：与源树同构，另含 `.vo`/`.glob`/`.vos`/`.vok` 编译产物（产物树注册序现势 1056 行·去重 1021 件，与认证档案同集） |
| `order.txt` | Registration order (one copy per tree; source tree currently 1070 lines·artifact tree 1056 lines (measured 2026-11-10); line counts grow with registration, the current state prevails; `scripts/` keeps a maintenance historical copy of 803 lines, ending at the R193 wave, not synced with R194) — the authoritative reference surface |
| `_CoqProject` | Root-level manifest: the historical 220-era version (92 lines, kept for the record, see the header note in the file); the active manifest is the dual-tree `_CoqProject` (source tree 967 lines, `-Q . ""`·measured 2026-11-10) |
| `scripts/` | 注册序维护脚本、`scripts/gates/` 哨兵（毒 token 守卫、公理解析、跨树 diff、注释哨兵、vo 依赖检疫、提取执行）与内容寻址认证档案 `scripts/gates/cw_attest.json`（1021 件·schema `cw.attest/v1`）；并行认证脚本 `scripts/parallel_chk.sh` |
| `.github/workflows/coq93.yml` | CI 全树驱动·现役 9.3 炉（编译＋14 路 `coqchk`＋哨兵＋gate2 FULL／ATTEST） |
| `.github/workflows/coq.yml` | CI 全树驱动·9.1 炉（并存保留） |
| `docs/` | 设计与规划文档 |
| `releases/` | 历史单文件合并版（220 版，见附录） |

## 7. 许可与引用

- **许可**：Apache-2.0。提取产物（`.ml`/`.mli`）与源件同许可。
- **制品引用（Zenodo）**：concept DOI [10.5281/zenodo.23717747](https://doi.org/10.5281/zenodo.23717747)——记录现绑定认证 tag `r-consistency-certified-v1`（2026-11-07/08 认证发布面，webhook 自动铸版六作者）；π 分离冻结面版本 `v1.0-pi-separation`（版本 DOI 10.5281/zenodo.23717748）仍可引用。
- **认证发布面引用**：GPG 签名 tag `GREEN-CERTIFIED-v1`（钉 `0ef0c40f`）＋GitHub Release「Consistency Certified v1 (Rocq 9.3.0)」双资产（`coqchk-logs.zip`＋`vo-trust-cache-windows-93.zip`）。
- **引用锚**：引用库内语句时，建议以「件名＋`order.txt` 行号＋批次指纹」定位，例如主件为 `LW0PiIrrational.v`，`order.txt` :525，`#R150-40656c`。批次指纹随注册批固化，可用于核对所引版本。

## 8. 公开范围与例外

引用面所在件全量公开。显式例外现势为零——两类历史例外均已清空：

1. **下划线探针件 `_twc_probe.v`（已退役）**：曾维持禁止引用口径、不在注册序内；已于 2026-11-06 退役出树（commit `0571411`——探针不属注册面·注册序探针行清除），双树现均无此件。
2. **Out-of-register difference-set modules (cleared)**: source modules present in the tree but not listed in `order.txt` — under the 2026-10 accounting there were 45; currently (measured 2026-11-10) the tree's 1035 `.v` modules and the registration order (1035 deduplicated rows) have a zero difference set, no out-of-register source modules. If unregistered modules appear later, their disposition will be recorded here following the ruling outcome of the pre-publication batch for the repository. The current registration order is the sole authoritative reference surface (line counts grow with registration·the current state prevails); unregistered modules do not constitute a reference commitment of the library.

## 附录：220 版历史说明（2026-09-07/08）

以下为仓库早期（220 版）的 README 内容，描述当时的模块化布局；现已由上文的注册序体系取代，原文保留备查。

---

# ConstructiveWorld220 — 构造世界 220 版模块化代码库

220 版 = 219 基座（信任缓存）+ 28 个独立模块（本工作流 2026-09-07/08 交付件）。

## 设计目标（用户规划）
后续开发直接调用本地库 & 云端镜像的**编译产物**实现快速编译与快速锁定问题：
- 每个模块一个 .v + 一个 .vo——**坏哪块，锁哪块**（产物名 = 问题位置）
- 基座 `CW_ConstructiveWorld_219.vo` 走信任缓存，永不重编（6MB 级编译在部分上下文会阻塞）
- `docs/BLOCKERS-220.md` 记录单文件 220 版的全部阻塞点及模块级映射

## 目录
| 路径 | 内容 |
|---|---|
| `ConstructiveWorld_Live/` | 活源码树：基座 .v + 28 模块 .v + _CoqProject + build.sh |
| `ConstructiveWorld_vo/` | 产物树：同上 + 每模块 .vo（基座 .vo = 信任缓存直拷） |
| `releases/` | 单文件全量合并版 CW_ConstructiveWorld_220.v（129K 行） |
| `docs/` | 合并指引、甄别报告、阻塞图谱 |

## 编译
```bash
cd ConstructiveWorld_vo
bash build.sh        # 拓扑序增量编译（.vo 已存在则跳过）
```
全量重编基座（可选，建议在交互终端跑）：`coqc -Q . "" CW_ConstructiveWorld_219.v`

## 模块清单（28，依赖拓扑序）
第 0 层：UpCS UpHlogZ UpDebtSqrtAbs UpDebtDual UpEntropyGain UpSigMigrate UpMinP UpAlignId UpProj UpFirewall UpTempWindow UpKVEv UpAuditBridge UpPredRelax UpPLA UpStepKLM3 UpRecast UpCLQuery UpSLM
第 1 层：UpBudgetReal↑UpHlogZ · UpArchAttn↑BudgetReal · UpConstitution↑BudgetReal · UpProjBPC↑Proj · UpEvictId · UpDebtGibbsT · UpDPOLip
第 2 层：UpDissip↑Constitution · UpStopTime↑BudgetReal+Constitution

已吸收进基座（勿重编）：UpStepKL UpLogMono AttnDoeblin AttnHardLimit218 AttnSqrt UpFEP UpPPO UpGRPO(→UpGRPO219) UpExtras(→UpExtras219)
