# Arch30_carrier_debt_census.md — Arch_UpAbl_30.v 载体伤情普查（keeper4 20261105·推岸随行件）

> Historical planning record (no date in the filename — Arch30 is a module number; the work date 20261105 is in the title line). Body lines anglicized in place; numbers, paths and identifiers preserved verbatim; current certification facts live in README.md section 2.

- 缔席：keeper4 手术官（20261105 手术窗·主会话裁决 A 案随行义务件）
- Fact source: measured on 20261105 in keeper4_wt (coqc 9.3 opam, wrapped in cpu_guard v3, layer-by-layer build logs
  `_tmp_jobs/keeper4_gate_build2.out`／`gate_build3.out`／`_Arch_UpAbl_30.gate.log` 在盘）。
- Qualification: the injury in this file is **not** P8 (UpAblP6_UniformLimit phantom) debt; the w_T/ pa6ul consumption surface of P8 has been
  重接并 rc=0 验证；本件是 **7672468（2026-09-27 "consolidation carriers"）生置件**的
  载体 scope 伤——生置后 S11_TP3B5 缺位（run#338 L141 `Arch_UpAbl_30 UNABLE_LIB S11_TP3B5`
  evidence) so compilation never got past L381; after the phantom/cascade were unblocked, the layers surfaced in sequence. **No overlap with the 586-fail spectrum**
  （run#3 Package/Arch_30 靠 runner 残留 stale UniformLimit.vo 编过——T2 冷清后 #4 必现）。

## 1. Cleared layers (rc=0 verified layer by layer; all landed in tree)

| # | 行 | 伤 | 修形 | 验证 |
|---|----|----|------|------|
| 1 | L45 | `Require Import UpAblP6_UniformLimit.` 幻影（源已整并） | 重接 `Arch_ToyR_02`（真归宿·pa6ul 全家同型） | 编译越面 |
| 2 | L380-385 | 嵌套 `existT _` 三层 sigT 推断病（`_` 谓词早熟绑定内层 sigma） | 证明体显式谓词（外层 `(fun _ : lt zero (fa56_covariance one one) => …)`） | 越面→下一层 |
| 3 | L391-398 | 内层 `existT _` 同病 + 裸 `Id` 双世界错配 | 内层谓词显式化 | 越面→下一层 |
| 4 | L375 起 | 裸 `Id`/`id_*` 解析到 UpAblMetaEngine 克隆 kit（其 L857 `Inductive Id`、L865 id_sym、L870 id_trans、L875 id_cong、L880 id_cong2、L908 id_refl 构子、L925 plus_zero nat 世界）遮蔽 S01_BaseRing 原版（L41 Id、L54 id_sym、L59 id_trans、L64 id_cong、L70 id_cong2、L42 id_refl） | 文件级 `Local Notation`×6 钉回 S01（L72-84·含注释） | 越面→L831 |
| 5 | L516 (same for Package) | bare `w_T` doubly defined (shadowing): AttnHardLimit218.v:514 vs S13_NLiveAudit.v:3893; the pa6ul_strict_first_cut statement (qualified as `S13_NLiveAudit.w_T` at Arch_ToyR_02:143) pins the S13 world | `Require Import S13_NLiveAudit.` placed after AttnHardLimit218 (shadowing order reversed) | **UpAblP6_Package.v EXIT=0** (measured) |

**Verification progress line**: after the four fixes Arch_30 compilation advanced to **L831**, i.e. L79-827 all GREEN:
uapkg6_temp_param_full_supply(81)、ems_cov 十一连(140-330)、**uapkg6_feeder_ri_abstract(377)**、
uapkg6_feeder_concrete_faces(413)、campaign_supply_closed(447)、v2 emsc/unilim/ts/fka 全节
(527-804)——**含全部 pa6ul/w_T 消费位（604/631/653/694/710）＝P8 在本文件的消费面已全过**。

## 2. 开放伤层（L828-3316·约 40+ 定理·载体考古战役对象）

### 2.1 First injury (stopping point; verbatim Error text in `_Arch_UpAbl_30.gate.log`)

```
File ".\Arch_UpAbl_30.v", line 831, characters 16-18:
The term "RI" has type "RealInterfaceEnhanced"
while it is expected to have type "Set".
```

L831-836 = `Section LoInflation.` 前奏 `Let one := @one RI.` 等——裸 `one` 解析到
**S01_BaseRing 的 Set-generic 环投影**（`{A : Set}` 形），而非 RealInterface 类投影器。

### 2.2 根因结构（三重同名影蔽·双 interface 世代）

1. **世代一**：S01_BaseRing.v:195 `Class RealInterfaceEnhanced := { RI_base :> RealInterface; one_pos : lt zero one; … }`——其字段经 `RealInterface`（S01 内·`zero/one/plus/mult/…`）继承；
2. **世代二**：S07_RealSetoidExpLog.v:7945 `Class RealInterfaceEnhancedSetoid (R : Set)`（`req` 世界·模块隔离——S07:6954 注「模块内外记录字段名互不冲突，实验验证 RC=0」·即作者已知同名冲突·以 Module 隔离内字段）；Arch_30 的 `req` 世界面（mtdc_* 1514 起）属此世代；
3. **克隆**：UpAblMetaEngine L857-925 全套 `Id/id_refl/id_sym/id_trans/id_cong/id_cong2`（S01 同型名克隆）＋ nat 世界 `zero/one`（L916-917）＋ nat `plus_zero`（L925）；
4. S01 generic 环投影 `{A : Set}` 形 `zero/one/plus/mult` 与上述全部同名。

Arch_30 的 `Import RealInterfaceEnhancedMod.` 仅 L71 一枚；裸 `one` 终局解析＝S01 generic
（实测 Error 证实）→ LoInflation 节前奏 6 枚 `Let one/zero/le/lt/plus/mult := @* RI` 全数
错绑世代。**828 以下每节前奏同构**（LoInflationAttn L1107 起、mtdc/ConjBridge L1460 起
＝req/Setoid 世界、mtd_param L2585 起）。

### 2.3 Injury surface by section (archaeological census master list; line numbers as landed-tree measurements)

| 节/波 | 行段 | 世界 | 首伤类 |
|---|---|---|---|
| LoInflation | 817-1101 | 世代一 RI | `@one RI` projector 错绑 S01 generic（L831 实测） |
| LoInflationAttn | 1107-1300 | 世代一 RI | 同构待勘 |
| loir_* 波 | 1277-1435 | 混（cf2_* 供给） | 待勘 |
| ConjBridge（mtdc_*） | 1460-1766 | 世代二 Setoid（`req` 型签名实测 L1514） | req 投影面 vs L71 Import 隔离模块——待勘 |
| mtd_* Q 波 | 1788-2600 | QArith 纯 Q 世界 | 疑低危（Q 独立名面） |
| mtd_param | 2585-3316 | 世代二 + req/real 互换桥（2217-2232 实测在册） | 待勘 |

### 2.4 绿证参考件（考古钥匙）

**UpAblP2WByPass.v**（order 在册·炉上绿）同为世代一 RI 消费件，其解法＝**节前 mid-file
重导**：`Import RealInterfaceEnhancedMod.` 于 L102/195/237/674（每个接口消费节前一枚）＋
节内 `Let R := @R RI.` 前奏（L999-1005 形）——Arch_30 仅 L71 一枚且 828 以下未重导。
plus_zero 影蔽序自正机制：RIF 投影面 Import（L71）晚于 MetaEngine（L65）→ RIF 的
`plus_zero`（class field，forall a : R 世界）胜 MetaEngine nat 版（L925）——L885
`id_sym (plus_zero zero)` 的 plus_zero 半边在 LoInflation 节本可自解，卡点只在 id_*/projector
影蔽（与 P2WByPass:504 同款 Green 先例）。

## 3. AttnHardLimit218 影蔽序机制（w_T 双定义实证）

- `w_T` has exactly two definitions in the whole tree: AttnHardLimit218.v:514 and S13_NLiveAudit.v:3893 (verified by grep).
- Package v2 依赖面顺序：EntropyMonoSplit_C(509)→**Arch_ToyR_02(510)**→SecondLaw(511)→
  fka(512)→**AttnHardLimit218(513)**→UpReqAttnUniformLimit(514)→SecondLawQuantified(515)。
- Coq Import 后到先得（后者胜）：裸 `w_T` 原绑 AttnHardLimit218.w_T；而
  pa6ul_strict_first_cut 陈述面（Arch_ToyR_02.v:143）限定钉 `S13_NLiveAudit.w_T`（其 L21
  `Require Import S13_NLiveAudit`）→ 消费位证明体（L618 裸 w_T）型错配——即 bb2a32ff
  verification record "AttnHardLimit218 shadowing order": the measured mechanism.
- 修形＝`Require Import S13_NLiveAudit.` 置 L516（AttnHardLimit218 之后·文件尾）→
  裸 w_T 改绑 S13 → 与 pa6ul 陈述面同世界。**Package EXIT=0 实测过关**；Arch_30 同款
  钉定（L68 后）使 604/631/653/694/710 五 pa6ul 消费位全过（编译推进线实证）。
- UpReqAttnUniformLimit（L514）定义 alm_uniform（其 L394·全树唯一定义）非 w_T——
  L616 裸 alm_uniform 解析自它·与 Arch_ToyR_02:148 用例同源·无冲突。

## 4. 考古战役任务书草案（候晨令单独立席·授权同 P8：解析面/证明体重接·语句面零触碰）

1. **逐节重导**：828 以下每接口消费节前补 `Import RealInterfaceEnhancedMod.`
   （P2WByPass 绿证同款·L102/195/237/674 先例）——先解世代一节（LoInflation/Attn）。
2. **世代二节**（mtdc/ConjBridge req 世界）：`Import RealInterfaceEnhancedMod` 后其
   Setoid 字段（req/req_minus/…）经模块隔离本可裸用；若 L71 单枚不足以覆盖 req 面，
   按节补导＋节内 `Let req := …` 前奏同构。
3. **投影错绑**：若重导后仍有 `@one RI` 绑 S01 generic（两世代 projector 同名竞态），
   节内 Let 显式形 `Let one := @RealInterfaceEnhancedMod.<字段路径> RI.`（限定路径·
   P2WByPass:299 限定形先例）或@解析面重接。
4. **id_*/plus_zero 残面**：L72-84 钉定已覆盖文件级；节内如有 MetaEngine 世界真消费
  (grep survey finds none), re-wire locally the same way as the P8 fix.
5. **红线**：陈述面零触碰；每修一层 rc=0 过层再进（cpu_guard v3 单 token 包裹）；
   每层落 `_Arch_UpAbl_30.gate.log` 留痕。
6. **估时**：世代一节（828-1300，约 25 面）0.5-1 天；世代二节（1460-1766）0.5 天；
   Q 波（1788-2600）0.5 天（疑低危）；mtd_param（2585-3316）0.5-1 天；合计
   **2-4 个工作日**（逐炉剥皮已定谳不取·一次普查正形）。

## 5. Not done / cannot be done

- L828-3316 not fixed (main-session ruling A; outside the resolution-surface surgery authorization);
- 世代一/二 projector 竞态的终局机理未定谳（止步于实测错绑证据＋P2WByPass 参考解）；
- Arch_30 双树落树文本 byte 同一（md5 实测 ae1cb61e…）·Live 炉编译待其归属炉验证。

---
*keeper4 20261105 手术窗·普查随行件完。证据面：`_tmp_jobs/keeper4_gate_build2.out`（47 绿）、
`gate_build3.out`（49 绿+2 红）、face_driver 三轮日志、run#338 `_seat3_fail_rows.txt:141`。*
