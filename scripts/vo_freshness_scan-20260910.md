# vo_freshness_scan — 两树信任缓存快扫（2026-09-10 深夜，主会话亲执）

> Historical planning record (dated in filename). Preserved verbatim for provenance; current certification facts live in README.md section 2.

> 用户裁决背景：全树编译须走信任缓存（219/220 版），禁全量重编（全量 ≥95min）。本扫描为编译调度底账。

## 一、仓库树（ConstructiveWorld_vo/，order.txt 全清单）

| 态 | 数 | 明细 |
|---|---|---|
| 新鲜（.vo 新于 .v，免编） | **87** | 其余全部模块 |
| 待重编（.v 新于 .vo） | **2** | UpMinP.v、UpIDL.v——合并轨收口席修复中（预期内，修后随四关重编） |
| 缺失 | **0** | — |

**结论**：仓库树信任缓存热度 97.7%（87/89），UpReqTempInterp 已由修复席重产 .vo（04:14）转入新鲜态。**无一个模块需要全量式重编**。

## 二、attn 树（根目录主库文件）

| 态 | 数 | 说明 |
|---|---|---|
| 新鲜 | **109** | 全部已交付库 |
| 待重编 | **2** | UpMinP.v（共修）、UpTVDoeblin.v（5.10 席在编辑，预期内） |
| 无 .vo | 54 | **非缺陷**：快照/副本/备份类工作拷贝（约 47 个「副本/快照/存档」件）+ 在飞席在建新文件（UpReqGeomIter.v①、UpReqRealFEP.v②、UpReqLogRDF.v 槽3，尚未到编译阶段）+ 历史件（CW_ConstructiveWorld_220.v 本地拷贝、UpReqGibbsE.v 被替代稿、UpReqAlignRest 系） |

## 三、世界分裂核查（TempInterp 回归的系统性排查）

- 仓库树：**0 个文件引 CW214 系（CW214KL_scan/AttnHardLimit218）；79 个纯 219 世界；混合世界 0**——改名迁移收尾干净，TempInterp 即最后一例，已修。
- attn 树：仍存在引 CW214 系的文件（历史上靠 `-Q ..\001` 双绑定解析）——轮 9 对账时按「统一 219 世界」口径收编（TempInterp 修复模式：主 Require 随迁 219 + 独有件本地重建/同名消费）。

## 四、两树分叉

已知分叉类（合并轨账本 38 文件改名 + 世界随迁差），逐文件 md5 全量枚举的作业仍在跑（后台），先录权威定性：分叉=改名差与世界随迁差的并集，无源码损坏类分叉（TempInterp 诊断实证：两树 md5 全同、分叉在依赖世界）。md5 枚举完成后由收口席/推送调度消费。

## 五、信任缓存资产

| 资产 | 位置 | 状态 |
|---|---|---|
| 219 版基座 .vo | 两树各一份（md5 相同） | ✅ 主信任缓存，PA 席刚验 153/153 Closed |
| CW220 历史 glob | releases/（Sep 9） | 历史产物，重生成后失效 |
| CW220 新 .vo | — | 待收口席全量编译产出（基座挂死探针实验中） |
| 在飞新库 .vo | UpTVDoeblin（5.10 席）等 | 属主席自管 |

## 六、轮 9 推送前必须重编清单

1. UpMinP.v、UpIDL.v（收口席修复后，随四关自动重编）；
2. attn 侧改名 38 文件中将被推送者：按仓库树同名 Freshness 对账后确定（推送前由主会话按本表调度）；
3. 其余 0 件。
