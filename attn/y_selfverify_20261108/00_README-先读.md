# 先读我 · y 系列 γ 段施工方自验工具包（20261108）

**这是什么**：给在自己机器上施工 γ 段节点的一方用，在本机独立复现认证 dossier 同款的六道链验收：编译、字节码 coqchk、Print Assumptions、注释规范卡、gate4、md5 账。

当前施工方是王小雪：C2.3 η 延拓六件与 C3-P08，协调台 #3 已登记在铸。脚本只验证，不改你的源码。

**五步上手**
1. 在包根运行 `python 50_toolkit/verify_pkg.py`，确认数据包完整。
2. 读 `01_施工方自验说明-y系列γ段六道链验收-20261108.md`，重点是 §2 节点规格、§5 温控、§6 已知问题。
3. 解压附卷A。zip 内 1021 个 .vo 平铺在根，解压目录本身就是 L0 目录。复制 `50_toolkit/config.example.json` 为 `config.json`，按说明 §3 的字段速览填写，然后跑 `python 50_toolkit/env_check.py --config 50_toolkit/config.json`。
4. 准备一次：`python 50_toolkit/build_deposit.py --config 50_toolkit/config.json --chk`，编译 56 个存档模块并逐件 coqchk。派单方本机在 G3 节流下，编译约 7 分钟、coqchk 约 9 分钟。
5. 每铸好一件就跑 `python 50_toolkit/accept_node.py --config 50_toolkit/config.json --node <节点号> --files <文件…>`；先加 `--static` 预检。结果在 `work_dir/accept/`，在协调台报完工时附上。

**目录**

| 目录 | 内容 |
|---|---|
| `01_施工方自验说明-…md` | 说明正本：现状口径、节点规格、准备与验收步骤、温控、已知问题、文献边界、约束 |
| `10_data/` | 85 节点名册与依赖边、闭合基态卷（C2 口径待王小雪更正）、文献考古回执、P08 对标一手证据、L0 .vo 的 md5 参照表 |
| `20_specs/` | 结构规范（唯一结构正本）、C2/C3 节点卡与草稿、存档认证 dossier |
| `30_sources/` | γ 存档波 62 件 .v（Main 仓 `attn/kbgamma_20261108/` 原样，只有源码） |
| `40_skills/` | 判据技能卷四件 |
| `50_toolkit/` | 包校验、环境自检、单根构建、六道链验收、gate4、温控脚本、配置样板；另有可选的施工工作流样板 `E1_outsource.dwf.ts`（已有自有施工流程就不用） |
| `MANIFEST.json` | 逐文件 md5 清单 |
| 附卷A（另一文件） | `附卷A_vo-trust-cache-windows-93.zip`：Main 主树 1021 件 Rocq 9.3 `.vo` 信任缓存。也可直接从认证 Release 下载同一文件（31,803,334 字节）：https://github.com/hy7pc8gfmf-dotcom/ConstructiveWorld-Main/releases/download/r-consistency-certified-v1/vo-trust-cache-windows-93.zip 。已有 Main 仓本地树的，`main_vo_dir` 也可直接指向它的 `ConstructiveWorld_vo`，env_check 会逐件核 md5 |

**环境要求**：Rocq 9.3.0（.vo 魔数 90300，跨版本不可混用，安装自理）、Python ≥3.9、Windows（温控脚本为 PowerShell，其余脚本跨平台）。
