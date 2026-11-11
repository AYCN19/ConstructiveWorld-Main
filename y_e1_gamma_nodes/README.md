# y-E1 γ 线节点件交付包（第二波·2026-11-12）

- **席**：AYCN19（y-E1 主会话）。分支 `sandbox/y-e1-gamma-nodes-20261111`，在首波 `9e8b432` 之上追加。
- **内容**：γ 线节点件 43 件 `.v`（11,435 行）＋ `MANIFEST.json`。较首波新增 6 件（GaC2_07 两件、GaC2_09 裸名 stem、GaC2_12 的 stem/_f/_g），其余为现行版本。
- **闸态**：43 件所属 13 个节点的 accept_node 六道链闸账在推送时全部为 PASS（闸账正本在 `attn/y_e1_work/accept/`，逐件 verdict 与时间见 MANIFEST）。

## 读清单前必须知道的三件事

1. **闸账 PASS 不等于卡面定理已证。** 它表示文件能编译、通过 coqchk、被审计的名字无公理依赖。
2. **部分卡面主命题是语句载体，只陈述、未证明**：
   - `GaC2_18_ZetaDerivBound.v` 全文无证明，`r_pos_lower` 与 `zeta_deriv_bound` 是 `Definition … : Set`。
   - `GaC2_07_DirichletTestAbel.v` 的 `abel_tail`、`eta_conv_uniform` 是载体，证明体在件头注登记为开槽。
   - `GaC2_17_StripVerticalAsm.v` 仅 1 条引理，另有以卡面命题命名的 Set 型定义（按普查，推送席未逐条阅读）。
   - MANIFEST 逐件列出 `theorem_count` 与 `set_typed_definitions`，可据此自行判断。
3. **`GaC2_09_DenomZeroSet.v`（裸名 stem）四名册只证了 2 条**：(a) `denom_zero_real_dir`、(d) `zero_set_membership`。(b)(c) 所需的 real 层一阶 exp-Taylor 余项面库内不存在，登记为开槽。

## 其他

- `GaC2_18` 主件相对草稿的四项语句面偏差（点前提改为代表函数 g 加逐点 bond、`dist_lb_ok` 改为盘内分母正下界、`real_const (2#1)` 原子修正、增 1 行 Require）经主会话批准，详见 MANIFEST。
- γ 线未在 Main 树注册（Live 树无 GaC 件、`order.txt` 无注册行），本分支推送不触发 CI。多数件头注超过 30 行，进 Main CI 前需整形与注册。
- 推送时独立复审（v25 八巷）仍在进行，复审结论不在本包内。
