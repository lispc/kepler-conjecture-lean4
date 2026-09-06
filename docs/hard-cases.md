# hard-cases.md — 卡壳记录

> PLAN.md §6.4：同一问题失败 3 次 → 记录于此并切换降级路线；
> 连续 3 个硬案例无法闭合 → 向人类汇报。

（暂无记录）

---

## 2026-09-06 hard_1 终端 LP 值偏差（±0.003–0.03，约 19%）——根因已定位并修复

### 根因

丢失的 branch.py 重放 hard 分裂树时**漏掉了 hard 特有的逐节点数值收紧**
（per-node numerics）。hard 证书的每个树节点（`build_certificates.hl`
`build`，hard_flag 恒 true——该标志从根节点起原样穿到整棵树）在求解前先
执行：

- `set_face_numerics_info`（hard_lp.ml:257 / build_certificates.hl:178）：
  由 std3_small 的边闭包、d_edge_200_225/d_edge_225_252 的对边闭包推出新的
  边限（e_200_225/e_225_252），并把含长边的 std 三角标记为大三角（bt）；
- `set_node_numerics_info`（hard_lp.ml:223 / build_certificates.hl:204）：
  仅当 card_node=13 时按已分类节点数把未分类节点放进 node_200_218 /
  node_218_236 等节点 ln 限。

这些修改在证书 Marshal 里记为一元 Lp_split 链（`add_big`，split_face=长边
dart；`high`/`mid`，split_face=节点列表），**只改 bb，不改变树形**——
easy 式重放把它们当成透明节点直接穿过，于是终端 LP 缺了这批收紧约束，
lnsum 最优值整体偏高，大量终端越过 12 的终端阈值。

### 证据（hard_1 = 图 161847242261，2,899 终端 / 134 infeasible）

对全部 2,899 个终端用 glpsol 求值（model2.mod，目标 sum ln[i]）：

| 重放模式 | 违反 ≤11.9999 的终端 | \|偏差\|>5e-4 | 偏差 0.003–0.03 |
|---|---|---|---|
| full（完整 numerics） | **0 / 2,899** | — | — |
| 无 numerics | 713 (24.6%) | 64.6% | 735 |
| 缺 face numerics | 527 (18.2%) | 54.3% | 781 |
| 缺 node numerics | 283 (9.8%) | 37.2% | 394 |

full 模式且非 infeasible 的终端最大值 11.99988386，贴着阈值 11.9999 下方
——与证书的终端判定完全一致。任一 numerics 缺失都产生 10⁻³–10⁻² 量级
的偏差签名（历史记录的"约 19% ±0.003–0.03"即此类部分缺失所致，具体占比
取决于丢失代码缺到哪一层）。

### 修复

`pipeline/lp/run/make_tasks_hard.py`：完整移植 hard 重放
（set_face/node_numerics_info、switch_std3/switch_edge/switch_node、
unary 链消费）。fail-loud 自检全部在位并通过（15 图 / 19,438 终端）：

- 每个一元 numerics 节点的（split_type, split_face）必须与重放计算出的
  info 逐项一致；
- quad/pent/hex 的 split_face 必须等于重放的分支面；tri 的 split_face
  必须是 std 三角；236/218 必须与 highish 成员判定一致；子节点数必须匹配。

附注（移植时踩过的坑）：`add_big` 的 dart 关联是
`zip (map face_of_dart long_edge) long_edge`——对**未 nub** 的 long_edge
逐项配对；先 nub 再 zip 会错位（只影响证书记录比对，不影响 LP）。

### 数值边界终端 t0138 的结论

`161847242261_t0138`（infeasible=False）：glpsol 5.0 浮点判定 LP 原始不可行
（inf=1.3e-07，LP 就在可行性边界上；OCaml 当年用旧版 GLPK 判定可行且
≤12）。driver 端到端抽验中 SoPlex 精确有理求解找到了可行点，Lean 内核
复检通过——证书原标记（feasible）在有理层面正确，任务清单保留原标记即可。
若全量运行中其他边界终端出现 gen fail-loud（SoPlex 找不到原始解），应把
该任务改走 slack 不可行路径（infeasible=True）后重跑。
