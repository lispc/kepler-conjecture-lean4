# DELIVERY.md — 柱③ 侦察结论

**结论（一段话）**：柱③ `DLWCHEM_full`/`XULJEPR_full` 的**句法真依赖闭包**在 `117511bb`
上是 **6 条 still-sorry**——`YSSKQOY_VECTOR`(13584)、`YSSKQOY_VECTOR2_ALT`(13609)，
以及经私件枢纽 `existsM_polyhedron_sums`(14179) 进入的 `GOTCJAH`(11950)、
`polyhedron_edge_sum`(12792)、`EXISTS_M_POLYHEDRON`(13062)、
`POLYHEDRON_FACET_SUM_4Pi`(13951)；按 HOL 证明意图还需追加
`YSSKQOY_VECTOR2`(13602) 与 `PACK_INEQ_DEF_A_797`(13595)，共 **8 条**，其中
**8 条全部真在路径上、0 条可跳过**；分类 **S 0 / M 2（GOTCJAH、
YSSKQOY_VECTOR2_ALT）/ L 3（YSSKQOY_VECTOR、YSSKQOY_VECTOR2、EXISTS_M_POLYHEDRON）
/ BLOCKED 2（polyhedron_edge_sum、POLYHEDRON_FACET_SUM_4Pi）/ DEFHOLE 1
（PACK_INEQ_DEF_A_797，现陈述因 `arclength22 := 0` 可反驳）**，最大单件
`EXISTS_M_POLYHEDRON`（HOL 267 行，估 350-500 Lean 行），三波可清的 6 条合计
**1150-2000 行**、全 8 条含阻塞尾 **1650-2800 行**；建议三波：
**W1 `GOTCJAH`（200-350，无阻塞，即可开工）→ W2 `EXISTS_M_POLYHEDRON`（350-500，
无阻塞，与 W1 并行喂同一枢纽）→ W3 Ysskqoy 三件 + `arclength` 真化（600-1150，
需 PA18 银行 5 条 + 缺失的 `arcV↔arcLength` 桥 + `_797` 陈述修改裁决，跨车道）**，
并把 `polyhedron_edge_sum` + `POLYHEDRON_FACET_SUM_4Pi` 明确留作 **BLOCKED 尾**
（前者吃 `BIJ_FACET_HYPERFACE`/`BIJ_DART_POLYEDGE` 且 `POLYHEDRON_TGJISOK` 空洞，
后者吃 `POLYHEDRON_CONFORMING_FAN` + 三件 ABSENT）；`fcdjdot` 本体估 **150-300 行**，
**必须落 `Assembly.lean`**（四柱中 3 个是 Assembly private），且落地前要先解
`Kepler.Text.sqrt3` 双胞胎（PA22:176 vs IneqClosureDefs:719）才能加
`import Kepler.Text.PackingAuto22`——属“需独立车道 + 冻结面审计”；**三波落完柱③仍带
`sorryAx`（来自那对 BLOCKED 尾件），柱③零 sorryAx 必须把尾并入 fan/Conforming lane**。

## 关键数字（给编排者）

- 柱③ 真依赖 still-sorry：**6 句法 / 8 含 HOL 意图**；真在路径 **8**，可跳过 **0**。
- S/M/L/BLOCKED/DEFHOLE：**0 / 2 / 3 / 2 / 1**。
- 最大单件：`EXISTS_M_POLYHEDRON`（267 HOL 行 → 350-500 Lean）。
- 三波行数：**1150-2000**；含阻塞尾 **1650-2800**；本体 **150-300**。
- `POLYHEDRON_FACET_SUM_4Pi`：**在路径上**（`existsM_polyhedron_sums:14238` 的 4π 端），
  但 **BLOCKED 不可跳过**。
- 本体落点：**Assembly.lean**（新 import + 加 `sqrt3` 去重；冻结面审计）。
- own-sorry 轨迹（live 基线 15，EUSOTYP2 已闭）：W1 15→14，W2 14→13，
  W3 13→9，尾 9→7。

## 交付物

`/Users/zhangzhuo/c17_backup/lane_snapshots/pa22-fcdjdot-pillars-recon-w1/`：
`DEPS.txt`、`WAVES.md`、`EVIDENCE.md`、`DELIVERY.md`，附 pin 快照
`PackingAuto22.at117511bb.lean`/`Assembly.at117511bb.lean`、探针
`probe{1,2,3b}.lean` + `.log`、脚本 `deps.py`/`closure2.py`/`holspans.py`。

## 只读合规

本车道对主仓 **零改动、零新增文件**：侦察期间 `EUSOTYP2_general` 由
**pa22-eusotyp2-assembly-w1** 车道落地（`f1f41235`，PA22 16→15，14769 行，
live 行号 = 本报告 pinned 行号 +335），期间 HEAD 由 `117511bb` → `dcb1a0fb` →
`8635c297`；结束时的 `git status` 里的改动/未跟踪项（`LocalAuto33.lean`、
`PackingAuto25.lean`、`docs/archive/lane-archives/pa25-rolling-w5/`、
`la33-straight-w1` 归档）**全部属其它车道**，无一由本车道产生。本车道未执行任何
`lake` 子命令、未写 `lean/.lake`、未写其它车道 scratch；所有探针为单进程串行
`script -q <log> lean <probe>`，文件都在 `/tmp/pa22-fcdjdot-pillars-recon-w1/`。

## UNRESOLVED

1. `arcV ↔ arcLength` 桥（HOL `arcVarc`+`ACS_ARCLENGTH`）无 Lean 对应物，W3 的
   桥成本只能给 100-250 行的粗估。
2. 任务书提到的 “`YSSKQOY_VECTOR` 的 DISCHARGES 注记”在 `117511bb` 树内不存在
   （grep 全树仅 LocalAuto33:2431 与 docs）；但 `EXISTS_M_POLYHEDRON`/`THETA_BOUNDS`
   与 `YSSKQOY_VECTOR` 之间**无环**已按陈述/证明体核实。
3. `POLYHEDRON_TGJISOK` 的“clean 但空洞”判定基于 `hypermap1OfFanxP22.darts := ∅`
   （PA22:237）；若 fan lane 后续把该 stub 换成真 hypermap，需重验其公理面。
