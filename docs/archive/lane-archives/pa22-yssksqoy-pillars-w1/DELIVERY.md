# 交付：pa22-yssksqoy-pillars-w1（PA22 第 7 波：`fcdjdot` 柱③ YSSKQOY 链）

- 主仓：`/Users/zhangzhuo/repos/kepler-conjecture-lean4`，基线 HEAD = `f1f41235`
- 目标文件：`lean/Kepler/Text/PackingAuto22.lean`（唯一改动文件）
- kit：`kit-pa22-yssksqoy-pillars-w1.diff`（`diff --git a/lean/Kepler/Text/PackingAuto22.lean b/lean/Kepler/Text/PackingAuto22.lean`，417+/2-，对 HEAD `git apply --check` PASS）
- 全文件 standalone 编译：RC=0，0 error（`logs/work3.log` / `logs/baseline.log`）

## 1. 闭合件表

| 件 | 位置（HEAD 行） | 证法一句 | `#print axioms` |
|---|---|---|---|
| `YSSKQOY_VECTOR` | :13919 | 绕开不在闭包内的 `arcLength` 银行，直接把 HOL 的 `YSSKQOY+arcVarc+ACS_ARCLENGTH` 压成两变量 arccos 不等式；固定 `b` 对 `a` 用 `antitoneOn_of_deriv_nonpos`，导数非正核化为 `16(b−2)(b+2)(2a²−b²+4) ≥ 0`，再 `Real.arccos_le_arccos` 把 `dist ≥ 2` 降到 `c = 2` 特例 | `[propext, Classical.choice, Quot.sound]` |
| `GOTCJAH` | :12285 | HOL 证路装配：`gotcjah_prep` → `EUSOTYP2_general` 取 `g/h` 环枚举 → `gotcjah_sol_lemma` 逐楔块 `X i` → `ORDER_AZIM_SUM2Pi`（Σhalf-azim=π）→ `GOTCJAH_convex_sum`（Jensen）→ `WEDGE_ORDER_DISJOINT`（互斥）→ 用文件内 `p22w4_sol_disjoint_union` 归纳得有限并 `sol` 可加性 → `SOL_SUBSET` 收尾 | `[propext, Classical.choice, Quot.sound]` |

两件均**零 sorry/admit/native_decide**，且 `#print axioms` 为标准三（实测原文见 `Evidence.md`）。

## 2. 路径判定（先做的判定步）

`DLWCHEM_full` 证明体消费 `YSSKQOY_VECTOR`（:14602 附近，transfer 到 `existsM_polyhedron_sums` 的 `htheta`）；`XULJEPR_full` 消费 `YSSKQOY_VECTOR2_ALT`（:14653）。`PACK_INEQ_DEF_A_797` / `YSSKQOY_VECTOR2` 在 `PackingAuto22.lean` 内**无任何证明项引用**（仅注释提及）。

- `YSSKQOY_VECTOR`：**ON-PATH**，本波已闭。
- `YSSKQOY_VECTOR2_ALT`：**ON-PATH**（`XULJEPR_full`），但其 4 个条件分支中两支经 `YSSKQOY_VECTOR2 → PACK_INEQ_DEF_A_797`。
- `YSSKQOY_VECTOR2`：**OFF-PATH**（无引用者），且被 `_797` DEFHOLE 阻塞。
- `PACK_INEQ_DEF_A_797`：**OFF-PATH / DEFHOLE**，不可证（见 §3）。

## 3. 残件精确缺口

### `PACK_INEQ_DEF_A_797`（:14345，DEFHOLE，不可证）
`arclength22 (r h d) : ℝ := 0`（`PackingAuto22.lean` 内紧邻该定理的桩）。取 `v0` 任意满足 `‖v0‖ = 2`，`v = −v0`：
- `‖v‖ = 2` ⇒ `2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2*h0`（`h0 = 1.26`，`2 ≤ 2.52`）；
- `‖v0‖ = 2` ✓；`dist v v0 = 4 ≥ 2*h0 = 2.52` ✓；
- 结论要求 `0.797 + acs(2/4) − π/6 < arclength22 … = 0`，而 LHS `= 0.797 + π/3 − π/6 = 1.3206… > 0`。
故陈述**可反驳**；该件不是数学缺口，是 `DEFHOLE` 占位（HOL 侧真输入 `pack_ineq_def_a` 是 UKBRPFE/WAZLDCD/BIEFJHU 的 flypaper 合取，Lean 侧 `packIneqDefAP22 := True` 且 `arclength22 := 0` 双双替换）。未改陈述、未硬凑。

### `YSSKQOY_VECTOR2`（:14352）
HOL 证明是 `MATCH_MP_TAC PACK_INEQ_DEF_A_797`（counting_spheres.hl:6599-6621），即**唯一**输入就是上述 DEFHOLE。因此本件 `BLOCKED-by-DEFHOLE`。可选替代路线是自己证 1-变量优化（最坏情形 `dist = 2h0`，`a = ‖w‖ ∈ [2,2.52]`：`acs(a/4) + 0.797 − π/6 ≤ arccos((4+a²−(2h0)²)/(4a))`，两端在 `a = 2.52` 取等），但常数 `0.797` 是数值设计值，需自建严格区间/单调性论证，非本波预算可闭。

### `YSSKQOY_VECTOR2_ALT`（:14359）
HOL 四分支：`v=v0`/`w=v0` 两支 → `YSSKQOY_VECTOR2`；`v=w=v0` 一支平凡；都不等于 `v0` 一支 → `YSSKQOY_VECTOR`。故 ALT 的闭合等价于 `VECTOR2`，同样 `BLOCKED-by-DEFHOLE`。注意其"都不等于 `v0`"分支在数学上已由本波 `YSSKQOY_VECTOR` 覆盖，缺的只是两支混合分支。

### `DLWCHEM_full` / `XULJEPR_full` 的剩余 `sorryAx`（非本簇）
本波后实测两者仍为 `[propext, sorryAx, Classical.choice, Quot.sound]`。精确定位：其装配层 `existsM_polyhedron_sums` 现在只经以下 3 个上游 sorry-GIANT 带债：
- `EXISTS_M_POLYHEDRON`（:13612，sorry）
- `polyhedron_edge_sum`（:13342，sorry）
- `POLYHEDRON_FACET_SUM_4Pi`（:14701，sorry）
（`facet_3_facets`、`FCHANGED_MEASURABLE`、`GOTCJAH`、`DLWCHEM_VECTOR_sumReal`、`XULJEPR_VECTOR_sumReal`、`SATURATE_BALL_ANNULUS`、`gotcjah_sol_lemma`、`EUSOTYP2_general`、`gotcjah_prep`、`GOTCJAH_convex_sum` 本波复测均为标准三。）

## 4. `DLWCHEM_full` / `XULJEPR_full` axioms 前后对比

| 名称 | 基线 | 本波后 | 说明 |
|---|---|---|---|
| `DLWCHEM_full` | `[propext, sorryAx, Classical.choice, Quot.sound]` | `[propext, sorryAx, Classical.choice, Quot.sound]` | GOTCJAH 与 YSSKQOY_VECTOR 两段债已除，但另 3 个上游 GIANT 仍在 |
| `XULJEPR_full` | 同上 | 同上 | 它不经 GOTCJAH；剩余同上 3 个 + `YSSKQOY_VECTOR2_ALT`（DEFHOLE 阻塞，自身仍 sorry） |

主验收指标（`DLWCHEM_full` 转干净）**未达成**，原因是 recon 前已知的口径修正：`DLWCHEM_full` 并非只因 `YSSKQOY_VECTOR` 带债，另有 `EXISTS_M_POLYHEDRON` / `polyhedron_edge_sum` / `POLYHEDRON_FACET_SUM_4Pi` 三条独立 GIANT 债；本波已把 YSSKQOY 与 GOTCJAH 两段清零。

## 5. 搬债审计

- **零新增债**：新增代码只证 `YSSKQOY_VECTOR`、`GOTCJAH` 及其私有支撑件（`yssF*`、`yss_scalar`、`p22g_sum_Icc_eq_range`）；两者 axioms 皆标准三。
- 未新引 `sorryAx`；未新增 import（`#check` 确认 `arcLength`/`YSSKQOY` 不在 PA22 闭包内，故走纯 Mathlib 的 arccos 证法，不造边）。
- 净减：文件内声明级 sorry 16 → 14（裸 `sorry` 行 15 → 13）。
- 本波未触 `EUSOTYP2_general`、polyhedron 组、`EXISTS_M_POLYHEDRON`、`POLYHEDRON_FACET_SUM_4Pi`、`regular_spherical_polygon_area_asnFnhk`、`vol_solid_triangle_ortho` 等禁改件。

## 6. 预算

- 工具调用约 70 次（上限 120）；墙钟约 50 分钟（上限 3h）。
- 探针/整文件进程皆单进程串行，日志在 `logs/`；仅用 standalone `lean`，零 `lake` 调用，未写 `lean/.lake/`。

## 7. 工件

`$S = /Users/zhangzhuo/c17_backup/lane_snapshots/pa22-yssksqoy-pillars-w1/`
- `kit-pa22-yssksqoy-pillars-w1.diff`
- `Work.lean`（全文件 RC=0 版本；不入库）
- `DELIVERY.md`、`Evidence.md`
- `logs/`（baseline / work1-3 / probe / olean）
- 无 `Kit-draft-*.lean`：4 个目标件中 `PACK_INEQ_DEF_A_797`/`VECTOR2`/`VECTOR2_ALT` 未尝试（DEFHOLE 阻塞），其体在 kit 中保持原 `sorry`。
