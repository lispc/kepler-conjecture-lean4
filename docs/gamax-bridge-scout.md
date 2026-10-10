# PA20 gammaX 双巨缺口侦察（只读，2026-10-10 归档）

> 结论：巨人波收窄时的 "C 级独立子项目" 判断**翻案为 B 级桥接**。总量
> ~950-1700 行新 Lean，无 C 级残留。对象：`gammaX_gamm4fgcy`（PA20:1470）、
> `gammaX_gamma3f`（:1494）——PA20 全文件仅此 2 处 sorry。

## 1. Mathlib v4.32.2 单形体积机器（复核重点）

- **字面成立**：无 `Simplex.volume`、无 CayleyMenger 行列式；Euclidean/Volume 只有
  Hausdorff 机器；StdBSimplex 只有凸性。
- **但装配件齐全**：`Measure.addHaar_image_linearMap`/`addHaar_preimage_linearMap`
  （|det| 缩放）、`addHaar_parallelepiped`、`image_parallelepiped`、
  **`LinearMap.normDet_sq_eq_det_gram`（NormDet.lean:304，Cayley-Menger 的 Gram 形
  核心，repo 判断漏看）**、`hausdorffMeasure_segment`、Fubini 全套。
- 体积桥 = 标准单形测度 1/6（Fubini 切片，唯一真新测度件）+ 仿射 |det| 迁移 +
  det² = deltaX/4 纯代数（Gram 条目 = 六距离二次式）。**B 级。**

## 2. repo 侧

- `volY`（PA20:103）= `√(deltaX…)/12`（sphere.hl vol_x 语义）；`volume.real` =
  Mathlib Lebesgue on V3。
- PA23 `grutoti_cell_vol`（真证）走锥帽径向路线不含单形 hull，但显式测度管线成熟；
  可复用：`volume_real_add_left/smul`、`sst_plane_null`（PA20:253）、
  **PA15 `p15_comboMap` + addHaar_image_linearMap 实战模板（PA15:2069-2071）**。
- delta↔行列式代数有先例（PA17 cross3 形 Cayley 恒等式族）。

## 3. SUM_PAIR_2_SET — A 级：已经证好，只差转正

- HOL 源 marchal3.hl:5854；PA15:2594 陈述仍 sorry（"needs SUM_GROUP" 注记过时）。
- **PA18:2627 `p18_sum_pair_2_set` 已全文证明同一陈述**（~110 行，2026-09-30
  SUM_GAMMAX wave 1 banked），private 只是可见性。动作 = 转正/别名，0-30 行。
- 配套全齐：`DIHX_SYM`（PA15:2573）、`FINITE_EDGE_X2`、`CARD_EDGEX_LE_16`、
  epsilon 模板 `GAMMAX_MCELL2`（PA21:1697）。

## 4. MXI_EXPLICIT → mxi 夹逼 — B−

`MXI_EXPLICIT`（PA12:1943 证）+ `p2g_OMEGA_LIST_N_IN_VORONOI_LIST_GEN`（PA2:3170
公开）→ 凸性 → voronoi_closed 夹逼。唯一私件 `p2g_CONVEX_VORONOI_LIST`
（PA2:1085 private，~15 行重证）。整段 ~100-200 行。

## 5. Wave 拆分（建议新文件 Geom/SimplexVolume.lean 或 PA26，避免动 PA20 冻结面）

| Wave | 内容 | 量级 |
|---|---|---|
| V 体积桥 | V1 标准单形 1/6（Fubini ~150-250）+ V2 平移/|det| 迁移（抄 p15_comboMap ~100-150）+ V3 det²=deltaX/4 Gram 代数（~200-350）+ V4 装配 volY 六距离（~50-100） | 500-900 |
| E 闭 gamm4fgcy | SUM_PAIR_2_SET 转正（~30）+ edgeX 6 对枚举（~80-150）+ per-edge 分发（GAMMAX_MCELL2 模板×6 ~100-200）+ gammaX↔vol4f 括号匹配（~50-100） | 250-450 |
| M 闭 gamma3f | mxi 夹逼 kit（~100-200）+ k=3 VX/dihX/sol 槽（~100-150）+ 3 边和 | 200-350 |

诚实性注记：kit 消费 PA17 AJRIPQN（上游 sorry 债流动，与已 banked 的 DIHX/SOL
k=4 核心同债级，不引入新债）。
