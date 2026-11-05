# DELIVERY — pa22-eusotyp2-assembly-w1

车道：`pa22-eusotyp2-assembly-w1`（PA22 第 6 波：`EUSOTYP2_general` 装配）
基线 HEAD：`9a03a60b`（PA22 `lean/Kepler/Text/PackingAuto22.lean`，14,434 行，
sha256 `1397802c4cf13190c9af1e51382d2273ab29decf033ed7f85e2f7f93ac585ed0`）
工作副本：`/tmp/pa22-eusotyp2-assembly-w1/Work2.lean`（14,769 行，
sha256 `5ef5c7b0457909c08d9ad36cc2fb83ba35beafc3b0f447ce1fb3c7702c5d1546`）

## 1. 闭合件表

| 件 | 位置 | HOL | 证法一句 |
|---|---|---|---|
| `EUSOTYP2_general` | PA22:10930（新） | counting_spheres.hl:3411 | 10 段装配：`u0=(b/(v·v))•v`、`u1=u0+v`、`cc=(b-u·v)/(v·v)`、`u2=u+cc•v`；`u0∈c3` 由 `rconeGt`+V3 仿射包（新 `p22w7_mem_affineSpan_of_mem_hyperplane` = HOL `affine_facet_hyper` 的 V3 形式）+`FCHANGED_AFFINE`；`RDISK_R` 取半径 `r`；调 `EUSOTYP_general`；`azim u0 u1 → azim 0 v` 用 `p22_azim_trans`+`p22_azim_axis_shift`（整对测点沿轴平移）；10 个合取逐条搬运（`u2→u` 用单点平移 `p22w7_azim_base_shift`）。 |

新增 `private` 补件（5 条，均在目标件之前、只被目标件消费）：

1. `p22w7_rcone_def_alt`（4 行）— `rcone_def_alt` 的本地副本（原件 PA22:11960 在目标之后）。
2. `p22w7_arcV_eq_angle`（6 行）— `p22_arcV_eq_angle` 的本地副本（原件 PA22:11994 在目标之后）。
3. `p22w7_mem_affineSpan_of_mem_hyperplane`（41 行）— facet 超平面点落入 `affineSpan c`（`affDim_hyperplane` 换序 + `finrank=2` 相等 + 方向相等 + `vsub/vadd`）。
4. `p22w7_azimSpec_base_shift`（27 行）— `AzimSpec` 对第一个测点沿轴平移不变（`h1` 吸收 `s`）。
5. `p22w7_azim_base_shift`（15 行，`set_option maxHeartbeats 12000000 in`）— `azim` 级同一性（退化/非退化两支，`rw [hpred]` 走 `Classical.epsilon`，避免 `congr 1` 的 whnf 超时）。

## 2. 残件精确缺口

无。`EUSOTYP2_general` 已闭合，无 `Kit-draft`。

## 3. 搬债审计（以 `docs/e2e-reachability-map.tsv` 为准）

体内新引用并在意是否 sorried 的件（`grep <name> docs/e2e-reachability-map.tsv`，
0 行 = 不在锥）：

```
EUSOTYP_general: 0            RDISK_R: 0
FCHANGED_AFFINE: 0            FACET_AFF_DIM_2: 0
FACE_OF_POLYHEDRON_POLYHEDRON: 0
p22_azim_trans: 0             p22_azim_axis_shift: 0
p22_collinear3_axis_shift: 0
```

结论：新证明未归结到任何仍-sorry 声明。最强证据：
`#print axioms Kepler.Text.EUSOTYP2_general` = `[propext, Classical.choice, Quot.sound]`
（无 `sorryAx`，原文见 `Evidence.md`）。

## 4. 冻结与变换保持

- 陈述切片（docstring + 签名 + `:= by`，26 行）与基线逐字节相同：
  sha256 `55a82de19ea8942802a36c12f58dce2f1e563560e695325dc12b46ff4aabf80d`（新旧一致）。
- `Work2.lean` 删除新增块并把目标体恢复为单行 `  sorry` 后与基线 `Work.lean`
  `cmp` 逐字节相同（`RECON_IDENTICAL`）——`EUSOTYP_simple` 等全部既有件零漂移。
- 零新 import（新增块 `grep import` = 0）；未新增 `open Classical`（新增块 `grep open` = 0，
  文件头既有 `open Kepler.Geom Set Classical` 未动）。
- 新增块 `grep -E 'sorry|admit|native_decide'` = 0。

## 5. 预算

- 工具调用：约 40 次（≤120）；墙钟约 1h10m（≤3h）。
- 全文件编译 3 次（基线 1 次、新件 1 次、axioms 1 次），每次约 1m45s。

## 6. 交付物

- `patch-pa22-eusotyp2-assembly-w1.diff`（336 insertions / 1 deletion，只含
  `lean/Kepler/Text/PackingAuto22.lean`；对 HEAD `git apply --check` PASS）。
- `Work.lean`（= 最终工作副本，无探针尾）。
- `DELIVERY.md`、`Evidence.md`、`logs/`。
- 无 `Kit-draft`（无残件）；`WORKORDER-w7.md` 不需要（本波收口）。
