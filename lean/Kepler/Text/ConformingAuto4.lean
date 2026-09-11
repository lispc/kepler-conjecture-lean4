/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 4
(Conforming.hl:859-1036).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 4, Conforming.hl:859-1036):
- `RADIAL_EMPTY` (859)
- `RADIAL_UNIONS` (864)
- `RADIAL_UNIV` (875)
- `RADIAL_AFF_GE_1_2` (887)
- `RADIAL_AFF_GT_3_1` (914)
- `RADIAL_INTERS` (944)
- `XFAN_INTER_BALL_UNIONS` (958)
- `RADIAL_XFAN_INTER_BALL` (986)
- `RADIAL_NORM_YFAN_INTER_BALL` (1008)
- `SOLID_ANGLE_YFAN` (1024)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `radial_norm r v0 C` ↔ `radialNorm r v0 C`
  (Kepler/Geom/Volume.lean:27). HOL's `RADIAL_EMPTY`/`RADIAL_UNIONS`/
  `RADIAL_UNIV`/`RADIAL_INTERS` are stated for a general `real^N`; the
  repo only defines `radialNorm` for `V3`, so these four are stated for
  `V3` (noted per-theorem). `RADIAL_AFF_GE_1_2`/`RADIAL_AFF_GT_3_1` are
  stated by HOL for `real^B` (2-dimensional affine plane); the repo only
  has `affGe`/`affGt` for `V3`, so they are stated for `V3` (noted
  per-theorem).
- HOL `normball x r` ↔ Mathlib `Metric.ball x r` (both are
  `{y | dist y x < r}`; cf. `NORMBALL_BALL`, sphere.hl).
- HOL `xfan (x,V,E)` ↔ `xfan x V E` (Kepler/Text/Fan.lean:154);
  HOL `yfan (x,V,E)` = `UNIV DIFF xfan` ↔ `yfan x V E`
  (Kepler/Text/Fan.lean:158); HOL `FAN(x,V,E)` ↔ `FAN x V E`
  (Kepler/Text/Fan.lean:56).
- HOL `aff_ge`/`aff_gt` ↔ `affGe`/`affGt` (Kepler/Geom/Aff.lean:42/39).
- HOL `UNIONS f` ↔ `⋃₀ f` (`Set.sUnion`); HOL `INTERS f` ↔ `⋂₀ f`
  (`Set.sInter`); HOL `UNIONS {y | ?e. e IN E /\ y = f e}` ↔
  `⋃ e ∈ E, f e` (`Set.iUnion`); HOL `INTER` ↔ `∩`, `DIFF` ↔ `\`,
  `SUBSET` ↔ `⊆`, `UNION` ↔ `∪`.
- HOL `DISJOINT s t` ↔ `Disjoint s t` (order-theoretic `Disjoint` on
  `Set`, equivalent to `s ∩ t = ∅`).
- HOL `sol x C` ↔ `Kepler.Geom.sol x C` (Kepler/Geom/Volume.lean:36);
  HOL `&4 * pi` ↔ `4 * Real.pi`.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `radialNorm`/`xfan`/`yfan`/`affGe`/`affGt`/`sol`/`FAN`
  vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## `radial_norm` 的基本封闭性（Conforming.hl:859-886） -/

/-- HOL Conforming.hl :859-863 `RADIAL_EMPTY`

HOL 原文：
```
!r v0:real^N. radial_norm r v0 {}
```

编码说明（缺口）：HOL 陈述对一般 `real^N`，仓库 `radialNorm`
（Kepler/Geom/Volume.lean:27）只对 `V3` 定义，故此处限定 `V3`
（不引入新定义）。`radial_norm` ↔ `radialNorm`；`{}` ↔ `∅`。

证明思路：`radialNorm r v0 ∅` 展开为两条合取。第一支 `∅ ⊆ ball v0 r`
用 `Set.empty_subset`。第二支前提 `v0 + u ∈ ∅` 为假，用 `False.elim` /
`Set.not_mem_empty` 收口。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Set.empty_subset`（Mathlib/Data/Set/Basic.lean）
- `Set.not_mem_empty`（Mathlib/Data/Set/Basic.lean）
- 缺口：HOL 的 `real^N` 一般维度未覆盖；`radial_norm` 仅 `V3` 版 -/
theorem RADIAL_EMPTY (r : ℝ) (v0 : V3) :
    radialNorm r v0 (∅ : Set V3) := by
  sorry

/-- HOL Conforming.hl :864-874 `RADIAL_UNIONS`

HOL 原文：
```
!r v0 f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> radial_norm r v0 s)
        ==> (radial_norm r v0 (UNIONS f))
```

编码说明（缺口）：HOL 陈述对一般 `real^N`，仓库 `radialNorm` 只对
`V3` 定义，故此处限定 `V3`（不引入新定义）。`FINITE f` ↔ `f.Finite`
（`Set.Finite`）；`UNIONS f` ↔ `⋃₀ f`（`Set.sUnion`）。

证明思路：对有限集 `f` 作 `Set.Finite.induction_on`（HOL
`FINITE_INDUCT_STRONG`）。空集情形用 `RADIAL_EMPTY`（`sUnion ∅ = ∅`）；
插入情形 `⋃₀ insert s f = s ∪ ⋃₀ f`，用归纳假设与 `RADIAL_UNION`
（ConformingAuto3.lean:588，HOL `RADIAL_UNION`）。

候选已有引理：
- `RADIAL_EMPTY`（本文件上文，HOL :859）
- `RADIAL_UNION`（Kepler/Text/ConformingAuto3.lean:588，HOL :852）
- `Set.Finite.induction_on`（Mathlib/Data/Set/Finite/Basic.lean:716）
- `Set.sUnion_empty`、`Set.sUnion_insert`（Mathlib/Data/Set/Basic.lean）
- 缺口：HOL 的 `real^N` 一般维度未覆盖；`radial_norm` 仅 `V3` 版 -/
theorem RADIAL_UNIONS (r : ℝ) (v0 : V3) (f : Set (Set V3))
    (hfin : f.Finite) (h : ∀ s ∈ f, radialNorm r v0 s) :
    radialNorm r v0 (⋃₀ f) := by
  sorry

/-- HOL Conforming.hl :875-886 `RADIAL_UNIV`

HOL 原文：
```
!r x. r> &0 ==> radial_norm r x ((:real^N) INTER normball x r)
```

编码说明（缺口）：HOL 陈述对一般 `real^N`，仓库 `radialNorm` 只对
`V3` 定义，故此处限定 `V3`（不引入新定义）。`(:real^N)` ↔ `Set.univ`；
`normball x r` ↔ `Metric.ball x r`；`r > &0` ↔ `0 < r`。

证明思路：展开 `radialNorm`。第一支 `Set.univ ∩ ball x r ⊆ ball x r`
用 `Set.inter_subset_right`。第二支设 `x + u ∈ Set.univ ∩ ball x r`，
由 `Metric.mem_ball` 得 `dist (x+u) x < r`，即 `‖u‖ < r`；对 `t > 0`
计算 `dist (x + t • u) x = ‖t • u‖ = t * ‖u‖`，由 `t * ‖u‖ < r` 直接
落入球（HOL 用 `aff_normball`，仓库未移植，改用 `Metric.mem_ball` +
`norm_smul` 直接验证）。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Metric.mem_ball`、`Metric.mem_ball_comm`（Mathlib/Topology/MetricSpace/Basic.lean）
- `norm_smul`、`Real.norm_eq_abs`（Mathlib/Analysis/Normed/...）
- `dist_eq_norm`（Mathlib/Analysis/Normed/Group/Basic.lean）
- 缺口：HOL `aff_normball`（vol1.hl:569）未移植；`real^N` 一般维度未覆盖 -/
theorem RADIAL_UNIV (r : ℝ) (x : V3) (hr : r > 0) :
    radialNorm r x (Set.univ ∩ Metric.ball x r) := by
  sorry

/-! ## 半空间与球的径向性（Conforming.hl:887-943） -/

/-- HOL Conforming.hl :887-913 `RADIAL_AFF_GE_1_2`

HOL 原文：
```
!x u v r.
     (DISJOINT {(x:real^B)} {u,v} /\ (r > &0) ) ==>
     radial_norm r x (aff_ge {x} {u,v} INTER normball x r)
```

编码说明（缺口）：HOL 陈述在 2 维仿射平面 `real^B` 上，仓库
`affGe`（Kepler/Geom/Aff.lean:42）与 `radialNorm`
（Kepler/Geom/Volume.lean:27）只对 `V3` 定义，故此处限定 `V3`
（不引入新定义）。`DISJOINT` ↔ `Disjoint`；`aff_ge` ↔ `affGe`；
`normball` ↔ `Metric.ball`。

证明思路：展开 `radialNorm`。第一支用 `Set.inter_subset_right`。第二支
设 `x + u' ∈ affGe {x} {u,v} ∩ ball x r`，用
`mem_affGe_singleton_pair`（TopologyFan.lean:2019，HOL `AFF_GE_1_2`）把
`x + u'` 写成 `t1 • x + t2 • u + t3 • v`（`t2,t3 ≥ 0`）；对 `t > 0`
构造系数 `1 + t*t1 - t`、`t*t2`、`t*t3`（均为非负、和为 `1`），并计算
`(1 + t*t1 - t) • x + (t*t2) • u + (t*t3) • v = x + t • u'`；落入球的部分
用球的凸性或 `Metric.mem_ball` + `norm_smul`（HOL 用 `aff_normball`，仓库
未移植）。

候选已有引理：
- `mem_affGe_singleton_pair`（Kepler/Text/TopologyFan.lean:2019，HOL `AFF_GE_1_2`）
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Metric.mem_ball`、`norm_smul`（Mathlib）
- `Real.le_mul_of_one_le_left`、`mul_nonneg`（Mathlib，用于系数非负）
- 缺口：HOL `aff_normball` 未移植；`real^B`（2 维）未覆盖 -/
theorem RADIAL_AFF_GE_1_2 (x u v : V3) (r : ℝ)
    (hdisj : Disjoint ({x} : Set V3) {u, v}) (hr : r > 0) :
    radialNorm r x (affGe ({x} : Set V3) {u, v} ∩ Metric.ball x r) := by
  sorry

/-- HOL Conforming.hl :914-943 `RADIAL_AFF_GT_3_1`

HOL 原文：
```
!x u v w r.
     (DISJOINT {(x:real^B),u,v} {w} /\ (r > &0) ) ==>
     radial_norm r x (aff_gt {x,u,v} {w} INTER normball x r)
```

编码说明（缺口）：HOL 陈述在 2 维仿射平面 `real^B` 上，仓库 `affGt`
（Kepler/Geom/Aff.lean:39）与 `radialNorm`（Kepler/Geom/Volume.lean:27）
只对 `V3` 定义，故此处限定 `V3`（不引入新定义）。`DISJOINT` ↔ `Disjoint`；
`aff_gt` ↔ `affGt`；`normball` ↔ `Metric.ball`。

证明思路：展开 `radialNorm`。第一支用 `Set.inter_subset_right`。第二支
设 `x + u' ∈ affGt {x,u,v} {w} ∩ ball x r`，用 `AFF_GT_3_1`
（PlanarityAuto11.lean:957，HOL `AFF_GT_3_1`）把 `x + u'` 写成
`t1•x + t2•u + t3•v + t4•w`（`0 < t4`）；对 `t > 0` 构造系数
`1 + t*t1 - t`、`t*t2`、`t*t3`、`t*t4`（`t*t4 > 0` 由 `Real.mul_pos`），
并计算仿射组合等于 `x + t • u'`；落入球的部分用 `Metric.mem_ball` +
`norm_smul`（HOL 用 `aff_normball`，仓库未移植）。

候选已有引理：
- `AFF_GT_3_1`（Kepler/Text/PlanarityAuto11.lean:957，HOL `AFF_GT_3_1`）
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Metric.mem_ball`、`norm_smul`（Mathlib）
- `Real.mul_pos`（Mathlib，用于 `t * t4 > 0`）
- 缺口：HOL `aff_normball` 未移植；`real^B`（2 维）未覆盖 -/
theorem RADIAL_AFF_GT_3_1 (x u v w : V3) (r : ℝ)
    (hdisj : Disjoint ({x, u, v} : Set V3) {w}) (hr : r > 0) :
    radialNorm r x (affGt ({x, u, v} : Set V3) {w} ∩ Metric.ball x r) := by
  sorry

/-! ## 交集与球（Conforming.hl:944-957） -/

/-- HOL Conforming.hl :944-957 `RADIAL_INTERS`

HOL 原文：
```
!r v0 f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> radial_norm r v0 (s INTER normball v0 r))/\  r> &0
        ==> (radial_norm r v0 (INTERS f INTER normball v0 r))
```

编码说明（缺口）：HOL 陈述对一般 `real^N`，仓库 `radialNorm` 只对
`V3` 定义，故此处限定 `V3`（不引入新定义）。`FINITE f` ↔ `f.Finite`；
`INTERS f` ↔ `⋂₀ f`（`Set.sInter`）；`INTER` ↔ `∩`；`normball` ↔
`Metric.ball`。

证明思路：对有限集 `f` 作 `Set.Finite.induction_on`（HOL
`FINITE_INDUCT_STRONG`）。空集情形 `⋂₀ ∅ = univ`，结论化为
`radialNorm r v0 (univ ∩ ball v0 r)`，即 `RADIAL_UNIV`（本文件上文，
HOL :875）。插入情形把 `(s ∩ ⋂₀ f) ∩ ball` 重排为
`(s ∩ ball) ∩ (⋂₀ f ∩ ball)`，对两个径向集用交集封闭性
（HOL `inter_radial`，仓库未移植，需现场证明或作为子引理）。

候选已有引理：
- `RADIAL_UNIV`（本文件上文，HOL :875）
- `Set.Finite.induction_on`（Mathlib/Data/Set/Finite/Basic.lean:716）
- `Set.sInter_empty`、`Set.sInter_insert`（Mathlib/Data/Set/Basic.lean）
- `Set.inter_assoc`、`Set.inter_comm`（Mathlib/Data/Set/Basic.lean）
- 缺口：HOL `inter_radial`（Conforming.hl 上文）未移植；`real^N` 一般维度未覆盖 -/
theorem RADIAL_INTERS (r : ℝ) (v0 : V3) (f : Set (Set V3))
    (hfin : f.Finite) (h : ∀ s ∈ f, radialNorm r v0 (s ∩ Metric.ball v0 r))
    (hr : r > 0) :
    radialNorm r v0 (⋂₀ f ∩ Metric.ball v0 r) := by
  sorry

/-! ## `xfan` 的并集分解与径向性（Conforming.hl:958-1007） -/

/-- HOL Conforming.hl :958-985 `XFAN_INTER_BALL_UNIONS`

HOL 原文：
```
!x:real^N V E.
xfan(x,V,E) INTER normball x r= UNIONS {y | ?e. e IN E /\ y = (aff_ge {x} e) INTER normball x r}
```

编码说明：HOL 中 `r` 为自由变量（`prove` 隐式全称化），此处显式列为
参数。`xfan` ↔ `xfan`（Kepler/Text/Fan.lean:154）；`normball` ↔
`Metric.ball`；`UNIONS {y | ?e. e IN E /\ y = f e}` ↔ `⋃ e ∈ E, f e`
（`Set.iUnion`）；`aff_ge` ↔ `affGe`。

证明思路：先用 `XFAN_EQ_UNIONS_AFF_GE_1_2`（ConformingAuto3.lean:306）
把 `xfan x V E` 写成 `⋃ e ∈ E, affGe {x} e`，再对集合等式用
`Set.ext`（HOL `EXTENSION`）与 `Set.mem_inter_iff`、`Set.mem_iUnion`、
`Set.mem_setOf_eq` 逐点化简；两个方向分别取/消去见证 `e ∈ E`。

候选已有引理：
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:306，HOL :746）
- `xfan`（Kepler/Text/Fan.lean:154）
- `Set.ext`、`Set.mem_iUnion`、`Set.mem_inter_iff`（Mathlib/Data/Set/Basic.lean）
- 缺口：无（`r` 由隐式全称改为显式参数） -/
theorem XFAN_INTER_BALL_UNIONS (x : V3) (V : Set V3) (E : Set (Set V3)) (r : ℝ) :
    xfan x V E ∩ Metric.ball x r =
      ⋃ e ∈ E, (affGe ({x} : Set V3) e ∩ Metric.ball x r) := by
  sorry

/-- HOL Conforming.hl :986-1007 `RADIAL_XFAN_INTER_BALL`

HOL 原文：
```
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) r.
FAN (x,V,E) /\ r> &0 ==>  radial_norm r x  (xfan (x,V,E) INTER normball x r)
```

编码说明：`FAN (x,V,E)` ↔ `FAN x V E`（Kepler/Text/Fan.lean:56）；
`xfan` ↔ `xfan`；`normball` ↔ `Metric.ball`；`radial_norm` ↔
`radialNorm`。

证明思路：用 `XFAN_INTER_BALL_UNIONS`（本文件上文，HOL :958）把
`xfan ∩ ball` 写成 `⋃ e ∈ E, (affGe {x} e ∩ ball x r)`，再用
`RADIAL_UNIONS`（本文件上文，HOL :864）；有限性来自
`setEdgesFiniteFan`（Fan.lean:851，HOL `set_edges_is_finite_fan`）；对
每个 `e ∈ E` 用 `expand_edge_graph_fan`（TopologyFan.lean:3212）写成
`e = {v,w}`，再用 `RADIAL_AFF_GE_1_2`（本文件上文，HOL :887）；其中
`Disjoint {x} {v,w}` 由 `FAN` 的 `remark1_fan` 互异性分量
`edge_ne_of_fan`（Fan.lean:1039）给出。

候选已有引理：
- `XFAN_INTER_BALL_UNIONS`（本文件上文，HOL :958）
- `RADIAL_UNIONS`（本文件上文，HOL :864）
- `RADIAL_AFF_GE_1_2`（本文件上文，HOL :887）
- `setEdgesFiniteFan`（Kepler/Text/Fan.lean:851，HOL `set_edges_is_finite_fan`）
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异性分量）
- 缺口：HOL `remark1_fan`、`FINITE_IMAGE` 未以该名移植 -/
theorem RADIAL_XFAN_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3)) (r : ℝ)
    (hfan : FAN x V E) (hr : r > 0) :
    radialNorm r x (xfan x V E ∩ Metric.ball x r) := by
  sorry

/-! ## `yfan` 的径向性与立体角（Conforming.hl:1008-1036） -/

/-- HOL Conforming.hl :1008-1023 `RADIAL_NORM_YFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r.
FAN(x,V,E) /\ r> &0
==> radial_norm r x ( (yfan (x,V,E)) INTER normball x r)
```

编码说明：`FAN(x,V,E)` ↔ `FAN x V E`；`yfan` ↔ `yfan`
（Kepler/Text/Fan.lean:158）；`normball` ↔ `Metric.ball`；
`radial_norm` ↔ `radialNorm`。

证明思路：把 `yfan = univ \ xfan` 代入，并用
`(univ \ xfan) ∩ ball = (univ ∩ ball) \ (xfan ∩ ball)`
（HOL `SET_RULE`）。由 `RADIAL_UNIV`（本文件上文，HOL :875）得
`radialNorm r x (univ ∩ ball x r)`，由 `RADIAL_XFAN_INTER_BALL`
（本文件上文，HOL :986）得 `radialNorm r x (xfan ∩ ball x r)`，再对
差集用 `RADIAL_DIFF`（ConformingAuto3.lean:545，HOL :815）；子集关系
`xfan ∩ ball ⊆ univ ∩ ball` 由 `Set.inter_subset_right` 与
`Set.subset_univ` 给出。

候选已有引理：
- `RADIAL_UNIV`（本文件上文，HOL :875）
- `RADIAL_XFAN_INTER_BALL`（本文件上文，HOL :986）
- `RADIAL_DIFF`（Kepler/Text/ConformingAuto3.lean:545，HOL :815）
- `yfan`（Kepler/Text/Fan.lean:158）
- `Set.diff_inter`、`Set.inter_subset_right`、`Set.subset_univ`（Mathlib/Data/Set/Basic.lean）
- 缺口：无 -/
theorem RADIAL_NORM_YFAN_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3)) (r : ℝ)
    (hfan : FAN x V E) (hr : r > 0) :
    radialNorm r x (yfan x V E ∩ Metric.ball x r) := by
  sorry

/-- HOL Conforming.hl :1024-1036 `SOLID_ANGLE_YFAN`

HOL 原文：
```
!x:real^3 V E.
FAN (x,V,E) ==>  sol x (yfan (x,V,E))= &4 * pi
```

编码说明：`FAN (x,V,E)` ↔ `FAN x V E`；`yfan` ↔ `yfan`；HOL
`sol x C` ↔ `Kepler.Geom.sol x C`（Kepler/Geom/Volume.lean:36）；
`&4 * pi` ↔ `4 * Real.pi`。

证明思路：取半径 `r = 1 > 0`，由 `RADIAL_NORM_YFAN_INTER_BALL`
（本文件上文，HOL :1008）得 `radialNorm 1 x (yfan ∩ ball x 1)`，由
`MESURABLE_YFAN_INTER_BALL`（ConformingAuto3.lean:499）得可测性，再用
`sol_spec`（Volume.lean:171）把 `sol x (yfan)` 写成
`3 * volume.real (yfan ∩ ball x 1) / 1 ^ 3`；由
`MEASURE_YFAN_INTER_BALL`（ConformingAuto3.lean:454）得
`volume.real (yfan ∩ ball x 1) = (4/3) * π * 1 ^ 3`；最后 `ring` 收口。

候选已有引理：
- `RADIAL_NORM_YFAN_INTER_BALL`（本文件上文，HOL :1008）
- `MESURABLE_YFAN_INTER_BALL`（Kepler/Text/ConformingAuto3.lean:499，HOL :800）
- `MEASURE_YFAN_INTER_BALL`（Kepler/Text/ConformingAuto3.lean:454，HOL :786）
- `sol_spec`（Kepler/Geom/Volume.lean:171，HOL `sol`）
- `sol`（Kepler/Geom/Volume.lean:36）
- 缺口：无 -/
theorem SOLID_ANGLE_YFAN (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) :
    sol x (yfan x V E) = 4 * Real.pi := by
  sorry
