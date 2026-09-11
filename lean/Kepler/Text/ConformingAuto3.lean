/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 3
(Conforming.hl:731-858).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 3, Conforming.hl:731-858):
- `HAS_MEASURE_AFF_GT_1_2_INTER_BALL` (731)
- `MEASURABLE_AFF_GT_2_1_INTER_BALL` (738)
- `XFAN_EQ_UNIONS_AFF_GE_1_2` (746)
- `NEGLIGIBLE_XFAN` (754)
- `NEGLIGIBLE_XFAN_INTER_BALL` (772)
- `HAS_MEASURE_XFAN_INTER_BALL` (779)
- `MEASURE_YFAN_INTER_BALL` (786)
- `MESURABLE_YFAN_INTER_BALL` (800)
- `RADIAL_DIFF` (815)
- `RADIAL_UNION` (852)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL `xfan`/
  `yfan` ↔ `xfan`/`yfan` (Kepler/Text/Fan.lean:154/158); HOL
  `aff_ge`/`aff_gt` ↔ `affGe`/`affGt` (Kepler/Geom/Aff.lean:42/39).
- HOL `UNIONS S` ↔ `⋃₀ S` (`Set.sUnion`), cf.
  Kepler/Text/PlanarityAuto12.lean:47/120.
- HOL `negligible s` and `measure s = &0` are NOT ported; both are
  encoded as the Mathlib Lebesgue null predicate `volume s = 0`
  (`volume : Measure V3`, cf. Kepler/Text/ConformingAuto2.lean:55-59).
- HOL `s has_measure m` (`measure1.ml:19`) is NOT ported. For the only
  use here (`m = &0`) the HOL equivalence `HAS_MEASURE_0`
  (`measure1.ml:327`, `s has_measure &0 <=> negligible s`) makes the
  closest encoding `volume s = 0` (same as `negligible`); the
  measurability conjunct of `HAS_MEASURE_MEASURABLE_MEASURE`
  (`measure1.ml:46`) is dropped, which is harmless for the `&0` case in
  the repo's encoding.
- HOL `measure s` (a real) is encoded as `volume.real s` = `(volume s).toReal`
  (the repo's real-valued volume, cf. Kepler/Geom/Volume.lean:40), used by
  `MEASURE_YFAN_INTER_BALL`; for a measurable finite-measure set this is
  exactly HOL's `measure`.
- HOL `measurable` ↔ `MeasurableSet`; HOL `normball x r` ↔ Mathlib
  `Metric.ball x r`; HOL `~collinear {x,v,u}` ↔ `¬ Collinear3 x v u`
  (Kepler/Geom/Azim.lean:43).
- HOL `real^N` (RADIAL_DIFF / RADIAL_UNION) is encoded with the repo's
  `V3`-specialised `radialNorm` (Kepler/Geom/Volume.lean:27), since the
  general `real^N` version is not ported; `B DIFF A` ↔ `B \ A`, `A UNION B`
  ↔ `A ∪ B`.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`xfan`/`yfan`/`affGt`/`radialNorm` vocabulary, so
  nothing is skipped.
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
open MeasureTheory
open scoped Topology
open scoped BigOperators

/-! ## 1-2 型仿射半空间的零测与可测（Conforming.hl:731-745） -/

/-- HOL Conforming.hl :731-737 `HAS_MEASURE_AFF_GT_1_2_INTER_BALL`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 r:real.
~collinear {x,v,u}==>  (aff_gt {x} {v,u} INTER normball x r)  has_measure  &0
```

编码说明（缺口）：HOL `s has_measure m`（measure1.ml:19）未移植；对
`m = &0` 由 `HAS_MEASURE_0`（measure1.ml:327）有
`s has_measure &0 <=> negligible s`，故按本仓库 `negligible` 的编码取
`volume s = 0`（见文件头）。`aff_gt {x} {v,u}` ↔
`affGt ({x} : Set V3) {v,u}`；`normball x r` ↔ `Metric.ball x r`；
`~collinear {x,v,u}` ↔ `¬ Collinear3 x v u`。

证明思路：HOL 由 `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL` 与 `HAS_MEASURE_0`
改写。在 `volume = 0` 编码下结论与
`NEGLIGIBLE_AFF_GT_1_2_INTER_BALL` 类型相同，直接引用即可。

候选已有引理：
- `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL`
  （Kepler/Text/ConformingAuto2.lean:468）
- `NEGLIGIBLE_AFF_GT_1_2`（Kepler/Text/ConformingAuto2.lean:415）
- 缺口：HOL `has_measure`、`HAS_MEASURE_0`（measure1.ml:327）未移植 -/
theorem HAS_MEASURE_AFF_GT_1_2_INTER_BALL (x v u : V3) (r : ℝ)
    (h : ¬ Collinear3 x v u) :
    volume (affGt ({x} : Set V3) {v, u} ∩ Metric.ball x r) = 0 := by
  sorry

/-- HOL Conforming.hl :738-745 `MEASURABLE_AFF_GT_2_1_INTER_BALL`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 r:real.
~collinear {x,v,u}==>   measurable (aff_gt {x} {v,u} INTER normball x r)
```

编码说明（缺口）：HOL 名虽为 `GT_2_1`，陈述中的集合仍是 1-2 型
`aff_gt {x} {v,u}`（名称原样保留）。HOL `measurable` ↔ `MeasurableSet`；
`aff_gt {x} {v,u}` ↔ `affGt ({x} : Set V3) {v,u}`；`normball x r` ↔
`Metric.ball x r`；`~collinear {x,v,u}` ↔ `¬ Collinear3 x v u`。

证明思路：HOL 由 `HAS_MEASURE_AFF_GT_1_2_INTER_BALL` 取
`measure = &0` 见证 `measurable`。Lean 侧两条独立路线：
(i) `affGt {x} {v,u}` 与球交可写为可数并/相对开集从而 Borel 可测；
(ii) 由 `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL` 与 `volume = 0`（在
完备 Lebesgue 测度下零测集可测）。

候选已有引理：
- `HAS_MEASURE_AFF_GT_1_2_INTER_BALL`（本文件上文，HOL :731）
- `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL`
  （Kepler/Text/ConformingAuto2.lean:468）
- `measure_mono_null`
  （Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `MeasurableSet.inter`
  （Mathlib/MeasureTheory/MeasurableSpace/Defs.lean）
- 缺口：HOL `measurable`（measure1.ml:22）、
  `HAS_MEASURE_MEASURABLE_MEASURE`（measure1.ml:46）未移植 -/
theorem MEASURABLE_AFF_GT_2_1_INTER_BALL (x v u : V3) (r : ℝ)
    (h : ¬ Collinear3 x v u) :
    MeasurableSet (affGt ({x} : Set V3) {v, u} ∩ Metric.ball x r) := by
  sorry

/-! ## `xfan` 的并集表示与零测性（Conforming.hl:746-785） -/

/-- HOL Conforming.hl :746-753 `XFAN_EQ_UNIONS_AFF_GE_1_2`

HOL 原文：
```
!x V E.
xfan(x,V,E) =UNIONS {y | ?e. e IN E /\ y = aff_ge {x} e}
```

编码说明：HOL `UNIONS S` ↔ `⋃₀ S`（`Set.sUnion`）；集合描述
`{y | ?e. e IN E /\ y = aff_ge {x} e}` 编码为
`{y : Set V3 | ∃ e ∈ E, y = affGe ({x} : Set V3) e}`。该等式即
`xfan` 定义（Kepler/Text/Fan.lean:154）的 `Set.mem_sUnion` 展开。

证明思路：`ext v; simp only [xfan, Set.mem_sUnion, Set.mem_setOf_eq]`
后两条 `∃ e ∈ E, v ∈ affGe {x} e` 与 `∃ e ∈ E, v ∈ affGe {x} e`
定义等价（`Set.sUnion` 成员性 + 存在量词换序）。

候选已有引理：
- `xfan`（Kepler/Text/Fan.lean:154）
- `affGe`（Kepler/Geom/Aff.lean:42）
- `Set.mem_sUnion`（Mathlib/Data/Set/Lattice.lean） -/
theorem XFAN_EQ_UNIONS_AFF_GE_1_2 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    xfan x V E = ⋃₀ {y : Set V3 | ∃ e ∈ E, y = affGe ({x} : Set V3) e} := by
  sorry

/-- HOL Conforming.hl :754-771 `NEGLIGIBLE_XFAN`

HOL 原文：
```
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool).
FAN (x,V,E) ==>  negligible (xfan (x,V,E))
```

编码说明（缺口）：HOL `negligible s` 未移植，按本仓库编码取
`volume s = 0`（见文件头）。

证明思路：用 `XFAN_EQ_UNIONS_AFF_GE_1_2` 把 `xfan` 写成边锥之并；由
`setEdgesFiniteFan` 得 `E` 有限，`measure_sUnion_null_iff`
（或 `measure_biUnion_null_iff`）把问题化为对每条边 `e ∈ E` 证
`volume (affGe {x} e) = 0`；`expand_edge_graph_fan` 写 `e = {v,w}`，
再由 `fan_not_collinear`（或 `remark1_fan` 成员性 + 边不退化）得
`¬ Collinear3 x v w`，最后用 `NEGLIGIBLE_AFF_GE_1_2`。

候选已有引理：
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（本文件上文，HOL :746）
- `setEdgesFiniteFan`（Kepler/Text/Fan.lean:849）
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `fan_not_collinear`（Kepler/Text/Fan.lean:342）
- `NEGLIGIBLE_AFF_GE_1_2`（Kepler/Text/ConformingAuto2.lean:386）
- `measure_sUnion_null_iff`
  （Mathlib/MeasureTheory/OuterMeasure/Basic.lean:113）
- 缺口：HOL `NEGLIGIBLE_UNIONS`（measure.ml）、`remark1_fan`
  （fan.hl:423）未以该名移植 -/
theorem NEGLIGIBLE_XFAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    volume (xfan x V E) = 0 := by
  sorry

/-- HOL Conforming.hl :772-778 `NEGLIGIBLE_XFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V:real^3->bool (E:(real^3->bool)->bool) r:real.
FAN (x,V,E) ==>  negligible (xfan (x,V,E) INTER normball x r)
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
`normball x r` ↔ `Metric.ball x r`。

证明思路：由 `Set.inter_subset_left` 得
`xfan x V E ∩ Metric.ball x r ⊆ xfan x V E`，再用 `measure_mono_null`
与 `NEGLIGIBLE_XFAN`。

候选已有引理：
- `NEGLIGIBLE_XFAN`（本文件上文，HOL :754）
- `measure_mono_null`
  （Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `Set.inter_subset_left`（Mathlib/Data/Set/Basic.lean） -/
theorem NEGLIGIBLE_XFAN_INTER_BALL {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (r : ℝ) :
    volume (xfan x V E ∩ Metric.ball x r) = 0 := by
  sorry

/-- HOL Conforming.hl :779-785 `HAS_MEASURE_XFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r.
FAN (x,V,E) ==>  (xfan (x,V,E) INTER normball x r)  has_measure  &0
```

编码说明（缺口）：HOL `s has_measure &0` 由 `HAS_MEASURE_0`
（measure1.ml:327）等价于 `negligible s`，故编码为 `volume s = 0`
（见文件头）；`normball x r` ↔ `Metric.ball x r`。

证明思路：HOL 由 `NEGLIGIBLE_XFAN_INTER_BALL` 与 `HAS_MEASURE_0`
改写。在 `volume = 0` 编码下与 `NEGLIGIBLE_XFAN_INTER_BALL` 类型相同。

候选已有引理：
- `NEGLIGIBLE_XFAN_INTER_BALL`（本文件上文，HOL :772）
- 缺口：HOL `has_measure`、`HAS_MEASURE_0`（measure1.ml:327）未移植 -/
theorem HAS_MEASURE_XFAN_INTER_BALL {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (r : ℝ) :
    volume (xfan x V E ∩ Metric.ball x r) = 0 := by
  sorry

/-! ## 球与 `yfan` 交的体积与可测性（Conforming.hl:786-814） -/

/-- HOL Conforming.hl :786-799 `MEASURE_YFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r.
FAN(x,V,E)/\ &0<= r
==> measure ( (yfan (x,V,E)) INTER normball x r)= &4/ &3 *pi *r pow 3
```

编码说明（缺口）：HOL `measure s`（实值）编码为 `volume.real s`
（`(volume s).toReal`，Kepler/Geom/Volume.lean:40）；`yfan` 定义见
Kepler/Text/Fan.lean:158（`yfan = univ \ xfan`）；`normball x r` ↔
`Metric.ball x r`；`&4/ &3 * pi * r pow 3` ↔ `4 / 3 * Real.pi * r ^ 3`。

证明思路：`yfan x V E ∩ ball = ball \ (xfan x V E ∩ ball)`（集合恒等）；
由 `HAS_MEASURE_XFAN_INTER_BALL` 得内层零测，故实值测度不变
（`Measure.real` 与 `measure_diff_null`/`n_null`）；最后
`volume_ball_fin_three` 给出 `volume.real (ball x r) = 4/3 * π * r^3`。

候选已有引理：
- `HAS_MEASURE_XFAN_INTER_BALL`（本文件上文，HOL :779）
- `volume_ball_fin_three`
  （Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:408）
- `Measure.real_def`（Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:107）
- `n_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean，旧名
  `measure_diff_null`）
- `yfan`（Kepler/Text/Fan.lean:158）
- 缺口：HOL `VOLUME_BALL`、`MEASURE_DIFF_SUBSET` 未以该名移植 -/
theorem MEASURE_YFAN_INTER_BALL {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (r : ℝ) (hr : 0 ≤ r) :
    volume.real (yfan x V E ∩ Metric.ball x r) = 4 / 3 * Real.pi * r ^ 3 := by
  sorry

/-- HOL Conforming.hl :800-814 `MESURABLE_YFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r.
FAN(x,V,E)/\ &0<= r
==> measurable ( (yfan (x,V,E)) INTER normball x r)
```

编码说明（缺口）：HOL `measurable` ↔ `MeasurableSet`；`yfan` 定义见
Kepler/Text/Fan.lean:158；`normball x r` ↔ `Metric.ball x r`。

证明思路：`yfan x V E ∩ ball = ball \ (xfan x V E ∩ ball)`；球可测
（`Metric.isOpen_ball.measurableSet`），由
`HAS_MEASURE_XFAN_INTER_BALL` 得内层零测从而可测，再用
`MeasurableSet.diff` 取差集可测。

候选已有引理：
- `HAS_MEASURE_XFAN_INTER_BALL`（本文件上文，HOL :779）
- `MeasurableSet.diff`
  （Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:175）
- `Metric.isOpen_ball`（Mathlib/Topology/MetricSpace/…）
- `IsOpen.measurableSet`
  （Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:26）
- `yfan`（Kepler/Text/Fan.lean:158）
- 缺口：HOL `MEASURABLE_DIFF`、`MEASURABLE_BALL` 未以该名移植 -/
theorem MESURABLE_YFAN_INTER_BALL {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (r : ℝ) (hr : 0 ≤ r) :
    MeasurableSet (yfan x V E ∩ Metric.ball x r) := by
  sorry

/-! ## 径向集合的差与并（Conforming.hl:815-858） -/

/-- HOL Conforming.hl :815-851 `RADIAL_DIFF`

HOL 原文：
```
!r v0 A B:real^N->bool. radial_norm r v0 A /\ radial_norm r v0 B /\ A SUBSET B ==> radial_norm r v0 (B DIFF A)
```

编码说明（缺口）：HOL `radial_norm`（vol1.hl:18）对一般 `real^N` 定义，
仓库仅移植 `V3` 版 `radialNorm`（Kepler/Geom/Volume.lean:27），故
`v0 : V3`、`A B : Set V3`；`B DIFF A` ↔ `B \ A`。

证明思路：展开 `radialNorm`（两项：包含性与径向封闭性）。包含性由
`hB.1` 与 `Set.diff_subset` 给出；径向封闭性用反证：设
`v0 + u ∈ B \ A`、`0 < t`、`t * ‖u‖ < r`。若 `v0 + t • u ∉ B \ A`，
则或 `v0 + t • u ∉ B`（与 `hB.2` 矛盾），或 `v0 + t • u ∈ A`；后者
再对 `A` 用径向封闭（`inv t` 缩放）把 `v0 + u` 拉回 `A`，与
`v0 + u ∉ A` 矛盾（此处需 `hB.1` 的球包含以约束 `‖u‖`）。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Set.diff_subset`、`Set.mem_diff`（Mathlib/Data/Set/Basic.lean）
- `radialNorm.volume_scaling`（Kepler/Geom/Volume.lean:78）
- 缺口：HOL `radial_norm` 的 `real^N` 一般版未移植 -/
theorem RADIAL_DIFF {r : ℝ} {v0 : V3} {A B : Set V3}
    (hA : radialNorm r v0 A) (hB : radialNorm r v0 B) (hAB : A ⊆ B) :
    radialNorm r v0 (B \ A) := by
  sorry

/-- HOL Conforming.hl :852-858 `RADIAL_UNION`

HOL 原文：
```
!r v0 A B:real^N->bool. radial_norm r v0 A /\ radial_norm r v0 B ==> radial_norm r v0 (A UNION B)
```

编码说明（缺口）：HOL `radial_norm`（vol1.hl:18）对一般 `real^N` 定义，
仓库仅移植 `V3` 版 `radialNorm`（Kepler/Geom/Volume.lean:27），故
`v0 : V3`、`A B : Set V3`；`A UNION B` ↔ `A ∪ B`。

证明思路：展开 `radialNorm`。包含性：`(A ∪ B) ⊆ ball x r` 由
`hA.1`、`hB.1` 与 `Set.union_subset` 给出；径向封闭性：对
`v0 + u ∈ A ∪ B` 分情形，分别用 `hA.2`/`hB.2`。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Set.union_subset`、`Set.mem_union`（Mathlib/Data/Set/Basic.lean）
- 缺口：HOL `radial_norm` 的 `real^N` 一般版未移植 -/
theorem RADIAL_UNION {r : ℝ} {v0 : V3} {A B : Set V3}
    (hA : radialNorm r v0 A) (hB : radialNorm r v0 B) :
    radialNorm r v0 (A ∪ B) := by
  sorry

end Kepler.Text
