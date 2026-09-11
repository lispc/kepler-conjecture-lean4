/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 3
(Conforming.hl:731-858).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 3, Conforming.hl:731-858):
- `HAS_MEASURE_AFF_GT_1_2_INTER_BALL` (731)
- `MEASURABLE_AFF_GT_2_1_INTER_BALL` (738; HOL name says 2-1 but the
  statement is about the 1-2 set `aff_gt {x} {v,u}`; the name is kept
  verbatim)
- `XFAN_EQ_UNIONS_AFF_GE_1_2` (746)
- `NEGLIGIBLE_XFAN` (754)
- `NEGLIGIBLE_XFAN_INTER_BALL` (772)
- `HAS_MEASURE_XFAN_INTER_BALL` (779)
- `MEASURE_YFAN_INTER_BALL` (786)
- `MESURABLE_YFAN_INTER_BALL` (800; HOL misspelling kept verbatim)
- `RADIAL_DIFF` (815)
- `RADIAL_UNION` (852)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56).
- HOL `xfan (x,V,E)` ↔ `xfan x V E` (Kepler/Text/Fan.lean:154);
  HOL `yfan (x,V,E)` = `UNIV DIFF xfan` ↔ `yfan x V E`
  (Kepler/Text/Fan.lean:158).
- HOL `normball x r` ↔ Mathlib `Metric.ball x r` (both are
  `{y | dist y x < r}`; cf. `NORMBALL_BALL`, sphere.hl).
- HOL `aff_ge`/`aff_gt` ↔ `affGe`/`affGt` (Kepler/Geom/Aff.lean:39/42);
  HOL `collinear {x,v,u}` ↔ `Collinear3 x v u` (Kepler/Geom/Azim.lean:43).
- HOL `UNIONS {y | ?e. e IN E /\ y = f e}` ↔ `⋃ e ∈ E, f e`
  (`Set.iUnion`); HOL `INTER` ↔ `∩`, `DIFF` ↔ `\`, `SUBSET` ↔ `⊆`,
  `UNION` ↔ `∪`.
- HOL `measurable` ↔ `MeasurableSet`; HOL `negligible s`,
  `measure s = &0` and `s has_measure &0` are all encoded as the Mathlib
  Lebesgue measure-zero predicate `volume s = 0` (cf.
  Kepler/Text/ConformingAuto2.lean:55-59). For the non-zero value in
  `MEASURE_YFAN_INTER_BALL`, HOL `measure s` (a real) is encoded as
  `volume.real s` (`Measure.real`, the real-valued part of `volume`),
  matching `Kepler.Geom.Volume`'s use of `volume.real`
  (Kepler/Geom/Volume.lean:40).
- HOL `radial_norm r v0 C` ↔ `radialNorm r v0 C`
  (Kepler/Geom/Volume.lean:27). HOL's statement is for a general
  `real^N`; the repo only defines `radialNorm` for `V3`, so `RADIAL_DIFF`
  and `RADIAL_UNION` are stated for `V3` (noted per-theorem).
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`xfan`/`yfan`/`affGt`/`affGe`/`radialNorm`
  vocabulary (or is the exact `affGt`-ball statement already ported in
  ConformingAuto2), so nothing is skipped.
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

/-! ## `aff_gt` 与球的测度/可测性（Conforming.hl:731-745） -/

/-- HOL Conforming.hl :731-737 `HAS_MEASURE_AFF_GT_1_2_INTER_BALL`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 r:real.
~collinear {x,v,u}==>  (aff_gt {x} {v,u} INTER normball x r)  has_measure  &0
```

编码说明（缺口）：HOL `has_measure &0`（= `measure s = &0`）未移植，
与 `negligible` 定义等价，统一编码为 `volume s = 0`（见文件头）；
`aff_gt {x} {v,u}` ↔ `affGt ({x} : Set V3) {v,u}`；
`normball x r` ↔ `Metric.ball x r`；HOL `~collinear {x,v,u}` ↔
`¬ Collinear3 x v u`。

证明思路：HOL 由 `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL` 与
`HAS_MEASURE_0` 收口。在 `volume = 0` 编码下结论与
`MEASURE_AFF_GT_2_1_INTER_BALL` 类型完全相同，直接引用即可。

候选已有引理：
- `MEASURE_AFF_GT_2_1_INTER_BALL`（Kepler/Text/ConformingAuto2.lean:495，
  类型完全相同）
- `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL`（Kepler/Text/ConformingAuto2.lean:468）
- `NEGLIGIBLE_AFF_GT_1_2`（Kepler/Text/ConformingAuto2.lean:415）
- 缺口：HOL `HAS_MEASURE_0` 未移植 -/
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

编码说明（缺口）：HOL 名虽为 `2_1`，陈述中的集合是 1-2 型
`aff_gt {x} {v,u}`（名称原样保留）。HOL `measurable` ↔ `MeasurableSet`；
`aff_gt {x} {v,u}` ↔ `affGt ({x} : Set V3) {v,u}`；
`normball x r` ↔ `Metric.ball x r`；HOL `~collinear {x,v,u}` ↔
`¬ Collinear3 x v u`。

证明思路：HOL 由 `HAS_MEASURE_AFF_GT_1_2_INTER_BALL` 得
`measure = 0`，再由 `HAS_MEASURE_MEASURABLE_MEASURE` 得可测。在
Mathlib 中由 `MEASURE_AFF_GT_2_1_INTER_BALL` 给出的零测性，
用 `measurableSet_of_null`（Lebesgue 测度完备）得 `MeasurableSet`。

候选已有引理：
- `MEASURE_AFF_GT_2_1_INTER_BALL`（Kepler/Text/ConformingAuto2.lean:495）
- `measurableSet_of_null`（Mathlib/MeasureTheory/Measure/NullMeasurable.lean:434，
  需 `volume.IsComplete` 实例）
- 缺口：HOL `measurable` 定义与 `HAS_MEASURE_MEASURABLE_MEASURE` 未移植 -/
theorem MEASURABLE_AFF_GT_2_1_INTER_BALL (x v u : V3) (r : ℝ)
    (h : ¬ Collinear3 x v u) :
    MeasurableSet (affGt ({x} : Set V3) {v, u} ∩ Metric.ball x r) := by
  sorry

/-! ## `xfan` 的并表示与零测性（Conforming.hl:746-785） -/

/-- HOL Conforming.hl :746-753 `XFAN_EQ_UNIONS_AFF_GE_1_2`

HOL 原文：
```
!x V E.
xfan(x,V,E) =UNIONS {y | ?e. e IN E /\ y = aff_ge {x} e}
```

编码说明：HOL `UNIONS {y | ?e. e IN E /\ y = aff_ge {x} e}` 是像集
`{aff_ge {x} e | e ∈ E}` 的并，编码为 `⋃ e ∈ E, affGe ({x} : Set V3) e`
（`Set.iUnion` 的 `∈` 绑定）；`xfan` ↔ `xfan`（Kepler/Text/Fan.lean:154，
定义即 `{v | ∃ e ∈ E, v ∈ affGe {x} e}`）。

证明思路：展开 `xfan` 与 `⋃ e ∈ E, ·` 的成员关系
（`Set.mem_iUnion` / `Set.mem_iUnion₂`）后外延即得，`V` 不参与。

候选已有引理：
- `xfan`（Kepler/Text/Fan.lean:154）
- `Set.mem_iUnion`、`Set.mem_iUnion₂`（Mathlib/Data/Set/Lattice.lean）
- 缺口：HOL `UNIONS`/`IN_ELIM_THM` 未以该名移植 -/
theorem XFAN_EQ_UNIONS_AFF_GE_1_2 (x : V3) (V : Set V3) (E : Set (Set V3)) :
    xfan x V E = ⋃ e ∈ E, affGe ({x} : Set V3) e := by
  sorry

/-- HOL Conforming.hl :754-771 `NEGLIGIBLE_XFAN`

HOL 原文：
```
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool).
FAN (x,V,E) ==>  negligible (xfan (x,V,E))
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
`xfan` ↔ `xfan`（Kepler/Text/Fan.lean:154）。

证明思路：先用 `XFAN_EQ_UNIONS_AFF_GE_1_2` 把 `xfan` 写成
`⋃ e ∈ E, affGe {x} e`；由 `setEdgesFiniteFan` 得 `E` 有限，故只需
有限个零测集的并仍零测（`measure_iUnion_null` /
`measure_biUnion_null_iff`）；每条边由 `expand_edge_graph_fan` 写成
`{v,w}`，再用 `NEGLIGIBLE_AFF_GE_1_2`（三点不共线由 `FAN` 的
`remark1_fan` 分量给出）。

候选已有引理：
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（本文件上文，HOL :746）
- `NEGLIGIBLE_AFF_GE_1_2`（Kepler/Text/ConformingAuto2.lean:386）
- `setEdgesFiniteFan`（Kepler/Text/Fan.lean:851，HOL
  `set_edges_is_finite_fan`）
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `measure_iUnion_null_iff`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:118）、
  `measure_iUnion_null`（同文件:122）、
  `measure_biUnion_null_iff`（同文件:107）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异分量）
- 缺口：HOL `NEGLIGIBLE_UNIONS`、`remark1_fan`、`FINITE_IMAGE` 未以该名移植 -/
theorem NEGLIGIBLE_XFAN (x : V3) (V : Set V3) (E : Set (Set V3))
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
`xfan` ↔ `xfan`；`normball x r` ↔ `Metric.ball x r`。

证明思路：由 `Set.inter_subset_left` 得
`xfan x V E ∩ Metric.ball x r ⊆ xfan x V E`，再用
`measure_mono_null` 与 `NEGLIGIBLE_XFAN`（HOL 用 `NEGLIGIBLE_SUBSET`）。

候选已有引理：
- `NEGLIGIBLE_XFAN`（本文件上文，HOL :754）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `Set.inter_subset_left`（Mathlib/Data/Set/Basic.lean）
- 缺口：HOL `NEGLIGIBLE_SUBSET` 未以该名移植 -/
theorem NEGLIGIBLE_XFAN_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3))
    (r : ℝ) (hfan : FAN x V E) :
    volume (xfan x V E ∩ Metric.ball x r) = 0 := by
  sorry

/-- HOL Conforming.hl :779-785 `HAS_MEASURE_XFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r.
FAN (x,V,E) ==>  (xfan (x,V,E) INTER normball x r)  has_measure  &0
```

编码说明（缺口）：HOL `has_measure &0`（= `measure s = &0`）未移植，
与 `negligible` 定义等价，统一编码为 `volume s = 0`（见文件头）；
`xfan` ↔ `xfan`；`normball x r` ↔ `Metric.ball x r`。

证明思路：HOL 由 `NEGLIGIBLE_XFAN_INTER_BALL` 与 `HAS_MEASURE_0`
收口；在 `volume = 0` 编码下两者类型相同，直接引用。

候选已有引理：
- `NEGLIGIBLE_XFAN_INTER_BALL`（本文件上文，HOL :772）
- 缺口：HOL `HAS_MEASURE_0` 未移植 -/
theorem HAS_MEASURE_XFAN_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3))
    (r : ℝ) (hfan : FAN x V E) :
    volume (xfan x V E ∩ Metric.ball x r) = 0 := by
  sorry

/-! ## `yfan` 与球的测度/可测性（Conforming.hl:786-814） -/

/-- HOL Conforming.hl :786-799 `MEASURE_YFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r.
FAN(x,V,E)/\ &0<= r
==> measure ( (yfan (x,V,E)) INTER normball x r)= &4/ &3 *pi *r pow 3
```

编码说明：HOL `measure s`（实值）↔ `volume.real s`
（`Measure.real`，见文件头与 Kepler/Geom/Volume.lean:40）；
`yfan` ↔ `yfan`（Kepler/Text/Fan.lean:158）；`normball x r` ↔
`Metric.ball x r`；`&4/ &3 *pi *r pow 3` ↔
`(4 / 3 : ℝ) * Real.pi * r ^ 3`。HOL 的 `&0<= r` ↔ `0 ≤ r`。

证明思路：把 `yfan = UNIV \ xfan` 代入并把球与差的交写成
`Metric.ball x r \ (xfan x V E ∩ Metric.ball x r)`
（HOL `SET_RULE` 步骤）；由 `HAS_MEASURE_XFAN_INTER_BALL` 得内层
零测且可测，`Metric.ball x r` 可测，用 `measure_sdiff`
（HOL `MEASURE_DIFF_SUBSET`）得实值测度等于球的实值测度；
最后 `EuclideanSpace.volume_ball_fin_three`（HOL `VOLUME_BALL`）给出
`r^3 * (π * 4 / 3)`，`ring` 收口。

候选已有引理：
- `HAS_MEASURE_XFAN_INTER_BALL`（本文件上文，HOL :779）
- `EuclideanSpace.volume_ball_fin_three`
  （Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:408）
- `MeasureTheory.measure_sdiff`
  （Mathlib/MeasureTheory/Measure/MeasureSpace.lean:250）
- `yfan`（Kepler/Text/Fan.lean:158）
- `measurableSet_ball`（Mathlib，球可测）
- 缺口：HOL `MEASURE_DIFF_SUBSET`、`VOLUME_BALL`、`GSYM ball_eq_normball`、
  `SET_RULE` 未以该名移植 -/
theorem MEASURE_YFAN_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3))
    (r : ℝ) (hfan : FAN x V E) (hr : 0 ≤ r) :
    volume.real (yfan x V E ∩ Metric.ball x r) =
      (4 / 3 : ℝ) * Real.pi * r ^ 3 := by
  sorry

/-- HOL Conforming.hl :800-814 `MESURABLE_YFAN_INTER_BALL`（HOL 拼写）

HOL 原文：
```
!x:real^3 V E r.
FAN(x,V,E)/\ &0<= r
==> measurable ( (yfan (x,V,E)) INTER normball x r)
```

编码说明：HOL `measurable` ↔ `MeasurableSet`；`yfan` ↔ `yfan`；
`normball x r` ↔ `Metric.ball x r`；HOL `&0<= r` ↔ `0 ≤ r`。
名称 `MESURABLE_...` 按 HOL 原样保留（非 `MEASURABLE_`）。

证明思路：把 `yfan = UNIV \ xfan` 代入并把球与差的交写成
`Metric.ball x r \ (xfan x V E ∩ Metric.ball x r)`；由
`HAS_MEASURE_XFAN_INTER_BALL` 得内层零测故可测
（`measurableSet_of_null`），`Metric.ball x r` 可测，用
`MeasurableSet.diff`（HOL `MEASURABLE_DIFF`）收口。

候选已有引理：
- `HAS_MEASURE_XFAN_INTER_BALL`（本文件上文，HOL :779）
- `MeasurableSet.diff`
  （Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:175）
- `measurableSet_of_null`
  （Mathlib/MeasureTheory/Measure/NullMeasurable.lean:434）
- `measurableSet_ball`（Mathlib）
- 缺口：HOL `MEASURABLE_DIFF`、`GSYM ball_eq_normball` 未以该名移植 -/
theorem MESURABLE_YFAN_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3))
    (r : ℝ) (hfan : FAN x V E) (hr : 0 ≤ r) :
    MeasurableSet (yfan x V E ∩ Metric.ball x r) := by
  sorry

/-! ## 径向集在差与并下的封闭性（Conforming.hl:815-858） -/

/-- HOL Conforming.hl :815-851 `RADIAL_DIFF`

HOL 原文：
```
!r v0 A B:real^N->bool. radial_norm r v0 A /\ radial_norm r v0 B /\ A SUBSET B ==> radial_norm r v0 (B DIFF A)
```

编码说明（缺口）：HOL 陈述对一般 `real^N`，而仓库
`radialNorm`（Kepler/Geom/Volume.lean:27）只对 `V3` 定义，故此处
限定 `V3`（不引入新定义）。`radial_norm` ↔ `radialNorm`；
`B DIFF A` ↔ `B \ A`；`A SUBSET B` ↔ `A ⊆ B`。
`radialNorm r v0 C` 展开为
`C ⊆ Metric.ball v0 r ∧ ∀ u, v0 + u ∈ C → ∀ t, 0 < t → t * ‖u‖ < r →
v0 + t • u ∈ C`。

证明思路：两条 `radialNorm` 合取。第一支 `B \ A ⊆ ball v0 r` 由
`B ⊆ ball` 与差集子集传递。第二支取 `v0 + u ∈ B \ A`，先用 `B` 的
径向性得 `v0 + t•u ∈ B`，再用反证：若 `v0 + t•u ∈ A`，对 `A` 用
径向性于方向 `t•u` 与参数 `inv t`（`t > 0`，`t * ‖t•u‖ < r`）反推
`v0 + u ∈ A`，与 `v0 + u ∉ A` 矛盾；故 `v0 + t•u ∈ B \ A`。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Set.diff_subset`、`Set.diff_subset_iff`（Mathlib/Data/Set/Basic.lean）
- `norm_smul`、`Real.norm_eq_abs`（Mathlib，用于 `t * ‖t•u‖` 计算）
- `inv_mul_cancel₀` / `mul_inv_cancel₀`（Mathlib/Algebra/GroupPower/...）
- 缺口：HOL 的 `real^N` 一般维度未覆盖；`radial_norm` 仅 `V3` 版 -/
theorem RADIAL_DIFF (r : ℝ) (v0 : V3) (A B : Set V3)
    (hA : radialNorm r v0 A) (hB : radialNorm r v0 B) (hsub : A ⊆ B) :
    radialNorm r v0 (B \ A) := by
  sorry

/-- HOL Conforming.hl :852-858 `RADIAL_UNION`

HOL 原文：
```
!r v0 A B:real^N->bool. radial_norm r v0 A /\ radial_norm r v0 B ==> radial_norm r v0 (A UNION B)
```

编码说明（缺口）：HOL 陈述对一般 `real^N`，而仓库
`radialNorm`（Kepler/Geom/Volume.lean:27）只对 `V3` 定义，故此处
限定 `V3`（不引入新定义）。`radial_norm` ↔ `radialNorm`；
`A UNION B` ↔ `A ∪ B`。

证明思路：两条 `radialNorm` 合取。第一支 `A ∪ B ⊆ ball v0 r` 由两条
`⊆ ball` 取并。第二支对 `v0 + u ∈ A ∪ B` 分情形，分别用 `A` 或 `B`
的径向性得到 `v0 + t • u` 落入同一侧，从而落入并。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Set.union_subset_iff`、`Set.mem_union`（Mathlib/Data/Set/Basic.lean）
- 缺口：HOL 的 `real^N` 一般维度未覆盖；`radial_norm` 仅 `V3` 版 -/
theorem RADIAL_UNION (r : ℝ) (v0 : V3) (A B : Set V3)
    (hA : radialNorm r v0 A) (hB : radialNorm r v0 B) :
    radialNorm r v0 (A ∪ B) := by
  sorry
