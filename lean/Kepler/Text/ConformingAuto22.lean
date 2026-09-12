/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 22
(Conforming.hl:14520-14792).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 22, Conforming.hl:14520-14792):
- `exists_point_in_dartset_leads_into_fan` (14520)
- `NEGLIGIBLE_AFF_3_FAN` (14538)
- `NEGLIGIBLE_AFF_3_UNION_INTER_BALL` (14554)
- `MEASURE_AFF_3_UNION_FAN` (14564)
- `HAS_MEASURE_AFF_3_UNION_INTER_BALL` (14571)
- `MEASURABLE_AFF_3_UNION_INTER_BALL` (14578)
- `measure_ball_diff_set_negligible` (14587)
- `exists_measure_ball_diff_set_negligible` (14601)
- `connected_in_dartset_leads_into_fan_union_aff_gt` (14624)
- `AFF_GT_1_1_SUBSET_DARTSET_LEADS_INTO_FAN` (14722)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings; same conventions as
batches 16-21):
- MEASURE THEORY (the batch-3/5 conventions, Kepler/Text/ConformingAuto3.lean
  and ConformingAuto5.lean headers): HOL `negligible s`, `measure s = &0`
  and `s has_measure &0` are all encoded as the Mathlib Lebesgue
  measure-zero predicate `volume s = 0` (`volume : Measure V3`); a NONZERO
  HOL `measure s` (real) is encoded as `volume.real s` (`Measure.real`),
  matching `Kepler.Geom.Volume` (Kepler/Geom/Volume.lean:40). Hence
  `NEGLIGIBLE_AFF_3_UNION_INTER_BALL`, `MEASURE_AFF_3_UNION_FAN` and
  `HAS_MEASURE_AFF_3_UNION_INTER_BALL` below have literally the same Lean
  statement (as the `volume = 0` encoding makes them definitionally equal),
  while `measure_ball_diff_set_negligible` uses `volume.real`.
  HOL `measurable` ↔ `MeasurableSet`; HOL `normball y r` ↔
  `Metric.ball y r`; HOL `VOLUME_BALL` ↔
  `EuclideanSpace.volume_ball_fin_three`; HOL `MEASURE_DIFF_SUBSET` ↦
  `measure_sdiff_null` (as in `MEASURE_YFAN_INTER_BALL`,
  Kepler/Text/ConformingAuto3.lean:452); gaps: HOL `HAS_MEASURE_0`,
  `MEASURE_EQ_0`, `MEASURABLE_BALL`, `ball_eq_normball` are not ported
  under those names.
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  HOL `(real^3->bool)` ↔ `Set V3`; HOL darts
  `real^3#real^3#real^3#real^3->bool` ↔ `Set (V3 × V3)`; HOL `(:real^3)` ↔
  `(Set.univ : Set V3)`; HOL `segment [y,z]` ↔ `segment ℝ y z` (Mathlib
  closed segment, cf. Kepler/Text/ConformingAuto8.lean:54-55);
  `INTER`/`DIFF`/`SUBSET`/`UNIONS` ↔ `∩`/`\`/`⊆`/`⋃ v ∈ V, ...`.
- FAN-witness arguments: `hypermapOfFan` (Kepler/Text/Fan.lean:1169) and the
  ConformingDefs predicate `conformingFan` (Kepler/Text/ConformingDefs.lean:184)
  need an explicit `FAN` witness, so each theorem mentioning them carries an
  extra explicit hypothesis `(hfan : FAN x V E)`. This is the only deviation
  from the HOL signatures.
- `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`;
  `face_set(hypermap1_of_fanx (x,V,E))` ↦
  `(hypermapOfFan x V E hfan).faceSet`; `dartset_leads_into_fan` ↦
  `dartsetLeadsIntoFan` (Kepler/Text/PlanarityComponent.lean:348);
  `topological_component_yfan` ↦ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); `aff_gt`/`aff_ge` ↦ `affGt`/`affGe`
  (Kepler/Geom/Aff.lean:39,42); `yfan` ↦ `yfan` (Kepler/Text/Fan.lean:158);
  HOL `UNIONS {aff_ge {x} {v}| v IN V}` ↔
  `⋃ v ∈ V, affGe ({x} : Set V3) {v}` (same convention as
  `yfan_union_aff_gt_fan`, Kepler/Text/ConformingAuto21.lean:869).
- HOL notions used by the HOL proofs but NOT ported that the pool proofs must
  work around: `remark1_fan` (fan.hl:423), `hypermap_of_fan_rep`,
  `dartset_fully_surrounded_is_non_isolated_fan`, `sigma_fan_in_set_of_edge`,
  `face_subset_dart_fan` (closest existing: `face_subset_darts`,
  Kepler/Text/Hypermap.lean:854), `AFF_GT_1_1`/`AFF_GE_1_1`/`AFF_GE_1_2`
  (member-form rep lemmas exist, cf. Kepler/Text/PlanarityAuto8.lean:41,
  `affGe_singleton_pair_subset_affineSpan_auto3`,
  Kepler/Text/ConformingAuto3.lean:311). No new definition is introduced
  for any of them.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto21

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical
open MeasureTheory

/-! ## 面内存在点与 `aff {x,z,v}` 并集的零测性（Conforming.hl:14520-14563） -/

/-- HOL Conforming.hl :14520-14537 `exists_point_in_dartset_leads_into_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> ?y. y IN dartset_leads_into_fan x V E ds
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`
（Kepler/Text/PlanarityComponent.lean:348）；`face_set(hypermap1_of_fanx …)`
↦ `(hypermapOfFan x V E hfan).faceSet`（需显式 `FAN` 见证，见文件头）。

证明思路：HOL 用 `dartset_leads_into_is_topological_component_yfan` 得
`dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E`，再展开
`topologicalComponentYfan` 的成员描述取其中一点 `y`；由
`CONNECTED_COMPONENT_REFL`（自反性）收口 `y` 属于该分量。

候选已有引理：
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- `CONNECTED_COMPONENT_REFL`（Mathlib/Topology/Connected/Components.lean） -/
theorem exists_point_in_dartset_leads_into_fan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (ds : Set (V3 × V3)) (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∃ y : V3, y ∈ dartsetLeadsIntoFan x V E ds := by
  sorry

/-- HOL Conforming.hl :14538-14553 `NEGLIGIBLE_AFF_3_FAN`

HOL 原文：
```
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) z:real^3.
FAN (x,V,E) ==>  negligible (UNIONS {aff {x, z, v} | v IN V} )
```

编码说明（缺口）：`negligible` ↔ `volume s = 0`（见文件头）；
HOL `UNIONS {aff {x,z,v} | v IN V}` ↔
`⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)`；HOL `aff`（仿射包）
↦ `affineSpan ℝ`（batch-17 约定）。注意 HOL 圆括号化的 binder `(x:real^3)`，
Lean 侧照常为具名参数。

证明思路：HOL 用 `NEGLIGIBLE_UNIONS` + `FINITE_IMAGE`（V 有限）把并集的
零测化归到每个 `aff {x,z,v}`；Lean 侧由 V 有限得 `Set.Finite.iUnion`，
再用 `measure_mono_null` / 零测并引理与 `NEGLIGIBLE_AFF_3` 收口。

候选已有引理：
- `NEGLIGIBLE_AFF_3`（Kepler/Text/ConformingAuto2.lean:447）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54，
  参见 Kepler/Text/ConformingAuto2.lean:603 的用法）
- V 的有限性：`FAN` 的 `(⋃₀ E) ⊆ V ∧ Graph E`（Kepler/Text/Fan.lean:56）
- 缺口：HOL `NEGLIGIBLE_UNIONS`/`FINITE_IMAGE` 未以该名移植 -/
theorem NEGLIGIBLE_AFF_3_FAN (x : V3) (V : Set V3) (E : Set (Set V3)) (z : V3)
    (hfan : FAN x V E) :
    volume (⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) = 0 := by
  rw [measure_biUnion_null_iff (hfan.2.2.1.1).countable]
  intro v hv
  exact NEGLIGIBLE_AFF_3 x z v

/-- HOL Conforming.hl :14554-14563 `NEGLIGIBLE_AFF_3_UNION_INTER_BALL`

HOL 原文：
```
!x:real^3 V:real^3->bool E:(real^3->bool)->bool z:real^3  y:real^3 r:real.
FAN (x,V,E) ==>
negligible ((UNIONS {aff {x, z, v} | v IN V} ) INTER normball y r)
```

编码说明（缺口）：`negligible` ↔ `volume s = 0`（见文件头）；
`normball y r` ↔ `Metric.ball y r`。

证明思路：`⋃ v ∈ V, affineSpan ℝ {x,z,v} ∩ Metric.ball y r` ⊆
`⋃ v ∈ V, affineSpan ℝ {x,z,v}`，用 `measure_mono_null` 与
`NEGLIGIBLE_AFF_3_FAN` 收口（HOL 用 `NEGLIGIBLE_SUBSET` 同型）。

候选已有引理：
- `NEGLIGIBLE_AFF_3_FAN`（本文件上文，HOL :14538）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `Set.inter_subset_left`（Mathlib/Data/Set/Basic.lean） -/
theorem NEGLIGIBLE_AFF_3_UNION_INTER_BALL (x : V3) (V : Set V3)
    (E : Set (Set V3)) (z y : V3) (r : ℝ) (hfan : FAN x V E) :
    volume ((⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) ∩
      Metric.ball y r) = 0 := by
  exact measure_mono_null Set.inter_subset_left (NEGLIGIBLE_AFF_3_FAN x V E z hfan)

/-! ## 同一集合的 measure / has_measure / measurable 三连
（Conforming.hl:14564-14586） -/

/-- HOL Conforming.hl :14564-14570 `MEASURE_AFF_3_UNION_FAN`

HOL 原文：
```
!x:real^3 V:real^3->bool E:(real^3->bool)->bool z:real^3 y:real^3 r:real.
FAN (x,V,E) ==>  measure (UNIONS {aff {x, z, v} | v IN V} INTER normball y r)= &0
```

编码说明（缺口）：HOL `measure s = &0`（实值）在 batch-3 约定下统一编码为
`volume s = 0`（见文件头），故本陈述与
`NEGLIGIBLE_AFF_3_UNION_INTER_BALL` 的 Lean 类型完全相同；`normball y r`
↦ `Metric.ball y r`。

证明思路：HOL 由 `MEASURE_EQ_0` + `NEGLIGIBLE_AFF_3_UNION_INTER_BALL`
收口；在 `volume = 0` 编码下两者同型，直接引用本文件的
`NEGLIGIBLE_AFF_3_UNION_INTER_BALL` 即可。

候选已有引理：
- `NEGLIGIBLE_AFF_3_UNION_INTER_BALL`（本文件上文，HOL :14554）
- 缺口：HOL `MEASURE_EQ_0` 未移植（编码下定义等价） -/
theorem MEASURE_AFF_3_UNION_FAN (x : V3) (V : Set V3) (E : Set (Set V3))
    (z y : V3) (r : ℝ) (hfan : FAN x V E) :
    volume ((⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) ∩
      Metric.ball y r) = 0 := by
  exact NEGLIGIBLE_AFF_3_UNION_INTER_BALL x V E z y r hfan

/-- HOL Conforming.hl :14571-14577 `HAS_MEASURE_AFF_3_UNION_INTER_BALL`

HOL 原文：
```
!x:real^3 V:real^3->bool E:(real^3->bool)->bool z:real^3 y:real^3 r:real.
FAN (x,V,E) ==>  (UNIONS {aff {x, z, v} | v IN V} INTER normball y r)  has_measure  &0
```

编码说明（缺口）：HOL `has_measure &0`（= `measure s = &0`）未移植，
与 `negligible` 定义等价，统一编码为 `volume s = 0`（见文件头），故本陈述
与前两条的 Lean 类型完全相同；`normball y r` ↔ `Metric.ball y r`。

证明思路：HOL 由 `NEGLIGIBLE_AFF_3_UNION_INTER_BALL` 与 `HAS_MEASURE_0`
收口；在 `volume = 0` 编码下直接引用。

候选已有引理：
- `NEGLIGIBLE_AFF_3_UNION_INTER_BALL`（本文件上文，HOL :14554）
- 缺口：HOL `HAS_MEASURE_0` 未移植 -/
theorem HAS_MEASURE_AFF_3_UNION_INTER_BALL (x : V3) (V : Set V3)
    (E : Set (Set V3)) (z y : V3) (r : ℝ) (hfan : FAN x V E) :
    volume ((⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) ∩
      Metric.ball y r) = 0 := by
  exact NEGLIGIBLE_AFF_3_UNION_INTER_BALL x V E z y r hfan

/-- HOL Conforming.hl :14578-14586 `MEASURABLE_AFF_3_UNION_INTER_BALL`

HOL 原文：
```
!x:real^3 V:real^3->bool E:(real^3->bool)->bool z:real^3 y:real^3 r:real.
FAN (x,V,E) ==>    measurable (UNIONS {aff {x, z, v} | v IN V} INTER normball y r)
```

编码说明：HOL `measurable` ↔ `MeasurableSet`（batch-3/5 约定）；
`normball y r` ↔ `Metric.ball y r`。

证明思路：HOL 由 `measurable` 定义 + `EXISTS_TAC &0` +
`HAS_MEASURE_AFF_3_UNION_INTER_BALL` 收口；Lean 侧直接由可测集的有限并
（V 有限）与球的 可测性组合：`MeasurableSet.iUnion`（有限指标）、
`measurableSet_ball`、`MeasurableSet.inter`。

候选已有引理：
- `MeasurableSet.inter`/`MeasurableSet.iUnion`（Mathlib，有限指标形式）
- `measurableSet_ball`（Mathlib/MeasureTheory/Measure/Lebesgue/Eborel?/
  MetricBall；batch-3 `MEASURE_YFAN_INTER_BALL` 头注已引用，见
  Kepler/Text/ConformingAuto3.lean:448）
- V 的有限性：`FAN` 的 `(⋃₀ E) ⊆ V ∧ Graph E`（Kepler/Text/Fan.lean:56）
- 缺口：HOL `measurable`（存在实值测度的形式）未以该名移植 -/
theorem MEASURABLE_AFF_3_UNION_INTER_BALL (x : V3) (V : Set V3)
    (E : Set (Set V3)) (z y : V3) (r : ℝ) (hfan : FAN x V E) :
    MeasurableSet ((⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) ∩
      Metric.ball y r) := by
  sorry

/-! ## 球去掉零测集后的体积与非空性（Conforming.hl:14587-14623） -/

/-- HOL Conforming.hl :14587-14600 `measure_ball_diff_set_negligible`

HOL 原文：
```
!x:real^3 V E z y r.
FAN(x,V,E)/\ &0<= r
==> measure ( (normball y r) DIFF (UNIONS {aff {x,z,v}| v IN V}))= &4/ &3 *pi *r pow 3
```

编码说明：HOL `measure s`（实值、非零）↔ `volume.real s`（`Measure.real`，
见文件头与 Kepler/Geom/Volume.lean:40）；`normball y r` ↔
`Metric.ball y r`；`&4/ &3 *pi *r pow 3` ↔ `(4 / 3 : ℝ) * Real.pi * r ^ 3`；
HOL `&0<= r` ↔ `0 ≤ r`。

证明思路：与 `MEASURE_YFAN_INTER_BALL`（Kepler/Text/ConformingAuto3.lean:452，
HOL :786）同型：由 `NEGLIGIBLE_AFF_3_UNION_INTER_BALL` 得
`volume (ball y r ∩ ⋃ …) = 0`，把 `ball y r \ ⋃ …` 写成
`ball y r \ (⋃ … ∩ ball y r)`，用 `measure_sdiff_null`（HOL
`MEASURE_DIFF_SUBSET` 路线）化归为球的测度，最后
`EuclideanSpace.volume_ball_fin_three`（HOL `VOLUME_BALL`）+ `ring` 收口。

候选已有引理：
- `NEGLIGIBLE_AFF_3_UNION_INTER_BALL`（本文件上文，HOL :14554）
- `EuclideanSpace.volume_ball_fin_three`
  （Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:408；用法见
  Kepler/Text/ConformingAuto3.lean:467）
- `measure_sdiff_null`（Mathlib；用法见 Kepler/Text/ConformingAuto3.lean:467）
- `MEASURE_YFAN_INTER_BALL`（Kepler/Text/ConformingAuto3.lean:452，同型模板）
- 缺口：HOL `MEASURE_DIFF_SUBSET`、`VOLUME_BALL`、`ball_eq_normball` 未以
  该名移植 -/
theorem measure_ball_diff_set_negligible (x : V3) (V : Set V3)
    (E : Set (Set V3)) (z y : V3) (r : ℝ) (hfan : FAN x V E) (hr : 0 ≤ r) :
    volume.real ((Metric.ball y r \
      (⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3))) : Set V3) =
      (4 / 3 : ℝ) * Real.pi * r ^ 3 := by
  sorry

/-- HOL Conforming.hl :14601-14623 `exists_measure_ball_diff_set_negligible`

HOL 原文：
```
!x:real^3 V E y z r.
FAN(x,V,E)/\ &0< r
==> ?a. a IN (normball y r) DIFF (UNIONS {aff {x,z,v}| v IN V})
```

编码说明：`normball y r` ↔ `Metric.ball y r`；HOL `&0< r` ↔ `0 < r`；
注意 HOL binder 顺序为 `y z r`（y 在前）。

证明思路：反证。若差集为空则 `ball y r ⊆ ⋃ …`，于是
`volume.real (ball y r) = volume.real (ball y r \ ⋃ …)`；结合
`measure_ball_diff_set_negligible` 得 `(4/3)·π·r³ = 0`，与 `0 < r`、
`0 < π`（`Real.pi_pos`）矛盾（HOL 用 `PI_WORKS`/`REAL_POW_EQ_0` 同型）。

候选已有引理：
- `measure_ball_diff_set_negligible`（本文件上文，HOL :14587）
- `EuclideanSpace.volume_ball_fin_three`（Mathlib；用法见
  Kepler/Text/ConformingAuto3.lean:467）
- `Real.pi_pos`（Mathlib/Analysis/SpecialFunctions/Trigonometric.Basic?）
- `Set.eq_empty_iff_forall_notMem`（Mathlib/Data/Set/Basic.lean） -/
theorem exists_measure_ball_diff_set_negligible (x : V3) (V : Set V3)
    (E : Set (Set V3)) (y z : V3) (r : ℝ) (hfan : FAN x V E) (hr : 0 < r) :
    ∃ a : V3, a ∈ Metric.ball y r \
      (⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) := by
  sorry

/-! ## 沿 dart 集引出的点的连通性与 `aff_gt {x} {y}` 包含
（Conforming.hl:14624-14792） -/

/-- HOL Conforming.hl :14624-14721 `connected_in_dartset_leads_into_fan_union_aff_gt`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds ds1 Z.
FAN(x,V,E)
/\ conforming_fan (x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ ds1 IN face_set(hypermap1_of_fanx (x,V,E))
/\ Z=(:real^3) DIFF (UNIONS {aff_ge {x} {v}| v IN V})
==> ?y z. y IN dartset_leads_into_fan x V E ds
/\ z IN dartset_leads_into_fan x V E ds1
/\ segment[y,z] SUBSET Z
```

编码说明：`conforming_fan` ↦ `conformingFan x V E hfan`（需显式 `FAN`
见证，见文件头）；`Z=(:real^3) DIFF (UNIONS {aff_ge {x} {v}| v IN V})` ↦
`Z = (Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v}`（同
`yfan_union_aff_gt_fan` 的右端，Kepler/Text/ConformingAuto21.lean:869）；
`segment[y,z]` ↔ `segment ℝ y z`（Mathlib 闭线段，
Kepler/Text/ConformingAuto8.lean:54-55）。

证明思路：两次用 `exists_point_in_dartset_leads_into_fan` 取 `y,z'`；由
`OPEN_TOPOLOGICAL_COMPONENT_YFAN` 得 `dartsetLeadsIntoFan x V E ds1` 开，
在 `y` 处取开球 `Metric.ball y' e ⊆ …`；由
`exists_measure_ball_diff_set_negligible` 取 `a ∈ ball y' e \ ⋃ …`，
则线段 `[a,y']` ⊆ Z（`aff_ge {x} {v}` 凸性/坐标参数化路线）；HOL 的
`u''`-分支用 `exists_inf_element_fix_fan` + `remark1_fan`（未移植）+
`AFF_GE_1_1` 展开 `yfan`/`xfan` 判定。

候选已有引理：
- `exists_point_in_dartset_leads_into_fan`（本文件上文，HOL :14520）
- `exists_measure_ball_diff_set_negligible`（本文件上文，HOL :14601）
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN`（Kepler/Text/ConformingAuto6.lean:317）
- `dartset_leads_into_subset_yfan`（Kepler/Text/PlanarityComponent.lean:583）
- `exists_inf_element_fix_fan`（Kepler/Text/Planarity.lean:2608）
- `XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:306）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `segment ℝ`（Mathlib，见 Kepler/Text/ConformingAuto8.lean:674 的用法）
- 缺口：HOL `remark1_fan`（fan.hl:423）、`AFF_GE_1_1` 未以该名移植
  （成员形式替代见 Kepler/Text/PlanarityAuto8.lean:41 与
  `affGe_singleton_pair_subset_affineSpan_auto3`，
  Kepler/Text/ConformingAuto3.lean:311） -/
theorem connected_in_dartset_leads_into_fan_union_aff_gt (x : V3) (V : Set V3)
    (E : Set (Set V3)) (ds ds1 : Set (V3 × V3)) (Z : Set V3) (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds1 : ds1 ∈ (hypermapOfFan x V E hfan).faceSet)
    (hZ : Z = (Set.univ : Set V3) \ ⋃ v ∈ V, affGe ({x} : Set V3) {v}) :
    ∃ y z : V3, y ∈ dartsetLeadsIntoFan x V E ds ∧
      z ∈ dartsetLeadsIntoFan x V E ds1 ∧
      (segment ℝ y z : Set V3) ⊆ Z := by
  sorry

/-- HOL Conforming.hl :14722-14792 `AFF_GT_1_1_SUBSET_DARTSET_LEADS_INTO_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y.
FAN(x,V,E)

/\ conforming_fan (x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ~(E={})
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ y IN dartset_leads_into_fan x V E ds
==> aff_gt {x} {y}  SUBSET dartset_leads_into_fan x V E ds
```

编码说明：`conforming_fan` ↦ `conformingFan x V E hfan`（需显式 `FAN`
见证）；`aff_gt {x} {y}` ↔ `affGt ({x} : Set V3) {y}`
（Kepler/Geom/Aff.lean:39）；`~(E={})` ↔ `E ≠ ∅`；`hypermap1_of_fanx` ↦
`hypermapOfFan x V E hfan`。

证明思路：由 `dartset_leads_into_is_topological_component_yfan` +
`point_in_yfan_not_x_fan` 得 `x ≠ y`，用 `AFF_GT_1_1`（未以该名移植，
成员形式见 Kepler/Text/PlanarityAuto8.lean:41）展开
`affGt {x} {y}` 的坐标参数；再由 `conformingHalfSpaceFan`
（Kepler/Text/ConformingDefs.lean:121）把 `dartsetLeadsIntoFan x V E ds`
写成 `⋂ y' ∈ ds, affGt {x, y'.1, y'.2} {(f1Fan x V E y').2}`；对任意
`p ∈ affGt {x} {y}`，从 `hypermap_of_fan_rep`（未移植）取 `y' ∈ ds` 使
`y'`-项等于 `ds`-项，配合
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
（Kepler/Text/ConformingAuto1.lean:166）、`sigma_fan_in_set_of_edge`（未
移植）、`properties_fully_surrounded`、`cross_dot_fully_surrounded_fan`、
`aff_gt_3_1_rep_cross_dot` 化为 `0 < cross·dot` 的严格乘积判定
（HOL 末步 `REAL_LT_MUL`）。

候选已有引理：
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
  （Kepler/Text/ConformingAuto1.lean:166）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `face_subset_darts`（Kepler/Text/Hypermap.lean:854，
  替代 HOL `face_subset_dart_fan`）
- 缺口：HOL `hypermap_of_fan_rep`、`dartset_fully_surrounded_is_non_isolated_fan`、
  `sigma_fan_in_set_of_edge`、`AFF_GT_1_1` 未以该名移植（参见
  Kepler/Text/ConformingAuto9.lean:232 的缺口注记） -/
theorem AFF_GT_1_1_SUBSET_DARTSET_LEADS_INTO_FAN (x : V3) (V : Set V3)
    (E : Set (Set V3)) (ds : Set (V3 × V3)) (y : V3) (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E) (hE : E ≠ ∅)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ dartsetLeadsIntoFan x V E ds) :
    affGt ({x} : Set V3) {y} ⊆ dartsetLeadsIntoFan x V E ds := by
  sorry

end Kepler.Text
