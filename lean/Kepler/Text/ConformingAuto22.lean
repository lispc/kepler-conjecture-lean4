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
  have hmem := dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds
  rw [topologicalComponentYfan, Set.mem_setOf_eq] at hmem
  obtain ⟨b, hb, heq⟩ := hmem
  exact ⟨b, heq ▸ mem_connectedComponentIn hb⟩

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
  refine MeasurableSet.inter ?_ Metric.isOpen_ball.measurableSet
  exact hfan.2.2.1.1.measurableSet_biUnion fun v _ =>
    IsClosed.measurableSet (AffineSubspace.closed_of_finiteDimensional _)

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
  have hzero : volume ((⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) ∩
      Metric.ball y r) = 0 :=
    NEGLIGIBLE_AFF_3_UNION_INTER_BALL x V E z y r hfan
  have hset : (Metric.ball y r \
      (⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) : Set V3) =
      Metric.ball y r \ ((⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) ∩
        Metric.ball y r) := by
    ext a
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hset]
  simp only [Measure.real]
  rw [measure_sdiff_null hzero, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
      ENNReal.toReal_ofReal (by positivity)]
  ring

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
  by_contra h
  have hsdiff : (Metric.ball y r \
      (⋃ v ∈ V, (affineSpan ℝ ({x, z, v} : Set V3) : Set V3)) : Set V3) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun a ha => h ⟨a, ha.1, ha.2⟩
  have hvol := measure_ball_diff_set_negligible x V E z y r hfan hr.le
  rw [hsdiff, Measure.real_def, measure_empty] at hvol
  simp at hvol
  linarith

/-- 系数和为 1 的有限加权和落入 `affineSpan`（复制
Kepler/Text/ConformingAuto3.lean 的私有引理
`finset_sum_smul_mem_affineSpan_auto3`）。 -/
private theorem sumSmulMemAffineSpan22 {T : Set V3} {s : Finset V3} {f : V3 → ℝ}
    (hS : ∀ w ∈ s, w ∈ (affineSpan ℝ T : Set V3)) (hsum : ∑ w ∈ s, f w = 1) :
    ∑ w ∈ s, f w • w ∈ (affineSpan ℝ T : Set V3) := by
  have hne : s.Nonempty := Finset.nonempty_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  obtain ⟨b, hb⟩ := hne
  have hbS : b ∈ (affineSpan ℝ T : Set V3) := hS b hb
  have hdir : ∑ w ∈ s, f w • (w - b) ∈ (affineSpan ℝ T).direction := by
    apply Submodule.sum_mem
    intro w hw
    exact Submodule.smul_mem _ (f w)
      (AffineSubspace.vsub_mem_direction (hS w hw) hbS)
  have hsub : ∑ w ∈ s, f w • (w - b) = (∑ w ∈ s, f w • w) - b := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hy : ∑ w ∈ s, f w • w = (∑ w ∈ s, f w • (w - b)) +ᵥ b := by
    rw [vadd_eq_add, hsub]
    abel
  rw [hy]
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hbS

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
  -- 两个面上的代表点（HOL 的两次 `exists_point_in_dartset_leads_into_fan`）
  obtain ⟨p0, hp0⟩ := exists_point_in_dartset_leads_into_fan x V E ds hfan hcard hfan80 hds
  obtain ⟨y1, hy1⟩ := exists_point_in_dartset_leads_into_fan x V E ds1 hfan hcard hfan80 hds1
  -- ds-分量是 yfan 的拓扑分量，故在 p0 处开
  have htop : dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E :=
    dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.mp
    (OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan hconf htop) p0 hp0
  -- 在球心 p0、半径 e 的球内取 a ∉ ⋃ v ∈ V, affineSpan ℝ {x, y1, v}
  obtain ⟨a, haball, haU⟩ := exists_measure_ball_diff_set_negligible x V E p0 y1 e hfan he
  have hxV : x ∉ V := hfan.2.2.2.1
  have hsub1 : dartsetLeadsIntoFan x V E ds1 ⊆ yfan x V E :=
    dartset_leads_into_subset_yfan hfan hcard hfan80 hds1
  refine ⟨a, y1, hball haball, hy1, ?_⟩
  rw [hZ]
  intro p hp
  simp only [Set.mem_sdiff, Set.mem_univ, true_and]
  rw [Set.mem_iUnion₂]
  intro hcon
  obtain ⟨v, hv, hpv⟩ := hcon
  rw [segment] at hp
  obtain ⟨α, β, hα0, -, hab, hpe⟩ := hp
  have hxv : x ≠ v := fun h => hxV (h ▸ hv)
  rcases hα0.eq_or_lt with hα | hα
  · -- 端点 p = y1：y1 ∈ affGe {x} {v} 推出 y1 ∈ xfan，与 ds1-分量 ⊆ yfan 矛盾
    have hβ1 : β = 1 := by rw [← hab, ← hα]; norm_num
    rw [← hα, zero_smul, hβ1, one_smul, zero_add] at hpe
    rw [← hpe] at hpv
    have hfinv : (setOfEdge v V E).Finite := remark_finite_fan1 v V E hfan.2.2.1.1
    have hvne : (setOfEdge v V E).Nonempty :=
      (Set.ncard_pos hfinv).mp (by have := hcard v hv; linarith)
    obtain ⟨u2, hu2⟩ := hvne
    have hEu : {v, u2} ∈ E := (properties_of_setOfEdge_fan x V E v u2 hfan).2 hu2
    have hu2V : u2 ∈ V :=
      hfan.1 (Set.mem_sUnion_of_mem (by simp : u2 ∈ ({v, u2} : Set V3)) hEu)
    have hxu2 : x ≠ u2 := fun h => hxV (h ▸ hu2V)
    have hymem2 : y1 ∈ affGe ({x} : Set V3) {v, u2} := by
      rcases eq_or_ne v u2 with rfl | hvu2
      · rw [Set.pair_eq_singleton]; exact hpv
      · rw [mem_affGe_singleton_pair (Set.disjoint_singleton_left.mpr (by simp [hxv, hxu2]))
          hvu2]
        obtain ⟨t1, t2, ht2, hsum', hy'⟩ := (mem_affGe_singleton hxv).mp hpv
        exact ⟨t1, t2, 0, ht2, le_refl 0, by linarith, by rw [hy']; module⟩
    have hymemXfan : y1 ∈ xfan x V E := by
      simp only [xfan, Set.mem_setOf_eq]
      exact ⟨{v, u2}, hEu, hymem2⟩
    have hy1fan : y1 ∈ yfan x V E := hsub1 hy1
    simp only [yfan, Set.mem_sdiff, Set.mem_univ, true_and] at hy1fan
    exact hy1fan hymemXfan
  · -- α > 0：由 p = α•a + β•y1 与 p ∈ affGe {x} {v} 解出 a ∈ affineSpan ℝ {x, y1, v}
    have hαne : α ≠ 0 := ne_of_gt hα
    have hpv' : Affsign (fun r : ℝ => 0 ≤ r) ({x} : Set V3) {v} p := hpv
    obtain ⟨f, hfin, hcomb, _hpos, hone⟩ := hpv'
    set S0 := hfin.toFinset with hS0
    set S1 := insert y1 S0 with hS1
    have hA : ∑ w ∈ S1, (if w = y1 then -β/α else 0) • w = (-β/α) • y1 := by
      rw [Finset.sum_eq_single y1]
      · simp
      · intro w _ hw; simp [hw]
      · intro h; exact absurd (Finset.mem_insert_self y1 S0) h
    have hB : ∑ w ∈ S1, ((1/α) * (if w ∈ S0 then f w else 0)) • w = (1/α) • p := by
      have hsplit : ∀ w ∈ S1, ((1/α) * (if w ∈ S0 then f w else 0)) • w
          = (1/α) • ((if w ∈ S0 then f w else 0) • w) := fun w _ => (smul_smul _ _ _).symm
      have hif : ∑ w ∈ S1, (if w ∈ S0 then f w else 0) • w = ∑ w ∈ S0, f w • w := by
        by_cases hy1S : y1 ∈ S0
        · have hsub : ∑ w ∈ S0, (if w ∈ S0 then f w else 0) • w
              = ∑ w ∈ S0, f w • w :=
            Finset.sum_congr rfl fun w hw => congrArg (fun z => z • w) (if_pos hw)
          rw [hS1, Finset.insert_eq_of_mem hy1S, hsub]
        · have hsub : ∑ w ∈ S0, (if w ∈ S0 then f w else 0) • w
              = ∑ w ∈ S0, f w • w :=
            Finset.sum_congr rfl fun w hw => congrArg (fun z => z • w) (if_pos hw)
          rw [hS1, Finset.sum_insert hy1S, if_neg hy1S, zero_smul, zero_add, hsub]
      rw [Finset.sum_congr rfl hsplit, ← Finset.smul_sum, hif, ← hcomb]
    have hconv : (1/α) • p + (-β/α) • y1 = a := by
      rw [← hpe, smul_add, smul_smul, one_div_mul_cancel hαne, one_smul, smul_smul,
        add_assoc]
      have hz2 : ((1/α) * β) • y1 + (-β/α) • y1 = 0 := by
        rw [← add_smul]
        have hz : (1/α) * β + -β/α = 0 := by ring
        rw [hz, zero_smul]
      rw [hz2, add_zero]
    have hcoef : ∑ w ∈ S1, ((if w = y1 then -β/α else 0)
        + (1/α) * (if w ∈ S0 then f w else 0)) = 1 := by
      have hB0 : ∑ w ∈ S1, (if w ∈ S0 then f w else 0) = ∑ w ∈ S0, f w := by
        by_cases hy1S : y1 ∈ S0
        · have hsub : ∑ w ∈ S0, (if w ∈ S0 then f w else 0)
              = ∑ w ∈ S0, f w := Finset.sum_congr rfl fun w hw => if_pos hw
          rw [hS1, Finset.insert_eq_of_mem hy1S, hsub]
        · have hsub : ∑ w ∈ S0, (if w ∈ S0 then f w else 0)
              = ∑ w ∈ S0, f w := Finset.sum_congr rfl fun w hw => if_pos hw
          rw [hS1, Finset.sum_insert hy1S, if_neg hy1S, zero_add, hsub]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hB0, hone,
        Finset.sum_eq_single y1]
      · simp
        field_simp
        linarith
      · intro w _ hw; simp [hw]
      · intro h; exact absurd (Finset.mem_insert_self y1 S0) h
    have hmem : ∀ w ∈ S1, w ∈ (affineSpan ℝ ({x, y1, v} : Set V3) : Set V3) := by
      intro w hw
      rw [hS1] at hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact subset_affineSpan ℝ _ (by simp)
      · have hw2 : w ∈ ({x} ∪ {v} : Set V3) := by rw [← hfin.coe_toFinset]; exact hw'
        have hw3 : w ∈ ({x, y1, v} : Set V3) := by
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hw2 ⊢
          tauto
        exact subset_affineSpan ℝ _ hw3
    have hvec : ∑ w ∈ S1, ((if w = y1 then -β/α else 0)
        + (1/α) * (if w ∈ S0 then f w else 0)) • w = a := by
      have h1 : ∀ w ∈ S1, ((if w = y1 then -β/α else 0)
          + (1/α) * (if w ∈ S0 then f w else 0)) • w
          = (if w = y1 then -β/α else 0) • w
            + ((1/α) * (if w ∈ S0 then f w else 0)) • w := fun w _ => add_smul _ _ _
      have h2 : ∑ w ∈ S1, ((if w = y1 then -β/α else 0)
          + (1/α) * (if w ∈ S0 then f w else 0)) • w
          = ∑ w ∈ S1, (if w = y1 then -β/α else 0) • w
            + ∑ w ∈ S1, ((1/α) * (if w ∈ S0 then f w else 0)) • w := by
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      rw [h2, hA, hB, ← hconv]
      abel
    have hspan := sumSmulMemAffineSpan22 hmem hcoef
    rw [hvec] at hspan
    exact haU (Set.mem_iUnion₂.mpr ⟨v, hv, hspan⟩)

/-- 系数移植：`y ∈ affGt s t` 时，沿基点 `x0 ∈ s` 的凸组合
`z = τ • y + (1 - τ) • x0`（`0 < τ`，且 `x0 ∉ t` 保证 t-系数严格正）
仍落在 `affGt s t` 中（`AFF_GT_1_1` 型展开的核心步骤）。 -/
private theorem affGt_transplant (s t : Set V3) (x0 y z : V3) (τ : ℝ)
    (hx0 : x0 ∈ s) (hxt : x0 ∉ t) (hy : y ∈ affGt s t) (hτ : 0 < τ)
    (hz : z = τ • y + (1 - τ) • x0) :
    z ∈ affGt s t := by
  have hy' : Affsign (fun r : ℝ => 0 < r) s t y := hy
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hy'
  have hmemS : x0 ∈ hfin.toFinset :=
    (hfin.mem_toFinset).2 (Set.mem_union_left t hx0)
  have hvec : z = ∑ w ∈ hfin.toFinset,
      (fun w => τ * f w + if w = x0 then 1 - τ else 0) w • w := by
    have hA : ∑ w ∈ hfin.toFinset,
        (fun w => τ * f w + if w = x0 then 1 - τ else 0) w • w
        = ∑ w ∈ hfin.toFinset,
          ((τ * f w) • w + (if w = x0 then 1 - τ else 0) • w) :=
      Finset.sum_congr rfl fun w _ => add_smul _ _ _
    have hB : ∑ w ∈ hfin.toFinset, (τ * f w) • w
        = τ • ∑ w ∈ hfin.toFinset, f w • w := by
      have hB1 : ∀ w ∈ hfin.toFinset, (τ * f w) • w = τ • (f w • w) :=
        fun w _ => mul_smul τ (f w) w
      rw [Finset.sum_congr rfl hB1, ← Finset.smul_sum]
    have hC : ∑ w ∈ hfin.toFinset, (if w = x0 then 1 - τ else 0) • w
        = (1 - τ) • x0 := by
      rw [Finset.sum_eq_single x0]
      · simp
      · intro w _ hw
        simp [hw]
      · intro h
        exact absurd hmemS h
    rw [hA, Finset.sum_add_distrib, hB, hC, ← hsum]
    exact hz
  have hpos' : ∀ w ∈ t, 0 < (fun w => τ * f w + if w = x0 then 1 - τ else 0) w := by
    intro w hw
    have hwne : w ≠ x0 := fun h => hxt (h ▸ hw)
    simp only [if_neg hwne, add_zero]
    exact mul_pos hτ (hpos w hw)
  have hsc : ∑ w ∈ hfin.toFinset,
      (fun w => τ * f w + if w = x0 then 1 - τ else 0) w = 1 := by
    have hD : ∑ w ∈ hfin.toFinset, (if w = x0 then 1 - τ else 0) = 1 - τ := by
      rw [Finset.sum_eq_single x0]
      · simp
      · intro w _ hw
        simp [hw]
      · intro h
        exact absurd hmemS h
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hD, hone]
    ring
  exact ⟨fun w => τ * f w + if w = x0 then 1 - τ else 0, hfin, hvec, hpos', hsc⟩

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
  -- `x ≠ y`：dartsetLeadsIntoFan 是 yfan 的拓扑分量，而 x ∈ xfan = yfanᶜ
  have htop : dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E :=
    dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds
  have hxy : x ≠ y :=
    point_in_yfan_not_x_fan x V E (dartsetLeadsIntoFan x V E ds) y hfan hE htop hy
  -- conforming 半空间分解
  have hHS : dartsetLeadsIntoFan x V E ds =
      ⋂ d ∈ ds, affGt ({x, d.1, d.2} : Set V3) {(f1Fan x V E d).2} :=
    hconf.2.2.2.1 ds hds
  rw [hHS]
  -- ds 中的 dart 都是带边 dart
  have hdartscoe : ((hypermapOfFan x V E hfan).darts : Set (V3 × V3)) =
      dart1OfFan V E := by
    change ((finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hxV : x ∉ V := hfan.2.2.2.1
  intro z hz
  simp only [Set.mem_iInter]
  intro d hd
  -- 半空间目标点换名
  show z ∈ affGt ({x, d.1, d.2} : Set V3) {inverse1SigmaFan x V E d.2 d.1}
  -- y 本身在每个半空间中
  have hyd : y ∈ affGt ({x, d.1, d.2} : Set V3)
      {inverse1SigmaFan x V E d.2 d.1} := by
    have hy' := hy
    rw [hHS] at hy'
    simp only [Set.mem_iInter] at hy'
    exact hy' d hd
  -- d 是带边 dart：{d.1, d.2} ∈ E
  have hde : ({d.1, d.2} : Set V3) ∈ E := by
    obtain ⟨d0, hd0, hd0f⟩ := (hypermapOfFan x V E hfan).face_representation hds
    have hmd : d ∈ (hypermapOfFan x V E hfan).face d0 := by
      rw [← hd0f]; exact hd
    have hsub := (hypermapOfFan x V E hfan).face_subset_darts hd0 hmd
    rw [hdartscoe] at hsub
    simpa [dart1OfFan] using hsub
  -- f1Fan 的第二分量是 E-邻居顶点，故 ≠ x（fan2: x ∉ V）
  have hpe : ({d.2, inverse1SigmaFan x V E d.2 d.1} : Set V3) ∈ E :=
    (INVERSE1_SIGMA_FAN (v := d.2) hfan).1 d.1 (by rw [Set.pair_comm]; exact hde)
  have hpV : inverse1SigmaFan x V E d.2 d.1 ∈ V :=
    hfan.1 (Set.mem_sUnion.mpr ⟨{d.2, inverse1SigmaFan x V E d.2 d.1}, hpe, by simp⟩)
  have hxp : x ≠ inverse1SigmaFan x V E d.2 d.1 := fun h => hxV (h ▸ hpV)
  -- z ∈ affGt {x} {y} 的坐标展开（AFF_GT_1_1 成员形式）
  have hz' : Affsign (fun r : ℝ => 0 < r) ({x} : Set V3) {y} z := hz
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hz'
  rw [sum_insert_single_s hfin hxy] at hone
  rw [sum_insert_single_v hfin hxy] at hsum
  have hfy : 0 < f y := hpos y (Set.mem_singleton y)
  have hfx : f x = 1 - f y := by linarith
  -- 沿基点 x 把射线移植进半空间锥
  refine affGt_transplant ({x, d.1, d.2} : Set V3)
      {inverse1SigmaFan x V E d.2 d.1} x y z (f y) ?_ ?_ hyd hfy ?_
  · simp
  · simp only [Set.mem_singleton_iff]
    exact hxp
  · rw [hsum, hfx]
    module

end Kepler.Text
