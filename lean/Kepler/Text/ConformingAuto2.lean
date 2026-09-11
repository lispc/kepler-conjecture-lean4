/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 2
(Conforming.hl:484-730).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 2, Conforming.hl:484-730):
- `version_JUTSTKG` (484)
- `measurable_dartset_leads_into30_fan` (531)
- `DWFBRQY` (550; HOL spells the binder `let   DWFBRQY`, the extra blanks
  defeat the pipeline's `let `-name extraction, which is why the batch
  listing showed an empty name at :550)
- `NEGLIGIBLE_AFF_3` (652)
- `NEGLIGIBLE_AFF_GE_2_1` (660)
- `NEGLIGIBLE_AFF_GE_1_2` (681)
- `NEGLIGIBLE_AFF_GT_1_2` (691)
- `NEGLIGIBLE_AFF_3_INTER_BALL` (703)
- `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL` (713)
- `MEASURE_AFF_GT_2_1_INTER_BALL` (722; HOL name says 2-1 but the statement
  is about the 1-2 set `aff_gt {x} {v,u}`; the name is kept verbatim)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityAuto15.lean:26).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`, `d_fan` ↦ `dartOfFan` (Fan.lean:90).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; `face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` with pair darts
  (Kepler/Text/Fan.lean:1169); `hfan : FAN x V E` is passed explicitly.
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL
  `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); HOL `fan80` ↔ `fan80` (Fan.lean:227);
  `CARD ds` ↔ `ds.ncard`.
- HOL `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (ConformingDefs.lean:184); HOL `N_FAN(x,V,E)` ↔ `nFan x V E hfan`
  (ConformingDefs.lean:204).
- HOL `measurable` ↔ `MeasurableSet`; HOL `ball (x,r)`/`normball x r` ↔
  Mathlib `Metric.ball x r` (cf. Kepler/Text/PlanarityAuto15.lean:46).
- HOL `aff {x,v,u}` (affine hull, `aff`) ↔ Mathlib
  `affineSpan ℝ ({x,v,u} : Set V3)`. HOL `aff_ge`/`aff_gt` ↔ `affGe`/`affGt`
  (Kepler/Geom/Aff.lean:39/42); HOL `collinear {x,v,u}` ↔
  `Collinear3 x v u` (Kepler/Geom/Azim.lean:43).
- HOL `negligible s` and `measure s = &0` are NOT ported. They are encoded
  as the Mathlib Lebesgue measure-zero predicate `volume s = 0`
  (`volume : Measure V3`, cf. Kepler/Geom/Volume.lean). `negligible` is
  definitionally `measure s = &0` in HOL, so `NEGLIGIBLE_*` and
  `MEASURE_*` share this encoding.
- This file imports `Kepler.Text.PlanarityAuto16` and
  `Kepler.Text.ConformingDefs` (the latter already pulls in `Mathlib`), so
  `MeasurableSet`, `volume` and `affineSpan` are reachable.
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

/-! ## 分量由面实现（Conforming.hl:484-530） -/

/-- HOL Conforming.hl :484-530 `version_JUTSTKG`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
==> ?f. f IN face_set (hypermap1_of_fanx (x,V,E)) /\ dartset_leads_into_fan x V E f = U
```

编码说明：HOL `?f. ...` 中 `f` 是面（dart 集合），在二元组编码下
`f : Set (V3 × V3)`；`hypermap1_of_fanx` ↦ `hypermapOfFan x V E hfan`
（需显式 `hfan`，见文件头）。

证明思路：先用 `JUTSTKG`（HOL planarity.hl:13413）把 `U` 写成
`dartLeadsInto x V E v u`（`{v,u} ∈ E`）；令
`y = (v, u)`、`f = (hypermapOfFan x V E hfan).face y`，由
`dartset_fully_surrounded_is_non_isolated_fan` 的二元组版
`dartOfFan_eq_dart1_of_surrounded` 得 `y ∈ d_fan`，再用
`DARTSET_LEADS_INTO_FAN` 与 `face_representation` 证明
`dartsetLeadsIntoFan x V E f = U`。

候选已有引理：
- `JUTSTKG`（Kepler/Text/PlanarityAuto11.lean:679）
- `DARTSET_LEADS_INTO_FAN`（Kepler/Text/PlanarityComponent.lean:375）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169） -/
theorem version_JUTSTKG (x : V3) (V : Set V3) (E : Set (Set V3)) (U : Set V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) :
    ∃ f : Set (V3 × V3), f ∈ (hypermapOfFan x V E hfan).faceSet ∧
      dartsetLeadsIntoFan x V E f = U := by
  obtain ⟨v, u, huv, hdart⟩ := JUTSTKG x V E U hfan hcard hfan80 hU
  have hdart1 : (v, u) ∈ dart1OfFan V E := huv
  have hmem : (v, u) ∈ (hypermapOfFan x V E hfan).darts := by
    show (v, u) ∈ (finite_dart1_fan hfan).toFinset
    exact (finite_dart1_fan hfan).mem_toFinset.mpr hdart1
  refine ⟨(hypermapOfFan x V E hfan).face (v, u), ?_, ?_⟩
  · exact (Hypermap.mem_darts_iff_face_mem _ _).mp hmem
  · have hyf : (v, u) ∈ (hypermapOfFan x V E hfan).face (v, u) :=
      Hypermap.mem_face_self _ _
    have hleads := DARTSET_LEADS_INTO_FAN hfan hcard hfan80
      (show (hypermapOfFan x V E hfan).face (v, u) ∈
        (hypermapOfFan x V E hfan).faceSet from
        (Hypermap.mem_darts_iff_face_mem _ _).mp hmem)
    rw [hleads (v, u) hyf, hdart]

/-- HOL Conforming.hl :531-549 `measurable_dartset_leads_into30_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds e.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
==>   measurable((dartset_leads_into_fan x V E ds) INTER ball (x,e))
```

编码说明：与 planarity.hl 的 `measurable_dartset_leads_into3_fan`
（PlanarityAuto16.lean:184）相比少了 `e > &0` 假设；HOL `measurable` ↦
`MeasurableSet`，`ball (x,e)` ↦ `Metric.ball x e`。

证明思路：由 `KVQWYDL_lemma10` 把 `dartsetLeadsIntoFan ds` 换为
`affGt {x} {f1.1,f2.1,f3.1}`（`CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
给出 `f1,f2,f3`），再用 `OPEN_AFF_GT_1_3` 得开集可测、
`Metric.isOpen_ball.measurableSet` 得球可测，最后取交。

候选已有引理：
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`（Kepler/Text/PlanarityAuto15.lean:371）
- `OPEN_AFF_GT_1_3`（Kepler/Text/PlanarityAuto12.lean:877）
- `measurable_dartset_leads_into3_fan`（Kepler/Text/PlanarityAuto16.lean:184）
- 缺口：HOL `MEASURABLE_BALL_AFF_GT` 未以该名移植（其结论由
  `OPEN_AFF_GT_1_3` + 球可测代替） -/
theorem measurable_dartset_leads_into30_fan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (ds : Set (V3 × V3)) (e : ℝ)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x e) := by
  by_cases he : 0 < e
  · exact measurable_dartset_leads_into3_fan hfan hcard hfan80 hds hds3 he
  · rw [Metric.ball_eq_empty.mpr (le_of_not_gt he)]
    simp

/-- HOL Conforming.hl :550-651 `DWFBRQY`（HOL 中 `let   DWFBRQY=prove(...)`，
多空格使批次名提取为空）

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ N_FAN(x,V,E)=0
==> conforming_fan (x,V,E)
```

编码说明：`conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
（ConformingDefs.lean:184，本身已含 `CARD (set_of_edge …) > 1` 与 `fan80`
合取项）；`N_FAN(x,V,E)` ↔ `nFan x V E hfan`（ConformingDefs.lean:204）。

证明思路：由 `N_FAN_EQ_0_IMP_CARD_FACE_EQ_3` 得每个面 `ds` 满足
`ds.ncard = 3`，逐项验证 `conformingFan` 的六个合取支：
`conformingBijectionFan` 用 `version_JUTSTKG` + `exists_point_dart_leads_into_fan`
与 `face_subset_darts`；`conformingHalfSpaceFan` 用 `KVQWYDL_lemma10` +
`CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` + `properties_fully_surrounded` +
`inter_aff_gt_3_1_is_aff_gt_1_3`；`conformingSolidAngleFan` 用
`measurable_dartset_leads_into30_fan` + `dartset_leads_into_fan_eventually_radial_norm`
+ `solid_of_dartset_leads_into_fan_triangle_fan`（后者为已知阻塞 sorry）；
`conformingDiagonalFan` 用 `KVQWYDL_lemma30` 与 `remark1_fan`。

候选已有引理：
- `N_FAN_EQ_0_IMP_CARD_FACE_EQ_3`（Kepler/Text/ConformingAuto1.lean:851）
- `version_JUTSTKG`（本文件上文，HOL :484）
- `measurable_dartset_leads_into30_fan`（本文件上文，HOL :531）
- `solid_of_dartset_leads_into_fan_triangle_fan`（Kepler/Text/PlanarityAuto16.lean:533）
- `dartset_leads_into_fan_eventually_radial_norm`（Kepler/Text/PlanarityAuto16.lean:140）
- `exists_point_dart_leads_into_fan`（Kepler/Text/PlanarityComponent.lean:500）
- `face_subset_darts`（Kepler/Text/Hypermap.lean:854）
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466）、
  `KVQWYDL_lemma30`（Kepler/Text/PlanarityAuto15.lean:587）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`（Kepler/Text/PlanarityAuto15.lean:371）
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- 缺口：`lemma_face_identity`（Kepler/Text/Hypermap.lean:2485 附近有实现，
  但 HOL `exists_point_dart_leads_into_fan` 的对应组合需现场拼装） -/
theorem DWFBRQY (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hn : nFan x V E hfan = 0) :
    conformingFan x V E hfan := by
  sorry

/-! ## 低维仿射集的零测性（Conforming.hl:652-730） -/

/-- HOL Conforming.hl :652-659 `NEGLIGIBLE_AFF_3`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3.
  negligible (aff {x,v,u})
```

编码说明（缺口）：HOL `negligible s`（= `measure s = &0`）未移植，用
Mathlib 的 Lebesgue 零测谓词 `volume s = 0`；HOL `aff`（仿射包）↦
Mathlib `affineSpan ℝ`。故结论为
`volume ((affineSpan ℝ {x,v,u}) : Set V3) = 0`。

证明思路：`affineSpan ℝ {x,v,u}` 至多 2 维，作为 `ℝ³` 的真仿射子空间由
`addHaar_affineSubspace` 得测度为零；需证 `affineSpan ℝ {x,v,u} ≠ ⊤`
（3 点生成的仿射子空间维数 ≤ 2 < 3）。

候选已有引理：
- `addHaar_affineSubspace`（Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:199）
- `finrank_affineSpan_le` / `AffineSubspace.finrank_lt`（Mathlib）
- 缺口：HOL `NEGLIGIBLE_AFFINE_HULL_3`、`aff` 未以该名移植 -/
private theorem finrank_span_pair_le_two_auto2 (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h
  have h2 : ({a, b} : Finset V3).card ≤ 2 := by
    calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
      _ = 2 := by simp
  omega

private theorem affineSpan_three_ne_top_auto2 (x v u : V3) :
    (affineSpan ℝ ({x, v, u} : Set V3)) ≠ ⊤ := by
  intro h
  have hdir : (affineSpan ℝ ({x, v, u} : Set V3)).direction = ⊤ := by
    rw [h]; exact AffineSubspace.direction_top ℝ V3 V3
  have hvs : vectorSpan ℝ ({x, v, u} : Set V3)
      = Submodule.span ℝ ({v - x, u - x} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show x ∈ ({x, v, u} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro p ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro p (rfl | rfl)
      · exact Submodule.subset_span ⟨v, by simp, rfl⟩
      · exact Submodule.subset_span ⟨u, by simp, rfl⟩
  have hle : Module.finrank ℝ (affineSpan ℝ ({x, v, u} : Set V3)).direction ≤ 2 := by
    rw [direction_affineSpan, hvs]
    exact finrank_span_pair_le_two_auto2 (v - x) (u - x)
  rw [hdir, finrank_top] at hle
  have h3 : Module.finrank ℝ V3 = 3 := by simp [V3]
  omega

theorem NEGLIGIBLE_AFF_3 (x v u : V3) :
    volume ((affineSpan ℝ ({x, v, u} : Set V3)) : Set V3) = 0 := by
  exact MeasureTheory.Measure.addHaar_affineSubspace volume _
    (affineSpan_three_ne_top_auto2 x v u)

/-- 有限仿射组合落入仿射子空间：`∑ w∈s, f w • w`（权重和为 1，各点属于
`affineSpan ℝ T`）仍属于 `affineSpan ℝ T`。取基点 `b`，把组合写成
`b + ∑ w, f w • (w - b)`，后项落在方向子空间。 -/
private theorem finset_sum_smul_mem_affineSpan_auto2 {T : Set V3} {s : Finset V3}
    {f : V3 → ℝ}
    (hS : ∀ w ∈ s, w ∈ (affineSpan ℝ T : Set V3))
    (hsum : ∑ w ∈ s, f w = 1) :
    ∑ w ∈ s, f w • w ∈ (affineSpan ℝ T : Set V3) := by
  have hne : s.Nonempty :=
    Finset.nonempty_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
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

/-- `affGe {x,v} {u} ⊆ aff {x,v,u}`：`Affsign` 的见证是 `{x,v,u}` 上权重和为 1
的仿射组合，故落入其仿射张成。 -/
private theorem affGe_pair_singleton_subset_affineSpan_auto2 (x v u : V3) :
    affGe ({x, v} : Set V3) {u} ⊆ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) := by
  intro y hy
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hy
  obtain ⟨f, hfin, hcomb, _hpos, hone⟩ := hy
  have hmem : ∀ w ∈ hfin.toFinset, w ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3) := by
    intro w hw
    have hw' : w ∈ ({x, v} ∪ {u} : Set V3) := by
      rw [← hfin.coe_toFinset]
      exact hw
    have hw'' : w ∈ ({x, v, u} : Set V3) := by
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hw' ⊢
      tauto
    exact subset_affineSpan ℝ _ hw''
  rw [hcomb]
  exact finset_sum_smul_mem_affineSpan_auto2 hmem hone

/-- HOL Conforming.hl :660-680 `NEGLIGIBLE_AFF_GE_2_1`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3.
~collinear {x,v,u}
==>  negligible (aff_ge {x,v} {u})
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
HOL `aff_ge {x,v} {u}` ↔ `affGe ({x,v} : Set V3) {u}`
（Kepler/Geom/Aff.lean:42）；HOL `~collinear {x,v,u}` ↔
`¬ Collinear3 x v u`（Kepler/Geom/Azim.lean:43）。

证明思路：不共线保证 `affGe {x,v} {u}` 含于过 `x,v,u` 的平面内某条
半平面；用 `NEGLIGIBLE_SUBSET` 的 Mathlib 版 `measure_mono_null`，把该
半平面含于一张二维仿射子空间（超平面），后者由
`addHaar_affineSubspace` 零测。

候选已有引理：
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `addHaar_affineSubspace`（Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:199）
- 缺口：HOL `exp_aff_ge_by_dot`、`NEGLIGIBLE_HYPERPLANE`、
  `properties_coordinate`、`e1_fan`/`e2_fan` 未以该名移植 -/
theorem NEGLIGIBLE_AFF_GE_2_1 (x v u : V3) (h : ¬ Collinear3 x v u) :
    volume (affGe ({x, v} : Set V3) {u}) = 0 := by
  exact measure_mono_null (affGe_pair_singleton_subset_affineSpan_auto2 x v u)
    (NEGLIGIBLE_AFF_3 x v u)

/-- HOL Conforming.hl :681-690 `NEGLIGIBLE_AFF_GE_1_2`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3.
~collinear {x,v,u}
==>  negligible (aff_ge {x} {v,u})
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
HOL `aff_ge {x} {v,u}` ↔ `affGe ({x} : Set V3) {v,u}`；
HOL `~collinear {x,v,u}` ↔ `¬ Collinear3 x v u`。

证明思路：HOL 由 `aff_ge_inter_aff_ge` 把 `affGe {x} {v,u}` 表示为
`affGe {x,v} {u} ∩ affGe {x,u} {v}`（或其一），再用
`measure_mono_null` 与 `NEGLIGIBLE_AFF_GE_2_1` 收口。

候选已有引理：
- `NEGLIGIBLE_AFF_GE_2_1`（本文件上文，HOL :660）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- 缺口：HOL `aff_ge_inter_aff_ge` 未以该名移植 -/
theorem NEGLIGIBLE_AFF_GE_1_2 (x v u : V3) (h : ¬ Collinear3 x v u) :
    volume (affGe ({x} : Set V3) {v, u}) = 0 := by
  rw [aff_ge_inter_aff_ge h]
  exact measure_mono_null Set.inter_subset_left (NEGLIGIBLE_AFF_GE_2_1 x v u h)

/-- HOL Conforming.hl :691-702 `NEGLIGIBLE_AFF_GT_1_2`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3.
~collinear {x,v,u}
==>  negligible (aff_gt {x} {v,u})
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
HOL `aff_gt {x} {v,u}` ↔ `affGt ({x} : Set V3) {v,u}`
（Kepler/Geom/Aff.lean:39）；HOL `~collinear {x,v,u}` ↔
`¬ Collinear3 x v u`。

证明思路：由 `aff_gt_subset_aff_ge`（`affGt s t ⊆ affGe s t`，
`Affsign` 中严格正推出非负）把 `affGt {x} {v,u}` 含于
`affGe {x} {v,u}`，再用 `measure_mono_null` 与
`NEGLIGIBLE_AFF_GE_1_2`。

候选已有引理：
- `NEGLIGIBLE_AFF_GE_1_2`（本文件上文，HOL :681）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- 缺口：HOL `aff_gt_subset_aff_ge`、`th3` 未以该名公开移植（`Affsign`
  的单调性可从定义直接展开） -/
theorem NEGLIGIBLE_AFF_GT_1_2 (x v u : V3) (h : ¬ Collinear3 x v u) :
    volume (affGt ({x} : Set V3) {v, u}) = 0 := by
  apply measure_mono_null _ (NEGLIGIBLE_AFF_GE_1_2 x v u h)
  rintro y ⟨f, hfin, hyeq, hpos, hone⟩
  exact ⟨f, hfin, hyeq, fun w hw => le_of_lt (hpos w hw), hone⟩

/-- HOL Conforming.hl :703-712 `NEGLIGIBLE_AFF_3_INTER_BALL`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 r:real.
negligible (aff  {x,v,u} INTER normball x r)
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
HOL `aff {x,v,u}` ↔ `affineSpan ℝ ({x,v,u} : Set V3)`；
`normball x r` ↔ `Metric.ball x r`。

证明思路：由 `Set.inter_subset_left` 得
`affineSpan … ∩ Metric.ball x r ⊆ affineSpan …`，再用
`measure_mono_null` 与 `NEGLIGIBLE_AFF_3`。

候选已有引理：
- `NEGLIGIBLE_AFF_3`（本文件上文，HOL :652）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `Set.inter_subset_left`（Mathlib/Data/Set/Basic.lean） -/
theorem NEGLIGIBLE_AFF_3_INTER_BALL (x v u : V3) (r : ℝ) :
    volume (((affineSpan ℝ ({x, v, u} : Set V3)) : Set V3) ∩
      Metric.ball x r) = 0 := by
  exact measure_mono_null Set.inter_subset_left (NEGLIGIBLE_AFF_3 x v u)

/-- HOL Conforming.hl :713-721 `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 r:real.
~collinear {x,v,u}
==>  negligible (aff_gt {x} {v,u} INTER normball x r)
```

编码说明（缺口）：`negligible` 用 `volume = 0`（见文件头）；
HOL `aff_gt {x} {v,u}` ↔ `affGt ({x} : Set V3) {v,u}`；
`normball x r` ↔ `Metric.ball x r`；HOL `~collinear {x,v,u}` ↔
`¬ Collinear3 x v u`。

证明思路：由 `Set.inter_subset_left` 得
`affGt {x} {v,u} ∩ Metric.ball x r ⊆ affGt {x} {v,u}`，再用
`measure_mono_null` 与 `NEGLIGIBLE_AFF_GT_1_2`。

候选已有引理：
- `NEGLIGIBLE_AFF_GT_1_2`（本文件上文，HOL :691）
- `measure_mono_null`（Mathlib/MeasureTheory/OuterMeasure/Basic.lean:54）
- `Set.inter_subset_left`（Mathlib/Data/Set/Basic.lean） -/
theorem NEGLIGIBLE_AFF_GT_1_2_INTER_BALL (x v u : V3) (r : ℝ)
    (h : ¬ Collinear3 x v u) :
    volume (affGt ({x} : Set V3) {v, u} ∩ Metric.ball x r) = 0 := by
  exact measure_mono_null Set.inter_subset_left (NEGLIGIBLE_AFF_GT_1_2 x v u h)

/-- HOL Conforming.hl :722-730 `MEASURE_AFF_GT_2_1_INTER_BALL`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 r:real.
~collinear {x,v,u}==>   measure (aff_gt {x} {v,u} INTER normball x r)= &0
```

编码说明（缺口）：HOL 名虽为 `GT_2_1`，陈述中的集合是 1-2 型
`aff_gt {x} {v,u}`（名称原样保留）。HOL `measure s = &0` 与
`negligible s` 定义等价，统一编码为 `volume s = 0`（见文件头）；
HOL `aff_gt {x} {v,u}` ↔ `affGt ({x} : Set V3) {v,u}`；
`normball x r` ↔ `Metric.ball x r`；HOL `~collinear {x,v,u}` ↔
`¬ Collinear3 x v u`。

证明思路：HOL 为 `MATCH_MP_TAC MEASURE_EQ_0` 后套用
`NEGLIGIBLE_AFF_GT_1_2_INTER_BALL`。在 `volume = 0` 编码下两条陈述
类型相同，直接引用即可。

候选已有引理：
- `NEGLIGIBLE_AFF_GT_1_2_INTER_BALL`（本文件上文，HOL :713）
- 缺口：HOL `MEASURE_EQ_0` 未移植（`volume = 0` 下即为定义等价） -/
theorem MEASURE_AFF_GT_2_1_INTER_BALL (x v u : V3) (r : ℝ)
    (h : ¬ Collinear3 x v u) :
    volume (affGt ({x} : Set V3) {v, u} ∩ Metric.ball x r) = 0 := by
  exact NEGLIGIBLE_AFF_GT_1_2_INTER_BALL x v u r h
