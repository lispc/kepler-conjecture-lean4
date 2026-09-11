/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 5
(Conforming.hl:1037-1266).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 5, Conforming.hl:1037-1266):
- `SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET` (1037)
- `SOL_EMPTY` (1085)
- `SOL_DISJOINT_UNION` (1093)
- `UNIONS_INTER` (1109)            [SKIPPED: Mathlib-general, see below]
- `UNIONS_INTER1` (1135)           [SKIPPED: Mathlib-general, see below]
- `MEASURABLE_UNIONS` (1158)       [SKIPPED: Mathlib-general, see below]
- `SOL_UNIONS` (1170)
- `BOUNDED_INTER_BALL` (1227)
- `OPEN_AFF_GT_3_1` (1238)
- `EQ_SET_THM` (1263)              [SKIPPED: Mathlib-general, see below]

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `sol x C` ↔ `Kepler.Geom.sol x C` (Kepler/Geom/Volume.lean:36);
  HOL `radial_norm r x C` ↔ `radialNorm r x C`
  (Kepler/Geom/Volume.lean:27); HOL `eventually_radial` ↔
  `EventuallyRadial` (Kepler/Geom/Volume.lean:32).
- HOL `measurable` ↔ `MeasurableSet`; HOL `normball x r` ↔ Mathlib
  `Metric.ball x r` (both are `{y | dist y x < r}`; cf. `NORMBALL_BALL`,
  sphere.hl); HOL `bounded s` ↔ `Bornology.IsBounded s` (repo convention,
  cf. Kepler/Text/TopologyFan.lean:2764).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184); HOL
  `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); HOL `dartset_leads_into_fan` ↔
  `dartsetLeadsIntoFan` (Kepler/Text/PlanarityComponent.lean:348).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48, `face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` with pair darts `V3 × V3`, and the
  explicit `hfan : FAN x V E` witness is carried through (HOL's
  `hypermap_of_fan` is total).
- HOL `sum S g` (set sum / `iterate`) ↔ finsum `∑ᶠ y ∈ S, g y`
  (`open scoped BigOperators`); `UNIONS f` ↔ `⋃₀ f` (`Set.sUnion`);
  `UNION`/`INTER` ↔ `∪`/`∩`; `DISJOINT s t` ↔ `Disjoint s t`.
- HOL `coplanar` ↔ `Coplanar` (Kepler/Geom/Coplanar.lean:23); HOL
  `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL `open` ↔ `IsOpen`.

Mathlib-general statements skipped (per task rules):
- `UNIONS_INTER` (Conforming.hl:1109-1134) and `UNIONS_INTER1`
  (1135-1157) are the same general distributive identity
  `(⋃₀ f) ∩ t = ⋃₀ {s ∩ t | s ∈ f}`. Mathlib has it: `Set.iUnion_inter`
  (Mathlib/Data/Set/Lattice.lean:337) after `Set.sUnion_eq_iUnion`
  (Mathlib/Data/Set/Lattice.lean:1064). Nothing repo-specific.
- `MEASURABLE_UNIONS` (1158-1169) is exactly
  `Set.Finite.measurableSet_sUnion`
  (Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:132):
  `s.Finite → (∀ t ∈ s, MeasurableSet t) → MeasurableSet (⋃₀ s)`.
- `EQ_SET_THM` (1263-1266) is the defining equation of `Set.image`:
  `f '' f' = {t | ∃ y ∈ f', t = f y}` is immediate from `Set.image`
  (Mathlib/Data/Set/Defs.lean:261) and `Set.mem_image`
  (Mathlib/Data/Set/Image.lean). No new content.
- The remaining six statements mention the repo-specific
  `FAN`/`conformingFan`/`topologicalComponentYfan`/`dartsetLeadsIntoFan`/
  `sol`/`radialNorm`/`Coplanar`/`affGt` vocabulary, so none is skipped.
- `OPEN_AFF_GT_3_1` was already proved in PlanarityAuto12.lean as the
  `private` helper `isOpen_affGt_3_1`; it is restated here (public, with
  its HOL name) as required by the batch, noting that helper.
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

/-! ## 拓扑分量与面集上的 `sol` 和（Conforming.hl:1037-1108） -/

/-- HOL Conforming.hl :1037-1084 `SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET`

HOL 原文：
```
!x:real^3 V E.
FAN(x,V,E) /\ conforming_fan (x,V,E)
==>  sum (topological_component_yfan (x,V,E)) (\f. sol x f) = sum (face_set (hypermap1_of_fanx (x,V,E))) (\f. sol x (dartset_leads_into_fan x V E f))
```

编码说明：`FAN(x,V,E)` ↔ `FAN x V E`；`conforming_fan (x,V,E)` ↔
`conformingFan x V E hfan`（需显式 `hfan`，见文件头）；HOL 集合和
`sum S g` ↔ finsum `∑ᶠ y ∈ S, g y`；`topological_component_yfan` ↔
`topologicalComponentYfan`；`face_set (hypermap1_of_fanx ...)` ↔
`(hypermapOfFan x V E hfan).faceSet`；`sol` ↔ `Kepler.Geom.sol`。

证明思路：由 `conformingFan` 取出 `conformingBijectionFan`，它给出
`topologicalComponentYfan` 与 `faceSet` 之间由
`f ↦ dartsetLeadsIntoFan x V E f` 实现的双射；对 finsum 作重指标
（HOL `SUM_IMAGE`，Mathlib `Finset.sum_image` + `finsum` 重指标），
并用 `dartset_leads_into_is_topological_component_yfan` 确认像恰为
`topologicalComponentYfan`，从而两边相等。

候选已有引理：
- `conformingBijectionFan`（Kepler/Text/ConformingDefs.lean:104）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `Finset.sum_image`
  （Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean）
- 缺口：Mathlib 无集合版 `finsum_image`，需先经
  `finsum_eq_sum` 与 `(hypermapOfFan …).faceSet` 的有限性转成 `Finset` -/
theorem SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET {x : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan) :
    (∑ᶠ f ∈ topologicalComponentYfan x V E, sol x f) =
      ∑ᶠ f ∈ (hypermapOfFan x V E hfan).faceSet,
        sol x (dartsetLeadsIntoFan x V E f) := by
  obtain ⟨hcard, hfan80, hbij, -⟩ := hconf
  have hmaps : Set.MapsTo (dartsetLeadsIntoFan x V E)
      (hypermapOfFan x V E hfan).faceSet (topologicalComponentYfan x V E) :=
    fun f hf => dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hf
  have hsurj : Set.SurjOn (dartsetLeadsIntoFan x V E)
      (hypermapOfFan x V E hfan).faceSet (topologicalComponentYfan x V E) := by
    intro s hs
    obtain ⟨f, hf, -⟩ := hbij s hs
    exact ⟨f, hf.1, hf.2.symm⟩
  have hinj : Set.InjOn (dartsetLeadsIntoFan x V E)
      (hypermapOfFan x V E hfan).faceSet := by
    intro f hf f' hf' heq
    have hsf : dartsetLeadsIntoFan x V E f ∈ topologicalComponentYfan x V E := hmaps hf
    obtain ⟨g, hg, huniq⟩ := hbij (dartsetLeadsIntoFan x V E f) hsf
    have hfg : f = g := huniq f ⟨hf, rfl⟩
    have hf'g : f' = g := huniq f' ⟨hf', heq⟩
    rw [hfg, hf'g]
  have hbijOn : Set.BijOn (dartsetLeadsIntoFan x V E)
      (hypermapOfFan x V E hfan).faceSet (topologicalComponentYfan x V E) :=
    ⟨hmaps, hinj, hsurj⟩
  exact (finsum_mem_eq_of_bijOn (dartsetLeadsIntoFan x V E) hbijOn
    (fun _ _ => rfl)).symm

/-- HOL Conforming.hl :1085-1092 `SOL_EMPTY`

HOL 原文：
```
!x:real^3.
         sol x {} = &0
```

编码说明：`sol` ↔ `Kepler.Geom.sol`；`{}` ↔ `∅`；`&0` ↔ `0`。

证明思路：用 `sol_spec`（Volume.lean:171）以半径 `r = 1 > 0` 实例化：
`∅ ∩ ball x 1 = ∅` 可测（`MeasurableSet.empty`）、
`radialNorm 1 x ∅`（`RADIAL_EMPTY`，ConformingAuto4.lean:93）；又
`volume.real ∅ = 0`，故 `sol x ∅ = 3 * 0 / 1 ^ 3 = 0`，`ring` 收口。

候选已有引理：
- `sol_spec`（Kepler/Geom/Volume.lean:171）
- `RADIAL_EMPTY`（Kepler/Text/ConformingAuto4.lean:93）
- `MeasurableSet.empty`、`measure_empty`（Mathlib）
- `Set.inter_empty`/`Set.empty_inter`（Mathlib/Data/Set/Basic.lean） -/
theorem SOL_EMPTY (x : V3) : sol x (∅ : Set V3) = 0 := by
  have hr : (0 : ℝ) < 1 := by norm_num
  have hm : MeasurableSet ((∅ : Set V3) ∩ Metric.ball x 1) := by
    rw [Set.empty_inter]
    exact MeasurableSet.empty
  have hrad : radialNorm 1 x ((∅ : Set V3) ∩ Metric.ball x 1) := by
    rw [Set.empty_inter]
    refine ⟨Set.empty_subset _, ?_⟩
    intro u hu
    exact (Set.notMem_empty (x := x + u) hu).elim
  rw [sol_spec hr hm hrad, Set.empty_inter, Measure.real_def, measure_empty]
  norm_num

/-- HOL Conforming.hl :1093-1108 `SOL_DISJOINT_UNION`

HOL 原文：
```
!x:real^3 s t r. r > &0 /\  measurable (s INTER normball x r) /\ measurable (t INTER normball x r) /\ DISJOINT s t /\ radial_norm r x (s INTER normball x r) /\ radial_norm r x (t INTER normball x r)
         ==> sol x (s UNION t) = sol x s + sol x t
```

编码说明：`measurable` ↔ `MeasurableSet`；`normball x r` ↔
`Metric.ball x r`；`DISJOINT s t` ↔ `Disjoint s t`；`radial_norm` ↔
`radialNorm`；`UNION`/`INTER` ↔ `∪`/`∩`；`sol` ↔ `Kepler.Geom.sol`。

证明思路：`MeasurableSet.union` 得 `(s ∪ t) ∩ ball` 可测；由
`Disjoint.inter` 得 `(s ∩ ball) ⊥ (t ∩ ball)`；`RADIAL_UNION`
（ConformingAuto3.lean:588）得 `(s ∪ t) ∩ ball` 径向；再用 `sol_spec`
把三个 `sol` 都写成 `3 * volume.real (· ∩ ball) / r ^ 3`，由
`Measure.real` 的可加性（`measure_union`）与 `ring` 收口。

候选已有引理：
- `RADIAL_UNION`（Kepler/Text/ConformingAuto3.lean:588）
- `sol_spec`（Kepler/Geom/Volume.lean:171）
- `MeasurableSet.union`
  （Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:163）
- `Disjoint.inter`、`Set.disjoint_iff_inter_eq_empty`（Mathlib）
- 缺口：HOL `MEASURE_DISJOINT_UNION` 的 `volume.real` 版本未移植 -/
theorem SOL_DISJOINT_UNION (x : V3) (s t : Set V3) (r : ℝ)
    (hr : r > 0)
    (hms : MeasurableSet (s ∩ Metric.ball x r))
    (hmt : MeasurableSet (t ∩ Metric.ball x r))
    (hdisj : Disjoint s t)
    (hrs : radialNorm r x (s ∩ Metric.ball x r))
    (hrt : radialNorm r x (t ∩ Metric.ball x r)) :
    sol x (s ∪ t) = sol x s + sol x t := by
  have hunion : (s ∪ t) ∩ Metric.ball x r =
      (s ∩ Metric.ball x r) ∪ (t ∩ Metric.ball x r) :=
    Set.union_inter_distrib_right s t (Metric.ball x r)
  have hmunion : MeasurableSet ((s ∪ t) ∩ Metric.ball x r) := by
    rw [hunion]
    exact hms.union hmt
  have hrunion : radialNorm r x ((s ∪ t) ∩ Metric.ball x r) := by
    rw [hunion]
    refine ⟨Set.union_subset hrs.1 hrt.1, ?_⟩
    intro u hu t' ht' htu
    rcases hu with hu | hu
    · exact Or.inl (hrs.2 u hu t' ht' htu)
    · exact Or.inr (hrt.2 u hu t' ht' htu)
  have hdisj_ball : Disjoint (s ∩ Metric.ball x r) (t ∩ Metric.ball x r) :=
    hdisj.mono Set.inter_subset_left Set.inter_subset_left
  rw [sol_spec hr hmunion hrunion, sol_spec hr hms hrs, sol_spec hr hmt hrt,
    hunion, measureReal_union hdisj_ball hmt]
  ring

/-! ## 有限并上的 `sol`（Conforming.hl:1170-1226） -/

/-- 有限族的径向性（HOL `RADIAL_UNIONS`，Conforming.hl:864-874）：
若有限集 `s` 中每个集合都径向，则 `⋃₀ s` 径向。 -/
private theorem radialNorm_sUnion (r : ℝ) (x : V3) (s : Set (Set V3))
    (hs : s.Finite) (h : ∀ t ∈ s, radialNorm r x t) :
    radialNorm r x (⋃₀ s) := by
  refine Set.Finite.induction_on
    (motive := fun s _ => (∀ t ∈ s, radialNorm r x t) → radialNorm r x (⋃₀ s))
    s hs ?_ ?_ h
  · intro _
    rw [Set.sUnion_empty]
    exact ⟨Set.empty_subset _, fun u hu =>
      (Set.notMem_empty (x := x + u) hu).elim⟩
  · intro a s _ _ ih hins
    rw [Set.sUnion_insert]
    have ha : radialNorm r x a := hins a (Set.mem_insert a s)
    have hs' : radialNorm r x (⋃₀ s) :=
      ih fun t ht => hins t (Set.mem_insert_of_mem a ht)
    refine ⟨Set.union_subset ha.1 hs'.1, ?_⟩
    intro u hu t ht htu
    rcases hu with hu | hu
    · exact Or.inl (ha.2 u hu t ht htu)
    · exact Or.inr (hs'.2 u hu t ht htu)

/-- HOL Conforming.hl :1170-1226 `SOL_UNIONS`

HOL 原文：
```
!r x f:(real^3->bool)->bool.
        FINITE f /\  r> &0 /\
        (!s. s IN f  ==> measurable (s INTER normball x r) /\ radial_norm r x (s INTER normball x r)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> sol x (UNIONS f) = sum f (\s. sol x s)
```

编码说明：`FINITE f` ↔ `f.Finite`；`UNIONS f` ↔ `⋃₀ f`；
`sum f (\s. sol x s)` ↔ `∑ᶠ s ∈ f, sol x s`；`measurable` ↔
`MeasurableSet`；`radial_norm` ↔ `radialNorm`；`DISJOINT` ↔ `Disjoint`。

证明思路：对有限集 `f` 作 `Set.Finite.induction_on`（HOL
`FINITE_INDUCT_STRONG`）。空集用 `SOL_EMPTY`（本文件上文）与
`finsum_empty`；插入 `x'` 时 `⋃₀ insert x' f = x' ∪ ⋃₀ f`，用
`SOL_DISJOINT_UNION`（本文件上文）配合 `RADIAL_UNIONS`
（ConformingAuto4.lean:123）、`Set.Finite.measurableSet_sUnion`
（替代 HOL `MEASURABLE_UNIONS`）以及 `UNIONS_INTER1` 的 Mathlib 版本
（`Set.iUnion_inter`/`Set.sUnion_eq_iUnion`）证前件，再用归纳假设与
`Finset.sum_insert`/finsum 插入公式收口。

候选已有引理：
- `SOL_EMPTY`（本文件上文，HOL :1085）
- `SOL_DISJOINT_UNION`（本文件上文，HOL :1093）
- `RADIAL_UNIONS`（Kepler/Text/ConformingAuto4.lean:123）
- `Set.Finite.induction_on`
  （Mathlib/Data/Set/Finite/Basic.lean:716）
- `Set.Finite.measurableSet_sUnion`
  （Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:132）
- 缺口：finsum 的插入/空集引理（`finsum_empty`、`finsum_insert`）需
  自行拼装；HOL `RADIAL_UNIONS` 的 `{y | ?s. s IN f ∧ y = …}` 形式 -/
theorem SOL_UNIONS (r : ℝ) (x : V3) (f : Set (Set V3))
    (hfin : f.Finite)
    (hr : r > 0)
    (hmeas_rad : ∀ s ∈ f, MeasurableSet (s ∩ Metric.ball x r) ∧
      radialNorm r x (s ∩ Metric.ball x r))
    (hdisj : ∀ s ∈ f, ∀ t ∈ f, s ≠ t → Disjoint s t) :
    sol x (⋃₀ f) = ∑ᶠ s ∈ f, sol x s := by
  refine Set.Finite.induction_on
    (motive := fun s _ =>
      (∀ t ∈ s, MeasurableSet (t ∩ Metric.ball x r) ∧
        radialNorm r x (t ∩ Metric.ball x r)) →
      (∀ t ∈ s, ∀ u ∈ s, t ≠ u → Disjoint t u) →
      sol x (⋃₀ s) = ∑ᶠ t ∈ s, sol x t)
    f hfin ?_ ?_ hmeas_rad hdisj
  · intro _ _
    rw [Set.sUnion_empty, SOL_EMPTY, finsum_mem_empty]
  · intro a s has hs ih hmeas hdisj
    have ha : MeasurableSet (a ∩ Metric.ball x r) ∧
        radialNorm r x (a ∩ Metric.ball x r) :=
      hmeas a (Set.mem_insert a s)
    have hs_meas : ∀ t ∈ s, MeasurableSet (t ∩ Metric.ball x r) ∧
        radialNorm r x (t ∩ Metric.ball x r) :=
      fun t ht => hmeas t (Set.mem_insert_of_mem a ht)
    have hs_disj : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → Disjoint t u :=
      fun t ht u hu htu =>
        hdisj t (Set.mem_insert_of_mem a ht) u (Set.mem_insert_of_mem a hu) htu
    have ihs : sol x (⋃₀ s) = ∑ᶠ t ∈ s, sol x t := ih hs_meas hs_disj
    have hsUnion_eq : (⋃₀ s) ∩ Metric.ball x r =
        ⋃₀ ((fun t => t ∩ Metric.ball x r) '' s) := by
      rw [Set.sUnion_image, Set.sUnion_eq_biUnion, Set.iUnion₂_inter]
    have hsUnion_meas : MeasurableSet ((⋃₀ s) ∩ Metric.ball x r) := by
      rw [hsUnion_eq]
      exact Set.Finite.measurableSet_sUnion (hs.image _) fun u hu => by
        rcases hu with ⟨t, ht, rfl⟩
        exact (hs_meas t ht).1
    have hsUnion_rad : radialNorm r x ((⋃₀ s) ∩ Metric.ball x r) := by
      rw [hsUnion_eq]
      exact radialNorm_sUnion r x ((fun t => t ∩ Metric.ball x r) '' s)
        (hs.image _) fun u hu => by
          rcases hu with ⟨t, ht, rfl⟩
          exact (hs_meas t ht).2
    have hdisj_a : Disjoint a (⋃₀ s) := by
      rw [Set.disjoint_sUnion_right]
      intro t ht
      refine hdisj a (Set.mem_insert a s) t (Set.mem_insert_of_mem a ht) ?_
      rintro rfl
      exact has ht
    have hsol_union : sol x (a ∪ ⋃₀ s) = sol x a + sol x (⋃₀ s) :=
      SOL_DISJOINT_UNION x a (⋃₀ s) r hr ha.1 hsUnion_meas hdisj_a ha.2 hsUnion_rad
    rw [Set.sUnion_insert, hsol_union, ihs,
      finsum_mem_insert (fun t => sol x t) has hs]

/-! ## 有界性与 `aff_gt` 的开性（Conforming.hl:1227-1262） -/

/-- HOL Conforming.hl :1227-1237 `BOUNDED_INTER_BALL`

HOL 原文：
```
!x:real^3 V E.
FAN(x,V,E) /\ conforming_fan (x,V,E)
==>(!f. f IN topological_component_yfan (x,V,E)
          ==> bounded (f INTER normball x r))
```

编码说明（缺口）：HOL 原文中 `r` 为自由变量（隐式全称量化），Lean 侧
显式写作参数 `(r : ℝ)`。`bounded` ↔ `Bornology.IsBounded`（仓库约定，
cf. Kepler/Text/TopologyFan.lean:2764）；`normball x r` ↔
`Metric.ball x r`；`INTER` ↔ `∩`；`FAN`/`conforming_fan`/`yfan` 同前。

证明思路：对任意 `f ∈ topologicalComponentYfan`，用
`Bornology.IsBounded.subset` 取超集 `Metric.ball x r`：先由
`Set.inter_subset_right` 得 `f ∩ ball x r ⊆ ball x r`，再由
`Metric.isBounded_ball` 得球有界。（HOL 用 `BOUNDED_SUBSET` +
`BOUNDED_BALL` + `ball_eq_normball`。）

候选已有引理：
- `Bornology.IsBounded.subset`
  （Mathlib/Topology/Bornology/Basic.lean:163）
- `Metric.isBounded_ball`
  （Mathlib/Topology/MetricSpace/Bounded.lean:79）
- `Set.inter_subset_right`（Mathlib/Data/Set/Basic.lean）
- 缺口：无 -/
theorem BOUNDED_INTER_BALL (x : V3) (V : Set V3) (E : Set (Set V3)) (r : ℝ)
    (hfan : FAN x V E)
    (hconf : conformingFan x V E hfan) :
    ∀ f ∈ topologicalComponentYfan x V E,
      Bornology.IsBounded (f ∩ Metric.ball x r) := by
  sorry

/-- HOL Conforming.hl :1238-1262 `OPEN_AFF_GT_3_1`

HOL 原文：
```
!x v u w:real^3.
                            (~coplanar {x,v,u,w}) ==> open (aff_gt {x,v,u} {w})
```

编码说明：`coplanar` ↔ `Coplanar`（Kepler/Geom/Coplanar.lean:23）；
`open` ↔ `IsOpen`；`aff_gt` ↔ `affGt`（Kepler/Geom/Aff.lean:39）。HOL
证明先对 `x` 作 `GEOM_ORIGIN_TAC`，再把 `{x,v,u,w}` 重排，分
`(v×u)·w` 正负两种情形用 `aff_gt_3_1_rep_cross_dot` 化为严格半空间。

证明思路：由 `coplanar_cross_dot`（PlanarityAuto12.lean:573）得
`(v×u)·w ≠ 0`，分正负：正时用 `aff_gt_3_1_rep_cross_dot`
（PlanarityAuto12.lean:723）把 `affGt {x,v,u} {w}` 写成
`{y | 0 < n·(y-x)}`，用 `isOpen_lt`；负时交换 `v,u` 并化归到
`{y | n·(y-x) < 0}`。本陈述与 PlanarityAuto12 的私有引理
`isOpen_affGt_3_1`（PlanarityAuto12.lean:816）逐字相同。

候选已有引理：
- `isOpen_affGt_3_1`（private，Kepler/Text/PlanarityAuto12.lean:816）
- `coplanar_cross_dot`（Kepler/Text/PlanarityAuto12.lean:573）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `isOpen_lt`（Mathlib/Topology/Order/OrderClosed.lean:587）
- 缺口：无 -/
theorem OPEN_AFF_GT_3_1 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    IsOpen (affGt ({x, v, u} : Set V3) {w}) := by
  sorry
