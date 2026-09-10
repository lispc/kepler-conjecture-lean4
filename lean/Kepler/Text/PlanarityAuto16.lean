/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18t.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18t of block 18, planarity.hl:15281-15463):
- `ball_eq_normball` (15281)            [SKIPPED: Mathlib-general, see below]
- `dartset_leads_into_fan_eventually_radial_norm` (15286)
- `measurable_dartset_leads_into3_fan` (15301)
- `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM` (15318)
- `CARD_GT1_IMP_AZIM_FAN_EQ_DIHV` (15333)
- `solid_of_dartset_leads_into_fan_triangle_fan` (15370)
- `MOZNWEH` (15443)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- `FAN` ↔ `FAN` (Kepler/Text/Fan.lean:56); `CARD (set_of_edge v V E) > 1`
  ↔ `1 < (setOfEdge v V E).ncard` (repo convention, cf.
  Kepler/Text/PlanarityDarts.lean:94); `fan80` ↔ `fan80`
  (Kepler/Text/Fan.lean:227); `sigma_fan` ↔ `sigmaFan`
  (Kepler/Text/Fan.lean:67).
- Quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y`
  ↦ `y.1`/`y.2`, `d_fan` ↦ `dartOfFan` (Fan.lean:90).
- `hypermap1_of_fanx (x,V,E)` is NOT ported; the face-set hypothesis
  `ds IN face_set(hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with `ds : Set (V3 × V3)`
  (cf. Kepler/Text/PlanarityComponent.lean:37-48, PlanarityAuto15.lean:33).
- `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); `dart_leads_into` ↔
  `dartLeadsInto` (Kepler/Text/TopologyFan.lean:4179).
- HOL `ball (x,r)` and `normball x r` both map to Mathlib
  `Metric.ball x r` (cf. PlanarityAuto15.lean:46). Consequently
  `ball_eq_normball` (`!x r. ball (x,r) = normball x r`) is a
  Mathlib-general statement already provided by Mathlib as
  `ball_eq` (the additive `to_additive` of
  `ball_eq'`, Mathlib/Analysis/Normed/Group/Basic.lean:864-865:
  `ball y ε = {x | ‖x - y‖ < ε}`). Per task instructions it is SKIPPED.
- HOL `eventually_radial` (sphere.hl:452) is NOT ported; it is inlined as
  `∃ r, 0 < r ∧ radial_norm r x (C ∩ Metric.ball x r)` with `radial_norm`
  (vol1.hl:18-23) inlined as `C' ⊆ Metric.ball x r ∧ ∀ u, x + u ∈ C' →
  ∀ t, 0 < t → t * ‖u‖ < r → x + t • u ∈ C'` (same convention as
  PlanarityAuto15.lean:673-700 for `radial_norm`).
- HOL `sol` (volume/vol1.hl:651, introduced by `new_specification` from
  `pre_def_4_3b_alt`) is NOT ported (module-map: Volume layer not started).
  It is encoded inline by its HOL specification using `Classical.epsilon`
  (the Lean analogue of HOL's `@`/`new_specification` choice): for fixed
  `x` and `C`, `sol x C` is the `s` with
  `∀ r, 0 < r → measurable (C ∩ ball x r) → radial_norm r x (C ∩ ball x r)
   → s = 3 * vol (C ∩ ball x r) / r^3`. No new named definition is added.
- HOL `dihV` (sphere.hl:377) is NOT ported; it is inlined via the ported
  `arcVFan` (Kepler/Text/TopologyFan.lean:3654, HOL `arcV`) and the HOL
  defining formula `let va = w2-w0; vb = w3-w0; vc = w1-w0;
  vap = (vc·vc)•va - (va·vc)•vc; vbp = (vc·vc)•vb - (vb·vc)•vc;
  arcV 0 vap vbp`.
- HOL `measurable` ↔ `MeasurableSet` (Mathlib); HOL `vol` ↔ `volume`.
- HOL `sum (ds) f` (set sum, HOL `sum`/`iterate`) is encoded as the
  Mathlib finite sum over a set, `∑ᶠ y ∈ ds, f y` (finsum); under
  `CARD ds = 3` the set is finite so this coincides with HOL's sum.
- `AZIM_DIVH` (used by the HOL proof of `CARD_GT1_IMP_AZIM_FAN_EQ_DIHV`)
  is NOT ported anywhere in the repo; noted per-theorem.
- This file imports `Mathlib` (in addition to the planarity chain) because
  `MeasurableSet`, `volume`, `∑ᶠ` and the Euclidean `MeasureSpace`
  instance are not reachable from `Kepler.Text.PlanarityAuto15`.
-/

import Kepler.Text.PlanarityAuto15
import Mathlib

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

/-! ## 径向性、可测性与方位角/二面角恒等式（planarity.hl:15281-15369） -/

/- HOL planarity.hl :15281-15285 `ball_eq_normball`

HOL 原文：
```
!x r.ball (x,r)= normball x r
```

编码说明（缺口）：本陈述是 Mathlib-general 的度量球刻画，Mathlib 已有
`ball_eq : ball y ε = {x | ‖x - y‖ < ε}`
（`ball_eq'` 的 `to_additive`，Mathlib/Analysis/Normed/Group/Basic.lean:864-865）。
按任务规则「Mathlib 已有则跳过」，本文件不重复陈述。

证明思路：`Set.ext` + `Metric.mem_ball` + `dist_eq_norm`（即 Mathlib
`ball_eq` 的证明）。

候选已有引理：
- `ball_eq`（Mathlib/Analysis/Normed/Group/Basic.lean:864）
- `Metric.mem_ball`、`dist_eq_norm`（Mathlib） -/

/-- HOL planarity.hl :15286-15300 `dartset_leads_into_fan_eventually_radial_norm`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
==>   eventually_radial  x ((dartset_leads_into_fan x V E ds))
```

编码说明（缺口）：HOL `eventually_radial x C`（sphere.hl:452）未移植，
就地展开为 `∃ r, 0 < r ∧ radial_norm r x (C ∩ Metric.ball x r)`，
其中 `radial_norm r x C'`（vol1.hl:18-23）展开为
`C' ⊆ Metric.ball x r ∧ ∀ u, x + u ∈ C' → ∀ t, 0 < t → t * ‖u‖ < r →
x + t • u ∈ C'`，取 `C = dartsetLeadsIntoFan x V E ds`、
`C' = C ∩ Metric.ball x r`。与 PlanarityAuto15.lean:673-700 的
`radial_norm` 内联方式一致。

证明思路：由 `dartset_leads_into_fan_radial`（本批上游，HOL :15260）
在 `r = 1` 处取 `radial_norm 1 x (C ∩ Metric.ball x 1)`，再取见证
`r = 1` 即得 `eventually_radial`；`0 < 1` 由 `norm_num` 收口。

候选已有引理：
- `dartset_leads_into_fan_radial`（Kepler/Text/PlanarityAuto15.lean:691，
  HOL `dartset_leads_into_fan_radial` :15260）
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466）
- 缺口：`eventually_radial`（sphere.hl:452）、`radial_norm`（vol1.hl:18）
  未移植（本陈述就地展开） -/
theorem dartset_leads_into_fan_eventually_radial_norm
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    ∃ r : ℝ, 0 < r ∧
      (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
        ∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
          ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
            x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r := by
  sorry

/-- HOL planarity.hl :15301-15317 `measurable_dartset_leads_into3_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds e:real.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
/\ e> &0
==>   measurable((dartset_leads_into_fan x V E ds) INTER ball (x,e))
```

编码说明：HOL `measurable` ↔ `MeasurableSet`；HOL `ball (x,e)` 用
`Metric.ball x e`（见 PlanarityAuto15.lean:46）。`INTER` ↔ `∩`。

证明思路：HOL 用 `KVQWYDL_lemma10`（HOL :15163）把 `dartsetLeadsIntoFan`
换成 `aff_gt {x} {pr2 f1, pr2 f2, pr2 f3}`，再交换 `INTER` 后用
`MEASURABLE_BALL_AFF_GT`（未移植）得可测。Lean 侧对应先用
`KVQWYDL_lemma10` + `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 归约，
再证 `affGt` 与球的交可测。

候选已有引理：
- `KVQWYDL_lemma10`（Kepler/Text/PlanarityAuto15.lean:466，HOL :15163）
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
  （Kepler/Text/PlanarityAuto15.lean:371，HOL :15114）
- `MeasurableSet`、`measurableSet_ball`（Mathlib）
- 缺口：`MEASURABLE_BALL_AFF_GT`（HOL 未在仓库移植） -/
theorem measurable_dartset_leads_into3_fan
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)} {e : ℝ}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3)
    (he : 0 < e) :
    MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x e) := by
  sorry

/-- HOL planarity.hl :15318-15332 `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y.
FAN(x,V,E)
/\ y IN d_fan(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==>
azim_fan x V E (pr2 y) (pr3 y)= azim x (pr2 y) (pr3 y) (sigma_fan x V E (pr2 y) (pr3 y))
```

编码说明：`d_fan` ↦ `dartOfFan V E`（Fan.lean:90）；二元组 dart 下
`pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；`azim_fan` ↦ `azimFan`
（Kepler/Text/TopologyFan.lean:3484，亦见 Fan.lean:177）；HOL `azim`
↦ `Kepler.Geom.azim`（Azim.lean:58）。注意 HOL `azim_fan` 的定义是
`if CARD (set_of_edge v V E) > 1 then azim x v w (sigma_fan ...) else 2π`，
在 `CARD > 1` 假设下化为 `azim ...`。

证明思路：`azimFan` 在 `1 < (setOfEdge y.1 V E).ncard` 上按定义展开，
由 `IN_D1_FAN_IMP_EDGE_FAN`（HOL :15179）得 `{y.1,y.2} ∈ E`，再经
`remark1_fan` 的分量（`edge_ne_of_fan` + `point_in_aff_ge`）与
`hcard y.1 (…)` 把条件 `1 < ncard` 消去，最后 `rfl`/`if_pos` 收口。

候选已有引理：
- `IN_D1_FAN_IMP_EDGE_FAN`（Kepler/Text/PlanarityAuto15.lean:513，
  HOL :15179）
- `dartOfFan`（Kepler/Text/Fan.lean:90）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异分量）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334，
  HOL `remark1_fan` 成员分量）
- 缺口：`remark1_fan`（fan.hl:423）未以原名移植（分量见上） -/
theorem CARD_GT1_IMP_AZIM_FAN_EQ_AZIM
    {x : V3} {V : Set V3} {E : Set (Set V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hy : y ∈ dartOfFan V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    azimFan x V E y.1 y.2 = azim x y.1 y.2 (sigmaFan x V E y.1 y.2) := by
  sorry

/-- HOL planarity.hl :15333-15369 `CARD_GT1_IMP_AZIM_FAN_EQ_DIHV`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ y IN d_fan(x,V,E)
==>
azim_fan x V E (pr2 y) (pr3 y)= dihV x (pr2 y) (pr3 y) (sigma_fan x V E (pr2 y) (pr3 y))
```

编码说明（缺口）：HOL `dihV w0 w1 w2 w3`（sphere.hl:377）未移植，就地
展开为 `let va = w2-w0; vb = w3-w0; vc = w1-w0;
vap = (vc·vc)•va - (va·vc)•vc; vbp = (vc·vc)•vb - (vb·vc)•vc;
arcV 0 vap vbp`，其中 `arcV` 用已移植的 `arcVFan`
（Kepler/Text/TopologyFan.lean:3654）。取 `w0 = x`、`w1 = y.1`、
`w2 = y.2`、`w3 = sigmaFan x V E y.1 y.2`。

证明思路：先用 `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM`（本文件上文）把
`azimFan` 换成 `azim x (pr2 y) (pr3 y) (sigma_fan …)`；由
`IN_D1_FAN_IMP_EDGE_FAN` 与 `remark1_fan` 分量得非退化，再用
`sigma_fan_in_set_of_edge` 与 `fan80` 的三点非共线条件，最后以
`AZIM_DIVH`（HOL，未移植）把 `azim` 与 `dihV` 等同。

候选已有引理：
- `CARD_GT1_IMP_AZIM_FAN_EQ_AZIM`（本文件上文，HOL :15318）
- `IN_D1_FAN_IMP_EDGE_FAN`（Kepler/Text/PlanarityAuto15.lean:513）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）
- `arcVFan`（Kepler/Text/TopologyFan.lean:3654，HOL `arcV`）
- 缺口：`dihV`（sphere.hl:377）未移植（本陈述就地展开）；
  `AZIM_DIVH`（HOL 证明所用）未移植；`sigma_fan_in_set_of_edge`
  （HOL fan.hl）未以原名移植 -/
theorem CARD_GT1_IMP_AZIM_FAN_EQ_DIHV
    {x : V3} {V : Set V3} {E : Set (Set V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hy : y ∈ dartOfFan V E) :
    azimFan x V E y.1 y.2 =
      let va := y.2 - x
      let vb := sigmaFan x V E y.1 y.2 - x
      let vc := y.1 - x
      arcVFan 0 ((vc ⬝ᵥ vc) • va - (va ⬝ᵥ vc) • vc)
                ((vc ⬝ᵥ vc) • vb - (vb ⬝ᵥ vc) • vc) := by
  sorry

/-! ## 立体角恒等式与 MOZNWEH（planarity.hl:15370-15463） -/

/-- HOL planarity.hl :15370-15442 `solid_of_dartset_leads_into_fan_triangle_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
	FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
==>    
sol  x (dartset_leads_into_fan x V E ds)= &2 * pi + sum (ds) (\y. (azim_fan x V E (pr2 y) (pr3 y))  - pi)
```

编码说明（缺口）：HOL `sol`（volume/vol1.hl:651，经 `new_specification`
由 `pre_def_4_3b_alt` 引入）未移植（module-map：Volume 层未开始）。
此处按 HOL 规格用 `Classical.epsilon` 就地编码（HOL `@`/规格选择算子的
Lean 对应）：固定 `x, C` 时 `sol x C` 取满足
`∀ r, 0 < r → MeasurableSet (C ∩ ball x r) → radial_norm r x (C ∩ ball x r)
 → s = 3 * vol (C ∩ ball x r) / r^3` 的 `s`（其中 `radial_norm` 按
vol1.hl:18-23 展开，`vol` ↔ `volume`）。不引入新的具名定义。
HOL `sum (ds) f` 用 Mathlib 集合有限和 `∑ᶠ y ∈ ds, f y`（`CARD ds = 3`
保证有限）；`&2 * pi` ↔ `2 * Real.pi`。

证明思路：HOL 由 `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1` 取
`ds = {f1,f2,f3}`，用 `SUM_UNION`/`SUM_SING` 拆成三项；由
`measurable_dartset_leads_into3_fan`、`dartset_leads_into_fan_radial`
（本批上文）与 `ball_eq_normball` 得 `sol` 规格的可测/径向前提，再用
`UNIQUE_DARTSET_LEADS_INTO1_FAN` + `KVQWYDL_lemma1` 定位
`dartsetLeadsIntoFan = aff_gt {x} {pr2 f1, pr2 f2, pr2 f3}`，接着
`CARD_GT1_IMP_AZIM_FAN_EQ_DIHV` 把每项 `azim_fan` 化为 `dihV`，最后
`VOLUME_SOLID_TRIANGLE` + `PROPERTIES_TRIANGLE_FAN` 与 `sol` 规格相减收口。

候选已有引理：
- `CARD_FACE_SET_EQ_3_FULLY_SURROUNDED_FAN1`
  （Kepler/Text/PlanarityAuto15.lean:371，HOL :15114）
- `measurable_dartset_leads_into3_fan`、`dartset_leads_into_fan_radial`
  （本文件上文 / PlanarityAuto15.lean:691）
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`
  （Kepler/Text/PlanarityComponent.lean:468）
- `KVQWYDL_lemma1`（Kepler/Text/PlanarityAuto13.lean:368）
- `PROPERTIES_TRIANGLE_FAN`（Kepler/Text/PlanarityAuto14.lean:368）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- 缺口：`sol`（vol1.hl:651）、`VOLUME_SOLID_TRIANGLE`（vol1.hl）、
  `AZIM_DIVH`、`dihV`（sphere.hl:377）未移植 -/
theorem solid_of_dartset_leads_into_fan_triangle_fan
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3) :
    Classical.epsilon (fun s : ℝ =>
      ∀ r : ℝ, 0 < r →
        MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) →
        (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
          (∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
            ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
              x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) →
        s = 3 * volume.real (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) / r ^ 3)
      = 2 * Real.pi + ∑ᶠ y ∈ ds, (azimFan x V E y.1 y.2 - Real.pi) := by
  sorry

/-- HOL planarity.hl :15443-15463 `MOZNWEH`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds e.
	FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ CARD ds=3
/\ e> &0
==>    measurable((dartset_leads_into_fan x V E ds) INTER ball (x,e))
/\ eventually_radial  x ((dartset_leads_into_fan x V E ds))
/\ sol  x (dartset_leads_into_fan x V E ds)= &2 * pi + sum (ds) (\y. (azim_fan x V E (pr2 y) (pr3 y))  - pi)
```

编码说明（缺口）：三个合取项分别内联
`measurable_dartset_leads_into3_fan`、
`dartset_leads_into_fan_eventually_radial_norm`、
`solid_of_dartset_leads_into_fan_triangle_fan`（本文件上文）的结论；
`eventually_radial`、`sol`、`sum` 的内联方式见上两条 docstring。
HOL `e` 为可测项半径，`eventually_radial` 自带存在半径。

证明思路：HOL 直接 `MESON_TAC` 三条上游定理
（`solid_of_dartset_leads_into_fan_triangle_fan`、
`measurable_dartset_leads_into3_fan`、
`dartset_leads_into_fan_eventually_radial_norm`）。Lean 侧即
`⟨measurable_dartset_leads_into3_fan … he, ‹eventually_radial›,
 ‹sol 等式›⟩` 三项组装。

候选已有引理：
- `solid_of_dartset_leads_into_fan_triangle_fan`（本文件上文）
- `measurable_dartset_leads_into3_fan`（本文件上文）
- `dartset_leads_into_fan_eventually_radial_norm`（本文件上文） -/
theorem MOZNWEH
    {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)} {e : ℝ}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : ds.ncard = 3)
    (he : 0 < e) :
    MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x e) ∧
      (∃ r : ℝ, 0 < r ∧
        (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
          ∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
            ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
              x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ∧
      Classical.epsilon (fun s : ℝ =>
        ∀ r : ℝ, 0 < r →
          MeasurableSet (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) →
          (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) ⊆ Metric.ball x r ∧
            (∀ u : V3, x + u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r →
              ∀ t : ℝ, 0 < t → t * ‖u‖ < r →
                x + t • u ∈ dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) →
          s = 3 * volume.real (dartsetLeadsIntoFan x V E ds ∩ Metric.ball x r) / r ^ 3)
        = 2 * Real.pi + ∑ᶠ y ∈ ds, (azimFan x V E y.1 y.2 - Real.pi) := by
  sorry

end Kepler.Text
