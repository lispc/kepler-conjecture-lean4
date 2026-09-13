/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level definitions
(Fan chapter, `Conforming.hl:20-62`).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage: the seven top-level `new_definition`s of `Conforming.hl`
- `conforming_bijection_fan` (20)    ↦ `conformingBijectionFan`
- `conforming_half_space_fan` (25)   ↦ `conformingHalfSpaceFan`
- `conforming_solid_angle_fan` (31)  ↦ `conformingSolidAngleFan`
- `conforming_diagonal_fan` (37)     ↦ `conformingDiagonalFan`
- `conforming_fan` (43)              ↦ `conformingFan`
- `N_FAN` (50)                       ↦ `nFan`
- `minimally_nonconforming_fan` (52) ↦ `minimallyNonconformingFan`
plus the auxiliary `f1_fan` (fan/fan.hl:2063) ↦ `f1Fan`, needed by the
half-space and diagonal predicates.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean, `face_set (hypermap1_of_fanx ...)`
  is encoded as `(hypermapOfFan x V E hfan).faceSet` with pair darts,
  where `hypermapOfFan` (Kepler/Text/Fan.lean:1169) requires a
  `hfan : FAN x V E` witness. Consequently every top-level definition
  below carries an explicit `hfan : FAN x V E` argument (same convention
  as Kepler/Text/PlanarityAuto15/16.lean). This is the only deviation
  from the HOL signatures (HOL's `hypermap_of_fan` is total).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348).
- HOL `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199).
- HOL `azim_fan` ↔ `azimFan` (Kepler/Text/Fan.lean:177); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `set_of_edge` ↔ `setOfEdge`
  (Kepler/Text/Fan.lean:62); `CARD (set_of_edge v V E) > 1` ↔
  `1 < (setOfEdge v V E).ncard`.
- HOL `INTERS {g y | y IN f}` ↔ `⋂ y ∈ f, g y` (`Set.iInter`).
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL `collinear` ↔
  `Collinear3` (Kepler/Geom/Azim.lean:43).
- HOL `measurable` ↔ `MeasurableSet`; HOL `ball (x,r)` ↔
  `Metric.ball x r`; HOL `&2 * pi` ↔ `2 * Real.pi`; HOL
  `eventually_radial` ↔ `EventuallyRadial` (Kepler/Geom/Volume.lean:32);
  HOL `sol` ↔ `sol` (Kepler/Geom/Volume.lean:36).
- HOL `sum (f) g` (set sum) ↔ `∑ᶠ y ∈ f, g y` (finsum); HOL
  `nsum (face_set ...) (\f. CARD f - 3)` ↔ `∑ᶠ f ∈ ..., (f.ncard - 3)`.
- HOL `f1_fan` is not ported elsewhere; defined below as `f1Fan` from
  `fan/fan.hl:2063` using the ported `inverse1SigmaFan`
  (Kepler/Text/Fan.lean:240). Under the pair-dart encoding,
  `f1_fan x V E (v,w) = (w, inverse1_sigma_fan x V E w v)`.
-/

import Kepler.Text.PlanarityComponent
import Kepler.Geom.Volume
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

/-! ## `f1_fan`（fan/fan.hl:2063） -/

/-- HOL fan/fan.hl:2063 `f1_fan`：

```
f1_fan (x,V,E) =
  (\((x,v,w,w1)). (x, w, inverse1_sigma_fan x V E w v, v))
```

编码说明：4 元组 dart 用点对 `V3 × V3` 表示，`pr2 y`/`pr3 y` ↦
`y.1`/`y.2`；`inverse1_sigma_fan` ↦ `inverse1SigmaFan`
（Kepler/Text/Fan.lean:240）。故 `f1_fan x V E (v,w) =
(w, inverse1_sigma_fan x V E w v)`。 -/
noncomputable def f1Fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (d : V3 × V3) : V3 × V3 :=
  (d.2, inverse1SigmaFan x V E d.2 d.1)

/-! ## 四个 conforming 子谓词（Conforming.hl:20-41） -/

/-- HOL Conforming.hl:20 `conforming_bijection_fan`：

```
conforming_bijection_fan (x,V,E) <=>
  !s. s IN topological_component_yfan (x,V,E) ==>
      (?!f. f IN face_set (hypermap1_of_fanx (x,V,E)) /\
             s = dartset_leads_into_fan x V E f)
```

编码说明：`?!f. P f`（唯一存在）↦ `∃! f, P f`；`hypermap1_of_fanx`
↦ `hypermapOfFan x V E hfan`（需显式 `hfan`，见文件头）。 -/
def conformingBijectionFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : Prop :=
  ∀ s ∈ topologicalComponentYfan x V E,
    ∃! f, f ∈ (hypermapOfFan x V E hfan).faceSet ∧
      s = dartsetLeadsIntoFan x V E f

/-- HOL Conforming.hl:25 `conforming_half_space_fan`：

```
conforming_half_space_fan (x,V,E) <=>
  !f. f IN face_set (hypermap1_of_fanx (x,V,E)) ==>
      dartset_leads_into_fan x V E f =
        INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y)} | y IN f}
```

编码说明：`INTERS {g y | y IN f}` ↦ `⋂ y ∈ f, g y`；`pr3 (f1_fan x V E y)`
↦ `(f1Fan x V E y).2`。 -/
def conformingHalfSpaceFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : Prop :=
  ∀ f ∈ (hypermapOfFan x V E hfan).faceSet,
    dartsetLeadsIntoFan x V E f =
      ⋂ y ∈ f, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}

/-- HOL Conforming.hl:31 `conforming_solid_angle_fan`：

```
conforming_solid_angle_fan (x,V,E) <=>
  !f. f IN face_set (hypermap1_of_fanx (x,V,E)) ==>
  (let U = dartset_leads_into_fan x V E f in
     (!r. measurable (ball (x,r) INTER U)) /\
       eventually_radial x U /\
       sol x U = &2 * pi + sum (f) (\y. (azim_fan x V E (pr2 y) (pr3 y)) - pi))
```

编码说明：HOL `let` 保留为 Lean `let`；`measurable` ↦ `MeasurableSet`；
`ball (x,r)` ↦ `Metric.ball x r`；`eventually_radial` ↦ `EventuallyRadial`；
`sum (f) g` ↦ `∑ᶠ y ∈ f, g y`。 -/
def conformingSolidAngleFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : Prop :=
  ∀ f ∈ (hypermapOfFan x V E hfan).faceSet,
    let U := dartsetLeadsIntoFan x V E f
    (∀ r : ℝ, MeasurableSet (Metric.ball x r ∩ U)) ∧
      EventuallyRadial x U ∧
      sol x U = 2 * Real.pi +
        ∑ᶠ y ∈ f, (azimFan x V E y.1 y.2 - Real.pi)

/-- HOL Conforming.hl:37 `conforming_diagonal_fan`：

```
conforming_diagonal_fan (x,V,E) <=>
  (!f y z. f IN face_set (hypermap1_of_fanx (x,V,E)) /\ y IN f /\ z IN f
           /\ ~(y = z) ==>
      ~collinear {x, pr2 y, pr2 z} /\
      ((y = f1_fan x V E z) \/ (z = f1_fan x V E y) \/
         aff_gt {x} {pr2 y, pr2 z} SUBSET (dartset_leads_into_fan x V E f)))
```

编码说明：`collinear` ↦ `Collinear3`；`pr2 y`/`pr2 z` ↦ `y.1`/`z.1`；
`f1_fan` ↦ `f1Fan`；`SUBSET` ↦ `⊆`。 -/
def conformingDiagonalFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : Prop :=
  ∀ f ∈ (hypermapOfFan x V E hfan).faceSet, ∀ y ∈ f, ∀ z ∈ f, y ≠ z →
    ¬ Collinear3 x y.1 z.1 ∧
      (y = f1Fan x V E z ∨ z = f1Fan x V E y ∨
        affGt ({x} : Set V3) {y.1, z.1} ⊆ dartsetLeadsIntoFan x V E f)

/-- HOL Conforming.hl:43 `conforming_fan`：

```
conforming_fan (x,V,E) <=>
  (!v. v IN V ==> CARD (set_of_edge v V E) > 1) /\
  fan80(x,V,E) /\
  conforming_bijection_fan (x,V,E) /\
  conforming_half_space_fan (x,V,E) /\
  conforming_solid_angle_fan (x,V,E) /\
  conforming_diagonal_fan (x,V,E)
```

编码说明：HOL 原文不含 `FAN(x,V,E)` 合取项；Lean 侧因构造
`hypermapOfFan` 需要 `hfan : FAN x V E`，故把它作为参数（见文件头）。 -/
def conformingFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : Prop :=
  (∀ v ∈ V, 1 < (setOfEdge v V E).ncard) ∧
    fan80 x V E ∧
    conformingBijectionFan x V E hfan ∧
    conformingHalfSpaceFan x V E hfan ∧
    conformingSolidAngleFan x V E hfan ∧
    conformingDiagonalFan x V E hfan

/-! ## 非 conforming 的极小性与计数（Conforming.hl:50-62） -/

/-- HOL Conforming.hl:50 `N_FAN`：

```
N_FAN (x,V,E) = nsum (face_set (hypermap1_of_fanx (x,V,E))) (\f. CARD f - 3)
```

编码说明：HOL `nsum S g`（集合上的自然数和）↦ finsum
`∑ᶠ f ∈ S, g f`；`CARD f` ↦ `f.ncard`；`hypermap1_of_fanx` ↦
`hypermapOfFan x V E hfan`。 -/
noncomputable def nFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : ℕ :=
  ∑ᶠ f ∈ (hypermapOfFan x V E hfan).faceSet, (f.ncard - 3)

/-- HOL Conforming.hl:52 `minimally_nonconforming_fan`：

```
minimally_nonconforming_fan(x,V,E) <=>
  FAN(x,V,E) /\
  (!v. v IN V ==> CARD (set_of_edge v V E) > 1) /\
  fan80(x,V,E) /\
  ~(conforming_fan (x,V,E)) /\
  (!E1. FAN(x,V,E1) /\
        (!v. v IN V ==> CARD (set_of_edge v V E1) > 1) /\
        fan80(x,V,E1) /\
        N_FAN(x,V,E1) < N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
```

编码说明：外层 `FAN(x,V,E)` 合取项保留，同时作为参数 `hfan` 传入
子谓词；内层 `!E1` 因 `conformingFan`/`nFan` 需要 `FAN x V E1` 见证，
写成 `∀ E1 (hfan1 : FAN x V E1), ...`，其合取前件中的 `FAN x V E1`
与 `hfan1` 的类型重复（保留以对齐 HOL 原文）。 -/
def minimallyNonconformingFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E) : Prop :=
  FAN x V E ∧
    (∀ v ∈ V, 1 < (setOfEdge v V E).ncard) ∧
    fan80 x V E ∧
    ¬ conformingFan x V E hfan ∧
    ∀ (E1 : Set (Set V3)) (hfan1 : FAN x V E1),
      FAN x V E1 ∧
        (∀ v ∈ V, 1 < (setOfEdge v V E1).ncard) ∧
        fan80 x V E1 ∧
        nFan x V E1 hfan1 < nFan x V E hfan →
          conformingFan x V E1 hfan1
