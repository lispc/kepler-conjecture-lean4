/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18g.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18g of block 18, planarity.hl:10807-11106): the
connected-component / dartset-leads-into layer
- `CONNECTED_COMPONENT_OF_SUBSET` (10807) — SKIPPED, see below
- `connected_component_of_faces_fan` (10812)
- `dart_leads_into1` / `dartset_leads_into` defs (10915/10921) — already
  ported as `dartLeadsInto1` / `dartsetLeadsInto`
  (Kepler/Text/Fan.lean:204/210)
- `dartset_leads_into_fan` def (10978) — ported below as
  `dartsetLeadsIntoFan` (required by 7 of the statements)
- `exists_dartset_leads_into_fan` (10927)
- `DARTSET_LEADS_INTO_FAN` (10984)
- `UNIQUE_DARTSET_LEADS_INTO_FAN` (11006)
- `equality_dart_leads_into` (11028)
- `UNIQUE_DARTSET_LEADS_INTO1_FAN` (11043)
- `exists_point_dart_leads_into_fan` (11059)
- `dartset_leads_into_is_topological_component_yfan` (11081)
- `dartset_leads_into_subset_yfan` (11094)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings)
designed by glm-5.3, proofs filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- `CONNECTED_COMPONENT_OF_SUBSET` (10807) is Mathlib-general and SKIPPED:
  HOL `connected_component s x y` ↔ `x ∈ connectedComponentIn s y`
  (Kepler/Text/TopologyFan.lean:4088 convention), and the statement is
  exactly `connectedComponentIn_mono`
  (Mathlib/Topology/Connected/Basic.lean:635). Similarly HOL
  `CONNECTED_COMPONENT_SUBSET` ↔ `connectedComponentIn_subset`
  (Mathlib/Topology/Connected/Basic.lean:529).
- HOL `hypermap1_of_fanx (x,V,E)` (quadruple-dart hypermap on `d1_fan`) is
  NOT ported. Closest encoding: the pair-dart fan hypermap
  `hypermapOfFan x V E hfan : Hypermap (V3 × V3)`
  (Kepler/Text/Fan.lean:1169, darts = `dart1OfFan V E`). The two hypermaps
  are canonically isomorphic via contraction
  `contractedDart (y0,v,u,w1) = (v,u)` (Kepler/Text/Fan.lean:104, HOL
  `contracted_dart`) / `extendedDart` (Kepler/Text/Fan.lean:99), and face
  sets correspond under it; every theorem in this slice only uses the
  contracted dart of each element. Hence `ds IN face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with `ds : Set (V3 × V3)`,
  and `pr2 y, pr3 y` as `y.1, y.2`.
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, e.g. Kepler/Text/PlanarityAngle.lean:821).
- HOL `dart_leads_into x V E v u` ↔ `dartLeadsInto x V E v u`
  (Kepler/Text/TopologyFan.lean:4179, ε-选择算子 via `Classical.epsilon`).
- Not yet ported proof dependencies (needed by the worker pool; pair-dart
  analogues must be developed): `FACE_FAN_NOT_EMPTY` (fan.hl:2376),
  `properties_of_elements_in_face_fully_surroundedfan` (fan.hl:2857),
  `hypermap_of_fan_rep` (fan.hl:2780), `id_power_enf_fan` (fan.hl:2651),
  `into_domain_power_efn_fan` (fan.hl:2694),
  `into_domain1_power_efn_fan` (fan.hl:2726),
  `properties_of_f1_fan` (fan.hl:2797).
-/

import Kepler.Text.PlanarityAngle

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 面上 dart_leads_into 的一致性（planarity.hl:10812-10976） -/

/-- HOL planarity.hl :10812-10913 `connected_component_of_faces_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==>
dart_leads_into x V E v u = dart_leads_into x V E u w
```

证明思路：对 (v,u) 与 (u,w) 各用 `exists_leads_into_fan` 得阈值刻画；
取 h00 = min h' (π/2)/2、h1 = min (min h'' h''') h'''' /2、h2 = min h (π/2)/2，
由 `exists_rw_dart_inter_aff_gt1_fan`（dart (v,u) 侧）与
`exists_rw_dart_inter_aff_gt_fan`（dart (u,w) 侧）取公共弦带
`aff_gt {x} {v, (1-h1)•u + h1•w}` 内的交点 y、y'；
`aff_gt` 凸（HOL CONVEX_AFF_GT）故连通，y、y' 同属其一个连通分量，
又 `fan_run_in_small_is_subset_yfan` 保证该 aff_gt（小 h1 时）⊆ yfan，
经 `connectedComponentIn_mono`（= HOL CONNECTED_COMPONENT_OF_SUBSET，
10807，Mathlib 已有故本批不重复移植）把分量粘合，得刻画集相等 U = U'；
最后两次 `unique_dart_leads_into` 收口。

候选已有引理：
- `exists_leads_into_fan`（Kepler/Text/TopologyFan.lean:4191）
- `unique_dart_leads_into`（Kepler/Text/TopologyFan.lean:4244）
- `exists_rw_dart_inter_aff_gt_fan`（Kepler/Text/PlanarityAngle.lean:817）
- `exists_rw_dart_inter_aff_gt1_fan`（Kepler/Text/PlanarityAngle.lean:2173）
- `fan_run_in_small_is_subset_yfan`（Kepler/Text/Planarity.lean:2588）
- `connectedComponentIn_mono`（Mathlib/Topology/Connected/Basic.lean:635） -/
theorem connected_component_of_faces_fan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    dartLeadsInto x V E v u = dartLeadsInto x V E u w := by
  sorry

/-- HOL planarity.hl :10927-10976 `exists_dartset_leads_into_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
?s:real^3->bool. !y. y IN ds==> s= dart_leads_into x V E (pr2 y) (pr3 y)
```

编码说明：`ds IN face_set(hypermap1_of_fanx (x,V,E))` 用二元组 dart 超图
编码为 `ds ∈ (hypermapOfFan x V E hfan).faceSet`（见文件头）；`pr2 y`/`pr3 y`
↦ `y.1`/`y.2`（收缩 `contractedDart`，Kepler/Text/Fan.lean:104）。

证明思路：由 `face_representation` 取 dart x' 使 ds 为 faceMap 轨道
（二元组版即 `fFanPair` 迭代轨道）；见证取
`s := dartLeadsInto x V E x'.1 x'.2`，沿轨道归纳：每步
d ↦ fFanPair d = (d.2, inverseSigmaFan x V E d.2 d.1)，边链与 σ 关系
（HOL 的 `properties_of_f1_fan` / `into_domain_power_efn_fan` 的二元组
替代品）使 `connected_component_of_faces_fan` 把 dart_leads_into 相等性
从 x' 传递到轨道上每个 y。

候选已有引理：
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `connected_component_of_faces_fan`（本文件上文）
- `fFanPair`（Kepler/Text/Fan.lean:118）、`inverseSigmaFan`
  （Kepler/Text/Fan.lean:79）、`sigma_fan_in_setOfEdge`
  （Kepler/Text/Fan.lean:326）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169） -/
theorem exists_dartset_leads_into_fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∃ s : Set V3, ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2 := by
  sorry

/-! ## dartset_leads_into_fan 的 ε-定义与其刻画（planarity.hl:10978-11106） -/

/-- HOL planarity.hl :10978-10981 定义 `dartset_leads_into_fan`（原样移植，
非新发明；HOL `@s` 选择算子 ↔ `Classical.epsilon`，同
Kepler/Text/Fan.lean:210 的 `dartsetLeadsInto` 风格）。

HOL 原文：
```
dartset_leads_into_fan x V E ds =
    @s. (!y. (y IN ds) ==> (s = dart_leads_into x V E (pr2 y) (pr3 y)))
```

编码说明：dart 采用二元组（见文件头），故 `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；
`dart_leads_into` ↦ `dartLeadsInto`（Kepler/Text/TopologyFan.lean:4179）。 -/
noncomputable def dartsetLeadsIntoFan (x : V3) (V : Set V3) (E : Set (Set V3))
    (ds : Set (V3 × V3)) : Set V3 :=
  Classical.epsilon (fun s => ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2)

/-- HOL planarity.hl :10984-11004 `DARTSET_LEADS_INTO_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
(!y. y IN ds==> dartset_leads_into_fan x V E ds= dart_leads_into x V E (pr2 y) (pr3 y))
```

证明思路：`dartsetLeadsIntoFan` 是性质
`P s := ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2` 的 ε-选择；
`exists_dartset_leads_into_fan` 给出满足者 s，用
`Classical.epsilon_spec` 直接把刻画搬到 ε-值上（对应 HOL 的
ONCE_REWRITE + SELECT_ELIM）。

候选已有引理：
- `exists_dartset_leads_into_fan`（本文件上文）
- `Classical.epsilon_spec`（Mathlib/Classical.lean）
- `dartLeadsInto_spec` 的同型用法（Kepler/Text/TopologyFan.lean:4233） -/
theorem DARTSET_LEADS_INTO_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∀ y ∈ ds, dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E y.1 y.2 := by
  sorry

/-- HOL planarity.hl :11006-11026 `UNIQUE_DARTSET_LEADS_INTO_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds s.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ (!y. y IN ds==> s= dart_leads_into x V E (pr2 y) (pr3 y))
==> dartset_leads_into_fan x V E ds= s
```

证明思路：面非空（HOL `FACE_FAN_NOT_EMPTY` fan.hl:2376 未移植；二元组
编码下用 `face_representation` + `mem_orbitMap_self` 即得 ds ≠ ∅），
取 y ∈ ds，由 `DARTSET_LEADS_INTO_FAN` 得
dartsetLeadsIntoFan ds = dartLeadsInto y，再与假设 hs 在 y 处相等。

候选已有引理：
- `DARTSET_LEADS_INTO_FAN`（本文件上文）
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `mem_orbitMap_self`（Kepler/Text/Hypermap.lean:713） -/
theorem UNIQUE_DARTSET_LEADS_INTO_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} (s : Set V3)
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hs : ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2) :
    dartsetLeadsIntoFan x V E ds = s := by
  sorry

/-- HOL planarity.hl :11028-11041 `equality_dart_leads_into`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y y1.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ y IN ds /\ y1 IN ds

==>dart_leads_into x V E (pr2 y) (pr3 y)= dart_leads_into x V E (pr2 y1) (pr3 y1)
```

证明思路：`exists_dartset_leads_into_fan` 给出公共 s，
在 y 与 y1 两处实例化即得两端都等于 s。

候选已有引理：
- `exists_dartset_leads_into_fan`（本文件上文） -/
theorem equality_dart_leads_into {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {y y1 : V3 × V3}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds) (hy1 : y1 ∈ ds) :
    dartLeadsInto x V E y.1 y.2 = dartLeadsInto x V E y1.1 y1.2 := by
  sorry

/-- HOL planarity.hl :11043-11057 `UNIQUE_DARTSET_LEADS_INTO1_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds s y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ y IN ds /\ s= dart_leads_into x V E (pr2 y) (pr3 y)
==> dartset_leads_into_fan x V E ds= s
```

证明思路：先用 `equality_dart_leads_into` 把假设强化为
`∀ y' ∈ ds, s = dartLeadsInto y'`，再套
`UNIQUE_DARTSET_LEADS_INTO_FAN`。

候选已有引理：
- `equality_dart_leads_into`、`UNIQUE_DARTSET_LEADS_INTO_FAN`
  （本文件上文） -/
theorem UNIQUE_DARTSET_LEADS_INTO1_FAN {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y : V3 × V3} (s : Set V3)
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds) (hs : s = dartLeadsInto x V E y.1 y.2) :
    dartsetLeadsIntoFan x V E ds = s := by
  sorry

/-- HOL planarity.hl :11059-11079 `exists_point_dart_leads_into_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> ?y. y IN ds /\ dartset_leads_into_fan x V E ds =dart_leads_into x V E (pr2 y) (pr3 y)
```

证明思路：面非空取 y ∈ ds（同上，`face_representation` +
`mem_orbitMap_self` 替代未移植的 `FACE_FAN_NOT_EMPTY`），对
s := dartLeadsInto x V E y.1 y.2 用 `UNIQUE_DARTSET_LEADS_INTO1_FAN`。

候选已有引理：
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`（本文件上文）
- `face_representation`（Kepler/Text/Hypermap.lean:2794）
- `mem_orbitMap_self`（Kepler/Text/Hypermap.lean:713） -/
theorem exists_point_dart_leads_into_fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∃ y ∈ ds, dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E y.1 y.2 := by
  sorry

/-- HOL planarity.hl :11081-11092 `dartset_leads_into_is_topological_component_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> dartset_leads_into_fan x V E ds IN topological_component_yfan (x,V,E)
```

证明思路：`exists_point_dart_leads_into_fan` 取 y ∈ ds 使
dartsetLeadsIntoFan ds = dartLeadsInto y；y ∈ 轨道 ⊆ darts =
dart1OfFan 给 {y.1, y.2} ∈ E（替代未移植的
`properties_of_elements_in_face_fully_surroundedfan` fan.hl:2857），
再用 `dart_leads_into_mem_topologicalComponentYfan`
（HOL 名 `dart_leads_into_fan_in_topological_component_yfan`）。

候选已有引理：
- `exists_point_dart_leads_into_fan`（本文件上文）
- `dart_leads_into_mem_topologicalComponentYfan`
  （Kepler/Text/TopologyFan.lean:4280）
- `orbitMap_subset_of_permutesOn`（Kepler/Text/Hypermap.lean:721）、
  `dart1OfFan`（Kepler/Text/Fan.lean:86） -/
theorem dartset_leads_into_is_topological_component_yfan {x : V3}
    {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E := by
  sorry

/-- HOL planarity.hl :11094-11106 `dartset_leads_into_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds:real^3#real^3#real^3#real^3->bool.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
dartset_leads_into_fan x V E ds SUBSET yfan (x,V,E)
```

证明思路：展开 `topologicalComponentYfan`（Fan.lean:199），由
`dartset_leads_into_is_topological_component_yfan` 得
dartsetLeadsIntoFan ds = connectedComponentIn (yfan x V E) b（b ∈ yfan），
再用 `connectedComponentIn_subset`（= HOL CONNECTED_COMPONENT_SUBSET）
得 ⊆ yfan x V E。

候选已有引理：
- `dartset_leads_into_is_topological_component_yfan`（本文件上文）
- `connectedComponentIn_subset`
  （Mathlib/Topology/Connected/Basic.lean:529） -/
theorem dartset_leads_into_subset_yfan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    dartsetLeadsIntoFan x V E ds ⊆ yfan x V E := by
  sorry

end Kepler.Text
