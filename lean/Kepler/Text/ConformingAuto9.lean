/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 9
(Conforming.hl:2101-2356).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 9, Conforming.hl:2101-2356):
- `AFF_GT_SUBSET_DART_LEADS_INTO_FAN` (2101)
- `STEP2_REDUCE_FAN` (2154)
- `STEP3_REDUCE_FAN` (2180)
- `SET_OF_EDGE_UNION_GRAPH` (2216)
- `add_edge_imp_card_set_edge_ge1_fan` (2227)
- `PR23_OF_D1_FAN` (2253)
- `PR23_OF_D20_FAN` (2279)
- `add_edge_graph` (2304)
- `expand_set_edge_fan` (2312)
- `DART_FANADD_EQ_DART_FAN_ADD_2DART` (2323)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48, `face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, with pair darts `V3 × V3`. Because
  `hypermapOfFan` requires an explicit `hfan : FAN x V E` witness (HOL's
  `hypermap_of_fan` is total), the face-set theorems below carry an extra
  explicit `(hfan : FAN x V E)` argument; this is the only deviation from
  the HOL signatures.
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`; HOL `f1_fan` ↔ `f1Fan` (ConformingDefs.lean:87);
  HOL `sigma_fan` ↔ `sigmaFan` (Fan.lean:67); HOL `fan80` ↔ `fan80`
  (Fan.lean:227).
- HOL `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179); HOL `dartset_leads_into_fan` ↔
  `dartsetLeadsIntoFan` (Kepler/Text/PlanarityComponent.lean:348); HOL
  `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39).
- HOL `pr23 = (\(x,y,z,t). (y,z))` (Conforming.hl:2249) is NOT ported.
  Under the pair-dart encoding the contracted dart already IS the pair
  `(pr2, pr3)`, so `pr23` collapses to the identity
  `(fun p : V3 × V3 => (p.1, p.2))`; every `IMAGE pr23 (...)` below is
  encoded as `Set.image (fun p : V3 × V3 => (p.1, p.2)) (...)`.
- HOL `d1_fan (x,V,E) = {(x',v,w,w1) | x'=x ∧ {v,w} IN E ∧
  w1 = sigma_fan x V E v w}` (fan.hl:952) is encoded as `dart1OfFan V E`
  (Fan.lean:86, `{d | {d.1,d.2} ∈ E}`); HOL
  `d20_fan (x,V,E) = {(x',v,v,v) | x'=x ∧ V v ∧ set_of_edge v V E = {}}`
  (fan.hl:2300) is encoded as the diagonal set
  `{p : V3 × V3 | p.1 = p.2 ∧ p.1 ∈ V ∧ setOfEdge p.1 V E = ∅}`; HOL
  `d_fan = d1_fan UNION d20_fan` (fan.hl:2302) is encoded as `dartOfFan V E`
  (Fan.lean:90). Consequently the `dart (hypermap1_of_fanx ...)` in
  `DART_FANADD_EQ_DART_FAN_ADD_2DART` is encoded as `dartOfFan V E`
  (the total pair-dart set, no `FAN` witness needed).
- HOL `IMAGE_UNION`/`IMAGE` ↔ Mathlib `Set.image_union`/`Set.image`.
- HOL `CARD ds > 3` ↔ `3 < ds.ncard`; `{f1,f2,f3} SUBSET ds` ↔
  `({f1, f2, f3} : Set (V3 × V3)) ⊆ ds`.
- `SET_OF_EDGE_UNION_GRAPH`, `add_edge_graph` and `expand_set_edge_fan` are
  pure set identities (no named Mathlib theorem packages them); the rest
  mention the repo-specific `FAN`/`dartLeadsInto`/`hypermapOfFan` vocabulary.
  Nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingAuto8
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

/-! ## aff_gt 包含于 dart_leads_into（Conforming.hl:2101-2214） -/

/-- `aff_gt_1_2` 展开后 `affGt {x} {p,q}` 是凸集（`{x}` 与 `{p,q}` 不交）。 -/
private theorem convex_affGt_pair_of_disjoint {x p q : V3}
    (hdis : Disjoint ({x} : Set V3) {p, q}) :
    Convex ℝ (affGt ({x} : Set V3) {p, q}) := by
  rw [aff_gt_1_2 hdis, convex_iff_forall_pos]
  intro y hy z hz a b ha hb hab
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hyeq⟩ := hy
  obtain ⟨s1, s2, s3, hs2, hs3, hssum, hzeq⟩ := hz
  refine ⟨a * t1 + b * s1, a * t2 + b * s2, a * t3 + b * s3,
    add_pos (mul_pos ha ht2) (mul_pos hb hs2),
    add_pos (mul_pos ha ht3) (mul_pos hb hs3), ?_, ?_⟩
  · nlinarith [hsum, hssum, hab]
  · rw [hyeq, hzeq]; module

/-- HOL Conforming.hl :2101-2152 `AFF_GT_SUBSET_DART_LEADS_INTO_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w.
FAN(x,V,E) /\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
==> aff_gt {x} {w,v} SUBSET dart_leads_into x V E u w
```

编码说明：`aff_gt` ↔ `affGt`；`dart_leads_into` ↔ `dartLeadsInto`；
`SUBSET` ↔ `⊆`；假设里被遮蔽的 `!v` 改名为 `z`。

证明思路：由 `fan80` 在 `(u,w)` 处得 `0 < azim x u w v < π`，用
`properties_fully_surrounded` 得四点不共面，`notcoplanar_disjoints` 得
`{x}` 与 `{w,v}` 不相交；由 `aff_gt_1_3_subset_dart_leads_into_fan` 与
`condition_aff_gt_subset_yfan`、`segment_subset_aff_gt_union` 取公共弦带内的
点，经 `dart_leads_into_mem_topologicalComponentYfan` 与连通分量
（`expand_element_in_topological_component_yfan`/`isPreconnected_...`）
把整条 `affGt {x} {w,v}` 收进同一分量。

候选已有引理：
- `aff_gt_1_3_subset_dart_leads_into_fan`（Kepler/Text/PlanarityAuto12.lean:270）
- `dart_leads_into_mem_topologicalComponentYfan`（Kepler/Text/TopologyFan.lean:4280，
  HOL `dart_leads_into_fan_in_topological_component_yfan`）
- `isPreconnected_of_mem_topologicalComponentYfan`（Kepler/Text/TopologyFan.lean:4315，
  HOL `in_topological_component_yfan_is_connected`）
- `expand_element_in_topological_component_yfan`（Kepler/Text/PlanarityAuto7.lean:271）
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `condition_aff_gt_subset_yfan`（Kepler/Text/ConformingAuto8.lean:629）
- `segment_subset_aff_gt_union`（Kepler/Text/ConformingAuto8.lean:674）
- `notcoplanar_4point_aff_gt_1_3_not_empty`（Kepler/Text/PlanarityAuto13.lean:323）
- `exists_in_aff_gt_disjoint`（Kepler/Text/PlanarityAuto7.lean:387）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `SEGMENT_CONNECTED`（Kepler/Text/ConformingAuto8.lean:740）
- 缺口：无 -/
theorem AFF_GT_SUBSET_DART_LEADS_INTO_FAN {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∉ E) (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt ({x} : Set V3) {w, v} ⊆ dartLeadsInto x V E u w := by
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ0 hθπ
  have hdis_wv : Disjoint ({x} : Set V3) {w, v} :=
    (notcoplanar_disjoints x v u w hcop).2.2.2.2.2.2.2
  have hsub13 : affGt ({x} : Set V3) ({v, u, w} : Set V3) ⊆
      dartLeadsInto x V E u w :=
    aff_gt_1_3_subset_dart_leads_into_fan x V E v u w hfan hvu huw hsigma hcard hfan80
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr
    (notcoplanar_4point_aff_gt_1_3_not_empty x v u w hcop)
  have hy_dl : y ∈ dartLeadsInto x V E u w := hsub13 hy
  have hU : dartLeadsInto x V E u w ∈ topologicalComponentYfan x V E :=
    dart_leads_into_mem_topologicalComponentYfan (v := u) (u := w) hfan huw
  have hsubyfan_dl : dartLeadsInto x V E u w ⊆ yfan x V E :=
    topological_component_subset_yfan hU
  have heq : dartLeadsInto x V E u w = connectedComponentIn (yfan x V E) y :=
    expand_element_in_topological_component_yfan x V E (dartLeadsInto x V E u w) y
      hfan hU hy_dl
  obtain ⟨y', hy'⟩ := exists_in_aff_gt_disjoint x w v hdis_wv
  have hsubwv_yfan : affGt ({x} : Set V3) {w, v} ⊆ yfan x V E := by
    rw [Set.pair_comm w v]
    exact condition_aff_gt_subset_yfan hfan hvu huw hsigma hcard hfan80 hwv
  have hsub13_yfan : affGt ({x} : Set V3) ({v, u, w} : Set V3) ⊆ yfan x V E :=
    fun z hz => hsubyfan_dl (hsub13 hz)
  have hseg : segment ℝ y y' ⊆
      affGt ({x} : Set V3) {w, v} ∪ affGt ({x} : Set V3) ({v, u, w} : Set V3) :=
    segment_subset_aff_gt_union (x := x) (y := y) (z := y') (v := v) (u := u) (w := w)
      hcop hy hy'
  have hseg_yfan : segment ℝ y y' ⊆ yfan x V E := by
    intro p hp
    rcases (Set.mem_union p _ _).mp (hseg hp) with hpwv | hp13
    · exact hsubwv_yfan hpwv
    · exact hsub13_yfan hp13
  have hy'_cc : y' ∈ connectedComponentIn (yfan x V E) y :=
    ((convex_segment y y').isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ y y') hseg_yfan) (right_mem_segment ℝ y y')
  have hcc_eq : connectedComponentIn (yfan x V E) y' =
      connectedComponentIn (yfan x V E) y :=
    (connectedComponentIn_eq hy'_cc).symm
  have hsub_wv_cc : affGt ({x} : Set V3) {w, v} ⊆
      connectedComponentIn (yfan x V E) y' :=
    (convex_affGt_pair_of_disjoint hdis_wv).isPreconnected.subset_connectedComponentIn
      hy' hsubwv_yfan
  rw [heq, ← hcc_eq]
  exact hsub_wv_cc

/-- HOL Conforming.hl :2154-2178 `STEP2_REDUCE_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds f1 f2 f3 v u w.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
==> aff_gt {x} {v,w} SUBSET dartset_leads_into_fan x V E ds
```

编码说明：四元组 dart ↔ `V3 × V3`，`f1 f2 f3 : V3 × V3`，
`pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；`f1_fan` ↔ `f1Fan`；`face_set` ↔
`(hypermapOfFan x V E hfan).faceSet`；`CARD ds > 3` ↔ `3 < ds.ncard`；
`{f1,f2,f3} SUBSET ds` ↔ `({f1, f2, f3} : Set (V3 × V3)) ⊆ ds`；
`dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`。

证明思路：由 `{f1,f2,f3} ⊆ ds`、`pr2 f2 = u`、`pr2 f3 = w` 得
`dartLeadsInto x V E u w = dartsetLeadsIntoFan x V E ds`
（`UNIQUE_DARTSET_LEADS_INTO1_FAN`，取 `f2` 为见证）；再把
`AFF_GT_SUBSET_DART_LEADS_INTO_FAN`（结论为 `affGt {x} {w,v} ⊆
dartLeadsInto u w`）经 `{v,w}={w,v}` 改写即得。

候选已有引理：
- `AFF_GT_SUBSET_DART_LEADS_INTO_FAN`（本文件上文）
- `UNIQUE_DARTSET_LEADS_INTO1_FAN`（Kepler/Text/PlanarityComponent.lean:468）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `dart_leads_into_mem_topologicalComponentYfan`（Kepler/Text/TopologyFan.lean:4280）
- 缺口：HOL `hypermap_of_fan_rep`、`dartset_fully_surrounded_is_non_isolated_fan`、
  `face_subset_dart_fan`、`properties_of_f1_fan` 未以该名移植
  （由 `dartOfFan_eq_dart1_of_surrounded`（Fan.lean:1084）等替代） -/
theorem STEP2_REDUCE_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {f1 f2 f3 : V3 × V3} {v u w : V3}
    (hfan : FAN x V E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) (hds3 : 3 < ds.ncard)
    (hfsub : ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds)
    (hf1 : f1Fan x V E f1 = f2) (hf2 : f1Fan x V E f2 = f3)
    (hf3 : ¬ (f1Fan x V E f3 = f1))
    (hv : f1.1 = v) (hu : f2.1 = u) (hw : f3.1 = w)
    (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E) (hwv : {w, v} ∉ E)
    (hsigma : sigmaFan x V E u w = v) :
    affGt ({x} : Set V3) {v, w} ⊆ dartsetLeadsIntoFan x V E ds := by
  sorry

/-- HOL Conforming.hl :2180-2214 `STEP3_REDUCE_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ E UNION {{v,w}}= E1
==> FAN (x,V,E1)
```

编码说明：`E1 : Set (Set V3)`，`E UNION {{v,w}} = E1` ↔
`E ∪ {({v, w} : Set V3)} = E1`；`dartset_leads_into_fan` ↔
`dartsetLeadsIntoFan`；`face_set`/`CARD ds` 同 STEP2。

证明思路：先用 `STEP2_REDUCE_FAN` 得 `affGt {x} {v,w} ⊆
dartsetLeadsIntoFan ds`；用 `remark1_fan` 的互异性分量（未移植，可由
`FAN` 的 `fan1`/`graph` 部分现场替代）得 `v ≠ w`、`v,u,w` 互异，由
`not_collinear_is_properties_fully_surrounded1` 得 `¬ Collinear3 x v w`；
最后对 `E1 = E ∪ {{v,w}}` 套 `DWWUTKW`（保持 fan1/fan2/fan6/fan7 的加边
定理）得 `FAN x V E1`。

候选已有引理：
- `STEP2_REDUCE_FAN`（本文件上文）
- `DWWUTKW`（Kepler/Text/PlanarityDarts.lean:650，加边保持 `FAN`）
- `not_collinear_is_properties_fully_surrounded1`（Kepler/Text/Planarity.lean:2508）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `add_edge_graph_fan`（Kepler/Text/PlanarityDarts.lean:120）
- 缺口：HOL `remark1_fan`（fan.hl:423）未以该名移植，需现场替代 -/
theorem STEP3_REDUCE_FAN {x : V3} {V : Set V3} {E E1 : Set (Set V3)}
    {ds : Set (V3 × V3)} {f1 f2 f3 : V3 × V3} {v u w : V3}
    (hfan : FAN x V E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) (hds3 : 3 < ds.ncard)
    (hfsub : ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds)
    (hf1 : f1Fan x V E f1 = f2) (hf2 : f1Fan x V E f2 = f3)
    (hf3 : ¬ (f1Fan x V E f3 = f1))
    (hv : f1.1 = v) (hu : f2.1 = u) (hw : f3.1 = w)
    (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E) (hwv : {w, v} ∉ E)
    (hsigma : sigmaFan x V E u w = v)
    (hE1 : E ∪ {({v, w} : Set V3)} = E1) :
    FAN x V E1 := by
  sorry

/-! ## 加边的集合论引理（Conforming.hl:2216-2316） -/

/-- HOL Conforming.hl :2216-2225 `SET_OF_EDGE_UNION_GRAPH`

HOL 原文：
```
!v V E1 E2. set_of_edge v V (E1 UNION E2)= (set_of_edge v V E1) UNION (set_of_edge v V E2)
```

编码说明：`set_of_edge` ↔ `setOfEdge`（Fan.lean:62）；`UNION` ↔ `∪`。

证明思路：`Set.ext` 后逐点展开 `setOfEdge`，把
`{v,w} ∈ E1 ∪ E2` 化为 `{v,w} ∈ E1 ∨ {v,w} ∈ E2`，两侧等价性由
`Set.mem_union` 与命题逻辑直接给出。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.mem_union`、`Set.ext`（Mathlib） -/
theorem SET_OF_EDGE_UNION_GRAPH (v : V3) (V : Set V3) (E1 E2 : Set (Set V3)) :
    setOfEdge v V (E1 ∪ E2) = setOfEdge v V E1 ∪ setOfEdge v V E2 := by
  sorry

/-- HOL Conforming.hl :2227-2247 `add_edge_imp_card_set_edge_ge1_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E1=E UNION {{v,w}}
==>
(!v. v IN V==>CARD (set_of_edge v V E1) > 1)
```

编码说明：HOL 原文的自由变量 `v,w`（不在绑定列表中）此处提升为显式
参数 `{v w : V3}`（HOL 定理的自由变量在使用时被全称量化）；
`E1 = E UNION {{v,w}}` ↔ `E1 = E ∪ {({v, w} : Set V3)}`；
`CARD (set_of_edge ...) > 1` ↔ `1 < (setOfEdge ...).ncard`。

证明思路：把 `E1` 代入并用 `SET_OF_EDGE_UNION_GRAPH` 展开为
`setOfEdge v' V E ∪ setOfEdge v' V {({v,w})}`；由 `remark_finite_fan1`
得 `setOfEdge v' V E` 有限，再用 `Set.ncard_le_ncard`（子集单调）与
`hcard v'` 得下界 `1 < ncard`。

候选已有引理：
- `SET_OF_EDGE_UNION_GRAPH`（本文件上文）
- `remark_finite_fan1`（Kepler/Text/Fan.lean:277）
- `FAN`（Kepler/Text/Fan.lean:56）、`fan1`（Kepler/Text/Fan.lean:41）
- `Set.ncard_le_ncard`、`Set.ncard_mono`（Mathlib/Data/Set/Card.lean） -/
theorem add_edge_imp_card_set_edge_ge1_fan {x : V3} {V : Set V3}
    {E E1 : Set (Set V3)} {v w : V3}
    (hfan : FAN x V E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hE1 : E1 = E ∪ {({v, w} : Set V3)}) :
    ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E1).ncard := by
  sorry

/-- HOL Conforming.hl :2253-2274 `PR23_OF_D1_FAN`

HOL 原文：
```
!x:real^3 V:real^3->bool E:(real^3->bool)->bool.
IMAGE pr23 (d1_fan(x,V,E))={ (v,w) | {v,w} IN E}
```

编码说明：`pr23 = (\(x,y,z,t). (y,z))` 未移植；在点对编码下契约 dart 已是
`(pr2,pr3)`，故 `pr23` 退化为恒等 `(fun p : V3 × V3 => (p.1, p.2))`，
`IMAGE pr23` 编码为 `Set.image (fun p : V3 × V3 => (p.1, p.2))`；
`d1_fan(x,V,E)` 编码为 `dart1OfFan V E`（Fan.lean:86），右端
`{(v,w) | {v,w} IN E}` 编码为 `{p : V3 × V3 | {p.1, p.2} ∈ E}`。

证明思路：把 `Set.image` 沿恒等函数化简为原集合
（`Set.image_id`/`funext` + `Prod.mk.eta`），此时两侧都等于
`dart1OfFan V E = {p | {p.1,p.2} ∈ E}`，由 `dart1OfFan` 的定义
`rfl` 收口。

候选已有引理：
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- `Set.image_id`（Mathlib/Data/Set/Image.lean）
- 缺口：HOL `pr23`、`d1_fan` 未以该名移植（见文件头编码说明） -/
theorem PR23_OF_D1_FAN (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Set.image (fun p : V3 × V3 => (p.1, p.2)) (dart1OfFan V E) =
      {p : V3 × V3 | {p.1, p.2} ∈ E} := by
  sorry

/-- HOL Conforming.hl :2279-2302 `PR23_OF_D20_FAN`

HOL 原文：
```
!x:real^3 V:real^3->bool E:(real^3->bool)->bool.
IMAGE pr23 (d20_fan(x,V,E))={ (v,v) | v IN V/\ set_of_edge v V E={}}
```

编码说明：`pr23` 退化为恒等（同 `PR23_OF_D1_FAN`）；
`d20_fan(x,V,E)` 编码为对角集
`{p : V3 × V3 | p.1 = p.2 ∧ p.1 ∈ V ∧ setOfEdge p.1 V E = ∅}`，
右端 `{(v,v) | v IN V ∧ set_of_edge v V E = {}}` 是同一集合。

证明思路：`Set.image` 沿恒等函数化简后两侧相同，`rfl` 或
`Set.ext`+`simp` 收口。

候选已有引理：
- `dartOfFan`（Kepler/Text/Fan.lean:90，`d_fan` 编码）
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.image_id`（Mathlib/Data/Set/Image.lean）
- 缺口：HOL `pr23`、`d20_fan` 未以该名移植（见文件头编码说明） -/
theorem PR23_OF_D20_FAN (x : V3) (V : Set V3) (E : Set (Set V3)) :
    Set.image (fun p : V3 × V3 => (p.1, p.2))
        {p : V3 × V3 | p.1 = p.2 ∧ p.1 ∈ V ∧ setOfEdge p.1 V E = ∅} =
      {p : V3 × V3 | p.1 = p.2 ∧ p.1 ∈ V ∧ setOfEdge p.1 V E = ∅} := by
  sorry

/-- HOL Conforming.hl :2304-2310 `add_edge_graph`

HOL 原文：
```
!v w E. {v',w' | {v', w'} IN E UNION {{v, w}}}= {v',w' | {v', w'} IN E} UNION {(v',w')| {v',w'}={v,w}}
```

编码说明：HOL `{v',w' | P}` 是点对集合 `{(v',w') | P}`，编码为
`{p : V3 × V3 | P[p.1,p.2]}`；`UNION` ↔ `∪`；
`{{v,w}}` ↔ `{({v, w} : Set V3)}`。

证明思路：`Set.ext` 后对 `p : V3 × V3` 逐点展开，把
`{p.1,p.2} ∈ E ∪ {{v,w}}` 化为 `{p.1,p.2} ∈ E ∨ {p.1,p.2} = {v,w}`，
与右端 `∈` 的并集定义直接对应，命题逻辑收口。

候选已有引理：
- `Set.mem_union`、`Set.mem_singleton_iff`、`Set.ext`（Mathlib）
- 注：同名 HOL 定理在 planarity.hl:11124 的对应物
  `add_edge_graph_fan`（Kepler/Text/PlanarityDarts.lean:120）是
  `⋃₀` 的保持命题，与本条不同 -/
theorem add_edge_graph (v w : V3) (E : Set (Set V3)) :
    {p : V3 × V3 | {p.1, p.2} ∈ E ∪ {({v, w} : Set V3)}} =
      {p : V3 × V3 | {p.1, p.2} ∈ E} ∪
        {p : V3 × V3 | ({p.1, p.2} : Set V3) = {v, w}} := by
  sorry

/-- HOL Conforming.hl :2312-2316 `expand_set_edge_fan`

HOL 原文：
```
!v w.{(v',w')| {v',w'}={v,w}}={(v,w), (w,v)}
```

编码说明：点对集合编码为 `Set (V3 × V3)`；`{(v,w),(w,v)}` ↔
`({(v, w), (w, v)} : Set (V3 × V3))`。

证明思路：`Set.ext` 后对 `p : V3 × V3` 展开：`{p.1,p.2} = {v,w}` 当且
仅当 `(p.1 = v ∧ p.2 = w) ∨ (p.1 = w ∧ p.2 = v)`（`Set.pair_eq_pair`
或 `Set.ext`+`simp`），右端恰是 `p = (v,w) ∨ p = (w,v)`。

候选已有引理：
- `Set.pair_comm`（Mathlib/Data/Set/Basic.lean）
- `Set.mem_insert_iff`、`Set.mem_singleton_iff`、`Set.ext`（Mathlib） -/
theorem expand_set_edge_fan (v w : V3) :
    {p : V3 × V3 | ({p.1, p.2} : Set V3) = {v, w}} =
      ({(v, w), (w, v)} : Set (V3 × V3)) := by
  sorry

/-- HOL Conforming.hl :2323-2356 `DART_FANADD_EQ_DART_FAN_ADD_2DART`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ ~(v=w)
/\ E UNION {{v,w}}=E1
==>
IMAGE pr23 (dart (hypermap1_of_fanx (x,V,E1)))

= (IMAGE pr23 (dart (hypermap1_of_fanx (x,V,E)))) UNION {(v,w),(w,v)}
```

编码说明：四元组 dart ↔ `V3 × V3`；`dart (hypermap1_of_fanx ...)` 是
`d_fan`，编码为 `dartOfFan V E`（Fan.lean:90，无需 `FAN` 见证）；
`IMAGE pr23` 退化为恒等（见文件头）；`E UNION {{v,w}} = E1` ↔
`E ∪ {({v, w} : Set V3)} = E1`；其余同 `STEP2_REDUCE_FAN`。

证明思路：由 `STEP3_REDUCE_FAN` 得 `FAN x V E1`，由
`add_edge_imp_card_set_edge_ge1_fan` 得新图的最小度条件；把
`dartOfFan V E1` 展开为 `d20 ∪ d1` 后套 `add_edge_graph`/
`expand_set_edge_fan`/`SET_OF_EDGE_UNION_GRAPH` 与
`PR23_OF_D20_FAN`/`PR23_OF_D1_FAN`，并用 `Set.image_union` 对齐两侧。

候选已有引理：
- `STEP3_REDUCE_FAN`（本文件上文）
- `add_edge_imp_card_set_edge_ge1_fan`（本文件上文）
- `add_edge_graph`（本文件上文）
- `expand_set_edge_fan`（本文件上文）
- `SET_OF_EDGE_UNION_GRAPH`（本文件上文）
- `PR23_OF_D1_FAN`、`PR23_OF_D20_FAN`（本文件上文）
- `dartOfFan`（Kepler/Text/Fan.lean:90）、`dart1OfFan`（Kepler/Text/Fan.lean:86）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）
- `Set.image_union`（Mathlib/Data/Set/Image.lean） -/
theorem DART_FANADD_EQ_DART_FAN_ADD_2DART {x : V3} {V : Set V3}
    {E E1 : Set (Set V3)} {ds : Set (V3 × V3)} {f1 f2 f3 : V3 × V3}
    {v u w : V3}
    (hfan : FAN x V E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) (hds3 : 3 < ds.ncard)
    (hfsub : ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds)
    (hf1 : f1Fan x V E f1 = f2) (hf2 : f1Fan x V E f2 = f3)
    (hf3 : ¬ (f1Fan x V E f3 = f1))
    (hv : f1.1 = v) (hu : f2.1 = u) (hw : f3.1 = w)
    (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E) (hwv : {w, v} ∉ E)
    (hsigma : sigmaFan x V E u w = v) (hvw : v ≠ w)
    (hE1 : E ∪ {({v, w} : Set V3)} = E1) :
    Set.image (fun p : V3 × V3 => (p.1, p.2)) (dartOfFan V E1) =
      Set.image (fun p : V3 × V3 => (p.1, p.2)) (dartOfFan V E) ∪
        ({(v, w), (w, v)} : Set (V3 × V3)) := by
  sorry

end Kepler.Text
