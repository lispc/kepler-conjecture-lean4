/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18i.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18i of block 18, planarity.hl:11439-11610): the
topological-component / fan-connectivity layer
- `exists_point_in_component_yfan` (11439)
- `nonsetedge_fully_surround_fan` (11455)
- `x_in_xfan` (11469)
- `xfan_closed_fan` (11489)
- `topological_component_subset_yfan` (11506)
- `aff_gt_connect_bound_not_inter_edges_fan` (11521)
- `aff_gt_connect_bound_subset_yfan` (11552)
- `sym_line1_fan` (11569)
- `POINT_IN_LINE` (11592)
- `POINT_IN_LINE1` (11600)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `xfan`/`yfan`/`topological_component_yfan` ↔ `xfan`/`yfan`/
  `topologicalComponentYfan` (Kepler/Text/Fan.lean:154/158/199).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42);
  HOL `aff` (affine hull) ↔ `affineSpan ℝ` (Mathlib).
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `closed` ↔ `IsClosed` (cf. `closed_aff_ge_1_2`,
  Kepler/Text/TopologyFan.lean:2648).
- HOL `remark1_fan` (fan.hl:423) is NOT ported under that name; its
  distinctness component is `edge_ne_of_fan` (Kepler/Text/Fan.lean:1039),
  its `aff_ge` membership component is `point_in_aff_ge`
  (Kepler/Text/Planarity.lean:4334). Gaps noted per-theorem.
- `sym_line1_fan`, `POINT_IN_LINE`, `POINT_IN_LINE1` are stated for a
  general real vector space `E` (stronger than HOL `real^N`; the
  affine-hull fact never uses the Euclidean structure). HOL `aff {a,b}`
  is `affineSpan ℝ ({a, b} : Set E)`.
-/

import Kepler.Text.PlanarityDarts

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 分量存在性与 xfan 的拓扑性质（planarity.hl:11439-11520） -/

/-- HOL planarity.hl :11439-11454 `exists_point_in_component_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool.
U IN topological_component_yfan (x,V,E)
==> ?z. z IN U
```

证明思路：展开 `topologicalComponentYfan`，得 `U = connectedComponentIn (yfan x V E) b`
且 `b ∈ yfan x V E`。取 `z = b`，由 `connectedComponentIn_nonempty_iff`（`b ∈ U` 当且
仅当 `b ∈ yfan`）即得。HOL 证明即对 `CONNECTED_COMPONENT_SET` 展开后取
`{y}` 为连通见证（`CONNECTED_SING`）。

候选已有引理：
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- `connectedComponentIn_nonempty_iff`（Mathlib/Topology/Connected/Basic.lean:524）
- `connectedComponentIn_subset`（Mathlib/Topology/Connected/Basic.lean:529） -/
theorem exists_point_in_component_yfan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {U : Set V3} (hU : U ∈ topologicalComponentYfan x V E) :
    ∃ z : V3, z ∈ U := by
  rcases hU with ⟨b, hb, rfl⟩
  exact connectedComponentIn_nonempty_iff.mpr hb

/-- HOL planarity.hl :11455-11468 `nonsetedge_fully_surround_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
(!v. v IN V==>CARD (set_of_edge v V E) >1)/\ FAN(x,V,E)
==> ~(E={})
```

证明思路：反设 `E = ∅`。由 `FAN` 的 `fan1` 分量得 `V ≠ ∅`，取 `w ∈ V`；由
`hcard w hw` 与 `exists_edge_fully_surround_fan` 得 `∃v, {w,v} ∈ E`，与 `E = ∅`
矛盾。HOL 即 `MRESA_TAC exists_edge_fully_surround_fan` 后 `SET_TAC[]`。

候选已有引理：
- `FAN`（Kepler/Text/Fan.lean:56）
- `fan1`（Kepler/Text/Fan.lean:41）
- `exists_edge_fully_surround_fan`（Kepler/Text/PlanarityDarts.lean:480） -/
theorem nonsetedge_fully_surround_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) (hfan : FAN x V E) :
    E ≠ ∅ := by
  intro hE
  have hVne : V ≠ ∅ := hfan.2.2.1.2
  obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hVne
  obtain ⟨v, hvE, _⟩ := exists_edge_fully_surround_fan hfan hw hcard
  rw [hE] at hvE
  exact hvE

/-- HOL planarity.hl :11469-11488 `x_in_xfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E) /\ ~(E={})
==> x IN xfan(x,V,E)
```

证明思路：由 `E ≠ ∅` 取边 `e ∈ E`，`expand_edge_graph_fan` 写成 `e = {v,w}`。由
`fan6` 得 `¬Collinear ℝ ({x,v,w})`（即 `¬Collinear3 x v w`），故
`point_in_aff_ge` 给出 `x ∈ affGe {x} {v,w} = affGe {x} e`。于是
`⟨e, he, hx⟩` 见证 `x ∈ xfan x V E`。

候选已有引理：
- `xfan`（Kepler/Text/Fan.lean:154）
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）
- `fan6`（Kepler/Text/Fan.lean:47） -/
theorem x_in_xfan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hne : E ≠ ∅) :
    x ∈ xfan x V E := by
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨v, w, rfl⟩ := expand_edge_graph_fan hfan he
  have hnc : ¬ Collinear3 x v w := by
    intro h
    exact hfan.2.2.2.2.1 {v, w} he h
  exact ⟨{v, w}, he, (point_in_aff_ge hnc).1⟩

/-- HOL planarity.hl :11489-11505 `xfan_closed_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E) 
==> closed (xfan(x,V,E))
```

证明思路：`xfan x V E = ⋃₀ {affGe {x} e | e ∈ E}`。由 `setEdgesFiniteFan` 得 `E`
有限，故只需证每个 `affGe {x} e` 闭：`expand_edge_graph_fan` 写 `e = {v,w}`，
`fan6` 给出 `¬Collinear3 x v w`，再用 `closed_aff_ge_1_2`。有限个闭集之并闭
（`isClosed_iUnion_of_finite` / `isClosed_sUnion`）。HOL 用 `CLOSED_UNIONS`。

候选已有引理：
- `setEdgesFiniteFan`（Kepler/Text/Fan.lean:851）
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `closed_aff_ge_1_2`（Kepler/Text/TopologyFan.lean:2648）
- `isClosed_iUnion_of_finite`（Mathlib/Topology/Basic.lean:181）
- `isClosed_sUnion`（Mathlib/Topology/AlexandrovDiscrete.lean:74） -/
theorem xfan_closed_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) :
    IsClosed (xfan x V E) := by
  have hfin : E.Finite := setEdgesFiniteFan hfan
  have hEq : xfan x V E = ⋃ e ∈ E, affGe {x} e := by
    ext v
    simp only [xfan, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hEq]
  exact hfin.isClosed_biUnion (fun e he => by
    obtain ⟨v, w, rfl⟩ := expand_edge_graph_fan hfan he
    have hnc : ¬ Collinear3 x v w := by
      intro h
      exact hfan.2.2.2.2.1 {v, w} he h
    exact closed_aff_ge_1_2 hnc)

/-- HOL planarity.hl :11506-11520 `topological_component_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool.
U IN topological_component_yfan (x,V,E)
==> U SUBSET yfan(x,V,E)
```

证明思路：展开 `topologicalComponentYfan`，`U = connectedComponentIn (yfan x V E) b`，
对任意分量用 `connectedComponentIn_subset` 即得 `U ⊆ yfan x V E`。HOL 即
`ASM_REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]`。

候选已有引理：
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- `connectedComponentIn_subset`（Mathlib/Topology/Connected/Basic.lean:529） -/
theorem topological_component_subset_yfan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {U : Set V3} (hU : U ∈ topologicalComponentYfan x V E) :
    U ⊆ yfan x V E := by
  rcases hU with ⟨b, _hb, rfl⟩
  exact connectedComponentIn_subset _ _

/-! ## 弦与边的 aff_gt 分离（planarity.hl:11521-11568） -/

/-- HOL planarity.hl :11521-11551 `aff_gt_connect_bound_not_inter_edges_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 z:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ DISJOINT {x} {y,z}
/\ (!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==>
aff_gt {x} {y,z} INTER aff_ge {x} {v,u}={}
```

证明思路：反设存在 `w ∈ affGt {x} {y,z} ∩ affGe {x} {v,u}`。`scale_in_edges_fan`
把 `w` 写成 `a•(w-x)` 形式（`a>0`），`scale_aff_ge_fan` 把它沿 `{v,u}` 缩放；
`in_aff_gt_1_2` 把 `(1-t)•y + t•z` 放入 `affGt {x} {y,z}`；又由 `hconn` 该点在
`yfan`，而 `yfan = univ \ xfan`，故它不在 `xfan`，与 `w ∈ affGe {x} {v,u} ⊆ xfan`
矛盾（HOL 用 `remark1_fan` 的互异性分量 `edge_ne_of_fan`）。注意
`DISJOINT {x} {y,z}` 在 Lean 中为 `Disjoint ({x} : Set V3) {y,z}`。

候选已有引理：
- `scale_in_edges_fan`（Kepler/Text/PlanarityAngle.lean:1006）
- `scale_aff_ge_fan`（Kepler/Text/Planarity.lean:746）
- `in_aff_gt_1_2`（Kepler/Text/PlanarityAngle.lean:2126）
- `xfan`（Kepler/Text/Fan.lean:154）、`yfan`（Kepler/Text/Fan.lean:158）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039） -/
private theorem disjoint_singleton_pair_of_fan {x v u : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) :
    Disjoint ({x} : Set V3) {v, u} := by
  have hnc : ¬ Collinear3 x v u := by
    intro h
    exact hfan.2.2.2.2.1 {v, u} hvu (by simpa [Collinear3] using h)
  rw [Set.disjoint_iff_inter_eq_empty, Set.singleton_inter_eq_empty]
  intro hmem
  rcases Set.mem_insert_iff.mp hmem with he | he
  · exact hnc (by rw [he]; exact collinear3_of_eq rfl)
  · exact hnc (by rw [Set.mem_singleton_iff.mp he]; exact collinear3_pair_left rfl)

theorem aff_gt_connect_bound_not_inter_edges_fan {x v u y z : V3}
    {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (hdis : Disjoint ({x} : Set V3) {y, z})
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    affGt {x} {y, z} ∩ affGe {x} {v, u} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  rw [Set.mem_inter_iff] at hw
  obtain ⟨hw_gt, hw_ge⟩ := hw
  obtain ⟨a, t, ha0, ht0, ht1, haeq⟩ := scale_in_edges_fan hdis hw_gt
  have hdis_vu : Disjoint ({x} : Set V3) {v, u} :=
    disjoint_singleton_pair_of_fan hfan hvu
  have hscaled : a • (w - x) + x ∈ affGe {x} {v, u} :=
    scale_aff_ge_fan hdis_vu w a hw_ge (le_of_lt ha0)
  have hpt : (1 - t) • y + t • z ∈ affGe {x} {v, u} := by
    rw [haeq] at hscaled
    simpa using hscaled
  have hxfan : (1 - t) • y + t • z ∈ xfan x V E := ⟨{v, u}, hvu, hpt⟩
  have hyfan := hconn t ht0 ht1
  rw [yfan, Set.mem_sdiff] at hyfan
  exact hyfan.2 hxfan

/-- HOL planarity.hl :11552-11568 `aff_gt_connect_bound_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y:real^3 z:real^3.
FAN(x,V,E) /\ DISJOINT {x} {y,z} 
/\ (!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==> aff_gt {x} {y,z} SUBSET yfan (x,V,E)
```

证明思路：`yfan = univ \ xfan`，故只需证
`affGt {x} {y,z} ∩ xfan x V E = ∅`。对任意边 `e ∈ E`，`expand_edge_graph_fan` 写
`e = {v,w}`，由上一引理 `aff_gt_connect_bound_not_inter_edges_fan` 得
`affGt {x} {y,z} ∩ affGe {x} e = ∅`；对 `e ∈ E` 取并即得与
`xfan = ⋃₀ {affGe {x} e | e ∈ E}` 的交为空。

候选已有引理：
- `aff_gt_connect_bound_not_inter_edges_fan`（本文件上文）
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `xfan`（Kepler/Text/Fan.lean:154）、`yfan`（Kepler/Text/Fan.lean:158） -/
theorem aff_gt_connect_bound_subset_yfan {x y z : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hdis : Disjoint ({x} : Set V3) {y, z})
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    affGt {x} {y, z} ⊆ yfan x V E := by
  intro w hw
  rw [yfan, Set.mem_sdiff]
  refine ⟨Set.mem_univ _, ?_⟩
  rintro ⟨e, he, hwe⟩
  obtain ⟨v, u, rfl⟩ := expand_edge_graph_fan hfan he
  have hempty := aff_gt_connect_bound_not_inter_edges_fan hfan he hdis hconn
  rw [Set.eq_empty_iff_forall_notMem] at hempty
  exact hempty w ⟨hw, hwe⟩

/-! ## real^N 仿射包的基本事实（planarity.hl:11569-11609） -/

/-- HOL planarity.hl :11569-11591 `sym_line1_fan`

HOL 原文：
```
!x y z:real^N. x IN aff {y, z} /\ ~(x=y)
==> z IN aff {x,y}
```

证明思路：设 `x ∈ affineSpan ℝ {y,z}` 且 `x ≠ y`。由
`affineSpan_insert_eq_affineSpan` 得 `affineSpan ℝ {x,y,z} = affineSpan ℝ {y,z}`；
又 `x,y ∈ affineSpan ℝ {x,y}`（`left_mem_affineSpan_pair`/`right_mem_affineSpan_pair`），
故 `affineSpan ℝ {x,y,z} ≤ affineSpan ℝ {x,y}`；`z ∈ affineSpan ℝ {x,y,z}` 于是
`z ∈ affineSpan ℝ {x,y}`。HOL 用 `AFFINE_HULL_2` 的显式组合展开。

编码说明：HOL `real^N`（任意有限维欧氏空间）在 Lean 中以任意实向量空间 `E`
表达（更强；仿射包结论不依赖欧氏结构）。HOL `aff {a,b}` =
`affineSpan ℝ ({a, b} : Set E)`。

候选已有引理：
- `affineSpan_insert_eq_affineSpan`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1088）
- `left_mem_affineSpan_pair`（同上 Defs.lean:1046）
- `right_mem_affineSpan_pair`（同上 Defs.lean:1050）
- `affineSpan_pair_comm`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Basic.lean:1001） -/
theorem sym_line1_fan {E : Type*} [AddCommGroup E] [Module ℝ E] (x y z : E)
    (hx : x ∈ affineSpan ℝ ({y, z} : Set E)) (hne : x ≠ y) :
    z ∈ affineSpan ℝ ({x, y} : Set E) := by
  have h := affineSpan_pair_eq_of_right_mem_of_ne (k := ℝ) hx hne
  rw [← AffineSubspace.affineSpan_pair_comm (k := ℝ) (p₁ := x) (p₂ := y)] at h
  rw [h]
  exact right_mem_affineSpan_pair (k := ℝ) y z

/-- HOL planarity.hl :11592-11599 `POINT_IN_LINE`

HOL 原文：
```
!x y:real^N. x IN  aff {x,y}
```

证明思路：`x` 是生成点之一，直接由 `left_mem_affineSpan_pair`（或
`mem_affineSpan` + `Set.mem_insert`）得。HOL 取组合系数 `(1,0)` 后
`REDUCE_VECTOR_TAC`。

编码说明：同 `sym_line1_fan`，以任意实向量空间 `E` 表达 `real^N`。

候选已有引理：
- `left_mem_affineSpan_pair`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1046）
- `mem_affineSpan`（Mathlib，`affineSpan` 的成员刻画） -/
theorem POINT_IN_LINE {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) :
    x ∈ affineSpan ℝ ({x, y} : Set E) := by
  exact left_mem_affineSpan_pair (k := ℝ) x y

/-- HOL planarity.hl :11600-11609 `POINT_IN_LINE1`

HOL 原文：
```
!x y:real^N. y IN  aff {x,y}
```

证明思路：`y` 是生成点之一，直接由 `right_mem_affineSpan_pair`（或
`mem_affineSpan` + `Set.mem_insert_of_mem`/`Set.mem_singleton`）得。HOL 取组合系数
`(0,1)` 后 `REDUCE_VECTOR_TAC`。

编码说明：同 `sym_line1_fan`，以任意实向量空间 `E` 表达 `real^N`。

候选已有引理：
- `right_mem_affineSpan_pair`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1050）
- `mem_affineSpan`（Mathlib，`affineSpan` 的成员刻画） -/
theorem POINT_IN_LINE1 {E : Type*} [AddCommGroup E] [Module ℝ E] (x y : E) :
    y ∈ affineSpan ℝ ({x, y} : Set E) := by
  sorry

end Kepler.Text
