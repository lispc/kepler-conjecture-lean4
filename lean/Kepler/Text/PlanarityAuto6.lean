/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18j.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18j of block 18, planarity.hl:11616-11786): the
affine-line symmetry / fan-separation layer
- `sym_line0_fan` (11616)
- `sym_line_fan` (11631)
- `sym_line01_fan` (11643)
- `sym_line02_fan` (11655)
- `sym_line_fan1` (11678)
- `aff_ge_1_1_subset_aff_fan` (11688)
- `exists_point_notxin_convex_in_xfan` (11700)
- `notempty_xfan_inter_segment_fan` (11747)
- `xfan_inter_segment_closed_fan` (11761)
- `point_in_yfan_not_x_fan` (11770)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `aff {a,b}` (affine hull of a two-point set) ↔
  `affineSpan ℝ ({a, b} : Set E)` (Mathlib).
- HOL `real^N` ↔ an arbitrary real vector space `E`
  (`[AddCommGroup E] [Module ℝ E]`), as already done for `sym_line1_fan`
  in Kepler/Text/PlanarityConnect.lean:316; the affine-hull facts never
  use the Euclidean structure.
- HOL `DISJOINT {a} {b,c}` ↔ `Disjoint ({a} : Set E) ({b, c} : Set E)`
  (`Set.disjoint_iff_inter_eq_empty`).
- HOL `aff_ge {a} {b}` ↔ `affGe {a} {b}` (Kepler/Geom/Aff.lean:42).
- HOL `xfan`/`yfan`/`topological_component_yfan` ↔ `xfan`/`yfan`/
  `topologicalComponentYfan` (Kepler/Text/Fan.lean:154/158/199).
- HOL `convex hull {v,z}` ↔ `convexHull ℝ ({v, z} : Set V3)`; HOL
  `segment[v,z]` ↔ `segment ℝ v z` (Mathlib closed segment).
- HOL `closed` ↔ `IsClosed`.
- `sym_line0_fan`/`sym_line01_fan`/`sym_line02_fan` are general affine
  facts. Mathlib has the ingredients
  (`affineSpan_pair_le_of_mem_of_mem`, `affineSpan_pair_eq_of_left_mem_of_ne`,
  `affineSpan_pair_eq_of_right_mem_of_ne`, `affineSpan_pair_comm`) but NOT
  these exact named statements; kept for HOL name fidelity.
-/

import Kepler.Text.PlanarityConnect

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## real^N 仿射线对称性（planarity.hl:11616-11687） -/

/-- HOL planarity.hl :11616-11630 `sym_line0_fan`

HOL 原文：
```
!x y z:real^N. x IN aff {y, z} /\ DISJOINT {x} {y,z}
==> aff {x,z} SUBSET aff {x,y}
```

证明思路：由 `DISJOINT {x} {y,z}` 得 `x ≠ y`。用已移植的
`sym_line1_fan`（`x ∈ aff {y,z}`、`x ≠ y`）得 `z ∈ aff {x,y}`；又
`x ∈ aff {x,y}`（`POINT_IN_LINE`）。于是 `{x,z} ⊆ aff {x,y}`，由
`affineSpan_le`/`HULL_MONO`（HOL）得 `aff {x,z} ⊆ aff {x,y}`。

编码说明：HOL `real^N` 以任意实向量空间 `E` 表达；`DISJOINT` 用
`Disjoint`。

候选已有引理：
- `sym_line1_fan`（Kepler/Text/PlanarityConnect.lean:316）
- `POINT_IN_LINE`（Kepler/Text/PlanarityConnect.lean:341）
- `affineSpan_pair_le_of_mem_of_mem`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1056）
- `affineSpan_le`（Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:639） -/
theorem sym_line0_fan {E : Type*} [AddCommGroup E] [Module ℝ E] (x y z : E)
    (hx : x ∈ affineSpan ℝ ({y, z} : Set E))
    (hdis : Disjoint ({x} : Set E) {y, z}) :
    affineSpan ℝ ({x, z} : Set E) ≤ affineSpan ℝ ({x, y} : Set E) := by
  have hxmem : x ∉ ({y, z} : Set E) := Set.disjoint_singleton_left.mp hdis
  have hxy : x ≠ y := by
    intro h
    exact hxmem (by simp [h])
  have hz : z ∈ affineSpan ℝ ({x, y} : Set E) := sym_line1_fan x y z hx hxy
  apply affineSpan_le.mpr
  intro w hw
  rcases Set.mem_insert_iff.mp hw with hwx | hwz
  · rw [hwx]
    exact POINT_IN_LINE x y
  · rw [Set.mem_singleton_iff.mp hwz]
    exact hz

/-- HOL planarity.hl :11631-11642 `sym_line_fan`

HOL 原文：
```
!x y z:real^N. x IN aff {y, z} /\ DISJOINT {x} {y,z}
==> aff {x,z} = aff {x,y}
```

证明思路：对 `sym_line0_fan` 用两次（第二次交换 `y`、`z`）得
`aff {x,z} ⊆ aff {x,y}` 与 `aff {x,y} ⊆ aff {x,z}`，`le_antisymm`（HOL 用
集合外延 + `SET_TAC`）即得相等。

编码说明：同 `sym_line0_fan`，以任意实向量空间 `E` 表达 `real^N`。

候选已有引理：
- `sym_line0_fan`（本文件上文）
- `le_antisymm`（Lean 序结构） -/
theorem sym_line_fan {E : Type*} [AddCommGroup E] [Module ℝ E] (x y z : E)
    (hx : x ∈ affineSpan ℝ ({y, z} : Set E))
    (hdis : Disjoint ({x} : Set E) {y, z}) :
    affineSpan ℝ ({x, z} : Set E) = affineSpan ℝ ({x, y} : Set E) := by
  apply le_antisymm
  · exact sym_line0_fan x y z hx hdis
  · exact sym_line0_fan x z y (by simpa [Set.pair_comm] using hx)
      (by simpa [Set.pair_comm] using hdis)

/-- HOL planarity.hl :11643-11654 `sym_line01_fan`

HOL 原文：
```
!x y z:real^N. x IN aff {y, z} /\ DISJOINT {y} {x,z}
==> aff {y,x} SUBSET aff {y,z}
```

证明思路：`y ∈ aff {y,z}`（`POINT_IN_LINE1`）且 `x ∈ aff {y,z}`（假设），故
`{y,x} ⊆ aff {y,z}`，由 `affineSpan_le`（HOL 的 `HULL_MONO` +
`AFFINE_HULL_AFFINE_EQ`）得 `aff {y,x} ⊆ aff {y,z}`。注意 `DISJOINT {y} {x,z}`
在本结论中未被用到（HOL 证明也未使用）。

编码说明：同 `sym_line0_fan`，以任意实向量空间 `E` 表达 `real^N`。

候选已有引理：
- `POINT_IN_LINE1`（Kepler/Text/PlanarityConnect.lean:362）
- `affineSpan_pair_le_of_mem_of_mem`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1056）
- `affineSpan_le`（Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:639） -/
theorem sym_line01_fan {E : Type*} [AddCommGroup E] [Module ℝ E] (x y z : E)
    (hx : x ∈ affineSpan ℝ ({y, z} : Set E))
    (hdis : Disjoint ({y} : Set E) {x, z}) :
    affineSpan ℝ ({y, x} : Set E) ≤ affineSpan ℝ ({y, z} : Set E) := by
  have := hdis
  exact affineSpan_pair_le_of_right_mem (k := ℝ) hx

/-- HOL planarity.hl :11655-11677 `sym_line02_fan`

HOL 原文：
```
!x y z:real^N. x IN aff {y, z} /\ DISJOINT {y} {x,z}
==> aff {y,z} SUBSET aff {y,x}
```

证明思路：由 `DISJOINT {y} {x,z}` 得 `x ≠ y`。用 `sym_line1_fan`
（`x ∈ aff {y,z}`、`x ≠ y`）得 `z ∈ aff {x,y} = aff {y,x}`；又
`y ∈ aff {y,x}`。故 `{y,z} ⊆ aff {y,x}`，`affineSpan_le`（HOL 用
`HULL_MONO` + `AFFINE_HULL_AFFINE_EQ`）给出 `aff {y,z} ⊆ aff {y,x}`。

编码说明：同 `sym_line0_fan`，以任意实向量空间 `E` 表达 `real^N`。

候选已有引理：
- `sym_line1_fan`（Kepler/Text/PlanarityConnect.lean:316）
- `POINT_IN_LINE1`（Kepler/Text/PlanarityConnect.lean:362）
- `affineSpan_pair_comm`
  （Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Basic.lean:1001）
- `affineSpan_le`（Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:639） -/
theorem sym_line02_fan {E : Type*} [AddCommGroup E] [Module ℝ E] (x y z : E)
    (hx : x ∈ affineSpan ℝ ({y, z} : Set E))
    (hdis : Disjoint ({y} : Set E) {x, z}) :
    affineSpan ℝ ({y, z} : Set E) ≤ affineSpan ℝ ({y, x} : Set E) := by
  have hy_notin : y ∉ ({x, z} : Set E) := Set.disjoint_singleton_left.mp hdis
  have hxy : x ≠ y := by
    intro h
    exact hy_notin (by simp [h])
  have hz : z ∈ affineSpan ℝ ({x, y} : Set E) := sym_line1_fan x y z hx hxy
  rw [AffineSubspace.affineSpan_pair_comm (k := ℝ) (p₁ := x) (p₂ := y)] at hz
  apply affineSpan_le.mpr
  intro w hw
  rcases Set.mem_insert_iff.mp hw with hwy | hwz
  · rw [hwy]
    exact POINT_IN_LINE y x
  · rw [Set.mem_singleton_iff.mp hwz]
    exact hz

/-- HOL planarity.hl :11678-11687 `sym_line_fan1`

HOL 原文：
```
!x y z:real^N. x IN aff {y, z} /\ DISJOINT {y} {x,z}
==> aff {y,z} = aff {y,x}
```

证明思路：合并 `sym_line01_fan` 与 `sym_line02_fan` 两个包含关系，
`le_antisymm`（HOL 用 `SET_TAC`）即得相等。

编码说明：同 `sym_line0_fan`，以任意实向量空间 `E` 表达 `real^N`。

候选已有引理：
- `sym_line01_fan`（本文件上文）
- `sym_line02_fan`（本文件上文）
- `le_antisymm`（Lean 序结构） -/
theorem sym_line_fan1 {E : Type*} [AddCommGroup E] [Module ℝ E] (x y z : E)
    (hx : x ∈ affineSpan ℝ ({y, z} : Set E))
    (hdis : Disjoint ({y} : Set E) {x, z}) :
    affineSpan ℝ ({y, z} : Set E) = affineSpan ℝ ({y, x} : Set E) := by
  apply le_antisymm
  · exact sym_line02_fan x y z hx hdis
  · exact sym_line01_fan x y z hx hdis

/-! ## aff_ge 落入仿射包（planarity.hl:11688-11699） -/

/-- HOL planarity.hl :11688-11699 `aff_ge_1_1_subset_aff_fan`

HOL 原文：
```
!x y z:real^3. ~(y=z) /\ x IN aff_ge {y} {z} ==> x IN aff {y,z}
```

证明思路：HOL 用 `AFF_GE_1_1` 展开 `x ∈ aff_ge {y} {z}` 为
`x = t1•y + t2•z`（`t1+t2=1`，`0≤t2`），再按 `AFFINE_HULL_2` 的二元组合
形式 `∃t1 t2, t1+t2=1 ∧ x = t1•y + t2•z` 给出 `x ∈ aff {y,z}`。

编码说明：`~(y=z)` 为 `y ≠ z`；HOL `aff_ge {y} {z}` 为 `affGe {y} {z}`。
注意与已有 `affGe_single_subset_affineSpan`（Planarity.lean 中 private，故
本文件重新陈述）是同一命题，变量名顺序不同。

候选已有引理：
- `affGe_ray`（Kepler/Geom/Aff.lean:196）
- `mem_affGe_singleton`（Kepler/Text/TopologyFan.lean:2663）
- `mem_affineSpan_pair_iff_exists_lineMap_eq`（Mathlib）
- `affGe_single_subset_affineSpan`（private，Kepler/Text/Planarity.lean:4190） -/
theorem aff_ge_1_1_subset_aff_fan (x y z : V3) (hyz : y ≠ z)
    (hx : x ∈ affGe {y} {z}) :
    x ∈ affineSpan ℝ ({y, z} : Set V3) := by
  obtain ⟨t, ht⟩ := affGe_ray hyz hx
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨t, ?_⟩
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  exact (sub_eq_iff_eq_add.mp ht).symm

/-! ## xfan 中避开给定凸包的点（planarity.hl:11700-11746） -/

/-- HOL planarity.hl :11700-11746 `exists_point_notxin_convex_in_xfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) z:real^3.
FAN(x,V,E)  /\ ~(x=z) /\ ~(E={})
==> ?v. v IN xfan(x,V,E) /\ ~(x IN convex hull{v,z})
```

证明思路：由 `E ≠ ∅` 取边 `e ∈ E`，`expand_edge_graph_fan` 写成
`e = {v,w}`。由 `point_in_aff_ge` 得 `v,w ∈ affGe {x} {v,w}`，故二者均在
`xfan`。分情形：若 `x ∉ convexHull {v,z}` 取 `v`；否则 `x ∈ convexHull {v,z}`，
用 `convexHull_subset_affineSpan` 得 `x ∈ aff {v,z}`，由 `~ (x=z)`、`~ (x=v)`
及 `sym_line_fan` 推出 `x ∈ aff {w,z}`，再 `POINT_IN_LINE1`/`sym_line_fan`
得矛盾（`x` 不可能既在 `aff {w,z}` 又不在其凸包，HOL 实际推出
`x ∉ convexHull {w,z}`）。取 `w` 为见证。

编码说明：HOL `convex hull {v,z}` 为 `convexHull ℝ ({v, z} : Set V3)`；
`remark1_fan` 的互异性分量为 `edge_ne_of_fan`（Fan.lean:1039）。

候选已有引理：
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）
- `convexHull_subset_affineSpan`（Mathlib/Analysis/Convex/Hull.lean:201）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `sym_line_fan`（本文件上文）、`POINT_IN_LINE1`（PlanarityConnect.lean:362）
- `xfan`（Kepler/Text/Fan.lean:154） -/
theorem exists_point_notxin_convex_in_xfan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (z : V3)
    (hfan : FAN x V E) (hxz : x ≠ z) (hne : E ≠ ∅) :
    ∃ v : V3, v ∈ xfan x V E ∧ x ∉ convexHull ℝ ({v, z} : Set V3) := by
  obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨v, w, rfl⟩ := expand_edge_graph_fan hfan he
  have hnc : ¬ Collinear3 x v w := fan_not_collinear hfan he
  obtain ⟨-, hv_ge, hw_ge⟩ := point_in_aff_ge hnc
  have hvx : v ∈ xfan x V E := ⟨{v, w}, he, hv_ge⟩
  have hwx : w ∈ xfan x V E := ⟨{v, w}, he, hw_ge⟩
  by_cases hxc : x ∈ convexHull ℝ ({v, z} : Set V3)
  · refine ⟨w, hwx, ?_⟩
    intro hxw
    have hxv_aff : x ∈ affineSpan ℝ ({v, z} : Set V3) :=
      convexHull_subset_affineSpan ({v, z} : Set V3) hxc
    have hxw_aff : x ∈ affineSpan ℝ ({w, z} : Set V3) :=
      convexHull_subset_affineSpan ({w, z} : Set V3) hxw
    have hline1 : affineSpan ℝ ({v, z} : Set V3) = affineSpan ℝ ({x, z} : Set V3) :=
      (affineSpan_pair_eq_of_left_mem_of_ne (k := ℝ) hxv_aff hxz).symm
    have hline2 : affineSpan ℝ ({x, z} : Set V3) = affineSpan ℝ ({w, z} : Set V3) :=
      affineSpan_pair_eq_of_left_mem_of_ne (k := ℝ) hxw_aff hxz
    have hw_line : w ∈ affineSpan ℝ ({v, z} : Set V3) := by
      rw [hline1, hline2]
      exact left_mem_affineSpan_pair (k := ℝ) w z
    have hcol : Collinear ℝ ({x, v, w} : Set V3) :=
      collinear_triple_of_mem_affineSpan_pair (p₁ := x) (p₂ := v) (p₃ := w)
        (p₄ := v) (p₅ := z) hxv_aff (left_mem_affineSpan_pair (k := ℝ) v z) hw_line
    exact hnc hcol
  · exact ⟨v, hvx, hxc⟩

/-! ## xfan 与线段的交（planarity.hl:11747-11769） -/

/-- HOL planarity.hl :11747-11760 `notempty_xfan_inter_segment_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) z:real^3 v:real^3.
FAN(x,V,E) /\ v IN xfan(x,V,E)
==> ~(xfan(x,V,E) INTER segment[v,z] ={})
```

证明思路：取 `y = v`，它同时在 `xfan`（假设）与 `segment[v,z]`（线段端点，
系数 `(1,0)`；HOL 的 `&0`）。故交非空。HOL 用 `segment` 展开 + `&0` +
`REDUCE_VECTOR_TAC`。

编码说明：HOL `segment[v,z]` 为 `segment ℝ v z`；`~(A={})` 为 `A ≠ ∅`。

候选已有引理：
- `xfan`（Kepler/Text/Fan.lean:154）
- `left_mem_segment`（Mathlib/Analysis/Convex/Segment.lean:105）
- `Set.nonempty_iff_ne_empty`（Mathlib） -/
theorem notempty_xfan_inter_segment_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (z : V3) (v : V3)
    (hfan : FAN x V E) (hv : v ∈ xfan x V E) :
    xfan x V E ∩ segment ℝ v z ≠ ∅ := by
  exact Set.nonempty_iff_ne_empty.mp ⟨v, hv, left_mem_segment ℝ v z⟩

/-- HOL planarity.hl :11761-11769 `xfan_inter_segment_closed_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) z:real^3 v:real^3.
FAN(x,V,E) ==> closed(xfan(x,V,E) INTER segment[v,z])
```

证明思路：`IsClosed.inter`（HOL 的 `CLOSED_INTER`）。`xfan x V E` 闭由
`xfan_closed_fan`；`segment ℝ v z` 闭（HOL 的 `CLOSED_SEGMENT`）：它是
紧集 `Set.Icc (0:ℝ) 1` 在连续映射 `t ↦ (1-t)•v + t•z` 下的像，紧故闭
（`isCompact_Icc.image` + `IsCompact.isClosed`；或 `segment_eq_image`）。

编码说明：HOL `closed` 为 `IsClosed`；`segment[v,z]` 为 `segment ℝ v z`。

候选已有引理：
- `xfan_closed_fan`（Kepler/Text/PlanarityConnect.lean:158）
- `IsClosed.inter`（Mathlib/Topology/Basic.lean:163）
- `convex_segment`（Mathlib/Analysis/Convex/Basic.lean:164）
- `segment_eq_image`（Mathlib/Analysis/Convex/Segment.lean:193）
- `isCompact_Icc`（Mathlib/Topology/Order/Compact.lean:54）
- `IsCompact.isClosed`（Mathlib/Topology/Separation/Hausdorff.lean:590） -/
theorem xfan_inter_segment_closed_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (z : V3) (v : V3) (hfan : FAN x V E) :
    IsClosed (xfan x V E ∩ segment ℝ v z) := by
  refine (xfan_closed_fan hfan).inter ?_
  rw [← convexHull_pair v z]
  exact (Set.toFinite ({v, z} : Set V3)).isClosed_convexHull ℝ

/-! ## yfan 分量不包含中心（planarity.hl:11770-11786） -/

/-- HOL planarity.hl :11770-11786 `point_in_yfan_not_x_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool z:real^3.
FAN(x,V,E) /\ ~(E={})
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
==> ~(x=z)
```

证明思路：由 `topological_component_subset_yfan` 得 `U ⊆ yfan x V E`，故
`z ∈ yfan x V E`。若 `x = z` 则 `x ∈ yfan x V E`；但由 `x_in_xfan`
（需 `E ≠ ∅`）有 `x ∈ xfan x V E`，而 `yfan = univ \ xfan`，矛盾。

编码说明：HOL `topological_component_yfan` 为 `topologicalComponentYfan`；
HOL `~(x=z)` 为 `x ≠ z`。

候选已有引理：
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `x_in_xfan`（Kepler/Text/PlanarityConnect.lean:128）
- `yfan`（Kepler/Text/Fan.lean:158）、`xfan`（Kepler/Text/Fan.lean:154）
- `Set.mem_sdiff`（Mathlib） -/
theorem point_in_yfan_not_x_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (z : V3)
    (hfan : FAN x V E) (hne : E ≠ ∅)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U) :
    x ≠ z := by
  sorry

end Kepler.Text
