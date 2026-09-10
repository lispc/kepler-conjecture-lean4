/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18l.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18l of block 18, planarity.hl:12006-12217): the
xfan/yfan separation and edge-minimization layer
- `place_there_point_line_fan` (12006)
- `aff_ge_1_1_subset_xfan` (12039)
- `point_in_yfan_and_point_in_xfan_indepent_fan` (12067)
- `permutes_4points_collinear` (12094)
- `permutes_4points_collinear1` (12105)
- `in_aff_gt_eq_azim` (12117)
- `no_origin_aff_ge_is_aff_gt` (12130)
- `exists_edge_component_yfan` (12155)
- `v_subset_xfan` (12195)
- `set_of_edge_subset_edges` (12209)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `xfan`/`yfan`/`topological_component_yfan` ↔ `xfan`/`yfan`/
  `topologicalComponentYfan` (Kepler/Text/Fan.lean:154/158/199).
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `aff {a,b}` (affine hull of a two-point set) ↔
  `affineSpan ℝ ({a, b} : Set E)` (Mathlib).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42).
- HOL `collinear {a,b,c}` ↔ `Collinear ℝ ({a, b, c} : Set E)`;
  HOL `~collinear {x,y,z}` ↔ `¬ Collinear3 x y z` when the ambient space
  is `real^3` (Kepler/Geom/Azim.lean:43).
- HOL `real^N` ↔ an arbitrary real vector space `E`
  (`[AddCommGroup E] [Module ℝ E]`), as in
  Kepler/Text/PlanarityConnect.lean:316 and
  Kepler/Text/PlanarityAuto6.lean:83; `permutes_4points_collinear` and
  `permutes_4points_collinear1` are stated this way (stronger).
- HOL `azim1 x v y w` ↔ `azim1 x v y w` (Kepler/Text/TopologyFan.lean:229).
- HOL `AFF_GT_1_1`/`AFF_GE_1_1` (the two-point `aff_gt`/`aff_ge`
  membership forms) are NOT ported under those names; the closest
  existing encodings are `mem_affGe_singleton`
  (Kepler/Text/TopologyFan.lean:2663) and `affGe_ray`
  (Kepler/Geom/Aff.lean:196) for `aff_ge`; there is no `aff_gt`
  singleton form yet. Gaps noted per-theorem.
- HOL `AZIM_SPECIAL_SCALE` (axis rescaling invariance of `azim`) is NOT
  ported under that name; the closest is `azim_of_affGt_combo`
  (Kepler/Text/TopologyFan.lean:824), which moves the third argument, not
  the axis. Gap noted in `in_aff_gt_eq_azim`.
- HOL `remark1_fan` is NOT ported under that name; its distinctness
  component is `edge_ne_of_fan` (Kepler/Text/Fan.lean:1039), its
  `aff_ge` membership component is `point_in_aff_ge`
  (Kepler/Text/Planarity.lean:4334). Gaps noted per-theorem.
-/

import Kepler.Text.PlanarityAuto7

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 直线上的点落入 aff_ge（planarity.hl:12006-12038） -/

/-- HOL planarity.hl :12006-12038 `place_there_point_line_fan`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3.
~(x=y)/\ z IN aff {x,y}==> ?t:real. &0<t /\ t< &1 /\ (&1-t)%y+t % z IN aff_ge {x} {y}
```

证明思路：HOL 用 `AFFINE_HULL_2` 把 `z ∈ aff {x,y}` 写成 `z = u•x + v•y`
（`u+v=1`），再用 `AFF_GE_1_1` 展开目标 `aff_ge {x} {y}`。按 `v ≥ 0` 与
`v < 0` 分情形：前者取 `t = 1/2`；后者取 `t = inv u`（此时 `u > 1`），
两情形都把 `(1-t)•y + t•z` 重新组合为 `x,y` 的非负系数组合。

编码说明：HOL `aff {x,y}` 为 `affineSpan ℝ ({x,y} : Set V3)`；
`~(x=y)` 为 `x ≠ y`；`aff_ge {x} {y}` 为 `affGe {x} {y}`。

候选已有引理：
- `mem_affGe_singleton`（Kepler/Text/TopologyFan.lean:2663）
- `affGe_ray`（Kepler/Geom/Aff.lean:196）
- `aff_ge_1_2`（Kepler/Text/Planarity.lean:622）
- `mem_affineSpan_pair_iff_exists_lineMap_eq`（Mathlib，`affineSpan` 二元刻画） -/
theorem place_there_point_line_fan (x y z : V3) (hxy : x ≠ y)
    (hz : z ∈ affineSpan ℝ ({x, y} : Set V3)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1 - t) • y + t • z ∈ affGe {x} {y} := by
  obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  have hz' : z = (1 - s) • x + s • y := by
    rw [← hs, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  rcases lt_or_ge s 0 with hs0 | hs0
  · refine ⟨1 / (1 - s), ?_, ?_, ?_⟩
    · exact one_div_pos.mpr (by linarith)
    · rw [div_lt_one (by linarith)]
      linarith
    · rw [mem_affGe_singleton hxy]
      refine ⟨1, 0, le_refl 0, by ring, ?_⟩
      rw [hz']
      have hsne : (1 : ℝ) - s ≠ 0 := by linarith
      rw [WithLp.ext_iff]
      ext i
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply]
      have h : (1 - s)⁻¹ * (1 - s) = 1 := inv_mul_cancel₀ hsne
      linear_combination (x.ofLp i - y.ofLp i) * h
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    rw [mem_affGe_singleton hxy]
    refine ⟨(1 - s) / 2, (1 + s) / 2, by linarith, by ring, ?_⟩
    rw [hz']
    module

/-! ## aff_ge 边锥含于 xfan（planarity.hl:12039-12066） -/

/-- HOL planarity.hl :12039-12066 `aff_ge_1_1_subset_xfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ y IN xfan(x,V,E) /\ ~(x=y)
==>  aff_ge {x} {y} SUBSET xfan(x,V,E)
```

证明思路：由 `y ∈ xfan` 取边 `e ∈ E` 使 `y ∈ aff_ge {x} e`；用
`expand_edge_graph_fan` 写 `e = {v,w}`，再用
`aff_ge_1_1_subset_aff_ge_fan` 把 `aff_ge {x} {y}` 嵌入 `aff_ge {x} {v,w}`，
后者按 `xfan` 定义含于 `xfan x V E`。`~ (x=y)` 与 `remark1_fan` 的互异性
分量（`edge_ne_of_fan`）保证嵌入引理的假设。

候选已有引理：
- `expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）
- `aff_ge_1_1_subset_aff_ge_fan`（Kepler/Text/Planarity.lean:4059）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `xfan`（Kepler/Text/Fan.lean:154） -/
theorem aff_ge_1_1_subset_xfan (x : V3) (V : Set V3) (E : Set (Set V3)) (y : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hy : y ∈ xfan x V E) (hxy : x ≠ y) :
    affGe {x} {y} ⊆ xfan x V E := by
  intro z hz
  obtain ⟨e, heE, hye⟩ := hy
  obtain ⟨v, w, heq⟩ := expand_edge_graph_fan hfan heE
  have hy' : y ∈ affGe {x} {v, w} := by simpa [heq] using hye
  have hxe : x ∉ e := by
    intro hx
    exact hfan.2.2.2.1 (hfan.1 (Set.mem_sUnion.mpr ⟨e, heE, hx⟩))
  have hxvw : x ∉ ({v, w} : Set V3) := by simpa [heq] using hxe
  have hdis : Disjoint ({x} : Set V3) {v, w} := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at hb
    exact hxvw hb
  refine ⟨e, heE, ?_⟩
  rw [heq]
  exact aff_ge_1_1_subset_aff_ge_fan (v1 := y) hdis hxy hy' hz

/-! ## yfan 与 xfan 的点独立性（planarity.hl:12067-12093） -/

/-- HOL planarity.hl :12067-12093 `point_in_yfan_and_point_in_xfan_indepent_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ y IN xfan(x,V,E) 
/\ ~(y=x) /\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==> ~collinear {x,y,z}
```

证明思路：反设 `x,y,z` 共线；由 `zpoint_in_yfan` 得 `z ∈ yfan`，故
`z ≠ x`。用 `place_there_point_line_fan` 取 `t ∈ (0,1)` 使
`(1-t)•y + t•z ∈ aff_ge {x} {y}`，再用 `aff_ge_1_1_subset_xfan` 得该点
在 `xfan`；但 `hconn` 说它在 `yfan = univ \ xfan`，矛盾。

候选已有引理：
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `zpoint_in_yfan`（Kepler/Text/PlanarityAuto7.lean:83）
- `place_there_point_line_fan`（本文件上文）
- `aff_ge_1_1_subset_xfan`（本文件上文）
- `yfan`（Kepler/Text/Fan.lean:158） -/
theorem point_in_yfan_and_point_in_xfan_indepent_fan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (U : Set V3) (y z : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hy : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    ¬ Collinear3 x y z := by
  have hxy : x ≠ y := hyx.symm
  intro hcol
  have hz_aff : z ∈ affineSpan ℝ ({x, y} : Set V3) :=
    (collinear3_iff_mem_affineSpan hxy).mp hcol
  obtain ⟨t, ht0, ht1, htmem⟩ := place_there_point_line_fan x y z hxy hz_aff
  have hsub := aff_ge_1_1_subset_xfan x V E y hfan hcard hy hxy
  have hxfan : (1 - t) • y + t • z ∈ xfan x V E := hsub htmem
  have hyfan : (1 - t) • y + t • z ∈ yfan x V E := hconn t ht0 ht1
  exact hyfan.2 hxfan

/-! ## 四点共线置换（planarity.hl:12094-12116） -/

/-- HOL planarity.hl :12094-12104 `permutes_4points_collinear`

HOL 原文：
```
!x y z w:real^N.
~(x=y)/\ ~(x=z) /\ y IN aff {x,z}/\ ~collinear{x,y,w}==> ~collinear{x,z,w}
```

证明思路：HOL 先 `REWRITE_TAC[collinear_fan]`，把 `collinear` 化为
`w ∈ aff {x,·}`。由 `~(x=y)`、`~(x=z)` 得 `DISJOINT {x} {y,z}`，再用
`sym_line_fan1` 把 `aff {y,z}` 换成 `aff {y,x}` 并传递，把
`w ∈ aff {x,y}` 转化为 `w ∈ aff {x,z}`，与 `¬collinear{x,z,w}` 矛盾。

编码说明：HOL `real^N` 以任意实向量空间 `E` 表达（更强）；HOL `aff {a,b}`
为 `affineSpan ℝ ({a,b} : Set E)`，`collinear {a,b,c}` 为
`Collinear ℝ ({a,b,c} : Set E)`。

候选已有引理：
- `sym_line_fan1`（Kepler/Text/PlanarityAuto6.lean:209）
- `collinear3_iff_mem_affineSpan`（Kepler/Text/TopologyFan.lean:785）
- `affineSpan_pair_comm`（Mathlib） -/
theorem permutes_4points_collinear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y z w : E) (hxy : x ≠ y) (hxz : x ≠ z)
    (hy : y ∈ affineSpan ℝ ({x, z} : Set E))
    (hnc : ¬ Collinear ℝ ({x, y, w} : Set E)) :
    ¬ Collinear ℝ ({x, z, w} : Set E) := by
  intro hc
  apply hnc
  have hw : w ∈ affineSpan ℝ ({x, z} : Set E) :=
    Collinear.mem_affineSpan_of_mem_of_ne hc (by simp) (by simp) (by simp) hxz
  exact collinear_triple_of_mem_affineSpan_pair (k := ℝ)
    (p₁ := x) (p₂ := y) (p₃ := w) (p₄ := x) (p₅ := z)
    (left_mem_affineSpan_pair _ _ _) hy hw

/-- HOL planarity.hl :12105-12116 `permutes_4points_collinear1`

HOL 原文：
```
!x y z w:real^N.
~(x=y)/\ ~(x=z) /\  y IN aff {x,z}/\ ~collinear{x,z,w}==> ~collinear{x,y,w}
```

证明思路：与 `permutes_4points_collinear` 对偶（交换假设与结论中的 `y`、`z`）。
HOL 用 `sym_line01_fan` 把 `aff {y,x}` 嵌入 `aff {y,z}`，再由
`DISJOINT {x} {y,z}` 与集合运算把 `w ∈ aff {y,z}` 转化为
`w ∈ aff {x,y}`，与 `¬collinear{x,y,w}` 矛盾。

编码说明：同 `permutes_4points_collinear`，以任意实向量空间 `E` 表达
`real^N`。

候选已有引理：
- `sym_line01_fan`（Kepler/Text/PlanarityAuto6.lean:146）
- `sym_line_fan1`（Kepler/Text/PlanarityAuto6.lean:209）
- `collinear3_iff_mem_affineSpan`（Kepler/Text/TopologyFan.lean:785） -/
theorem permutes_4points_collinear1 {E : Type*} [AddCommGroup E] [Module ℝ E]
    (x y z w : E) (hxy : x ≠ y) (hxz : x ≠ z)
    (hy : y ∈ affineSpan ℝ ({x, z} : Set E))
    (hnc : ¬ Collinear ℝ ({x, z, w} : Set E)) :
    ¬ Collinear ℝ ({x, y, w} : Set E) := by
  sorry

/-! ## aff_gt 上的 azim 不变性与 aff_ge/aff_gt 边界（planarity.hl:12117-12154） -/

/-- HOL planarity.hl :12117-12129 `in_aff_gt_eq_azim`

HOL 原文：
```
!x y z w0 w1:real^3.
~(x=z) /\ y IN aff_gt {x} {z}==> azim x y w0 w1=azim x z w0 w1
```

证明思路：HOL 用 `AFF_GT_1_1` 把 `y ∈ aff_gt {x} {z}` 展开为
`y = u•x + v•z`（`0 < v`、`u+v=1`），即 `y - x = v•(z - x)`（`v>0`）；
再以 `x` 为原点（`GEOM_ORIGIN_TAC`）把轴从 `y-x` 缩放为 `z-x`，最后用
`AZIM_SPECIAL_SCALE`（azim 在轴的正常数缩放下不变）得证。

编码缺口：HOL `AZIM_SPECIAL_SCALE` 未移植；最接近的是
`azim_of_affGt_combo`（Kepler/Text/TopologyFan.lean:824，固定轴、变动第三
自变量，与本定理不同），以及 `azim_master`（Kepler/Geom/Azim.lean:1000）
给出的标架刻画。

候选已有引理：
- `azim_of_affGt_combo`（Kepler/Text/TopologyFan.lean:824）
- `azim_master`（Kepler/Geom/Azim.lean:1000）
- `azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193）
- `affGt`（Kepler/Geom/Aff.lean:39） -/
theorem in_aff_gt_eq_azim (x y z w0 w1 : V3) (hxz : x ≠ z)
    (hy : y ∈ affGt {x} {z}) :
    azim x y w0 w1 = azim x z w0 w1 := by
  sorry

/-- HOL planarity.hl :12130-12154 `no_origin_aff_ge_is_aff_gt`

HOL 原文：
```
!x y z:real^3. 
~(x=y) /\ ~(x=z) /\ z IN aff_ge {x} {y}==> z IN aff_gt {x} {y}
```

证明思路：HOL 用 `AFF_GE_1_1` 展开 `z ∈ aff_ge {x} {y}` 为
`z = t1•x + t2•y`（`0 ≤ t2`、`t1+t2=1`），按 `t2 = 0` 或 `0 < t2` 分情形：
`t2 = 0` 时 `z = x`，与 `~(x=z)` 矛盾；`0 < t2` 时同一组系数（`t2>0`）即
`z ∈ aff_gt {x} {y}`。

编码说明：`~(x=y)` 为 `x ≠ y`，`~(x=z)` 为 `x ≠ z`；
`aff_ge`/`aff_gt` 为 `affGe`/`affGt`。

候选已有引理：
- `mem_affGe_singleton`（Kepler/Text/TopologyFan.lean:2663）
- `affGe_ray`（Kepler/Geom/Aff.lean:196）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `affGt`（Kepler/Geom/Aff.lean:39） -/
theorem no_origin_aff_ge_is_aff_gt (x y z : V3) (hxy : x ≠ y) (hxz : x ≠ z)
    (hz : z ∈ affGe {x} {y}) :
    z ∈ affGt {x} {y} := by
  sorry

/-! ## 邻居集上 azim1 最小元的存在性（planarity.hl:12155-12194） -/

/-- HOL planarity.hl :12155-12194 `exists_edge_component_yfan`

HOL 原文：
```
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (y:real^3).
 FAN(x,V,E) /\ (!v. v IN V==>CARD (set_of_edge v V E) >1) /\ v IN V
/\  ~(y IN set_of_edge v V E) 
==>
(?(w:real^3). (w IN (set_of_edge v V E)) /\
(!(w1:real^3). (w1 IN (set_of_edge v V E)) ==> azim1 x v y w <=  azim1 x v y w1))
```

证明思路：由 `exists_edge_fully_surround_fan` 取 `v' ∈ setOfEdge v V E`，故
邻居集非空；由 `remark_finite_fan1`（经 `FAN` 的 `fan1` 得 `V` 有限）得
`setOfEdge v V E` 有限。对有限非空集用 `Set.exists_min_image`
（HOL 的 `INF_FINITE`）取使 `azim1 x v y` 最小的 `w`，即得。

编码说明：`~(y IN set_of_edge v V E)` 为 `y ∉ setOfEdge v V E`；
HOL `azim1` 为 `azim1`（Kepler/Text/TopologyFan.lean:229）。

候选已有引理：
- `exists_edge_fully_surround_fan`（Kepler/Text/PlanarityDarts.lean:480）
- `exists_inverse_in_orbits`（Kepler/Text/TopologyFan.lean:234，同型最小元构造）
- `remark_finite_fan1`（Kepler/Text/Fan.lean:277）
- `Set.exists_min_image`（Mathlib/Data/Set/...）
- `azim1`（Kepler/Text/TopologyFan.lean:229） -/
theorem exists_edge_component_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v y : V3)
    (hfan : FAN x V E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hv : v ∈ V) (hy : y ∉ setOfEdge v V E) :
    ∃ w : V3, w ∈ setOfEdge v V E ∧
      ∀ w1 : V3, w1 ∈ setOfEdge v V E →
        azim1 x v y w ≤ azim1 x v y w1 := by
  sorry

/-! ## 顶点集含于 xfan 与邻居集含于顶点集（planarity.hl:12195-12217） -/

/-- HOL planarity.hl :12195-12208 `v_subset_xfan`

HOL 原文：
```
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E) /\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==> V SUBSET xfan(x,V,E)
```

证明思路：对任意 `v ∈ V`，由 `exists_edge_fully_surround_fan` 取边
`{v,x'}`；`remark1_fan` 的 `aff_ge` 成员分量（`point_in_aff_ge`）给出
`v ∈ aff_ge {x} {x',v} = aff_ge {x} {v,x'}`，于是 `{v,x'} ∈ E` 见证
`v ∈ xfan x V E`。

候选已有引理：
- `exists_edge_fully_surround_fan`（Kepler/Text/PlanarityDarts.lean:480）
- `point_in_aff_ge`（Kepler/Text/Planarity.lean:4334）
- `xfan`（Kepler/Text/Fan.lean:154） -/
theorem v_subset_xfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    V ⊆ xfan x V E := by
  sorry

/-- HOL planarity.hl :12209-12217 `set_of_edge_subset_edges`

HOL 原文：
```
!(V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3).
 set_of_edge v V E SUBSET V
```

证明思路：直接展开 `setOfEdge v V E = {w | {v,w} ∈ E ∧ w ∈ V}`（HOL
`REWRITE_TAC[set_of_edge]`），第二个合取项即 `w ∈ V`，故任意 `w` 属于该集
蕴含 `w ∈ V`。HOL 收尾 `SET_TAC[]`。

编码说明：HOL `set_of_edge` 为 `setOfEdge`（Kepler/Text/Fan.lean:62）；
HOL 名称虽为 `..._subset_edges`，但结论实为 `⊆ V`，按 HOL 原样保留。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62） -/
theorem set_of_edge_subset_edges (V : Set V3) (E : Set (Set V3)) (v : V3) :
    setOfEdge v V E ⊆ V := by
  sorry

end Kepler.Text
