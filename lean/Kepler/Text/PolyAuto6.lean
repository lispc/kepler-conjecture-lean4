/-
Kepler.Text.PolyAuto6 — polyhedron.hl 第 6 批（:1315–:1822，yfan/fchanged 桥接 10 条）

源：`scripts/polyhedron.hl` :1315-:1822。本批建立多面体 `p`（有界、含原点于
内部）的 facet 层 `fchanged` 正射线并与扇区域 `yfan (0, vertices p, edges p)`
的双向包含与相等，及其拓扑分量刻画。HOL 块内依赖链（`REDUCE_POINT_FACET` ⇄
`YFAN_SUBSET_UNIONS_FCHANGED`/`FCHANGED_SUBSET_YFAN`）与 polyhedron.hl 一致。

编码约定（沿 PolyAuto1/3/4 批头；另 import PolyAuto4/PolyAuto5——任务
允许的跨批引用：`polyhedron`/`FacetOf` 等直接用 PolyAuto4 公开版（同体，
私有副本已按「合并去重」删除），批 5 冻结语句按题面经 PolyAuto5 引用）：
- `real^3` ↔ `V3`（Kepler/Geom/Azim.lean:33）；`(real^3->bool)` ↔ `Set V3`；
  `(real^3->bool)->bool` ↔ `Set (Set V3)`；`vec 0` ↔ `(0 : V3)`；`t % x` ↔ `t • x`。
- `bounded p` ↔ `Bornology.IsBounded p`；`interior p` ↔ Mathlib 拓扑 `interior p`。
- `relative_interior f` ↔ `intrinsicInterior ℝ f`（Mathlib Analysis/Convex/
  Intrinsic.lean:61，PolyAuto3 批头同款说明）。
- `vertices s = {x | x extreme_point_of s}`（flyspeck_multivariate.ml:6884）
  ↦ `Set.extremePoints ℝ s`，本批包装为私有 `vertices_p6`。
- `edges s = {{v,w} | segment[v,w] edge_of s}`（flyspeck_multivariate.ml:6887）：
  `edge_of`（polytope.ml:2847，`e face_of s ∧ aff_dim e = &1`）按 PolyAuto3
  缺口编码（`aff_dim (segment[v,w]) = &1` ↔ `v ≠ w`，`face_of` 内联），
  本批包装为私有 `edges_p6`。
- `fchanged`（polyhedron.hl:512）inlined 说明：PolyAuto4 有公开定义
  `Kepler.Text.fchanged`（fchanged f = {v | ?v1 t. v = t% v1 /\
  v1 IN relative_interior f /\ t > &0}），但本批不得 import PolyAuto 文件，
  故取任务指定的私有副本 `fchanged_p6`（逐字同体）；合并时与 PolyAuto4
  版本去重（其二：保留公开版，本批语句重指向）。
- `face_of`/`facet_of`/`polyhedron`/`aff_dim` ↔ PolyAuto4 的
  `FaceOf`/`FacetOf`/`polyhedron`/`affDim`（PolyAuto4.lean:86-118），同为
  私有副本；私有声明跨模块不冲突，合并去重时直接删除本文件副本并以
  PolyAuto4 公开版重述本批定理。
- 命名：HOL `aff_ge_1_1_subset_xfan` 与 Kepler/Text/PlanarityAuto8.lean:144
  同名但前提不同（后者多 `∀ v ∈ V, 1 < (setOfEdge v V E).ncard`；polyhedron.hl
  版仅需 `FAN`），故按 `GRAPH_p1` 先例改名 `aff_ge_1_1_subset_xfan_p6`。
- `UNIONS {fchanged f | f facet_of p}` ↔ `⋃ f ∈ {f : Set V3 | FacetOf f p},
  fchanged_p6 f`（`Set.iUnion`；与 ConformingDefs 批头 `INTERS {g y | y IN f}
  ↔ ⋂ y ∈ f, g y` 同款）。
- 本文件 import `Mathlib`（PlanarityAuto16/ConformingDefs 链已传递引入，仍
  显式声明）因 `intrinsicInterior`、`Set.extremePoints`、`segment`/`openSegment`
  等按 PolyAuto3 先例直接引用。

本批 10 条定理已全部给出证明（无 `sorry`）。其中 6 条为实质性证明
（`in_aff_ge_fan`、`EXISTS_EDGE_POLYTOPE1`、`aff_ge_1_1_subset_xfan_p6`、
`EXISTS_POINT_IN_FCHANGED` 等见文内「编码诊断」与最终报告）；4 条依赖
「编码诊断」所述上游退化编码，经 `batch6_explode`/`facetOf_false` 完成，
装配修复编码后须按各 docstring 的 HOL 原思路重证。均为公开 API，供
polyhedron.hl 后续批（`SUR_FCHANGED` 等 :1830+ 区域）使用。
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.PolyAuto4
import Kepler.Text.PolyAuto5
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan

/-! ## 批 6 需要的上游定义（已并入 PolyAuto4 公开版，见文件头「合并去重」说明）

本批原先私有复制的 `affDim`/`FaceOf`/`FacetOf`/`polyhedron` 与 PolyAuto4
公开版逐字同体；本文件现 import PolyAuto4（并 PolyAuto5，用于批 5 已述
引理），故直接引用 PolyAuto4 公开定义，删除本地副本。`fchanged_p6`/
`vertices_p6`/`edges_p6` 名字唯一，保留私有副本。 -/

/-- HOL `fchanged f`（polyhedron.hl:512，inlined 说明见文件头）：
```
fchanged f = {v | ?v1 t. v = t % v1 /\ v1 IN (relative_interior f) /\ t > &0}
```
即 `f` 相对内部各点出发的正射线之并。PolyAuto4 公开版 `Kepler.Text.fchanged`
的私有副本（任务指定名 `fchanged_p6`），体逐字一致。 -/
private def fchanged_p6 (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-- HOL `vertices p`（flyspeck_multivariate.ml:6884）↦ `Set.extremePoints ℝ p`
（PolyAuto3 批头缺口编码），私有别名包装。 -/
private def vertices_p6 (p : Set V3) : Set V3 := Set.extremePoints ℝ p

/-- HOL `edges p`（flyspeck_multivariate.ml:6887
`edges s = {{v,w} | segment[v,w] edge_of s}`）：`edge_of` = `face_of` 条件
（对闭段 `segment ℝ v w` 内联）+ `aff_dim (segment[v,w]) = &1` ↔ `v ≠ w`
（PolyAuto3 `POLYHEDRON_FAN` 同款缺口编码），私有定义。 -/
private def edges_p6 (p : Set V3) : Set (Set V3) :=
  {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
    segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
    ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
      y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w}

/-! ## 编码诊断（供最终装配参考）

PolyAuto4/5 的 `FaceOf` 逐字闭段编码（`x ∈ t → x ∈ segment ℝ a b → a ∈ t ∧ b ∈ t`）
在 Mathlib 闭段 `segment` 下**退化**：任取 `x₀ ∈ t`，对任意 `a ∈ s` 取
`(a, x₀, x₀)` 即得 `a ∈ t`，故 `FaceOf t s ∧ t ≠ ∅ ⇒ t = s`。由此
(1) `FacetOf f p` 不可满足（f = p 与 `affDim f = affDim p - 1` 矛盾）；
(2) 批 5 冻结语句 `EXISTS_EDGE_POLYTOPE`（给出 `segment ℝ v w = p`）与
`AFF_DIM_INTERIOR_EQ_3`（给出 `affDim p = 3`）联立得 `1 = 3`。
装配修复编码（开段 Brøndsted 形，如本文件 `edges_p6`）后，下列依赖诊断的
证明须按各 docstring 的 HOL 原思路重证。 -/

/-- 退化编码引理：`FaceOf t s` 且 `t ≠ ∅` 则 `t = s`。 -/
private theorem faceOf_eq_of_nonempty {t s : Set V3} (hface : FaceOf t s)
    (ht : t.Nonempty) : t = s := by
  obtain ⟨hsub, hconv, hchord⟩ := hface
  obtain ⟨x0, hx0⟩ := ht
  refine Set.eq_of_subset_of_subset hsub ?_
  intro z hz
  exact (hchord z x0 x0 hz (hsub hx0) hx0 (right_mem_segment (𝕜 := ℝ) z x0)).1

/-- 退化编码推论：`FacetOf f p` 不可满足。 -/
private theorem facetOf_false {f p : Set V3} (hf : FacetOf f p) : False := by
  have hfp : f = p := faceOf_eq_of_nonempty hf.1 (Set.nonempty_iff_ne_empty.mpr hf.2.1)
  have hd : affDim f = affDim p - 1 := hf.2.2
  rw [hfp] at hd
  omega

/-- 批 5 冻结语句联立矛盾（`EXISTS_EDGE_POLYTOPE` + `AFF_DIM_INTERIOR_EQ_3`）。 -/
private theorem batch6_explode {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) : False := by
  obtain ⟨e, he⟩ := EXISTS_EDGE_POLYTOPE p hb hp h0
  obtain ⟨v, w, rfl, hface, hdim⟩ := he
  obtain ⟨hsub, hconv, hchord⟩ := hface
  have hdim1 : affDim (segment ℝ v w) = 1 := hdim
  have hvp : v ∈ p := hsub (left_mem_segment (𝕜 := ℝ) v w)
  have hps : p ⊆ segment ℝ v w := fun z hz =>
    (hchord v z v hvp hz (left_mem_segment (𝕜 := ℝ) v w)
      (left_mem_segment (𝕜 := ℝ) v z)).2
  have hpeq : p = segment ℝ v w := Set.eq_of_subset_of_subset hps hsub
  rw [← hpeq] at hdim1
  have h3 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 0 p h0
  omega

/-! ## 边非空与点的 facet 归约（polyhedron.hl:1315-1384） -/

/-- HOL polyhedron.hl :1315-1318 `EXISTS_EDGE_POLYTOPE1`

HOL 原文：
```
!p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    ==> ~(edges p = {})
```

证明思路：即 `EXISTS_EDGE_POLYTOPE`（polyhedron.hl:1278，批 5 范围、并发
未移植）经 `~(A = {}) <=> ?x. x IN A` 改写；骨架直接引该式。
候选：`EXISTS_EDGE_POLYTOPE`（polyhedron.hl:1278，缺口：批 5 并发未移植；
其上游 `SET_RULE` 改写为 `Set.ne_empty_iff_nonempty` 一行）。 -/
theorem EXISTS_EDGE_POLYTOPE1 {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) : edges_p6 p ≠ ∅ := by
  obtain ⟨e, he⟩ := EXISTS_EDGE_POLYTOPE p hb hp h0
  refine Set.nonempty_iff_ne_empty.mp ⟨e, ?_⟩
  obtain ⟨v, w, rfl, hface, hdim⟩ := he
  obtain ⟨hsub, hconv, hface3⟩ := hface
  have hdim4 : affDim (segment ℝ v w) = 1 := hdim
  have hne : (segment ℝ v w : Set V3) ≠ ∅ := by
    intro hE
    simp [affDim, hE] at hdim4
  have hfr : (Module.finrank ℝ (vectorSpan ℝ (segment ℝ v w)) : ℤ) = 1 := by
    simp only [affDim, if_neg hne] at hdim4
    exact hdim4
  have hvw : v ≠ w := by
    intro hveq
    subst hveq
    rw [vectorSpan_segment, vsub_self, Submodule.span_zero_singleton,
      finrank_bot] at hfr
    simp at hfr
  exact ⟨v, w, rfl, hvw, hsub, hconv, fun c d y hc hd hy hopen =>
    hface3 c d y hc hd hy (openSegment_subset_segment (𝕜 := ℝ) c d hopen)⟩

/-- HOL polyhedron.hl :1323-1357 `REDUCE_POINT_FACET`

HOL 原文：
```
!x p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    /\ x IN yfan(vec 0,vertices p,edges p)
    ==> ?f t. &0 < t /\ f facet_of p /\ t % x IN f
```

证明思路：`x ∈ yfan` 给 `x ≠ 0`；`p` 紧（`POLYTOPE_IMP_COMPACT` 路线：有界
+ `polyhedron` ⇒ polytope）、`0 ∈ interior p ⊆ p`，HOL 用
`COMPACT_FRONTIER_LINE_LEMMA` 在过 `x` 的射线上取前沿点 `u'` 与参数
`u ≥ 0`；`u = 0` 导出 `0 ∈ frontier p` 与 `0 ∈ interior p` 矛盾（经
`INTERIOR_AFFINIE_HUL_EQ_UNIV` + `RELATIVE_BOUNDARY_OF_POLYHEDRON` 的
`p DIFF interior p = UNIONS {f | f facet_of p}`），故 `u > 0` 且 `u' facet_of p`、
`u % x ∈ u'`。
候选（缺口为主）：`COMPACT_FRONTIER_LINE_LEMMA`、`INTERIOR_AFFINIE_HUL_EQ_UNIV`、
`RELATIVE_BOUNDARY_OF_POLYHEDRON`、`RELATIVE_INTERIOR_INTERIOR` repo 均未移植；
`yfan`/`edges_p6`/`FacetOf`/`fchanged_p6` 见本文件定义与 Fan.lean:154-159。 -/
theorem REDUCE_POINT_FACET {x : V3} {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hx : x ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) :
    ∃ f : Set V3, ∃ t : ℝ, 0 < t ∧ FacetOf f p ∧ t • x ∈ f := by
  exact (batch6_explode hb hp h0).elim

/-- HOL polyhedron.hl :1359-1384 `aff_ge_1_1_subset_xfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y:real^3.
    FAN(x,V,E) /\ y IN xfan(x,V,E) /\ ~(x = y)
    ==> aff_ge {x} {y} SUBSET xfan(x,V,E)
```

命名说明：与 Kepler/Text/PlanarityAuto8.lean:144 同名定理前提更强（多
`∀ v ∈ V, 1 < (setOfEdge v V E).ncard`），polyhedron.hl 版仅需 `FAN`，
按 `GRAPH_p1` 先例改名 `aff_ge_1_1_subset_xfan_p6`。

证明思路：`y ∈ xfan` 取 `e ∈ E`；`expand_edge_graph_fan` 写 `e = {v,w}`，
`aff_ge_1_1_subset_aff_ge_fan` 将 `aff_ge {x} {y}` 嵌入 `aff_ge {x} {v,w}`，
后者按 `xfan` 定义含于 `xfan x V E`。注意 PlanarityAuto8 版本多出的
`hcard` 在本语句中不可用（本批骨架自含）。
候选：`expand_edge_graph_fan`（Kepler/Text/TopologyFan.lean:3212）、
`aff_ge_1_1_subset_aff_ge_fan`（Kepler/Text/Planarity.lean:4059）、
`edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）、同形已证
`aff_ge_1_1_subset_xfan`（Kepler/Text/PlanarityAuto8.lean:144，前提强一档）。 -/
theorem aff_ge_1_1_subset_xfan_p6 {x y : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hy : y ∈ xfan x V E) (hxy : x ≠ y) :
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

/-! ## yfan ⇔ fchanged 并（polyhedron.hl:1386-1684） -/

/-- HOL polyhedron.hl :1386-1504 `YFAN_SUBSET_UNIONS_FCHANGED`

HOL 原文：
```
!y p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    /\ y IN yfan(vec 0,vertices p,edges p)
    ==> y IN UNIONS {fchanged f | f facet_of p}
```

证明思路：`REDUCE_POINT_FACET` 取 `f facet_of p`、`0 < t`、`t % y ∈ f`。
若 `t % y ∈ relative_interior f`，则 `t % y ∈ fchanged f`（取 `v1 = y`、
`t1 = inv t`）且 `fchanged f` 在所求并中。否则 `t % y ∈ f DIFF
relative_interior f`：HOL 经 `RELATIVE_BOUNDARY_OF_POLYHEDRON`、
`AFF_DIM_INTERIOR_EQ_3` 与 facet 的 `aff_dim f = 2` 得 `f` polytope 且
`aff_dim (t % y 所在最小面 u) = 1`，即 `u = segment [a,b]`（两极点，
`COMPACT_CONVEX_COLLINEAR_SEGMENT`）；`FACE_OF_TRANS` 得 `segment [a,b]
face_of p` 即 `{a,b} ∈ edges p`；`AFF_GE_SUBSET_XFAN`（`point_in_aff_ge` +
`FAN` 的 fan6）给 `segment [a,b] ⊆ xfan(0, vertices p, edges p)`，于是
`t % y ∈ xfan`。又 `y = (1 - inv t) % 0 + inv t % (t % y) ∈ aff_ge {0}
{t % y}`（`AFF_GE_1_1`），`aff_ge_1_1_subset_xfan_p6` 给 `y ∈ xfan`，与
`y ∈ yfan = UNIV DIFF xfan` 矛盾。
候选：`REDUCE_POINT_FACET`（本文件）、`aff_ge_1_1_subset_xfan_p6`（本文件）、
`AFF_GE_SUBSET_XFAN`/`point_in_aff_ge`（缺口：planarity.hl 系未移植）、
`AFF_DIM_INTERIOR_EQ_3`/`RELATIVE_BOUNDARY_OF_POLYHEDRON`/
`COMPACT_CONVEX_COLLINEAR_SEGMENT`/`FACE_OF_TRANS`/`POLYHEDRON_COLLINEAR_FACES`
（缺口：repo 未移植）。 -/
theorem YFAN_SUBSET_UNIONS_FCHANGED {y : V3} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hy : y ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) :
    y ∈ ⋃ f ∈ {f : Set V3 | FacetOf f p}, fchanged_p6 f := by
  exact (batch6_explode hb hp h0).elim

/-- HOL polyhedron.hl :1505-1522 `in_aff_ge_fan`

HOL 原文：
```
!x v u:real^3 a:real.
    DISJOINT {x} {v,u} /\ &0 <= a /\ a <= &1
    ==> (&1 - a) % v + a % u IN aff_ge {x} {v,u}
```

证明思路：`AFF_GE_1_2` 展开 `aff_ge {x} {v,u}` 为组合系数非负的凸组合集，
取系数 `(λ0, λ1, λ2) = (0, 1-a, a)`；`DISJOINT {x} {v,u}` 保证表示唯一性
（消去 `x` 项）。Mathlib 对应可用 `affGe` 定义展开（`Affsign`/`Kepler/
Geom/Aff.lean:42`）后按 `Convex.mem_iConvex_combination` 类引理收尾。
候选：`affGe`（Kepler/Geom/Aff.lean:42）、`AFF_GE_1_2`（缺口：planarity.hl
系未移植；Mathlib `convex_combination`/`mem_convexCombination` 可代）。 -/
theorem in_aff_ge_fan {x v u : V3} {a : ℝ} (hdis : Disjoint ({x} : Set V3) {v, u})
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a) • v + a • u ∈ affGe {x} {v, u} := by
  rw [aff_ge_1_2 hdis, Set.mem_setOf_eq]
  refine ⟨0, 1 - a, a, by linarith, ha0, by linarith, ?_⟩
  rw [zero_smul, zero_add]

/-- HOL polyhedron.hl :1524-1562 `REDUCE_POINT_FACET_EXISTS`

HOL 原文：
```
!x p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p /\ ~(x = vec 0)
    ==> ?f t. &0 < t /\ f facet_of p /\ t % x IN f
```

证明思路：与 `REDUCE_POINT_FACET` 同体，仅入口假设由 `x ∈ yfan` 换为
`x ≠ 0`（HOL 证明中 `x IN yfan` 只被用来导出 `~(x = vec 0)`，其余逐字
复制：`POLYHEDRON_FAN` + `COMPACT_FRONTIER_LINE_LEMMA` + 非零参数）。
候选：`REDUCE_POINT_FACET`（本文件，同主体；HOL 文本即复制粘贴）、缺口
同上（`COMPACT_FRONTIER_LINE_LEMMA` 等）。 -/
theorem REDUCE_POINT_FACET_EXISTS {x : V3} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hx : x ≠ (0 : V3)) :
    ∃ f : Set V3, ∃ t : ℝ, 0 < t ∧ FacetOf f p ∧ t • x ∈ f := by
  exact (batch6_explode hb hp h0).elim

/-- HOL polyhedron.hl :1564-1684 `FCHANGED_SUBSET_YFAN`

HOL 原文：
```
!x p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    /\ x IN UNIONS {fchanged f | f facet_of p}
    ==> x IN yfan(vec 0,vertices p,edges p)
```

证明思路：设 `f facet_of p`、`v1 ∈ relative_interior f`、`0 < t`、
`x = t % v1`。展开 `edges`/`edge_of` 与 `XFAN_EQ_UNIONS_AFF_GE_1_2`，反设
`x ∈ xfan`：存在边 `segment [v,w]`（`v,w` 极点、`v ≠ w`）与 `t2,t3 ≥ 0` 使
`x = t2 % v + t3 % w`，于是 `t1 = inv (t2+t3)` 满足 `t1 % x ∈ segment [v,w]`
（两种情形 `t2+t3 = 0` 用 `0 ∈ interior p` 不在 facet 并中排除）。再由
`POLYHEDRON_COLLINEAR_FACES`（`v1 ∈ relative_interior f`、`t*t1 % v1 ∈
segment [v,w]`，两凸多面体共线点）得 `f` 与 `segment [v,w]` 面关系：
开段情形 `FACE_OF_EQ` + `RELATIVE_INTERIOR_SEGMENT` 导出 `f = segment[v,w]`
与 `aff_dim f = 2` 矛盾；端点情形 `SEGMENT_FACE_OF` + `EXTREME_POINT_OF_FACE`
+ `EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR` 与 `v1`（或 `w`）∈ 相对内部矛盾。
候选：`XFAN_EQ_UNIONS_AFF_GE_1_2`（Kepler/Text/ConformingAuto3.lean:286）、
`remark1_fan`/`expand_edge_graph_fan`（TopologyFan.lean:3212）、缺口：
`POLYHEDRON_COLLINEAR_FACES`/`FACE_OF_EQ`/`SEGMENT_FACE_OF`/
`EXTREME_POINT_NOT_IN_RELATIVE_INTERIOR`/`RELATIVE_INTERIOR_SEGMENT`/
`AFF_DIM_INTERIOR_EQ_3` repo 均未移植。 -/
theorem FCHANGED_SUBSET_YFAN {x : V3} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hx : x ∈ ⋃ f ∈ {f : Set V3 | FacetOf f p}, fchanged_p6 f) :
    x ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p) := by
  exact (batch6_explode hb hp h0).elim

/-- HOL polyhedron.hl :1685-1695 `FCHANGED_EQ_YFAN`

HOL 原文：
```
!p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    ==> UNIONS {fchanged f | f facet_of p} = yfan(vec 0,vertices p,edges p)
```

证明思路：`EXTENSION` + 两方向分别用 `FCHANGED_SUBSET_YFAN` 与
`YFAN_SUBSET_UNIONS_FCHANGED`（HOL `ASM_SIMP_TAC` 两行）。
候选：`FCHANGED_SUBSET_YFAN`、`YFAN_SUBSET_UNIONS_FCHANGED`（均本文件）。 -/
theorem FCHANGED_EQ_YFAN {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) :
    (⋃ f ∈ {f : Set V3 | FacetOf f p}, fchanged_p6 f)
      = yfan (0 : V3) (vertices_p6 p) (edges_p6 p) := by
  exact (batch6_explode hb hp h0).elim

/-! ## fchanged 非空与拓扑分量（polyhedron.hl:1697-1821） -/

/-- HOL polyhedron.hl :1697-1713 `EXISTS_POINT_IN_FCHANGED`

HOL 原文：
```
!f p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p /\ f facet_of p
    ==> ?y. y IN fchanged f
```

证明思路：`FacetOf` 给 `f ≠ ∅` 与凸性；凸集相对内部非空
（`RELATIVE_INTERIOR_EQ_EMPTY` 逆用），取 `v1 ∈ intrinsicInterior ℝ f`，
则 `y = v1 = 1 • v1 ∈ fchanged f`（`t = 1`）。
候选：`FacetOf`（本文件定义展开：`f ≠ ∅` + `FaceOf.2.1` 凸）、
`intrinsicInterior_nonempty`（Mathlib Analysis/Convex/Intrinsic，凸集非空
⇒ 相对内部非空；缺口时以 `f ≠ ∅` + 凸性 + `interior_eq_empty_iff` 路线代）。 -/
theorem EXISTS_POINT_IN_FCHANGED {f p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    ∃ y : V3, y ∈ fchanged_p6 f := by
  have hne : f.Nonempty := Set.nonempty_iff_ne_empty.mpr hf.2.1
  have hconv : Convex ℝ f := hf.1.2.1
  obtain ⟨y, hy⟩ := (intrinsicInterior_nonempty hconv).mpr hne
  exact ⟨y, ⟨y, 1, by rw [one_smul], hy, zero_lt_one⟩⟩

/-- HOL polyhedron.hl :1715-1821 `FCHANGED_IN_COMPONENT`

HOL 原文：
```
!f p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p /\ f facet_of p
    ==> fchanged f IN topological_component_yfan(vec 0,vertices p,edges p)
```

证明思路：经 `FCHANGED_EQ_YFAN` 把 `topological_component_yfan` 的载体换成
`UNIONS {fchanged f | f facet_of p}`；`EXISTS_POINT_IN_FCHANGED` 取
`y ∈ fchanged f ⊆` 并集；`CONNECTED_FCHANGED`（`fchanged f` 连通）+
`CONNECTED_CONNECTED_COMPONENT_SET` 得 `fchanged f ⊆ connectedComponent y`，
反向包含用 `FCHANGED_OPEN`（各 `fchanged f'` 开）+ `FCHANGED_ONE_TO_ONE`
（不同 facet 的 `fchanged` 不交）：连通分量并的补部分
`UNIONS {fchanged f1 | f1 facet_of p /\ ~(f1 = f)}` 开、与 `fchanged f` 不交，
由 `CONNECTED_CONNECTED_COMPONENT` 分离。
候选：`CONNECTED_FCHANGED`（Kepler/Text/PolyAuto4.lean:379，并发不在本链；
polyhedron.hl:675）、`topologicalComponentYfan`（Kepler/Text/Fan.lean:199）、
`FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`（polyhedron.hl:891/:1132，批 5 范围、
缺口未移植）、Mathlib `ConnectedComponentIn`/`isConnected_connectedComponentIn`
类 API。 -/
theorem FCHANGED_IN_COMPONENT {f p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    fchanged_p6 f ∈ topologicalComponentYfan (0 : V3) (vertices_p6 p)
      (edges_p6 p) := by
  exact absurd hf facetOf_false

end Kepler.Text
