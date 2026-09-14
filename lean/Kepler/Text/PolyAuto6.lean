/-
Kepler.Text.PolyAuto6 — polyhedron.hl 第 6 批（:1315–:1822，yfan/fchanged 桥接 10 条）

源：`scripts/polyhedron.hl` :1315-:1822。本批建立多面体 `p`（有界、含原点于
内部）的 facet 层 `fchanged` 正射线并与扇区域 `yfan (0, vertices p, edges p)`
的双向包含与相等，及其拓扑分量刻画。HOL 块内依赖链（`REDUCE_POINT_FACET` ⇄
`YFAN_SUBSET_UNIONS_FCHANGED`/`FCHANGED_SUBSET_YFAN`）与 polyhedron.hl 一致。

编码约定（沿 PolyAuto1/3/4 批头；import `Kepler.Text.Polytope`（canonical
公开定义与 kit，开段 Brøndsted 形 `FaceOf`）与 `Kepler.Text.PolyAuto5`
（批 5 引理 `EXISTS_EDGE_POLYTOPE`/`FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`/
`AFF_DIM_INTERIOR_EQ_3`/`INTERIOR_AFFINIE_HUL_EQ_UNIV` 等）。注意本批不得
import `Kepler.Text.PolyAuto4`：其私有 `FaceOf`/`FacetOf`/`affDim`/
`polyhedron`/`fchanged` 与 Polytope 公开版同名，同环境 import 触发
duplicate-declaration 错误（`Kepler.Text.FacetOf from Kepler.Text.PolyAuto4`），
故全部引用 Polytope 公开版；批 4 引理（`CONNECTED_FCHANGED` 等，本批
`FCHANGED_IN_COMPONENT` 需要）按公开版编码在本批就地私有重述）：
- `real^3` ↔ `V3`（Kepler/Geom/Azim.lean:33）；`(real^3->bool)` ↔ `Set V3`；
  `(real^3->bool)->bool` ↔ `Set (Set V3)`；`vec 0` ↔ `(0 : V3)`；`t % x` ↔ `t • x`。
- `bounded p` ↔ `Bornology.IsBounded p`；`interior p` ↔ Mathlib 拓扑 `interior p`。
- `relative_interior f` ↔ `intrinsicInterior ℝ f`（Mathlib Analysis/Convex/
  Intrinsic.lean:61）。
- `vertices s = {x | x extreme_point_of s}`（flyspeck_multivariate.ml:6884）
  ↦ `Set.extremePoints ℝ s`，本批包装为私有 `vertices_p6`。
- `edges s = {{v,w} | segment[v,w] edge_of s}`（flyspeck_multivariate.ml:6887）：
  与 Polytope 公开 `edges`/`edgeOf`（开段弦性质 + 闭段载体）逐字同体的内联
  编码，本批包装为私有 `edges_p6`。
- `face_of`/`facet_of`/`polyhedron`/`aff_dim`/`fchanged` ↔ Polytope 公开版
  （合并去重：本批无私有副本，语句直接用公开版；私有 `fchanged_p6` 仅供
  冻结语句引用，与公开 `fchanged` 逐字同体，`rfl` 互转）。
- 命名：HOL `aff_ge_1_1_subset_xfan` 与 Kepler/Text/PlanarityAuto8.lean:144
  同名但前提不同（后者多 `∀ v ∈ V, 1 < (setOfEdge v V E).ncard`；polyhedron.hl
  版仅需 `FAN`），故按 `GRAPH_p1` 先例改名 `aff_ge_1_1_subset_xfan_p6`。
- `UNIONS {fchanged f | f facet_of p}` ↔ `⋃ f ∈ {f : Set V3 | FacetOf f p},
  fchanged_p6 f`（`Set.iUnion`）。
- 本文件 import `Mathlib`（显式声明）因 `intrinsicInterior`、`Set.extremePoints`、
  `segment`/`openSegment` 等按 PolyAuto3 先例直接引用。

本批 10 条定理全部诚实证明（无 `sorry`、无退化编码技巧）。早期版本中 6 条
依赖旧闭段 `FaceOf` 的退化编码（`batch6_explode`/`facetOf_false`，随闭段
编码一起删除），现按各 docstring 的 HOL 原思路重证：射线上取极大参数
（`COMPACT_FRONTIER_LINE_LEMMA` 路线，就地紧性论证）、
`RELATIVE_BOUNDARY_OF_POLYHEDRON` 路线的 `RELATIVE_INTERIOR_OF_POLYHEDRON`
（Polytope.lean:1793，rint = s \ ⋃₀ facets）、facet 边界点归约到 edge 的
1 维面=闭段引理（就地证明）、`POLYHEDRON_COLLINEAR_FACES_STRONG`
（Polytope.lean:2309）+ `FACE_OF_EQ` + 维数矛盾，以及批 4 中心定理
`CONNECTED_FCHANGED` 的分量拼链。均为公开 API，供 polyhedron.hl 后续批
（`SUR_FCHANGED` 等 :1830+ 区域）使用。
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.Polytope
import Kepler.Text.PolyAuto5
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan

/-! ## 批 6 需要的上游定义

`affDim`/`FaceOf`/`FacetOf`/`edgeOf`/`edges`/`polyhedron`/`fchanged` 均为
Polytope 公开版（本文件 import 之）。`fchanged_p6`/`vertices_p6`/`edges_p6`
名字唯一，保留私有副本（冻结语句引用）。 -/

/-- HOL `fchanged f`（polyhedron.hl:512，inlined 说明见文件头）：
```
fchanged f = {v | ?v1 t. v = t % v1 /\ v1 IN (relative_interior f) /\ t > &0}
```
即 `f` 相对内部各点出发的正射线之并。Polytope 公开版 `Kepler.Text.fchanged`
的私有副本（任务指定名 `fchanged_p6`），体逐字一致。 -/
private def fchanged_p6 (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-- HOL `vertices p`（flyspeck_multivariate.ml:6884）↦ `Set.extremePoints ℝ p`
（PolyAuto3 批头缺口编码），私有别名包装。 -/
private def vertices_p6 (p : Set V3) : Set V3 := Set.extremePoints ℝ p

/-- HOL `edges p`（flyspeck_multivariate.ml:6887
`edges s = {{v,w} | segment[v,w] edge_of s}`）：`edge_of` = `face_of` 条件
（Polytope 开段编码内联）+ 闭段载体，私有定义（= Polytope 公开 `edges`
的逐字内联展开）。 -/
private def edges_p6 (p : Set V3) : Set (Set V3) :=
  {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
    segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
    ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
      y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w}

/-! ## 批 6 私有辅助引理（全部诚实证明；替代旧退化编码 helper） -/

/-- 闭段成员的组合刻画（Mathlib `segment` 定义本身，`Iff.rfl`）。 -/
private theorem mem_segment_pair {a b z : V3} :
    z ∈ segment ℝ a b ↔ ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 ∧ u • a + v • b = z :=
  Iff.rfl

/-- `aff_ge {x} {v}` 的射线入元（构造方向；`affGe_ray` 的对偶）。 -/
private theorem affGe_ray_intro {x v y : V3} (hxv : x ≠ v) {c : ℝ} (hc : 0 ≤ c)
    (hy : y = x + c • (v - x)) : y ∈ affGe {x} {v} := by
  have hfin : ({x} ∪ {v} : Set V3).Finite :=
    (Set.finite_singleton x).union (Set.finite_singleton v)
  refine ⟨fun w => if w = v then c else 1 - c, hfin, ?_, ?_, ?_⟩
  · rw [sum_insert_single_v hfin hxv, if_neg hxv, if_pos (rfl : v = v)]
    rw [hy]
    module
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    show (0:ℝ) ≤ if w = w then c else 1 - c
    rw [if_pos rfl]
    exact hc
  · rw [sum_insert_single_s hfin hxv, if_neg hxv, if_pos (rfl : v = v)]
    ring

/-- `edges_p6` 的进入引理：闭段是 `p` 的面 ⇒ `{v,w} ∈ edges_p6 p`。 -/
private theorem mem_edges_p6_intro {p : Set V3} {v w : V3} (hvw : v ≠ w)
    (hface : FaceOf (segment ℝ v w) p) : ({v, w} : Set V3) ∈ edges_p6 p :=
  Set.mem_setOf_eq.mpr ⟨v, w, rfl, hvw, hface.1, hface.2.1, hface.2.2⟩

/-- `edges_p6` 的退出引理：元素必为 `{v,w}` 且闭段是 `p` 的面。 -/
private theorem mem_edges_p6_face {p e : Set V3} (he : e ∈ edges_p6 p) :
    ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧ FaceOf (segment ℝ v w) p := by
  obtain ⟨v, w, rfl, hvw, hsub, hconv, hchord⟩ := he
  exact ⟨v, w, rfl, hvw, ⟨hsub, hconv, hchord⟩⟩

/-- 原点属于 `xfan`：只要 `edges_p6 p` 非空（`aff_ge {0} {v,w}` 总含原点：
系数 `f 0 = 1`、`f v = f w = 0`，无需互异）。 -/
private theorem zero_mem_xfan_of_ne_edges {p : Set V3} (hne : edges_p6 p ≠ ∅) :
    (0 : V3) ∈ xfan (0 : V3) (vertices_p6 p) (edges_p6 p) := by
  obtain ⟨e, heE⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨v, w, rfl, -, -⟩ := mem_edges_p6_face heE
  refine ⟨{v, w}, heE, ?_⟩
  have hK : ({(0 : V3)} ∪ {v, w} : Set V3).Finite :=
    (Set.finite_singleton (0 : V3)).union ((Set.finite_singleton w).insert v)
  refine ⟨fun z => if z = (0 : V3) then (1 : ℝ) else 0, hK, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single_of_mem (0 : V3) (by simp)
      (fun a _ ha => by
        beta_reduce
        rw [if_neg ha, zero_smul])]
    simp
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · by_cases hz0 : z = 0 <;> simp [hz0]
    · by_cases hz0 : z = 0 <;> simp [hz0]
  · rw [Finset.sum_eq_single_of_mem (0 : V3) (by simp)
      (fun a _ ha => by
        beta_reduce
        exact if_neg ha)]
    simp

/-- 内部点不是极点（`0` 的对称扰动）。 -/
private theorem interior_not_extremePoint {p : Set V3} (h0 : (0 : V3) ∈ interior p) :
    (0 : V3) ∉ Set.extremePoints ℝ p := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (0 : V3) h0
  have hbp : ∀ z ∈ Metric.ball (0 : V3) ε, z ∈ p := fun z hz => interior_subset (hball hz)
  intro hext
  obtain ⟨a, b, hab⟩ : ∃ a b : V3, a ≠ b := exists_pair_ne V3
  have hd0 : a - b ≠ 0 := sub_ne_zero.2 hab
  have hnorm : (0:ℝ) < ‖a - b‖ := norm_pos_iff.mpr hd0
  have hcn : (0:ℝ) < ε / (2 * ‖a - b‖) := by
    refine div_pos hε ?_
    linarith
  have hscal : (ε / (2 * ‖a - b‖)) * ‖a - b‖ = ε / 2 := by
    rw [div_mul_eq_mul_div]
    field_simp
  have hscal2 : (ε / (2 * ‖a - b‖)) * ‖b - a‖ = ε / 2 := by
    rw [div_mul_eq_mul_div, norm_sub_rev]
    field_simp
  have hy : (ε / (2 * ‖a - b‖)) • (a - b) ∈ p := by
    refine hbp _ ?_
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hcn, hscal]
    linarith
  have hz : (ε / (2 * ‖a - b‖)) • (b - a) ∈ p := by
    refine hbp _ ?_
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hcn, hscal2]
    linarith
  have hy0 : (ε / (2 * ‖a - b‖)) • (a - b) ≠ (0 : V3) := by
    intro hc
    rcases smul_eq_zero.mp hc with h | h
    · exact hcn.ne' h
    · exact hd0 h
  have hz0 : (ε / (2 * ‖a - b‖)) • (b - a) ≠ (0 : V3) := by
    intro hc
    rcases smul_eq_zero.mp hc with h | h
    · exact hcn.ne' h
    · exact hd0 (by rw [sub_eq_zero.mp h]; exact sub_self a)
  rw [mem_extremePoints_iff_forall_segment] at hext
  have hmem : (0 : V3) ∈ segment ℝ ((ε / (2 * ‖a - b‖)) • (a - b))
      ((ε / (2 * ‖a - b‖)) • (b - a)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have hcontra := hext.2 ((ε / (2 * ‖a - b‖)) • (a - b)) hy
      ((ε / (2 * ‖a - b‖)) • (b - a)) hz hmem
  exact hz0 (hcontra.resolve_left hy0)

/-- 0 维非空凸集是单点。 -/
private theorem singleton_of_affDim_zero {g : Set V3} (hne : g.Nonempty)
    (hd : affDim g = 0) : ∃ a : V3, g = {a} := by
  obtain ⟨a, ha⟩ := id hne
  refine ⟨a, Set.eq_singleton_iff_unique_mem.2 ⟨ha, fun y hy => ?_⟩⟩
  have hfr : (Module.finrank ℝ (vectorSpan ℝ g) : ℤ) = 0 := by
    have h2 : affDim g = ((Module.finrank ℝ (vectorSpan ℝ g) : ℕ) : ℤ) :=
      if_neg (Set.nonempty_iff_ne_empty.mp hne)
    omega
  have hvsub : y - a ∈ vectorSpan ℝ g := vsub_mem_vectorSpan ℝ hy ha
  have hfrN : Module.finrank ℝ (vectorSpan ℝ g) = 0 := by exact_mod_cast hfr
  rw [Submodule.finrank_eq_zero.mp hfrN] at hvsub
  have hzero : y - a = 0 := by simpa using hvsub
  exact sub_eq_zero.mp hzero

/-- 1 维闭凸集（多面体的 1 维面）是闭段。 -/
private theorem segment_of_affDim_one {g : Set V3} (hcv : Convex ℝ g) (hcl : IsClosed g)
    (hbd : Bornology.IsBounded g) (hne : g.Nonempty) (hd : affDim g = 1) :
    ∃ a b : V3, a ≠ b ∧ g = segment ℝ a b := by
  obtain ⟨a₀, ha₀⟩ := id hne
  have hne' : g ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
  have hfr : (Module.finrank ℝ (vectorSpan ℝ g) : ℤ) = 1 := by
    have h2 : affDim g = ((Module.finrank ℝ (vectorSpan ℝ g) : ℕ) : ℤ) := if_neg hne'
    omega
  have hfrN : Module.finrank ℝ (vectorSpan ℝ g) = 1 := by exact_mod_cast hfr
  obtain ⟨z₀, hz₀g, hz₀a⟩ : ∃ z ∈ g, z ≠ a₀ := by
    by_contra hcon
    push_neg at hcon
    have hgsing : g = {a₀} := Set.eq_singleton_iff_unique_mem.2 ⟨ha₀, hcon⟩
    rw [hgsing, affDim_singleton] at hd
    omega
  obtain ⟨d, hd0, hdV⟩ : ∃ d : V3, d ≠ 0 ∧ d ∈ vectorSpan ℝ g :=
    ⟨z₀ - a₀, sub_ne_zero.2 hz₀a, vsub_mem_vectorSpan ℝ hz₀g ha₀⟩
  have hle : (ℝ ∙ d) ≤ vectorSpan ℝ g :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hdV)
  have hfrD : Module.finrank ℝ (ℝ ∙ d) = 1 := finrank_span_singleton hd0
  have heq : ℝ ∙ d = vectorSpan ℝ g :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hfrD]; exact hfrN.le)
  have hmem : ∀ z ∈ g, ∃ c : ℝ, z = a₀ + c • d := by
    intro z hz
    have hv : z - a₀ ∈ vectorSpan ℝ g := vsub_mem_vectorSpan ℝ hz ha₀
    rw [← heq] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨c, ?_⟩
    rw [hc]
    module
  set S : Set ℝ := {t : ℝ | a₀ + t • d ∈ g} with hSdef
  have hScl : IsClosed S :=
    hcl.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hSne : S.Nonempty := ⟨0, by rw [hSdef]; simpa using ha₀⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff_subset_ball (0 : V3) |>.mp hbd
  have hdn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd0
  have hSbd : Bornology.IsBounded S := by
    refine Metric.isBounded_iff_subset_ball 0 |>.2 ⟨2 * C / ‖d‖ + 1, ?_⟩
    rintro t ht
    have h2 : dist (a₀ + t • d : V3) (0 : V3) < C := hC ht
    rw [dist_zero_right] at h2
    have h3 : dist (a₀ : V3) (0 : V3) < C := hC ha₀
    rw [dist_zero_right] at h3
    have h4 : |t| * ‖d‖ ≤ ‖(a₀ + t • d : V3)‖ + ‖(a₀ : V3)‖ := by
      have h41 : |t| * ‖d‖ = ‖(t • d : V3)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have h42 : ‖(t • d : V3)‖ = ‖(a₀ + t • d : V3) - (a₀ : V3)‖ := by
        rw [add_sub_cancel_left]
      rw [h41, h42]
      exact norm_sub_le (a₀ + t • d) (a₀ : V3)
    have h6 : |t| < 2 * C / ‖d‖ := by
      rw [lt_div_iff₀ hdn]
      linarith
    show dist (t : ℝ) 0 < 2 * C / ‖d‖ + 1
    rw [Real.dist_eq, sub_zero]
    linarith
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSbd
  obtain ⟨α, hαS, hαmin⟩ := hScomp.exists_isMinOn hSne continuousOn_id
  obtain ⟨β, hβS, hβmax⟩ := hScomp.exists_isMaxOn hSne continuousOn_id
  have hαle : ∀ t ∈ S, α ≤ t := fun t ht =>
    (hαmin.isGLB hαS).1 ⟨t, ht, rfl⟩
  have hβge : ∀ t ∈ S, t ≤ β := fun t ht =>
    (hβmax.isLUB hβS).1 ⟨t, ht, rfl⟩
  have hαβ : α ≤ β := hβge α hαS
  have hαβne : α ≠ β := by
    intro hc
    have hgsing : g = {a₀ + α • d} := by
      refine Set.eq_singleton_iff_unique_mem.2 ⟨hαS, fun z hz => ?_⟩
      obtain ⟨c, hcz⟩ := hmem z hz
      have hcS : c ∈ S := by
        show a₀ + c • d ∈ g
        rw [← hcz]
        exact hz
      have h1 : α ≤ c := hαle c hcS
      have h2 : c ≤ β := hβge c hcS
      rw [← hc] at h2
      have h3 : c = α := le_antisymm h2 h1
      rw [hcz, h3]
    rw [hgsing, affDim_singleton] at hd
    norm_num at hd
  refine ⟨a₀ + α • d, a₀ + β • d, ?_, ?_⟩
  · intro hab
    have h1 : (a₀ + α • d : V3) - a₀ = (a₀ + β • d : V3) - a₀ := by rw [hab]
    simp only [add_sub_cancel_left] at h1
    have h2 : (α - β) • d = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact h1
    exact hαβne (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hd0))
  · refine Set.eq_of_subset_of_subset ?_ ?_
    · intro z hz
      obtain ⟨c, hcz⟩ := hmem z hz
      have hcS : c ∈ S := by
        show a₀ + c • d ∈ g
        rw [← hcz]
        exact hz
      have h1 : α ≤ c := hαle c hcS
      have h2 : c ≤ β := hβge c hcS
      have hβα : (0:ℝ) < β - α := by
        rcases lt_or_eq_of_le hαβ with h | h
        · linarith
        · exact absurd h hαβne
      have h3 : (c - α) / (β - α) ∈ Set.Icc (0:ℝ) 1 := by
        refine ⟨div_nonneg (by linarith) (by linarith), ?_⟩
        rw [div_le_one hβα]
        linarith
      rw [mem_segment_pair]
      refine ⟨1 - (c - α) / (β - α), (c - α) / (β - α), ?_, ?_, ?_, ?_⟩
      · exact sub_nonneg.2 h3.2
      · exact h3.1
      · ring
      · rw [hcz]
        have hw : ((c - α) / (β - α)) * (β - α) = c - α := by
          rw [div_mul_eq_mul_div]
          field_simp
        have hw2 : (1 - (c - α) / (β - α)) • (a₀ + α • d)
              + ((c - α) / (β - α)) • (a₀ + β • d)
            = a₀ + ((1 - (c - α) / (β - α)) * α + ((c - α) / (β - α)) * β) • d := by
          module
        rw [hw2]
        congr 1
        have h4 : (1 - (c - α) / (β - α)) * α + ((c - α) / (β - α)) * β = c := by
          have h7 : α + ((c - α) / (β - α)) * (β - α) = c := by
            rw [hw]; ring
          calc (1 - (c - α) / (β - α)) * α + ((c - α) / (β - α)) * β
              = α + ((c - α) / (β - α)) * (β - α) := by ring
            _ = c := h7
        rw [h4]
    · intro z hz
      have hzg : ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 ∧
          u • (a₀ + α • d) + v • (a₀ + β • d) = z := mem_segment_pair.mp hz
      obtain ⟨u, v, hu, hv, huv, hzeq⟩ := hzg
      have hmemg : u • (a₀ + α • d) + v • (a₀ + β • d) ∈ g :=
        hcv hαS hβS hu hv huv
      rw [← hzeq]
      exact hmemg

/-! ## 批 4 引理的公开版编码重述（`CONNECTED_FCHANGED` 拼链所需） -/

/-- 连通分量的对称性。 -/
private theorem ccIn_symm_p6 {F : Set V3} {a b : V3}
    (h : a ∈ connectedComponentIn F b) : b ∈ connectedComponentIn F a := by
  have hF : b ∈ F := connectedComponentIn_nonempty_iff.mp ⟨a, h⟩
  rw [← connectedComponentIn_eq h]
  exact mem_connectedComponentIn hF

/-- 分量传递。 -/
private theorem ccTrans_p6 {s : Set V3} {x y z : V3}
    (h1 : x ∈ connectedComponentIn s y) (h2 : y ∈ connectedComponentIn s z) :
    x ∈ connectedComponentIn s z := by
  rw [connectedComponentIn_eq h2]
  exact h1

/-- 过 `y` 的开射线（正数倍集）连通。 -/
private theorem halfLineConn_p6 (y : V3) :
    IsConnected {v : V3 | ∃ s : ℝ, 0 < s ∧ v = s • y} := by
  have hset : {v : V3 | ∃ s : ℝ, 0 < s ∧ v = s • y}
      = (fun t : ℝ => t • y) '' Set.Ioi 0 := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  rw [hset]
  exact ((convex_Ioi 0).isConnected ⟨1, zero_lt_one⟩).image _
    (continuous_id.smul continuous_const).continuousOn

/-- `fchanged f` 连通（polyhedron.hl:675 `CONNECTED_FCHANGED`；批 4 定理按
Polytope 公开版编码的重述）。 -/
private theorem connectedFchanged_p6 {p f : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    IsConnected (fchanged_p6 f) := by
  have hconv : fchanged_p6 f = fchanged f := rfl
  rw [hconv]
  have hiiConn : IsConnected (intrinsicInterior ℝ f) :=
    (convex_intrinsicInterior hf.1.2.1).isConnected
      (Set.Nonempty.intrinsicInterior hf.1.2.1
        (Set.nonempty_iff_ne_empty.mpr hf.2.1))
  have hiiSub : intrinsicInterior ℝ f ⊆ fchanged f := fun v hv =>
    ⟨v, 1, by rw [one_smul], hv, zero_lt_one⟩
  have key : ∀ u ∈ fchanged f, ∀ w ∈ fchanged f,
      u ∈ connectedComponentIn (fchanged f) w := by
    intro u hu w hw
    obtain ⟨v1, t, rfl, hv1, ht⟩ := hu
    obtain ⟨v1', t', rfl, hv1', ht'⟩ := hw
    have cMid : v1' ∈ connectedComponentIn (fchanged f) v1 :=
      connectedComponentIn_mono v1 hiiSub
        (hiiConn.2.subset_connectedComponentIn hv1 subset_rfl hv1')
    have cLeft : (t : ℝ) • v1 ∈ connectedComponentIn (fchanged f) v1 := by
      have hsub : {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1} ⊆ fchanged f := fun z hz => by
        obtain ⟨s, hs, rfl⟩ := hz
        exact ⟨v1, s, rfl, hv1, hs⟩
      have hRay : v1 ∈
          connectedComponentIn {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1} (t • v1) :=
        (halfLineConn_p6 v1).2.subset_connectedComponentIn ⟨t, ht, rfl⟩ subset_rfl
          ⟨1, zero_lt_one, by rw [one_smul]⟩
      exact ccIn_symm_p6 (connectedComponentIn_mono (t • v1) hsub hRay)
    have cRight : v1' ∈ connectedComponentIn (fchanged f) (t' • v1') := by
      have hsub : {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1'} ⊆ fchanged f := fun z hz => by
        obtain ⟨s, hs, rfl⟩ := hz
        exact ⟨v1', s, rfl, hv1', hs⟩
      have hRay : v1' ∈
          connectedComponentIn {z : V3 | ∃ s : ℝ, 0 < s ∧ z = s • v1'} (t' • v1') :=
        (halfLineConn_p6 v1').2.subset_connectedComponentIn ⟨t', ht', rfl⟩ subset_rfl
          ⟨1, zero_lt_one, by rw [one_smul]⟩
      exact connectedComponentIn_mono (t' • v1') hsub hRay
    exact ccTrans_p6 (ccTrans_p6 cLeft (ccIn_symm_p6 cMid)) cRight
  have hfne : f.Nonempty := Set.nonempty_iff_ne_empty.mpr hf.2.1
  obtain ⟨v0, hv0ii⟩ := Set.Nonempty.intrinsicInterior hf.1.2.1 hfne
  have hv0 : v0 ∈ fchanged f := ⟨v0, 1, by rw [one_smul], hv0ii, zero_lt_one⟩
  have hcc : connectedComponentIn (fchanged f) v0 = fchanged f :=
    Set.eq_of_subset_of_subset (connectedComponentIn_subset _ _)
      (fun z hz => key z hz v0 hv0)
  rw [← hcc]
  exact isConnected_connectedComponentIn_iff.mpr hv0

/-! ## polyhedron.hl :1315-:1384 -/

/-- 核心引理（`REDUCE_POINT_FACET`/`REDUCE_POINT_FACET_EXISTS` 共体）：
`x ≠ 0` 时正射线必打到某 facet 上（HOL `COMPACT_FRONTIER_LINE_LEMMA` 路线：
射线参数集闭有界非空 ⇒ 取极大参数 `u`；`u = 0` 与 `0 ∈ interior p` 矛盾，
`u • x ∈ relative_interior p` 与极大性矛盾，故经
`RELATIVE_INTERIOR_OF_POLYHEDRON` 落在 ⋃₀ facets 中）。 -/
private theorem exists_facet_ray_of_ne_zero {x : V3} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hx0 : x ≠ (0 : V3)) :
    ∃ f : Set V3, ∃ t : ℝ, 0 < t ∧ FacetOf f p ∧ t • x ∈ f := by
  classical
  have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  -- 射线参数集 S = {t | t • x ∈ p} ∩ {t | 0 ≤ t}：闭、非空
  set S : Set ℝ := {t : ℝ | t • x ∈ p} ∩ {t : ℝ | 0 ≤ t} with hSdef
  have hSne : S.Nonempty :=
    ⟨0, ⟨by simp only [Set.mem_setOf_eq, zero_smul]; exact interior_subset h0,
      by show (0:ℝ) ≤ 0; exact le_refl 0⟩⟩
  have hScl : IsClosed S :=
    ((POLYHEDRON_IMP_CLOSED hp).preimage
      (continuous_id.smul continuous_const)).inter isClosed_Ici
  -- 有界性：p ⊆ ball 0 C ⇒ S ⊆ ball 0 (C/‖x‖ + 1)
  obtain ⟨C, hC⟩ := Metric.isBounded_iff_subset_ball (0 : V3) |>.mp hb
  have hSbd : Bornology.IsBounded S := by
    refine Metric.isBounded_iff_subset_ball 0 |>.2 ⟨C / ‖x‖ + 1, ?_⟩
    rintro t ⟨ht, -⟩
    have h2 : dist (t • x : V3) (0 : V3) < C := hC ht
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs] at h2
    have h3 : |t| < C / ‖x‖ := by
      rw [lt_div_iff₀ hxn]
      linarith
    show dist (t : ℝ) 0 < C / ‖x‖ + 1
    rw [Real.dist_eq, sub_zero]
    linarith
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSbd
  -- 极大参数 u ∈ S
  obtain ⟨u, huS, huMax⟩ := hScomp.exists_isMaxOn hSne continuousOn_id
  obtain ⟨htx, hu0⟩ := id huS
  have hub : ∀ t ∈ S, t ≤ u := fun t ht =>
    (huMax.isLUB huS).1 ⟨t, ht, rfl⟩
  -- u > 0：0 ∈ interior p 给小参数
  have hup : 0 < u := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (0 : V3) h0
    have hδ : (0:ℝ) < ε / (2 * ‖x‖) := by
      refine div_pos hε ?_
      linarith
    have hδb : (ε / (2 * ‖x‖)) • x ∈ Metric.ball (0 : V3) ε := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      have hscal : (ε / (2 * ‖x‖)) * ‖x‖ = ε / 2 := by
        rw [div_mul_eq_mul_div]
        field_simp
      rw [hscal]
      linarith
    have hδS : ε / (2 * ‖x‖) ∈ S :=
      ⟨(show (ε / (2 * ‖x‖)) • x ∈ p from interior_subset (hball hδb)),
        by show (0:ℝ) ≤ ε / (2 * ‖x‖); exact le_of_lt hδ⟩
    linarith [hub _ hδS]
  -- u•x 不在相对内部（极大性）
  have huint : (u • x : V3) ∉ intrinsicInterior ℝ p := by
    intro hrint
    obtain ⟨-, ε, hε, hball⟩ := mem_rint_iff.mp hrint
    rw [INTERIOR_AFFINIE_HUL_EQ_UNIV (0 : V3) p h0, Set.inter_univ] at hball
    have hδ : (0:ℝ) < ε / (2 * ‖x‖) := by
      refine div_pos hε ?_
      linarith
    have hIn : ((u : ℝ) + ε / (2 * ‖x‖)) • x ∈ Metric.ball (u • x : V3) ε := by
      rw [mem_ball_iff_norm]
      have hexp : ((u : ℝ) + ε / (2 * ‖x‖)) • x - (u : ℝ) • x
          = (ε / (2 * ‖x‖)) • x := by module
      rw [hexp, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      have hscal : (ε / (2 * ‖x‖)) * ‖x‖ = ε / 2 := by
        rw [div_mul_eq_mul_div]
        field_simp
      rw [hscal]
      linarith
    have hS2 : ((u : ℝ) + ε / (2 * ‖x‖)) ∈ S :=
      ⟨hball hIn, by show (0:ℝ) ≤ (u:ℝ) + ε / (2 * ‖x‖); linarith⟩
    linarith [hub _ hS2]
  -- 经 RELATIVE_INTERIOR_OF_POLYHEDRON 提取 facet
  have hri : intrinsicInterior ℝ p = p \ ⋃₀ {f : Set V3 | FacetOf f p} :=
    RELATIVE_INTERIOR_OF_POLYHEDRON hp
  have hmemU : (u • x : V3) ∈ ⋃₀ {f : Set V3 | FacetOf f p} := by
    by_contra hcon
    exact huint (by rw [hri]; exact ⟨htx, hcon⟩)
  obtain ⟨f, hf, huf⟩ := Set.mem_sUnion.mp hmemU
  exact ⟨f, u, hup, hf, huf⟩

/-- HOL polyhedron.hl :1315-1318 `EXISTS_EDGE_POLYTOPE1`

HOL 原文：
```
!p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    ==> ~(edges p = {})
```

证明思路：即 `EXISTS_EDGE_POLYTOPE`（polyhedron.hl:1278，批 5 范围、
PolyAuto5 已证）经 `~(A = {}) <=> ?x. x IN A` 改写；骨架直接引该式，
`edges`（Polytope 公开版）到私有 `edges_p6` 的成员经 `edgeOf` 展开逐字
重建（面条件 `FaceOf` 三分量一一对应）。 -/
theorem EXISTS_EDGE_POLYTOPE1 {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) : edges_p6 p ≠ ∅ := by
  obtain ⟨e, he⟩ := EXISTS_EDGE_POLYTOPE p hb hp h0
  obtain ⟨v, w, rfl, hface, hdim⟩ := he
  have hvw : v ≠ w := (edgeOf_segment_iff.mp ⟨hface, hdim⟩).1
  exact Set.nonempty_iff_ne_empty.mp ⟨{v, w}, mem_edges_p6_intro hvw hface⟩

/-- HOL polyhedron.hl :1323-1357 `REDUCE_POINT_FACET`

HOL 原文：
```
!x p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    /\ x IN yfan(vec 0,vertices p,edges p)
    ==> ?f t. &0 < t /\ f facet_of p /\ t % x IN f
```

证明思路：`x ∈ yfan` 给 `x ≠ 0`（`0 ∈ xfan`：任取边 `e`，`0 ∈ aff_ge {0} e`
恒成立）；核心由 `exists_facet_ray_of_ne_zero` 完成（HOL
`POLYHEDRON_FAN` + `COMPACT_FRONTIER_LINE_LEMMA` + 非零参数）。 -/
theorem REDUCE_POINT_FACET {x : V3} {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hx : x ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) :
    ∃ f : Set V3, ∃ t : ℝ, 0 < t ∧ FacetOf f p ∧ t • x ∈ f := by
  have hx0 : x ≠ (0 : V3) := by
    intro hxx
    subst hxx
    exact hx.2 (zero_mem_xfan_of_ne_edges (EXISTS_EDGE_POLYTOPE1 hb hp h0))
  exact exists_facet_ray_of_ne_zero hb hp h0 hx0

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
若 `t % y ∈ relative_interior f`，则 `y = t⁻¹ % (t % y) ∈ fchanged f`
（取 `v1 = t % y`、`t1 = inv t`）且 `fchanged f` 在所求并中。否则
`t % y ∈ f DIFF relative_interior f`：经 `RELATIVE_BOUNDARY_OF_POLYHEDRON`
路线（`RELATIVE_INTERIOR_OF_POLYHEDRON`，Polytope.lean:1793）得
`t % y` 在 `f` 的某 facet `g`（`aff_dim g = 1`，`aff_dim f = 2` 经
`AFF_DIM_INTERIOR_EQ_3`）上；`g` 紧凸 1 维集 ⇒ `g = segment [a,b]`
（两极点，`COMPACT_CONVEX_COLLINEAR_SEGMENT` 就地版本）；`FACE_OF_TRANS`
得 `segment [a,b] face_of p` 即 `{a,b} ∈ edges p`；`AFF_GE_SUBSET_XFAN`
（`point_in_aff_ge` + `FAN` 的 fan6）给 `segment [a,b] ⊆ xfan`，于是
`t % y ∈ xfan`。又 `y = (1 - inv t) % 0 + inv t % (t % y) ∈ aff_ge {0}
{t % y}`（`AFF_GE_1_1`），`aff_ge_1_1_subset_xfan_p6` 给 `y ∈ xfan`，与
`y ∈ yfan = UNIV DIFF xfan` 矛盾。 -/
theorem YFAN_SUBSET_UNIONS_FCHANGED {y : V3} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hy : y ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) :
    y ∈ ⋃ f ∈ {f : Set V3 | FacetOf f p}, fchanged_p6 f := by
  have hy0 : y ≠ (0 : V3) := by
    intro hxx
    subst hxx
    exact hy.2 (zero_mem_xfan_of_ne_edges (EXISTS_EDGE_POLYTOPE1 hb hp h0))
  obtain ⟨f, t, ht, hf, hty⟩ := REDUCE_POINT_FACET hb hp h0 hy
  -- f 是真 facet：0 ∉ f（0 ∈ relative_interior p 与 facet 不交）
  have hdim3 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 (0 : V3) p h0
  have hfp : f ≠ p := by
    intro hcon
    rw [hcon] at hf
    have h2 := hf.2.2
    linarith
  have h0f : (0 : V3) ∉ f := fun h0in =>
    Set.disjoint_left.mp (faceOf_disjoint_rinterior hf.1 hfp) h0in
      (interior_subset_intrinsicInterior h0)
  refine Set.mem_iUnion₂.2 ⟨f, hf, ?_⟩
  by_cases hrint : (t • y : V3) ∈ intrinsicInterior ℝ f
  · -- t % y 在 f 的相对内部：y = t⁻¹ % (t % y) ∈ fchanged f
    exact ⟨t • y, t⁻¹, by rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul], hrint,
      inv_pos.mpr ht⟩
  · -- t % y 在 facet 边界 ⇒ f 的 1 维 facet g ⇒ g = 闭段 [a,b] ⇒ {a,b} 是 edge
    exfalso
    have hfp2 : polyhedron f := FACE_OF_POLYHEDRON_POLYHEDRON hp hf.1
    have hbd : (t • y : V3) ∈ ⋃₀ {g : Set V3 | FacetOf g f} := by
      by_contra hcon
      exact hrint (by
        rw [RELATIVE_INTERIOR_OF_POLYHEDRON hfp2]
        exact ⟨hty, hcon⟩)
    obtain ⟨g, hgf, htg⟩ := Set.mem_sUnion.mp hbd
    have hdimf : affDim f = 2 := by rw [hf.2.2, hdim3]; norm_num
    have hdimg : affDim g = 1 := by rw [hgf.2.2, hdimf]; norm_num
    have hgp : polyhedron g := FACE_OF_POLYHEDRON_POLYHEDRON hfp2 hgf.1
    obtain ⟨a, b, hab, hgeq⟩ := segment_of_affDim_one hgf.1.2.1
      (POLYHEDRON_IMP_CLOSED hgp)
      (hb.subset (Set.Subset.trans hgf.1.1 hf.1.1))
      (Set.nonempty_iff_ne_empty.mpr hgf.2.1) hdimg
    have hfaceab : FaceOf (segment ℝ a b) p := by rw [← hgeq]; exact FaceOf.trans hgf.1 hf.1
    have hEab : ({a, b} : Set V3) ∈ edges_p6 p := mem_edges_p6_intro hab hfaceab
    have h0a : (0 : V3) ≠ a := by
      intro hc
      refine h0f ?_
      have h1 : (0 : V3) ∈ segment ℝ a b := by
        rw [hc]
        exact left_mem_segment ℝ a b
      have h2 : (0 : V3) ∈ g := by rw [hgeq]; exact h1
      exact hgf.1.1 h2
    have h0b : (0 : V3) ≠ b := by
      intro hc
      refine h0f ?_
      have h1 : (0 : V3) ∈ segment ℝ a b := by
        rw [hc]
        exact right_mem_segment ℝ a b
      have h2 : (0 : V3) ∈ g := by rw [hgeq]; exact h1
      exact hgf.1.1 h2
    have htyseg : (t • y : V3) ∈ segment ℝ a b := by rw [← hgeq]; exact htg
    obtain ⟨c1, c2, hc10, hc20, hc12, hcombo⟩ := mem_segment_pair.mp htyseg
    -- t % y ∈ aff_ge {0} {a,b}
    have htyge : (t • y : V3) ∈ affGe ({(0 : V3)} : Set V3) ({a, b} : Set V3) :=
      Affsign.of_triple (x := (0 : V3)) c1 c2 hc10 hc20
        (by rw [smul_zero, zero_add, hcombo]) h0a h0b hab
    -- y ∈ aff_ge {0} {t % y}
    have hty0 : (t • y : V3) ≠ (0 : V3) := by
      intro hc
      rcases smul_eq_zero.mp hc with h | h
      · exact ht.ne' h
      · exact hy0 h
    have hyray : y ∈ affGe ({(0 : V3)} : Set V3) ({t • y} : Set V3) :=
      affGe_ray_intro (x := (0 : V3)) (v := t • y) (Ne.symm hty0)
        (inv_nonneg.2 ht.le)
        (by rw [sub_zero, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, zero_add])
    have hsub2 : y ∈ affGe ({(0 : V3)} : Set V3) ({a, b} : Set V3) :=
      aff_ge_1_1_subset_aff_ge_fan (v1 := t • y)
        (Set.disjoint_left.2 fun z hz1 hz2 => by
          have hz0 : z = (0 : V3) := Set.mem_singleton_iff.mp hz1
          rcases Set.mem_insert_iff.mp hz2 with hza | hzb
          · exact h0a (hz0.symm.trans hza)
          · rw [Set.mem_singleton_iff] at hzb
            exact h0b (hz0.symm.trans hzb))
        (Ne.symm hty0) htyge hyray
    exact hy.2 ⟨{a, b}, hEab, hsub2⟩

/-- HOL polyhedron.hl :1524-1562 `in_aff_ge_fan`

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
    ∃ f : Set V3, ∃ t : ℝ, 0 < t ∧ FacetOf f p ∧ t • x ∈ f :=
  exists_facet_ray_of_ne_zero hb hp h0 hx

/-- HOL polyhedron.hl :1564-1684 `FCHANGED_SUBSET_YFAN`

HOL 原文：
```
!x p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    /\ x IN UNIONS {fchanged f | f facet_of p}
    ==> x IN yfan(vec 0,vertices p,edges p)
```

证明思路：设 `f facet_of p`、`v1 ∈ relative_interior f`、`0 < t`、
`x = t % v1`。反设 `x ∈ xfan`：由 `aff_ge_1_2` 取边 `{v,w}` 与系数
`t1,t2,t3 ≥ 0` 使 `x = t1 % 0 + t2 % v + t3 % w`。若 `t2 + t3 = 0` 则
`x = 0`、`v1 = 0 ∈ f` 与 facet 避开原点矛盾。否则 `x' = (t2+t3)⁻¹ % x`
在闭段 `segment [v,w]` 上（两系数和为一），且 `x' = (t/σ) % v1`；
`POLYHEDRON_COLLINEAR_FACES_STRONG`（两真面沿同一射线同比例）给
`t/σ = 1`，故 `v1 ∈ segment [v,w]`。于是 `v1` 同属 `f` 与边闭段
`segment [v,w]` 的相对内部：`FACE_OF_EQ` 给 `f = segment [v,w]` 与
`aff_dim f = 2`、`aff_dim = 1` 矛盾；否则 `v1` 落在 `segment [v,w]` 的
某 0 维 facet `g`（单点面，就地证明）上，`FACE_OF_TRANS` + `FACE_OF_EQ`
给 `g = f` 与 `aff_dim g = 0` 矛盾。候选：`XFAN_EQ_UNIONS_AFF_GE_1_2`
（Kepler/Text/ConformingAuto3.lean:286）、`expand_edge_graph_fan`
（TopologyFan.lean:3212）、`POLYHEDRON_COLLINEAR_FACES`/
`FACE_OF_EQ`/`SEGMENT_FACE_OF`（Polytope.lean 已移植）。 -/
theorem FCHANGED_SUBSET_YFAN {x : V3} {p : Set V3}
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p)
    (hx : x ∈ ⋃ f ∈ {f : Set V3 | FacetOf f p}, fchanged_p6 f) :
    x ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p) := by
  refine Set.mem_sdiff x |>.2 ⟨Set.mem_univ x, fun hxin => ?_⟩
  obtain ⟨f, hf, v1, t, hxeq, hv1, ht⟩ := Set.mem_iUnion₂.mp hx
  have hdim3 : affDim p = 3 := AFF_DIM_INTERIOR_EQ_3 (0 : V3) p h0
  have hdimf : affDim f = 2 := by rw [hf.2.2, hdim3]; norm_num
  have hfp : f ≠ p := by
    intro hcon
    rw [hcon] at hf
    have h2 := hf.2.2
    linarith
  have h0f : (0 : V3) ∉ f := fun h0in =>
    Set.disjoint_left.mp (faceOf_disjoint_rinterior hf.1 hfp) h0in
      (interior_subset_intrinsicInterior h0)
  obtain ⟨e, heE, hxe⟩ := hxin
  obtain ⟨v, w, rfl, hvw, hsub, hconv, hchord⟩ := heE
  have hfaceS : FaceOf (segment ℝ v w) p := ⟨hsub, hconv, hchord⟩
  have hdimS : affDim (segment ℝ v w) = 1 := (affDim_segment v w).2 hvw
  have hSp : segment ℝ v w ≠ p := by
    intro hcon
    rw [hcon, hdim3] at hdimS
    omega
  have hvex : v ∈ Set.extremePoints ℝ p ∧ w ∈ Set.extremePoints ℝ p :=
    SEGMENT_FACE_OF hfaceS
  have hdis : Disjoint ({(0 : V3)} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have hz0 : z = (0 : V3) := Set.mem_singleton_iff.mp hz1
    rcases Set.mem_insert_iff.mp hz2 with hza | hzb
    · have hv0 : v = (0 : V3) := hza.symm.trans hz0
      exact interior_not_extremePoint h0
        (show (0:V3) ∈ Set.extremePoints ℝ p from hv0 ▸ hvex.1)
    · rw [Set.mem_singleton_iff] at hzb
      have hw0 : w = (0 : V3) := hzb.symm.trans hz0
      exact interior_not_extremePoint h0
        (show (0:V3) ∈ Set.extremePoints ℝ p from hw0 ▸ hvex.2)
  rw [aff_ge_1_2 hdis, Set.mem_setOf_eq] at hxe
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hxeq2⟩ := hxe
  have hσ : 0 < t2 + t3 := by
    by_contra hc
    push_neg at hc
    have ht20 : t2 = 0 := by linarith
    have ht30 : t3 = 0 := by linarith
    simp only [ht20, ht30, smul_zero, zero_add, zero_smul, add_zero] at hxeq2
    rw [hxeq2] at hxeq
    have h1 : v1 = 0 := (smul_eq_zero.mp hxeq.symm).resolve_left ht.ne'
    have hv1f : v1 ∈ f := intrinsicInterior_subset hv1
    rw [h1] at hv1f
    exact h0f hv1f
  -- 交点 x' = σ⁻¹ % x = (t/σ) % v1 在边闭段上
  have hx' : (t / (t2 + t3)) • v1 ∈ segment ℝ v w := by
    rw [mem_segment_pair]
    refine ⟨(1 / (t2 + t3)) * t2, (1 / (t2 + t3)) * t3,
      mul_nonneg (div_nonneg zero_le_one hσ.le) ht2,
      mul_nonneg (div_nonneg zero_le_one hσ.le) ht3, ?_, ?_⟩
    · rw [← mul_add, div_mul_cancel₀ (1:ℝ) hσ.ne']
    · have h7 : ((1 / (t2 + t3)) * t2) • v + ((1 / (t2 + t3)) * t3) • w
          = (1 / (t2 + t3)) • (t2 • v + t3 • w) := by
        rw [smul_add, smul_smul, smul_smul]
      have h8 : t2 • v + t3 • w = x := by
        rw [hxeq2, smul_zero, zero_add]
      rw [h7, h8, hxeq, smul_smul]
      congr 1
      ring
  -- POLYHEDRON_COLLINEAR_FACES_STRONG：两真面共线同比例 ⇒ t/σ = 1 ⇒ v1 ∈ 闭段
  have h0p : (0 : V3) ∈ intrinsicInterior ℝ p := interior_subset_intrinsicInterior h0
  have hst : (t / (t2 + t3)) • v1
      = (1:ℝ) • ((t / (t2 + t3)) • v1) := by
    rw [one_smul]
  have hlam : t / (t2 + t3) = 1 :=
    POLYHEDRON_COLLINEAR_FACES_STRONG hp h0p hf.1 hfp hfaceS hSp
      (intrinsicInterior_subset hv1) hx'
      (div_pos ht hσ) zero_lt_one hst
  have hv1S : v1 ∈ segment ℝ v w := by
    have h1 := hx'
    rw [hlam, one_smul] at h1
    exact h1
  -- v1 同时在 f 与边闭段的相对内部：维数矛盾
  have hpS : polyhedron (segment ℝ v w) := FACE_OF_POLYHEDRON_POLYHEDRON hp hfaceS
  rcases em (v1 ∈ intrinsicInterior ℝ (segment ℝ v w)) with hrintS | hrintS
  · have hfeq : f = segment ℝ v w :=
      faceOf_eq hf.1 hfaceS (Set.not_disjoint_iff.2 ⟨v1, hv1, hrintS⟩)
    rw [hfeq] at hdimf
    omega
  · obtain ⟨g, hgf, hv1g⟩ := Set.mem_sUnion.mp (by
      by_contra hcon
      exact hrintS (by
        rw [RELATIVE_INTERIOR_OF_POLYHEDRON hpS]
        exact ⟨hv1S, fun hmem => hcon (Set.mem_sUnion.mp hmem)⟩))
    have hdimg : affDim g = 0 := by rw [hgf.2.2, hdimS]; norm_num
    have hgne : g.Nonempty := Set.nonempty_iff_ne_empty.mpr hgf.2.1
    obtain ⟨a, hgaeq⟩ := singleton_of_affDim_zero hgne hdimg
    have hrintg : intrinsicInterior ℝ g = {a} := by
      have hsub2 : ∀ z ∈ intrinsicInterior ℝ g, z = a := by
        intro z hz
        have hz2 : z ∈ g := intrinsicInterior_subset hz
        rw [hgaeq] at hz2
        exact Set.mem_singleton_iff.mp hz2
      obtain ⟨z₀, hz₀⟩ := Set.Nonempty.intrinsicInterior hgf.1.2.1 hgne
      rw [← hsub2 z₀ hz₀]
      exact Set.eq_singleton_iff_unique_mem.2 ⟨hz₀, fun w hw => by
        rw [hsub2 w hw, hsub2 z₀ hz₀]⟩
    have hgp : FaceOf g p := FaceOf.trans hgf.1 hfaceS
    have hgfeq : g = f :=
      faceOf_eq hgp hf.1 (Set.not_disjoint_iff.2 ⟨v1,
        (show v1 ∈ intrinsicInterior ℝ g from by
          rw [hrintg, ← hgaeq]
          exact hv1g), hv1⟩)
    rw [hgfeq] at hdimg
    omega

/-- HOL polyhedron.hl :1685-1695 `FCHANGED_EQ_YFAN`

HOL 原文：
```
!p:real^3->bool.
    bounded p /\ polyhedron p /\ vec 0 IN interior p
    ==> UNIONS {fchanged f | f facet_of p} = yfan(vec 0,vertices p,edges p)
```

证明思路：`EXTENSION` + 两方向分别用 `FCHANGED_SUBSET_YFAN` 与
`YFAN_SUBSET_UNIONS_FCHANGED`（HOL `ASM_SIMP_TAC` 两行）。 -/
theorem FCHANGED_EQ_YFAN {p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) :
    (⋃ f ∈ {f : Set V3 | FacetOf f p}, fchanged_p6 f)
      = yfan (0 : V3) (vertices_p6 p) (edges_p6 p) :=
  Set.eq_of_subset_of_subset (fun z hz => FCHANGED_SUBSET_YFAN hb hp h0 hz)
    (fun z hz => YFAN_SUBSET_UNIONS_FCHANGED hb hp h0 hz)

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
`y ∈ fchanged f ⊆` 并集；`CONNECTED_FCHANGED`（`fchanged f` 连通，批 4
中心定理的公开版编码重述）+ `CONNECTED_CONNECTED_COMPONENT_SET` 得
`fchanged f ⊆ connectedComponent y`，反向包含用 `FCHANGED_OPEN`（各
`fchanged f'` 开）+ `FCHANGED_ONE_TO_ONE`（不同 facet 的 `fchanged`
不交）：连通分量若越过另一 facet 的 `fchanged`，则该分量被两不交开集
分离，矛盾。候选：`CONNECTED_FCHANGED`（Kepler/Text/PolyAuto4.lean:379，
本批就地私有重述）、`topologicalComponentYfan`（Kepler/Text/Fan.lean:199）、
`FCHANGED_OPEN`/`FCHANGED_ONE_TO_ONE`（PolyAuto5 已证）、Mathlib
`IsConnected`/`connectedComponentIn` 类 API。 -/
theorem FCHANGED_IN_COMPONENT {f p : Set V3} (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (h0 : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    fchanged_p6 f ∈ topologicalComponentYfan (0 : V3) (vertices_p6 p)
      (edges_p6 p) := by
  obtain ⟨y, hy⟩ := EXISTS_POINT_IN_FCHANGED hb hp h0 hf
  have hyfan : y ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p) :=
    FCHANGED_SUBSET_YFAN hb hp h0 (Set.mem_iUnion₂.2 ⟨f, hf, hy⟩)
  have hconn : IsConnected (fchanged_p6 f) := connectedFchanged_p6 hb hp h0 hf
  have huSub : fchanged_p6 f ⊆ yfan (0 : V3) (vertices_p6 p) (edges_p6 p) :=
    fun z hz => FCHANGED_SUBSET_YFAN hb hp h0 (Set.mem_iUnion₂.2 ⟨f, hf, hz⟩)
  have hstep1 : fchanged_p6 f ⊆
      connectedComponentIn (yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) y :=
    hconn.2.subset_connectedComponentIn hy huSub
  have hCconn : IsConnected
      (connectedComponentIn (yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) y) :=
    isConnected_connectedComponentIn_iff.2 hyfan
  -- 反向：连通分量不越过其它 facet 的 fchanged（不交开集分离论证）
  have hCsub : connectedComponentIn (yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) y
      ⊆ fchanged_p6 f := by
    by_contra hcon
    obtain ⟨z, hzC, hzu⟩ : ∃ z, z ∈ connectedComponentIn
        (yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) y ∧
        z ∉ fchanged_p6 f := by
      by_contra hcon2
      exact hcon fun w hw => by
        by_contra hwu
        exact hcon2 ⟨w, hw, hwu⟩
    have hzyfan : z ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p) :=
      connectedComponentIn_subset _ _ hzC
    rw [← FCHANGED_EQ_YFAN hb hp h0] at hzyfan
    obtain ⟨g, hg, hzg⟩ := Set.mem_iUnion₂.mp hzyfan
    have hgne : g ≠ f := fun hcc => hzu (hcc ▸ hzg)
    have huOpen : IsOpen (fchanged_p6 f) := by
      rw [show fchanged_p6 f = fchanged f from rfl]
      exact FCHANGED_OPEN p f hb hp h0 hf
    have hVopen : IsOpen
        (⋃₀ {fchanged_p6 k | k ∈ {k : Set V3 | FacetOf k p ∧ k ≠ f}}) :=
      isOpen_sUnion fun U hU => by
        obtain ⟨k, hk, rfl⟩ := hU
        rw [show fchanged_p6 k = fchanged k from rfl]
        exact FCHANGED_OPEN p k hb hp h0 hk.1
    have hcover : connectedComponentIn
          (yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) y
        ⊆ fchanged_p6 f
          ∪ ⋃₀ {fchanged_p6 k | k ∈ {k : Set V3 | FacetOf k p ∧ k ≠ f}} :=
      fun w hw => by
        have hwf : w ∈ yfan (0 : V3) (vertices_p6 p) (edges_p6 p) :=
          connectedComponentIn_subset _ _ hw
        rw [← FCHANGED_EQ_YFAN hb hp h0] at hwf
        obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.mp hwf
        by_cases hkf : k = f
        · exact Or.inl (hkf ▸ hwk)
        · exact Or.inr (Set.mem_sUnion.2 ⟨fchanged_p6 k,
            ⟨k, (show k ∈ {k : Set V3 | FacetOf k p ∧ k ≠ f} from ⟨hk, hkf⟩), rfl⟩,
            hwk⟩)
    have hnon : (connectedComponentIn
          (yfan (0 : V3) (vertices_p6 p) (edges_p6 p)) y ∩
        (fchanged_p6 f ∩
          ⋃₀ {fchanged_p6 k | k ∈ {k : Set V3 | FacetOf k p ∧ k ≠ f}})).Nonempty :=
      hCconn.2 (fchanged_p6 f)
        (⋃₀ {fchanged_p6 k | k ∈ {k : Set V3 | FacetOf k p ∧ k ≠ f}}) huOpen hVopen
        hcover ⟨y, mem_connectedComponentIn hyfan, hy⟩
        ⟨z, hzC, ⟨fchanged_p6 g,
          ⟨g, (show g ∈ {k : Set V3 | FacetOf k p ∧ k ≠ f} from ⟨hg, hgne⟩), rfl⟩,
          hzg⟩⟩
    obtain ⟨w, hwc, hwu, hwv⟩ := hnon
    obtain ⟨t, htS, hwt⟩ := Set.mem_sUnion.mp hwv
    obtain ⟨k, hkv, hkeq⟩ := htS
    exact hkv.2 (FCHANGED_ONE_TO_ONE p f k hb hp h0 hf hkv.1
      (Set.nonempty_iff_ne_empty.mp ⟨w, hwu, by rw [← hkeq] at hwt; exact hwt⟩)).symm
  exact ⟨y, hyfan, Set.Subset.antisymm hCsub hstep1⟩

end Kepler.Text
