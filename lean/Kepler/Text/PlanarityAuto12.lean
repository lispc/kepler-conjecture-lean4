/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18p.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18p of block 18, planarity.hl:13632-14124):
- `coplanar_imp_continuous_collinear` (13632)
- `aff_gt_1_3_eq_unions_aff_gt_1_2` (13645)
- `aff_gt_1_3_subset_yfan` (13724)
- `aff_gt_1_3_subset_dart_leads_into_fan` (13744)
- `inter_aff_gt_3_1_is_aff_gt_1_3` (13806)
- `coplanar_cross_dot` (13872)
- `aff_gt_3_1_rep_cross_dot` (13897)
- `OPEN_AFF_GT_1_3` (14075)
- `OPEN_DIFF_AFF_GE` (14115)

Skipped (already in Mathlib):
- `CRAMER_LEMMA1` (13884): the identity
  `det (A.updateCol k (A *ᵥ x)) = x k * det A` is exactly Mathlib
  `Matrix.det_updateCol_sum` (Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:435),
  with `c := x` (as `A *ᵥ x = fun k => ∑ i, x i • A k i` and `• = *` on `ℝ`).
  Mathlib's statement is the general `Matrix n n R` form, so the HOL
  `real^N^N` version is a specialization; not ported.

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42).
- HOL `coplanar` ↔ `Coplanar` (Kepler/Geom/Coplanar.lean:23); HOL
  `~collinear {a,b,c}` ↔ `¬ Collinear3 a b c` (Kepler/Geom/Azim.lean:43).
- HOL `cross` has no public V3-level definition in the repo; the
  established idiom is the Pi-side `crossProduct` (Mathlib
  `LinearAlgebra.CrossProduct`) applied to `(a : Fin 3 → ℝ)`, cf.
  Kepler/Text/PlanarityAuto10.lean:26-34. HOL `dot` ↔ `⬝ᵥ`
  (`dotProduct`). HOL `%` ↔ `•`.
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `fan80` ↔ `fan80` (Kepler/Text/Fan.lean:227); HOL `sigma_fan` ↔
  `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `yfan` ↔ `yfan`
  (Kepler/Text/Fan.lean:158); HOL `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179).
- HOL `UNIONS` ↔ `⋃₀` (`Set.sUnion`); HOL `open` ↔ `IsOpen`;
  HOL `(:real^3) DIFF A` ↔ `(Set.univ : Set V3) \ A`.
-/

import Kepler.Text.PlanarityAuto11

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## 不共面四点沿弦的连续性与 aff_gt 的射线并（planarity.hl:13632-13723） -/

/-- HOL planarity.hl :13632-13644 `coplanar_imp_continuous_collinear`

HOL 原文：
```
!x:real^3  v:real^3 u:real^3 w:real^3.
 ~(coplanar{x,v,u,w})
==>(!t:real.  ~(t= &0) ==> ~collinear {x,v,(&1-t)%u+t%w} )
```

证明思路：给定 `t ≠ 0`，由 `continuous_coplanar_fan x v u w hcop t ht`
得 `¬ Coplanar {x,v,u,(1-t)•u+t•w}`，再用
`notcoplanar_imp_notcollinear_fan` 的第三分量取出
`¬ Collinear3 x v ((1-t)•u+t•w)`。HOL 即
`continuous_coplanar_fan` 后接 `notcoplanar_imp_notcollinear_fan`。

候选已有引理：
- `continuous_coplanar_fan`（Kepler/Text/Planarity.lean:1142）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `Collinear3`（Kepler/Geom/Azim.lean:43） -/
theorem coplanar_imp_continuous_collinear (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    ∀ t : ℝ, t ≠ 0 → ¬ Collinear3 x v ((1 - t) • u + t • w) := by
  intro t ht
  exact (notcoplanar_imp_notcollinear_fan
    (continuous_coplanar_fan x v u w hcop t ht)).2.2

/-- HOL planarity.hl :13645-13723 `aff_gt_1_3_eq_unions_aff_gt_1_2`

HOL 原文：
```
!x  v u w:real^3.
~coplanar {x,v,u,w}
==>
aff_gt {x} {v,u,w} = UNIONS {aff_gt{x} {v,(&1-a)%u+ a % w}| &0<a /\ a< &1}
```

证明思路：由 `notcoplanar_disjoints`/`notcoplanar_disjoint` 得四点互异，
用 `AFF_GT_1_3` 展开左侧为 `t1•x+t2•v+t3•u+t4•w`（`t2,t3,t4>0`）。
`⊆` 方向取 `a = t4/(t3+t4) ∈ (0,1)`，把 `y` 重写为
`t1•x+t2•v+(t3+t4)•((1-a)•u+a•w)`，再用 `AFF_GT_1_2` 落入
`affGt {x} {v,(1-a)•u+a•w}`（其非退化性由
`coplanar_imp_continuous_collinear` 提供）。`⊇` 方向对
`a ∈ (0,1)` 与 `AFF_GT_1_2` 的系数 `t1,t2,t3` 取
`t3•(1-a)`, `t3•a` 合并回 `AFF_GT_1_3`。

候选已有引理：
- `AFF_GT_1_3`（Kepler/Text/PlanarityAuto11.lean:1029）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `notcoplanar_disjoint`（Kepler/Text/PlanarityAuto11.lean:1220）
- `coplanar_imp_continuous_collinear`（本文件，HOL :13632） -/
theorem aff_gt_1_3_eq_unions_aff_gt_1_2 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    affGt ({x} : Set V3) ({v, u, w} : Set V3) =
      ⋃₀ {s : Set V3 | ∃ a : ℝ, 0 < a ∧ a < 1 ∧
        s = affGt ({x} : Set V3) ({v, (1 - a) • u + a • w} : Set V3)} := by
  have hdis : Disjoint ({x} : Set V3) ({v, u, w} : Set V3) :=
    (notcoplanar_disjoints x v u w hcop).2.2.2.1
  ext y
  rw [AFF_GT_1_3 x v u w hdis]
  constructor
  · rintro ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum, hy⟩
    set a : ℝ := t4 / (t3 + t4) with ha_def
    have hden : t3 + t4 ≠ 0 := by positivity
    have ha0 : 0 < a := by rw [ha_def]; positivity
    have ha1 : a < 1 := by
      rw [ha_def, div_lt_one (by linarith : (0 : ℝ) < t3 + t4)]
      linarith
    have hnc := coplanar_imp_continuous_collinear x v u w hcop a (ne_of_gt ha0)
    have hdis2 : Disjoint ({x} : Set V3)
        ({v, (1 - a) • u + a • w} : Set V3) := by
      rw [Set.disjoint_singleton_left]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hxv
        exact hnc (by rw [hxv]; exact collinear3_of_eq rfl)
      · intro hxz
        exact hnc (by rw [← hxz]; exact collinear3_pair_left rfl)
    have hcoef1 : (t3 + t4) * (1 - a) = t3 := by
      rw [ha_def]; field_simp [hden]; ring
    have hcoef2 : (t3 + t4) * a = t4 := by
      rw [ha_def]; field_simp [hden]
    refine Set.mem_sUnion.mpr ⟨affGt ({x} : Set V3)
      ({v, (1 - a) • u + a • w} : Set V3), ⟨a, ha0, ha1, rfl⟩, ?_⟩
    rw [aff_gt_1_2 hdis2]
    refine ⟨t1, t2, t3 + t4, ht2, by linarith, by linarith, ?_⟩
    rw [hy, smul_add, smul_smul, smul_smul, hcoef1, hcoef2]; abel
  · rintro ⟨s, ⟨a, ha0, ha1, rfl⟩, hy⟩
    have hnc := coplanar_imp_continuous_collinear x v u w hcop a (ne_of_gt ha0)
    have hdis2 : Disjoint ({x} : Set V3)
        ({v, (1 - a) • u + a • w} : Set V3) := by
      rw [Set.disjoint_singleton_left]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hxv
        exact hnc (by rw [hxv]; exact collinear3_of_eq rfl)
      · intro hxz
        exact hnc (by rw [← hxz]; exact collinear3_pair_left rfl)
    rw [aff_gt_1_2 hdis2] at hy
    obtain ⟨t1, t2, t3, ht2, ht3, hsum, hy⟩ := hy
    refine ⟨t1, t2, t3 * (1 - a), t3 * a, ht2, mul_pos ht3 (by linarith),
      mul_pos ht3 ha0, ?_, ?_⟩
    · ring_nf; linarith [hsum]
    · rw [hy, smul_add, smul_smul, smul_smul]; abel

/-! ## aff_gt 含于 yfan / dart_leads_into（planarity.hl:13724-13805） -/

/-- HOL planarity.hl :13724-13743 `aff_gt_1_3_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E 
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==>  (aff_gt{x} {v,u,w} SUBSET yfan (x,V,E))
```

证明思路：由 `fan80` 在边 `{u,w}` 上给出 `0 < azim x u w v < π`，再用
`properties_fully_surrounded` 得四点 `{x,v,u,w}` 不共面；于是可用
`aff_gt_1_3_eq_unions_aff_gt_1_2` 把 `aff_gt {x} {v,u,w}` 写成
`⋃₀ aff_gt {x} {v,(1-a)•u+a•w}`（`0<a<1`）。对每个 `a`，用
`not_cut_in_edges_fan` 说明该 `aff_gt` 不与任何边的 `aff_ge` 相交，故
落在 `yfan = univ \ xfan` 中；集合收尾 `SET_TAC`。

候选已有引理：
- `fan80`（Kepler/Text/Fan.lean:227）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `aff_gt_1_3_eq_unions_aff_gt_1_2`（本文件上文，HOL :13645）
- `not_cut_in_edges_fan`（Kepler/Text/PlanarityNotCut.lean:1224）
- `xfan`/`yfan`（Kepler/Text/Fan.lean:154/158） -/
theorem aff_gt_1_3_subset_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u w : V3) (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt ({x} : Set V3) ({v, u, w} : Set V3) ⊆ yfan x V E := by
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hcop := properties_fully_surrounded hfan hvu huw hθ0 hθπ
  intro y hy
  rw [aff_gt_1_3_eq_unions_aff_gt_1_2 x v u w hcop] at hy
  rw [Set.mem_sUnion] at hy
  obtain ⟨s, ⟨a, ha0, ha1, rfl⟩, hys⟩ := hy
  refine ⟨trivial, ?_⟩
  intro hyx
  have hdisj := not_cut_in_edges_fan hfan hvu huw hsigma ha0 ha1 hcard hfan80
  have hmem : y ∈ affGt {x} {v, (1 - a) • u + a • w} ∩ xfan x V E := ⟨hys, hyx⟩
  rw [hdisj] at hmem
  exact hmem

/-- `Disjoint {x} {v,u,w}` 时 `affGt {x} {v,u,w}` 凸（HOL `CONVEX_AFF_GT` 的
3-1 情形；经 `AFF_GT_1_3` 的系数展开直接验证）。 -/
private theorem convex_affGt_triple {x v u w : V3}
    (hdis : Disjoint ({x} : Set V3) ({v, u, w} : Set V3)) :
    Convex ℝ (affGt ({x} : Set V3) ({v, u, w} : Set V3)) := by
  rw [AFF_GT_1_3 x v u w hdis, convex_iff_forall_pos]
  intro p hp q hq a b ha hb hab
  obtain ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum, rfl⟩ := hp
  obtain ⟨s1, s2, s3, s4, hs2, hs3, hs4, hssum, rfl⟩ := hq
  refine ⟨a * t1 + b * s1, a * t2 + b * s2, a * t3 + b * s3, a * t4 + b * s4,
    add_pos (mul_pos ha ht2) (mul_pos hb hs2),
    add_pos (mul_pos ha ht3) (mul_pos hb hs3),
    add_pos (mul_pos ha ht4) (mul_pos hb hs4), ?_, ?_⟩
  · nlinarith [hsum, hssum, hab]
  · module

/-- HOL planarity.hl :13744-13805 `aff_gt_1_3_subset_dart_leads_into_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E 
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==>  aff_gt{x} {v,u,w} SUBSET dart_leads_into x V E u w
```

证明思路：同 `aff_gt_1_3_subset_yfan` 先得四点不共面并把
`aff_gt {x} {v,u,w}` 写成射线并。由 `not_empty_rw_dart_fan` 取
`rw_dart_fan (x,u,w,v) (cos h1)` 的半径 `h1`，`DART_LEADS_INTO`
（`dartLeadsInto` 的刻画）给出 `rw_dart_fan ⊆ dart_leads_into` 且落在
`yfan` 的同一连通分量；再用 `exists_rw_dart_inter_aff_gt1_fan` 取
`y' ∈ rw_dart_fan ∩ aff_gt {x} {v,(1-a1)•u+a1•w}`，
`aff_gt_1_3_subset_yfan` 与 `CONVEX_CONNECTED`/`CONNECTED_COMPONENT_MAXIMAL`
（`IsPreconnected`/`connectedComponentIn_maximal`）把整个 `aff_gt` 收进
`dart_leads_into`。

编码缺口：HOL `DART_LEADS_INTO`/`rw_dart_avoids_fan`/`CONVEX_AFF_GT`/
`CONVEX_CONNECTED`/`CONNECTED_COMPONENT_MAXIMAL` 在仓库中的最近对应为
`dartLeadsInto` 的定义展开、`rw_dart_avoids_fan`、`convex_affGt_of_disjoint`
（private）与 Mathlib `Convex.isPreconnected`/`connectedComponentIn_maximal`。

候选已有引理：
- `dartLeadsInto`（Kepler/Text/TopologyFan.lean:4179）
- `exists_leads_into_fan`（Kepler/Text/TopologyFan.lean:4191）
- `not_empty_rw_dart_fan`（Kepler/Text/TopologyFan.lean:4125）
- `rw_dart_avoids_fan`（Kepler/Text/TopologyFan.lean:3303）
- `exists_rw_dart_inter_aff_gt1_fan`（Kepler/Text/PlanarityAngle.lean:2182）
- `expand_element_in_topological_component_yfan`（Kepler/Text/PlanarityAuto7.lean:271）
- `dartset_leads_into_is_topological_component_yfan`（Kepler/Text/PlanarityComponent.lean:535）
- `aff_gt_1_3_subset_yfan`（本文件上文，HOL :13724） -/
theorem aff_gt_1_3_subset_dart_leads_into_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (v u w : V3) (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt ({x} : Set V3) ({v, u, w} : Set V3) ⊆ dartLeadsInto x V E u w := by
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hcop := properties_fully_surrounded hfan hvu huw hθ0 hθπ
  have hdis : Disjoint ({x} : Set V3) ({v, u, w} : Set V3) :=
    (notcoplanar_disjoints x v u w hcop).2.2.2.1
  obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec hfan huw
  set h1 : ℝ := min h (Real.pi / 2) / 2 with hh1def
  have hmin0 : 0 < min h (Real.pi / 2) := lt_min hh0 (by positivity)
  have hh10 : 0 < h1 := by rw [hh1def]; exact div_pos hmin0 two_pos
  have hh1lt : h1 < h := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hmin0) (min_le_left _ _)
  have hh1pi : h1 < Real.pi / 2 := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hmin0) (min_le_right _ _)
  obtain ⟨h'', hh''0, hne⟩ :=
    exists_rw_dart_inter_aff_gt1_fan (s := h1) hfan hvu huw hsigma hh10 hh1pi
      hfan80 hcard
  set a1 : ℝ := min h'' 1 / 2 with ha1def
  have hmin1 : 0 < min h'' 1 := lt_min hh''0 one_pos
  have ha10 : 0 < a1 := by rw [ha1def]; exact div_pos hmin1 two_pos
  have ha1h'' : a1 < h'' := by
    rw [ha1def]
    exact lt_of_lt_of_le (half_lt_self hmin1) (min_le_left _ _)
  have ha11 : a1 < 1 := by
    rw [ha1def]
    exact lt_of_lt_of_le (half_lt_self hmin1) (min_le_right _ _)
  obtain ⟨y', hy'⟩ := Set.nonempty_iff_ne_empty.mpr (hne a1 ha10 ha1h'')
  obtain ⟨hy'D, hy'aff⟩ := hy'
  have hy'dl : y' ∈ dartLeadsInto x V E u w :=
    (hspec h1 y' hh10 hh1lt hy'D).1 hy'D
  have hy'affGt : y' ∈ affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
    rw [aff_gt_1_3_eq_unions_aff_gt_1_2 x v u w hcop]
    exact Set.mem_sUnion.mpr ⟨_, ⟨a1, ha10, ha11, rfl⟩, hy'aff⟩
  have hU : dartLeadsInto x V E u w ∈ topologicalComponentYfan x V E :=
    dart_leads_into_mem_topologicalComponentYfan (v := u) (u := w) hfan huw
  have heq' : dartLeadsInto x V E u w = connectedComponentIn (yfan x V E) y' :=
    expand_element_in_topological_component_yfan x V E (dartLeadsInto x V E u w) y'
      hfan hU hy'dl
  have hsubyfan : affGt ({x} : Set V3) ({v, u, w} : Set V3) ⊆ yfan x V E :=
    aff_gt_1_3_subset_yfan x V E v u w hfan hvu huw hsigma hcard hfan80
  have hpre : IsPreconnected (affGt ({x} : Set V3) ({v, u, w} : Set V3)) :=
    (convex_affGt_triple hdis).isPreconnected
  rw [heq']
  exact hpre.subset_connectedComponentIn hy'affGt hsubyfan

/-! ## 三个 aff_gt 3-1 半空间的交（planarity.hl:13806-13871） -/

/-- HOL planarity.hl :13806-13871 `inter_aff_gt_3_1_is_aff_gt_1_3`

HOL 原文：
```
!x v u w:real^3.
~coplanar {x,v,u,w}
==>
aff_gt {x,v,u} {w} INTER aff_gt {x,u,w} {v} INTER aff_gt {x,w,v} {u}=aff_gt {x} {v,u,w}
```

证明思路：`GEOM_ORIGIN_TAC x` 平移 `x = 0`；由 `notcoplanar_disjoints`
得四点互异，用三次 `AFF_GT_3_1` 与一次 `AFF_GT_1_3` 展开两边。`⊆` 方向
把三个 `3-1` 等式联立，用 `NOT_COPLANAR_0_4_IMP_INDEPENDENT`（即
`LinearIndependent ℝ ![v,u,w]`）与三向量线性无关推出各系数相等
（HOL `INDEPENDENT_3`），从而左式的四个系数满足右式的正性/和为 1；
`⊇` 方向直接把右式系数重排成三个 `3-1` 组合（`VECTOR_ARITH`）。

编码缺口：HOL `NOT_COPLANAR_0_4_IMP_INDEPENDENT`/`INDEPENDENT_3` 未以该名
移植；最近对应是 Mathlib `LinearIndependent`（cf.
Kepler/Text/Planarity.lean:2900 的用法）与 `notcoplanar_imp_notcollinear_fan`。

候选已有引理：
- `AFF_GT_3_1`（Kepler/Text/PlanarityAuto11.lean:957）
- `AFF_GT_1_3`（Kepler/Text/PlanarityAuto11.lean:1029）
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `notcoplanar_disjoint`（Kepler/Text/PlanarityAuto11.lean:1220）
- `LinearIndependent`（Mathlib/LinearAlgebra/LinearIndependent/Basic.lean） -/
private theorem mem_affineSpan_sub_of_smul_eq_neg {x y a b : V3} {p q r : ℝ}
    (hp : p ≠ 0) (h : p • (y - x) + q • (a - x) + r • (b - x) = 0) :
    y ∈ affineSpan ℝ ({x, a, b} : Set V3) := by
  have ha : a - x ∈ vectorSpan ℝ ({x, a, b} : Set V3) := by
    simpa [vsub_eq_sub] using
      vsub_mem_vectorSpan (k := ℝ) (p₁ := a) (p₂ := x) (by simp) (by simp)
  have hb : b - x ∈ vectorSpan ℝ ({x, a, b} : Set V3) := by
    simpa [vsub_eq_sub] using
      vsub_mem_vectorSpan (k := ℝ) (p₁ := b) (p₂ := x) (by simp) (by simp)
  have hqr : q • (a - x) + r • (b - x) ∈ vectorSpan ℝ ({x, a, b} : Set V3) :=
    add_mem (Submodule.smul_mem _ q ha) (Submodule.smul_mem _ r hb)
  have hpy : p • (y - x) = -(q • (a - x) + r • (b - x)) := by
    have h' : p • (y - x) + (q • (a - x) + r • (b - x)) = 0 := by
      rw [← h]; abel
    exact eq_neg_of_add_eq_zero_left h'
  have hpy_mem : p • (y - x) ∈ vectorSpan ℝ ({x, a, b} : Set V3) := by
    rw [hpy]; exact neg_mem hqr
  have hyx : y - x ∈ vectorSpan ℝ ({x, a, b} : Set V3) := by
    have := Submodule.smul_mem _ p⁻¹ hpy_mem
    rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at this
  have hx : x ∈ affineSpan ℝ ({x, a, b} : Set V3) := mem_affineSpan ℝ (by simp)
  have hdir : y - x ∈ (affineSpan ℝ ({x, a, b} : Set V3)).direction := by
    rwa [direction_affineSpan]
  have hmem := (AffineSubspace.vadd_mem_iff_mem_direction
    (s := affineSpan ℝ ({x, a, b} : Set V3)) (y - x) hx).mpr hdir
  rwa [vadd_eq_add, sub_add_cancel] at hmem

private theorem notcoplanar_smul_sub_eq_zero {x v u w : V3} {p q r : ℝ}
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (h : p • (v - x) + q • (u - x) + r • (w - x) = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hp
    have hv : v ∈ affineSpan ℝ ({x, u, w} : Set V3) :=
      mem_affineSpan_sub_of_smul_eq_neg (a := u) (b := w) hp h
    exact hcop ⟨x, u, w, fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact hv
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)⟩
  · by_contra hq
    have h' : q • (u - x) + p • (v - x) + r • (w - x) = 0 := by
      rw [← h]; abel
    have hu : u ∈ affineSpan ℝ ({x, v, w} : Set V3) :=
      mem_affineSpan_sub_of_smul_eq_neg (a := v) (b := w) hq h'
    exact hcop ⟨x, v, w, fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · exact hu
      · exact subset_affineSpan ℝ _ (by simp)⟩
  · by_contra hr
    have h' : r • (w - x) + p • (v - x) + q • (u - x) = 0 := by
      rw [← h]; abel
    have hw : w ∈ affineSpan ℝ ({x, v, u} : Set V3) :=
      mem_affineSpan_sub_of_smul_eq_neg (a := v) (b := u) hr h'
    exact hcop ⟨x, v, u, fun z hz => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · exact subset_affineSpan ℝ _ (by simp)
      · exact hw⟩

theorem inter_aff_gt_3_1_is_aff_gt_1_3 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    affGt ({x, v, u} : Set V3) {w} ∩ affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, w, v} : Set V3) {u} =
        affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
  obtain ⟨hdis1, hdis2, hdis3, hdis4, -, -, -, -⟩ :=
    notcoplanar_disjoints x v u w hcop
  ext y
  constructor
  · intro hy
    simp only [Set.mem_inter_iff] at hy
    obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
    rw [AFF_GT_3_1 x v u w hdis1, Set.mem_setOf_eq] at hy1
    rw [AFF_GT_3_1 x u w v hdis2, Set.mem_setOf_eq] at hy2
    rw [AFF_GT_3_1 x w v u hdis3, Set.mem_setOf_eq] at hy3
    rw [AFF_GT_1_3 x v u w hdis4, Set.mem_setOf_eq]
    obtain ⟨a1, a2, a3, a4, ha4, hasum, hay⟩ := hy1
    obtain ⟨b1, b2, b3, b4, hb4, hbsum, hby⟩ := hy2
    obtain ⟨c1, c2, c3, c4, hc4, hcsum, hcy⟩ := hy3
    have heq1 : (a2 - b4) • (v - x) + (a3 - b2) • (u - x) +
        (a4 - b3) • (w - x) = 0 := by
      have hEq : a1 • x + a2 • v + a3 • u + a4 • w =
          b1 • x + b2 • u + b3 • w + b4 • v := by rw [← hay, hby]
      have h1 : a1 = 1 - a2 - a3 - a4 := by linarith
      have h2 : b1 = 1 - b2 - b3 - b4 := by linarith
      have hdiff : (a2 - b4) • (v - x) + (a3 - b2) • (u - x) +
          (a4 - b3) • (w - x) =
          (a1 • x + a2 • v + a3 • u + a4 • w) -
            (b1 • x + b2 • u + b3 • w + b4 • v) := by
        rw [h1, h2]; module
      rw [hdiff, hEq, sub_self]
    have heq2 : (b4 - c3) • (v - x) + (b2 - c4) • (u - x) +
        (b3 - c2) • (w - x) = 0 := by
      have hEq : b1 • x + b2 • u + b3 • w + b4 • v =
          c1 • x + c2 • w + c3 • v + c4 • u := by rw [← hby, hcy]
      have h1 : b1 = 1 - b2 - b3 - b4 := by linarith
      have h2 : c1 = 1 - c2 - c3 - c4 := by linarith
      have hdiff : (b4 - c3) • (v - x) + (b2 - c4) • (u - x) +
          (b3 - c2) • (w - x) =
          (b1 • x + b2 • u + b3 • w + b4 • v) -
            (c1 • x + c2 • w + c3 • v + c4 • u) := by
        rw [h1, h2]; module
      rw [hdiff, hEq, sub_self]
    obtain ⟨ha2b4, ha3b2, _ha4b3⟩ := notcoplanar_smul_sub_eq_zero hcop heq1
    obtain ⟨_hb4c3, hb2c4, _hb3c2⟩ := notcoplanar_smul_sub_eq_zero hcop heq2
    have ha2pos : 0 < a2 := by
      have h : a2 = b4 := sub_eq_zero.mp ha2b4
      rw [h]; exact hb4
    have ha3pos : 0 < a3 := by
      have h1 : a3 = b2 := sub_eq_zero.mp ha3b2
      have h2 : b2 = c4 := sub_eq_zero.mp hb2c4
      rw [h1, h2]; exact hc4
    exact ⟨a1, a2, a3, a4, ha2pos, ha3pos, ha4, hasum, hay⟩
  · intro hy
    rw [AFF_GT_1_3 x v u w hdis4, Set.mem_setOf_eq] at hy
    obtain ⟨t1, t2, t3, t4, ht2, ht3, ht4, htsum, hty⟩ := hy
    simp only [Set.mem_inter_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [AFF_GT_3_1 x v u w hdis1, Set.mem_setOf_eq]
      exact ⟨t1, t2, t3, t4, ht4, htsum, hty⟩
    · rw [AFF_GT_3_1 x u w v hdis2, Set.mem_setOf_eq]
      refine ⟨t1, t3, t4, t2, ht2, ?_, ?_⟩
      · linarith
      · rw [hty]; module
    · rw [AFF_GT_3_1 x w v u hdis3, Set.mem_setOf_eq]
      refine ⟨t1, t4, t2, t3, ht3, ?_, ?_⟩
      · linarith
      · rw [hty]; module

/-! ## cross/dot 与 aff_gt 3-1 半空间（planarity.hl:13872-14074） -/

/-- 由线性关系 `c0•(p-x)+c1•(a-x)+c2•(b-x)=0`（`c0 ≠ 0`）推出
`p ∈ affineSpan{x,a,b}`：解出 `p-x` 作为 `a-x,b-x` 的线性组合，再用
`vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan`。 -/
private lemma mem_affineSpan_of_smul_relation {x a b p : V3} {c0 c1 c2 : ℝ}
    (hc0 : c0 ≠ 0)
    (hrel : c0 • (p - x) + c1 • (a - x) + c2 • (b - x) = 0) :
    p ∈ (affineSpan ℝ ({x, a, b} : Set V3) : Set V3) := by
  have hp : p - x = (-(c1 * c0⁻¹)) • (a - x) + (-(c2 * c0⁻¹)) • (b - x) := by
    have h1 : c0 • (p - x) = -(c1 • (a - x) + c2 • (b - x)) := by
      linear_combination (norm := module) hrel
    calc p - x = c0⁻¹ • (c0 • (p - x)) := (inv_smul_smul₀ hc0 _).symm
      _ = c0⁻¹ • (-(c1 • (a - x) + c2 • (b - x))) := by rw [h1]
      _ = (-(c1 * c0⁻¹)) • (a - x) + (-(c2 * c0⁻¹)) • (b - x) := by module
  have ha : (a - x : V3) ∈ vectorSpan ℝ ({x, a, b} : Set V3) :=
    vsub_mem_vectorSpan ℝ (by simp) (by simp)
  have hb : (b - x : V3) ∈ vectorSpan ℝ ({x, a, b} : Set V3) :=
    vsub_mem_vectorSpan ℝ (by simp) (by simp)
  have hmem : (p - x : V3) ∈ vectorSpan ℝ ({x, a, b} : Set V3) := by
    rw [hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ hb)
  have hx : x ∈ (affineSpan ℝ ({x, a, b} : Set V3) : Set V3) := mem_affineSpan ℝ (by simp)
  have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hx hmem
  simpa using this

private lemma coplanar_of_v1_mem (x v u v1 : V3)
    (h : v1 ∈ (affineSpan ℝ ({x, v, u} : Set V3) : Set V3)) :
    Coplanar ({x, v, u, v1} : Set V3) := by
  refine ⟨x, v, u, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact h

private lemma coplanar_of_v_mem (x v u v1 : V3)
    (h : v ∈ (affineSpan ℝ ({x, u, v1} : Set V3) : Set V3)) :
    Coplanar ({x, v, u, v1} : Set V3) := by
  refine ⟨x, u, v1, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact h
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)

private lemma coplanar_of_u_mem (x v u v1 : V3)
    (h : u ∈ (affineSpan ℝ ({x, v, v1} : Set V3) : Set V3)) :
    Coplanar ({x, v, u, v1} : Set V3) := by
  refine ⟨x, v, v1, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact h
  · exact mem_affineSpan ℝ (by simp)

/-- HOL planarity.hl :13872-13883 `coplanar_cross_dot`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 v1:real^3.
~coplanar {x,v,u,v1}
==> ~(((v-x) cross (u-x)) dot (v1-x)= &0)
```

证明思路：反设 `((v-x)⨯(u-x))·(v1-x) = 0`。用 `CROSS_TRIPLE`
（`crossProduct` 的循环等式）与 `DOT_SYM` 把该式化为三向量
`v-x,u-x,v1-x` 的行列式为零，再用 `COPLANAR_DET_EQ_0`（行列式为 0
⟺ 三点共面 ⟺ 四点共面）与 `hcop` 矛盾。HOL 即
`MATCH_MP_TAC MONO_NOT` 后重写。

编码缺口：HOL `CROSS_TRIPLE`/`DOT_CROSS_DET`/`COPLANAR_DET_EQ_0` 未以该名
移植；最近对应是 Mathlib `crossProduct` 的
`cross_dot`/`det` 恒等式与 `Coplanar` 的 `affineSpan` 定义。

候选已有引理：
- `Coplanar`（Kepler/Geom/Coplanar.lean:23）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `crossProduct`（Mathlib/LinearAlgebra/CrossProduct.lean）
- `dotProduct`（Mathlib/Analysis/InnerProductSpace/...） -/
theorem coplanar_cross_dot (x v u v1 : V3)
    (hcop : ¬ Coplanar ({x, v, u, v1} : Set V3)) :
    crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((v1 - x : V3) : Fin 3 → ℝ) ≠ 0 := by
  by_contra h
  apply hcop
  let vec : Fin 3 → V3 := ![v1 - x, v - x, u - x]
  let f : V3 →ₗ[ℝ] (Fin 3 → ℝ) := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
  let mat : Matrix (Fin 3) (Fin 3) ℝ := f ∘ vec
  have hmat : mat = ![((v1 - x : V3) : Fin 3 → ℝ), ((v - x : V3) : Fin 3 → ℝ),
      ((u - x : V3) : Fin 3 → ℝ)] := by
    funext i
    fin_cases i <;> rfl
  have hdet : Matrix.det mat = 0 := by
    have hh : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((v1 - x : V3) : Fin 3 → ℝ) = 0 := h
    rw [dotProduct_comm] at hh
    rw [triple_product_eq_det ((v1 - x : V3) : Fin 3 → ℝ) ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)] at hh
    rwa [hmat]
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
  have hnotli_mat : ¬ LinearIndependent ℝ mat := by
    intro hli
    have h1 : IsUnit mat := (Matrix.linearIndependent_rows_iff_isUnit (A := mat)).mp hli
    have h2 : IsUnit (Matrix.det mat) := (Matrix.isUnit_iff_isUnit_det mat).mp h1
    exact h2.ne_zero hdet
  have hnotli_vec : ¬ LinearIndependent ℝ vec := by
    rw [← LinearMap.linearIndependent_iff f hker]
    exact hnotli_mat
  rw [Fintype.not_linearIndependent_iff] at hnotli_vec
  obtain ⟨g, hg, i, hi⟩ := hnotli_vec
  rw [Fin.sum_univ_three] at hg
  simp only [vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hg
  fin_cases i
  · refine coplanar_of_v1_mem x v u v1 ?_
    exact mem_affineSpan_of_smul_relation (a := v) (b := u) (p := v1) hi hg
  · refine coplanar_of_v_mem x v u v1 ?_
    refine mem_affineSpan_of_smul_relation (a := u) (b := v1) (p := v) (c0 := g 1)
      (c1 := g 2) (c2 := g 0) hi ?_
    linear_combination (norm := module) hg
  · refine coplanar_of_u_mem x v u v1 ?_
    refine mem_affineSpan_of_smul_relation (a := v) (b := v1) (p := u) (c0 := g 2)
      (c1 := g 1) (c2 := g 0) hi ?_
    linear_combination (norm := module) hg

/-- HOL planarity.hl :13897-14074 `aff_gt_3_1_rep_cross_dot`

HOL 原文：
```
!x:real^3  v:real^3 u:real^3 w:real^3.
~coplanar {x,v,u,w} 
/\ &0< ((v-x) cross (u-x)) dot (w-x)

==> aff_gt {x,v,u} {w} ={y:real^3|  &0< (((v-x) cross (u-x)) dot (y-x)) }
```

证明思路：设 `n = (v-x)⨯(u-x)`。`⊆` 方向由 `AFF_GT_3_1` 展开
`y = t1•x+t2•v+t3•u+t4•w`（`t4>0`，系数和 1），则
`y-x = t2•(v-x)+t3•(u-x)+t4•(w-x)`，用 `cross`/`dot` 的双线性与
`cross_refl`、`dot_cross_self` 化简得 `n·(y-x) = t4·(n·(w-x)) > 0`。
`⊇` 方向由 `properties_coordinate` 取标准正交标架 `e1,e2,e3`，
把 `y-x = x''₁•e1+x''₂•e2+x''₃•e3` 展成坐标，`n·(y-x) > 0` 化为关于
坐标的线性不等式，解出 `t2,t3,t4`（用 `CRAMER`/`CRAMER_LEMMA1` 的线性
方程组），从而 `y ∈ affGt {x,v,u} {w}`。

编码缺口：HOL `properties_coordinate`/`ORTHONORMAL_IMP_SPANNING`/
`ORTHONORMAL_CROSS`/`CRAMER` 未以这些名移植；最近对应是
`e1Fan`/`e2Fan`/`e3Fan`（Kepler/Text/TopologyFan.lean:2486 附近）与
Mathlib 的 `Matrix.cramer`/`Matrix.det_updateCol_sum`。

候选已有引理：
- `AFF_GT_3_1`（Kepler/Text/PlanarityAuto11.lean:957）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `e1Fan`/`e2Fan`/`e3Fan`（Kepler/Text/TopologyFan.lean:2486 附近）
- `crossProduct`（Mathlib/LinearAlgebra/CrossProduct.lean） -/
theorem aff_gt_3_1_rep_cross_dot (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hpos : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((w - x : V3) : Fin 3 → ℝ)) :
    affGt ({x, v, u} : Set V3) {w} =
      {y : V3 | 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} := by
  sorry

/-! ## aff_gt 1-3 与 aff_ge 补集的开性（planarity.hl:14075-14124） -/

/-- HOL planarity.hl :14075-14114 `OPEN_AFF_GT_1_3`

HOL 原文：
```
!x v u w:real^3.
~coplanar {x,v,u,w}
==>
open (aff_gt {x} {v,u,w})
```

证明思路：`GEOM_ORIGIN_TAC x` 后由
`inter_aff_gt_3_1_is_aff_gt_1_3` 把 `aff_gt {x} {v,u,w}` 写成三个
`aff_gt {·,·,·} {·}` 之交。`coplanar_cross_dot` 给出
`(v⨯u)·w ≠ 0`，分正负两种情形，对每个 `3-1` 半空间用
`aff_gt_3_1_rep_cross_dot` 化为严格半空间
`{y | 0 < n·(y-x)}`，再由 `isOpen_lt`（`OPEN_HALFSPACE_GT`）与
`IsOpen.inter` 得交开。

候选已有引理：
- `inter_aff_gt_3_1_is_aff_gt_1_3`（本文件上文，HOL :13806）
- `coplanar_cross_dot`（本文件上文，HOL :13872）
- `aff_gt_3_1_rep_cross_dot`（本文件上文，HOL :13897）
- `isOpen_lt`（Mathlib/Topology/Order/OrderClosed.lean:587）
- `IsOpen.inter`（Mathlib/Topology/Defs/Basic.lean） -/
theorem OPEN_AFF_GT_1_3 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    IsOpen (affGt ({x} : Set V3) ({v, u, w} : Set V3)) := by
  sorry

/-- HOL planarity.hl :14115-14124 `OPEN_DIFF_AFF_GE`

HOL 原文：
```
!x v u w:real^3.
open ((:real^3) DIFF (aff_ge {x} {v,u,w}))
```

证明思路：`OPEN_CLOSED` 把目标化为 `aff_ge {x} {v,u,w}` 闭。由
`AFF_GE_1_3`/`aff_ge_1_3` 的显式非负组合刻画，`aff_ge {x} {v,u,w}` 是
有限个闭半空间之交，或用 `CLOSED_AFF_GE`（`affGe` 对任意有限点集闭）
直接得闭性；集合恒等式 `univ \ (univ \ A) = A` 收尾。

编码缺口：HOL `CLOSED_AFF_GE` 未以该名移植，仓库只有
`closed_aff_ge_1_2`（Kepler/Text/TopologyFan.lean:2648）与
`closed_aff_ge_2_1`（Kepler/Text/TopologyFan.lean:2635）等低阶形状；
一般 `affGe {x} {v,u,w}` 的闭性需由 `AFF_GE_1_3` 的半空间表示补证。

候选已有引理：
- `affGe`（Kepler/Geom/Aff.lean:42）
- `AFF_GE_1_3`（Kepler/Text/PlanarityAuto11.lean:1136）
- `closed_aff_ge_1_2`（Kepler/Text/TopologyFan.lean:2648）
- `closed_aff_ge_2_1`（Kepler/Text/TopologyFan.lean:2635）
- `isClosed_iff_isOpen_compl`（Mathlib/Topology/...） -/
theorem OPEN_DIFF_AFF_GE (x v u w : V3) :
    IsOpen ((Set.univ : Set V3) \ affGe ({x} : Set V3) ({v, u, w} : Set V3)) := by
  sorry

end Kepler.Text
