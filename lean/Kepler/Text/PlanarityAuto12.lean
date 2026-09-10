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

/-- 叉积平面分解的辅助恒等式（无假设版本）：对 `n = a ⨯ b`，
`(n·n) • z = ((a·z)(b·b) - (b·z)(a·b)) • a +
            ((b·z)(a·a) - (a·z)(a·b)) • b + (n·z) • n`。 -/
private lemma crossProduct_plane_decomp_aux (a b z : Fin 3 → ℝ) :
    (crossProduct a b ⬝ᵥ crossProduct a b) • z =
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
      ((crossProduct a b) ⬝ᵥ z) • crossProduct a b := by
  have h1 : crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) =
      (crossProduct a b ⬝ᵥ crossProduct a b) • z -
        (z ⬝ᵥ crossProduct a b) • crossProduct a b :=
    cross_cross_eq_smul_sub_smul (crossProduct a b) z (crossProduct a b)
  have h2 : crossProduct (crossProduct a b) z =
      (a ⬝ᵥ z) • b - (b ⬝ᵥ z) • a :=
    cross_cross_eq_smul_sub_smul a b z
  have hb : crossProduct b (crossProduct a b) =
      (b ⬝ᵥ b) • a - (a ⬝ᵥ b) • b :=
    cross_cross_eq_smul_sub_smul' b a b
  have ha : crossProduct a (crossProduct a b) =
      (a ⬝ᵥ b) • a - (a ⬝ᵥ a) • b :=
    cross_cross_eq_smul_sub_smul' a a b
  have h1' : crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) =
      ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
      ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b := by
    rw [h2, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hb, ha]
    module
  calc (crossProduct a b ⬝ᵥ crossProduct a b) • z =
        crossProduct (crossProduct (crossProduct a b) z) (crossProduct a b) +
          (z ⬝ᵥ crossProduct a b) • crossProduct a b := by
        rw [h1]; abel
    _ = ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
          (z ⬝ᵥ crossProduct a b) • crossProduct a b := by rw [h1']
    _ = ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b +
          ((crossProduct a b) ⬝ᵥ z) • crossProduct a b := by
        rw [dotProduct_comm z (crossProduct a b)]

/-- 平面分解：`n = a ⨯ b ≠ 0` 且 `n·z = 0` 时，
`z = ((n·n)⁻¹ * ((a·z)(b·b) - (b·z)(a·b))) • a +
     ((n·n)⁻¹ * ((b·z)(a·a) - (a·z)(a·b))) • b`。 -/
private lemma crossProduct_plane_decomp {a b z : Fin 3 → ℝ}
    (hn : crossProduct a b ≠ 0) (hz : (crossProduct a b) ⬝ᵥ z = 0) :
    z = (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))) • a +
        (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))) • b := by
  have hnn : crossProduct a b ⬝ᵥ crossProduct a b ≠ 0 := by
    intro h0
    apply hn
    funext i
    have hsum : ∑ j, (crossProduct a b) j * (crossProduct a b) j = 0 := by
      simpa only [dotProduct] using h0
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg ((crossProduct a b) j))).mp hsum
    exact mul_self_eq_zero.mp (h3 i (Finset.mem_univ i))
  have hmain := crossProduct_plane_decomp_aux a b z
  rw [hz, zero_smul, add_zero] at hmain
  calc z = (crossProduct a b ⬝ᵥ crossProduct a b)⁻¹ •
        ((crossProduct a b ⬝ᵥ crossProduct a b) • z) :=
        (inv_smul_smul₀ hnn z).symm
    _ = (crossProduct a b ⬝ᵥ crossProduct a b)⁻¹ •
        (((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b)) • a +
         ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b)) • b) := by rw [hmain]
    _ = (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((a ⬝ᵥ z) * (b ⬝ᵥ b) - (b ⬝ᵥ z) * (a ⬝ᵥ b))) • a +
        (((crossProduct a b ⬝ᵥ crossProduct a b)⁻¹) *
          ((b ⬝ᵥ z) * (a ⬝ᵥ a) - (a ⬝ᵥ z) * (a ⬝ᵥ b))) • b := by
        rw [smul_add, smul_smul, smul_smul]

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
  obtain ⟨hdis, -, -, -, -, -, -, -⟩ := notcoplanar_disjoints x v u w hcop
  rw [AFF_GT_3_1 x v u w hdis]
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨t1, t2, t3, t4, ht4, hsum, hy⟩
    have hz : (y - x : V3) = t2 • (v - x) + t3 • (u - x) + t4 • (w - x) := by
      have ht1 : t1 = 1 - t2 - t3 - t4 := by linarith
      rw [hy, ht1]
      module
    have hz' : ((y - x : V3) : Fin 3 → ℝ) =
        t2 • ((v - x : V3) : Fin 3 → ℝ) + t3 • ((u - x : V3) : Fin 3 → ℝ) +
          t4 • ((w - x : V3) : Fin 3 → ℝ) := by
      have h := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) hz
      simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
    rw [hz']
    have ha : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((v - x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]; exact dot_self_cross _ _
    have hb : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ
        ((u - x : V3) : Fin 3 → ℝ) = 0 := by
      rw [dotProduct_comm]; exact dot_cross_self _ _
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, ha, hb, mul_zero,
      zero_add, add_zero]
    exact mul_pos ht4 hpos
  · intro hy
    let a : Fin 3 → ℝ := ((v - x : V3) : Fin 3 → ℝ)
    let b : Fin 3 → ℝ := ((u - x : V3) : Fin 3 → ℝ)
    let c : Fin 3 → ℝ := ((w - x : V3) : Fin 3 → ℝ)
    let z : Fin 3 → ℝ := ((y - x : V3) : Fin 3 → ℝ)
    let n : Fin 3 → ℝ := crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)
    have hd : 0 < n ⬝ᵥ c := by dsimp only [n, a, b, c]; exact hpos
    have hnz : 0 < n ⬝ᵥ z := by dsimp only [n, a, b, z]; exact hy
    have hn : n ≠ 0 := by
      intro h0
      rw [h0, zero_dotProduct] at hd
      exact lt_irrefl 0 hd
    let t4 : ℝ := (n ⬝ᵥ z) / (n ⬝ᵥ c)
    have ht4 : 0 < t4 := by dsimp only [t4]; exact div_pos hnz hd
    let z' : Fin 3 → ℝ := z - t4 • c
    have hz' : n ⬝ᵥ z' = 0 := by
      dsimp only [z', t4]
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      field_simp [hd.ne']
      ring
    have hn_ab : crossProduct a b ≠ 0 := by
      dsimp only [a, b]
      dsimp only [n] at hn
      exact hn
    have hz'_ab : crossProduct a b ⬝ᵥ z' = 0 := by
      dsimp only [a, b]
      dsimp only [n] at hz'
      exact hz'
    have hdecomp := crossProduct_plane_decomp (a := a) (b := b) (z := z') hn_ab hz'_ab
    obtain ⟨A, B, hAB⟩ : ∃ A B : ℝ, z' = A • a + B • b := ⟨_, _, hdecomp⟩
    refine ⟨1 - A - B - t4, A, B, t4, ht4, by ring, ?_⟩
    have hz_eq : z = A • a + B • b + t4 • c := by
      rw [← hAB]
      dsimp only [z']
      abel
    have hzV : (y - x : V3) = A • (v - x) + B • (u - x) + t4 • (w - x) := by
      have h := congrArg (WithLp.toLp 2) hz_eq
      simpa only [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_ofLp, a, b, c, z] using h
    calc y = (y - x) + x := by abel
      _ = (A • (v - x) + B • (u - x) + t4 • (w - x)) + x := by rw [hzV]
      _ = (1 - A - B - t4) • x + A • v + B • u + t4 • w := by module

private theorem continuous_vsub_ofLp (x : V3) :
    Continuous (fun y : V3 => ((y - x : V3) : Fin 3 → ℝ)) :=
  (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_id.sub continuous_const)

private theorem isOpen_dot_pos (x : V3) (n : Fin 3 → ℝ) :
    IsOpen {y : V3 | 0 < n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} := by
  have hcont : Continuous (fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) :=
    continuous_const.dotProduct (continuous_vsub_ofLp x)
  exact isOpen_lt (f := fun _ : V3 => (0 : ℝ))
    (g := fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) continuous_const hcont

private theorem isOpen_dot_neg (x : V3) (n : Fin 3 → ℝ) :
    IsOpen {y : V3 | n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) < 0} := by
  have hcont : Continuous (fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) :=
    continuous_const.dotProduct (continuous_vsub_ofLp x)
  exact isOpen_lt (f := fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ))
    (g := fun _ : V3 => (0 : ℝ)) hcont continuous_const

private theorem isOpen_affGt_3_1 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    IsOpen (affGt ({x, v, u} : Set V3) {w}) := by
  have hne := coplanar_cross_dot x v u w hcop
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hcop' : ¬ Coplanar ({x, u, v, w} : Set V3) := by
      have he : ({x, u, v, w} : Set V3) = {x, v, u, w} := by
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [he]
    have hpos' : 0 < crossProduct ((u - x : V3) : Fin 3 → ℝ)
        ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) := by
      rw [← cross_anticomm, neg_dotProduct]
      linarith
    have heq := aff_gt_3_1_rep_cross_dot x u v w hcop' hpos'
    have hseteq : ({x, v, u} : Set V3) = {x, u, v} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hseteq, heq]
    have hset2 : {y : V3 | 0 < crossProduct ((u - x : V3) : Fin 3 → ℝ)
        ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} =
        {y : V3 | crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((u - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) < 0} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [← cross_anticomm, neg_dotProduct]
      constructor <;> intro h <;> linarith
    rw [hset2]
    exact isOpen_dot_neg x _
  · have heq := aff_gt_3_1_rep_cross_dot x v u w hcop hpos
    rw [heq]
    exact isOpen_dot_pos x _

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
  rw [← inter_aff_gt_3_1_is_aff_gt_1_3 x v u w hcop]
  have h2 : ¬ Coplanar ({x, u, w, v} : Set V3) := by
    have he : ({x, u, w, v} : Set V3) = {x, v, u, w} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [he]
  have h3 : ¬ Coplanar ({x, w, v, u} : Set V3) := by
    have he : ({x, w, v, u} : Set V3) = {x, v, u, w} := by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [he]
  exact ((isOpen_affGt_3_1 x v u w hcop).inter
    (isOpen_affGt_3_1 x u w v h2)).inter (isOpen_affGt_3_1 x w v u h3)

/-! ### Helpers for `OPEN_DIFF_AFF_GE`

`affGe {x} {v,u,w}` is a closed set: away from the degenerate case `x ∈ {v,u,w}`
it is the translate of the cone generated by `v-x, u-x, w-x`; a finitely
generated cone is closed (finitely many generators, Carathéodory reduction to
a linearly independent subset, then a closed embedding).  When `x` is one of
the three points the set is the convex hull of `{v,u,w}`. -/

private def coneF {n : ℕ} (v : Fin n → V3) : Set V3 :=
  {z : V3 | ∃ c : Fin n → ℝ, (∀ j, 0 ≤ c j) ∧ z = ∑ j, c j • v j}

private def cone1 (a : V3) : Set V3 :=
  {z : V3 | ∃ s : ℝ, 0 ≤ s ∧ z = s • a}

private def cone2 (a b : V3) : Set V3 :=
  {z : V3 | ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ z = s • a + t • b}

private def cone3 (a b c : V3) : Set V3 :=
  {z : V3 | ∃ s t r : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ 0 ≤ r ∧ z = s • a + t • b + r • c}

private theorem cone2_eq_coneF (a b : V3) : cone2 a b = coneF ![a, b] := by
  ext z; constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    refine ⟨![s, t], fun j => by fin_cases j <;> simp [hs, ht], ?_⟩
    simp [Fin.sum_univ_two]
  · rintro ⟨f, hf, hz⟩
    exact ⟨f 0, f 1, hf 0, hf 1, by rw [hz]; simp [Fin.sum_univ_two]⟩

private theorem cone3_eq_coneF (a b c : V3) : cone3 a b c = coneF ![a, b, c] := by
  ext z; constructor
  · rintro ⟨s, t, r, hs, ht, hr, rfl⟩
    refine ⟨![s, t, r], fun j => by fin_cases j <;> simp [hs, ht, hr], ?_⟩
    simp [Fin.sum_univ_three]
  · rintro ⟨f, hf, hz⟩
    exact ⟨f 0, f 1, f 2, hf 0, hf 1, hf 2, by rw [hz]; simp [Fin.sum_univ_three]⟩

private theorem isClosed_coneF {n : ℕ} {v : Fin n → V3}
    (hli : LinearIndependent ℝ v) : IsClosed (coneF v) := by
  let L : (Fin n → ℝ) →ₗ[ℝ] V3 :=
    { toFun := fun c => ∑ j, c j • v j
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        simp [Finset.smul_sum, mul_smul] }
  have hker : L.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro c d hcd
    funext j
    have h0 : ∑ k, (c k - d k) • v k = 0 := by
      have h1 : L (c - d) = 0 := by rw [map_sub, hcd, sub_self]
      change (∑ k, (c - d) k • v k) = 0 at h1
      simpa only [Pi.sub_apply] using h1
    have := Fintype.linearIndependent_iff.mp hli (fun k => c k - d k) h0 j
    linarith
  have hemb : Topology.IsClosedEmbedding L := L.isClosedEmbedding_of_injective hker
  let O : Set (Fin n → ℝ) := {c : Fin n → ℝ | ∀ j, 0 ≤ c j}
  have hO : IsClosed O := by
    rw [show O = ⋂ j, {c : Fin n → ℝ | 0 ≤ c j} by
      ext c; simp [O]]
    exact isClosed_iInter (fun j => isClosed_Ici.preimage (continuous_apply j))
  have hset : coneF v = L '' O := by
    ext z; constructor
    · rintro ⟨c, hc, hz⟩; exact ⟨c, hc, by rw [hz]; rfl⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, rfl⟩
  rw [hset]
  exact hemb.isClosedMap O hO

private theorem isClosed_cone1 (a : V3) : IsClosed (cone1 a) := by
  by_cases ha : a = 0
  · have h0 : cone1 a = {0} := by
      ext z; constructor
      · rintro ⟨s, _, rfl⟩; rw [ha, smul_zero]; simp
      · intro hz; rw [hz]; exact ⟨0, le_refl 0, by rw [ha, smul_zero]⟩
    rw [h0]; exact isClosed_singleton
  · have hset : cone1 a = (fun t : ℝ => t • a) '' Set.Ici (0 : ℝ) := by
      ext z; constructor
      · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    rw [hset]
    exact (isClosedEmbedding_smul_left ha).isClosedMap (Set.Ici (0 : ℝ)) isClosed_Ici

/-- If `coef` is a nonnegative combination of the vectors `v`, and the `v j` are
linearly dependent, then the same vector is a nonnegative combination with at
least one coefficient equal to `0` (Carathéodory reduction for cones). -/
private theorem exists_nonneg_rep_with_zero {n : ℕ}
    {v : Fin n → V3} {coef : Fin n → ℝ}
    (hrel : ∃ g : Fin n → ℝ, (∑ j, g j • v j = 0) ∧ (∃ j, g j ≠ 0))
    (hcoef : ∀ j, 0 ≤ coef j) :
    ∃ coef' : Fin n → ℝ, (∀ j, 0 ≤ coef' j) ∧ (∃ j, coef' j = 0) ∧
      (∑ j, coef' j • v j = ∑ j, coef j • v j) := by
  obtain ⟨g, hgsum, j, hgj⟩ := hrel
  have hrel' : ∃ g' : Fin n → ℝ, (∑ k, g' k • v k = 0) ∧ (∃ k, 0 < g' k) := by
    by_cases h : ∃ k, 0 < g k
    · obtain ⟨k, hk⟩ := h; exact ⟨g, hgsum, k, hk⟩
    · push Not at h
      refine ⟨-g, ?_, j, ?_⟩
      · have : ∑ k, (-g) k • v k = -∑ k, g k • v k := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [Pi.neg_apply, neg_smul]
        rw [this, hgsum, neg_zero]
      · have : g j < 0 := lt_of_le_of_ne (h j) hgj
        simpa using neg_pos.mpr this
  obtain ⟨g', hg'sum, j, hg'j⟩ := hrel'
  let S : Finset (Fin n) := Finset.univ.filter (fun k => 0 < g' k)
  have hSne : S.Nonempty := ⟨j, by simp [S, hg'j]⟩
  obtain ⟨j0, hj0S, hj0min⟩ := Finset.exists_min_image S (fun k => coef k / g' k) hSne
  have hg'j0 : 0 < g' j0 := (Finset.mem_filter.mp hj0S).2
  set lam : ℝ := coef j0 / g' j0 with hlam
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]; exact div_nonneg (hcoef j0) (le_of_lt hg'j0)
  refine ⟨fun k => coef k - lam * g' k, ?_, ⟨j0, ?_⟩, ?_⟩
  · intro k
    by_cases hk : k ∈ S
    · have hg'k : 0 < g' k := (Finset.mem_filter.mp hk).2
      have hle : lam ≤ coef k / g' k := by rw [hlam]; exact hj0min k hk
      have h1 : lam * g' k ≤ coef k := by
        have := mul_le_mul_of_nonneg_right hle (le_of_lt hg'k)
        rwa [div_mul_cancel₀ _ (ne_of_gt hg'k)] at this
      linarith
    · have hg'k : g' k ≤ 0 := by
        have := Finset.mem_filter.not.mp hk
        simp only [Finset.mem_univ, true_and] at this
        exact not_lt.mp this
      have h2 : lam * g' k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam_nonneg hg'k
      linarith [hcoef k]
  · simp only [hlam]
    rw [div_mul_cancel₀ _ (ne_of_gt hg'j0), sub_self]
  · have hsum_eq : ∑ k, (coef k - lam * g' k) • v k =
        ∑ k, coef k • v k - lam • ∑ k, g' k • v k := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [sub_smul, mul_smul]
    rw [hsum_eq, hg'sum, smul_zero, sub_zero]

private theorem cone2_eq_union_single (a b : V3)
    (hdep : ¬ LinearIndependent ℝ ![a, b]) :
    cone2 a b = cone1 a ∪ cone1 b := by
  ext z; constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    obtain ⟨coef', hcoef', hzero, hsum⟩ :=
      exists_nonneg_rep_with_zero (v := ![a, b]) (coef := ![s, t])
        (Fintype.not_linearIndependent_iff.mp hdep)
        (by intro j; fin_cases j <;> simp [hs, ht])
    obtain ⟨j0, hj0⟩ := hzero
    have hsum2 : s • a + t • b = coef' 0 • a + coef' 1 • b := by
      simpa [Fin.sum_univ_two] using hsum.symm
    rw [hsum2]
    have hj01 : j0 = 0 ∨ j0 = 1 := by fin_cases j0 <;> simp
    rcases hj01 with rfl | rfl
    · right
      refine ⟨coef' 1, hcoef' 1, ?_⟩
      rw [hj0, zero_smul, zero_add]
    · left
      refine ⟨coef' 0, hcoef' 0, ?_⟩
      rw [hj0, zero_smul, add_zero]
  · rintro (h | h)
    · obtain ⟨s, hs, rfl⟩ := h
      exact ⟨s, 0, hs, le_refl 0, by rw [zero_smul, add_zero]⟩
    · obtain ⟨t, ht, rfl⟩ := h
      exact ⟨0, t, le_refl 0, ht, by rw [zero_smul, zero_add]⟩

private theorem cone3_eq_union_pair (a b c : V3)
    (hdep : ¬ LinearIndependent ℝ ![a, b, c]) :
    cone3 a b c = cone2 a b ∪ cone2 a c ∪ cone2 b c := by
  ext z; constructor
  · rintro ⟨s, t, r, hs, ht, hr, rfl⟩
    obtain ⟨coef', hcoef', hzero, hsum⟩ :=
      exists_nonneg_rep_with_zero (v := ![a, b, c]) (coef := ![s, t, r])
        (Fintype.not_linearIndependent_iff.mp hdep)
        (by intro j; fin_cases j <;> simp [hs, ht, hr])
    obtain ⟨j0, hj0⟩ := hzero
    have hsum2 : s • a + t • b + r • c = coef' 0 • a + coef' 1 • b + coef' 2 • c := by
      simpa [Fin.sum_univ_three] using hsum.symm
    rw [hsum2]
    have hj01 : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 := by fin_cases j0 <;> simp
    rcases hj01 with rfl | rfl | rfl
    · right
      refine ⟨coef' 1, coef' 2, hcoef' 1, hcoef' 2, ?_⟩
      rw [hj0, zero_smul, zero_add]
    · left; right
      refine ⟨coef' 0, coef' 2, hcoef' 0, hcoef' 2, ?_⟩
      rw [hj0, zero_smul, add_zero]
    · left; left
      refine ⟨coef' 0, coef' 1, hcoef' 0, hcoef' 1, ?_⟩
      rw [hj0, zero_smul, add_zero]
  · rintro ((h | h) | h)
    · obtain ⟨s, t, hs, ht, rfl⟩ := h
      exact ⟨s, t, 0, hs, ht, le_refl 0, by rw [zero_smul, add_zero]⟩
    · obtain ⟨s, r, hs, hr, rfl⟩ := h
      exact ⟨s, 0, r, hs, le_refl 0, hr, by rw [zero_smul, add_zero]⟩
    · obtain ⟨t, r, ht, hr, rfl⟩ := h
      exact ⟨0, t, r, le_refl 0, ht, hr, by rw [zero_smul, zero_add]⟩

private theorem isClosed_cone2 (a b : V3) : IsClosed (cone2 a b) := by
  by_cases hli : LinearIndependent ℝ ![a, b]
  · rw [cone2_eq_coneF]; exact isClosed_coneF hli
  · rw [cone2_eq_union_single a b hli]
    exact (isClosed_cone1 a).union (isClosed_cone1 b)

private theorem isClosed_cone3 (a b c : V3) : IsClosed (cone3 a b c) := by
  by_cases hli : LinearIndependent ℝ ![a, b, c]
  · rw [cone3_eq_coneF]; exact isClosed_coneF hli
  · rw [cone3_eq_union_pair a b c hli]
    exact ((isClosed_cone2 a b).union (isClosed_cone2 a c)).union (isClosed_cone2 b c)

private theorem affGe_triple_eq_cone (x v u w : V3)
    (hdis : Disjoint ({x} : Set V3) ({v, u, w} : Set V3)) :
    affGe ({x} : Set V3) ({v, u, w} : Set V3) =
      {y : V3 | (y - x) ∈ cone3 (v - x) (u - x) (w - x)} := by
  rw [AFF_GE_1_3 x v u w hdis]
  ext y; constructor
  · rintro ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum, hy⟩
    exact ⟨t2, t3, t4, ht2, ht3, ht4, by
      rw [hy, show t1 = 1 - t2 - t3 - t4 from by linarith]; module⟩
  · rintro ⟨t2, t3, t4, ht2, ht3, ht4, hy⟩
    refine ⟨1 - t2 - t3 - t4, t2, t3, t4, ht2, ht3, ht4, by ring, ?_⟩
    rw [show y = (y - x) + x from (sub_add_cancel y x).symm, hy]
    module

/-- When `x` is one of the three points, the free coefficient is constrained and
`affGe {x} {v,u,w}` is exactly the convex hull of `{v,u,w}`. -/
private theorem affGe_triple_eq_convexHull_of_mem (x v u w : V3)
    (hx : x ∈ ({v, u, w} : Set V3)) :
    affGe ({x} : Set V3) ({v, u, w} : Set V3) = convexHull ℝ ({v, u, w} : Set V3) := by
  ext y; constructor
  · intro hy
    change Affsign (fun r : ℝ => 0 ≤ r) ({x} : Set V3) ({v, u, w} : Set V3) y at hy
    obtain ⟨f, hfin, hsum, hpos, hone⟩ := hy
    have hmem' : ∀ i : V3, i ∈ hfin.toFinset → i ∈ ({v, u, w} : Set V3) := by
      intro i hi
      have := hfin.mem_toFinset.mp hi
      rcases this with hxi | hti
      · rw [Set.mem_singleton_iff] at hxi; rw [hxi]; exact hx
      · exact hti
    have hcenter : hfin.toFinset.centerMass f id = y := by
      simp only [Finset.centerMass]
      rw [hone, inv_one, one_smul]
      exact hsum.symm
    have hmemc := Finset.centerMass_id_mem_convexHull hfin.toFinset (w := f)
      (fun i hi => hpos i (hmem' i hi)) (by rw [hone]; norm_num)
    exact convexHull_mono (fun i hi => hmem' i hi) (hcenter ▸ hmemc)
  · intro hy
    obtain ⟨ι, _, f, z, hf0, hf1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hy
    let h : ({x} ∪ {v, u, w} : Set V3).Finite :=
      (Set.finite_singleton x).union (((Set.finite_singleton w).insert u).insert v)
    have hmem : ∀ i : ι, z i ∈ ({v, u, w} : Set V3) := hz
    have hzi_mem : ∀ i : ι, z i ∈ h.toFinset := by
      intro i
      rw [h.mem_toFinset]
      exact Or.inr (hmem i)
    refine ⟨fun p => ∑ i, if p = z i then f i else 0, h, ?_, ?_, ?_⟩
    · have h1 : ∑ p ∈ h.toFinset, (∑ i, if p = z i then f i else 0) • p =
          ∑ i, f i • z i := by
        simp_rw [Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        have hinner : (∑ p ∈ h.toFinset, (if p = z i then f i else 0) • p) =
            ∑ p ∈ h.toFinset, (if p = z i then f i • p else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : p = z i <;> simp [hp]
        rw [hinner, Finset.sum_ite_eq' h.toFinset (z i) (fun p => f i • p),
          if_pos (hzi_mem i)]
      rw [h1, hsum]
    · intro p _
      apply Finset.sum_nonneg
      intro i _
      by_cases hp : p = z i
      · rw [if_pos hp]; exact hf0 i
      · rw [if_neg hp]
    · have h2 : ∑ p ∈ h.toFinset, (∑ i, if p = z i then f i else 0) = ∑ i, f i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_ite_eq' h.toFinset (z i) (fun _ => f i), if_pos (hzi_mem i)]
      rw [h2, hf1]

private theorem isClosed_affGe_triple (x v u w : V3) :
    IsClosed (affGe ({x} : Set V3) ({v, u, w} : Set V3)) := by
  by_cases hdis : Disjoint ({x} : Set V3) ({v, u, w} : Set V3)
  · rw [affGe_triple_eq_cone x v u w hdis]
    exact (isClosed_cone3 (v - x) (u - x) (w - x)).preimage
      (continuous_id.sub continuous_const)
  · have hx : x ∈ ({v, u, w} : Set V3) := by
      by_contra h
      exact hdis (Set.disjoint_singleton_left.mpr h)
    rw [affGe_triple_eq_convexHull_of_mem x v u w hx]
    have hfin : ({v, u, w} : Set V3).Finite := by simp
    exact Set.Finite.isClosed_convexHull (𝕜 := ℝ) hfin

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
  have h : (Set.univ : Set V3) \ affGe ({x} : Set V3) ({v, u, w} : Set V3) =
      (affGe ({x} : Set V3) ({v, u, w} : Set V3))ᶜ := by
    rw [Set.sdiff_eq, Set.univ_inter]
  rw [h, isOpen_compl_iff]
  exact isClosed_affGe_triple x v u w

end Kepler.Text
