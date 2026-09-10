/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18o.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18o of block 18, planarity.hl:13121-13631):
- `point_in_aff_gt_2_1_change_point_in_aff_gt_1_2` (13121)
- `pos_in_aff_gt_2_1_fan` (13150)
- `condition_4point_aff_gt_1_2inter_aff_gt_1_2` (13169)
- `exists_dart_leads_into_edge_eq_topological1_component_fan` (13293)
- `JUTSTKG` (13413)
- `AFF_GT_3_1` (13573)
- `AFF_GT_1_3` (13585)
- `AFF_GE_1_3` (13595)
- `notcoplanar_disjoint` (13607)
- `notcoplanar_disjoints` (13623)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42);
  these are repo-specific (`Affsign`-based) objects with no Mathlib
  counterpart, so the `AFF_GT_3_1`/`AFF_GT_1_3`/`AFF_GE_1_3` combination
  characterizations are NOT skipped even though they are "general" affine
  facts (Mathlib has `affineSpan`/`convexHull` but no strict/non-strict
  affine-combination-cone with exactly the HOL interface).
- HOL `cross` has no public V3-level definition; the established idiom is
  the Pi-side `crossProduct` (Mathlib `LinearAlgebra.CrossProduct`), cf.
  Kepler/Text/PlanarityAuto10.lean:37-43. HOL `dot` ↔ `⬝ᵥ`
  (`dotProduct`). HOL `%` ↔ `•`.
- HOL `~collinear {a,b,c}` ↔ `¬ Collinear3 a b c`
  (Kepler/Geom/Azim.lean:43; defeq to `¬ Collinear ℝ ({a,b,c} : Set V3)`).
- HOL `coplanar` ↔ `Coplanar` (Kepler/Geom/Coplanar.lean:23).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `fan80` ↔ `fan80` (Kepler/Text/Fan.lean:227); HOL `sigma_fan` ↔
  `sigmaFan` (Kepler/Text/Fan.lean:67).
- HOL `xfan`/`yfan`/`topological_component_yfan` ↔ `xfan`/`yfan`/
  `topologicalComponentYfan` (Kepler/Text/Fan.lean:154/158/199).
- HOL `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179).
- HOL `let a = e in body` is kept as a Lean `let` binding in the statement
  (cf. Kepler/Text/PlanarityAuto10.lean:765-771), so the theorem type
  mirrors the HOL quantifier/let structure literally.
- `AFF_GT_3_1`/`AFF_GT_1_3`/`AFF_GE_1_3` are general affine-combination
  characterizations but the repo has no existing statement for the
  3-source/1-point and 1-source/3-point shapes (`aff_gt_1_2`
  Kepler/Text/Planarity.lean:165 and `affGt2_2`
  Kepler/Text/Planarity.lean:1496 only cover the 1-2 and 2-2 shapes), so
  they are ported as-is.
-/

import Kepler.Text.PlanarityAuto10

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## aff_gt 的换点与射线成员（planarity.hl:13121-13168） -/

/-- HOL planarity.hl :13121-13149 `point_in_aff_gt_2_1_change_point_in_aff_gt_1_2`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 y:real^3.
 ~collinear {x,v,u}
/\  y IN aff_gt {x} {v,u}
==> u IN aff_gt {x,v} {y}
```

证明思路：`~collinear {x,v,u}` 给出 `x,v,u` 互异；由
`aff_gt_1_2`（HOL `AFF_GT_1_2`）把 `y = t1•x + t2•v + t3•u` 展开
（`t2,t3 > 0`，和 1）。对 `t3 > 0` 取逆，把 `u` 重写为
`x,v,y` 的组合 `u = (-1/t3)•x + (-1/t3)•v + (1/t3)•y`（系数和
`(t1+t2+t3)/t3 = 1`，`y` 系数 `1/t3 > 0`），再用 `affGt_pair_iff`
（HOL `AFF_GT_2_1`）落入 `aff_gt {x,v} {y}`。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82）
- `Affsign`（Kepler/Geom/Aff.lean:32）
- `collinear3_of_eq`（Kepler/Geom/Azim.lean:121） -/
theorem point_in_aff_gt_2_1_change_point_in_aff_gt_1_2 (x v u y : V3)
    (hnc : ¬ Collinear3 x v u)
    (hy : y ∈ affGt ({x} : Set V3) {v, u}) :
    u ∈ affGt ({x, v} : Set V3) {y} := by
  have hxv : x ≠ v := fun he =>
    hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he.symm)
  have hxu : x ≠ u := fun he =>
    hnc (collinear3_pair_left (v0 := x) (v1 := v) (x := u) he.symm)
  have hdis : Disjoint ({x} : Set V3) {v, u} := by
    rw [Set.disjoint_left]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp [hxv, hxu]
  rw [aff_gt_1_2 hdis] at hy
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hyeq⟩ := hy
  have ht3ne : t3 ≠ 0 := ne_of_gt ht3
  have ht1 : t1 = 1 - t2 - t3 := by linarith
  have hyx : y - x = t2 • (v - x) + t3 • (u - x) := by
    rw [hyeq, ht1]
    module
  have hyxne : y ≠ x := by
    intro heq
    have hlin : t2 • (v - x) + t3 • (u - x) = 0 := by
      rw [← hyx, heq, sub_self]
    have hkey : t3 • (u - x) = -(t2 • (v - x)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hlin
    have hu_eq : u - x = (-(t2 / t3)) • (v - x) := by
      calc u - x = t3⁻¹ • (t3 • (u - x)) := (inv_smul_smul₀ ht3ne _).symm
        _ = t3⁻¹ • (-(t2 • (v - x))) := by rw [hkey]
        _ = (-(t2 / t3)) • (v - x) := by module
    exact hnc ((collinear3_iff_smul (w := v) (v := x) (w1 := u)
      (Ne.symm hxv)).mpr ⟨_, hu_eq⟩)
  have hyvne : y ≠ v := by
    intro heq
    have hthis : v - x = t2 • (v - x) + t3 • (u - x) := by rw [← hyx, heq]
    have hrel : (1 - t2) • (v - x) = t3 • (u - x) := by
      have h2 : (v - x) - t2 • (v - x) = t3 • (u - x) := by
        nth_rewrite 1 [hthis]
        abel
      rw [show (1 - t2) • (v - x) = (v - x) - t2 • (v - x) by module]
      exact h2
    have h1mt2 : 1 - t2 ≠ 0 := by
      intro h0
      have hz : t3 • (u - x) = 0 := by rw [← hrel, h0, zero_smul]
      have hux0 : u - x = 0 := by
        rw [← inv_smul_smul₀ ht3ne (u - x), hz, smul_zero]
      exact hxu (sub_eq_zero.mp hux0).symm
    have hu_eq : u - x = ((1 - t2) / t3) • (v - x) := by
      calc u - x = t3⁻¹ • (t3 • (u - x)) := (inv_smul_smul₀ ht3ne _).symm
        _ = t3⁻¹ • ((1 - t2) • (v - x)) := by rw [hrel]
        _ = ((1 - t2) / t3) • (v - x) := by module
    exact hnc ((collinear3_iff_smul (w := v) (v := x) (w1 := u)
      (Ne.symm hxv)).mpr ⟨_, hu_eq⟩)
  refine (affGt_pair_iff (v0 := x) (v1 := v) (x := y) (y := u)
    hxv hyxne hyvne).mpr ?_
  refine ⟨t3⁻¹, inv_pos.mpr ht3, -(t2 / t3), ?_⟩
  have hkey : t3 • (u - x) = (y - x) - t2 • (v - x) := by
    rw [hyx]; abel
  calc u - x = t3⁻¹ • (t3 • (u - x)) := (inv_smul_smul₀ ht3ne _).symm
    _ = t3⁻¹ • ((y - x) - t2 • (v - x)) := by rw [hkey]
    _ = t3⁻¹ • (y - x) + (-(t2 / t3)) • (v - x) := by module

/-- HOL planarity.hl :13150-13168 `pos_in_aff_gt_2_1_fan`

HOL 原文：
```
!x:real^3 v:real^3 u:real^3 a:real.
DISJOINT {x,v} {u}
/\ &0<a /\ a< &1
==>
(&1-a)%v + a % u IN aff_gt {x,v} {u:real^3}
```

证明思路：由 `DISJOINT {x,v} {u}` 得 `x ≠ u`、`v ≠ u`，故三点互异。
把点写成 `(1-a)•v + a•u = 0•x + (1-a)•v + a•u`，系数
`0, 1-a, a` 中 `a > 0`、`1-a > 0`、和为 1，用 `affGt_pair_iff`
（HOL `AFF_GT_2_1`，或展开 `aff_gt_1_2`/`Affsign`）即得成员关系。

候选已有引理：
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82）
- `affGt2_2`（Kepler/Text/Planarity.lean:1496）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `Affsign`（Kepler/Geom/Aff.lean:32） -/
theorem pos_in_aff_gt_2_1_fan (x v u : V3) (a : ℝ)
    (hdis : Disjoint ({x, v} : Set V3) {u})
    (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - a) • v + a • u ∈ affGt ({x, v} : Set V3) {u} := by
  have _ := ha1
  have hxu : x ≠ u := by
    intro he
    exact (Set.disjoint_left.mp hdis)
      (show x ∈ ({x, v} : Set V3) by simp)
      (show x ∈ ({u} : Set V3) by simp [he])
  have hvu : v ≠ u := by
    intro he
    exact (Set.disjoint_left.mp hdis)
      (show v ∈ ({x, v} : Set V3) by simp)
      (show v ∈ ({u} : Set V3) by simp [he])
  rcases eq_or_ne x v with hxv | hxv
  · rw [hxv]
    rw [show ({v, v} : Set V3) = {v} by ext z; simp]
    have hfin : ({v} ∪ {u} : Set V3).Finite :=
      (Set.finite_singleton v).union (Set.finite_singleton u)
    refine ⟨fun z => if z = u then a else 1 - a, hfin, ?_, ?_, ?_⟩
    · rw [sum_insert_single_v hfin hvu]
      rw [if_neg hvu, if_pos rfl]
    · intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      simpa using ha0
    · rw [sum_insert_single_s hfin hvu]
      rw [if_neg hvu, if_pos rfl]
      ring
  · rw [affGt_pair_iff (v0 := x) (v1 := v) (x := u)
      (y := (1 - a) • v + a • u) hxv (Ne.symm hxu) (Ne.symm hvu)]
    exact ⟨a, ha0, 1 - a, by module⟩

/-! ## 四点 aff_gt 交集条件（planarity.hl:13169-13292） -/

/-- 混合积轮换：`(a × b) · c = (b × c) · a`。 -/
private theorem cross_dot_cyclic {a b c : Fin 3 → ℝ} :
    (crossProduct a b) ⬝ᵥ c = (crossProduct b c) ⬝ᵥ a := by
  calc (crossProduct a b) ⬝ᵥ c = c ⬝ᵥ crossProduct a b := dotProduct_comm _ _
    _ = a ⬝ᵥ crossProduct b c := triple_product_permutation c a b
    _ = (crossProduct b c) ⬝ᵥ a := dotProduct_comm _ _

/-- HOL planarity.hl :13169-13292 `condition_4point_aff_gt_1_2inter_aff_gt_1_2`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 v:real^3 u:real^3 w:real^3 a:real.
              let a1 = y - x in
              let a2 = z - x in
              let a3 = v - x in
              let a4 = u - x in
              let a5 = w - x in

 ~collinear {x,v,u}
/\ ~collinear {x,u,w}
/\ ~collinear {x,y,z}
/\  &0< a /\ a< &1 
/\ y IN aff_gt {x} {v,u}
/\ &0<(a3 cross a4) dot a5
/\ (!h. &0< h /\ h< a==> ~collinear {x,v,(&1-h)%u+h%w})
/\ &0<(a3 cross a1) dot a2
 ==> ?t. &0< t /\ t< &1 /\ 
(!h. &0< h /\ h< t==> ~(aff_gt {x} {y,z} INTER aff_gt {x} {v,(&1-h)%u+h%w}={}))
```

证明思路：HOL 把 `a1..a5` 作为差向量，两个正混合积给出
`v, u, w` 与 `v, y, z` 张成的方向锥。证明先由
`aff_gt_1_2_cross_dotr_4point`/`invariant_cross_dotr_esilon_3piont`
和 `invariant_rcross_dot_esilon_3piont` 取到两族阈值 `t, t'`，再用
`point_in_aff_gt_2_1_change_point_in_aff_gt_1_2` 与
`aff_gt_2_1r_rcross_dotl_4point` 把 `y` 挪进 `aff_gt {x,u}{...}`。
取 `t1 = min (min t t') a`，对任意 `h < t1` 令
`va = a1 ⨯ a2`、`vb = a3 ⨯ a4`，见证
`v3 = (vb ⨯ va) + x` 同时落在两个 `aff_gt` 中，最后
`aff_gt_inter_aff_gt`/`condition_cross_dot_4point` 与 `SET_TAC` 收尾。

编码说明：HOL `let a1 = e in ...` 保留为 Lean `let` 绑定；
`cross`/`dot` 按仓库惯例写作 `crossProduct`（Pi 侧）与 `⬝ᵥ`；
`~(A={})` 写作 `A ≠ ∅`。

候选已有引理：
- `point_in_aff_gt_2_1_change_point_in_aff_gt_1_2`（本文件上文，HOL :13121）
- `pos_in_aff_gt_2_1_fan`（本文件上文，HOL :13150）
- `aff_gt_1_2_cross_dotr_4point`（Kepler/Text/PlanarityAuto10.lean:335）
- `invariant_cross_dotr_esilon_3piont`（Kepler/Text/PlanarityAuto10.lean:594）
- `invariant_rcross_dot_esilon_3piont`（Kepler/Text/PlanarityAuto10.lean:676）
- `aff_gt_2_1_cross_dotl_4point`（Kepler/Text/PlanarityAuto10.lean:223）
- `aff_gt_2_1r_rcross_dotl_4point`（Kepler/Text/PlanarityAuto10.lean:247）
- `condition_cross_dot_4point`（Kepler/Text/PlanarityAuto10.lean:94）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860） -/
theorem condition_4point_aff_gt_1_2inter_aff_gt_1_2
    (x y z v u w : V3) (a : ℝ) :
    let a1 : V3 := y - x
    let a2 : V3 := z - x
    let a3 : V3 := v - x
    let a4 : V3 := u - x
    let a5 : V3 := w - x
    ¬ Collinear3 x v u →
    ¬ Collinear3 x u w →
    ¬ Collinear3 x y z →
    0 < a → a < 1 →
    y ∈ affGt ({x} : Set V3) {v, u} →
    0 < (crossProduct ((a3 : V3) : Fin 3 → ℝ) ((a4 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a5 : V3) : Fin 3 → ℝ) →
    (∀ h : ℝ, 0 < h → h < a → ¬ Collinear3 x v ((1 - h) • u + h • w)) →
    0 < (crossProduct ((a3 : V3) : Fin 3 → ℝ) ((a1 : V3) : Fin 3 → ℝ)) ⬝ᵥ
      ((a2 : V3) : Fin 3 → ℝ) →
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ h : ℝ, 0 < h → h < t →
        affGt ({x} : Set V3) {y, z} ∩
          affGt ({x} : Set V3) {v, (1 - h) • u + h • w} ≠ ∅ := by
  dsimp only
  intro hnc_xvu hnc_xuw hnc_xyz ha0 ha1 hy hpos_vuw hnc_line hpos_vyz
  have hpos_yzv : 0 < (crossProduct ((y - x : V3) : Fin 3 → ℝ)
      ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) := by
    rw [← cross_dot_cyclic]
    exact hpos_vyz
  have h1 := aff_gt_1_2_cross_dotr_4point x y z v u hnc_xvu hy hpos_yzv
  have h1' : 0 < (crossProduct ((z - x : V3) : Fin 3 → ℝ)
      ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ) := by
    rw [← cross_anticomm, neg_dotProduct]
    exact h1
  obtain ⟨t, ht0, ht1, ht⟩ := invariant_cross_dotr_esilon_3piont x z y u w h1'
  have hy_vu : u ∈ affGt ({x, v} : Set V3) ({y} : Set V3) :=
    point_in_aff_gt_2_1_change_point_in_aff_gt_1_2 x v u y hnc_xvu hy
  have hnc_xyv : ¬ Collinear3 x y v :=
    properties_of_collinear4_points_fan (v1 := y) hnc_xvu hy
  have hnc_xvy : ¬ Collinear3 x v y := by
    intro h
    apply hnc_xyv
    change Collinear ℝ ({x, y, v} : Set V3)
    rw [show ({x, y, v} : Set V3) = {x, v, y} by
      ext s; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact h
  have hy_vu' : y ∈ affGt ({x, v} : Set V3) ({u} : Set V3) := by
    have h := aff_gt_inter_aff_gt (x := x) (v := v) (w := u) hnc_xvu
    rw [h] at hy
    exact hy.1
  have hE := aff_gt_2_1r_rcross_dotl_4point x y z v u hnc_xvy hy_vu hpos_yzv
  obtain ⟨t', ht'0, ht'1, ht'⟩ := invariant_rcross_dot_esilon_3piont x u z v w hE
  have hxw : x ≠ w := fun he =>
    hnc_xuw (collinear3_pair_left (v0 := x) (v1 := u) (x := w) he.symm)
  have huw : u ≠ w := fun he =>
    hnc_xuw (collinear3_pair_right (v0 := x) (v1 := u) (x := w) he.symm)
  have hdis_xuw : Disjoint ({x, u} : Set V3) ({w} : Set V3) := by
    rw [Set.disjoint_left]
    intro s hs hsw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rw [Set.mem_singleton_iff] at hsw
    rcases hs with rfl | rfl
    · exact hxw hsw
    · exact huw hsw
  refine ⟨min (min t t') a, ?_, ?_, ?_⟩
  · exact lt_min (lt_min ht0 ht'0) ha0
  · exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) ht1
  · intro h hh0 hhh
    have hh_lt_a : h < a := lt_of_lt_of_le hhh (min_le_right _ _)
    have hh_lt_t : h < t :=
      lt_of_lt_of_le hhh (le_trans (min_le_left _ _) (min_le_left _ _))
    have hh_lt_t' : h < t' :=
      lt_of_lt_of_le hhh (le_trans (min_le_left _ _) (min_le_right _ _))
    have hh_lt1 : h < 1 := lt_trans hh_lt_a ha1
    set p : V3 := (1 - h) • u + h • w with hp
    have hC : 0 < (crossProduct ((z - x : V3) : Fin 3 → ℝ)
        ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((p - x : V3) : Fin 3 → ℝ) :=
      ht h hh0 hh_lt_t
    have hA : 0 < (crossProduct ((p - x : V3) : Fin 3 → ℝ)
        ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) :=
      ht' h hh0 hh_lt_t'
    have hA' : 0 < (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((p - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ) := by
      rw [cross_dot_cyclic]
      exact hA
    have hD : 0 < -((crossProduct ((z - x : V3) : Fin 3 → ℝ)
        ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) := by
      rw [← cross_anticomm, neg_dotProduct, neg_neg]
      exact hpos_yzv
    have hp_mem : p ∈ affGt ({x, u} : Set V3) ({w} : Set V3) :=
      pos_in_aff_gt_2_1_fan x u w h hdis_xuw hh0 hh_lt1
    have hp_vuw : 0 < (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((p - x : V3) : Fin 3 → ℝ) :=
      aff_gt_2_1_cross_dotl_4point x v u w p hnc_xuw hp_mem hpos_vuw
    have hp_vuw' : 0 < (crossProduct ((u - x : V3) : Fin 3 → ℝ)
        ((p - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) := by
      rw [← cross_dot_cyclic]
      exact hp_vuw
    have hB' : 0 < -((crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((p - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) := by
      have hB := aff_gt_2_1r_rcross_dotl_4point x u p v y hnc_xvu hy_vu' hp_vuw'
      rw [cross_dot_cyclic] at hB
      rw [← cross_anticomm, neg_dotProduct] at hB
      exact hB
    have hmem1 : (WithLp.toLp 2 (crossProduct
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ))
        (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ))) + x)
        ∈ affGt ({x} : Set V3) ({y, z} : Set V3) :=
      condition_cross_dot_4point x v p y z hnc_xyz hA' hB'
    have hmem2 : (WithLp.toLp 2 (crossProduct
        (crossProduct ((z - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ))
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ))) + x)
        ∈ affGt ({x} : Set V3) ({v, p} : Set V3) :=
      condition_cross_dot_4point x z y v p (hnc_line h hh0 hh_lt_a) hC hD
    have hcross_eq : crossProduct
        (crossProduct ((z - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ))
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ)) =
        crossProduct
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ))
        (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ)) := by
      have hzy : crossProduct ((z - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ) =
          -crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ) :=
        (cross_anticomm _ _).symm
      rw [hzy, map_neg, LinearMap.neg_apply, cross_anticomm]
    have hEq : (WithLp.toLp 2 (crossProduct
        (crossProduct ((z - x : V3) : Fin 3 → ℝ) ((y - x : V3) : Fin 3 → ℝ))
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ))) + x) =
        (WithLp.toLp 2 (crossProduct
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ))
        (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ))) + x) := by
      rw [hcross_eq]
    have hmem2' : (WithLp.toLp 2 (crossProduct
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((p - x : V3) : Fin 3 → ℝ))
        (crossProduct ((y - x : V3) : Fin 3 → ℝ) ((z - x : V3) : Fin 3 → ℝ))) + x)
        ∈ affGt ({x} : Set V3) ({v, p} : Set V3) := by
      rw [← hEq]
      exact hmem2
    rw [← Set.nonempty_iff_ne_empty]
    exact ⟨_, hmem1, hmem2'⟩

/-! ## dart_leads_into 恰为分量（planarity.hl:13293-13572） -/

/-- 交换 `Collinear3` 的第二、三点（本文件私有版本）。 -/
private theorem collinear3_swap_auto11 {x v u : V3} (h : Collinear3 x v u) :
    Collinear3 x u v := by
  unfold Collinear3 at h ⊢
  rw [show ({x, u, v} : Set V3) = {x, v, u} by
    ext a; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  exact h

/-- 三点不共线时 `affGt {x} {v,w}` 是凸集（`convex_affGt_single_pair` 的
本文件私有版本，经 `aff_gt_1_2` 展开）。 -/
private theorem convex_affGt_single_pair_auto11 {x v w : V3}
    (hnc : ¬ Collinear3 x v w) :
    Convex ℝ (affGt ({x} : Set V3) {v, w}) := by
  have hdis : Disjoint ({x} : Set V3) {v, w} := by
    rw [Set.disjoint_left]
    intro a ha haw
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at haw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at haw
    rcases haw with h | h
    · exact hnc (by rw [h]; exact collinear3_of_eq rfl)
    · exact hnc (by rw [h]; exact collinear3_pair_left rfl)
  rw [aff_gt_1_2 hdis, convex_iff_forall_pos]
  intro y hy z hz a b ha hb hab
  obtain ⟨t1, t2, t3, ht2, ht3, hsum, hyeq⟩ := hy
  obtain ⟨s1, s2, s3, hs2, hs3, hssum, hzeq⟩ := hz
  refine ⟨a * t1 + b * s1, a * t2 + b * s2, a * t3 + b * s3,
    add_pos (mul_pos ha ht2) (mul_pos hb hs2),
    add_pos (mul_pos ha ht3) (mul_pos hb hs3), ?_, ?_⟩
  · nlinarith [hsum, hssum, hab]
  · rw [hyeq, hzeq]; module

/-- HOL planarity.hl :13293-13412 `exists_dart_leads_into_edge_eq_topological1_component_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 v:real^3 u:real^3 w:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ {v,u} IN E /\ {u,w} IN E 
/\ sigma_fan x V E u w = v
/\ y IN aff_gt {x} {v,u} 
/\ y IN xfan(x,V,E)
/\ ~(y=x)
/\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan(x,V,E))
/\ &0<((v-x) cross (y-x)) dot (z-x)

==> dart_leads_into x V E v u = U
```

证明思路：由 `connected_component_of_faces_fan` 与 `fan80` 的展开得
`{u,w}` 的后继关系；`fan_run_in_small_is_subset_yfan` 给
`rw_dart_fan (u,w)` 小半径落入 `yfan`。取
`h1 = min h (min h' (acs h''))/2` 后用
`exists_rw_dart_inter_aff_gt1_fan` 与
`condition_4point_aff_gt_1_2inter_aff_gt_1_2` 造出同时落在
`dart_leads_into (u,w)` 与 `aff_gt {x}{v, ...}` 的点，再经
`expand_element_in_topological_component_yfan` /
`zpoint_in_yfan` 与连通分量相等（`CONNECTED_COMPONENT_EQ_EQ`）得
`dart_leads_into x V E v u = U`。

编码说明：HOL `&0<((v-x) cross (y-x)) dot (z-x)` 按仓库惯例写作
`0 < (crossProduct ((v-x):Fin 3→ℝ) ((y-x):Fin 3→ℝ)) ⬝ᵥ ((z-x):Fin 3→ℝ)`；
`sigma_fan` 为 `sigmaFan`，`aff_gt` 为 `affGt`，`xfan`/`yfan` 为
`xfan`/`yfan`，`dart_leads_into` 为 `dartLeadsInto`。

候选已有引理：
- `connected_component_of_faces_fan`（Kepler/Text/PlanarityComponent.lean:134）
- `fan_run_in_small_is_subset_yfan`（Kepler/Text/Planarity.lean:2588）
- `not_empty_rw_dart_fan`（Kepler/Text/TopologyFan.lean:4125）
- `dartLeadsInto_spec`（Kepler/Text/TopologyFan.lean:4233）
- `rw_dart_avoids_fan`（Kepler/Text/TopologyFan.lean:3303）
- `exists_rw_dart_inter_aff_gt1_fan`（Kepler/Text/PlanarityAngle.lean:2182）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `condition_4point_aff_gt_1_2inter_aff_gt_1_2`（本文件上文，HOL :13169）
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `aff_gt_subset_component_y_fan`（Kepler/Text/PlanarityAuto7.lean:454）
- `point_in_yfan_and_point_in_xfan_indepent_fan`（Kepler/Text/PlanarityAuto8.lean:195）
- `exists_open_not_collinear`（Kepler/Text/Planarity.lean:125）
- `expand_element_in_topological_component_yfan`（Kepler/Text/PlanarityAuto7.lean:271）
- `zpoint_in_yfan`（Kepler/Text/PlanarityAuto7.lean:83） -/
theorem exists_dart_leads_into_edge_eq_topological1_component_fan
    (x : V3) (V : Set V3) (E : Set (Set V3)) (U : Set V3)
    (y z v u w : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hygt : y ∈ affGt ({x} : Set V3) {v, u})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E)
    (hpos : 0 < (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ)) :
    dartLeadsInto x V E v u = U := by
  have hθ := hfan80 u w huw
  rw [hsigma] at hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ0 hθπ
  obtain ⟨hncuw, hncvu, _hncvw⟩ := notcoplanar_imp_notcollinear_fan hcop
  have hnc_xuv : ¬ Collinear3 x u v := fun hc => hncvu (collinear3_swap_auto11 hc)
  have hnc_xyz : ¬ Collinear3 x y z :=
    point_in_yfan_and_point_in_xfan_indepent_fan x V E U y z
      hfan hcard hfan80 hU hz hyxfan hyx hconn
  have hne : E ≠ ∅ := nonsetedge_fully_surround_fan hcard hfan
  have hxz : x ≠ z := point_in_yfan_not_x_fan x V E U z hfan hne hU hz
  have hdis : Disjoint ({x} : Set V3) {y, z} := by
    rw [Set.disjoint_left]
    intro a ha haz
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at haz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at haz
    rcases haz with h | h
    · exact hyx h.symm
    · exact hxz h
  have hsub_yz : affGt ({x} : Set V3) {y, z} ⊆ U :=
    aff_gt_subset_component_y_fan x V E U y z
      hfan hcard hfan80 hU hz hdis hconn
  -- 混合积 `(v-x) × (u-x) · (w-x) > 0`
  have hpos_vuw : 0 < (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) := by
    have htmp : 0 < (crossProduct ((u - x : V3) : Fin 3 → ℝ)
        ((w - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) :=
      cross_dot_fully_surrounded_fan (v1 := u) (v := w) (u1 := v)
        hnc_xuv hncuw hθ0 hθπ
    calc 0 < (crossProduct ((u - x : V3) : Fin 3 → ℝ)
          ((w - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) := htmp
      _ = (crossProduct ((w - x : V3) : Fin 3 → ℝ)
          ((v - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ) :=
        cross_dot_cyclic
      _ = (crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((u - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) :=
        cross_dot_cyclic
  -- 小参数使 `x, v, (1-h)u + h w` 不共线
  obtain ⟨t1, ht10, ht11, hnc_line⟩ := exists_open_not_collinear hfan hvu huw
  have hnc_line' : ∀ h : ℝ, 0 < h → h < t1 / 2 →
      ¬ Collinear3 x v ((1 - h) • u + h • w) := by
    intro h hh0 hh
    exact hnc_line h (le_of_lt hh0)
      (le_of_lt (lt_of_lt_of_le hh (by linarith)))
  obtain ⟨T, hT0, hT1, hcond⟩ :=
    condition_4point_aff_gt_1_2inter_aff_gt_1_2 x y z v u w (t1 / 2)
      hncvu hncuw hnc_xyz (half_pos ht10) (by linarith) hygt
      hpos_vuw hnc_line' hpos
  -- dart (u,w) 的刻画阈值
  obtain ⟨h_dart, hh_dart_pos, hspec⟩ :=
    dartLeadsInto_spec (x := x) (V := V) (E := E) (v := u) (u := w) hfan huw
  set s : ℝ := min h_dart (Real.pi / 2) / 2 with hsdef
  have hminpos : 0 < min h_dart (Real.pi / 2) :=
    lt_min hh_dart_pos (by positivity)
  have hs0 : 0 < s := by rw [hsdef]; exact div_pos hminpos two_pos
  have hslt_dart : s < h_dart := by
    rw [hsdef]
    exact lt_of_lt_of_le (half_lt_self hminpos) (min_le_left _ _)
  have hslt_pi2 : s < Real.pi / 2 := by
    rw [hsdef]
    exact lt_of_lt_of_le (half_lt_self hminpos) (min_le_right _ _)
  -- rwDartFan 与扰动扇区的交、扰动扇区含于 yfan
  obtain ⟨H1, hH10, hH1⟩ :=
    exists_rw_dart_inter_aff_gt1_fan (x := x) (v := v) (u := u) (w := w)
      hfan hvu huw hsigma hs0 hslt_pi2 hfan80 hcard
  obtain ⟨H3, hH30, _hH3le, hH3⟩ :=
    fan_run_in_small_is_subset_yfan hfan hvu huw hθ0 hθπ hsigma
  set t2 : ℝ := min (min H1 H3) (min T (t1 / 2)) / 2 with ht2def
  have hmin2pos : 0 < min (min H1 H3) (min T (t1 / 2)) :=
    lt_min (lt_min hH10 hH30) (lt_min hT0 (half_pos ht10))
  have ht20 : 0 < t2 := by rw [ht2def]; exact div_pos hmin2pos two_pos
  have ht2_lt_H1 : t2 < H1 := by
    rw [ht2def]
    exact lt_of_lt_of_le (half_lt_self hmin2pos)
      (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2_lt_H3 : t2 < H3 := by
    rw [ht2def]
    exact lt_of_lt_of_le (half_lt_self hmin2pos)
      (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht2_lt_T : t2 < T := by
    rw [ht2def]
    exact lt_of_lt_of_le (half_lt_self hmin2pos)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht2_lt_t1half : t2 < t1 / 2 := by
    rw [ht2def]
    exact lt_of_lt_of_le (half_lt_self hmin2pos)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  set p : V3 := (1 - t2) • u + t2 • w with hp
  have hnc_xvp : ¬ Collinear3 x v p := by
    rw [hp]
    exact hnc_line' t2 ht20 ht2_lt_t1half
  -- 两个交点 y1, y2
  have hne1 : (rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos s) ∩
      affGt ({x} : Set V3) {v, p}) ≠ ∅ := by
    rw [hp]
    exact hH1 t2 ht20 ht2_lt_H1
  obtain ⟨y1, hy1rw, hy1aff⟩ := Set.nonempty_iff_ne_empty.mpr hne1
  have hne2 : (affGt ({x} : Set V3) {y, z} ∩
      affGt ({x} : Set V3) {v, p}) ≠ ∅ := by
    rw [hp]
    exact hcond t2 ht20 ht2_lt_T
  obtain ⟨y2, hy2yz, hy2aff⟩ := Set.nonempty_iff_ne_empty.mpr hne2
  have hy2U : y2 ∈ U := hsub_yz hy2yz
  -- 扰动扇区凸、含于 yfan，故 y1、y2 同属一个分量
  have hpre : IsPreconnected (affGt ({x} : Set V3) {v, p}) :=
    (convex_affGt_single_pair_auto11 hnc_xvp).isPreconnected
  have hyfan_p : affGt ({x} : Set V3) {v, p} ⊆ yfan x V E := by
    rw [hp]
    exact hH3 t2 ht20 ht2_lt_H3
  have hy2_cc_y1 : y2 ∈ connectedComponentIn (yfan x V E) y1 :=
    hpre.subset_connectedComponentIn hy1aff hyfan_p hy2aff
  have hcc12 : connectedComponentIn (yfan x V E) y1 =
      connectedComponentIn (yfan x V E) y2 :=
    connectedComponentIn_eq hy2_cc_y1
  obtain ⟨-, hy1_dart⟩ := hspec s y1 hs0 hslt_dart hy1rw
  have hUeq : U = connectedComponentIn (yfan x V E) z :=
    expand_element_in_topological_component_yfan x V E U z hfan hU hz
  have hy2_ccz : y2 ∈ connectedComponentIn (yfan x V E) z := hUeq ▸ hy2U
  have hccz2 : connectedComponentIn (yfan x V E) z =
      connectedComponentIn (yfan x V E) y2 :=
    connectedComponentIn_eq hy2_ccz
  have hdart_U : dartLeadsInto x V E u w = U := by
    rw [← hy1_dart, hcc12, ← hccz2, hUeq]
  have hfaces : dartLeadsInto x V E v u = dartLeadsInto x V E u w :=
    connected_component_of_faces_fan hfan hvu huw hsigma hcard hfan80
  rw [hfaces, hdart_U]

/-- HOL planarity.hl :13413-13572 `JUTSTKG`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
==> ?v u. {v,u} IN E /\ dart_leads_into x V E v u = U
```

证明思路：由 `exists_point_in_component_yfan` 取 `z ∈ U`，
`connect_insidepoint_to_bound_yfan` 取边界点 `y` 与边 `{v,w}`（用
`expand_edge_graph_fan` 展开 `xfan`）。按
`((v-x) cross (y-x)) dot (z-x)` 的符号（正/负/零）分三情形：正、负
两支用 `INVERSE1_SIGMA_FAN` 与
`exists_dart_leads_into_edge_eq_topological1_component_fan` 直接得结论；
零支用 `aff_gt_1_2_cross_dotr_4point_zero` 与 `not_azim_points1_in_yfan`
把 `y` 化为与 `v` 共线、再用 `sum5_azim_fan` 与
`cross_dot_fully_surrounded_fan` 推出矛盾/结论。

编码说明：HOL `&0 < ((v-x) cross (y-x)) dot (z-x) \/ &0< --(...) \/ ...=0`
在证明中按实数的三分解处理；陈述本身只涉及 `FAN`/`fan80`/分量与
`dartLeadsInto`，无需 cross/dot 记号。

候选已有引理：
- `exists_point_in_component_yfan`（Kepler/Text/PlanarityConnect.lean）
- `connect_insidepoint_to_bound_yfan`（Kepler/Text/PlanarityAuto6.lean）
- `expand_edge_graph_fan`（Kepler/Text/PlanarityAuto6.lean）
- `exists_dart_leads_into_edge_eq_topological1_component_fan`（本文件上文，HOL :13293）
- `exists_dart_leads_into_edge_eq_topological_component_fan`（Kepler/Text/PlanarityAuto9.lean:889）
- `aff_gt_1_2_cross_dotr_4point_zero`（Kepler/Text/PlanarityAuto10.lean:489）
- `not_azim_points1_in_yfan`（Kepler/Text/PlanarityAuto9.lean:977）
- `sum5_azim_fan`（Kepler/Text/Fan.lean）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `inverse1SigmaFan`（Kepler/Text/Fan.lean:240） -/
theorem JUTSTKG (x : V3) (V : Set V3) (E : Set (Set V3)) (U : Set V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) :
    ∃ v u : V3, {v, u} ∈ E ∧ dartLeadsInto x V E v u = U := by
  obtain ⟨z, hz⟩ := exists_point_in_component_yfan hU
  obtain ⟨y, hyx, hy_xfan_mem, hconn⟩ :=
    connect_insidepoint_to_bound_yfan x V E U z hfan hcard hfan80 hU hz
  have hy_xfan : y ∈ xfan x V E := hy_xfan_mem
  rw [xfan, Set.mem_setOf_eq] at hy_xfan_mem
  obtain ⟨e, he, hye⟩ := hy_xfan_mem
  obtain ⟨v, w, rfl⟩ := expand_edge_graph_fan hfan he
  have hnc_vw : ¬ Collinear3 x v w := fan_not_collinear hfan he
  have hmem := fan_mem_of_edge hfan he
  have hvV : v ∈ V := hmem.1
  have hwV : w ∈ V := hmem.2
  have hpair : ({w, v} : Set V3) = {v, w} := by
    ext a; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have he_wv : {w, v} ∈ E := by rwa [hpair]
  rw [aff_ge_eq_aff_gt_union_aff_ge hnc_vw] at hye
  rcases hye with (hygt | hyv) | hyw
  · have hygt_wv : y ∈ affGt ({x} : Set V3) {w, v} := by rwa [hpair]
    rcases lt_trichotomy ((crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ)) 0
      with hneg | hzero | hpos
    · have hneg_yzv : 0 < -((crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) := by
        have hcyc : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
            ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) =
            (crossProduct ((v - x : V3) : Fin 3 → ℝ)
              ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ) := by
          rw [cross_dot_cyclic, cross_dot_cyclic]
        rw [hcyc]
        linarith
      have hyzw : 0 < (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) :=
        aff_gt_1_2_cross_dotr_4point_neg x y z v w hnc_vw hygt hneg_yzv
      have hpos_wyz : 0 < (crossProduct ((w - x : V3) : Fin 3 → ℝ)
          ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ) := by
        calc 0 < (crossProduct ((y - x : V3) : Fin 3 → ℝ)
              ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) := hyzw
          _ = (crossProduct ((z - x : V3) : Fin 3 → ℝ)
                ((w - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) :=
              cross_dot_cyclic
          _ = (crossProduct ((w - x : V3) : Fin 3 → ℝ)
                ((y - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((z - x : V3) : Fin 3 → ℝ) :=
              cross_dot_cyclic
      have hinv := INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := v) hfan
      obtain ⟨hinv_edge, hinv_sigma, -⟩ := hinv
      have hedge : {v, inverse1SigmaFan x V E v w} ∈ E := hinv_edge w he
      have hsig : sigmaFan x V E v (inverse1SigmaFan x V E v w) = w :=
        hinv_sigma w he
      have hdart :=
        exists_dart_leads_into_edge_eq_topological1_component_fan x V E U y z w v
          (inverse1SigmaFan x V E v w) hfan hcard hfan80 hU hz he_wv hedge hsig
          hygt_wv hy_xfan hyx hconn hpos_wyz
      exact ⟨w, v, he_wv, hdart⟩
    · exfalso
      have hzero_yzv : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) = 0 := by
        rw [cross_dot_cyclic, cross_dot_cyclic]
        exact hzero
      have hzero_yzw : (crossProduct ((y - x : V3) : Fin 3 → ℝ)
          ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) = 0 :=
        aff_gt_1_2_cross_dotr_4point_zero x y z v w hnc_vw hygt hzero_yzv
      have hazimw : azim x y z w ≠ 0 :=
        not_azim_points1_in_yfan x V E U y z v w hfan hcard hfan80 hU hz
          he hygt hy_xfan hyx hconn
      have hazimv : azim x y z v ≠ 0 :=
        not_azim_points1_in_yfan x V E U y z w v hfan hcard hfan80 hU hz
          he_wv hygt_wv hy_xfan hyx hconn
      have hnc_xyz : ¬ Collinear3 x y z :=
        point_in_yfan_and_point_in_xfan_indepent_fan x V E U y z
          hfan hcard hfan80 hU hz hy_xfan hyx hconn
      have hnc_xyv : ¬ Collinear3 x y v :=
        properties_of_collinear4_points_fan (x := x) (v := v) (u := w) (v1 := y)
          hnc_vw hygt
      have hnc_xyw : ¬ Collinear3 x y w :=
        properties_of_collinear4_points_fan (x := x) (v := w) (u := v) (v1 := y)
          (fun h => hnc_vw (collinear3_swap_auto11 h)) hygt_wv
      have hazimv_pos : 0 < azim x y z v :=
        lt_of_le_of_ne (azim_nonneg x y z v) (Ne.symm hazimv)
      rcases lt_or_ge (azim x y z v) Real.pi with hlt_pi | hge_pi
      · have hcontr : 0 < (crossProduct ((y - x : V3) : Fin 3 → ℝ)
            ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) :=
          cross_dot_fully_surrounded_fan (x := x) (v1 := y) (u1 := v) (v := z)
            hnc_xyv hnc_xyz hazimv_pos hlt_pi
        rw [hzero_yzv] at hcontr
        exact (lt_irrefl (0 : ℝ)) hcontr
      · have hdis_x_wv : Disjoint ({x} : Set V3) {w, v} := by
          rw [Set.disjoint_singleton_left]
          intro hmem'
          rcases Set.mem_insert_iff.mp hmem' with h | h
          · exact hnc_vw (collinear3_swap_auto11
              (collinear3_of_eq (v := x) (w := w) (w1 := v) h.symm))
          · exact hnc_vw (collinear3_of_eq (v := x) (w := v) (w1 := w) h.symm)
        have hazim_pi : azim x y w v = Real.pi :=
          aff_gt2_subset_aff_ge (x := x) (v := w) (u := v) (v1 := y)
            hdis_x_wv hnc_xyv hnc_xyw hygt_wv
        have hle : azim x y w v ≤ azim x y z v := by rw [hazim_pi]; exact hge_pi
        have hsum : azim x y z v = azim x y z w + azim x y w v :=
          sum5_azim_fan (x := x) (v := y) (u := z) (w1 := w) (w2 := v)
            hyx hnc_xyz hnc_xyw hnc_xyv hle
        have hazimw_pos : 0 < azim x y z w :=
          lt_of_le_of_ne (azim_nonneg x y z w) (Ne.symm hazimw)
        have hazimw_lt_pi : azim x y z w < Real.pi := by
          have h2pi : azim x y z v < 2 * Real.pi := azim_lt_two_pi x y z v
          linarith
        have hcontr : 0 < (crossProduct ((y - x : V3) : Fin 3 → ℝ)
            ((z - x : V3) : Fin 3 → ℝ)) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) :=
          cross_dot_fully_surrounded_fan (x := x) (v1 := y) (u1 := w) (v := z)
            hnc_xyw hnc_xyz hazimw_pos hazimw_lt_pi
        rw [hzero_yzw] at hcontr
        exact (lt_irrefl (0 : ℝ)) hcontr
    · have hinv := INVERSE1_SIGMA_FAN (x := x) (V := V) (E := E) (v := w) hfan
      obtain ⟨hinv_edge, hinv_sigma, -⟩ := hinv
      have hedge : {w, inverse1SigmaFan x V E w v} ∈ E := hinv_edge v he_wv
      have hsig : sigmaFan x V E w (inverse1SigmaFan x V E w v) = v :=
        hinv_sigma v he_wv
      have hdart :=
        exists_dart_leads_into_edge_eq_topological1_component_fan x V E U y z v w
          (inverse1SigmaFan x V E w v) hfan hcard hfan80 hU hz he hedge hsig
          hygt hy_xfan hyx hconn hpos
      exact ⟨v, w, he, hdart⟩
  · obtain ⟨w', hw'E, hdart⟩ :=
      exists_dart_leads_into_edge_eq_topological_component_fan x V E U y z v
        hfan hcard hfan80 hU hz hvV hyv hy_xfan hyx hconn
    exact ⟨v, w', hw'E, hdart⟩
  · obtain ⟨w', hw'E, hdart⟩ :=
      exists_dart_leads_into_edge_eq_topological_component_fan x V E U y z w
        hfan hcard hfan80 hU hz hwV hyw hy_xfan hyx hconn
    exact ⟨w, w', hw'E, hdart⟩

/-! ## aff_gt/aff_ge 的三点组合刻画（planarity.hl:13573-13606） -/

/-- `({x,v,u} ∪ {w}).toFinset` 就是去重后的四点 `Finset`。 -/
private theorem toFinset_triple_union_single {x v u w : V3}
    (h : ({x, v, u} ∪ {w} : Set V3).Finite) :
    h.toFinset = ({x, v, u, w} : Finset V3) := by
  apply Finset.ext
  intro z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- 指示函数标量和：`∑ z∈{x,v,u,w} (∑ᵢ tᵢ[z=pᵢ]) = t1+t2+t3+t4`。 -/
private theorem finset_sum_indicators_s (t1 t2 t3 t4 : ℝ) (x v u w : V3) :
    (∑ z ∈ ({x, v, u, w} : Finset V3),
      ((if z = x then t1 else 0) + (if z = v then t2 else 0) +
        (if z = u then t3 else 0) + (if z = w then t4 else 0)))
      = t1 + t2 + t3 + t4 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- 指示函数向量和：`∑ z∈{x,v,u,w} (∑ᵢ tᵢ[z=pᵢ]) • z = ∑ᵢ tᵢ • pᵢ`。 -/
private theorem finset_sum_indicators_v (t1 t2 t3 t4 : ℝ) (x v u w : V3) :
    (∑ z ∈ ({x, v, u, w} : Finset V3),
      (((if z = x then t1 else 0) + (if z = v then t2 else 0) +
        (if z = u then t3 else 0) + (if z = w then t4 else 0)) • z))
      = t1 • x + t2 • v + t3 • u + t4 • w := by
  have h : ∀ z : V3,
      (((if z = x then t1 else 0) + (if z = v then t2 else 0) +
        (if z = u then t3 else 0) + (if z = w then t4 else 0)) • z)
      = ((if z = x then t1 • z else 0) + (if z = v then t2 • z else 0) +
         (if z = u then t3 • z else 0) + (if z = w then t4 • z else 0)) := by
    intro z
    rw [add_smul, add_smul, add_smul]
    by_cases hx : z = x <;> by_cases hv : z = v <;> by_cases hu : z = u <;>
      by_cases hw : z = w <;> simp [hx, hv, hu, hw]
  rw [Finset.sum_congr rfl (fun z _ => h z)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- 三点去重标量和：把重合点系数归并到首次出现处。 -/
private theorem sum_triple_first_s (f : V3 → ℝ) (x v u : V3) :
    (∑ z ∈ ({x, v, u} : Finset V3), f z)
      = f x + (if v = x then 0 else f v)
          + (if u = x then 0 else if u = v then 0 else f u) := by
  by_cases hxv : v = x
  · rw [hxv]
    by_cases hux : u = x
    · rw [hux]
      simp
    · rw [show ({x, x, u} : Finset V3) = ({x, u} : Finset V3) by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
      rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hux h.symm),
        Finset.sum_singleton]
      simp [hux]
  · by_cases hxu : u = x
    · rw [hxu]
      rw [show ({x, v, x} : Finset V3) = ({x, v} : Finset V3) by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
      rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hxv h.symm),
        Finset.sum_singleton]
      simp [hxv]
    · by_cases hvu : u = v
      · rw [hvu]
        rw [show ({x, v, v} : Finset V3) = ({x, v} : Finset V3) by
            ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hxv h.symm),
          Finset.sum_singleton]
        simp [hxv]
      · rw [Finset.sum_insert (by
            rw [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hxv h.symm, fun h => hxu h.symm⟩)]
        rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hvu h.symm),
          Finset.sum_singleton]
        simp only [if_neg hxv, if_neg hxu, if_neg hvu]
        ring

/-- 三点去重向量和：把重合点系数归并到首次出现处。 -/
private theorem sum_triple_first_v (f : V3 → ℝ) (x v u : V3) :
    (∑ z ∈ ({x, v, u} : Finset V3), f z • z)
      = f x • x + (if v = x then 0 else f v) • v
          + (if u = x then 0 else if u = v then 0 else f u) • u := by
  by_cases hxv : v = x
  · rw [hxv]
    by_cases hux : u = x
    · rw [hux]
      simp
    · rw [show ({x, x, u} : Finset V3) = ({x, u} : Finset V3) by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
      rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hux h.symm),
        Finset.sum_singleton]
      simp [hux]
  · by_cases hxu : u = x
    · rw [hxu]
      rw [show ({x, v, x} : Finset V3) = ({x, v} : Finset V3) by
          ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
      rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hxv h.symm),
        Finset.sum_singleton]
      simp [hxv]
    · by_cases hvu : u = v
      · rw [hvu]
        rw [show ({x, v, v} : Finset V3) = ({x, v} : Finset V3) by
            ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hxv h.symm),
          Finset.sum_singleton]
        simp [hxv]
      · rw [Finset.sum_insert (by
            rw [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨fun h => hxv h.symm, fun h => hxu h.symm⟩)]
        rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hvu h.symm),
          Finset.sum_singleton]
        simp only [if_neg hxv, if_neg hxu, if_neg hvu]
        abel

/-- HOL planarity.hl :13573-13584 `AFF_GT_3_1`

HOL 原文：
```
!x v u w.
        DISJOINT {x,v,u} {w}
        ==> aff_gt {x,v,u} {w} =
             {y | ?t1 t2 t3 t4.
                     &0 < t4 /\
                     t1 + t2 +t3 +t4 = &1 /\
                     y = t1 % x + t2 % v + t3 % u +t4 % w }
```

证明思路：纯仿射组合事实（HOL 由 `AFF_TAC` 自动完成）。展开
`affGt`/`Affsign`：`w` 侧系数严格正，`{x,v,u}` 侧系数任意；由
`DISJOINT` 得四点互异，有限和按 `{x,v,u,w}` 去重后直接提取
`t1,t2,t3,t4`。反向由任意系数构造 `Affsign` 见证。

编码说明：`aff_gt` 为 `affGt`，`DISJOINT` 为 `Disjoint`，`%` 为 `•`。
该结论是通用仿射组合刻画，但 `affGt` 是仓库特有对象（Mathlib 只有
`affineSpan`/`convexHull`），且无 3-1 形状的现成引理，故不跳过。

候选已有引理：
- `affGt`（Kepler/Geom/Aff.lean:39）
- `Affsign`（Kepler/Geom/Aff.lean:32）
- `affGt2_2`（Kepler/Text/Planarity.lean:1496，2-2 形状）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165，1-2 形状）
- `affGt_pair_iff`（Kepler/Geom/Aff.lean:82，2-1 形状） -/
theorem AFF_GT_3_1 (x v u w : V3)
    (hdis : Disjoint ({x, v, u} : Set V3) {w}) :
    affGt ({x, v, u} : Set V3) {w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 < t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • v + t3 • u + t4 • w} := by
  have hw_notin : w ∉ ({x, v, u} : Set V3) :=
    (Set.disjoint_right.mp hdis) (Set.mem_singleton w)
  have hwx : w ≠ x := fun h => hw_notin (by rw [h]; simp)
  have hwv : w ≠ v := fun h => hw_notin (by rw [h]; simp)
  have hwu : w ≠ u := fun h => hw_notin (by rw [h]; simp)
  have hfin : ({x, v, u} ∪ {w} : Set V3).Finite :=
    (((Set.finite_singleton u).insert v).insert x).union (Set.finite_singleton w)
  have hTeq := toFinset_triple_union_single hfin
  have hsplit : ({x, v, u, w} : Finset V3) = insert w ({x, v, u} : Finset V3) := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hwmem : w ∉ ({x, v, u} : Finset V3) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or]
    exact ⟨hwx, hwv, hwu⟩
  ext y
  simp only [affGt, Set.mem_setOf_eq, Affsign]
  constructor
  · rintro ⟨f, hfin', hsum, hpos, hone⟩
    have hT' := toFinset_triple_union_single hfin'
    rw [hT', hsplit] at hsum hone
    rw [Finset.sum_insert hwmem] at hsum hone
    rw [sum_triple_first_v] at hsum
    rw [sum_triple_first_s] at hone
    refine ⟨f x, (if v = x then 0 else f v),
      (if u = x then 0 else if u = v then 0 else f u), f w,
      hpos w (Set.mem_singleton w), ?_, ?_⟩
    · linarith
    · rw [hsum]; abel
  · rintro ⟨t1, t2, t3, t4, ht4, hsum, hy⟩
    refine ⟨fun z => (if z = x then t1 else 0) + (if z = v then t2 else 0) +
      (if z = u then t3 else 0) + (if z = w then t4 else 0), hfin, ?_, ?_, ?_⟩
    · rw [hTeq, finset_sum_indicators_v]; exact hy
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      simpa [hwx, hwv, hwu] using ht4
    · rw [hTeq, finset_sum_indicators_s]; exact hsum

/-- HOL planarity.hl :13585-13594 `AFF_GT_1_3`

HOL 原文：
```
!x v u w.
        DISJOINT {x} {v,u,w}
        ==> aff_gt {x} {v,u,w} =
             {y | ?t1 t2 t3 t4.
                     &0 < t2 /\ &0< t3 /\ &0<t4 /\
                     t1 + t2 +t3 +t4 = &1 /\
                     y = t1 % x + t2 % v + t3 % u +t4 % w }
```

证明思路：同 `AFF_GT_3_1`（HOL `AFF_TAC`）。`affGt {x}{v,u,w}` 的
`{v,u,w}` 侧三系数严格正、`x` 侧任意；`DISJOINT` 保证四点互异，
去重求和后逐项对应，反向构造 `Affsign` 见证。

候选已有引理：
- `affGt`（Kepler/Geom/Aff.lean:39）
- `Affsign`（Kepler/Geom/Aff.lean:32）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165，1-2 形状）
- `AFF_GT_3_1`（本文件下文，HOL :13573） -/
private theorem toFinset_single_union_triple {x v u w : V3}
    (h : ({x} ∪ {v, u, w} : Set V3).Finite) :
    h.toFinset = ({x, v, u, w} : Finset V3) := by
  apply Finset.ext
  intro z
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff, Finset.mem_insert, Finset.mem_singleton]

theorem AFF_GT_1_3 (x v u w : V3)
    (hdis : Disjoint ({x} : Set V3) {v, u, w}) :
    affGt ({x} : Set V3) {v, u, w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 < t2 ∧ 0 < t3 ∧ 0 < t4 ∧
        t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • v + t3 • u + t4 • w} := by
  have hdis' := Set.disjoint_left.mp hdis
  have hxv : x ≠ v := by
    intro he; exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  have hxu : x ≠ u := by
    intro he; exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  have hxw : x ≠ w := by
    intro he; exact hdis' (Set.mem_singleton x) (by rw [he]; simp)
  ext y
  simp only [affGt, Set.mem_setOf_eq, Affsign]
  constructor
  · rintro ⟨f, hfin, hsum, hpos, hone⟩
    have hfv : 0 < f v := hpos v (by simp)
    have hfu : 0 < f u := hpos u (by simp)
    have hfw : 0 < f w := hpos w (by simp)
    have hTeq := toFinset_single_union_triple hfin
    rw [hTeq] at hsum hone
    rw [Finset.sum_insert (by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or]
      exact ⟨hxv, hxu, hxw⟩)] at hsum hone
    rw [sum_triple_first_v f v u w] at hsum
    rw [sum_triple_first_s f v u w] at hone
    by_cases hvu : u = v
    · by_cases hwv : w = v
      · simp only [hvu, hwv, if_true] at hone hsum
        refine ⟨f x, f v / 3, f v / 3, f v / 3, ?_, ?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith
        · rw [hsum]; simp only [hvu, hwv]; module
      · simp only [hvu, hwv, if_true, if_false] at hone hsum
        refine ⟨f x, f v / 2, f v / 2, f w, ?_, ?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · exact hfw
        · linarith
        · rw [hsum]; simp only [hvu]; module
    · by_cases hwv : w = v
      · simp only [hvu, hwv, if_true, if_false] at hone hsum
        refine ⟨f x, f v / 2, f u, f v / 2, ?_, ?_, ?_, ?_, ?_⟩
        · linarith
        · exact hfu
        · linarith
        · linarith
        · rw [hsum]; simp only [hwv]; module
      · by_cases hwu : w = u
        · simp only [hvu, hwu, if_true, if_false] at hone hsum
          refine ⟨f x, f v, f u / 2, f u / 2, ?_, ?_, ?_, ?_, ?_⟩
          · exact hfv
          · linarith
          · linarith
          · linarith
          · rw [hsum]; simp only [hwu]; module
        · simp only [hvu, hwv, hwu, if_false] at hone hsum
          refine ⟨f x, f v, f u, f w, ?_, ?_, ?_, ?_, ?_⟩
          · exact hfv
          · exact hfu
          · exact hfw
          · linarith
          · rw [hsum]; module
  · rintro ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsum, hy⟩
    have hfin : ({x} ∪ {v, u, w} : Set V3).Finite :=
      (Set.finite_singleton x).union (((Set.finite_singleton w).insert u).insert v)
    refine ⟨fun z => (if z = x then t1 else 0) + (if z = v then t2 else 0) +
      (if z = u then t3 else 0) + (if z = w then t4 else 0), hfin, ?_, ?_, ?_⟩
    · rw [toFinset_single_union_triple hfin, finset_sum_indicators_v]; exact hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · simp only [if_neg (Ne.symm hxv)]
        split_ifs <;> linarith
      · simp only [if_neg (Ne.symm hxu)]
        split_ifs <;> linarith
      · simp only [if_neg (Ne.symm hxw)]
        split_ifs <;> linarith
    · rw [toFinset_single_union_triple hfin, finset_sum_indicators_s]; exact hsum

/-- HOL planarity.hl :13595-13606 `AFF_GE_1_3`

HOL 原文：
```
!x v u w.
        DISJOINT {x} {v,u,w}
        ==> aff_ge {x} {v,u,w} =
             {y | ?t1 t2 t3 t4.
                     &0 <= t2 /\ &0<= t3 /\ &0<= t4 /\
                     t1 + t2 +t3 +t4 = &1 /\
                     y = t1 % x + t2 % v + t3 % u +t4 % w }
```

证明思路：同 `AFF_GT_1_3`，但 `affGe` 的 `sgn` 为 `0 ≤ ·`（HOL
`AFF_TAC`）。展开 `affGe`/`Affsign` 后 `{v,u,w}` 侧系数取非负，
`x` 侧任意；反向由非负系数构造见证。

候选已有引理：
- `affGe`（Kepler/Geom/Aff.lean:42）
- `Affsign`（Kepler/Geom/Aff.lean:32）
- `mem_affGe_singleton_pair`（Kepler/Text/TopologyFan.lean:2019）
- `mem_affGe_pair`（Kepler/Text/TopologyFan.lean:1967）
- `aff_ge_1_2`（Kepler/Text/Planarity.lean:622）
- `AFF_GT_1_3`（本文件上文，HOL :13585） -/
theorem AFF_GE_1_3 (x v u w : V3)
    (hdis : Disjoint ({x} : Set V3) {v, u, w}) :
    affGe ({x} : Set V3) {v, u, w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t2 ∧ 0 ≤ t3 ∧ 0 ≤ t4 ∧
        t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • v + t3 • u + t4 • w} := by
  sorry

/-! ## 四点不共面的互异性与不交性（planarity.hl:13607-13631） -/

/-- HOL planarity.hl :13607-13622 `notcoplanar_disjoint`

HOL 原文：
```
!x  v u w:real^3.
~coplanar {x,v,u,w} 
==> ~(x=v) /\ ~(x=u) /\ ~(x=w)/\ ~(v=u) /\ ~(v=w) /\ ~(u=w)
```

证明思路：每个等式假设都使四点集降为至多三点（例如 `x=v` 时
`{x,v,u,w} = {x,u,w}`），而 `coplanar_triple` 说明三点集共面，与
`~coplanar` 矛盾；也可直接由 `notcoplanar_imp_notcollinear_fan`
在相应三点上取不共线，再取 `th3` 型的互异分量。

编码说明：HOL `~coplanar {x,v,u,w}` 为 `¬ Coplanar ({x,v,u,w} : Set V3)`；
等式假设编码为 `≠` 的合取。

候选已有引理：
- `Coplanar`（Kepler/Geom/Coplanar.lean:23）
- `coplanar_triple`（Kepler/Geom/Coplanar.lean:45）
- `coplanar_pair`（Kepler/Geom/Coplanar.lean:39）
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `collinear3_of_eq`（Kepler/Geom/Azim.lean:121）
- `collinear3_pair_left`（Kepler/Geom/AzimLemmas.lean:164）
- `collinear3_pair_right`（Kepler/Geom/AzimLemmas.lean:171） -/
theorem notcoplanar_disjoint (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    x ≠ v ∧ x ≠ u ∧ x ≠ w ∧ v ≠ u ∧ v ≠ w ∧ u ≠ w := by
  sorry

/-- HOL planarity.hl :13623-13631 `notcoplanar_disjoints`

HOL 原文：
```
!x  v u w:real^3.
~coplanar {x,v,u,w} 
==> DISJOINT{x,v,u} {w} /\ DISJOINT{x,u,w} {v} /\ DISJOINT{x,w,v} {u} /\ DISJOINT{x} {v,u,w}/\ DISJOINT {x,u} {v,w} /\ DISJOINT {x} {v,u} /\ DISJOINT {x} {u,w} /\ DISJOINT {x} {w,v}
```

证明思路：由 `notcoplanar_disjoint` 得六条两两互异，再逐条把
`Disjoint A B` 化为 `∀ a∈A, a∉B`，对每个交叠情形用相应的
`≠` 矛盾；HOL 的 `SET_TAC` 对应这里的集合外延/`simp` 收尾。

编码说明：HOL `DISJOINT A B` 为 `Disjoint A B`（`Set V3`）；各点集
`{x,v,u}` 等按字面集合书写。

候选已有引理：
- `notcoplanar_disjoint`（本文件上文，HOL :13607）
- `Set.disjoint_left`/`Set.disjoint_iff_forall_ne`（Mathlib）
- `collinear3_of_eq`（Kepler/Geom/Azim.lean:121）
- `collinear3_pair_left`（Kepler/Geom/AzimLemmas.lean:164）
- `collinear3_pair_right`（Kepler/Geom/AzimLemmas.lean:171） -/
theorem notcoplanar_disjoints (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    Disjoint ({x, v, u} : Set V3) {w} ∧
    Disjoint ({x, u, w} : Set V3) {v} ∧
    Disjoint ({x, w, v} : Set V3) {u} ∧
    Disjoint ({x} : Set V3) {v, u, w} ∧
    Disjoint ({x, u} : Set V3) {v, w} ∧
    Disjoint ({x} : Set V3) {v, u} ∧
    Disjoint ({x} : Set V3) {u, w} ∧
    Disjoint ({x} : Set V3) {w, v} := by
  sorry

end Kepler.Text
