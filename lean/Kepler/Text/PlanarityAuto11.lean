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
  sorry

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
  sorry

/-! ## 四点 aff_gt 交集条件（planarity.hl:13169-13292） -/

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
  sorry

/-! ## dart_leads_into 恰为分量（planarity.hl:13293-13572） -/

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
  sorry

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
  sorry

/-! ## aff_gt/aff_ge 的三点组合刻画（planarity.hl:13573-13606） -/

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
  sorry

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
theorem AFF_GT_1_3 (x v u w : V3)
    (hdis : Disjoint ({x} : Set V3) {v, u, w}) :
    affGt ({x} : Set V3) {v, u, w} =
      {y | ∃ t1 t2 t3 t4 : ℝ, 0 < t2 ∧ 0 < t3 ∧ 0 < t4 ∧
        t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • v + t3 • u + t4 • w} := by
  sorry

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
