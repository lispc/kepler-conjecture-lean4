/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18m.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18m of block 18, planarity.hl:12219-12818): the
yfan-component / dart-leads-into layer
- `aff_ge_2_1_is_exists_point_inaff_ge_1_2` (12219)
- `not_azim_points_in_yfan` (12261)
- `exists_edge_bounded_topological_component_yfan` (12323)
- `aff_gt_in_w_dart_fan` (12425)
- `not_empty_rcone_fan_inter_aff_gt` (12464)
- `condition_rw_dart_fan_inter_aff_gt_is_not_empty` (12574)
- `exists_edge_rw_dart_fan_inter_aff_gt_not_empty_fan` (12599)
- `exists_edge_rw_dart_fan_inter_topological_component_not_empty_fan` (12630)
- `exists_dart_leads_into_edge_eq_topological_component_fan` (12695)
- `not_azim_points1_in_yfan` (12759)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `xfan`/`yfan`/`topological_component_yfan` ↔ `xfan`/`yfan`/
  `topologicalComponentYfan` (Kepler/Text/Fan.lean:154/158/199).
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42).
- HOL `~collinear {a,b,c}` ↔ `¬ Collinear3 a b c`
  (Kepler/Geom/Azim.lean:43; defeq to `¬ Collinear ℝ ({a,b,c} : Set V3)`).
- HOL `rcone_fan`/`rw_dart_fan`/`w_dart_fan` ↔ `rconeFan`/`rwDartFan`
  (Kepler/Text/TopologyFan.lean:2253/3145) and `wDartFan`
  (Kepler/Text/Fan.lean:162). `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179).
- HOL `DISJOINT {x} {y,w}` ↔ `Disjoint ({x} : Set V3) {y, w}`.
- HOL `azim` ↔ `azim` (Kepler/Geom/Azim.lean:58); `cos`/`pi` ↔
  `Real.cos`/`Real.pi`.
- HOL `remark1_fan` is NOT ported under that name; its distinctness
  component is `edge_ne_of_fan` (Kepler/Text/Fan.lean:1039), its
  `aff_ge` membership component is `point_in_aff_ge`
  (Kepler/Text/Planarity.lean:4334). Gaps noted per-theorem.
- HOL `AZIM_EQ_0_GE` is NOT ported under that name; the closest is
  `azim_eq_zero_iff` (Kepler/Geom/AzimLemmas.lean:296). Gap noted in
  `not_azim_points_in_yfan` / `not_azim_points1_in_yfan`.
- HOL `AFF_GE_2_1` / `AFF_GE_1_2` membership forms are only partly
  ported: `aff_ge_1_2` (Kepler/Text/Planarity.lean:622) exists, the
  `aff_ge_2_1` membership form does not (only `closed_aff_ge_2_1`,
  Kepler/Text/TopologyFan.lean:2635). Gap noted in
  `aff_ge_2_1_is_exists_point_inaff_ge_1_2`.
-/

import Kepler.Text.PlanarityAuto8

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## aff_ge 2-1 中的点可缩到 aff_ge 1-2（planarity.hl:12219-12260） -/

/-- HOL planarity.hl :12219-12260 `aff_ge_2_1_is_exists_point_inaff_ge_1_2`

HOL 原文：
```
!x:real^3 y:real^3 z:real^3 w:real^3.
DISJOINT {x} {y,w} /\ DISJOINT {x,y} {w}/\ z IN aff_ge {x,y} {w}
==> ?t. &0<t /\ t< &1 /\ (&1-t) %y+ t%z IN aff_ge {x} {y,w}
```

证明思路：由 `AFF_GE_2_1`（`aff_ge {x,y} {w}` 的非负组合刻画）把 `z` 写成
`t1•x + t2•y + t3•w`（`t1,t2,t3 ≥ 0`，和 1）。按 `0 ≤ t2` 与 `t2 < 0` 分情形：
前者取 `t = 1/2`，把 `(1-t)•y + t•z` 重组为 `x,y,w` 的非负组合；后者取
`t = 1/(1-t2)`（此时 `1-t2 > 1`），同样重组。`DISJOINT` 假设保证系数良定。

编码说明：HOL `DISJOINT {x} {y,w}` 为 `Disjoint ({x} : Set V3) {y, w}`，
`DISJOINT {x,y} {w}` 为 `Disjoint ({x, y} : Set V3) {w}`；HOL `%` 为 `•`。
这是纯仿射组合事实，但 `affGe`（非负组合锥）在 Mathlib 中无同名对象，
故不跳过、按 HOL 原样落地。

候选已有引理：
- `aff_ge_1_2`（Kepler/Text/Planarity.lean:622）
- `mem_affGe_singleton`（Kepler/Text/TopologyFan.lean:2664）
- `affGe_ray`（Kepler/Geom/Aff.lean:196）
- `Affsign`（Kepler/Geom/Aff.lean:32，`affGt`/`affGe` 的组合定义） -/
theorem aff_ge_2_1_is_exists_point_inaff_ge_1_2 (x y z w : V3)
    (h1 : Disjoint ({x} : Set V3) {y, w})
    (h2 : Disjoint ({x, y} : Set V3) {w})
    (hz : z ∈ affGe {x, y} {w}) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1 - t) • y + t • z ∈ affGe {x} {y, w} := by
  sorry

/-! ## yfan 中点的 azim 不为零（planarity.hl:12261-12322） -/

/-- HOL planarity.hl :12261-12322 `not_azim_points_in_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 u:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ u IN V
/\ y IN aff_ge {x} {u}
/\ y IN xfan (x,V,E)
/\ ~(y=x)
 /\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==>(!(w1:real^3). (w1 IN (set_of_edge u V E)) ==> ~(azim x u z w1= &0))
```

证明思路：反设某邻居 `w1` 使 `azim x u z w1 = 0`。由 `remark1_fan`
（互异性 `edge_ne_of_fan` + `point_in_aff_ge`）得 `w1 ∈ aff_ge {x} {u}` 的
边关系；`point_in_yfan_not_x_fan` 给 `z ≠ x`；`no_origin_aff_ge_is_aff_gt`
把 `y ∈ aff_ge {x} {u}` 强化为 `y ∈ aff_gt {x} {u}`，再用 `in_aff_gt_eq_azim`
把 `azim x u z w1` 换成 `azim x y z w1`；`AZIM_EQ_0_GE`（本仓对应
`azim_eq_zero_iff`）给出共线，经 `permutes_4points_collinear1`、
`aff_ge_2_1_is_exists_point_inaff_ge_1_2`、`aff_ge_eq_aff_gt_union_aff_ge`
与 `aff_ge1_subset_aff_ge` 推出 `(1-t)•y + t•z ∈ xfan`，与 `hconn` 给出的
`∈ yfan = univ \ xfan` 矛盾。

编码缺口：HOL `AZIM_EQ_0_GE` 未以该名移植；最接近 `azim_eq_zero_iff`
（Kepler/Geom/AzimLemmas.lean:296）。HOL `th3` 未以该名移植；可用
`collinear3_iff_mem_affineSpan`（Kepler/Text/TopologyFan.lean:785）。

候选已有引理：
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `no_origin_aff_ge_is_aff_gt`（Kepler/Text/PlanarityAuto8.lean:414）
- `in_aff_gt_eq_azim`（Kepler/Text/PlanarityAuto8.lean:356）
- `point_in_yfan_and_point_in_xfan_indepent_fan`（Kepler/Text/PlanarityAuto8.lean:195）
- `aff_ge_1_1_subset_aff_fan`（Kepler/Text/PlanarityAuto6.lean:239）
- `permutes_4points_collinear1`（Kepler/Text/PlanarityAuto8.lean:270）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `aff_ge1_subset_aff_ge`（Kepler/Text/Planarity.lean:4041）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296） -/
theorem not_azim_points_in_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (y z u : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hu : u ∈ V) (hyge : y ∈ affGe {x} {u})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    ∀ w1 : V3, w1 ∈ setOfEdge u V E → azim x u z w1 ≠ 0 := by
  sorry

/-! ## 引导进入有界 yfan 分量的边（planarity.hl:12323-12424） -/

/-- HOL planarity.hl :12323-12424 `exists_edge_bounded_topological_component_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 u:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ u IN V
/\ y IN aff_ge {x} {u}
/\ y IN xfan(x,V,E)
/\ ~(y=x)
/\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==> ?w. {u,w} IN E /\  z IN w_dart_fan x V E (x,u,w,sigma_fan x V E u w)
```

证明思路：由 `nonsetedge_fully_surround_fan`、`zpoint_in_yfan` 与
`v_subset_xfan`/`set_of_edge_subset_edges` 得 `z ∉ set_of_edge u V E`；用
`exists_edge_component_yfan` 取邻居 `w` 使 `azim1 x u z` 最小。`remark1_fan`
给 `{u,w} ∈ E`。展开 `w_dart_fan`（`wedge` 定义）只需证
`azim x u w z ∈ (0, azim x u w (sigma_fan u w))`：由 `not_azim_points_in_yfan`
知 `azim x u z w ≠ 0`，`azim` 给 `azim x u w z ≥ 0`，再用 `SIGMA_FAN` 与
`sum4_azim_fan` 比较 `sigma_fan`；`azim = 0` 情形由 `AZIM_COMPL_EQ_0` 排除，
否则 `AZIM_COMPL` 处理补角。

候选已有引理：
- `exists_edge_component_yfan`（Kepler/Text/PlanarityAuto8.lean:464）
- `zpoint_in_yfan`（Kepler/Text/PlanarityAuto7.lean:83）
- `v_subset_xfan`（Kepler/Text/PlanarityAuto8.lean:501）
- `set_of_edge_subset_edges`（Kepler/Text/PlanarityAuto8.lean:526）
- `not_azim_points_in_yfan`（本文件上文）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `unique_azim0_point_fan`（Kepler/Text/Fan.lean:456）
- `unique_azim_point_fan`（Kepler/Text/Fan.lean:463）
- `wDartFan`（Kepler/Text/Fan.lean:162）、`wedge`（Kepler/Geom/Azim.lean:63） -/
theorem exists_edge_bounded_topological_component_yfan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (U : Set V3) (y z u : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hu : u ∈ V) (hyge : y ∈ affGe {x} {u})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    ∃ w : V3, {u, w} ∈ E ∧
      z ∈ wDartFan x V E (x, u, w, sigmaFan x V E u w) := by
  sorry

/-! ## aff_gt 边锥含于 w_dart_fan（planarity.hl:12425-12463） -/

/-- HOL planarity.hl :12425-12463 `aff_gt_in_w_dart_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) u:real^3 w:real^3 y:real^3.
FAN(x,V,E) /\ {u,w} IN E
/\ y IN w_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(sigma_fan x V E u w:real^3)) 
/\ fan80(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==> aff_gt {x} {u,y} SUBSET w_dart_fan x V E ((x:real^3),(u:real^3),(w:real^3),(sigma_fan x V E u w:real^3)) 
```

证明思路：展开 `w_dart_fan` 与 `wedge`，对任意
`x' ∈ aff_gt {x} {u,y}` 证其落在同一 wedge。由 `fan80` 与 `hcard` 保证
`set_of_edge u V E ≠ {w}`；用 `aff_gt_inter_aff_gt` 把
`aff_gt {x} {u,y}` 分解为两个 `aff_gt` 之交，`aff_gt_imp_not_collinear` 给
非共线，再用 `AZIM_EQ_ALT`（本仓 `azim_eq_azim_iff`）把
`azim x u w x'` 与 `azim x u w y` 联系起来完成 wedge 包含。

编码缺口：HOL `AZIM_EQ_ALT` 未以该名移植；最接近 `azim_eq_azim_iff`
（Kepler/Geom/AzimLemmas.lean:193）。

候选已有引理：
- `aff_gt_inter_aff_gt`（Kepler/Text/Planarity.lean:4078）
- `aff_gt_imp_not_collinear`（Kepler/Text/PlanarityAngle.lean:1069）
- `azim_eq_azim_iff`（Kepler/Geom/AzimLemmas.lean:193）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `wDartFan`（Kepler/Text/Fan.lean:162）、`wedge`（Kepler/Geom/Azim.lean:63）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317） -/
theorem aff_gt_in_w_dart_fan (x : V3) (V : Set V3) (E : Set (Set V3))
    (u w y : V3)
    (hfan : FAN x V E) (huw : {u, w} ∈ E)
    (hy : y ∈ wDartFan x V E (x, u, w, sigmaFan x V E u w))
    (hfan80 : fan80 x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard) :
    affGt {x} {u, y} ⊆ wDartFan x V E (x, u, w, sigmaFan x V E u w) := by
  sorry

/-! ## rcone 与 aff_gt 的非空交（planarity.hl:12464-12573） -/

/-- HOL planarity.hl :12464-12573 `not_empty_rcone_fan_inter_aff_gt`

HOL 原文：
```
!x v u:real^3 h:real.
~collinear {x,v,u} /\ &0< h /\ h<= pi==>
~(rcone_fan x v (cos h) INTER aff_gt {x} {v, u}={})
```

证明思路：HOL 按 `(v-x)·(u-x) ≤ 0` 与 `> 0` 分两情形，各显式构造
`sin s1 • e1_fan + cos s1 • e3_fan + x`（取
`s1 = min h (pi/2)/2` 或 `s1 = min h (atn(...))/2`）。用
`properties_coordinate`（e1/e2/e3 标架的正交单位性）与
`SIN_CIRCLE` 算范数为 1、与 `v-x` 的夹角为 `s1`，再由
`condition_to_in_aff_gt_by_angle`（或 `condition1_to_in_aff_gt_by_angle`）
得该点在 `aff_gt {x} {v,u}`，同时由 `cos s1 > cos h` 落在 `rcone_fan` 内。

编码缺口：HOL `properties_coordinate` 未以该名移植；可用
`e1Fan_dot_self` / `e1Fan_dot_e2` / `e1Fan_dot_e3` / `e3Fan_dot_self`
（Kepler/Text/TopologyFan.lean:2415/2424/2431/2347）及
`propertiesCoordinate`（若存在）拼合。

候选已有引理：
- `condition_to_in_aff_gt_by_angle`（Kepler/Text/PlanarityAngle.lean:112）
- `condition1_to_in_aff_gt_by_angle`（Kepler/Text/PlanarityAngle.lean:280）
- `e1Fan_dot_self`（Kepler/Text/TopologyFan.lean:2415）
- `e1Fan_dot_e2`（Kepler/Text/TopologyFan.lean:2424）
- `e1Fan_dot_e3`（Kepler/Text/TopologyFan.lean:2431）
- `e3Fan_dot_self`（Kepler/Text/TopologyFan.lean:2347）
- `rconeFan`（Kepler/Text/TopologyFan.lean:2253）
- `collinear3_iff_mem_affineSpan`（Kepler/Text/TopologyFan.lean:785） -/
theorem not_empty_rcone_fan_inter_aff_gt (x v u : V3) (h : ℝ)
    (hnc : ¬ Collinear3 x v u)
    (hh0 : 0 < h) (hhpi : h ≤ Real.pi) :
    rconeFan x v (Real.cos h) ∩ affGt {x} {v, u} ≠ ∅ := by
  sorry

/-! ## rw_dart_fan 与 aff_gt 的非空交（planarity.hl:12574-12598） -/

/-- HOL planarity.hl :12574-12598 `condition_rw_dart_fan_inter_aff_gt_is_not_empty`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 z:real^3 h:real.
FAN(x,V,E)/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E) /\ ~collinear {x,v,z}
/\ {v,u} IN E /\ z IN w_dart_fan x V E (x,v,u,sigma_fan x V E v u)
/\ &0<h /\ h<= pi
==>
~(rw_dart_fan x V E ((x:real^3),(v:real^3),(u:real^3),sigma_fan x V E v u ) (cos(h)) INTER aff_gt {x} {v,z}={})
```

证明思路：由 `aff_gt_in_w_dart_fan`（作用于 `z ∈ w_dart_fan`）得
`aff_gt {x} {v,z} ⊆ w_dart_fan`，于是 `rw_dart_fan ∩ aff_gt` 化为
`rcone_fan ∩ aff_gt`（集合交的交换/结合）；再由
`not_empty_rcone_fan_inter_aff_gt`（`~collinear {x,v,z}`）即得非空。

候选已有引理：
- `aff_gt_in_w_dart_fan`（本文件上文）
- `not_empty_rcone_fan_inter_aff_gt`（本文件上文）
- `rwDartFan`（Kepler/Text/TopologyFan.lean:3145）
- `wDartFan`（Kepler/Text/Fan.lean:162） -/
theorem condition_rw_dart_fan_inter_aff_gt_is_not_empty (x : V3) (V : Set V3)
    (E : Set (Set V3)) (v u z : V3) (h : ℝ)
    (hfan : FAN x V E)
    (hcard : ∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard)
    (hfan80 : fan80 x V E) (hnc : ¬ Collinear3 x v z)
    (hvu : {v, u} ∈ E)
    (hz : z ∈ wDartFan x V E (x, v, u, sigmaFan x V E v u))
    (hh0 : 0 < h) (hhpi : h ≤ Real.pi) :
    rwDartFan x V E (x, v, u, sigmaFan x V E v u) (Real.cos h) ∩
      affGt {x} {v, z} ≠ ∅ := by
  sorry

/-! ## 存在边使 rw_dart_fan 与 aff_gt 交非空（planarity.hl:12599-12629） -/

/-- HOL planarity.hl :12599-12629 `exists_edge_rw_dart_fan_inter_aff_gt_not_empty_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 u:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ u IN V
/\ y IN aff_ge {x} {u}
/\ y IN xfan(x,V,E)
/\ ~(y=x)
/\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==> ?w. {u,w} IN E /\
(!h. &0<h /\ h<= pi
==> ~((rw_dart_fan x V E (x,u,w,sigma_fan x V E u w) (cos h)) INTER aff_gt {x} {u,z}={}))
```

证明思路：由 `exists_edge_bounded_topological_component_yfan` 取 `w` 使
`{u,w} ∈ E` 且 `z ∈ w_dart_fan x V E (x,u,w,sigma_fan u w)`；对任意
`h ∈ (0,π]` 用 `condition_rw_dart_fan_inter_aff_gt_is_not_empty`（此时
`~collinear {x,u,z}` 由 `remark1_fan`、`point_in_yfan_and_point_in_xfan_indepent_fan`、
`aff_ge_1_1_subset_aff_fan` 与 `permutes_4points_collinear` 提供）得非空。

候选已有引理：
- `exists_edge_bounded_topological_component_yfan`（本文件上文）
- `condition_rw_dart_fan_inter_aff_gt_is_not_empty`（本文件上文）
- `point_in_yfan_and_point_in_xfan_indepent_fan`（Kepler/Text/PlanarityAuto8.lean:195）
- `aff_ge_1_1_subset_aff_fan`（Kepler/Text/PlanarityAuto6.lean:239）
- `permutes_4points_collinear`（Kepler/Text/PlanarityAuto8.lean:237）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039） -/
theorem exists_edge_rw_dart_fan_inter_aff_gt_not_empty_fan (x : V3) (V : Set V3)
    (E : Set (Set V3)) (U : Set V3) (y z u : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hu : u ∈ V) (hyge : y ∈ affGe {x} {u})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    ∃ w : V3, {u, w} ∈ E ∧
      ∀ h : ℝ, 0 < h → h ≤ Real.pi →
        rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos h) ∩
          affGt {x} {u, z} ≠ ∅ := by
  sorry

/-! ## 存在边使 rw_dart_fan 与分量交非空（planarity.hl:12630-12694） -/

/-- HOL planarity.hl :12630-12694 `exists_edge_rw_dart_fan_inter_topological_component_not_empty_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 u:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ u IN V
/\ y IN aff_ge {x} {u}
/\ y IN xfan(x,V,E)
/\ ~(y=x)
/\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))

==> ?w. {u,w} IN E 
/\(!h.  &0<h /\ h<= pi
==> ~((rw_dart_fan x V E (x,u,w,sigma_fan x V E u w) (cos h)) INTER U={}))
```

证明思路：由 `nonsetedge_fully_surround_fan`、`point_in_yfan_not_x_fan` 与
`aff_gt_subset_component_y_fan` 得 `aff_gt {x} {y,z} ⊆ U`；用
`exists_edge_rw_dart_fan_inter_aff_gt_not_empty_fan` 取 `w`。关键是把
`aff_gt {x} {u,z}` 换成 `aff_gt {x} {y,z}`（`aff_gt_1_2_scale_fan`，由
`y ∈ aff_ge {x} {u}` 的显式组合与 `AFF_GE_1_1` 给出缩放因子），从而
`rw_dart_fan ∩ U ≠ ∅` 由 `rw_dart_fan ∩ aff_gt {x} {u,z} ≠ ∅` 与
`aff_gt {x} {y,z} = aff_gt {x} {u,z}` 推出。

候选已有引理：
- `exists_edge_rw_dart_fan_inter_aff_gt_not_empty_fan`（本文件上文）
- `aff_gt_subset_component_y_fan`（Kepler/Text/PlanarityAuto7.lean:454）
- `aff_gt_1_2_scale_fan`（Kepler/Text/PlanarityAngle.lean:1692）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `point_in_yfan_and_point_in_xfan_indepent_fan`（Kepler/Text/PlanarityAuto8.lean:195）
- `permutes_4points_collinear`（Kepler/Text/PlanarityAuto8.lean:237） -/
theorem exists_edge_rw_dart_fan_inter_topological_component_not_empty_fan
    (x : V3) (V : Set V3) (E : Set (Set V3)) (U : Set V3) (y z u : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hu : u ∈ V) (hyge : y ∈ affGe {x} {u})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    ∃ w : V3, {u, w} ∈ E ∧
      ∀ h : ℝ, 0 < h → h ≤ Real.pi →
        rwDartFan x V E (x, u, w, sigmaFan x V E u w) (Real.cos h) ∩ U ≠ ∅ := by
  sorry

/-! ## 存在边其 dart_leads_into 恰为该分量（planarity.hl:12695-12758） -/

/-- HOL planarity.hl :12695-12758 `exists_dart_leads_into_edge_eq_topological_component_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 u:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ u IN V
/\ y IN aff_ge {x} {u}
/\ y IN xfan(x,V,E)
/\ ~(y=x)
/\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan(x,V,E))
==> ?w. {u,w} IN E /\ dart_leads_into x V E u w = U
```

证明思路：由 `exists_edge_rw_dart_fan_inter_topological_component_not_empty_fan`
取 `w`，再由 `not_empty_rw_dart_fan` 取 `h`（`h' ∈ (0,1)`）使
`rw_dart_fan (cos h1) ≠ ∅`。取 `h1 = min h (acs h')/2`，`cos h1 > h'`，
故 `rw_dart_fan (cos h1) ⊆ yfan` 且预连通；由 `DART_LEADS_INTO`
（`dartLeadsInto_spec`）与 `rw_dart_avoids_fan` 得 `dart_leads_into` 满足刻画
性质；`expand_element_in_topological_component_yfan` 把 `U` 展开为
`connected_component (yfan) z`，最后用
`connected_component` 的重叠引理（`CONNECTED_COMPONENT_OVERLAP`）得
`dart_leads_into x V E u w = U`。

编码缺口：HOL `DART_LEADS_INTO` 未以该名移植；最接近
`dartLeadsInto_spec`（Kepler/Text/TopologyFan.lean:4233）与
`dart_leads_into_mem_topologicalComponentYfan`
（Kepler/Text/TopologyFan.lean:4280）。

候选已有引理：
- `exists_edge_rw_dart_fan_inter_topological_component_not_empty_fan`（本文件上文）
- `not_empty_rw_dart_fan`（Kepler/Text/TopologyFan.lean:4125）
- `dartLeadsInto_spec`（Kepler/Text/TopologyFan.lean:4233）
- `unique_dart_leads_into`（Kepler/Text/TopologyFan.lean:4244）
- `dart_leads_into_mem_topologicalComponentYfan`（Kepler/Text/TopologyFan.lean:4280）
- `rw_dart_avoids_fan`（Kepler/Text/TopologyFan.lean:3303）
- `expand_element_in_topological_component_yfan`（Kepler/Text/PlanarityAuto7.lean:271）
- `dartLeadsInto`（Kepler/Text/TopologyFan.lean:4179） -/
theorem exists_dart_leads_into_edge_eq_topological_component_fan
    (x : V3) (V : Set V3) (E : Set (Set V3)) (U : Set V3) (y z u : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (hu : u ∈ V) (hyge : y ∈ affGe {x} {u})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    ∃ w : V3, {u, w} ∈ E ∧ dartLeadsInto x V E u w = U := by
  sorry

/-! ## 情形 2：aff_gt 上点的 azim 不为零（planarity.hl:12759-12818） -/

/-- HOL planarity.hl :12759-12818 `not_azim_points1_in_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) U:real^3->bool y:real^3 z:real^3 u:real^3 w:real^3.
FAN(x,V,E) 
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ U IN topological_component_yfan (x,V,E)
/\ z IN U
/\ {u,w} IN E
/\ y IN aff_gt {x} {u,w}
/\ y IN xfan (x,V,E)
/\ ~(y=x)
 /\(!t. &0< t /\ t< &1==>   (&1-t)%y+t%z IN yfan (x,V,E))
==>  ~(azim x y z w= &0)
```

证明思路：反设 `azim x y z w = 0`。由 `remark1_fan`、`nonsetedge_fully_surround_fan`、
`point_in_yfan_not_x_fan` 与 `point_in_yfan_and_point_in_xfan_indepent_fan`
得 `y` 与 `w` 的独立性；`properties_of_collinear4_points_fan` 处理 `x,w,u,y`
共线置换；`AZIM_EQ_0_GE`（本仓 `azim_eq_zero_iff`）把 `azim = 0` 化为共线，
`th3`（`collinear3_iff_mem_affineSpan`）展开；再用
`aff_ge_2_1_is_exists_point_inaff_ge_1_2` 与
`aff_ge_eq_aff_gt_union_aff_ge`、`aff_ge1_subset_aff_ge` 推出
`(1-t)•y + t•z ∈ xfan`，与 `hconn` 给出的 `∈ yfan = univ \ xfan` 矛盾。

编码缺口：HOL `AZIM_EQ_0_GE` 未以该名移植；最接近 `azim_eq_zero_iff`
（Kepler/Geom/AzimLemmas.lean:296）。HOL `th3` 未以该名移植；可用
`collinear3_iff_mem_affineSpan`（Kepler/Text/TopologyFan.lean:785）。

候选已有引理：
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `point_in_yfan_and_point_in_xfan_indepent_fan`（Kepler/Text/PlanarityAuto8.lean:195）
- `properties_of_collinear4_points_fan`（Kepler/Text/Planarity.lean:3087）
- `aff_ge_2_1_is_exists_point_inaff_ge_1_2`（本文件上文）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `aff_ge1_subset_aff_ge`（Kepler/Text/Planarity.lean:4041）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296） -/
theorem not_azim_points1_in_yfan (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) (y z u w : V3)
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hU : U ∈ topologicalComponentYfan x V E) (hz : z ∈ U)
    (huw : {u, w} ∈ E)
    (hy : y ∈ affGt {x} {u, w})
    (hyxfan : y ∈ xfan x V E) (hyx : y ≠ x)
    (hconn : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) • y + t • z ∈ yfan x V E) :
    azim x y z w ≠ 0 := by
  sorry

end Kepler.Text
