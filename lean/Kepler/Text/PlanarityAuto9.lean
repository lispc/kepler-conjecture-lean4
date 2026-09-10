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
  have hxy : x ≠ y := Set.disjoint_iff_forall_ne.mp h1 rfl (Or.inl rfl)
  have hyw : y ≠ w := Set.disjoint_iff_forall_ne.mp h2 (Or.inr rfl) rfl
  obtain ⟨t1, t2, t3, ht3, hsum, hz'⟩ := (mem_affGe_pair h2 hxy).mp hz
  by_cases ht2 : 0 ≤ t2
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    rw [mem_affGe_singleton_pair h1 hyw]
    refine ⟨t1 / 2, 1 / 2 + t2 / 2, t3 / 2, by linarith, by linarith, by linarith, ?_⟩
    rw [hz']
    module
  · simp only [not_le] at ht2
    have hpos : 0 < 1 - t2 := by linarith
    refine ⟨1 / (1 - t2), by positivity, ?_, ?_⟩
    · rw [div_lt_one hpos]; linarith
    · rw [mem_affGe_singleton_pair h1 hyw]
      refine ⟨t1 / (1 - t2), 0, t3 / (1 - t2), by norm_num, by positivity, ?_, ?_⟩
      · have hsum' : t1 + t3 = 1 - t2 := by linarith
        rw [add_zero, ← add_div, hsum', div_self (ne_of_gt hpos)]
      · rw [hz']
        field_simp
        module

/-- `affGt s t ⊆ affGe s t`：严格正系数组合是非负组合。 -/
private theorem affGt_subset_affGe_gen {s t : Set V3} : affGt s t ⊆ affGe s t := by
  intro v hv
  obtain ⟨f, hfin, hsum, hpos, hone⟩ := hv
  exact ⟨f, hfin, hsum, fun w hw => (hpos w hw).le, hone⟩

/-- `¬Collinear3 x v w` 蕴含 `{x}` 与 `{v,w}` 不交。 -/
private theorem disjoint_of_not_collinear3' {x v w : V3} (hnc : ¬ Collinear3 x v w) :
    Disjoint ({x} : Set V3) {v, w} := by
  rw [Set.disjoint_singleton_left]
  intro hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact hnc (collinear3_of_eq (v := x) (w := v) (w1 := w) h.symm)
  · exact hnc (collinear3_pair_left (v0 := x) (v1 := v) (x := w) h.symm)

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
  intro w1 hw1
  obtain ⟨huw1E, _hw1V⟩ := hw1
  intro hazim
  have hnc_xuw1 : ¬ Collinear3 x u w1 := fan_not_collinear hfan huw1E
  have hxu : x ≠ u := fun h => hnc_xuw1 (collinear3_of_eq h.symm)
  have hxw1 : x ≠ w1 := fun h => hnc_xuw1 (collinear3_pair_left h.symm)
  have hnc_xyz : ¬ Collinear3 x y z :=
    point_in_yfan_and_point_in_xfan_indepent_fan x V E U y z
      hfan hcard hfan80 hU hz hyxfan hyx hconn
  have hy_span : y ∈ affineSpan ℝ ({x, u} : Set V3) :=
    aff_ge_1_1_subset_aff_fan y x u hxu hyge
  have hnc_xyw1 : ¬ Collinear3 x y w1 :=
    permutes_4points_collinear1 x y u w1 hyx.symm hxu hy_span hnc_xuw1
  have hyw1 : y ≠ w1 :=
    fun h => hnc_xyw1 (collinear3_pair_right (v0 := x) (v1 := y) (x := w1) h.symm)
  have hyGt : y ∈ affGt {x} {u} :=
    no_origin_aff_ge_is_aff_gt x u y hxu hyx.symm hyge
  have hazim_xy : azim x y z w1 = 0 := by
    rw [in_aff_gt_eq_azim x y u z w1 hxu hyGt]
    exact hazim
  have hz_gt : z ∈ affGt {x, y} {w1} :=
    (azim_eq_zero_iff (v0 := x) (v1 := y) (w := z) (x := w1) hnc_xyz hnc_xyw1).mp hazim_xy
  have hz_ge : z ∈ affGe {x, y} {w1} := affGt_subset_affGe_gen hz_gt
  have h1 : Disjoint ({x} : Set V3) {y, w1} := disjoint_of_not_collinear3' hnc_xyw1
  have h2 : Disjoint ({x, y} : Set V3) {w1} := by
    rw [Set.disjoint_left]
    intro a ha
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hxw1
    · exact hyw1
  obtain ⟨t, ht0, ht1, hmem⟩ :=
    aff_ge_2_1_is_exists_point_inaff_ge_1_2 x y z w1 h1 h2 hz_ge
  have hy_ge_uw1 : y ∈ affGe {x} {u, w1} := by
    rw [aff_ge_eq_aff_gt_union_aff_ge hnc_xuw1]
    exact Or.inl (Or.inr hyge)
  have hdis_x_uw1 : Disjoint ({x} : Set V3) {u, w1} := by
    rw [Set.disjoint_singleton_left]
    intro hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hxu h
    · exact hxw1 h
  have hsub : affGe {x} {y, w1} ⊆ affGe {x} {u, w1} :=
    aff_ge1_subset_aff_ge (x := x) (v := u) (u := w1) (v1 := y)
      hdis_x_uw1 hnc_xyw1 hy_ge_uw1
  have hmem_uw1 : (1 - t) • y + t • z ∈ affGe {x} {u, w1} := hsub hmem
  have hxfan_mem : (1 - t) • y + t • z ∈ xfan x V E := ⟨{u, w1}, huw1E, hmem_uw1⟩
  exact (hconn t ht0 ht1).2 hxfan_mem

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
  have hE : E ≠ ∅ := nonsetedge_fully_surround_fan hcard hfan
  have hz_yfan : z ∈ yfan x V E :=
    zpoint_in_yfan x V E U z hfan hE hU hz
  have hsetV : setOfEdge u V E ⊆ V := set_of_edge_subset_edges V E u
  have hsetXfan : setOfEdge u V E ⊆ xfan x V E :=
    hsetV.trans (v_subset_xfan x V E hfan hcard)
  have hz_not_set : z ∉ setOfEdge u V E :=
    fun hzmem => hz_yfan.2 (hsetXfan hzmem)
  obtain ⟨w, hw_mem, hw_min⟩ :=
    exists_edge_component_yfan x V E u z hfan hcard hu hz_not_set
  refine ⟨w, hw_mem.1, ?_⟩
  have hcard_u : 1 < (setOfEdge u V E).ncard := hcard u hu
  have hnc_xyz : ¬ Collinear3 x y z :=
    point_in_yfan_and_point_in_xfan_indepent_fan x V E U y z
      hfan hcard hfan80 hU hz hyxfan hyx hconn
  have hnc_xuw : ¬ Collinear3 x u w := fan_not_collinear hfan hw_mem.1
  have hxu : x ≠ u := by
    intro h
    exact hnc_xuw (by rw [h]; exact collinear3_of_eq rfl)
  have hy_span : y ∈ affineSpan ℝ ({x, u} : Set V3) :=
    aff_ge_1_1_subset_aff_fan y x u hxu hyge
  have hnc_xuz : ¬ Collinear3 x u z :=
    permutes_4points_collinear x y u z (Ne.symm hyx) hxu hy_span hnc_xyz
  have hne_azim_z_w : azim x u z w ≠ 0 :=
    not_azim_points_in_yfan x V E U y z u
      hfan hcard hfan80 hU hz hu hyge hyxfan hyx hconn w hw_mem
  have hpos : 0 < azim x u w z := by
    rcases lt_or_eq_of_le (azim_nonneg x u w z) with h | h
    · exact h
    · exfalso
      exact hne_azim_z_w
        (azim_compl_eq_zero (z := x) (w := u) (w1 := w) (w2 := z)
          hnc_xuw hnc_xuz h.symm)
  have hne_singleton : setOfEdge u V E ≠ {w} := by
    intro h
    have h1 : (setOfEdge u V E).ncard = 1 := by rw [h, Set.ncard_singleton]
    omega
  obtain ⟨hwσ_mem, hwσ_ne_w, hwσ_min⟩ :=
    SIGMA_FAN hne_singleton hfan hw_mem
  have hnc_xuwσ : ¬ Collinear3 x u (sigmaFan x V E u w) :=
    fan_not_collinear hfan hwσ_mem.1
  have hne_azim_z_σ : azim x u z (sigmaFan x V E u w) ≠ 0 :=
    not_azim_points_in_yfan x V E U y z u
      hfan hcard hfan80 hU hz hu hyge hyxfan hyx hconn
      (sigmaFan x V E u w) hwσ_mem
  have hle : azim x u z (sigmaFan x V E u w) ≤ azim x u z w := by
    have h := hw_min (sigmaFan x V E u w) hwσ_mem
    unfold azim1 at h
    linarith
  have hsum4 : azim x u z w
      = azim x u z (sigmaFan x V E u w) + azim x u (sigmaFan x V E u w) w :=
    sum4_azim_fan (Ne.symm hxu) hnc_xuz hnc_xuwσ hnc_xuw hle
  have hpos_azim_z_σ : 0 < azim x u z (sigmaFan x V E u w) :=
    lt_of_le_of_ne (azim_nonneg x u z (sigmaFan x V E u w))
      (Ne.symm hne_azim_z_σ)
  have hne_azim_σw : azim x u (sigmaFan x V E u w) w ≠ 0 := by
    intro h0
    exact hwσ_ne_w (unique_azim0_point_fan hfan hwσ_mem.1 hw_mem.1 h0)
  have hlt : azim x u w z < azim x u w (sigmaFan x V E u w) := by
    have hcompl_z : azim x u w z = 2 * Real.pi - azim x u z w := by
      rw [azim_compl (z := x) (w := u) (w1 := z) (w2 := w)
        hnc_xuz hnc_xuw, if_neg hne_azim_z_w]
    have hcompl_σ : azim x u w (sigmaFan x V E u w)
        = 2 * Real.pi - azim x u (sigmaFan x V E u w) w := by
      rw [azim_compl (z := x) (w := u) (w1 := sigmaFan x V E u w) (w2 := w)
        hnc_xuwσ hnc_xuw, if_neg hne_azim_σw]
    have hlt_aux : azim x u (sigmaFan x V E u w) w < azim x u z w := by
      linarith [hsum4, hpos_azim_z_σ]
    rw [hcompl_z, hcompl_σ]
    linarith
  have hwdart : wDartFan x V E (x, u, w, sigmaFan x V E u w)
      = wedge x u w (sigmaFan x V E u w) := by
    unfold wDartFan
    rw [if_pos hcard_u]
  rw [hwdart]
  exact ⟨hnc_xuz, hpos, hlt⟩

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
  have huV : u ∈ V := (fan_mem_of_edge hfan huw).1
  have hcardu : 1 < (setOfEdge u V E).ncard := hcard u huV
  have hwd : wDartFan x V E (x, u, w, sigmaFan x V E u w)
      = wedge x u w (sigmaFan x V E u w) := by
    unfold wDartFan
    rw [if_pos hcardu]
  rw [hwd] at hy
  rw [hwd]
  obtain ⟨hnc_uy, h0y, hy_lt⟩ := hy
  have hnc_uw : ¬ Collinear3 x u w := fan_not_collinear hfan huw
  intro z hz
  have hsplit : z ∈ affGt {x, u} {y} ∩ affGt {x, y} {u} := by
    rw [← aff_gt_inter_aff_gt hnc_uy]
    exact hz
  have hncz : ¬ Collinear3 x u z := aff_gt_imp_not_collinear hnc_uy hsplit.1
  have heq : azim x u w z = azim x u w y :=
    (azim_eq_azim_iff_alt hnc_uw hncz hnc_uy).mpr hsplit.1
  exact ⟨hncz, by rw [heq]; exact h0y, by rw [heq]; exact hy_lt⟩

/-! ## rcone 与 aff_gt 的非空交（planarity.hl:12464-12573） -/

/-- 叉积为零推出共线（`collinear3_of_cross_eq_zero` 的本地副本）。 -/
private theorem collinear3_of_cross_eq_zero_a9 {x v u : V3}
    (h : crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ) = 0) :
    Collinear3 x v u := by
  by_cases hvx : v = x
  · rw [hvx]
    exact collinear3_of_eq rfl
  · have hp : ((v - x : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro h0
      apply hvx
      exact sub_eq_zero.mp ((WithLp.ofLp_eq_zero 2).mp h0)
    have h0 : crossProduct ((v - x : V3) : Fin 3 → ℝ)
        (crossProduct ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)) = 0 := by
      rw [h]
      exact map_zero _
    have h1 := cross_cross_eq_smul_sub_smul' ((v - x : V3) : Fin 3 → ℝ)
      ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)
    rw [h0] at h1
    have h2 : (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) •
        ((v - x : V3) : Fin 3 → ℝ) =
        (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) •
          ((u - x : V3) : Fin 3 → ℝ) :=
      sub_eq_zero.mp h1.symm
    have hpp : ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ) ≠ 0 := by
      intro h1'
      apply hp
      funext i
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_self_nonneg (((v - x : V3) : Fin 3 → ℝ) j))).mp h1'
      exact mul_self_eq_zero.mp (h3 i (Finset.mem_univ i))
    have hqe : ((u - x : V3) : Fin 3 → ℝ)
        = ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) /
          (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))) •
          ((v - x : V3) : Fin 3 → ℝ) := by
      calc ((u - x : V3) : Fin 3 → ℝ)
          = (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))⁻¹ •
              ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) •
                ((u - x : V3) : Fin 3 → ℝ)) := by
            rw [smul_smul, inv_mul_cancel₀ hpp, one_smul]
        _ = (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))⁻¹ •
              ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) •
                ((v - x : V3) : Fin 3 → ℝ)) := by rw [h2]
        _ = ((((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) /
              (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ))) •
              ((v - x : V3) : Fin 3 → ℝ) := by
            rw [smul_smul, div_eq_inv_mul, mul_comm]
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
        c = (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((u - x : V3) : Fin 3 → ℝ)) /
          (((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((v - x : V3) : Fin 3 → ℝ)) := ⟨_, rfl⟩
    have hqec : ((u - x : V3) : Fin 3 → ℝ) = c • ((v - x : V3) : Fin 3 → ℝ) := by
      rw [hcdef]
      exact hqe
    have hqV : (u - x : V3) = c • (v - x : V3) := by
      have hc := congrArg (WithLp.toLp 2) hqec
      rwa [WithLp.toLp_ofLp, WithLp.toLp_smul, WithLp.toLp_ofLp] at hc
    rw [collinear3_iff_mem_affineSpan (Ne.symm hvx), affine_hull_2_fan]
    refine ⟨1 - c, c, by ring, ?_⟩
    calc u = (u - x) + x := by module
      _ = c • (v - x) + x := by rw [hqV]
      _ = (1 - c) • x + c • v := by module

/-- 非共线 ⇒ 叉积范数为正（`cross_pos_of_not_collinear3_anc` 的本地副本）。 -/
private theorem cross_pos_of_not_collinear3_a9 {x v u : V3}
    (hnc : ¬ Collinear3 x v u) :
    0 < ‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ := by
  have hzne : (WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((u - x : V3) : Fin 3 → ℝ)) : V3) ≠ 0 := by
    intro h0
    apply hnc
    have hcoe := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) h0
    simp only [WithLp.ofLp_zero] at hcoe
    exact collinear3_of_cross_eq_zero_a9 hcoe
  exact norm_pos_iff.mpr hzne

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
  have hvx : v ≠ x := fun he => hnc (collinear3_of_eq (v := x) (w := v) (w1 := u) he)
  have hnv : ‖v - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hvx)
  have hnvpos : 0 < ‖v - x‖ := lt_of_le_of_ne (norm_nonneg _) fun h => hnv h.symm
  have haxf : (v - x : V3) = ‖v - x‖ • e3Fan x v u := by
    rw [e3Fan, smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have he1s : e1Fan x v u ⬝ᵥ e1Fan x v u = 1 := e1Fan_dot_self hnc
  have he3s : e3Fan x v u ⬝ᵥ e3Fan x v u = 1 := e3Fan_dot_self hvx u
  have he1d3 : e1Fan x v u ⬝ᵥ e3Fan x v u = 0 := e1Fan_dot_e3 hnc
  have he1vx : inner ℝ (e1Fan x v u) (v - x) = 0 := by
    conv_lhs => rw [haxf]
    rw [real_inner_smul_right, inner_eq_dot, he1d3, mul_zero]
  have he3vx : inner ℝ (e3Fan x v u) (v - x) = ‖v - x‖ := by
    conv_lhs => rw [haxf]
    rw [real_inner_smul_right, inner_eq_dot, he3s, mul_one]
  -- 通用 rcone 成员：标架点 `sin s1 • e1 + cos s1 • e3 + x`（`s1 < π/2`）
  have hrcone : ∀ s1 : ℝ, 0 < s1 → s1 < h → s1 < Real.pi / 2 →
      Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u + x ∈
        rconeFan x v (Real.cos h) := by
    intro s1 hs1pos hs1h hs1pi
    have hsin : 0 < Real.sin s1 :=
      Real.sin_pos_of_pos_of_lt_pi hs1pos (by linarith [hs1pi, Real.pi_pos])
    have hcos1 : 0 < Real.cos s1 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hs1pi⟩
    have hcoslt : Real.cos h < Real.cos s1 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hs1pos) hhpi hs1h
    set w : V3 := Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u + x with hwdef
    have hwxs : w - x = Real.sin s1 • e1Fan x v u + Real.cos s1 • e3Fan x v u := by
      rw [hwdef]; module
    have he1n : ‖e1Fan x v u‖ = 1 := by
      have h : ‖e1Fan x v u‖ ^ 2 = 1 := by
        rw [norm_sq_eq_dot]; exact he1s
      nlinarith [h, norm_nonneg (e1Fan x v u), sq_nonneg (‖e1Fan x v u‖ - 1)]
    have he3n : ‖e3Fan x v u‖ = 1 := by
      have h : ‖e3Fan x v u‖ ^ 2 = 1 := by
        rw [norm_sq_eq_dot]; exact he3s
      nlinarith [h, norm_nonneg (e3Fan x v u), sq_nonneg (‖e3Fan x v u‖ - 1)]
    have hnw : ‖w - x‖ = 1 := by
      have h2 : ‖w - x‖ ^ 2 = 1 := by
        conv_lhs => rw [hwxs, norm_add_sq_real, norm_smul, norm_smul,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsin, abs_of_pos hcos1,
          he1n, he3n, real_inner_smul_left, real_inner_smul_right, inner_eq_dot,
          he1d3]
        have hsc := Real.sin_sq_add_cos_sq s1
        rw [sq, sq] at hsc
        linarith
      nlinarith [h2, norm_nonneg (w - x), sq_nonneg (‖w - x‖ - 1)]
    have hdot : (w - x) ⬝ᵥ (v - x) = Real.cos s1 * ‖v - x‖ := by
      rw [← inner_eq_dot, hwxs, inner_add_left, real_inner_smul_left,
        real_inner_smul_left]
      change Real.sin s1 * inner ℝ (e1Fan x v u) (v - x) +
        Real.cos s1 * inner ℝ (e3Fan x v u) (v - x) = Real.cos s1 * ‖v - x‖
      rw [he1vx, he3vx]
      ring
    show (w - x) ⬝ᵥ (v - x) > dist w x * dist v x * Real.cos h
    rw [hdot, dist_eq_norm, dist_eq_norm, hnw, one_mul]
    have hstep : (Real.cos s1 - Real.cos h) * ‖v - x‖ > 0 :=
      mul_pos (sub_pos.mpr hcoslt) hnvpos
    have hstep2 : Real.cos s1 * ‖v - x‖ - ‖v - x‖ * Real.cos h
        = (Real.cos s1 - Real.cos h) * ‖v - x‖ := by ring
    linarith
  rcases lt_or_ge 0 ((v - x) ⬝ᵥ (u - x)) with hd | hle
  · -- 正支：s1 = min h (atn (|cross|/dot)) / 2
    set A : ℝ := Real.arctan (‖(WithLp.toLp 2 (crossProduct ((v - x : V3) : Fin 3 → ℝ)
        ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ * ((v - x) ⬝ᵥ (u - x))⁻¹) with hAdef
    have hApos : 0 < A := by
      rw [hAdef]
      exact Real.arctan_pos.mpr (mul_pos (cross_pos_of_not_collinear3_a9 hnc) (inv_pos.mpr hd))
    have hApi : A < Real.pi / 2 := by
      rw [hAdef]; exact (Real.arctan_mem_Ioo _).2
    have hs1pos : 0 < min h A / 2 := div_pos (lt_min hh0 hApos) two_pos
    have hs1h : min h A / 2 < h := by linarith [min_le_left h A, hh0]
    have hs1pi : min h A / 2 < Real.pi / 2 := by linarith [min_le_right h A, hApi]
    have hs1A : min h A / 2 < Real.arctan (‖(WithLp.toLp 2 (crossProduct
        ((v - x : V3) : Fin 3 → ℝ) ((u - x : V3) : Fin 3 → ℝ)) : V3)‖ *
        ((v - x) ⬝ᵥ (u - x))⁻¹) := by
      rw [← hAdef]; linarith [min_le_right h A, hApos]
    exact Set.Nonempty.ne_empty
      ⟨_, hrcone _ hs1pos hs1h hs1pi,
        condition_to_in_aff_gt_by_angle hnc hd hs1pos hs1A⟩
  · -- 非正支：s1 = min h (π/2) / 2
    have hs1pos : 0 < min h (Real.pi / 2) / 2 :=
      div_pos (lt_min hh0 (by linarith [Real.pi_pos])) two_pos
    have hs1h : min h (Real.pi / 2) / 2 < h := by
      linarith [min_le_left h (Real.pi / 2), hh0]
    have hs1pi : min h (Real.pi / 2) / 2 < Real.pi / 2 := by
      linarith [min_le_right h (Real.pi / 2), Real.pi_pos]
    exact Set.Nonempty.ne_empty
      ⟨_, hrcone _ hs1pos hs1h hs1pi,
        condition1_to_in_aff_gt_by_angle hnc hs1pos hs1pi hle⟩

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
  have hsub : affGt {x} {v, z} ⊆ wDartFan x V E (x, v, u, sigmaFan x V E v u) :=
    aff_gt_in_w_dart_fan x V E v u z hfan hvu hz hfan80 hcard
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr
    (not_empty_rcone_fan_inter_aff_gt x v z h hnc hh0 hhpi)
  exact Set.Nonempty.ne_empty ⟨p, by
    rw [rwDartFan]
    exact ⟨⟨hsub hp.2, hp.1⟩, hp.2⟩⟩

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
