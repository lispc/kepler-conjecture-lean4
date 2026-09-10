/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18h.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18h of block 18, planarity.hl:11111-11438): the
edge-insertion / fan-preservation layer
- `RWXUYZZ` (11111)
- `add_edge_graph_fan` (11124)
- `graph_add_edge_is_graph` (11138)
- `add_edge_into_collinear_fan` (11151)
- `condition_not_edge_fan` (11168)
- `properties_edges_eq_fan` (11211)
- `condition_not_intersection_fan` (11226)
- `exists_edge_fully_surround_fan` (11295)
- `condition_not_intersection_point_fan` (11310)
- `DWWUTKW` (11377)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings)
designed by glm-5.3, proofs filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean, the face-set hypothesis
  `ds IN face_set(hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with `ds : Set (V3 × V3)`
  (pair darts) and `pr2 y`/`pr3 y` as `y.1`/`y.2`.
- HOL `UNIONS E` ↔ `⋃₀ E`; `E UNION {{v,u}}` ↔ `E ∪ {{v, u}}`.
- HOL `graph E` ↔ `Graph E` (Kepler/Text/Fan.lean:37). HOL's `graph` is
  polymorphic in `A`; the repo `Graph` is `V3`-specific, so
  `graph_add_edge_is_graph` is stated for `V3` (fidelity gap noted).
- HOL `CARD e = 2` ↔ `e.ncard = 2` (repo convention, cf.
  Kepler/Text/PlanarityComponent.lean:49).
- HOL `collinear ({x} UNION e)` ↔ `Collinear ℝ (insert x e)` (the form
  used by `fan6`, Kepler/Text/Fan.lean:46).
- HOL `~collinear {x,v,u}` ↔ `¬ Collinear3 x v u`
  (Kepler/Geom/Azim.lean:43).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348).
- HOL `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179).
- `RWXUYZZ` (11111) is exactly the conjunction of the already-ported
  `exists_dartset_leads_into_fan` (PlanarityComponent.lean:283) and
  `dartset_leads_into_is_topological_component_yfan`
  (PlanarityComponent.lean:535); kept as a separate statement for HOL
  name fidelity.
-/

import Kepler.Text.PlanarityComponent

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## RWXUYZZ（planarity.hl:11111-11122） -/

/-- HOL planarity.hl :11111-11122 `RWXUYZZ`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds:real^3#real^3#real^3#real^3->bool.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==>
(?s:real^3->bool. !y. y IN ds==> s= dart_leads_into x V E (pr2 y) (pr3 y))
/\ dartset_leads_into_fan x V E ds IN topological_component_yfan (x,V,E)
```

证明思路：两个合取项分别是本仓库已移植的
`exists_dartset_leads_into_fan`（给出 ∃s）与
`dartset_leads_into_is_topological_component_yfan`（给出分量归属），
直接 `⟨..., ...⟩` 组装即可。HOL 证明即
`MESON_TAC[dartset_leads_into_is_topological_component_yfan;
exists_dartset_leads_into_fan]`。

候选已有引理：
- `exists_dartset_leads_into_fan`
  （Kepler/Text/PlanarityComponent.lean:283）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535） -/
theorem RWXUYZZ {x : V3} {V : Set V3} {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    (∃ s : Set V3, ∀ y ∈ ds, s = dartLeadsInto x V E y.1 y.2) ∧
      dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E := by
  exact ⟨exists_dartset_leads_into_fan hfan hcard hfan80 hds,
    dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds⟩

/-! ## 加边保持图/扇性质（planarity.hl:11124-11224） -/

/-- HOL planarity.hl :11124-11136 `add_edge_graph_fan`

HOL 原文：
```
!(V:A->bool) (E:(A->bool)->bool) v:A u:A.
 v IN V /\ u IN V /\ E1=E UNION {{v,u}} /\ UNIONS E SUBSET V==> UNIONS E1 SUBSET V
```

证明思路：`E1 = E ∪ {{v,u}}` 代入，`⋃₀ (E ∪ {{v,u}}) = ⋃₀ E ∪ {v,u}`
（`Set.sUnion_union` + `Set.sUnion_pair`/`Set.sUnion_singleton`），
再由 `v ∈ V`、`u ∈ V`、`⋃₀ E ⊆ V` 逐点证。

候选已有引理：
- `Set.sUnion_union`（Mathlib/Data/Set/Lattice.lean:897）
- `Set.sUnion_pair`（Mathlib/Data/Set/Lattice.lean:925）
- `Set.sUnion_singleton`（Mathlib/Data/Set/Lattice.lean:853） -/
theorem add_edge_graph_fan {A : Type*} {V : Set A} {E : Set (Set A)} {v u : A}
    (E1 : Set (Set A)) (hv : v ∈ V) (hu : u ∈ V)
    (hE1 : E1 = E ∪ {{v, u}}) (hU : ⋃₀ E ⊆ V) :
    ⋃₀ E1 ⊆ V := by
  intro x hx
  rw [hE1, Set.sUnion_union, Set.sUnion_singleton] at hx
  rcases hx with hx | hx
  · exact hU hx
  · rcases hx with rfl | rfl
    · exact hv
    · exact hu

/-- HOL planarity.hl :11138-11149 `graph_add_edge_is_graph`

HOL 原文：
```
!E1 (E:(A->bool)->bool) v:A u:A.
 E1=E UNION {{v,u}} /\ ~(v=u) /\ graph E==> graph E1
```

证明思路：对 `E1` 的每条边分类：旧边由 `Graph E` 给出；
新边 `{v,u}` 由 `v ≠ u` 及 `CARD_2_FAN`/`Set.ncard_pair` 给出两点基数。

编码差距：HOL 的 `graph` 对任意类型 `A` 多态，本仓库 `Graph`
（Kepler/Text/Fan.lean:37）仅定义在 `V3` 上，故此处理论上应为 `V3` 版本。

候选已有引理：
- `Graph`（Kepler/Text/Fan.lean:37）
- `GRAPH`（Kepler/Text/Planarity.lean:4965）
- `CARD_2_FAN`（Kepler/Text/Planarity.lean:4975）
- `Set.ncard_pair`（Mathlib/Data/Set/Card.lean:746） -/
theorem graph_add_edge_is_graph {E E1 : Set (Set V3)} {v u : V3}
    (hE1 : E1 = E ∪ {{v, u}}) (hvu : v ≠ u) (hgraph : Graph E) :
    Graph E1 := by
  intro e he
  rw [hE1, Set.mem_union, Set.mem_singleton_iff] at he
  rcases he with he | rfl
  · exact hgraph e he
  · refine ⟨(Set.finite_singleton u).insert v, ?_⟩
    rw [← Set.ncard_eq_toFinset_card ({v, u} : Set V3) ((Set.finite_singleton u).insert v),
      CARD_2_FAN hvu]

/-- HOL planarity.hl :11151-11166 `add_edge_into_collinear_fan`

HOL 原文：
```
!x:real^3 (E:(real^3->bool)->bool) v:real^3 u:real^3.
~collinear {x,v,u} /\
(!e. e IN E ==> ~collinear ({x} UNION e))
==>
(!e. e IN E UNION {{v, u}} ==> ~collinear ({x} UNION e))
```

证明思路：对 `e ∈ E ∪ {{v,u}}` 分类：`e ∈ E` 用第二假设；
`e = {v,u}` 时 `insert x e = {x,v,u}`，用 `~collinear {x,v,u}`。
（HOL 用 `SET_RULE {X} UNION {A,B}={X,A,B}`。）

候选已有引理：
- `fan6`（Kepler/Text/Fan.lean:46，`¬ Collinear ℝ (insert x e)` 形式）
- `Collinear3`（Kepler/Geom/Azim.lean:43） -/
theorem add_edge_into_collinear_fan {x v u : V3} {E : Set (Set V3)}
    (hnc : ¬ Collinear3 x v u)
    (hE : ∀ e ∈ E, ¬ Collinear ℝ (insert x e)) :
    ∀ e ∈ E ∪ {{v, u}}, ¬ Collinear ℝ (insert x e) := by
  intro e he
  rw [Set.mem_union, Set.mem_singleton_iff] at he
  rcases he with he | rfl
  · exact hE e he
  · simpa [Collinear3] using hnc

/-! ## 条件：新边不与 face dartset 相交（planarity.hl:11168-11293） -/

/-- HOL planarity.hl :11168-11209 `condition_not_edge_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 ds.
FAN(x,V,E) /\ v IN V /\ u IN V /\ ~collinear {x,v,u}
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ e1 IN E /\ e2 = {v, u}
/\ aff_gt {x} {v,u} SUBSET dartset_leads_into_fan x V E ds
==> ~(e1=e2)
```

证明思路：反设 `e1 = e2 = {v,u}`。由
`aff_ge_eq_aff_gt_union_aff_ge` 得 `aff_ge {x} {v,u}` 包含
`aff_gt {x} {v,u}`；`dartset_leads_into_subset_yfan` 把 dartset 放入
`yfan`，故 `aff_gt {x} {v,u} ∩ xfan = ∅`。但 `e1 ∈ E` 给出
`aff_ge {x} e1 ⊆ xfan`，而 `exists_in_aff_gt` 提供
`aff_gt {x} {v,u}` 的非空点，矛盾。

候选已有引理：
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `dartset_leads_into_subset_yfan`
  （Kepler/Text/PlanarityComponent.lean:583）
- `exists_in_aff_gt`（Kepler/Text/PlanarityNotCut.lean:1847）
- `xfan`（Kepler/Text/Fan.lean:154）、`yfan`（Kepler/Text/Fan.lean:158） -/
theorem condition_not_edge_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {v u : V3} {ds : Set (V3 × V3)} {e1 e2 : Set V3}
    (hfan : FAN x V E) (hv : v ∈ V) (hu : u ∈ V) (hnc : ¬ Collinear3 x v u)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (he1 : e1 ∈ E) (he2 : e2 = {v, u})
    (hsub : affGt {x} {v, u} ⊆ dartsetLeadsIntoFan x V E ds) :
    e1 ≠ e2 := by
  intro heq
  rw [he2] at heq
  obtain ⟨y, hy⟩ := exists_in_aff_gt hnc
  have hy' : y ∈ affGe {x} {v, u} := by
    rw [aff_ge_eq_aff_gt_union_aff_ge hnc]
    exact Set.mem_union_left _ (Set.mem_union_left _ hy)
  have hyx : y ∈ xfan x V E := ⟨e1, he1, by rw [heq]; exact hy'⟩
  have hysub := dartset_leads_into_subset_yfan hfan hcard hfan80 hds
  have hyy : y ∈ yfan x V E := hysub (hsub hy)
  rw [yfan, Set.mem_sdiff] at hyy
  exact hyy.2 hyx

/-- HOL planarity.hl :11211-11224 `properties_edges_eq_fan`

HOL 原文：
```
!e:A-> bool v:A u:A.
FINITE e /\ ~(e={v,u}) /\ ~(v=u)  /\ CARD e=2  ==>  ~(v IN e)\/ ~(u IN e)
```

证明思路：反设 `v ∈ e ∧ u ∈ e`，则 `{v,u} ⊆ e`；由 `v ≠ u` 得
`CARD {v,u} = 2`，与 `CARD e = 2` 及 `e` 有限合起来用
`Set.eq_of_subset_of_ncard_le` 得 `e = {v,u}`，与 `~(e={v,u})` 矛盾。

候选已有引理：
- `Set.ncard_pair`（Mathlib/Data/Set/Card.lean:746）
- `Set.eq_of_subset_of_ncard_le`（Mathlib/Data/Set/Card.lean:862）
- `CARD_2_FAN`（Kepler/Text/Planarity.lean:4975） -/
theorem properties_edges_eq_fan {A : Type*} {e : Set A} {v u : A}
    (hfin : e.Finite) (hne : e ≠ {v, u}) (hvu : v ≠ u) (hcard : e.ncard = 2) :
    v ∉ e ∨ u ∉ e := by
  by_contra h
  push Not at h
  obtain ⟨hve, hue⟩ := h
  have hsub : ({v, u} : Set A) ⊆ e := by
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hve
    · exact hue
  have hpair : ({v, u} : Set A).ncard = 2 := Set.ncard_pair hvu
  have heq : ({v, u} : Set A) = e :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hpair]) hfin
  exact hne heq.symm

/-- `affGe {x} S ⊆ affGe {x} T`（`S ⊆ T`，`{x} ∪ T` 有限，`x ∉ T`）。
移植自 `Kepler/Text/Planarity.lean` 的私有 `affGe_mono_right`。 -/
private theorem affGe_mono_right' {x : V3} {S T : Set V3} (hST : S ⊆ T)
    (hfin : ({x} ∪ T : Set V3).Finite) (hxT : x ∉ T) :
    affGe {x} S ⊆ affGe {x} T := by
  intro y hy
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hy ⊢
  obtain ⟨f, hS, hyv, hpos, hsum⟩ := hy
  have hsub : ({x} ∪ S : Set V3) ⊆ {x} ∪ T := by
    intro z hz
    simp only [Set.mem_union] at hz ⊢
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (hST h)
  have hsubfin : hS.toFinset ⊆ hfin.toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz ⊢
    exact hsub hz
  have hgv0 : ∀ z ∈ hfin.toFinset, z ∉ hS.toFinset →
      (if z ∈ ({x} ∪ S : Set V3) then f z else 0) = 0 := by
    intro z hz hzs
    exact if_neg (fun hcon => hzs (by
      simp only [Set.Finite.mem_toFinset]
      exact hcon))
  have hgvv : ∀ z ∈ hfin.toFinset, z ∉ hS.toFinset →
      (if z ∈ ({x} ∪ S : Set V3) then f z else 0) • z = 0 := by
    intro z hz hzs
    rw [hgv0 z hz hzs, zero_smul]
  refine ⟨fun z => if z ∈ ({x} ∪ S : Set V3) then f z else 0, hfin, ?_, ?_, ?_⟩
  · show y = ∑ z ∈ hfin.toFinset, (if z ∈ ({x} ∪ S : Set V3) then f z else 0) • z
    rw [hyv, ← Finset.sum_subset hsubfin hgvv]
    exact Finset.sum_congr rfl
      (fun z hz => by
        simp only [Set.Finite.mem_toFinset] at hz
        rw [if_pos hz])
  · intro z hzT
    show 0 ≤ (if z ∈ ({x} ∪ S : Set V3) then f z else 0)
    by_cases hzS : z ∈ ({x} ∪ S : Set V3)
    · rw [if_pos hzS]
      simp only [Set.mem_union] at hzS
      rcases hzS with h | h
      · exact (hxT ((Set.mem_singleton_iff.mp h) ▸ hzT)).elim
      · exact hpos z h
    · rw [if_neg hzS]
  · show ∑ z ∈ hfin.toFinset, (if z ∈ ({x} ∪ S : Set V3) then f z else 0) = 1
    rw [← hsum, ← Finset.sum_subset hsubfin hgv0]
    exact Finset.sum_congr rfl (fun z hz => by
      simp only [Set.Finite.mem_toFinset] at hz
      rw [if_pos hz])

/-- HOL planarity.hl :11226-11293 `condition_not_intersection_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 ds e1:real^3->bool e2:real^3->bool.
FAN(x,V,E) /\ v IN V /\ u IN V /\ ~collinear {x,v,u}
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ aff_gt {x} {v,u} SUBSET dartset_leads_into_fan x V E ds
/\ e1 IN E /\ e2 = {v, u}
==>aff_ge {x} e1 INTER aff_ge {x} e2 = aff_ge {x} (e1 INTER e2)
```

证明思路：HOL 路线：`aff_ge_eq_aff_gt_union_aff_ge` 展开
`aff_ge {x} {v,u}`；`dartset_leads_into_subset_yfan` 得
`aff_gt {x} {v,u} ∩ xfan = ∅`；又 `aff_ge {x} e1 ⊆ xfan`
（`e1 ∈ E`）。于是 `aff_ge {x} e1` 与 `aff_ge {x} {v,u}` 的交只能落在
`aff_ge {x} {v} ∪ aff_ge {x} {u}` 上；再由 `properties_edges_eq_fan`
与 `fan7` 的分配律，将交化为 `aff_ge {x} (e1 ∩ e2)`。

候选已有引理：
- `fan7`（Kepler/Text/Fan.lean:51，HOL `fan7` 分配律）
- `condition_not_edge_fan`（本文件上文）
- `properties_edges_eq_fan`（本文件上文）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `dartset_leads_into_subset_yfan`
  （Kepler/Text/PlanarityComponent.lean:583） -/
theorem condition_not_intersection_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {v u : V3} {ds : Set (V3 × V3)} {e1 e2 : Set V3}
    (hfan : FAN x V E) (hv : v ∈ V) (hu : u ∈ V) (hnc : ¬ Collinear3 x v u)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hsub : affGt {x} {v, u} ⊆ dartsetLeadsIntoFan x V E ds)
    (he1 : e1 ∈ E) (he2 : e2 = {v, u}) :
    affGe {x} e1 ∩ affGe {x} e2 = affGe {x} (e1 ∩ e2) := by
  subst he2
  have hgraph : Graph E := hfan.2.1
  obtain ⟨hfin1, hcard_fin⟩ := hgraph e1 he1
  have hcard1 : e1.ncard = 2 := by
    rw [Set.ncard_eq_toFinset_card e1 hfin1]
    exact hcard_fin
  have hvu : v ≠ u := fun h =>
    hnc (by rw [h]; exact collinear3_pair_right (v0 := x) (v1 := u) rfl)
  have hxv : x ≠ v := fun h =>
    hnc (by rw [h]; exact collinear3_of_eq rfl)
  have hxu : x ≠ u := fun h =>
    hnc (by rw [h]; exact collinear3_pair_left rfl)
  have hne : e1 ≠ ({v, u} : Set V3) :=
    condition_not_edge_fan hfan hv hu hnc hcard hfan80 hds he1 rfl hsub
  have hprop := properties_edges_eq_fan hfin1 hne hvu hcard1
  have h77 := aff_ge_eq_aff_gt_union_aff_ge (x := x) (v := v) (w := u) hnc
  have hyfan := dartset_leads_into_subset_yfan hfan hcard hfan80 hds
  have hgt_yfan : affGt {x} {v, u} ⊆ yfan x V E :=
    fun y hy => hyfan (hsub hy)
  have hgt_xfan : affGt {x} {v, u} ∩ xfan x V E = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨hygt, hyx⟩ := hy
    have hyy := hgt_yfan hygt
    rw [yfan, Set.mem_sdiff] at hyy
    exact hyy.2 hyx
  have he1_xfan : affGe {x} e1 ⊆ xfan x V E := fun y hy => ⟨e1, he1, hy⟩
  have hgt_e1_disj : affGe {x} e1 ∩ affGt {x} {v, u} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨hyA, hyG⟩ := hy
    have hmem : y ∈ affGt {x} {v, u} ∩ xfan x V E := ⟨hyG, he1_xfan hyA⟩
    rw [hgt_xfan] at hmem
    exact hmem
  have hfan7 := hfan.2.2.2.2.2
  have h7v : affGe {x} e1 ∩ affGe {x} {v} = affGe {x} (e1 ∩ {v}) :=
    hfan7 e1 (Or.inl he1) ({v} : Set V3) (Or.inr ⟨v, hv, rfl⟩)
  have h7u : affGe {x} e1 ∩ affGe {x} {u} = affGe {x} (e1 ∩ {u}) :=
    hfan7 e1 (Or.inl he1) ({u} : Set V3) (Or.inr ⟨u, hu, rfl⟩)
  have hfin_u : ({x} ∪ (e1 ∩ ({u} : Set V3)) : Set V3).Finite :=
    (Set.finite_singleton x).union (hfin1.subset Set.inter_subset_left)
  have hfin_v : ({x} ∪ (e1 ∩ ({v} : Set V3)) : Set V3).Finite :=
    (Set.finite_singleton x).union (hfin1.subset Set.inter_subset_left)
  have hx_u : x ∉ e1 ∩ ({u} : Set V3) := by
    intro hx
    obtain ⟨_, hx2⟩ := (Set.mem_inter_iff x _ _).mp hx
    exact hxu (Set.mem_singleton_iff.mp hx2)
  have hx_v : x ∉ e1 ∩ ({v} : Set V3) := by
    intro hx
    obtain ⟨_, hx2⟩ := (Set.mem_inter_iff x _ _).mp hx
    exact hxv (Set.mem_singleton_iff.mp hx2)
  rw [h77]
  have hdist : affGe {x} e1 ∩
        (affGt {x} {v, u} ∪ affGe {x} {v} ∪ affGe {x} {u})
      = affGe {x} (e1 ∩ {v}) ∪ affGe {x} (e1 ∩ {u}) := by
    rw [Set.inter_union_distrib_left, Set.inter_union_distrib_left,
      hgt_e1_disj, h7v, h7u]
    simp
  rw [hdist]
  rcases hprop with hvnot | hunot
  · have hveq : e1 ∩ ({v} : Set V3) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hz1, hz2⟩ := (Set.mem_inter_iff z _ _).mp hz
      exact hvnot (Set.mem_singleton_iff.mp hz2 ▸ hz1)
    have hveq2 : e1 ∩ ({v, u} : Set V3) = e1 ∩ ({u} : Set V3) := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hz2⟩ := (Set.mem_inter_iff z _ _).mp hz
        rcases Set.mem_insert_iff.mp hz2 with h | h
        · exact absurd (h ▸ hz1) hvnot
        · exact (Set.mem_inter_iff z _ _).mpr ⟨hz1, h⟩
      · intro hz
        obtain ⟨hz1, hz2⟩ := (Set.mem_inter_iff z _ _).mp hz
        exact (Set.mem_inter_iff z _ _).mpr ⟨hz1, Set.mem_insert_of_mem v hz2⟩
    rw [hveq, hveq2]
    exact Set.union_eq_right.mpr
      (affGe_mono_right' (Set.empty_subset _) hfin_u hx_u)
  · have hueq : e1 ∩ ({u} : Set V3) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      obtain ⟨hz1, hz2⟩ := (Set.mem_inter_iff z _ _).mp hz
      exact hunot (Set.mem_singleton_iff.mp hz2 ▸ hz1)
    have hueq2 : e1 ∩ ({v, u} : Set V3) = e1 ∩ ({v} : Set V3) := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz1, hz2⟩ := (Set.mem_inter_iff z _ _).mp hz
        rcases Set.mem_insert_iff.mp hz2 with h | h
        · exact (Set.mem_inter_iff z _ _).mpr ⟨hz1, Set.mem_singleton_iff.mpr h⟩
        · exact absurd (h ▸ hz1) hunot
      · intro hz
        obtain ⟨hz1, hz2⟩ := (Set.mem_inter_iff z _ _).mp hz
        exact (Set.mem_inter_iff z _ _).mpr
          ⟨hz1, Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hz2))⟩
    rw [hueq, hueq2]
    exact Set.union_eq_left.mpr
      (affGe_mono_right' (Set.empty_subset _) hfin_v hx_v)

/-! ## 完全环绕边与点相交（planarity.hl:11295-11375） -/

/-- HOL planarity.hl :11295-11308 `exists_edge_fully_surround_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) w:real^3.
FAN(x,V,E) /\ w IN V
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
==> ?v. {w,v} IN E /\ v IN V
```

证明思路：由 `w ∈ V` 得 `CARD (set_of_edge w V E) > 1 > 0`，
故 `setOfEdge w V E ≠ ∅`；取 `v ∈ setOfEdge w V E`，
按 `setOfEdge` 定义即 `{w,v} ∈ E` 且 `v ∈ V`。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.ncard_pos`（Mathlib/Data/Set/Card.lean:679）
- `Set.nonempty_iff_ne_empty`（Mathlib/Data/Set/Basic.lean:434） -/
theorem exists_edge_fully_surround_fan {x w : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hw : w ∈ V)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard) :
    ∃ v : V3, {w, v} ∈ E ∧ v ∈ V := by
  have hVfin : V.Finite := hfan.2.2.1.1
  have hfin : (setOfEdge w V E).Finite := remark_finite_fan1 w V E hVfin
  have hpos : 0 < (setOfEdge w V E).ncard :=
    lt_trans Nat.zero_lt_one (hcard w hw)
  obtain ⟨v, hv⟩ := (Set.ncard_pos hfin).mp hpos
  exact ⟨v, hv.1, hv.2⟩

/-- 当 `S,T ⊆ {w}` 且 `x ∉ S,T` 时，`S,T` 各为 `∅` 或 `{w}`，故两处
`affGe` 的并集可合并为 `affGe {x} (S ∪ T)`（退化项 `affGe {x} ∅` 含于
另一项）。 -/
private theorem affGe_union_of_subset_singleton {x w : V3} {S T : Set V3}
    (hS : S ⊆ ({w} : Set V3)) (hT : T ⊆ ({w} : Set V3))
    (hxS : x ∉ S) (hxT : x ∉ T)
    (hfinS : ({x} ∪ S : Set V3).Finite) (hfinT : ({x} ∪ T : Set V3).Finite) :
    affGe {x} S ∪ affGe {x} T = affGe {x} (S ∪ T) := by
  rcases Set.subset_singleton_iff_eq.mp hS with hS0 | hSw
  · rw [hS0, Set.empty_union]
    exact Set.union_eq_right.mpr (affGe_mono_right' (Set.empty_subset T) hfinT hxT)
  · subst hSw
    rcases Set.subset_singleton_iff_eq.mp hT with hT0 | hTw
    · rw [hT0, Set.union_empty]
      exact Set.union_eq_left.mpr (affGe_mono_right' (Set.empty_subset _) hfinS hxS)
    · rw [hTw, Set.union_self, Set.union_self]

/-- HOL planarity.hl :11310-11375 `condition_not_intersection_point_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 ds:real^3#real^3#real^3#real^3->bool e1:real^3->bool w:real^3.
FAN(x,V,E) /\ v IN V /\ u IN V /\ ~collinear {x,v,u}
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ aff_gt {x} {v,u} SUBSET dartset_leads_into_fan x V E ds
/\ w IN V /\ e1 = {v, u}
==>aff_ge {x} e1 INTER aff_ge {x} {w} = aff_ge {x} (e1 INTER {w})
```

证明思路：与 `condition_not_intersection_fan` 同型，但把 `e2` 换成
顶点单点集 `{w}`。`aff_ge {x} {w} ⊆ xfan` 由
`exists_edge_fully_surround_fan` 取环绕边 `{w,v'}` 并展开
`aff_ge_eq_aff_gt_union_aff_ge` 得到；其余用 `fan7` 与
`aff_gt {x} {v,u} ∩ xfan = ∅` 收尾。

候选已有引理：
- `exists_edge_fully_surround_fan`（本文件上文）
- `fan7`（Kepler/Text/Fan.lean:51）
- `aff_ge_eq_aff_gt_union_aff_ge`（Kepler/Text/Planarity.lean:4419）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 互异分量）
- `dartset_leads_into_subset_yfan`
  （Kepler/Text/PlanarityComponent.lean:583） -/
theorem condition_not_intersection_point_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {v u w : V3} {ds : Set (V3 × V3)} {e1 : Set V3}
    (hfan : FAN x V E) (hv : v ∈ V) (hu : u ∈ V) (hnc : ¬ Collinear3 x v u)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hsub : affGt {x} {v, u} ⊆ dartsetLeadsIntoFan x V E ds)
    (hw : w ∈ V) (he1 : e1 = {v, u}) :
    affGe {x} e1 ∩ affGe {x} {w} = affGe {x} (e1 ∩ {w}) := by
  subst he1
  have hVfin : V.Finite := hfan.2.2.1.1
  have hxV : x ∉ V := hfan.2.2.2.1
  have hvu : v ≠ u := fun h =>
    hnc (by rw [h]; exact collinear3_pair_right (v0 := x) (v1 := u) rfl)
  have h77 := aff_ge_eq_aff_gt_union_aff_ge (x := x) (v := v) (w := u) hnc
  have hyfan := dartset_leads_into_subset_yfan hfan hcard hfan80 hds
  have hgt_yfan : affGt {x} {v, u} ⊆ yfan x V E :=
    fun y hy => hyfan (hsub hy)
  have hgt_xfan : affGt {x} {v, u} ∩ xfan x V E = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨hygt, hyx⟩ := hy
    have hyy := hgt_yfan hygt
    rw [yfan, Set.mem_sdiff] at hyy
    exact hyy.2 hyx
  obtain ⟨v', hvv', hv'⟩ := exists_edge_fully_surround_fan hfan hw hcard
  have hw_xfan : affGe {x} {w} ⊆ xfan x V E := by
    have hpairfin : ({w, v'} : Set V3).Finite :=
      hVfin.subset (by
        intro z hz
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact hw
        · exact hv')
    have hfin : ({x} ∪ {w, v'} : Set V3).Finite :=
      (Set.finite_singleton x).union hpairfin
    have hxpair : x ∉ ({w, v'} : Set V3) := by
      intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h
      · exact hxV (by rw [h]; exact hw)
      · exact hxV (by rw [h]; exact hv')
    have hsub' : ({w} : Set V3) ⊆ {w, v'} := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [Set.mem_insert_iff]
      exact Or.inl hz
    intro y hy
    exact ⟨{w, v'}, hvv', affGe_mono_right' hsub' hfin hxpair hy⟩
  have hA_disj : affGt {x} {v, u} ∩ affGe {x} {w} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨hyA, hyW⟩ := hy
    have hmem : y ∈ affGt {x} {v, u} ∩ xfan x V E := ⟨hyA, hw_xfan hyW⟩
    rw [hgt_xfan] at hmem
    exact hmem
  have hfan7 := hfan.2.2.2.2.2
  have h7wv : affGe {x} {w} ∩ affGe {x} {v} = affGe {x} ({w} ∩ {v} : Set V3) :=
    hfan7 {w} (Or.inr ⟨w, hw, rfl⟩) {v} (Or.inr ⟨v, hv, rfl⟩)
  have h7wu : affGe {x} {w} ∩ affGe {x} {u} = affGe {x} ({w} ∩ {u} : Set V3) :=
    hfan7 {w} (Or.inr ⟨w, hw, rfl⟩) {u} (Or.inr ⟨u, hu, rfl⟩)
  have hdist : ((affGt {x} {v, u} ∪ affGe {x} {v}) ∪ affGe {x} {u}) ∩
        affGe {x} {w}
      = affGe {x} ({w} ∩ {v} : Set V3) ∪ affGe {x} ({w} ∩ {u} : Set V3) := by
    rw [Set.union_inter_distrib_right, Set.union_inter_distrib_right, hA_disj,
      Set.empty_union]
    rw [Set.inter_comm (affGe {x} {v}) (affGe {x} {w}), h7wv,
      Set.inter_comm (affGe {x} {u}) (affGe {x} {w}), h7wu]
  rw [h77, hdist]
  have hST : ({w} ∩ {v} : Set V3) ∪ ({w} ∩ {u} : Set V3) = ({v, u} ∩ {w} : Set V3) := by
    rw [← Set.inter_union_distrib_left, Set.singleton_union, Set.inter_comm]
  rw [← hST]
  have hxw : x ∉ ({w} : Set V3) := by
    rw [Set.mem_singleton_iff]
    intro h
    exact hxV (by rw [h]; exact hw)
  exact affGe_union_of_subset_singleton (Set.inter_subset_left) (Set.inter_subset_left)
    (fun hz => hxw (Set.inter_subset_left hz))
    (fun hz => hxw (Set.inter_subset_left hz))
    ((Set.finite_singleton x).union ((Set.finite_singleton w).subset Set.inter_subset_left))
    ((Set.finite_singleton x).union ((Set.finite_singleton w).subset Set.inter_subset_left))

/-! ## DWWUTKW：加边保持 FAN（planarity.hl:11377-11438） -/

/-- HOL planarity.hl :11377-11438 `DWWUTKW`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 ds.
FAN(x,V,E) /\ v IN V /\ u IN V /\ ~collinear {x,v,u}
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ aff_gt {x} {v,u} SUBSET dartset_leads_into_fan x V E ds
/\ E1=E UNION {{v,u}}
==> FAN (x,V,E1)
```

证明思路：展开 `FAN` 为 `(⋃₀ E1 ⊆ V) ∧ Graph E1 ∧ fan1 ∧ fan2 ∧
fan6 ∧ fan7`。
- `⋃₀ E1 ⊆ V`：`add_edge_graph_fan`；
- `Graph E1`：`graph_add_edge_is_graph`（`v ≠ u` 由 `th3` 的非共线推出）；
- `fan6`：`add_edge_into_collinear_fan`；
- `fan7`：对新增边分类，用 `condition_not_intersection_fan` 与
  `condition_not_intersection_point_fan` 处理含 `{v,u}` 的相交；
- `fan1`/`fan2` 与 `E` 的情形一致（加边不改 `V`、不改原点）。

候选已有引理：
- `FAN`（Kepler/Text/Fan.lean:56）
- `add_edge_graph_fan`（本文件上文）
- `graph_add_edge_is_graph`（本文件上文）
- `add_edge_into_collinear_fan`（本文件上文）
- `condition_not_intersection_fan`（本文件上文）
- `condition_not_intersection_point_fan`（本文件上文）
- `fan7`（Kepler/Text/Fan.lean:51） -/
theorem DWWUTKW {x : V3} {V : Set V3} {E E1 : Set (Set V3)}
    {v u : V3} {ds : Set (V3 × V3)}
    (hfan : FAN x V E) (hv : v ∈ V) (hu : u ∈ V) (hnc : ¬ Collinear3 x v u)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hsub : affGt {x} {v, u} ⊆ dartsetLeadsIntoFan x V E ds)
    (hE1 : E1 = E ∪ {{v, u}}) :
    FAN x V E1 := by
  have hvu : v ≠ u := fun h =>
    hnc (by rw [h]; exact collinear3_pair_right (v0 := x) (v1 := u) rfl)
  refine ⟨?_, ?_, hfan.2.2.1, hfan.2.2.2.1, ?_, ?_⟩
  · exact add_edge_graph_fan E1 hv hu hE1 hfan.1
  · exact graph_add_edge_is_graph hE1 hvu hfan.2.1
  · intro e he
    rw [hE1] at he
    exact add_edge_into_collinear_fan hnc hfan.2.2.2.2.1 e he
  · intro e1 he1 e2 he2
    have classify : ∀ e : Set V3,
        e ∈ E1 ∪ {s | ∃ w ∈ V, s = {w}} →
        e ∈ E ∨ e = {v, u} ∨ (∃ w ∈ V, e = {w}) := by
      intro e he
      rw [hE1] at he
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at he
      rcases he with (he | he) | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr he)
    have hfan7_old := hfan.2.2.2.2.2
    rcases classify e1 he1 with he1E | he1vu | ⟨w1, hw1, he1w1⟩
    · rcases classify e2 he2 with he2E | he2vu | he2P
      · exact hfan7_old e1 (Or.inl he1E) e2 (Or.inl he2E)
      · rw [he2vu]
        exact condition_not_intersection_fan hfan hv hu hnc hcard hfan80 hds hsub he1E rfl
      · exact hfan7_old e1 (Or.inl he1E) e2 (Or.inr he2P)
    · rcases classify e2 he2 with he2E | he2vu | ⟨w2, hw2, he2w2⟩
      · rw [Set.inter_comm (affGe {x} e1) (affGe {x} e2), Set.inter_comm e1 e2]
        exact condition_not_intersection_fan hfan hv hu hnc hcard hfan80 hds hsub he2E he1vu
      · rw [he1vu, he2vu, Set.inter_self, Set.inter_self]
      · rw [he1vu, he2w2]
        exact condition_not_intersection_point_fan hfan hv hu hnc hcard hfan80 hds hsub hw2 rfl
    · rcases classify e2 he2 with he2E | he2vu | he2P
      · exact hfan7_old e1 (Or.inr ⟨w1, hw1, he1w1⟩) e2 (Or.inl he2E)
      · rw [he1w1, he2vu,
          Set.inter_comm (affGe {x} {w1}) (affGe {x} {v, u}),
          Set.inter_comm ({w1} : Set V3) ({v, u} : Set V3)]
        exact condition_not_intersection_point_fan hfan hv hu hnc hcard hfan80 hds hsub hw1 rfl
      · exact hfan7_old e1 (Or.inr ⟨w1, hw1, he1w1⟩) e2 (Or.inr he2P)

end Kepler.Text
