/-
Port of the HOL Light Flyspeck planarity theory (Fan chapter), slice 18r.

Source: `reference/flyspeck/text_formalization/fan/planarity.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010; persistent copy
`/home/scroll/hol-light-ref/`).

Coverage (slice 18r of block 18, planarity.hl:14509-14909):
- `KVQWYDL_lemma2` (14509)
- `condition_unique_by_dart_leads_into` (14624)
- `PROPERTIES_TRIANGLE_FAN_lemma1` (14669)
- `PROPERTIES_TRIANGLE_FAN_lemma2` (14702)
- `PROPERTIES_TRIANGLE_FAN` (14713)
- `inter_aff_gt_3_1_is_aff_gt_2_2` (14725)
- `condition_edge_in_face_fan` (14775)
- `KVQWYDL_lemma3` (14846)
- `FINITE_FACE_FAN` (14872)
- `condition_f1_fan_in_face_set` (14883)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `aff_gt`/`aff_ge` ↔ `affGt`/`affGe` (Kepler/Geom/Aff.lean:39/42);
  repo-specific (`Affsign`-based), no Mathlib counterpart.
- HOL `coplanar` ↔ `Coplanar` (Kepler/Geom/Coplanar.lean:23).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `w_dart_fan` ↔ `wDartFan`
  (Kepler/Text/Fan.lean:162); HOL `dart_leads_into` ↔ `dartLeadsInto`
  (Kepler/Text/TopologyFan.lean:4179).
- HOL `hypermap1_of_fanx (x,V,E)` (quadruple-dart hypermap on `d1_fan`) is
  NOT ported; as in Kepler/Text/PlanarityComponent.lean:37-48, the face-set
  hypothesis `ds IN face_set(hypermap1_of_fanx (x,V,E))` is encoded as
  `ds ∈ (hypermapOfFan x V E hfan).faceSet` with pair darts `ds : Set (V3 × V3)`.
- HOL `d_fan`/`d1_fan`/`f1_fan` are NOT ported. Closest encodings: pair
  `dartOfFan` (Kepler/Text/Fan.lean:90) for `d_fan`, `dart1OfFan`
  (Kepler/Text/Fan.lean:86) for `d1_fan`, and the pair face map
  `fFanPair x V E` (Kepler/Text/Fan.lean:118) for `f1_fan` (its contracted
  dart projection; HOL `f1_fan` uses `inverse1_sigma_fan` while `fFanPair`
  uses `inverseSigmaFan`, equal on edges by
  `inverse_sigma_fan_eq_inverse1`, Kepler/Text/Fan.lean:829). Hence
  `d_fan (x,V,E) = d1_fan (x,V,E)` ↦ `dartOfFan V E = dart1OfFan V E`.
  Gap: `hypermap_of_fan_rep` (fan.hl:2780) and `into_domain_power_efn_fan`
  (fan.hl:2694) are not ported, so `condition_f1_fan_in_face_set`'s proof
  needs pair-dart analogues.
- Not-yet-ported proof dependencies (not in any statement): `UNIQUE_SIGMA_FAN`
  (fan.hl:2107), `WEDGE_LUNE_GT` (planarity.hl), `dart_leads_into_fan_in_
  topological_component_yfan` (closest: `dartset_leads_into_is_topological_
  component_yfan`, Kepler/Text/PlanarityComponent.lean:535),
  `face_subset_dart_fan` (closest: `face_subset_darts`,
  Kepler/Text/Hypermap.lean:854), `lemma_face_representation` (closest:
  `face_representation`, Kepler/Text/Hypermap.lean:2794).
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`affGt`/`dartLeadsInto`/`hypermapOfFan` vocabulary, so
  nothing is skipped.
-/

import Kepler.Text.PlanarityAuto13

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open scoped Topology

/-! ## KVQWYDL_lemma2 与 dart_leads_into 的唯一性（planarity.hl:14509-14668） -/

/-- HOL planarity.hl :14509-14623 `KVQWYDL_lemma2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 u1:real^3 w1:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E /\ {u1,w1} IN E
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\   aff_gt{x} {v,u,w} = dart_leads_into x V E u1 w1
==> u1 IN {v,u,w}
```

证明思路：由 `fan80` 与 `sigma_fan x V E u w = v` 经
`properties_fully_surrounded` 得 `¬ Coplanar {x,v,u,w}`；取
`not_empty_rw_dart_fan` 与 `rw_dart_avoids_fan` 的小阈值 `h1`，
`dartLeadsInto_spec` 给 `rwDartFan (u1,w1)(cos h1) ⊆ aff_gt {x}{v,u,w}`。
再用 `aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3`、
`POINT_IN_CLOSURE_AFF_GT_1_2`、`v_subset_xfan` 把 `u1` 归约到三条
`aff_ge` 之一，最后由 `POINT_IN_AFF_GE_IMP_IN_EDGE` 得 `u1 ∈ {v,u,w}`。

候选已有引理：
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `not_empty_rw_dart_fan`（Kepler/Text/TopologyFan.lean:4125）
- `dartLeadsInto_spec`（Kepler/Text/TopologyFan.lean:4233）
- `rw_dart_avoids_fan`（Kepler/Text/TopologyFan.lean:3303）
- `sigma_fan_in_setOfEdge`（Kepler/Text/Fan.lean:326）
- `properties_of_setOfEdge_fan`（Kepler/Text/Fan.lean:334）
- `aff_gt_in_rw_dart_fan`（Kepler/Text/PlanarityAngle.lean:2069）
- `point_in_yfan_is_not_inv_fan`（Kepler/Text/PlanarityAuto13.lean:429）
- `nonsetedge_fully_surround_fan`（Kepler/Text/PlanarityConnect.lean:99）
- `point_in_yfan_not_x_fan`（Kepler/Text/PlanarityAuto6.lean:387）
- `aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3`（Kepler/Text/PlanarityAuto13.lean:89）
- `POINT_IN_CLOSURE_AFF_GT_1_2`（Kepler/Text/PlanarityAuto13.lean:584）
- `topological_component_subset_yfan`（Kepler/Text/PlanarityConnect.lean:189）
- `v_subset_xfan`（Kepler/Text/PlanarityAuto8.lean:501）
- `POINT_IN_AFF_GE_IMP_IN_EDGE`（Kepler/Text/PlanarityAuto13.lean:529）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039，HOL `remark1_fan` 的互异部分） -/
private theorem affGt_subset_affGe_auto14 {s t : Set V3} : affGt s t ⊆ affGe s t := by
  rintro y ⟨f, hfin, hsum, hpos, hone⟩
  exact ⟨f, hfin, hsum, fun w hw => le_of_lt (hpos w hw), hone⟩

theorem KVQWYDL_lemma2 {x v u w u1 w1 : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hu1w1 : {u1, w1} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (haff : affGt ({x} : Set V3) ({v, u, w} : Set V3) = dartLeadsInto x V E u1 w1) :
    u1 ∈ ({v, u, w} : Set V3) := by
  obtain ⟨hθ0, hθπ⟩ := hfan80 u w huw
  rw [hsigma] at hθ0 hθπ
  have hcop : ¬ Coplanar ({x, v, u, w} : Set V3) :=
    properties_fully_surrounded hfan hvu huw hθ0 hθπ
  obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec hfan hu1w1
  set h1 : ℝ := min h (Real.pi / 2) / 2 with hh1def
  have hminpos : 0 < min h (Real.pi / 2) := lt_min hh0 (by positivity)
  have hh1_0 : 0 < h1 := by
    rw [hh1def]; exact div_pos hminpos two_pos
  have hh1_h : h1 < h := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hminpos) (min_le_left _ _)
  have hh1_pi2 : h1 < Real.pi / 2 := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hminpos) (min_le_right _ _)
  obtain ⟨y, hy⟩ := not_empty_rw_dart_fan hfan hu1w1 hh1_0 hh1_pi2
  obtain ⟨hsub, -⟩ := hspec h1 y hh1_0 hh1_h hy
  have hu1V : u1 ∈ V := (fan_mem_of_edge hfan hu1w1).1
  have hxu1 : x ≠ u1 := by
    intro hx
    exact hfan.2.2.2.1 (by rw [hx]; exact hu1V)
  have hσmem : sigmaFan x V E u1 w1 ∈ setOfEdge u1 V E :=
    sigma_fan_in_setOfEdge hfan
      ((properties_of_setOfEdge_fan x V E u1 w1 hfan).mp hu1w1)
  have hvu' : ({sigmaFan x V E u1 w1, u1} : Set V3) ∈ E := by
    have h :=
      (properties_of_setOfEdge_fan x V E u1 (sigmaFan x V E u1 w1) hfan).mpr hσmem
    rw [Set.pair_comm] at h
    exact h
  have hgt_sub : affGt ({x} : Set V3) ({u1, y} : Set V3) ⊆
      rwDartFan x V E (x, u1, w1, sigmaFan x V E u1 w1) (Real.cos h1) :=
    aff_gt_in_rw_dart_fan (v := sigmaFan x V E u1 w1) (u := u1) (w := w1)
      (y := y) (s := h1) hfan hvu' hu1w1 rfl hh1_0 hh1_pi2 hy hfan80 hcard
  have hgt_sub' : affGt ({x} : Set V3) ({u1, y} : Set V3) ⊆
      affGt ({x} : Set V3) ({v, u, w} : Set V3) :=
    hgt_sub.trans (hsub.trans (le_of_eq haff.symm))
  have hne : E ≠ ∅ := nonsetedge_fully_surround_fan hcard hfan
  have hU : dartLeadsInto x V E u1 w1 ∈ topologicalComponentYfan x V E :=
    dart_leads_into_mem_topologicalComponentYfan hfan hu1w1
  have hydl : y ∈ dartLeadsInto x V E u1 w1 := hsub hy
  have hxy : x ≠ y :=
    point_in_yfan_not_x_fan x V E (dartLeadsInto x V E u1 w1) y hfan hne hU hydl
  have hu1y : u1 ≠ y :=
    point_in_yfan_is_not_inv_fan x V E (dartLeadsInto x V E u1 w1) y u1 hfan hcard
      hU hydl hu1V
  have hu1clos : u1 ∈ closure (affGt ({x} : Set V3) ({u1, y} : Set V3)) :=
    POINT_IN_CLOSURE_AFF_GT_1_2 x u1 y hxu1 hxy hu1y
  have hclosed : IsClosed (affGe ({x} : Set V3) ({v, u, w} : Set V3)) := by
    have hcompl : IsOpen (affGe ({x} : Set V3) ({v, u, w} : Set V3))ᶜ := by
      simpa [Set.sdiff_eq, Set.univ_inter] using OPEN_DIFF_AFF_GE x v u w
    exact isOpen_compl_iff.mp hcompl
  have hcl : closure (affGt ({x} : Set V3) ({u1, y} : Set V3)) ⊆
      affGe ({x} : Set V3) ({v, u, w} : Set V3) := by
    calc closure (affGt ({x} : Set V3) ({u1, y} : Set V3))
        ⊆ closure (affGe ({x} : Set V3) ({v, u, w} : Set V3)) :=
          closure_mono (hgt_sub'.trans affGt_subset_affGe_auto14)
      _ = affGe ({x} : Set V3) ({v, u, w} : Set V3) := hclosed.closure_eq
  have hu1ge : u1 ∈ affGe ({x} : Set V3) ({v, u, w} : Set V3) := hcl hu1clos
  have hgt_yfan : affGt ({x} : Set V3) ({v, u, w} : Set V3) ⊆ yfan x V E := by
    rw [haff]
    exact topological_component_subset_yfan
      (dart_leads_into_mem_topologicalComponentYfan hfan hu1w1)
  have hu1xfan : u1 ∈ xfan x V E := v_subset_xfan x V E hfan hcard hu1V
  have hu1notgt : u1 ∉ affGt ({x} : Set V3) ({v, u, w} : Set V3) := by
    intro hgt
    have hyf : u1 ∈ yfan x V E := hgt_yfan hgt
    rw [yfan, Set.mem_sdiff] at hyf
    exact hyf.2 hu1xfan
  have hdecomp := aff_ge_1_3_eq_unions_aff_ge_1_2_and_aff_gt_1_3 x v u w hcop
  rw [hdecomp] at hu1ge
  rcases (by simpa only [Set.mem_union] using hu1ge) with ((h1' | h2') | h3') | h4'
  · have hm := POINT_IN_AFF_GE_IMP_IN_EDGE x V E v u u1 hfan hvu hu1V hxu1 h1'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    tauto
  · have hm := POINT_IN_AFF_GE_IMP_IN_EDGE x V E u w u1 hfan huw hu1V hxu1 h2'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    tauto
  · have hm := POINT_IN_AFF_GE_IMP_IN_EDGE x V E w v u1 hfan hwv hu1V hxu1 h3'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    tauto
  · exact absurd h4' hu1notgt

/-- HOL planarity.hl :14624-14668 `condition_unique_by_dart_leads_into`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) w:real^3 u:real^3 w1:real^3.
FAN(x,V,E)/\ {u,w} IN E /\ {u,w1} IN E
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ dart_leads_into x V E u w SUBSET w_dart_fan x V E (x,u,w,sigma_fan x V E u w)
/\  dart_leads_into x V E u w  = dart_leads_into x V E u w1 
==> w= w1
```

证明思路：同 `KVQWYDL_lemma2` 的小角度构造：取 `h1 = min h (acs h')/2`
得 `rwDartFan (u,w1)(cos h1) ⊆ dart_leads_into u w1 = dart_leads_into u w`，
配合子集假设得两 `wDartFan` 有公共点，故
`w_dart_fan (u,w) ∩ w_dart_fan (u,w1) ≠ ∅`；由 `disjoint_fan2`，不同边
（`w ≠ w1`）的 `wDartFan` 不相交，故 `w = w1`。

候选已有引理：
- `dartLeadsInto_spec`（Kepler/Text/TopologyFan.lean:4233）
- `not_empty_rw_dart_fan`（Kepler/Text/TopologyFan.lean:4125）
- `rw_dart_avoids_fan`（Kepler/Text/TopologyFan.lean:3303）
- `disjoint_fan2`（Kepler/Text/TopologyFan.lean:1912） -/
theorem condition_unique_by_dart_leads_into {x w u w1 : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (huw : {u, w} ∈ E) (huw1 : {u, w1} ∈ E)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (hsub : dartLeadsInto x V E u w ⊆
      wDartFan x V E (x, u, w, sigmaFan x V E u w))
    (heq : dartLeadsInto x V E u w = dartLeadsInto x V E u w1) :
    w = w1 := by
  by_contra hne
  obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec (v := u) (u := w1) hfan huw1
  set h1 : ℝ := min h (Real.pi / 2) / 2 with hh1def
  have hminpos : 0 < min h (Real.pi / 2) := lt_min hh0 (by positivity)
  have hh1_0 : 0 < h1 := by
    rw [hh1def]; exact div_pos hminpos two_pos
  have hh1_h : h1 < h := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hminpos) (min_le_left _ _)
  have hh1_pi2 : h1 < Real.pi / 2 := by
    rw [hh1def]
    exact lt_of_lt_of_le (half_lt_self hminpos) (min_le_right _ _)
  obtain ⟨y, hy⟩ :=
    not_empty_rw_dart_fan (v := u) (u := w1) hfan huw1 hh1_0 hh1_pi2
  obtain ⟨hsub', -⟩ := hspec h1 y hh1_0 hh1_h hy
  have hyw1 : y ∈ wDartFan x V E (x, u, w1, sigmaFan x V E u w1) := hy.1
  have hydl1 : y ∈ dartLeadsInto x V E u w1 := hsub' hy
  have hydl : y ∈ dartLeadsInto x V E u w := heq.symm ▸ hydl1
  have hyw : y ∈ wDartFan x V E (x, u, w, sigmaFan x V E u w) := hsub hydl
  have hmem : y ∈ wDartFan x V E (x, u, w, sigmaFan x V E u w) ∩
      wDartFan x V E (x, u, w1, sigmaFan x V E u w1) := ⟨hyw, hyw1⟩
  have hempty := disjoint_fan2 (v := u) hfan huw huw1 hne
  rw [hempty] at hmem
  exact hmem

/-! ## 三角形扇面的 σ 性质（planarity.hl:14669-14724） -/

/-- HOL planarity.hl :14669-14701 `PROPERTIES_TRIANGLE_FAN_lemma1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E 
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==> sigma_fan x V E v u = w 
```

证明思路：由三条边经 `edge_ne_of_fan` 得 `u ≠ w`，故
`set_of_edge v V E ≠ {u}`。用 `UNIQUE_SIGMA_FAN`（HOL 未移植，需补）对
任意 `w1 ∈ set_of_edge v V E` 证明 `azim x v u w ≤ azim x v u w1`：
`SIGMA_FAN` 给 `sigma_fan v u` 最小，`angle_is_small_fan` 把 `w` 与
`sigma_fan v u` 的角序对齐，`REAL_ARITH` 收口。

候选已有引理：
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- `angle_is_small_fan`（Kepler/Text/PlanarityAngle.lean:490）
- `edge_ne_of_fan`（Kepler/Text/Fan.lean:1039）
- `properties_of_setOfEdge_fan`（Kepler/Text/Fan.lean:334）
- 缺口：`UNIQUE_SIGMA_FAN`（fan.hl:2107）未移植 -/
theorem PROPERTIES_TRIANGLE_FAN_lemma1 {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    sigmaFan x V E v u = w := by
  have huw_ne : u ≠ w := edge_ne_of_fan hfan huw
  have hwv' : {v, w} ∈ E := by simpa [Set.pair_comm] using hwv
  have hw_mem : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hwv'
  have hu_mem : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hne : setOfEdge v V E ≠ {u} := by
    intro h
    have hw : w ∈ ({u} : Set V3) := h ▸ hw_mem
    exact huw_ne (Set.mem_singleton_iff.mp hw).symm
  have hσ := SIGMA_FAN hne hfan hu_mem
  have hσmin : azim x v u (sigmaFan x V E v u) ≤ azim x v u w :=
    hσ.2.2 w hw_mem (fun h => huw_ne h.symm)
  have hsmall : azim x v u w ≤ azim x v u (sigmaFan x V E v u) :=
    angle_is_small_fan hfan hvu huw hsigma hfan80 hcard
  have heq : azim x v u (sigmaFan x V E v u) = azim x v u w :=
    le_antisymm hσmin hsmall
  have hvσ : {v, sigmaFan x V E v u} ∈ E :=
    (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v u) hfan).mpr hσ.1
  exact unique_azim_point_fan hfan hvu hvσ hwv' heq

/-- HOL planarity.hl :14702-14712 `PROPERTIES_TRIANGLE_FAN_lemma2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E 
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==> sigma_fan x V E w v=u
```

证明思路：对三元组 `(w,v,u)` 再次调用 `PROPERTIES_TRIANGLE_FAN_lemma1`：
边 `{w,v},{v,u},{u,w}` 轮换后满足前提（`sigma_fan w v = u` 由 lemma1
在 `(v,u,w)` 上的结论提供）。

候选已有引理：
- `PROPERTIES_TRIANGLE_FAN_lemma1`（本文件上文，HOL :14669） -/
theorem PROPERTIES_TRIANGLE_FAN_lemma2 {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    sigmaFan x V E w v = u := by
  have h1 : sigmaFan x V E v u = w :=
    PROPERTIES_TRIANGLE_FAN_lemma1 hfan hvu huw hwv hsigma hcard hfan80
  exact PROPERTIES_TRIANGLE_FAN_lemma1 hfan hwv hvu huw h1 hcard hfan80

/-- HOL planarity.hl :14713-14724 `PROPERTIES_TRIANGLE_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E 
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==> sigma_fan x V E v u = w/\ sigma_fan x V E w v=u
```

证明思路：合取，两个分量分别是
`PROPERTIES_TRIANGLE_FAN_lemma1` 与 `PROPERTIES_TRIANGLE_FAN_lemma2`。

候选已有引理：
- `PROPERTIES_TRIANGLE_FAN_lemma1`（本文件上文，HOL :14669）
- `PROPERTIES_TRIANGLE_FAN_lemma2`（本文件上文，HOL :14702） -/
theorem PROPERTIES_TRIANGLE_FAN {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    sigmaFan x V E v u = w ∧ sigmaFan x V E w v = u := by
  exact ⟨PROPERTIES_TRIANGLE_FAN_lemma1 hfan hvu huw hwv hsigma hcard hfan80,
    PROPERTIES_TRIANGLE_FAN_lemma2 hfan hvu huw hwv hsigma hcard hfan80⟩

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

/-! ## 3-1 与 2-2 仿射开单纯形的交（planarity.hl:14725-14774） -/

/-- HOL planarity.hl :14725-14774 `inter_aff_gt_3_1_is_aff_gt_2_2`

HOL 原文：
```
!x v u w:real^3.
~coplanar {x,v,u,w}
==>
aff_gt {x,v,u} {w} INTER aff_gt {x,u,w} {v} =aff_gt {x,u} {v,w}
```

证明思路：`GEOM_ORIGIN_TAC x` 平移 `x` 到原点，`notcoplanar_disjoints`
得各点互异；`AFF_GT_3_1`（两次）与 `AFF_GT_2_2` 展开成系数形式，由
`NOT_COPLANAR_0_4_IMP_INDEPENDENT` 的向量独立性 + `INDEPENDENT_3`
比较系数，再互相构造系数见证（`EXTENSION`/`REAL_ARITH`/`VECTOR_ARITH`）。

候选已有引理：
- `AFF_GT_3_1`（Kepler/Text/PlanarityAuto11.lean:957）
- `affGt2_2`（Kepler/Text/Planarity.lean:1496，2-2 形状）
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `notcoplanar_disjoint`（Kepler/Text/PlanarityAuto11.lean:1220）
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418） -/
theorem inter_aff_gt_3_1_is_aff_gt_2_2 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    affGt ({x, v, u} : Set V3) {w} ∩ affGt ({x, u, w} : Set V3) {v} =
      affGt ({x, u} : Set V3) {v, w} := by
  obtain ⟨hdis1, hdis2, -, -, hdis5, -, -, -⟩ :=
    notcoplanar_disjoints x v u w hcop
  ext y
  constructor
  · intro hy
    simp only [Set.mem_inter_iff] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [AFF_GT_3_1 x v u w hdis1, Set.mem_setOf_eq] at hy1
    rw [AFF_GT_3_1 x u w v hdis2, Set.mem_setOf_eq] at hy2
    rw [affGt2_2 hdis5, Set.mem_setOf_eq]
    obtain ⟨a1, a2, a3, a4, ha4, hasum, hay⟩ := hy1
    obtain ⟨b1, b2, b3, b4, hb4, hbsum, hby⟩ := hy2
    have heq : (a2 - b4) • (v - x) + (a3 - b2) • (u - x) +
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
    obtain ⟨ha2b4, -, -⟩ := notcoplanar_smul_sub_eq_zero hcop heq
    have ha2pos : 0 < a2 := by rw [sub_eq_zero.mp ha2b4]; exact hb4
    exact ⟨a1, a3, a2, a4, ha2pos, ha4, by linarith, by rw [hay]; module⟩
  · intro hy
    rw [affGt2_2 hdis5, Set.mem_setOf_eq] at hy
    obtain ⟨t1, t2, t3, t4, ht3, ht4, htsum, hty⟩ := hy
    simp only [Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · rw [AFF_GT_3_1 x v u w hdis1, Set.mem_setOf_eq]
      exact ⟨t1, t3, t2, t4, ht4, by linarith, by rw [hty]; module⟩
    · rw [AFF_GT_3_1 x u w v hdis2, Set.mem_setOf_eq]
      exact ⟨t1, t2, t4, t3, ht3, by linarith, by rw [hty]; module⟩

/-! ## 面上边与 dart_leads_into 的对应（planarity.hl:14775-14845） -/

/-- HOL planarity.hl :14775-14845 `condition_edge_in_face_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 u1:real^3 w1:real^3.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E /\ {u1,w1} IN E
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ u1=v
/\   aff_gt{x} {v,u,w} = dart_leads_into x V E u1 w1
==> (u1,w1) IN {(v,u),(u,w),(w,v)}
```

证明思路：代入 `u1 = v`，用 `condition_unique_by_dart_leads_into` 对
`(v,u)` 与 `(v,w1)` 得 `u = w1`；其子集前提
`dart_leads_into v u ⊆ w_dart_fan (x,v,u,·)` 由
`PROPERTIES_TRIANGLE_FAN`、`KVQWYDL_lemma1`、`WEDGE_LUNE_GT`（未移植）、
`inter_aff_gt_3_1_is_aff_gt_2_2` 与 `inter_aff_gt_3_1_is_aff_gt_1_3` 拼出。
于是 `(u1,w1) = (v,u) ∈ {(v,u),(u,w),(w,v)}`。

候选已有引理：
- `condition_unique_by_dart_leads_into`（本文件上文，HOL :14624）
- `PROPERTIES_TRIANGLE_FAN`（本文件上文，HOL :14713）
- `KVQWYDL_lemma1`（Kepler/Text/PlanarityAuto13.lean:368）
- `inter_aff_gt_3_1_is_aff_gt_2_2`（本文件上文，HOL :14725）
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418）
- 缺口：`WEDGE_LUNE_GT`（planarity.hl）未移植 -/
theorem condition_edge_in_face_fan {x v u w u1 w1 : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hu1w1 : {u1, w1} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) (hu1 : u1 = v)
    (haff : affGt ({x} : Set V3) ({v, u, w} : Set V3) = dartLeadsInto x V E u1 w1) :
    (u1, w1) ∈ ({(v, u), (u, w), (w, v)} : Set (V3 × V3)) := by
  sorry

/-- HOL planarity.hl :14846-14871 `KVQWYDL_lemma3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 w:real^3 u1 w1.
FAN(x,V,E)/\ {v,u} IN E /\ {u,w} IN E /\ {w,v} IN E /\ {u1,w1} IN E
/\ sigma_fan x V E u w = v
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\   aff_gt{x} {v,u,w} = dart_leads_into x V E u1 w1
==> (u1,w1) IN {(v,u),(u,w),(w,v)}
```

证明思路：`KVQWYDL_lemma2` 给 `u1 ∈ {v,u,w}`，分三种情形
（`u1=v` / `u1=u` / `u1=w`），各自把边三元组轮换后用
`PROPERTIES_TRIANGLE_FAN` 与 `condition_edge_in_face_fan` 得到对应
有序对属于 `{(v,u),(u,w),(w,v)}`。

候选已有引理：
- `KVQWYDL_lemma2`（本文件上文，HOL :14509）
- `PROPERTIES_TRIANGLE_FAN`（本文件上文，HOL :14713）
- `condition_edge_in_face_fan`（本文件上文，HOL :14775） -/
theorem KVQWYDL_lemma3 {x v u w u1 w1 : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hwv : {w, v} ∈ E) (hu1w1 : {u1, w1} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E)
    (haff : affGt ({x} : Set V3) ({v, u, w} : Set V3) = dartLeadsInto x V E u1 w1) :
    (u1, w1) ∈ ({(v, u), (u, w), (w, v)} : Set (V3 × V3)) := by
  sorry

/-! ## 面的有限性与 f1 封闭性（planarity.hl:14872-14909） -/

/-- HOL planarity.hl :14872-14882 `FINITE_FACE_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E))
==> FINITE ds 
```

证明思路：`hypermap1_of_fanx` 的 face set 元素是 `d_fan` 的轨道，故
`ds ⊆ d_fan`（HOL `face_subset_dart_fan`；二元组版即 `face_subset_darts`）。
由 `FAN` 的 `fan1` 得 `V` 有限，`finite_dart_fan` 给 `d_fan`（二元组
`dartOfFan`）有限，`Set.Finite.subset` 收口。

候选已有引理：
- `face_subset_darts`（Kepler/Text/Hypermap.lean:854，HOL `face_subset_dart_fan`）
- `finite_dart_fan`（Kepler/Text/Fan.lean:872，HOL `finite_d_fan`）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169） -/
theorem FINITE_FACE_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ds.Finite := by
  sorry

/-- HOL planarity.hl :14883-14909 `condition_f1_fan_in_face_set`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) y y1 ds.
FAN(x,V,E) 
/\ y = f1_fan x V E y1 
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ d_fan (x,V,E) =d1_fan (x,V,E)
/\ y1 IN ds
==> y IN ds
```

编码说明（缺口）：`hypermap1_of_fanx`/`f1_fan`/`d_fan`/`d1_fan` 均未
移植；按本仓库二元组 dart 约定（PlanarityComponent.lean:37-48）编码为
`ds ∈ (hypermapOfFan x V E hfan).faceSet`、`y = fFanPair x V E y1`、
`dartOfFan V E = dart1OfFan V E`，dart 类型为 `V3 × V3`。

证明思路：`face_representation` 给 `ds = H.face x'` 且 `x' ∈ ds`，故
`y1` 是 `H.faceMap` 轨道上的点；`d_fan = d1_fan` 保证 `y1 ∈ d1_fan`，
从而 `H.faceMap y1 = fFanPair x V E y1 = y`（二元组版
`hypermapOfFan_faceMap_eq`），轨道对 `faceMap` 封闭即得 `y ∈ ds`。
HOL 用未移植的 `hypermap_of_fan_rep`/`into_domain_power_efn_fan` 构造幂表示。

候选已有引理：
- `face_representation`（Kepler/Text/Hypermap.lean:2794，HOL `lemma_face_representation`）
- `hypermapOfFan`（Kepler/Text/Fan.lean:1169）
- `fFanPair`（Kepler/Text/Fan.lean:118）
- `hypermapOfFan_faceMap_eq`（Kepler/Text/PlanarityComponent.lean:242，`private`，需公开或重导）
- 缺口：`hypermap_of_fan_rep`（fan.hl:2780）、`into_domain_power_efn_fan`（fan.hl:2694）未移植 -/
theorem condition_f1_fan_in_face_set {x : V3} {V : Set V3} {E : Set (Set V3)}
    {y y1 : V3 × V3} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hy : y = fFanPair x V E y1)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hdf : dartOfFan V E = dart1OfFan V E)
    (hy1 : y1 ∈ ds) :
    y ∈ ds := by
  sorry

end Kepler.Text
