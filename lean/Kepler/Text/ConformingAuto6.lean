/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 6
(Conforming.hl:1267-1477).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 6, Conforming.hl:1267-1477):
- `fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan` (1267)
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN` (1292)
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL` (1333)
- `MEASURABLE_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL` (1342)
- `RADIAL_TOPOLOGICAL_COMPONENT_YFAN` (1352)
- `FINITE_TOPOLOGICAL_COMPONENT_YFAN` (1396)
- `SUM_SOL_TOPOLOGICAL_COMPONENT_YFAN_EQ_SOL_UNIONS` (1419)
- `UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN` (1435)
- `SUM_SOL_IN_FACE_SET_EQ_4PI` (1456)
- `DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET` (1470)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94); HOL
  `fan80` ↔ `fan80` (Kepler/Text/Fan.lean:227); HOL `sigma_fan` ↔
  `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `f1_fan` ↔ `f1Fan`
  (Kepler/Text/ConformingDefs.lean:87).
- HOL `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184); the explicit `hfan : FAN x V E`
  witness is carried through because `hypermapOfFan` needs it (HOL's
  `hypermap_of_fan` is total).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48, `face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet` with pair darts `V3 × V3`.
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48);
  `pr2 y`/`pr3 y` ↦ `y.1`/`y.2`; `pr3 (f1_fan x V E y)` ↦
  `(f1Fan x V E y).2`.
- HOL `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); HOL `yfan` ↔ `yfan` (Kepler/Text/Fan.lean:158);
  HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348).
- HOL `open` ↔ `IsOpen`; HOL `measurable` ↔ `MeasurableSet`; HOL
  `normball x r` ↔ Mathlib `Metric.ball x r` (both are
  `{y | dist y x < r}`; cf. `NORMBALL_BALL`, sphere.hl); HOL
  `bounded` ↔ `Bornology.IsBounded` (repo convention, cf.
  Kepler/Text/TopologyFan.lean:2764).
- HOL `radial_norm r x C` ↔ `radialNorm r x C`
  (Kepler/Geom/Volume.lean:27); HOL `sol x C` ↔ `Kepler.Geom.sol x C`
  (Kepler/Geom/Volume.lean:36).
- HOL `UNIONS f` ↔ `⋃₀ f` (`Set.sUnion`); HOL `INTERS f` ↔ `⋂₀ f`
  (`Set.sInter`); HOL `INTER` ↔ `∩`; HOL `sum S g` (set sum) ↔ finsum
  `∑ᶠ y ∈ S, g y` (`open scoped BigOperators`); HOL `&4 * pi` ↔
  `4 * Real.pi`.
- HOL `(A)hypermap` ↔ `Hypermap α` (Kepler/Text/Hypermap.lean:765); HOL
  `dart H` (the dart *set*) ↔ `(↑H.darts : Set α)` (Kepler/Text/Hypermap.lean:767);
  HOL `face_set`/`node_set`/`edge_set` ↔ `H.faceSet`/`H.nodeSet`/`H.edgeSet`
  (Kepler/Text/Hypermap.lean:1002-1008).
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL` has `r` free in HOL
  (implicitly universally quantified); as in `BOUNDED_INTER_BALL`
  (ConformingAuto5.lean:380), `r` is an explicit parameter here.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`conformingFan`/`topologicalComponentYfan`/`affGt`/
  `radialNorm`/`sol`/`Hypermap` vocabulary, so nothing is skipped.
  `DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET` is repo-specific to the
  `Hypermap` structure, but its content is the three specializations of
  the already-ported `sUnion_setOfOrbits` (Hypermap.lean:1562); it is kept
  (public, HOL name) as required by the batch.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto5

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Complex
open Filter
open Classical
open MeasureTheory
open scoped Topology
open scoped BigOperators

/-! ## 全包围 fan 的 `aff_gt` 与 dart（Conforming.hl:1267-1291） -/

private theorem cross_dot_cyclic_conf_auto6 {a b c : Fin 3 → ℝ} :
    (crossProduct a b) ⬝ᵥ c = (crossProduct b c) ⬝ᵥ a := by
  calc (crossProduct a b) ⬝ᵥ c = c ⬝ᵥ crossProduct a b := dotProduct_comm _ _
    _ = a ⬝ᵥ crossProduct b c := triple_product_permutation c a b
    _ = (crossProduct b c) ⬝ᵥ a := dotProduct_comm _ _

private theorem fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan_auto6 {x : V3}
    {V : Set V3} {E : Set (Set V3)} {v w : V3}
    (hfan : FAN x V E) (hvw : {v, w} ∈ E)
    (_hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) :
    affGt ({x, v, w} : Set V3) {sigmaFan x V E v w} =
      affGt ({x, v, w} : Set V3) {inverse1SigmaFan x V E w v} := by
  have hwv : {w, v} ∈ E := by
    rw [show ({w, v} : Set V3) = {v, w} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hvw
  have hwS : w ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v w hfan).mp hvw
  have hsS : sigmaFan x V E v w ∈ setOfEdge v V E :=
    sigma_fan_in_setOfEdge hfan hwS
  have hvs : {v, sigmaFan x V E v w} ∈ E :=
    (properties_of_setOfEdge_fan x V E v (sigmaFan x V E v w) hfan).mpr hsS
  have hsv : {sigmaFan x V E v w, v} ∈ E := by
    rw [show ({sigmaFan x V E v w, v} : Set V3) = {v, sigmaFan x V E v w} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hvs
  have hwt : {w, inverse1SigmaFan x V E w v} ∈ E :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).1 v hwv
  have hsig_t : sigmaFan x V E w (inverse1SigmaFan x V E w v) = v :=
    (INVERSE1_SIGMA_FAN (v := w) hfan).2.1 v hwv
  have h80_vw := hfan80 v w hvw
  have h80_wt := hfan80 w (inverse1SigmaFan x V E w v) hwt
  rw [hsig_t] at h80_wt
  have hcop_inv : ¬ Coplanar ({x, v, w, inverse1SigmaFan x V E w v} : Set V3) :=
    properties_fully_surrounded hfan hvw hwt h80_wt.1 h80_wt.2
  have hcop_sig' : ¬ Coplanar ({x, sigmaFan x V E v w, v, w} : Set V3) :=
    properties_fully_surrounded (v := sigmaFan x V E v w) (u := v) (w := w)
      hfan hsv hvw h80_vw.1 h80_vw.2
  have hcop_sig : ¬ Coplanar ({x, v, w, sigmaFan x V E v w} : Set V3) := by
    rw [show ({x, v, w, sigmaFan x V E v w} : Set V3) =
        {x, sigmaFan x V E v w, v, w} from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hcop_sig'
  have hncv_s : ¬ Collinear3 x v (sigmaFan x V E v w) := fan_not_collinear hfan hvs
  have hncvw : ¬ Collinear3 x v w := fan_not_collinear hfan hvw
  have hncwv : ¬ Collinear3 x w v := fan_not_collinear hfan hwv
  have hncwt : ¬ Collinear3 x w (inverse1SigmaFan x V E w v) :=
    fan_not_collinear hfan hwt
  have hpos_sig : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((sigmaFan x V E v w - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := v) (v := w)
      (u1 := sigmaFan x V E v w) hncv_s hncvw h80_vw.1 h80_vw.2
  have hpos_inv_raw : 0 < crossProduct ((w - x : V3) : Fin 3 → ℝ)
      ((inverse1SigmaFan x V E w v - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((v - x : V3) : Fin 3 → ℝ) :=
    cross_dot_fully_surrounded_fan (x := x) (v1 := w)
      (v := inverse1SigmaFan x V E w v) (u1 := v) hncwv hncwt h80_wt.1 h80_wt.2
  have hpos_inv : 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
      ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ
      ((inverse1SigmaFan x V E w v - x : V3) : Fin 3 → ℝ) := by
    rw [cross_dot_cyclic_conf_auto6 (a := ((v - x : V3) : Fin 3 → ℝ))
      (b := ((w - x : V3) : Fin 3 → ℝ))
      (c := ((inverse1SigmaFan x V E w v - x : V3) : Fin 3 → ℝ))]
    exact hpos_inv_raw
  calc affGt ({x, v, w} : Set V3) {sigmaFan x V E v w}
      = {y : V3 | 0 < crossProduct ((v - x : V3) : Fin 3 → ℝ)
          ((w - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} :=
        aff_gt_3_1_rep_cross_dot x v w (sigmaFan x V E v w) hcop_sig hpos_sig
    _ = affGt ({x, v, w} : Set V3) {inverse1SigmaFan x V E w v} :=
        (aff_gt_3_1_rep_cross_dot x v w (inverse1SigmaFan x V E w v) hcop_inv
          hpos_inv).symm

/-- HOL Conforming.hl :1267-1291 `fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds  y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
/\ ds IN face_set (hypermap1_of_fanx (x,V,E))
/\ y IN ds
==>  aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y)} =
 aff_gt {x, pr2 y, pr3 y} {sigma_fan x V E  (pr2 y) (pr3 y)}
```

编码说明：dart 用二元组编码，`pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；
`f1_fan x V E y` ↦ `f1Fan x V E y`，故 `pr3 (f1_fan x V E y)` ↦
`(f1Fan x V E y).2`；`ds`/`y` 为二元组。`face_set (hypermap1_of_fanx …)` ↦
`(hypermapOfFan x V E hfan).faceSet`。

证明思路：由 `hds` 与 `hy` 得 `y ∈ (hypermapOfFan …).darts = dart1OfFan`
（用 `dartOfFan_eq_dart1_of_surrounded` 消去孤立点），从而 `{y.1, y.2} ∈ E`；
把 `f1Fan x V E y` 展开为 `(y.2, inverse1SigmaFan x V E y.2 y.1)`，再用
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`（取 `v = y.2`、`w = y.1`）
把 `pr3 (f1Fan …) = inverse1SigmaFan x V E y.2 y.1` 一侧换成
`sigmaFan x V E y.1 y.2`，并用 `SET_RULE` 重排 `{x, pr2, pr3}` 的次序。

候选已有引理：
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
  （Kepler/Text/ConformingAuto1.lean:166）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `faceSet_subset_dartOfFan_auto2`（private，Kepler/Text/ConformingAuto2.lean:220）
- `properties_of_setOfEdge_fan`（Kepler/Text/Fan.lean:334）
- 缺口：HOL `dartset_fully_surrounded_is_non_isolated_fan` 对应
  `dartOfFan_eq_dart1_of_surrounded`；HOL `hypermap_of_fan_rep` 未移植 -/
theorem fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hy : y ∈ ds) :
    affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2} =
      affGt ({x, y.1, y.2} : Set V3) {sigmaFan x V E y.1 y.2} := by
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hy_dart : y ∈ dart1OfFan V E := by
    simp only [Hypermap.faceSet, setOfOrbits] at hds
    obtain ⟨d, hd, rfl⟩ := hds
    have hsub : orbitMap H.faceMap d ⊆ (↑H.darts : Set (V3 × V3)) :=
      H.face_subset_darts hd
    exact hdarts ▸ hsub hy
  have hyE : {y.1, y.2} ∈ E := by
    simpa [dart1OfFan] using hy_dart
  have h := fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan_auto6
    (x := x) (V := V) (E := E) (v := y.1) (w := y.2) hfan hyE hcard hfan80
  simpa only [f1Fan] using h.symm

/-! ## 拓扑分量的开性（Conforming.hl:1292-1351） -/

private theorem continuous_vsub_ofLp_auto6 (x : V3) :
    Continuous (fun y : V3 => ((y - x : V3) : Fin 3 → ℝ)) :=
  (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
    (continuous_id.sub continuous_const)

private theorem isOpen_dot_pos_auto6 (x : V3) (n : Fin 3 → ℝ) :
    IsOpen {y : V3 | 0 < n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)} := by
  have hcont : Continuous (fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) :=
    continuous_const.dotProduct (continuous_vsub_ofLp_auto6 x)
  exact isOpen_lt (f := fun _ : V3 => (0 : ℝ))
    (g := fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) continuous_const hcont

private theorem isOpen_dot_neg_auto6 (x : V3) (n : Fin 3 → ℝ) :
    IsOpen {y : V3 | n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ) < 0} := by
  have hcont : Continuous (fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ)) :=
    continuous_const.dotProduct (continuous_vsub_ofLp_auto6 x)
  exact isOpen_lt (f := fun y : V3 => n ⬝ᵥ ((y - x : V3) : Fin 3 → ℝ))
    (g := fun _ : V3 => (0 : ℝ)) hcont continuous_const

private theorem isOpen_affGt_3_1_auto6 (x v u w : V3)
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3)) :
    IsOpen (affGt ({x, v, u} : Set V3) {w}) := by
  have hne := coplanar_cross_dot x v u w hcop
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hcop' : ¬ Coplanar ({x, u, v, w} : Set V3) := by
      have he : ({x, u, v, w} : Set V3) = {x, v, u, w} := by
        ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [he]
    have hpos' : 0 < crossProduct ((u - x : V3) : Fin 3 → ℝ)
        ((v - x : V3) : Fin 3 → ℝ) ⬝ᵥ ((w - x : V3) : Fin 3 → ℝ) := by
      rw [← cross_anticomm, neg_dotProduct]
      linarith
    have heq := aff_gt_3_1_rep_cross_dot x u v w hcop' hpos'
    have hseteq : ({x, v, u} : Set V3) = {x, u, v} := by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
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
    exact isOpen_dot_neg_auto6 x _
  · have heq := aff_gt_3_1_rep_cross_dot x v u w hcop hpos
    rw [heq]
    exact isOpen_dot_pos_auto6 x _

/-- HOL Conforming.hl :1292-1332 `OPEN_TOPOLOGICAL_COMPONENT_YFAN`

HOL 原文：
```
!x:real^3 V E f.
FAN(x,V,E) /\ conforming_fan (x,V,E)/\ f IN topological_component_yfan (x,V,E)
          ==> open f
```

编码说明：`FAN(x,V,E)` ↔ `FAN x V E`；`conforming_fan (x,V,E)` ↔
`conformingFan x V E hfan`（需显式 `hfan`）；`open` ↔ `IsOpen`；
`topological_component_yfan` ↔ `topologicalComponentYfan`。

证明思路：由 `conformingFan` 取出 `conformingHalfSpaceFan` 与
`conformingBijectionFan`：对 `f ∈ topologicalComponentYfan` 取唯一面
`f'` 使 `f = dartsetLeadsIntoFan x V E f'`；再用
`conformingHalfSpaceFan` 把 `f` 写成有限族
`{affGt {x, y.1, y.2} {(f1Fan …).2} | y ∈ f'}` 的交
（`OPEN_INTERS`，Mathlib `Set.Finite.isOpen_sInter`）。每个成员由
`fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan` 换成
`affGt {x, y.1, y.2} {sigmaFan …}`，再用 `OPEN_AFF_GT_3_1` 及
`properties_fully_surrounded` 得开。

候选已有引理：
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- `conformingBijectionFan`（Kepler/Text/ConformingDefs.lean:104）
- `fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan`（本文件上文，HOL :1267）
- `OPEN_AFF_GT_3_1`（Kepler/Text/ConformingAuto5.lean:433）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `fan_not_collinear`（Kepler/Text/Fan.lean:342）
- `Set.Finite.isOpen_sInter`（Mathlib/Topology/Basic.lean:92）
- 缺口：HOL `FINITE_FACE_FAN`/`properties_of_elements_in_face_fully_surroundedfan`
  （fan.hl:2857）未移植，需用 `Hypermap.faceSet_finite` +
  `dartOfFan_eq_dart1_of_surrounded` 现场拼装 -/
theorem OPEN_TOPOLOGICAL_COMPONENT_YFAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    {f : Set V3} (hf : f ∈ topologicalComponentYfan x V E) :
    IsOpen f := by
  obtain ⟨hcard, hfan80, hbij, hhalf, _hsolid, _hdiag⟩ := hconf
  obtain ⟨f', ⟨hf'mem, hf'eq⟩, _⟩ := hbij f hf
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  obtain ⟨d, hd, hd_eq⟩ := H.face_representation hf'mem
  have hfin : f'.Finite := by rw [hd_eq]; exact H.face_finite d
  rw [hf'eq, hhalf f' hf'mem]
  refine hfin.isOpen_biInter (fun y hy => ?_)
  rw [fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan hfan hcard hfan80 hf'mem hy]
  refine isOpen_affGt_3_1_auto6 x y.1 y.2 (sigmaFan x V E y.1 y.2) ?_
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hyE : {y.1, y.2} ∈ E := by
    have hsub : f' ⊆ (↑H.darts : Set (V3 × V3)) := by
      rw [hd_eq]; exact H.face_subset_darts hd
    have hy_dart : y ∈ dart1OfFan V E := by
      have : y ∈ (↑H.darts : Set (V3 × V3)) := hsub hy
      rwa [hdarts] at this
    simpa [dart1OfFan] using hy_dart
  have hy2S : y.2 ∈ setOfEdge y.1 V E :=
    (properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp hyE
  have hσS : sigmaFan x V E y.1 y.2 ∈ setOfEdge y.1 V E :=
    sigma_fan_in_setOfEdge hfan hy2S
  have hσy1 : {sigmaFan x V E y.1 y.2, y.1} ∈ E := by
    have hy1σ : {y.1, sigmaFan x V E y.1 y.2} ∈ E :=
      (properties_of_setOfEdge_fan x V E y.1 (sigmaFan x V E y.1 y.2) hfan).mpr hσS
    rwa [show ({sigmaFan x V E y.1 y.2, y.1} : Set V3) =
        ({y.1, sigmaFan x V E y.1 y.2} : Set V3) from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have h80 := hfan80 y.1 y.2 hyE
  have hraw := properties_fully_surrounded (v := sigmaFan x V E y.1 y.2)
    (u := y.1) (w := y.2) hfan hσy1 hyE h80.1 h80.2
  have hset : ({x, sigmaFan x V E y.1 y.2, y.1, y.2} : Set V3) =
      ({x, y.1, y.2, sigmaFan x V E y.1 y.2} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rwa [hset] at hraw

/-- HOL Conforming.hl :1333-1341 `OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E f.
FAN(x,V,E) /\ conforming_fan (x,V,E)/\ f IN topological_component_yfan (x,V,E)
          ==> open (f INTER normball x r)
```

编码说明（缺口）：HOL 原文中 `r` 为自由变量（隐式全称量化），Lean 侧
显式写作参数 `(r : ℝ)`（同 `BOUNDED_INTER_BALL`，ConformingAuto5.lean:380）。
`open` ↔ `IsOpen`；`INTER` ↔ `∩`；`normball x r` ↔ `Metric.ball x r`。

证明思路：`f ∩ ball x r` 是两个开集之交：由
`OPEN_TOPOLOGICAL_COMPONENT_YFAN`（本文件上文）得 `f` 开，由
`isOpen_ball` 得球开，再用 `IsOpen.inter` 收口。

候选已有引理：
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN`（本文件上文，HOL :1292）
- `isOpen_ball`（Mathlib/Topology/MetricSpace/Pseudo/Metric.lean）
- `IsOpen.inter`（Mathlib/Topology/Defs/Basic.lean）
- 缺口：HOL `GSYM ball_eq_normball`/`OPEN_BALL` 由 Mathlib
  `isOpen_ball` 覆盖；`r` 的隐式量化在 Lean 侧显式化 -/
theorem OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL {x : V3} {V : Set V3}
    {E : Set (Set V3)} (r : ℝ)
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    {f : Set V3} (hf : f ∈ topologicalComponentYfan x V E) :
    IsOpen (f ∩ Metric.ball x r) := by
  exact (OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan hconf hf).inter Metric.isOpen_ball

/-- HOL Conforming.hl :1342-1351 `MEASURABLE_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL`

HOL 原文：
```
!x:real^3 V E r f.
FAN(x,V,E) /\ conforming_fan (x,V,E) /\ f IN topological_component_yfan (x,V,E)
          ==> measurable (f INTER normball x r)
```

编码说明：`measurable` ↔ `MeasurableSet`；`INTER` ↔ `∩`；`normball` ↔
`Metric.ball`；`FAN`/`conforming_fan`/`topological_component_yfan` 同前。

证明思路：由 `OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL`（本文件上文）
得 `f ∩ ball x r` 开，再用 `IsOpen.measurableSet` 得可测。（HOL 用
`MEASURABLE_OPEN`；`BOUNDED_INTER_BALL` 在该 HOL 版本中作为
`MEASURABLE_OPEN` 的前件之一。）

候选已有引理：
- `OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL`（本文件上文，HOL :1333）
- `BOUNDED_INTER_BALL`（Kepler/Text/ConformingAuto5.lean:380）
- `IsOpen.measurableSet`
  （Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:222）
- 缺口：无 -/
theorem MEASURABLE_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL {x : V3} {V : Set V3}
    {E : Set (Set V3)} (r : ℝ)
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan)
    {f : Set V3} (hf : f ∈ topologicalComponentYfan x V E) :
    MeasurableSet (f ∩ Metric.ball x r) := by
  exact (OPEN_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL r hfan hconf hf).measurableSet

private theorem radialNorm_inter_auto6 (r : ℝ) (v0 : V3) (P Q : Set V3)
    (hP : radialNorm r v0 P) (hQ : radialNorm r v0 Q) :
    radialNorm r v0 (P ∩ Q) := by
  refine ⟨Set.inter_subset_left.trans hP.1, ?_⟩
  intro u hu t ht htu
  exact ⟨hP.2 u hu.1 t ht htu, hQ.2 u hu.2 t ht htu⟩

private theorem RADIAL_UNIV_auto6 (r : ℝ) (x : V3) (hr : r > 0) :
    radialNorm r x (Set.univ ∩ Metric.ball x r) := by
  refine ⟨Set.inter_subset_right, ?_⟩
  intro u _ t ht htu
  refine ⟨Set.mem_univ _, ?_⟩
  have hsub : (x + t • u) - x = t • u := by abel
  rw [Metric.mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht]
  exact htu

private theorem RADIAL_INTERS_auto6 (r : ℝ) (v0 : V3) (f : Set (Set V3))
    (hfin : f.Finite) (h : ∀ s ∈ f, radialNorm r v0 (s ∩ Metric.ball v0 r))
    (hr : r > 0) :
    radialNorm r v0 (⋂₀ f ∩ Metric.ball v0 r) := by
  refine Set.Finite.induction_on
    (motive := fun s _ => (∀ t ∈ s, radialNorm r v0 (t ∩ Metric.ball v0 r)) →
      radialNorm r v0 (⋂₀ s ∩ Metric.ball v0 r))
    f hfin ?_ ?_ h
  · intro _
    rw [Set.sInter_empty]
    exact RADIAL_UNIV_auto6 r v0 hr
  · intro a s _ _ ih hins
    have ha : radialNorm r v0 (a ∩ Metric.ball v0 r) :=
      hins a (Set.mem_insert a s)
    have hsih : radialNorm r v0 (⋂₀ s ∩ Metric.ball v0 r) :=
      ih fun t ht => hins t (Set.mem_insert_of_mem a ht)
    have key : ⋂₀ (insert a s) ∩ Metric.ball v0 r
        = (a ∩ Metric.ball v0 r) ∩ (⋂₀ s ∩ Metric.ball v0 r) := by
      rw [Set.sInter_insert]
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    rw [key]
    exact radialNorm_inter_auto6 r v0 _ _ ha hsih

private theorem radialNorm_biInter_auto6 {α : Type*} (r : ℝ) (v0 : V3)
    (s : Set α) (g : α → Set V3)
    (hfin : s.Finite) (h : ∀ a ∈ s, radialNorm r v0 (g a ∩ Metric.ball v0 r))
    (hr : r > 0) :
    radialNorm r v0 ((⋂ a ∈ s, g a) ∩ Metric.ball v0 r) := by
  rw [← Set.sInter_image g s]
  exact RADIAL_INTERS_auto6 r v0 (g '' s) (hfin.image g)
    (fun t ht => by rcases ht with ⟨a, ha, rfl⟩; exact h a ha) hr

private theorem affGt_triple_star_auto6 {x u v w y : V3}
    (hdisj : Disjoint ({x, u, v} : Set V3) {w})
    (hy : y ∈ affGt ({x, u, v} : Set V3) {w}) (t : ℝ) (ht : 0 < t) :
    (1 - t) • x + t • y ∈ affGt ({x, u, v} : Set V3) {w} := by
  rw [AFF_GT_3_1 x u v w hdisj] at hy ⊢
  obtain ⟨t1, t2, t3, t4, ht4, hsum, hyeq⟩ := hy
  exact ⟨1 - t + t * t1, t * t2, t * t3, t * t4, mul_pos ht ht4,
    by nlinarith, by rw [hyeq]; module⟩

private theorem RADIAL_AFF_GT_3_1_auto6 (x u v w : V3) (r : ℝ)
    (hdisj : Disjoint ({x, u, v} : Set V3) {w}) (hr : r > 0) :
    radialNorm r x (affGt ({x, u, v} : Set V3) {w} ∩ Metric.ball x r) := by
  refine ⟨Set.inter_subset_right, ?_⟩
  intro u' hu' t ht htu'
  rw [Set.mem_inter_iff] at hu'
  obtain ⟨hgt, _hball⟩ := hu'
  refine ⟨?_, ?_⟩
  · have hstar := affGt_triple_star_auto6 hdisj hgt t ht
    have heq : (1 - t) • x + t • (x + u') = x + t • u' := by module
    rw [← heq]
    exact hstar
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : (x + t • u') - x = t • u' := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact htu'

/-- HOL Conforming.hl :1352-1395 `RADIAL_TOPOLOGICAL_COMPONENT_YFAN`

HOL 原文：
```
!x:real^3 V E r f.
FAN(x,V,E) /\ r> &0 /\ conforming_fan (x,V,E) /\ f IN topological_component_yfan (x,V,E)
          ==> radial_norm r x (f INTER normball x r)
```

编码说明：`radial_norm` ↔ `radialNorm`；`INTER` ↔ `∩`；`normball` ↔
`Metric.ball`；`FAN`/`conforming_fan`/`topological_component_yfan` 同前。

证明思路：与 `OPEN_TOPOLOGICAL_COMPONENT_YFAN` 同构：由
`conformingHalfSpaceFan` 把 `f` 写成有限族
`{affGt {x, y.1, y.2} {(f1Fan …).2} | y ∈ f'}` 的交，用
`fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan` 换成
`{sigmaFan …}` 形式，对每个成员用 `RADIAL_AFF_GT_3_1`
（前件 `notcoplanar_disjoints` + `properties_fully_surrounded`），
再用 `RADIAL_INTERS` 对有限交封闭。

候选已有引理：
- `RADIAL_INTERS`（Kepler/Text/ConformingAuto4.lean:345）
- `RADIAL_AFF_GT_3_1`（Kepler/Text/ConformingAuto4.lean:292）
- `fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan`（本文件上文，HOL :1267）
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- 缺口：HOL `FINITE_FACE_FAN` 未移植；`real^N` 一般维度未覆盖 -/
theorem RADIAL_TOPOLOGICAL_COMPONENT_YFAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (r : ℝ) (hfan : FAN x V E) (hr : r > 0)
    (hconf : conformingFan x V E hfan)
    {f : Set V3} (hf : f ∈ topologicalComponentYfan x V E) :
    radialNorm r x (f ∩ Metric.ball x r) := by
  obtain ⟨hcard, hfan80, hbij, hhalf, _hsolid, _hdiag⟩ := hconf
  obtain ⟨f', ⟨hf'mem, hf'eq⟩, _⟩ := hbij f hf
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  obtain ⟨d, hd, hd_eq⟩ := H.face_representation hf'mem
  have hfin : f'.Finite := by rw [hd_eq]; exact H.face_finite d
  rw [hf'eq, hhalf f' hf'mem]
  refine radialNorm_biInter_auto6 r x f'
    (fun y : V3 × V3 => affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2})
    hfin ?_ hr
  intro y hy
  rw [fully_surrounded_imp_aff_gt_3_1_of_dart_eq_fan hfan hcard hfan80 hf'mem hy]
  refine RADIAL_AFF_GT_3_1_auto6 x y.1 y.2 (sigmaFan x V E y.1 y.2) r ?_ hr
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hyE : {y.1, y.2} ∈ E := by
    have hsub : f' ⊆ (↑H.darts : Set (V3 × V3)) := by
      rw [hd_eq]; exact H.face_subset_darts hd
    have hy_dart : y ∈ dart1OfFan V E := by
      have : y ∈ (↑H.darts : Set (V3 × V3)) := hsub hy
      rwa [hdarts] at this
    simpa [dart1OfFan] using hy_dart
  have hy2S : y.2 ∈ setOfEdge y.1 V E :=
    (properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp hyE
  have hσS : sigmaFan x V E y.1 y.2 ∈ setOfEdge y.1 V E :=
    sigma_fan_in_setOfEdge hfan hy2S
  have hσy1 : {sigmaFan x V E y.1 y.2, y.1} ∈ E := by
    have hy1σ : {y.1, sigmaFan x V E y.1 y.2} ∈ E :=
      (properties_of_setOfEdge_fan x V E y.1 (sigmaFan x V E y.1 y.2) hfan).mpr hσS
    rwa [show ({sigmaFan x V E y.1 y.2, y.1} : Set V3) =
        ({y.1, sigmaFan x V E y.1 y.2} : Set V3) from by
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  have h80 := hfan80 y.1 y.2 hyE
  have hraw := properties_fully_surrounded (v := sigmaFan x V E y.1 y.2)
    (u := y.1) (w := y.2) hfan hσy1 hyE h80.1 h80.2
  have hset : ({x, sigmaFan x V E y.1 y.2, y.1, y.2} : Set V3) =
      ({x, y.1, y.2, sigmaFan x V E y.1 y.2} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset] at hraw
  exact (notcoplanar_disjoints x y.1 y.2 (sigmaFan x V E y.1 y.2) hraw).1

/-! ## 拓扑分量的有限性与 `sol` 可加性（Conforming.hl:1396-1455） -/

/-- HOL Conforming.hl :1396-1418 `FINITE_TOPOLOGICAL_COMPONENT_YFAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ fan80(x,V,E)
==> FINITE (topological_component_yfan (x,V,E))
```

编码说明：`FINITE` ↔ `Set.Finite`（`.Finite`）；`topological_component_yfan`
↔ `topologicalComponentYfan`；`FAN`/`fan80` 同前。

证明思路：由 `Hypermap.faceSet_finite` 得 `faceSet` 有限，用
`Set.Finite.image` 沿 `f ↦ dartsetLeadsIntoFan x V E f` 得
`{dartsetLeadsIntoFan x V E f | f ∈ faceSet}` 有限；再由
`dartset_leads_into_is_topological_component_yfan` 与 `version_JUTSTKG`
证明该像恰为 `topologicalComponentYfan x V E`。

候选已有引理：
- `Hypermap.faceSet_finite`（Kepler/Text/Hypermap.lean:1016）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `version_JUTSTKG`（Kepler/Text/ConformingAuto2.lean:114）
- `Set.Finite.image`（Mathlib/Data/Set/Finite/Basic.lean:566）
- 缺口：HOL `FINITE_HYPERMAP_ORBITS` 由 `faceSet_finite` 覆盖 -/
theorem FINITE_TOPOLOGICAL_COMPONENT_YFAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E) :
    (topologicalComponentYfan x V E).Finite := by
  have himg : ((fun d : V3 × V3 => dartLeadsInto x V E d.1 d.2) ''
      dart1OfFan V E).Finite :=
    (finite_dart1_fan hfan).image _
  refine himg.subset ?_
  intro U hU
  obtain ⟨v, u, huv, hUeq⟩ := JUTSTKG x V E U hfan hcard hfan80 hU
  exact ⟨(v, u), by simpa [dart1OfFan] using huv, hUeq⟩

/-- HOL Conforming.hl :1419-1434 `SUM_SOL_TOPOLOGICAL_COMPONENT_YFAN_EQ_SOL_UNIONS`

HOL 原文：
```
!x:real^3 V E.
FAN(x,V,E) /\ conforming_fan (x,V,E)
==>  sol x (UNIONS (topological_component_yfan (x,V,E)))=sum (topological_component_yfan (x,V,E)) (\f. sol x f)
```

编码说明：`sol` ↔ `Kepler.Geom.sol`；`UNIONS` ↔ `⋃₀`；HOL 集合和
`sum S g` ↔ finsum `∑ᶠ f ∈ S, g f`；`conforming_fan` ↔
`conformingFan x V E hfan`。

证明思路：对有限族 `topologicalComponentYfan x V E` 用 `SOL_UNIONS`：
由 `FINITE_TOPOLOGICAL_COMPONENT_YFAN` 得有限；取 `r = 1 > 0`，
由 `RADIAL_TOPOLOGICAL_COMPONENT_YFAN` 与
`MEASURABLE_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL` 得每个成员的
径向性与可测性；成员互不相交由连通分量非重叠
（HOL `CONNECTED_COMPONENT_NONOVERLAP`，Mathlib
`connectedComponentIn_eq`/`Disjoint`）得到。

候选已有引理：
- `SOL_UNIONS`（Kepler/Text/ConformingAuto5.lean:298）
- `FINITE_TOPOLOGICAL_COMPONENT_YFAN`（本文件上文，HOL :1396）
- `RADIAL_TOPOLOGICAL_COMPONENT_YFAN`（本文件上文，HOL :1352）
- `MEASURABLE_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL`（本文件上文，HOL :1342）
- `connectedComponentIn_eq`（Mathlib/Topology/Connected/Basic.lean:585）
- 缺口：HOL `CONNECTED_COMPONENT_NONOVERLAP` 无逐字对应，需由
  `connectedComponentIn_eq` 导出 `Disjoint` -/
private theorem disjoint_connectedComponentIn_auto6 {α : Type*} [TopologicalSpace α]
    {F : Set α} {b c : α}
    (h : connectedComponentIn F b ≠ connectedComponentIn F c) :
    Disjoint (connectedComponentIn F b) (connectedComponentIn F c) := by
  refine Set.disjoint_left.2 fun z hz1 hz2 => h ?_
  rw [connectedComponentIn_eq hz1, connectedComponentIn_eq hz2]

theorem SUM_SOL_TOPOLOGICAL_COMPONENT_YFAN_EQ_SOL_UNIONS {x : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) :
    sol x (⋃₀ topologicalComponentYfan x V E) =
      ∑ᶠ f ∈ topologicalComponentYfan x V E, sol x f := by
  have hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard := hconf.1
  have hfan80 : fan80 x V E := hconf.2.1
  refine SOL_UNIONS 1 x (topologicalComponentYfan x V E)
    (FINITE_TOPOLOGICAL_COMPONENT_YFAN hfan hcard hfan80)
    one_pos ?_ ?_
  · intro f hf
    exact ⟨MEASURABLE_TOPOLOGICAL_COMPONENT_YFAN_INTER_BALL 1 hfan hconf hf,
      RADIAL_TOPOLOGICAL_COMPONENT_YFAN 1 hfan one_pos hconf hf⟩
  · intro s hs t ht hst
    rw [topologicalComponentYfan] at hs ht
    obtain ⟨b, _hb, rfl⟩ := hs
    obtain ⟨c, _hc, rfl⟩ := ht
    exact disjoint_connectedComponentIn_auto6 hst

/-- HOL Conforming.hl :1435-1455 `UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN`

HOL 原文：
```
!x:real^3 V E.
  UNIONS (topological_component_yfan (x,V,E))= yfan(x,V,E)
```

编码说明：`UNIONS` ↔ `⋃₀`；`topological_component_yfan` ↔
`topologicalComponentYfan`；`yfan` ↔ `yfan`。无额外假设（HOL 亦无）。

证明思路：双向包含。⊆：任取 `y ∈ ⋃₀ topologicalComponentYfan`，
则 `y` 属于某连通分量 `connectedComponentIn (yfan x V E) b`，由
`connectedComponentIn_subset` 得 `y ∈ yfan`。⊇：对 `y ∈ yfan`，
取分量 `connectedComponentIn (yfan x V E) y`，由
`connectedComponentIn_eq`（或 `connectedComponentIn_self`/自反性）得
`y` 属于该分量，故属于并。

候选已有引理：
- `topologicalComponentYfan`（Kepler/Text/Fan.lean:199）
- `connectedComponentIn_subset`（Mathlib/Topology/Connected/Basic.lean:529）
- `connectedComponentIn_eq`（Mathlib/Topology/Connected/Basic.lean:585）
- `Set.mem_sUnion`（Mathlib/Data/Set/Lattice.lean）
- 缺口：无 -/
theorem UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN (x : V3) (V : Set V3)
    (E : Set (Set V3)) :
    ⋃₀ topologicalComponentYfan x V E = yfan x V E := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_sUnion] at hy
    obtain ⟨s, hs, hys⟩ := hy
    rw [topologicalComponentYfan] at hs
    obtain ⟨b, _hb, rfl⟩ := hs
    exact connectedComponentIn_subset _ _ hys
  · intro hy
    rw [Set.mem_sUnion]
    exact ⟨connectedComponentIn (yfan x V E) y, ⟨y, hy, rfl⟩,
      mem_connectedComponentIn hy⟩

/-! ## 面集上的 `sol` 和与 dart 分解（Conforming.hl:1456-1477） -/

/-- HOL Conforming.hl :1456-1469 `SUM_SOL_IN_FACE_SET_EQ_4PI`

HOL 原文：
```
!x:real^3 V E.
FAN(x,V,E) /\ conforming_fan (x,V,E)
==>  sum (face_set (hypermap1_of_fanx (x,V,E))) (\f. sol x (dartset_leads_into_fan x V E f))= &4 * pi
```

编码说明：HOL 集合和 `sum S g` ↔ finsum `∑ᶠ f ∈ S, g f`；
`face_set (hypermap1_of_fanx …)` ↔ `(hypermapOfFan x V E hfan).faceSet`；
`dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`；`sol` ↔
`Kepler.Geom.sol`；`&4 * pi` ↔ `4 * Real.pi`。

证明思路：由 `SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET` 把
面集和化为拓扑分量上的和，由
`SUM_SOL_TOPOLOGICAL_COMPONENT_YFAN_EQ_SOL_UNIONS` 化为
`sol x (⋃₀ topologicalComponentYfan x V E)`，再由
`UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN` 化为 `sol x (yfan x V E)`，
最后用 `SOLID_ANGLE_YFAN` 得 `4 * π`。

候选已有引理：
- `SUM_SOL_IN_TOPOLOGICAL_COMPONENET_EQ_IN_FACE_SET`
  （Kepler/Text/ConformingAuto5.lean:124）
- `SUM_SOL_TOPOLOGICAL_COMPONENT_YFAN_EQ_SOL_UNIONS`（本文件上文，HOL :1419）
- `UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN`（本文件上文，HOL :1435）
- `SOLID_ANGLE_YFAN`（Kepler/Text/ConformingAuto4.lean:551）
- 缺口：无 -/
theorem SUM_SOL_IN_FACE_SET_EQ_4PI {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) :
    (∑ᶠ f ∈ (hypermapOfFan x V E hfan).faceSet,
        sol x (dartsetLeadsIntoFan x V E f)) = 4 * Real.pi := by
  sorry

/-- HOL Conforming.hl :1470-1477 `DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET`

HOL 原文：
```
!(H:(A)hypermap). dart H = UNIONS (face_set H)/\ dart H = UNIONS (node_set H)/\ dart H = UNIONS (edge_set H)
```

编码说明：HOL `(A)hypermap` ↔ `Hypermap α`（Kepler/Text/Hypermap.lean:765）；
HOL `dart H`（dart *集合*）↔ `(↑H.darts : Set α)`（`H.darts : Finset α`）；
`face_set`/`node_set`/`edge_set` ↔ `H.faceSet`/`H.nodeSet`/`H.edgeSet`；
`UNIONS` ↔ `⋃₀`。

证明思路：三条等式分别是 `sUnion_setOfOrbits`（Hypermap.lean:1562）
在 `H.faceMap`、`H.nodeMap`、`H.edgeMap` 上的实例化，配合
`H.faceMap_permutes`/`H.nodeMap_permutes`/`H.edgeMap_permutes`
（即 HOL `lemma_partition` + `hypermap_lemma`）。

候选已有引理：
- `sUnion_setOfOrbits`（Kepler/Text/Hypermap.lean:1562）
- `Hypermap.faceMap_permutes`、`Hypermap.nodeMap_permutes`、
  `Hypermap.edgeMap_permutes`（Kepler/Text/Hypermap.lean:774-780）
- `Hypermap.faceSet`/`nodeSet`/`edgeSet`（Kepler/Text/Hypermap.lean:1002-1008）
- 缺口：无（该结果在本仓库已由 `sUnion_setOfOrbits` 覆盖，但按批次
  要求保留 HOL 名与公开陈述） -/
theorem DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET {α : Type*} [DecidableEq α]
    (H : Hypermap α) :
    (↑H.darts : Set α) = ⋃₀ H.faceSet ∧
      (↑H.darts : Set α) = ⋃₀ H.nodeSet ∧
      (↑H.darts : Set α) = ⋃₀ H.edgeSet := by
  sorry

end Kepler.Text
