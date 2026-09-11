/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 16
(Conforming.hl:7119-8258).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 16, Conforming.hl:7119-8258):
- `dartset_leads_into_fanadd2` (7119)
- `INTERS_HALF_SPACE_DS_FANADD1` (7225)
- `inverse1_sigma_fan_FANADD` (7386)
- `aff_gt_eq_fanadd` (7464)
- `f2_EQ_F30_FANADD` (7565)
- `CONDITION_DART_IN_NODE` (7606)
- `INTERS_HALF_SPACE_DS_FANADD2` (7652)
- `lemmaINTERS_HALF_SPACE_DS_FANADD1` (8003)
- `lemmaINTERS_HALF_SPACE_DS_FANADD2` (8118)
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1` (8219)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL `CARD (set_of_edge v V E) > 1` ↔
  `1 < (setOfEdge v V E).ncard`; HOL `CARD ds > 3` ↔ `3 < ds.ncard`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and the earlier conforming
  batches, `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, `face (hypermap1_of_fanx (x,V,E)) f`
  as `(hypermapOfFan x V E hfan).face f`, `node_set (hypermap1_of_fanx
  (x,V,E))` as `(hypermapOfFan x V E hfan).nodeSet`, and `dart
  (hypermap1_of_fanx (x,V,E))` as `(hypermapOfFan x V E hfan).darts`.
  Since `hypermapOfFan` (Kepler/Text/Fan.lean:1169) needs an explicit
  `hfan : FAN x V E`, every theorem that mentions it carries an extra
  explicit `(hfan : FAN x V E)` argument; theorems that also mention
  `hypermapOfFan x V E1` carry a second extra explicit argument
  `(hfan1 : FAN x V E1)`. These are the only deviations from the HOL
  signatures (HOL's `hypermap_of_fan` is total).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to the
  pairs `(v,w)` / `(w,v)`.
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87);
  HOL `d1_fan (x,V,E)` ↔ `dart1OfFan V E` (Kepler/Text/Fan.lean:86).
- HOL `N_FAN` ↔ `nFan` (Kepler/Text/ConformingDefs.lean:204); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL `dart_leads_into` ↔
  `dartLeadsInto` (Kepler/Text/TopologyFan.lean:4179).
- HOL `INTERS {g y | y IN f}` ↔ `⋂ y ∈ f, g y` (`Set.iInter`);
  `U1 INTER s` ↔ `U1 ∩ s`.
- HOL `inverse1_sigma_fan` ↔ `inverse1SigmaFan` (Kepler/Text/Fan.lean:240);
  HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39).
- The inner quantifier `(!E1. ... ==> conforming_fan (x,V,E1))` shadows the
  outer `E1`; as in `FANADD_CONFORMING`
  (Kepler/Text/ConformingAuto15.lean:588) and `minimallyNonconformingFan`
  (Kepler/Text/ConformingDefs.lean:226) the inner variable is renamed `E2`
  and, because `conformingFan`/`nFan` need a `FAN` witness, encoded as
  `∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), FAN x V E2 ∧ ... →
  conformingFan x V E2 hfan2` (the `FAN x V E2` conjunct is kept to align
  with the HOL antecedent).
- `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1` is the only statement with a
  geometric (non-fan) flavour, but it still uses the repo-specific
  `azim`/`Coplanar`/`Collinear3`/`affGt` vocabulary, so it is not
  Mathlib-general. HOL `azim a x y z` ↔ `azim a x y z`
  (Kepler/Geom/Azim.lean:58); HOL `coplanar` ↔ `Coplanar`
  (Kepler/Geom/Coplanar.lean:23); HOL `collinear` ↔ `Collinear3`
  (Kepler/Geom/Azim.lean:43); HOL `aff s` (affine hull) ↔
  `affineSpan ℝ s` (Mathlib); HOL `DISJOINT s t` ↔ `Disjoint s t`.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`hypermapOfFan`/`sigmaFan`/`nFan`/`azim`/`affGt`
  vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto15

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## `dartset_leads_into_fan` 的第二个包含（Conforming.hl:7119-7224） -/

/-- 加边 `E1 = E ∪ {{v,w}}` 时，对不在新增边上的 dart `(s,v)`，
`dartLeadsInto` 关于 `yfan` 单调。与 `ConformingAuto15` 中的同名私有
引理同型，此处为 `dartset_leads_into_fanadd2` 复制一份。 -/
private lemma dartLeadsInto_add_edge_subset_ca16 {x : V3} {V : Set V3}
    {E E1 : Set (Set V3)} {v w s : V3}
    (hfan : FAN x V E) (hfan1 : FAN x V E1)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hvw_not : ({v, w} : Set V3) ∉ E)
    (hE1 : E ∪ {({v, w} : Set V3)} = E1)
    (hsvE : ({s, v} : Set V3) ∈ E) (hs_not : s ∉ ({v, w} : Set V3)) :
    dartLeadsInto x V E1 s v ⊆ dartLeadsInto x V E s v := by
  have hsvE1 : ({s, v} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Set.mem_union_left _ hsvE
  have hs_not_sUnion : s ∉ ⋃₀ ({({v, w} : Set V3)} : Set (Set V3)) := by
    rwa [Set.sUnion_singleton]
  have hsoe : setOfEdge s V E1 = setOfEdge s V E := by
    rw [← hE1]
    exact SET_OF_EDGE_INVARIANT s V E {({v, w} : Set V3)} hs_not_sUnion
  have hsigma : sigmaFan x V E1 s v = sigmaFan x V E s v :=
    SIGMA_FAN_OF_FANADD1 x V E E1 v w
      ⟨hfan, hfan1, hcard, hvw_not, hE1⟩ s v ⟨hsvE, hs_not⟩
  have hwdart : wDartFan x V E1 (x, s, v, sigmaFan x V E1 s v) =
      wDartFan x V E (x, s, v, sigmaFan x V E s v) := by
    simp only [wDartFan, hsoe, hsigma]
  have hrw : ∀ r : ℝ, rwDartFan x V E1 (x, s, v, sigmaFan x V E1 s v) r =
      rwDartFan x V E (x, s, v, sigmaFan x V E s v) r := by
    intro r
    simp only [rwDartFan, hwdart]
  obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec (v := s) (u := v) hfan hsvE
  obtain ⟨h', hh0', hspec'⟩ := dartLeadsInto_spec (v := s) (u := v) hfan1 hsvE1
  set s' : ℝ := min (min h h') (Real.pi / 2) / 2 with hs'def
  have hmin_pos : 0 < min (min h h') (Real.pi / 2) :=
    lt_min (lt_min hh0 hh0') (half_pos Real.pi_pos)
  have hs'0 : 0 < s' := by rw [hs'def]; exact div_pos hmin_pos (by norm_num)
  have hs'lt_h : s' < h := by
    rw [hs'def]
    have hle : min (min h h') (Real.pi / 2) ≤ h :=
      (min_le_left _ _).trans (min_le_left _ _)
    linarith [hmin_pos]
  have hs'lt_h' : s' < h' := by
    rw [hs'def]
    have hle : min (min h h') (Real.pi / 2) ≤ h' :=
      (min_le_left _ _).trans (min_le_right _ _)
    linarith [hmin_pos]
  have hs'lt_pi2 : s' < Real.pi / 2 := by
    rw [hs'def]
    have hle : min (min h h') (Real.pi / 2) ≤ Real.pi / 2 := min_le_right _ _
    linarith [hmin_pos, Real.pi_pos]
  obtain ⟨z, hz⟩ := not_empty_rw_dart_fan (v := s) (u := v) hfan hsvE hs'0 hs'lt_pi2
  have hz1 : z ∈ rwDartFan x V E1 (x, s, v, sigmaFan x V E1 s v) (Real.cos s') := by
    rwa [hrw]
  have hspecE := hspec s' z hs'0 hs'lt_h hz
  have hspecE1 := hspec' s' z hs'0 hs'lt_h' hz1
  have hxfan : xfan x V E ⊆ xfan x V E1 := by
    intro y hy
    simp only [xfan, Set.mem_setOf_eq] at hy ⊢
    obtain ⟨e, he, hye⟩ := hy
    exact ⟨e, by rw [← hE1]; exact Set.mem_union_left _ he, hye⟩
  have hyfan : yfan x V E1 ⊆ yfan x V E := by
    intro y hy
    simp only [yfan, Set.mem_sdiff, Set.mem_univ, true_and] at hy ⊢
    exact fun hyE => hy (hxfan hyE)
  rw [← hspecE1.2, ← hspecE.2]
  exact connectedComponentIn_mono z hyfan

/-- HOL Conforming.hl :7119-7224 `dartset_leads_into_fanadd2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> dartset_leads_into_fan x V E1 ds2 SUBSET  dartset_leads_into_fan x V E ds
```

编码说明：`dartset_leads_into_fan` ↦ `dartsetLeadsIntoFan`；结论
`dartsetLeadsIntoFan x V E1 ds2 ⊆ dartsetLeadsIntoFan x V E ds`。除结论用
`ds2` 外，与 `dartset_leads_into_fanadd1`（ConformingAuto15.lean:1154）同型。

证明思路：`FAN80_FANADD` 得 `fan80 x V E1`；`ds2_in_face_set_fanadd` 得
`ds2` 仍是 `faceSet`；`DARTSET_LEADS_INTO_FAN` 把 `dartsetLeadsIntoFan`
化为对应 `dartLeadsInto`；取公共 dart `(x,u,w,v) = f30`，用
`YFANADD_AFF_GT` 与 `connectedComponentIn_mono` 证明两拓扑分量相等。

候选已有引理：
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `DARTSET_LEADS_INTO_FAN`（Kepler/Text/PlanarityComponent.lean:375）
- `dartsetLeadsIntoFan`（Kepler/Text/PlanarityComponent.lean:348）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `dartset_leads_into_fanadd1`（Kepler/Text/ConformingAuto15.lean:1154）
- `connectedComponentIn_mono`（Mathlib，HOL `CONNECTED_COMPONENT_MONO`）
- 缺口：`hypermap_of_fan_rep`、`rw_dart_fan`/`not_empty_rw_dart_fan` 未移植 -/
theorem dartset_leads_into_fanadd2 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      dartsetLeadsIntoFan x V E1 ds2 ⊆ dartsetLeadsIntoFan x V E ds := by
  intro h
  have hfan80_1 : fan80 x V E1 :=
    FAN80_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1 h
  obtain ⟨hFAN, hcard, hfan80, hds, hds3, hf123, hf12, hf23, hf31, hf1v, hf2u,
    hf3w, hvu, huw, hwv, hsigma, hf1_2, hf2_2, hds1, hds2, hf10, hf20, hf30,
    hE1⟩ := h
  have huv : u ≠ v := (edge_ne_of_fan hfan hvu).symm
  have huw_ne : u ≠ w := edge_ne_of_fan hfan huw
  have hu_not : u ∉ ({v, w} : Set V3) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨huv, huw_ne⟩
  have hds2_mem : ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
    have hwvE1 : ({w, v} : Set V3) ∈ E1 := by
      rw [← hE1]
      exact Set.mem_union_right E (by simp [Set.pair_comm])
    have hdart1 : (w, v) ∈ dart1OfFan V E1 := hwvE1
    have hmem : (w, v) ∈ (hypermapOfFan x V E1 hfan1).darts := by
      show (w, v) ∈ (finite_dart1_fan hfan1).toFinset
      exact (finite_dart1_fan hfan1).mem_toFinset.mpr hdart1
    have hface : (hypermapOfFan x V E1 hfan1).face (w, v) ∈
        (hypermapOfFan x V E1 hfan1).faceSet :=
      (Hypermap.mem_darts_iff_face_mem _ _).mp hmem
    rw [← hds2]
    exact hface
  have hcard1 : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E1).ncard :=
    add_edge_imp_card_set_edge_ge1_fan hfan hcard hE1.symm
  have hrep : ds2 = ({f10, f20, f30} : Set (V3 × V3)) :=
    reperentation_of_ds2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hFAN, hcard, hfan80, hds, hds3, hf123, hf12, hf23, hf31, hf1v, hf2u,
       hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm, hf10, hf20, hf30,
       hE1⟩
  have hf30_ds2 : f30 ∈ ds2 := by
    rw [hrep]; simp
  have hf2_ds : f2 ∈ ds := hf123 (by simp)
  have hleadsE : dartsetLeadsIntoFan x V E ds = dartLeadsInto x V E u w := by
    have hh := DARTSET_LEADS_INTO_FAN hfan hcard hfan80 hds f2 hf2_ds
    simpa [hf2u, hf2_2] using hh
  have hleadsE1 : dartsetLeadsIntoFan x V E1 ds2 = dartLeadsInto x V E1 u w := by
    have hh := DARTSET_LEADS_INTO_FAN hfan1 hcard1 hfan80_1 hds2_mem f30 hf30_ds2
    simpa [hf30] using hh
  rw [hleadsE1, hleadsE]
  exact dartLeadsInto_add_edge_subset_ca16 hfan hfan1 hcard hwv
    (by rw [Set.pair_comm]; exact hE1) huw
    (by rw [Set.pair_comm]; exact hu_not)

/-! ## 半空间交与 `dartset_leads_into_fan`（Conforming.hl:7225-7385） -/

/-- HOL Conforming.hl :7225-7385 `INTERS_HALF_SPACE_DS_FANADD1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\ INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y) } |  y IN ds} =U1
==> U1 INTER aff_gt {x, v, w} {u} SUBSET dartset_leads_into_fan x V E1 ds2
```

编码说明：内层 `!E1` 与外层同名，改名为 `E2` 并携带见证
`hfan2 : FAN x V E2`（见文件头）；`INTERS {aff_gt {x, pr2 y, pr3 y}
{pr3 (f1_fan x V E y)} | y IN ds}` ↦
`⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}`；
`U1 INTER s` ↦ `U1 ∩ s`。

证明思路：`STEP3_REDUCE_FAN`/`FAN80_FANADD`/`YFANADD_AFF_GT` 建立 fanadd
结构；`ds2_in_face_set_fanadd` 得 `ds2 ∈ faceSet`；
`FANADD_CONFORMING` 给出 `conformingFan x V E1 hfan1`，其
`conformingHalfSpaceFan` 分量把 `dartsetLeadsIntoFan x V E1 ds2` 展开为
`⋂` 半空间交，再用假设 `U1 = ⋂ ...` 与三个 dart `f10/f20/f30` 的
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan` 逐个验证包含。

候选已有引理：
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `reperentation_of_ds2`（Kepler/Text/ConformingAuto12.lean:596）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`（Kepler/Text/ConformingAuto1.lean:166）
- `conformingHalfSpaceFan`（Kepler/Text/ConformingDefs.lean:121）
- 缺口：`hypermap_of_fan_rep`、`hypermap1_of_fanx` 未移植 -/
theorem INTERS_HALF_SPACE_DS_FANADD1 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    (⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}) = U1 →
      U1 ∩ affGt ({x, v, w} : Set V3) {u} ⊆ dartsetLeadsIntoFan x V E1 ds2 := by
  intro h
  obtain ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hmin, hInter⟩ := h
  have hbase : FAN x V E ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
      fan80 x V E ∧
      ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
      ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
      f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
      f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
      ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
      sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
      (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
      (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
      f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
      E ∪ {({v, w} : Set V3)} = E1 ∧
      (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
        FAN x V E2 ∧
        (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
        fan80 x V E2 ∧
        nFan x V E2 hfan2 < nFan x V E hfan →
          conformingFan x V E2 hfan2) :=
    ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
      hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20,
      hf30, hE1, hmin⟩
  have hconf : conformingFan x V E1 hfan1 :=
    FANADD_CONFORMING x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1 hbase
  obtain ⟨hcard1, hfan80_1, -, hhalf, -, -⟩ := hconf
  have hds2eq : ds2 = ({f10, f20, f30} : Set (V3 × V3)) :=
    reperentation_of_ds2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
        hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm, hf10, hf20,
        hf30, hE1⟩
  have hds2_face : ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds2_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hfanE, hcard, hfan80, hds, hds3, hfsub, hf1f2, hf2f3, hf3ne, hf1v,
        hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2.symm,
        hf10, hf20, hf30, hE1⟩
  have hEsub : E ⊆ E1 := by
    intro e he
    rw [← hE1]
    exact Set.mem_union_left _ he
  have hvuE1 : ({v, u} : Set V3) ∈ E1 := hEsub hvu
  have huwE1 : ({u, w} : Set V3) ∈ E1 := hEsub huw
  have hwvE1 : ({w, v} : Set V3) ∈ E1 := by
    rw [← hE1]
    exact Set.mem_union_right E (by simp [Set.pair_comm])
  have hvw_not : ({v, w} : Set V3) ∉ E :=
    fun hh => hwv (Set.pair_comm v w ▸ hh)
  have huv : u ≠ v := by
    intro huv
    have hvwE : ({v, w} : Set V3) ∈ E := by
      rw [← huv]
      exact huw
    exact hwv (Set.pair_comm v w ▸ hvwE)
  have huw_ne : u ≠ w := by
    intro huw_eq
    have hvwE : ({v, w} : Set V3) ∈ E := by
      rw [← huw_eq]
      exact hvu
    exact hwv (Set.pair_comm v w ▸ hvwE)
  have hu_not : u ∉ ({v, w} : Set V3) := by
    intro hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu
    · exact huv hu
    · exact huw_ne hu
  have hσ2 : sigmaFan x V E1 v u = w :=
    SIGMA_FAN_OF_FANADD_AT_POINT2 x V E E1 v u w
      ⟨hfan, hfan1, hvu, huw, hwv, hsigma, hfan80, hcard, hE1⟩
  have hσ3 : sigmaFan x V E1 w v = u :=
    SIGMA_FAN_OF_FANADD_AT_POINT3 x V E E1 v u w
      ⟨hfan, hfan1, hvu, huw, hwv, hsigma, hfan80, hcard, hE1⟩
  have hσ1_uw : sigmaFan x V E1 u w = sigmaFan x V E u w :=
    SIGMA_FAN_OF_FANADD1 x V E E1 v w
      ⟨hfan, hfan1, hcard, hvw_not, hE1⟩ u w ⟨huw, hu_not⟩
  have hfs_wv : affGt ({x, w, v} : Set V3) {sigmaFan x V E1 w v} =
      affGt ({x, w, v} : Set V3) {inverse1SigmaFan x V E1 v w} :=
    fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan (x := x) (V := V) (E := E1)
      (v := w) (w := v) hfan1 hwvE1 hcard1 hfan80_1
  have hfs_vu : affGt ({x, v, u} : Set V3) {sigmaFan x V E1 v u} =
      affGt ({x, v, u} : Set V3) {inverse1SigmaFan x V E1 u v} :=
    fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan (x := x) (V := V) (E := E1)
      (v := v) (w := u) hfan1 hvuE1 hcard1 hfan80_1
  have hfs_uw : affGt ({x, u, w} : Set V3) {sigmaFan x V E1 u w} =
      affGt ({x, u, w} : Set V3) {inverse1SigmaFan x V E1 w u} :=
    fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan (x := x) (V := V) (E := E1)
      (v := u) (w := w) hfan1 huwE1 hcard1 hfan80_1
  have hfs_uw_E : affGt ({x, u, w} : Set V3) {sigmaFan x V E u w} =
      affGt ({x, u, w} : Set V3) {inverse1SigmaFan x V E w u} :=
    fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan (x := x) (V := V) (E := E)
      (v := u) (w := w) hfan huw hcard hfan80
  have hset_wv : ({x, w, v} : Set V3) = ({x, v, w} : Set V3) := by
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hhalf ds2 hds2_face]
  intro z hz
  have hzU1 : z ∈ ⋂ y ∈ ds,
      affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2} := by
    rw [hInter]
    exact hz.1
  simp only [Set.mem_iInter] at hzU1
  simp only [Set.mem_iInter]
  intro y hy
  have hy' : y = f10 ∨ y = f20 ∨ y = f30 := by
    rw [hds2eq] at hy
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
  rcases hy' with rfl | rfl | rfl
  · rw [hf10]
    simp only [f1Fan]
    rw [← hfs_wv, hσ3, hset_wv]
    exact hz.2
  · rw [hf20]
    simp only [f1Fan]
    rw [← hfs_vu, hσ2]
    have hzE : z ∈ affGt ({x, f1.1, f1.2} : Set V3) {(f1Fan x V E f1).2} :=
      hzU1 f1 (hfsub (by simp))
    rw [hf1f2, hf1v, hf1u, hf2w] at hzE
    exact hzE
  · rw [hf30]
    simp only [f1Fan]
    rw [← hfs_uw, hσ1_uw, hsigma]
    have hzE : z ∈ affGt ({x, f2.1, f2.2} : Set V3) {(f1Fan x V E f2).2} :=
      hzU1 f2 (hfsub (by simp))
    rw [hf2u, hf2w] at hzE
    simp only [f1Fan] at hzE
    rw [hf2u, hf2w] at hzE
    rw [← hfs_uw_E, hsigma] at hzE
    exact hzE

/-! ## `inverse1_sigma_fan` 在 fanadd 下的不变性（Conforming.hl:7386-7463） -/

/-- HOL Conforming.hl :7386-7463 `inverse1_sigma_fan_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> inverse1_sigma_fan x V E1 w v =  inverse1_sigma_fan x V E w u
```

编码说明：`inverse1_sigma_fan` ↦ `inverse1SigmaFan`；结论
`inverse1SigmaFan x V E1 w v = inverse1SigmaFan x V E w u`。

证明思路：由 `INVERSE1_SIGMA_FAN` 在 `E1` 处实例化得
`inverse1SigmaFan x V E1 w v` 满足 `sigmaFan x V E1 w (inverse1SigmaFan
x V E1 w v) = v`；用 `SIGMA_FAN_OF_FANADD1`（对不在 `{v,w}` 中的边不变）
把 `sigmaFan x V E1 w ·` 换成 `sigmaFan x V E w ·`，再对
`inverse1SigmaFan x V E w u` 用 `INVERSE1_SIGMA_FAN` 的唯一性
（`MONO_SIGMA_FAN`）得到相等。

候选已有引理：
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `inverse1SigmaFan`（Kepler/Text/Fan.lean:240）
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `SIGMA_FAN_OF_FANADD_AT_POINT6`（Kepler/Text/ConformingAuto11.lean:987）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- 缺口：`MONO_SIGMA_FAN`（HOL fan.hl）未以该名移植 -/
theorem inverse1_sigma_fan_FANADD (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      inverse1SigmaFan x V E1 w v = inverse1SigmaFan x V E w u := by
  sorry

/-! ## `aff_gt` 的相等（Conforming.hl:7464-7564） -/

/-- HOL Conforming.hl :7464-7564 `aff_gt_eq_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
==> aff_gt {x, w, inverse1_sigma_fan x V E1 w v} {v} = aff_gt {x, w, inverse1_sigma_fan x V E w u} {u}
```

编码说明：`aff_gt` ↦ `affGt`，`inverse1_sigma_fan` ↦ `inverse1SigmaFan`；
结论 `affGt ({x, w, inverse1SigmaFan x V E1 w v} : Set V3) {v} =
affGt ({x, w, inverse1SigmaFan x V E w u} : Set V3) {u}`。

证明思路：`inverse1_sigma_fan_FANADD` 给出两个逆 σ 点相等；再用
`FAN80_FANADD` 得 `fan80 x V E1`，`properties_fully_surrounded` 给出
四点非共面，`NOT_COPLANAR_NOT_COLLINEAR` 与
`cross_dot_fully_surrounded_fan` 建立叉积定向，最后
`aff_gt_3_1_rep_cross_dot` 把两个 `affGt` 化为同一定向半空间。

候选已有引理：
- `inverse1_sigma_fan_FANADD`（本文件上文）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- 缺口：`NOT_COPLANAR_NOT_COLLINEAR`、`remark1_fan` 未以该名移植 -/
theorem aff_gt_eq_fanadd (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      affGt ({x, w, inverse1SigmaFan x V E1 w v} : Set V3) {v} =
        affGt ({x, w, inverse1SigmaFan x V E w u} : Set V3) {u} := by
  sorry

/-! ## `f30 = f2`（Conforming.hl:7565-7605） -/

/-- HOL Conforming.hl :7565-7605 `f2_EQ_F30_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ f30=(x,u,w,v)
/\ E UNION {{v,w}}= E1
==> f30= f2
```

编码说明：`(x,w,v,u)=f10`、`(x,v,u,w)=f20`、`f30=(x,u,w,v)` 分别 ↦
`f10 = (w, v)`、`f20 = (v, u)`、`f30 = (u, w)`；结论 `f30 = f2`。

证明思路：`f1`、`f2`、`f3` 是 `ds` 中沿 `f1_fan` 的三连 dart；
`f2 = (u, w)`，而 `f30 = (u, w)` 是 `sigma_fan x V E u w = v` 对应的
四元组。由 `EQ_PAIR_IMP_EQ_4_FAN`/`pr2`/`pr3` 与 `d1_fan` 展开得
`f2 = (x, pr2 f2, pr3 f2, sigma_fan x V E (pr2 f2) (pr3 f2))`，再由
假设 `f30 = (x,u,w,v)` 与 `f2.1 = u`、`f2.2 = w` 直接代入。

候选已有引理：
- `EQ_PAIR_IMP_EQ_4_FAN`（Kepler/Text/PlanarityAuto15.lean:546）
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- `STEP3_REDUCE_FAN`（Kepler/Text/ConformingAuto9.lean:298）
- 缺口：`hypermap_of_fan_rep` 未移植 -/
theorem f2_EQ_F30_FANADD (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 →
      f30 = f2 := by
  sorry

/-! ## node 对 dart 的封闭性（Conforming.hl:7606-7651） -/

/-- HOL Conforming.hl :7606-7651 `CONDITION_DART_IN_NODE`

HOL 原文：
```
!x V E f y y1. FAN (x,V,E)
/\(!v. v IN V ==> CARD (set_of_edge v V E) > 1)
/\ f IN (node_set (hypermap1_of_fanx (x,V,E)) )
/\ y IN f
/\ y1 IN d1_fan(x,V,E)
/\ pr2 y1= pr2 y
==> y1 IN f
```

编码说明：`node_set (hypermap1_of_fanx (x,V,E))` ↦
`(hypermapOfFan x V E hfan).nodeSet`；`d1_fan (x,V,E)` ↦ `dart1OfFan V E`；
`pr2 y1 = pr2 y` ↦ `y1.1 = y.1`；额外携带 `hfan`。

证明思路：`dartOfFan_eq_dart1_of_surrounded` 消去孤立点；`node_subset_dart_fan`
给 `f ⊆ dart1OfFan`；`rep_node_set_fan` 把 `y` 的 node 表示为
`{f1_fan^i y}`，再对 `y1` 用 `ORBITS_EQ_SET_EDGE_FAN` 找到同一
`setOfEdge` 中的幂次 `i`，由 `power_map_points` 得到 `y1 ∈ f`。

候选已有引理：
- `rep_node_set_fan`（Kepler/Text/ConformingAuto7.lean:240）
- `nodeSet`（Kepler/Text/Hypermap.lean:1005）
- `node`（Kepler/Text/Hypermap.lean:843）
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `ORBITS_EQ_SET_EDGE_FAN`、`set_of_orbits_points_fan`、`node_subset_dart_fan`
  未以该名移植（缺口） -/
theorem CONDITION_DART_IN_NODE (x : V3) (V : Set V3) (E : Set (Set V3))
    (f : Set (V3 × V3)) (y y1 : V3 × V3) (hfan : FAN x V E) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    f ∈ (hypermapOfFan x V E hfan).nodeSet ∧
    y ∈ f ∧
    y1 ∈ dart1OfFan V E ∧
    y1.1 = y.1 →
      y1 ∈ f := by
  sorry

/-! ## 半空间交与 `dartset_leads_into_fan`（Conforming.hl:7652-8002） -/

/-- HOL Conforming.hl :7652-8002 `INTERS_HALF_SPACE_DS_FANADD2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\ INTERS {aff_gt {x, pr2 y, pr3 y} {pr3 (f1_fan x V E y) } |  y IN ds} =U1
==> U1 INTER aff_gt {x, v, w} {sigma_fan x V E v u} SUBSET dartset_leads_into_fan x V E1 ds1
```

编码说明：内层 `!E1` 改名为 `E2`（携带 `hfan2`）；`INTERS` ↦ `⋂`；
结论 `U1 ∩ affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ⊆
dartsetLeadsIntoFan x V E1 ds1`。

证明思路：与 `INTERS_HALF_SPACE_DS_FANADD1` 同型但目标是 `ds1`；
`ds1_in_face_set_fanadd` 给 `ds1 ∈ faceSet`；`FANADD_CONFORMING` 的
`conformingHalfSpaceFan` 分量展开 `dartsetLeadsIntoFan x V E1 ds1`；
把 `ds1` 的元素分三类（`f10`、`f20`、`f30` 或落在旧面内），分别用
`SIGMA_FAN_OF_FANADD_AT_POINT1/2/3`、`inverse1_sigma_fan_FANADD`、
`aff_gt_eq_fanadd`、`CONDITION_DART_IN_NODE` 验证半空间包含。

候选已有引理：
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `CONDITION_DART_IN_NODE`（本文件上文）
- `aff_gt_eq_fanadd`（本文件上文）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- 缺口：`hypermap_of_fan_rep`、`DOMAIN_TRANF_FACE_DELETE_DS` 的完全移植 -/
theorem INTERS_HALF_SPACE_DS_FANADD2 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    (⋂ y ∈ ds, affGt ({x, y.1, y.2} : Set V3) {(f1Fan x V E y).2}) = U1 →
      U1 ∩ affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ⊆
        dartsetLeadsIntoFan x V E1 ds1 := by
  sorry

/-! ## 四个半空间交与 `dartset_leads_into_fan`（Conforming.hl:8003-8117） -/

/-- HOL Conforming.hl :8003-8117 `lemmaINTERS_HALF_SPACE_DS_FANADD1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\  aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}=U1
==> U1 INTER aff_gt {x, v, w} {u} SUBSET dartset_leads_into_fan x V E1 ds2
```

编码说明：内层 `!E1` 改名为 `E2`（携带 `hfan2`）；假设中的四个 `aff_gt`
交 ↦ `affGt ... ∩ affGt ... ∩ affGt ... ∩ affGt ... = U1`；
结论 `U1 ∩ affGt ({x, v, w} : Set V3) {u} ⊆ dartsetLeadsIntoFan x V E1 ds2`。

证明思路：`FANADD_CONFORMING` 的 `conformingHalfSpaceFan` 分量把
`dartsetLeadsIntoFan x V E1 ds2` 展开为 `⋂` 半空间交；由假设 `U1` 是
四个半空间交，`reperentation_of_ds2` 把 `ds2` 的元素归约为
`f10/f20/f30`，再用 `SIGMA_FAN_OF_FANADD_AT_POINT2/3`、
`INVERSE1_SIGMA_FAN`、`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`
逐项证明 `U1 ∩ aff_gt {x,v,w} {u}` 含于各半空间。

候选已有引理：
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `reperentation_of_ds2`（Kepler/Text/ConformingAuto12.lean:596）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`（Kepler/Text/ConformingAuto1.lean:166）
- `SIGMA_FAN_OF_FANADD_AT_POINT2`（Kepler/Text/ConformingAuto10.lean:510）
- `SIGMA_FAN_OF_FANADD_AT_POINT3`（Kepler/Text/ConformingAuto11.lean:554）
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- 缺口：`hypermap_of_fan_rep`、`remark1_fan` 未以该名移植 -/
theorem lemmaINTERS_HALF_SPACE_DS_FANADD1 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} = U1 →
      U1 ∩ affGt ({x, v, w} : Set V3) {u} ⊆ dartsetLeadsIntoFan x V E1 ds2 := by
  sorry

/-- HOL Conforming.hl :8118-8218 `lemmaINTERS_HALF_SPACE_DS_FANADD2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U1.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
/\ {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\  pr2 f1 =v /\  pr2 f2 =u /\  pr2 f3=w
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v /\ pr3 f1= u /\ pr3 f2= w
/\ face (hypermap1_of_fanx (x,V,E1)) (x,v,w,sigma_fan x V E1 v w)= ds1
/\ face (hypermap1_of_fanx (x,V,E1)) (x,w,v,sigma_fan x V E1 w v)=ds2
/\ (x,w,v,u)=f10
/\ (x,v,u,w)=f20
/\ (x,u,w,v)=f30
/\ E UNION {{v,w}}= E1
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
/\  aff_gt {x, u, w} {v } INTER aff_gt {x, v,u} {sigma_fan x V E v u } INTER aff_gt {x, v, sigma_fan x V E v u } {w} INTER aff_gt {x, sigma_fan x V E v u,w} {v}=U1
==> U1 INTER aff_gt {x, v, w} {sigma_fan x V E v u} SUBSET dartset_leads_into_fan x V E1 ds1
```

编码说明：内层 `!E1` 改名为 `E2`（携带 `hfan2`）；结论
`U1 ∩ affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ⊆
dartsetLeadsIntoFan x V E1 ds1`。

证明思路：`FANADD_CONFORMING` 的 `conformingHalfSpaceFan` 分量展开
`dartsetLeadsIntoFan x V E1 ds1`；`SIGMA_FAN_OF_FANADD_AT_POINT1` 给出
`sigmaFan x V E1 v w = sigmaFan x V E v u`；`ds1` 中的 dart 或为
`(v,w)`，或落在旧面内；用
`fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`、
`inter_aff_gt_3_1_is_aff_gt_1_3`、`aff_gt_1_3_subset_dart_leads_into_fan`
与 `dartLeadsInto` 的单调性完成包含。

候选已有引理：
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `SIGMA_FAN_OF_FANADD_AT_POINT1`（Kepler/Text/ConformingAuto10.lean:399）
- `inter_aff_gt_3_1_is_aff_gt_1_3`（Kepler/Text/PlanarityAuto12.lean:418）
- `aff_gt_1_3_subset_dart_leads_into_fan`（Kepler/Text/PlanarityAuto12.lean:270）
- `fully_surrounded_imp_aff_gt_3_1_of_edge_eq_fan`（Kepler/Text/ConformingAuto1.lean:166）
- 缺口：`hypermap_of_fan_rep`、`properties_fully_surrounded` 的完全移植 -/
theorem lemmaINTERS_HALF_SPACE_DS_FANADD2 (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U1 : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard ∧
    ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
    f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
    f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
    (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
    (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
    f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
    E ∪ {({v, w} : Set V3)} = E1 ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
    affGt ({x, u, w} : Set V3) {v} ∩
      affGt ({x, v, u} : Set V3) {sigmaFan x V E v u} ∩
      affGt ({x, v, sigmaFan x V E v u} : Set V3) {w} ∩
      affGt ({x, sigmaFan x V E v u, w} : Set V3) {v} = U1 →
      U1 ∩ affGt ({x, v, w} : Set V3) {sigmaFan x V E v u} ⊆
        dartsetLeadsIntoFan x V E1 ds1 := by
  sorry

/-! ## 几何半空间包含（Conforming.hl:8219-8258） -/

/-- HOL Conforming.hl :8219-8258 `aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1`

HOL 原文：
```
!a x y z w:real^3.
azim a x y z < pi
/\ &0< azim a x y z
/\ azim a x y w < pi
/\ &0< azim a x y w
/\ DISJOINT {a, x} {w}
/\ ~collinear {a, x, w}
/\ ~coplanar {a, x, y, z}
==> aff_gt {a,x,y}{z} INTER aff{a,x,w} SUBSET aff_gt {a,x} {w}
```

编码说明：`azim` ↦ `azim`（Kepler/Geom/Azim.lean:58）；`DISJOINT` ↦
`Disjoint`；`collinear` ↦ `Collinear3`；`coplanar` ↦ `Coplanar`；
`aff s`（仿射包）↦ `(affineSpan ℝ s : Set V3)`；`aff_gt` ↦ `affGt`。
结论 `affGt ({a, x, y} : Set V3) {z} ∩
(affineSpan ℝ ({a, x, w} : Set V3) : Set V3) ⊆ affGt ({a, x} : Set V3) {w}`。

证明思路：由 `~coplanar {a,x,y,z}` 得 `~collinear {a,x,z}` 与
`~collinear {a,x,y}`（`notcoplanar_imp_notcollinear_fan`）；用
`cross_dot_fully_surrounded_fan` 与 `aff_gt_3_1_rep_cross_dot` 把
`affGt {a,x,y}{z}` 化为定向叉积条件；把 `aff{a,x,w}` 展开为
`u % a + v % x + w' % w`（`AFF_GT_2_1`），代入后用
`cross_dot_fully_surrounded_fan` 对 `w` 的符号与
`REAL_LT_LCANCEL_IMP` 得到 `affGt {a,x}{w}`。

候选已有引理：
- `notcoplanar_imp_notcollinear_fan`（Kepler/Text/PlanarityNotCut.lean:2298）
- `cross_dot_fully_surrounded_fan`（Kepler/Text/Planarity.lean:2860）
- `aff_gt_3_1_rep_cross_dot`（Kepler/Text/PlanarityAuto12.lean:723）
- `aff_gt_2_1_cross_dotl_4point`（Kepler/Text/PlanarityAuto10.lean:177）
- `affGt`（Kepler/Geom/Aff.lean:39）
- `azim`（Kepler/Geom/Azim.lean:58）
- `Coplanar`（Kepler/Geom/Coplanar.lean:23）
- `Collinear3`（Kepler/Geom/Azim.lean:43）
- 缺口：`AFF_GT_2_1`/`AFFINE_HULL_3` 的展开在 Mathlib 中对应
  `affineSpan`/`AffineSubspace` 的坐标刻画，需手工桥接 -/
theorem aff_gt_3_1_INTER_aff_SUBSET_aff_gt_2_1 (a x y z w : V3) :
    azim a x y z < Real.pi ∧
    0 < azim a x y z ∧
    azim a x y w < Real.pi ∧
    0 < azim a x y w ∧
    Disjoint ({a, x} : Set V3) {w} ∧
    ¬ Collinear3 a x w ∧
    ¬ Coplanar ({a, x, y, z} : Set V3) →
      affGt ({a, x, y} : Set V3) {z} ∩
        (affineSpan ℝ ({a, x, w} : Set V3) : Set V3) ⊆
          affGt ({a, x} : Set V3) {w} := by
  sorry

end Kepler.Text
