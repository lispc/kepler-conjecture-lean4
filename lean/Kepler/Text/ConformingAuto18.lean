/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 18
(Conforming.hl:9066-10303).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 18, Conforming.hl:9066-10303):
- `U_INTER_U2_FANADD` (9066)
- `dartset_leads_into_fan_SUBSET_U` (9166)
- `rep_dartset_leads_into_fan_ds` (9350)
- `dartset_leads_into_fan_eq_fanadd` (9401)
- `conforming_bijection_fanadd` (9742)
- `RADIAL_AFF_GT_1_2` (9915)
- `NORMBALL_SUBSET` (9942)             [SKIPPED: Mathlib-general, see below]
- `RADIAL_NORM_CO` (9950)
- `tranf_eq_image_of_tran` (9988)
- `azim_fanadd_eq` (10117)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62); HOL
  `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `fan80` ↔
  `fan80` (Kepler/Text/Fan.lean:227); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`; HOL
  `CARD ds > 3` ↔ `3 < ds.ncard`.
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48 and the earlier conforming
  batches, `face_set (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, `face (hypermap1_of_fanx (x,V,E)) f`
  as `(hypermapOfFan x V E hfan).face f`, and `face_set (...) DELETE ds` as
  `(hypermapOfFan x V E hfan).faceSet \ {ds}`. Since `hypermapOfFan`
  (Kepler/Text/Fan.lean:1169) needs an explicit `hfan : FAN x V E`, every
  theorem that mentions it carries an extra explicit `(hfan : FAN x V E)`
  argument; theorems that also mention `face (hypermap1_of_fanx (x,V,E1))`
  carry a second extra explicit argument `(hfan1 : FAN x V E1)`. These are
  the only deviations from the HOL signatures (HOL's `hypermap_of_fan` is
  total).
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair darts
  `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/`pr3 y` ↦
  `y.1`/`y.2`. Consequently the HOL quadruples `(x,w,v,u)`, `(x,v,u,w)`,
  `(x,u,w,v)` contract to the pairs `(w,v)`, `(v,u)`, `(u,w)`, and
  `(x,v,w,sigma_fan x V E1 v w)` / `(x,w,v,sigma_fan x V E1 w v)` to the
  pairs `(v,w)` / `(w,v)`.
- HOL `f1_fan x V E` ↔ `f1Fan x V E` (Kepler/Text/ConformingDefs.lean:87).
- HOL `N_FAN` ↔ `nFan` (Kepler/Text/ConformingDefs.lean:204); HOL
  `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (Kepler/Text/ConformingDefs.lean:184).
- HOL `dartset_leads_into_fan` ↔ `dartsetLeadsIntoFan`
  (Kepler/Text/PlanarityComponent.lean:348); HOL
  `topological_component_yfan` ↔ `topologicalComponentYfan`
  (Kepler/Text/Fan.lean:199); HOL `azim_fan` ↔ `azimFan`
  (Kepler/Text/Fan.lean:177); HOL `aff_gt` ↔ `affGt`
  (Kepler/Geom/Aff.lean:39).
- HOL `UNIONS s` ↔ `⋃₀ s` (`Set.sUnion`); HOL `DELETE` ↔ `\`; HOL
  `INTER`/`SUBSET`/`UNION` ↔ `∩`/`⊆`/`∪`; HOL `{}` ↔ `∅`.
- The inner quantifier `(!E1. ... ==> conforming_fan (x,V,E1))` shadows the
  outer `E1`; as in `minimallyNonconformingFan`
  (Kepler/Text/ConformingDefs.lean:226) the inner variable is renamed `E2`
  and, because `conformingFan`/`nFan` need a `FAN` witness, encoded as
  `∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2), FAN x V E2 ∧ ... →
  conformingFan x V E2 hfan2` (the `FAN x V E2` conjunct is kept to align
  with the HOL antecedent). The binder `!v. v IN V ==> ...` inside that
  block is renamed `v'` to avoid shadowing the outer parameter `v`.
- HOL `tran` (Conforming.hl:4097) is NOT ported. It is
  `(\(x,y,z,w). (x,y,z,sigma_fan x V E1 y z))`: it only rewrites the 4th
  component of a dart. Since the repo's pair-dart encoding keeps
  `(pr2,pr3)` and drops the 4th component, `tran x V E1` is the IDENTITY on
  pair darts (same convention as Kepler/Text/ConformingAuto13.lean:55-68 and
  Kepler/Text/ConformingAuto14.lean:59-72). Hence in `tranf_eq_image_of_tran`
  the right-hand side `IMAGE (tran x V E1) ds0` collapses to `ds0`, and in
  `azim_fanadd_eq` the arguments `pr2 (tran x V E1 y)`, `pr3 (tran x V E1 y)`
  collapse to `y.1`, `y.2`.
- HOL `tranf x V E E1 ds = @f. ?y. f = face (hypermap1_of_fanx (x,V,E1))
  (tran x V E1 y) /\ y IN ds` (Conforming.hl:4101) is NOT ported. Its
  closest existing encoding is the Hilbert choice of the same existence
  predicate (with `tran` read as the identity, i.e. `f = face y /\ y ∈ ds`);
  since the existence is only available under the theorem's hypotheses,
  `tranf` is inlined in each statement as the totalized function
  `fun s => if h : (∃ g, ∃ z, g = face z ∧ z ∈ s) then Classical.choose h else ∅`
  bound by a local `let` (the `else` branch is unreachable under the
  hypotheses). No new definition is introduced. Same convention as
  `unique_tranf_fan` (Kepler/Text/ConformingAuto14.lean:171).
- `RADIAL_AFF_GT_1_2` is stated in HOL over `real^B` (arbitrary dimension).
  The repo's `radialNorm` (Kepler/Geom/Volume.lean:27) and `affGt`
  (Kepler/Geom/Aff.lean:39) are `V3`-specific, so the statement is
  specialised to `V3`; this is the only deviation. HOL `normball x r` ↔
  Mathlib `Metric.ball x r`; HOL `DISJOINT` ↔ `Disjoint`.
- `NORMBALL_SUBSET` (`!x r r'. r <= r' ==> normball x r SUBSET normball x r'`)
  is Mathlib-general and already provided by Mathlib as
  `Metric.ball_subset_ball`
  (Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:534,
  `ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂`). Per task
  instructions it is SKIPPED.
- Proof dependencies living in earlier conforming batches are NOT imported
  here (per the porting convention this batch imports only
  `PlanarityAuto16` and `ConformingDefs`); the proof sketches name them as
  candidates to be restated or imported by the worker pool.
- None of the remaining statements is Mathlib-general: each mentions the
  repo-specific `FAN`/`affGt`/`dartsetLeadsIntoFan`/`azimFan`/`radialNorm`
  vocabulary, so nothing else is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto15
import Kepler.Text.ConformingAuto17

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

/-! ## `U` 与补分量之并的交为空（Conforming.hl:9066-9350） -/

/-- 同一 `topologicalComponentYfan` 中两个相交的连通分量相等。 -/
private lemma tcy_eq_of_mem {x : V3} {V : Set V3} {E : Set (Set V3)}
    {A C : Set V3} (hA : A ∈ topologicalComponentYfan x V E)
    (hC : C ∈ topologicalComponentYfan x V E) {p : V3}
    (hpA : p ∈ A) (hpC : p ∈ C) : A = C := by
  rw [topologicalComponentYfan, Set.mem_setOf_eq] at hA hC
  obtain ⟨a, _, hAeq⟩ := hA
  obtain ⟨c, _, hCeq⟩ := hC
  rw [← hAeq] at hpA
  rw [← hCeq] at hpC
  rw [← hAeq, ← hCeq]
  exact (connectedComponentIn_eq hpA).trans (connectedComponentIn_eq hpC).symm

/-- `topologicalComponentYfan` 的每个成员都是 `yfan` 的子集。 -/
private lemma tcy_subset_yfan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {C : Set V3} (hC : C ∈ topologicalComponentYfan x V E) :
    C ⊆ yfan x V E := by
  rw [topologicalComponentYfan, Set.mem_setOf_eq] at hC
  obtain ⟨b, _, hCeq⟩ := hC
  rw [← hCeq]
  exact connectedComponentIn_subset (yfan x V E) b

/-- HOL Conforming.hl :9066-9165 `U_INTER_U2_FANADD`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
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
/\ U= dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}
==>
U INTER
 UNIONS
 (topological_component_yfan (x,V,E1) DELETE
  dartset_leads_into_fan x V E1 ds1 DELETE
  dartset_leads_into_fan x V E1 ds2) = {}
```

编码说明：`UNIONS` ↦ `⋃₀`；`DELETE` ↦ `\`；`INTER`/`SUBSET`/`UNION` ↦
`∩`/`⊆`/`∪`；内层 `!E1` 块改名 `E2`/`hfan2`（见文件头）。额外携带
`hfan`、`hfan1`。

证明思路：`FAN80_FANADD`/`YFANADD_AFF_GT` 给出 `yfan x V E` 被
`dartsetLeadsIntoFan ds1 ∪ ds2 ∪ affGt {x}{v,w}` 分解；由 `ds1`/`ds2`
的面集性（`ds1_in_face_set_fanadd`/`ds2_in_face_set_fanadd`）与
`dartset_leads_into_is_topological_component_yfan` 知补分量与 `U` 不交；
`aff_gt {x}{v,w}` 落入 `xfan` 之外（`AFF_GE_SUBSET_XFAN` +
`aff_gt_subset_aff_ge`），最后 `SET_TAC` 收口。

候选已有引理：
- `FAN80_FANADD`（Kepler/Text/ConformingAuto15.lean:404）
- `YFANADD_AFF_GT`（Kepler/Text/ConformingAuto15.lean:1014）
- `ds1_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:555）
- `ds2_in_face_set_fanadd`（Kepler/Text/ConformingAuto14.lean:623）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `AFF_GE_SUBSET_XFAN`（Kepler/Text/PlanarityAuto13.lean:255）
- `aff_gt_subset_aff_ge`（Kepler/Text/Planarity.lean:3878）
- `version_JUTSTKG`（Kepler/Text/ConformingAuto2.lean）
- 缺口：`version_JUTSTKG`、`hypermap_of_fan_rep`、`remark1_fan`、
  `CONNECTED_COMPONENT_EQ`、`UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN` 的
  具体 port 位置需由 worker 确认 -/
theorem U_INTER_U2_FANADD (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    U = dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} →
      U ∩ ⋃₀ ((topologicalComponentYfan x V E1 \
          {dartsetLeadsIntoFan x V E1 ds1}) \
          {dartsetLeadsIntoFan x V E1 ds2}) = ∅ := by
  intro h
  obtain ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w,
    hds1, hds2, hf10, hf20, hf30, hE1, _hconf, hU⟩ := h
  have hbig :
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
      E ∪ {({v, w} : Set V3)} = E1 :=
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
      hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30, hE1⟩
  have hcard1 : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E1).ncard :=
    add_edge_imp_card_set_edge_ge1_fan (x := x) (V := V) (E := E) (E1 := E1)
      (v := v) (w := w) hfan hcard hE1.symm
  have hfan801 : fan80 x V E1 :=
    FAN80_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1 hbig
  have hds1mem : ds1 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds1_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1.symm, hds2.symm,
        hf10, hf20, hf30, hE1⟩
  have hds2mem : ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds2_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2.symm,
        hf10, hf20, hf30, hE1⟩
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Or.inr rfl
  have hvV : v ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hwV : w ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hxV : x ∉ V := hfan1.2.2.2.1
  have hxv : x ≠ v := fun hh => hxV (hh ▸ hvV)
  have hxw : x ≠ w := fun hh => hxV (hh ▸ hwV)
  have hdis : Disjoint ({x} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxv, hxw⟩
  have haff : affGt ({x} : Set V3) ({v, w} : Set V3) ⊆ xfan x V E1 :=
    (aff_gt_subset_aff_ge hdis).trans (AFF_GE_SUBSET_XFAN x V E1 v w hvwE1)
  set A : Set V3 := dartsetLeadsIntoFan x V E1 ds1 with hAdef
  set B : Set V3 := dartsetLeadsIntoFan x V E1 ds2 with hBdef
  have hA : A ∈ topologicalComponentYfan x V E1 := by
    rw [hAdef]
    exact dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds1mem
  have hB : B ∈ topologicalComponentYfan x V E1 := by
    rw [hBdef]
    exact dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds2mem
  rw [hU]
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Set.mem_inter_iff, Set.mem_union, Set.mem_union] at hp
  obtain ⟨hpU, hpS⟩ := hp
  rw [Set.mem_sUnion] at hpS
  obtain ⟨C, hC, hpC⟩ := hpS
  rw [Set.mem_sdiff, Set.mem_sdiff] at hC
  obtain ⟨⟨hCmem, hCneA⟩, hCneB⟩ := hC
  have hCneA' : C ≠ A := by simpa using hCneA
  have hCneB' : C ≠ B := by simpa using hCneB
  rcases hpU with (hpA | hpB) | hpaff
  · exact hCneA' (tcy_eq_of_mem (A := A) (C := C) (p := p) hA hCmem hpA hpC).symm
  · exact hCneB' (tcy_eq_of_mem (A := B) (C := C) (p := p) hB hCmem hpB hpC).symm
  · have hCyfan : C ⊆ yfan x V E1 := tcy_subset_yfan hCmem
    have hp_yfan : p ∈ yfan x V E1 := hCyfan hpC
    have hp_xfan : p ∈ xfan x V E1 := haff hpaff
    rw [yfan, Set.mem_sdiff] at hp_yfan
    exact hp_yfan.2 hp_xfan

/-- HOL Conforming.hl :9166-9349 `dartset_leads_into_fan_SUBSET_U`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
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
/\ dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}=U
==> dartset_leads_into_fan x V E ds SUBSET U
```

编码说明：`SUBSET` ↦ `⊆`；假设中并集等式方向为 `... = U`。额外携带
`hfan`、`hfan1`。

证明思路：由 `dartset_leads_into_fanadd1`/`dartset_leads_into_fanadd2` 与
`STEP2_REDUCE_FAN` 把 `dartsetLeadsIntoFan x V E ds` 分解到
`dartsetLeadsIntoFan x V E1 ds1 ∪ ds2 ∪ affGt {x}{v,w}`，再用假设
`... = U` 及 `SET_TAC` 收口。

候选已有引理：
- `dartset_leads_into_fanadd1`（Kepler/Text/ConformingAuto15.lean:1154）
- `dartset_leads_into_fanadd2`（Kepler/Text/ConformingAuto16.lean:204）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- `dartset_leads_into_subset_yfan`
  （Kepler/Text/PlanarityComponent.lean:583）
- `exists_in_aff_gt_disjoint`（Kepler/Text/PlanarityAuto7.lean:387）
- 缺口：`STEP2_REDUCE_FAN`、`UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN` 的
  port 位置需由 worker 确认 -/
theorem dartset_leads_into_fan_SUBSET_U (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} = U →
      dartsetLeadsIntoFan x V E ds ⊆ U := by
  intro h
  obtain ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hconf, hUeq⟩ := h
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
      E ∪ {({v, w} : Set V3)} = E1 :=
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
      hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30, hE1⟩
  have hconf1 : conformingFan x V E1 hfan1 :=
    FANADD_CONFORMING x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30,
        hE1, hconf⟩
  have hopenU : IsOpen U :=
    dartset_leads_into_ds_open_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U
      hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30,
        hE1, hconf, hUeq⟩
  set A : Set V3 := dartsetLeadsIntoFan x V E1 ds1 with hAdef
  set B : Set V3 := dartsetLeadsIntoFan x V E1 ds2 with hBdef
  set C : Set V3 := affGt ({x} : Set V3) {v, w} with hCdef
  set D : Set V3 := dartsetLeadsIntoFan x V E ds with hDdef
  have hU' : U = A ∪ B ∪ C := hUeq.symm
  have hcard1 : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E1).ncard :=
    add_edge_imp_card_set_edge_ge1_fan hfan hcard hE1.symm
  have hfan801 : fan80 x V E1 :=
    FAN80_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1 hbase
  have hds1mem : ds1 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds1_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1.symm, hds2.symm,
        hf10, hf20, hf30, hE1⟩
  have hds2mem : ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet :=
    ds2_in_face_set_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2.symm,
        hf10, hf20, hf30, hE1⟩
  have hA : A ∈ topologicalComponentYfan x V E1 := by
    rw [hAdef]
    exact dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds1mem
  have hB : B ∈ topologicalComponentYfan x V E1 := by
    rw [hBdef]
    exact dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds2mem
  have hyfan : yfan x V E = yfan x V E1 ∪ C := by
    rw [hCdef]
    exact YFANADD_AFF_GT x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfan hfan1 hbase
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Or.inr rfl
  have hvV : v ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hwV : w ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hxV : x ∉ V := hfan1.2.2.2.1
  have hxv : x ≠ v := fun hh => hxV (hh ▸ hvV)
  have hxw : x ≠ w := fun hh => hxV (hh ▸ hwV)
  have hdis : Disjoint ({x} : Set V3) {v, w} := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxv, hxw⟩
  have hCxfan : C ⊆ xfan x V E1 := by
    rw [hCdef]
    exact (aff_gt_subset_aff_ge hdis).trans (AFF_GE_SUBSET_XFAN x V E1 v w hvwE1)
  have hCdisj : C ∩ yfan x V E1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rw [Set.mem_inter_iff] at hp
    obtain ⟨hpC, hpY⟩ := hp
    rw [yfan, Set.mem_sdiff] at hpY
    exact hpY.2 (hCxfan hpC)
  have hAU : A ⊆ U := by rw [hU']; intro z hz; exact Or.inl (Or.inl hz)
  have hBU : B ⊆ U := by rw [hU']; intro z hz; exact Or.inl (Or.inr hz)
  have hCU : C ⊆ U := by rw [hU']; intro z hz; exact Or.inr hz
  have hcover1 : ⋃₀ topologicalComponentYfan x V E1 = yfan x V E1 :=
    UNIONS_TOPOLOGICAL_COMPONENT_EQ_YFAN x V E1
  have hVE : yfan x V E \ U = ⋃₀ (topologicalComponentYfan x V E1 \ {A, B}) := by
    ext p
    constructor
    · intro hp
      rw [Set.mem_sdiff] at hp
      obtain ⟨hpE, hpU⟩ := hp
      rw [hyfan, Set.mem_union] at hpE
      rcases hpE with hpE1 | hpC
      · rw [← hcover1] at hpE1
        rw [Set.mem_sUnion] at hpE1 ⊢
        obtain ⟨s, hs, hps⟩ := hpE1
        refine ⟨s, ?_, hps⟩
        rw [Set.mem_sdiff]
        refine ⟨hs, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hsa => hpU (hAU (hsa ▸ hps)),
               fun hsb => hpU (hBU (hsb ▸ hps))⟩
      · exact absurd (hCU hpC) hpU
    · intro hp
      rw [Set.mem_sUnion] at hp
      obtain ⟨s, hs, hps⟩ := hp
      rw [Set.mem_sdiff] at hs
      obtain ⟨hs_tcy, hs_not⟩ := hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs_not
      obtain ⟨hsA, hsB⟩ := hs_not
      rw [Set.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [hyfan, Set.mem_union]
        left
        rw [← hcover1]
        exact Set.mem_sUnion.mpr ⟨s, hs_tcy, hps⟩
      · intro hpU
        rw [hU'] at hpU
        rcases hpU with (hpA | hpB) | hpC
        · exact hsA (tcy_eq_of_mem hs_tcy hA hps hpA)
        · exact hsB (tcy_eq_of_mem hs_tcy hB hps hpB)
        · have hpsY : p ∈ yfan x V E1 := by
            rw [← hcover1]; exact Set.mem_sUnion.mpr ⟨s, hs_tcy, hps⟩
          have hmem : p ∈ C ∩ yfan x V E1 := ⟨hpC, hpsY⟩
          rw [hCdisj] at hmem
          exact hmem
  have hopenV : IsOpen (yfan x V E \ U) := by
    rw [hVE]
    apply isOpen_sUnion
    intro s hs
    rw [Set.mem_sdiff] at hs
    exact OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan1 hconf1 hs.1
  have hD : D ∈ topologicalComponentYfan x V E := by
    rw [hDdef]
    exact dartset_leads_into_is_topological_component_yfan hfan hcard hfan80 hds
  have hDpre : IsPreconnected D := isPreconnected_of_mem_topologicalComponentYfan hD
  have hDsub : D ⊆ yfan x V E := by
    rw [hDdef]
    exact dartset_leads_into_subset_yfan hfan hcard hfan80 hds
  have hCsubD : C ⊆ D := by
    rw [hCdef, hDdef]
    exact STEP2_REDUCE_FAN hfan hcard hfan80 hds hds3 hsub hf1f2 hf2f3 hf3ne
      hf1v hf2u hf3w hvu huw hwv hsigma
  have hCne : C.Nonempty := by
    rw [hCdef]
    exact exists_in_aff_gt_disjoint x v w hdis
  have hDinterU : (D ∩ U).Nonempty := by
    obtain ⟨p, hpC⟩ := hCne
    exact ⟨p, hCsubD hpC, hCU hpC⟩
  have hcoverD : D ⊆ U ∪ (yfan x V E \ U) := by
    intro p hp
    rw [Set.mem_union]
    by_cases hpU : p ∈ U
    · exact Or.inl hpU
    · exact Or.inr ⟨hDsub hp, hpU⟩
  have hdisU : D ∩ (U ∩ (yfan x V E \ U)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    simp only [Set.mem_inter_iff, Set.mem_sdiff] at hp
    exact hp.2.2.2 hp.2.1
  rcases (isPreconnected_iff_subset_of_disjoint.mp hDpre) U (yfan x V E \ U)
      hopenU hopenV hcoverD hdisU with hDU | hDV
  · exact hDU
  · exfalso
    obtain ⟨p, hpD, hpU⟩ := hDinterU
    have hmem := hDV hpD
    rw [Set.mem_sdiff] at hmem
    exact hmem.2 hpU

/-- HOL Conforming.hl :9350-9400 `rep_dartset_leads_into_fan_ds`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U.
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
/\ dartset_leads_into_fan x V E1 ds1 UNION dartset_leads_into_fan x V E1 ds2 UNION aff_gt {x} {v, w}=U
==> dartset_leads_into_fan x V E ds =U
```

编码说明：结论 `dartset_leads_into_fan x V E ds = U`。额外携带
`hfan`、`hfan1`。

证明思路：由 `dartset_leads_into_fan_SUBSET_U` 得 `⊆ U`，由
`dartset_leads_into_fanadd2`/`dartset_leads_into_fanadd1` 与
`STEP2_REDUCE_FAN` 得反向包含，`Set.Subset.antisymm` 收口。

候选已有引理：
- `dartset_leads_into_fan_SUBSET_U`（本文件上文）
- `dartset_leads_into_fanadd1`（Kepler/Text/ConformingAuto15.lean:1154）
- `dartset_leads_into_fanadd2`（Kepler/Text/ConformingAuto16.lean:204）
- `dartset_leads_into_is_topological_component_yfan`
  （Kepler/Text/PlanarityComponent.lean:535）
- 缺口：`STEP2_REDUCE_FAN` 的 port 位置需由 worker 确认 -/
theorem rep_dartset_leads_into_fan_ds (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (U : Set V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
      affGt ({x} : Set V3) {v, w} = U →
      dartsetLeadsIntoFan x V E ds = U := by
  intro h
  obtain ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hconf, hUeq⟩ := h
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
      E ∪ {({v, w} : Set V3)} = E1 :=
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
      hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30, hE1⟩
  have hsubU : dartsetLeadsIntoFan x V E ds ⊆ U :=
    dartset_leads_into_fan_SUBSET_U x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 U
      hfan hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
        hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30,
        hE1, hconf, hUeq⟩
  have hA : dartsetLeadsIntoFan x V E1 ds1 ⊆ dartsetLeadsIntoFan x V E ds :=
    dartset_leads_into_fanadd1 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1 hbase
  have hB : dartsetLeadsIntoFan x V E1 ds2 ⊆ dartsetLeadsIntoFan x V E ds :=
    dartset_leads_into_fanadd2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
      hfan hfan1 hbase
  have hC : affGt ({x} : Set V3) {v, w} ⊆ dartsetLeadsIntoFan x V E ds :=
    STEP2_REDUCE_FAN hfan hcard hfan80 hds hds3 hsub hf1f2 hf2f3 hf3ne
      hf1v hf2u hf3w hvu huw hwv hsigma
  have hUsub : U ⊆ dartsetLeadsIntoFan x V E ds := by
    rw [← hUeq]
    intro p hp
    rcases hp with (hpA | hpB) | hpC
    · exact hA hpA
    · exact hB hpB
    · exact hC hpC
  exact Set.Subset.antisymm hsubU hUsub

/-! ## `tranf` 保持 `dartset_leads_into_fan`（Conforming.hl:9401-9741） -/

/-- `f1Fan` 与 `fFanPair` 在 `dart1OfFan` 上一致（本批本地副本）。 -/
private theorem f1Fan_eq_fFanPair_of_dart1_ca18 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    f1Fan x V E d = fFanPair x V E d := by
  have hba : ({d.2, d.1} : Set V3) ∈ E := by
    have h : ({d.1, d.2} : Set V3) ∈ E := hd
    rwa [Set.pair_comm] at h
  simp only [f1Fan, fFanPair]
  rw [inverse_sigma_fan_eq_inverse1 hfan hba]

/-- `f1Fan` 的迭代保持 `dart1OfFan`。 -/
private theorem f1Fan_iterate_mem_dart1OfFan_ca18 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    (f1Fan x V E)^[k] d ∈ dart1OfFan V E := by
  induction k with
  | zero => simpa using hd
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [f1Fan_eq_fFanPair_of_dart1_ca18 hfan ih]
      exact fFanPair_mem_dart1 hfan ih

/-- `hypermapOfFan` 的 `faceMap` 在 `dart1OfFan` 上等于 `f1Fan`。 -/
private theorem hypermapOfFan_faceMap_eq_f1Fan_ca18 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = f1Fan x V E d := by
  have hface : (hypermapOfFan x V E hfan).faceMap d = fFanPair x V E d := by
    unfold hypermapOfFan extendPerm
    simp only [Equiv.ofBijective_apply]
    unfold Kepler.Text.Fan.res
    rw [if_pos (by simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]
  rw [hface, f1Fan_eq_fFanPair_of_dart1_ca18 hfan hd]

/-- `hypermapOfFan` 的 `faceMap` 幂在 `dart1OfFan` 上等于 `f1Fan` 的迭代。 -/
private theorem hypermapOfFan_faceMap_pow_eq_iterate_ca18 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) (k : ℕ) :
    ((hypermapOfFan x V E hfan).faceMap ^ k) d = (f1Fan x V E)^[k] d := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, Function.iterate_succ_apply']
      exact hypermapOfFan_faceMap_eq_f1Fan_ca18 hfan
        (f1Fan_iterate_mem_dart1OfFan_ca18 hfan hd k)

/-- HOL Conforming.hl :9401-9741 `dartset_leads_into_fan_eq_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0.
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
/\ ds0 IN face_set (hypermap1_of_fanx (x,V,E)) DELETE ds
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))

==> dartset_leads_into_fan x V E1 (tranf x V E E1 ds0) = dartset_leads_into_fan x V E ds0
```

编码说明：`tranf` 未移植，按文件头内联为局部 `let`
（`fun s => if h : (∃ g, ∃ z, g = face z ∧ z ∈ s) then Classical.choose h
else ∅`，`tran` 读作恒等）；`face_set ... DELETE ds` ↦ `faceSet \ {ds}`。
额外携带 `hfan`、`hfan1`。

证明思路：`TRANF` 给出 `tranf ds0` 是 `E1` 的一个面；由
`DARTSET_LEADS_INTO_FAN`/`DART_LEADS_INTO` 与 `unique_dart_leads_into`
证明两个引导集相等；`ds0` 中任一 dart 的 `dartLeadsInto` 在 `E`/`E1` 下
相同（`INVARANT_SIGMA_FAN_ADD`），再对两个集合做外延与
`Set.Subset.antisymm`。

候选已有引理：
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `unique_tranf_fan`（Kepler/Text/ConformingAuto14.lean:171）
- `DARTSET_LEADS_INTO_FAN`（Kepler/Text/PlanarityComponent.lean）
- `DART_LEADS_INTO`（Kepler/Text/TopologyFan.lean）
- `unique_dart_leads_into`（Kepler/Text/TopologyFan.lean）
- `INVARANT_SIGMA_FAN_ADD`（Kepler/Text/ConformingAuto15.lean）
- `DOMAIN_TRANF_FACE_DELETE_DS`（Kepler/Text/ConformingAuto14.lean:1033）
- 缺口：`tran`/`tranf`（Conforming.hl:4097-4101）未移植 -/
theorem dartset_leads_into_fan_eq_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (ds0 : Set (V3 × V3)) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
      if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
          g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
      then Classical.choose h else ∅;
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
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) →
      dartsetLeadsIntoFan x V E1 (tranf ds0) =
        dartsetLeadsIntoFan x V E ds0 := by
  dsimp only
  rintro ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1, hds0mem, hmin⟩
  obtain ⟨hds0_faceSet, hds0_ne⟩ := hds0mem
  have hEsub : E ⊆ E1 := by rw [← hE1]; exact Set.subset_union_left
  have hcard1 : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E1).ncard :=
    add_edge_imp_card_set_edge_ge1_fan hfanC hcard hE1.symm
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Set.mem_union_right E (by simp)
  have hwvE1 : ({w, v} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Set.mem_union_right E (by simp [Set.pair_comm])
  have hbase : FAN x V E ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
      fan80 x V E ∧
      ds ∈ (hypermapOfFan x V E hfanC).faceSet ∧ 3 < ds.ncard ∧
      ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
      f1Fan x V E f1 = f2 ∧ f1Fan x V E f2 = f3 ∧ ¬ (f1Fan x V E f3 = f1) ∧
      f1.1 = v ∧ f2.1 = u ∧ f3.1 = w ∧
      ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
      sigmaFan x V E u w = v ∧ f1.2 = u ∧ f2.2 = w ∧
      (hypermapOfFan x V E1 hfan1).face (v, w) = ds1 ∧
      (hypermapOfFan x V E1 hfan1).face (w, v) = ds2 ∧
      f10 = (w, v) ∧ f20 = (v, u) ∧ f30 = (u, w) ∧
      E ∪ {({v, w} : Set V3)} = E1 :=
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
     hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30, hE1⟩
  have hfan801 : fan80 x V E1 :=
    FAN80_FANADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfanC hfan1 hbase
  have hconf1 : conformingFan x V E1 hfan1 :=
    FANADD_CONFORMING x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfanC hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
       hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30,
       hE1, hmin⟩
  have hbij1 : conformingBijectionFan x V E1 hfan1 := hconf1.2.2.1
  have hT := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0 hfanC hfan1
    ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
     hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm, hf10, hf20, hf30, hE1,
     ⟨hds0_faceSet, hds0_ne⟩⟩
  dsimp only at hT
  obtain ⟨y, hy_eq, hy_mem⟩ := hT
  have hdarts_E : (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfanC).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfanC).coe_toFinset
  obtain ⟨a, ha_darts, ha_face⟩ := (hypermapOfFan x V E hfanC).face_representation hds0_faceSet
  have hds0_subset : ds0 ⊆ (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) := by
    rw [ha_face]; exact (hypermapOfFan x V E hfanC).face_subset_darts ha_darts
  have hy_dart1_E : y ∈ dart1OfFan V E := by
    rw [← hdarts_E]; exact hds0_subset hy_mem
  have hy_dartOfFan : y ∈ dartOfFan V E := Or.inr hy_dart1_E
  have hface_y_ds0 : (hypermapOfFan x V E hfanC).face y = ds0 := by
    have hy_in : y ∈ (hypermapOfFan x V E hfanC).face a := by
      rw [← ha_face]; exact hy_mem
    exact ((hypermapOfFan x V E hfanC).face_eq_of_mem hy_in).symm.trans ha_face.symm
  have hy_not_ds : y ∉ ds := by
    intro hyds
    have hface_ds : ds = (hypermapOfFan x V E hfanC).face y :=
      identity_face_in_face_set hfanC hds hyds
    exact hds0_ne (hface_ds.trans hface_y_ds0).symm
  have hy1V : y.1 ∈ V := by
    have h : ({y.1, y.2} : Set V3) ∈ E := hy_dart1_E
    exact hfanC.1 (Set.mem_sUnion.mpr ⟨{y.1, y.2}, h, by simp⟩)
  have hdarts_E1 : (↑(hypermapOfFan x V E1 hfan1).darts : Set (V3 × V3)) = dart1OfFan V E1 := by
    change (↑(finite_dart1_fan hfan1).toFinset : Set (V3 × V3)) = dart1OfFan V E1
    exact (finite_dart1_fan hfan1).coe_toFinset
  have hy_dart1_E1 : y ∈ dart1OfFan V E1 := hEsub hy_dart1_E
  have hy_darts1 : y ∈ (hypermapOfFan x V E1 hfan1).darts := by
    change y ∈ (↑(hypermapOfFan x V E1 hfan1).darts : Set (V3 × V3))
    rw [hdarts_E1]; exact hy_dart1_E1
  have hpow : ∀ n : ℕ,
      ((hypermapOfFan x V E hfanC).faceMap ^ n) y =
      ((hypermapOfFan x V E1 hfan1).faceMap ^ n) y := by
    intro n
    rw [hypermapOfFan_faceMap_pow_eq_iterate_ca18 hfanC hy_dart1_E n,
        hypermapOfFan_faceMap_pow_eq_iterate_ca18 hfan1 hy_dart1_E1 n]
    exact TRAN_COMMUTATIVE_F1_FAN_POWER x V E E1 ds f1 f2 f3 v u w ds1 ds2
      f10 f20 f30 y n hfanC hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w,
       hds1.symm, hds2.symm, hf10, hf20, hf30, hE1, hy_not_ds, hy_dartOfFan⟩
  have hface_eq : (hypermapOfFan x V E1 hfan1).face y =
      (hypermapOfFan x V E hfanC).face y := by
    ext z
    simp only [Hypermap.face, orbitMap, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, (hpow n).trans hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, (hpow n).symm.trans hn⟩
  have hds0_eq_face1 : ds0 = (hypermapOfFan x V E1 hfan1).face y := by
    rw [← hface_y_ds0, hface_eq]
  have hds0_faceSet1 : ds0 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
    rw [hds0_eq_face1]
    exact (Hypermap.mem_darts_iff_face_mem (hypermapOfFan x V E1 hfan1) y).mp hy_darts1
  have htranf : (if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
        g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ ds0)
      then Classical.choose h else ∅) = ds0 :=
    hy_eq.trans hds0_eq_face1.symm
  rw [htranf]
  have hU1mem' : dartsetLeadsIntoFan x V E1 ds0 ∈ topologicalComponentYfan x V E1 :=
    dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds0_faceSet1
  have hU0mem' : dartsetLeadsIntoFan x V E ds0 ∈ topologicalComponentYfan x V E :=
    dartset_leads_into_is_topological_component_yfan hfanC hcard hfan80 hds0_faceSet
  have hxV : x ∉ V := hfan1.2.2.2.1
  have hvV : v ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hwV : w ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hxv : x ≠ v := fun hh => hxV (hh ▸ hvV)
  have hxw : x ≠ w := fun hh => hxV (hh ▸ hwV)
  have hdis_x : Disjoint ({x} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxv, hxw⟩
  have haff_xfan1 : affGt ({x} : Set V3) {v, w} ⊆ xfan x V E1 :=
    (aff_gt_subset_aff_ge hdis_x).trans (AFF_GE_SUBSET_XFAN x V E1 v w hvwE1)
  have hyfan_eq : yfan x V E = yfan x V E1 ∪ affGt ({x} : Set V3) {v, w} :=
    YFANADD_AFF_GT x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfanC hfan1 hbase
  have hU1_sub_U0 : dartsetLeadsIntoFan x V E1 ds0 ⊆
      dartsetLeadsIntoFan x V E ds0 := by
    rw [DARTSET_LEADS_INTO_FAN hfan1 hcard1 hfan801 hds0_faceSet1 y hy_mem,
        DARTSET_LEADS_INTO_FAN hfanC hcard hfan80 hds0_faceSet y hy_mem]
    have hsigma_y : sigmaFan x V E1 y.1 y.2 = sigmaFan x V E y.1 y.2 :=
      INVARANT_SIGMA_FAN_ADD x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 y
        hfanC hfan1
        ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
         hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w,
         hds1.symm, hds2.symm, hf10, hf20, hf30, hE1, hy_not_ds, hy_dartOfFan⟩
    have hrw_eq : ∀ r : ℝ,
        rwDartFan x V E1 (x, y.1, y.2, sigmaFan x V E1 y.1 y.2) r =
        rwDartFan x V E (x, y.1, y.2, sigmaFan x V E y.1 y.2) r := by
      intro r
      simp only [rwDartFan, wDartFan, hsigma_y]
      rw [if_pos (hcard1 y.1 hy1V), if_pos (hcard y.1 hy1V)]
    obtain ⟨h, hh0, hspec⟩ := dartLeadsInto_spec (v := y.1) (u := y.2) hfanC hy_dart1_E
    obtain ⟨h', hh0', hspec'⟩ := dartLeadsInto_spec (v := y.1) (u := y.2) hfan1 hy_dart1_E1
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
    obtain ⟨z, hz⟩ :=
      not_empty_rw_dart_fan (v := y.1) (u := y.2) hfanC hy_dart1_E hs'0 hs'lt_pi2
    have hz1 : z ∈ rwDartFan x V E1 (x, y.1, y.2, sigmaFan x V E1 y.1 y.2)
        (Real.cos s') := by
      rwa [hrw_eq]
    have hspecE := hspec s' z hs'0 hs'lt_h hz
    have hspecE1 := hspec' s' z hs'0 hs'lt_h' hz1
    have hyfan_sub : yfan x V E1 ⊆ yfan x V E := by
      intro p hp
      simp only [yfan, Set.mem_sdiff, Set.mem_univ, true_and] at hp ⊢
      intro hpE
      exact hp (by
        simp only [xfan, Set.mem_setOf_eq] at hpE ⊢
        obtain ⟨e, he, hpe⟩ := hpE
        exact ⟨e, by rw [← hE1]; exact Set.mem_union_left _ he, hpe⟩)
    rw [← hspecE1.2, ← hspecE.2]
    exact connectedComponentIn_mono z hyfan_sub
  have hds1_faceSet1 : ds1 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
    rw [← hds1]
    exact (Hypermap.mem_darts_iff_face_mem (hypermapOfFan x V E1 hfan1) (v, w)).mp (by
      change (v, w) ∈ (↑(hypermapOfFan x V E1 hfan1).darts : Set (V3 × V3))
      rw [hdarts_E1]; exact hvwE1)
  have hds2_faceSet1 : ds2 ∈ (hypermapOfFan x V E1 hfan1).faceSet := by
    rw [← hds2]
    exact (Hypermap.mem_darts_iff_face_mem (hypermapOfFan x V E1 hfan1) (w, v)).mp (by
      change (w, v) ∈ (↑(hypermapOfFan x V E1 hfan1).darts : Set (V3 × V3))
      rw [hdarts_E1]; exact hwvE1)
  have hds12 : ds1 ≠ ds2 :=
    disjoint_ds1_and_ds2 x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfanC hfan1
      ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
       hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm, hf10, hf20, hf30, hE1⟩
  have hU1pre : IsPreconnected (dartsetLeadsIntoFan x V E1 ds0) := by
    have hmem := hU1mem'
    rw [topologicalComponentYfan, Set.mem_setOf_eq] at hmem
    obtain ⟨c, hc, hceq⟩ := hmem
    rw [← hceq]
    exact isPreconnected_connectedComponentIn
  have hU1ne : (dartsetLeadsIntoFan x V E1 ds0).Nonempty := by
    have hmem := hU1mem'
    rw [topologicalComponentYfan, Set.mem_setOf_eq] at hmem
    obtain ⟨c, hc, hceq⟩ := hmem
    rw [← hceq]
    exact ⟨c, mem_connectedComponentIn hc⟩
  have hU0_disj_aff : dartsetLeadsIntoFan x V E ds0 ∩
      affGt ({x} : Set V3) {v, w} = ∅ := by
    by_contra hne
    obtain ⟨p, hpU0, hpaff⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hpds : p ∈ dartsetLeadsIntoFan x V E ds :=
      STEP2_REDUCE_FAN hfanC hcard hfan80 hds hds3 hsub hf1f2 hf2f3 hf3ne
        hf1v hf2u hf3w hvu huw hwv hsigma hpaff
    have hUdsmem : dartsetLeadsIntoFan x V E ds ∈ topologicalComponentYfan x V E :=
      dartset_leads_into_is_topological_component_yfan hfanC hcard hfan80 hds
    have hU0eqds : dartsetLeadsIntoFan x V E ds0 = dartsetLeadsIntoFan x V E ds :=
      tcy_eq_of_mem hU0mem' hUdsmem hpU0 hpds
    have hrep : dartsetLeadsIntoFan x V E ds =
        dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
          affGt ({x} : Set V3) {v, w} :=
      rep_dartset_leads_into_fan_ds x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30
        (dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
          affGt ({x} : Set V3) {v, w}) hfanC hfan1
        ⟨hfanC, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne, hf1v, hf2u,
         hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2, hf10, hf20, hf30,
         hE1, hmin, rfl⟩
    have hU0decomp : dartsetLeadsIntoFan x V E ds0 =
        dartsetLeadsIntoFan x V E1 ds1 ∪ dartsetLeadsIntoFan x V E1 ds2 ∪
          affGt ({x} : Set V3) {v, w} := hU0eqds.trans hrep
    set A : Set V3 := dartsetLeadsIntoFan x V E1 ds1 with hAdef
    set B : Set V3 := dartsetLeadsIntoFan x V E1 ds2 with hBdef
    have hAmem : A ∈ topologicalComponentYfan x V E1 := by
      rw [hAdef]
      exact dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds1_faceSet1
    have hBmem : B ∈ topologicalComponentYfan x V E1 := by
      rw [hBdef]
      exact dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hds2_faceSet1
    have hAopen : IsOpen A := OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan1 hconf1 hAmem
    have hBopen : IsOpen B := OPEN_TOPOLOGICAL_COMPONENT_YFAN hfan1 hconf1 hBmem
    have hdisjAB : Disjoint A B := by
      rw [Set.disjoint_left]
      intro q hqA hqB
      have hAB : A = B := tcy_eq_of_mem hAmem hBmem hqA hqB
      have huniq := hbij1 A hAmem
      obtain ⟨f, ⟨hfmem, hfeq⟩, hfuniq⟩ := huniq
      have hf1 : f = ds1 := (hfuniq ds1 ⟨hds1_faceSet1, hAdef⟩).symm
      have hf2 : f = ds2 := (hfuniq ds2 ⟨hds2_faceSet1, hAB.trans hBdef⟩).symm
      exact hds12 (hf1.symm.trans hf2)
    have hU1_sub_AB : dartsetLeadsIntoFan x V E1 ds0 ⊆ A ∪ B := by
      intro q hq
      have hqU0 : q ∈ dartsetLeadsIntoFan x V E ds0 := hU1_sub_U0 hq
      rw [hU0decomp] at hqU0
      rcases hqU0 with (hqA | hqB) | hqaff
      · exact Or.inl hqA
      · exact Or.inr hqB
      · exfalso
        have hq_yfan1 : q ∈ yfan x V E1 :=
          dartset_leads_into_subset_yfan hfan1 hcard1 hfan801 hds0_faceSet1 hq
        have hq_xfan1 : q ∈ xfan x V E1 := haff_xfan1 hqaff
        rw [yfan, Set.mem_sdiff] at hq_yfan1
        exact hq_yfan1.2 hq_xfan1
    have hU1_subA_or_B : dartsetLeadsIntoFan x V E1 ds0 ⊆ A ∨
        dartsetLeadsIntoFan x V E1 ds0 ⊆ B :=
      hU1pre.subset_or_subset hAopen hBopen hdisjAB hU1_sub_AB
    rcases hU1_subA_or_B with hsubA | hsubB
    · have hU1eqA : dartsetLeadsIntoFan x V E1 ds0 = A := by
        obtain ⟨q, hq⟩ := hU1ne
        exact tcy_eq_of_mem hU1mem' hAmem hq (hsubA hq)
      have hU1eq_ds1 : dartsetLeadsIntoFan x V E1 ds0 =
          dartsetLeadsIntoFan x V E1 ds1 := hU1eqA.trans hAdef
      have huniq := hbij1 (dartsetLeadsIntoFan x V E1 ds0) hU1mem'
      obtain ⟨f, ⟨hfmem, hfeq⟩, hfuniq⟩ := huniq
      have hf_ds0 : f = ds0 := (hfuniq ds0 ⟨hds0_faceSet1, rfl⟩).symm
      have hf_ds1 : f = ds1 := (hfuniq ds1 ⟨hds1_faceSet1, hU1eq_ds1⟩).symm
      have hds0_eq_ds1 : ds0 = ds1 := hf_ds0.symm.trans hf_ds1
      have hvw_ds1 : (v, w) ∈ ds1 := by
        rw [← hds1]; exact (hypermapOfFan x V E1 hfan1).mem_face_self (v, w)
      have hvw_not_ds0 : (v, w) ∉ ds0 := by
        intro hvw
        have h1 : (v, w) ∈ dart1OfFan V E := by
          have : (v, w) ∈ (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) :=
            hds0_subset hvw
          rwa [hdarts_E] at this
        have hvw_notE : ({v, w} : Set V3) ∉ E := by simpa [Set.pair_comm v w] using hwv
        exact hvw_notE (by simpa [dart1OfFan] using h1)
      have hmem0 : (v, w) ∈ ds0 := by rwa [← hds0_eq_ds1] at hvw_ds1
      exact hvw_not_ds0 hmem0
    · have hU1eqB : dartsetLeadsIntoFan x V E1 ds0 = B := by
        obtain ⟨q, hq⟩ := hU1ne
        exact tcy_eq_of_mem hU1mem' hBmem hq (hsubB hq)
      have hU1eq_ds2 : dartsetLeadsIntoFan x V E1 ds0 =
          dartsetLeadsIntoFan x V E1 ds2 := hU1eqB.trans hBdef
      have huniq := hbij1 (dartsetLeadsIntoFan x V E1 ds0) hU1mem'
      obtain ⟨f, ⟨hfmem, hfeq⟩, hfuniq⟩ := huniq
      have hf_ds0 : f = ds0 := (hfuniq ds0 ⟨hds0_faceSet1, rfl⟩).symm
      have hf_ds2 : f = ds2 := (hfuniq ds2 ⟨hds2_faceSet1, hU1eq_ds2⟩).symm
      have hds0_eq_ds2 : ds0 = ds2 := hf_ds0.symm.trans hf_ds2
      have hwv_ds2 : (w, v) ∈ ds2 := by
        rw [← hds2]; exact (hypermapOfFan x V E1 hfan1).mem_face_self (w, v)
      have hwv_not_ds0 : (w, v) ∉ ds0 := by
        intro hwv'
        have h1 : (w, v) ∈ dart1OfFan V E := by
          have : (w, v) ∈ (↑(hypermapOfFan x V E hfanC).darts : Set (V3 × V3)) :=
            hds0_subset hwv'
          rwa [hdarts_E] at this
        exact hwv (by simpa [dart1OfFan] using h1)
      have hmem0 : (w, v) ∈ ds0 := by rwa [← hds0_eq_ds2] at hwv_ds2
      exact hwv_not_ds0 hmem0
  have hU0_sub_yfan1 : dartsetLeadsIntoFan x V E ds0 ⊆ yfan x V E1 := by
    intro q hq
    have hq_yfan : q ∈ yfan x V E :=
      dartset_leads_into_subset_yfan hfanC hcard hfan80 hds0_faceSet hq
    rw [hyfan_eq] at hq_yfan
    rcases hq_yfan with hq1 | hqaff
    · exact hq1
    · exact absurd ⟨hq, hqaff⟩ (Set.eq_empty_iff_forall_notMem.mp hU0_disj_aff q)
  have hU0_sub_U1 : dartsetLeadsIntoFan x V E ds0 ⊆
      dartsetLeadsIntoFan x V E1 ds0 := by
    have hU0pre : IsPreconnected (dartsetLeadsIntoFan x V E ds0) := by
      have hmem := hU0mem'
      rw [topologicalComponentYfan, Set.mem_setOf_eq] at hmem
      obtain ⟨c, hc, hceq⟩ := hmem
      rw [← hceq]
      exact isPreconnected_connectedComponentIn
    obtain ⟨b, hbU1⟩ := hU1ne
    have hbU0 : b ∈ dartsetLeadsIntoFan x V E ds0 := hU1_sub_U0 hbU1
    have hsub_cc := hU0pre.subset_connectedComponentIn hbU0 hU0_sub_yfan1
    have hcc_eq : connectedComponentIn (yfan x V E1) b =
        dartsetLeadsIntoFan x V E1 ds0 := by
      have hmem := hU1mem'
      rw [topologicalComponentYfan, Set.mem_setOf_eq] at hmem
      obtain ⟨c, hc, hceq⟩ := hmem
      rw [← hceq]
      exact (connectedComponentIn_eq (by rw [hceq]; exact hbU1)).symm
    rw [hcc_eq] at hsub_cc
    exact hsub_cc
  exact Set.Subset.antisymm hU1_sub_U0 hU0_sub_U1

/-! ## fanadd 上的 conforming 双射（Conforming.hl:9742-9914） -/

/-- HOL Conforming.hl :9742-9914 `conforming_bijection_fanadd`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ (!E1. FAN(x,V,E1)  /\
         (!v. v IN V==>CARD (set_of_edge v V E1) > 1) /\
         fan80(x,V,E1)/\
         N_FAN(x,V,E1)< N_FAN(x,V,E) ==> conforming_fan (x,V,E1))
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
==>

!s. s IN topological_component_yfan (x,V,E) ==> (?!f. f IN face_set (hypermap1_of_fanx (x,V,E)) /\
                                                         s = dartset_leads_into_fan x V E f)
```

编码说明：`?!f. P f`（唯一存在）↦ `∃! f, P f`；内层 `!E1` 块改名
`E2`/`hfan2`（见文件头）；注意该块位置在 `fan80` 之后、`ds IN face_set`
之前。额外携带 `hfan`、`hfan1`。

证明思路：`version_JUTSTKG` 给出存在性，取 `f` 为 `s` 对应的面；
唯一性由 `FANADD_CONFORMING`（得 `E1` 的 conforming 性）与
`dartset_leads_into_fan_eq_fanadd`/`INJ_TRANF_FACE_DELETE_DS` 给出；
分 `y = ds` 与 `y ≠ ds` 讨论。

候选已有引理：
- `version_JUTSTKG`（Kepler/Text/ConformingAuto2.lean）
- `FANADD_CONFORMING`（Kepler/Text/ConformingAuto15.lean:588）
- `dartset_leads_into_fan_eq_fanadd`（本文件上文）
- `INJ_TRANF_FACE_DELETE_DS`（Kepler/Text/ConformingAuto14.lean:407）
- `DOMAIN_TRANF_FACE_DELETE_DS`（Kepler/Text/ConformingAuto14.lean:1033）
- `rep_dartset_leads_into_fan_ds`（本文件上文）
- 缺口：`STEP3_REDUCE_FAN`、`hypermap_of_fan_rep` 的 port 位置需确认 -/
theorem conforming_bijection_fanadd (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    FAN x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    fan80 x V E ∧
    (∀ (E2 : Set (Set V3)) (hfan2 : FAN x V E2),
      FAN x V E2 ∧
      (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E2).ncard) ∧
      fan80 x V E2 ∧
      nFan x V E2 hfan2 < nFan x V E hfan →
        conformingFan x V E2 hfan2) ∧
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
      ∀ s ∈ topologicalComponentYfan x V E,
        ∃! f : Set (V3 × V3),
          f ∈ (hypermapOfFan x V E hfan).faceSet ∧
            s = dartsetLeadsIntoFan x V E f := by
  intro h
  obtain ⟨hfanE, hcard, hfan80, hmin, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
    hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
    hf10, hf20, hf30, hE1⟩ := h
  have hconf1 : conformingFan x V E1 hfan1 :=
    FANADD_CONFORMING x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 hfanE hfan1
      ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
       hf10, hf20, hf30, hE1, hmin⟩
  have hbij1 : conformingBijectionFan x V E1 hfan1 := hconf1.2.2.1
  have hcard1 : ∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E1).ncard := hconf1.1
  have hfan801 : fan80 x V E1 := hconf1.2.1
  have hvwE1 : ({v, w} : Set V3) ∈ E1 := by
    rw [← hE1]; exact Set.mem_union_right E (by simp)
  have hvV : v ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hwV : w ∈ V := hfan1.1 (Set.mem_sUnion.mpr ⟨{v, w}, hvwE1, by simp⟩)
  have hxV : x ∉ V := hfan1.2.2.2.1
  have hxv : x ≠ v := fun hh => hxV (hh ▸ hvV)
  have hxw : x ≠ w := fun hh => hxV (hh ▸ hwV)
  have hdis_x : Disjoint ({x} : Set V3) ({v, w} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxv, hxw⟩
  have hxfan1 : affGt ({x} : Set V3) {v, w} ⊆ xfan x V E1 :=
    (aff_gt_subset_aff_ge (x := x) (v := v) (u := w) hdis_x).trans
      (AFF_GE_SUBSET_XFAN x V E1 v w hvwE1)
  have hstep2 : affGt ({x} : Set V3) {v, w} ⊆ dartsetLeadsIntoFan x V E ds :=
    STEP2_REDUCE_FAN hfanE hcard hfan80 hds hds3 hsub hf1f2 hf2f3 hf3ne
      hf1v hf2u hf3w hvu huw hwv hsigma
  have contra : ∀ z : Set (V3 × V3), z ∈ (hypermapOfFan x V E hfanE).faceSet →
      z ≠ ds →
      dartsetLeadsIntoFan x V E z = dartsetLeadsIntoFan x V E ds → False := by
    intro z hz hz_ne hz_eq
    have hT := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 z hfanE hfan1
      ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
       hf10, hf20, hf30, hE1, ⟨hz, hz_ne⟩⟩
    dsimp only at hT
    obtain ⟨y, hy_eq, _hy_mem⟩ := hT
    have hD := DOMAIN_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2
      f10 f20 f30 z hfanE hfan1
      ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
       hf10, hf20, hf30, hE1, ⟨hz, hz_ne⟩⟩
    dsimp only at hD
    rw [hy_eq] at hD
    have hmem1 : (hypermapOfFan x V E1 hfan1).face y ∈
        (hypermapOfFan x V E1 hfan1).faceSet :=
      hD.1.1
    have hL := dartset_leads_into_fan_eq_fanadd x V E E1 ds f1 f2 f3 v u w ds1 ds2
      f10 f20 f30 z hfanE hfan1
      ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
       hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
       hf10, hf20, hf30, hE1, ⟨hz, hz_ne⟩, hmin⟩
    dsimp only at hL
    rw [hy_eq] at hL
    have hyfan1 : dartsetLeadsIntoFan x V E1 ((hypermapOfFan x V E1 hfan1).face y) ⊆
        yfan x V E1 :=
      dartset_leads_into_subset_yfan hfan1 hcard1 hfan801 hmem1
    obtain ⟨p, hpaff⟩ := exists_in_aff_gt_disjoint x v w hdis_x
    have hp_ds : p ∈ dartsetLeadsIntoFan x V E ds := hstep2 hpaff
    have hds_eq_E1 : dartsetLeadsIntoFan x V E ds =
        dartsetLeadsIntoFan x V E1 ((hypermapOfFan x V E1 hfan1).face y) :=
      hz_eq.symm.trans hL.symm
    have hp_E1 : p ∈ dartsetLeadsIntoFan x V E1
        ((hypermapOfFan x V E1 hfan1).face y) := by
      rw [← hds_eq_E1]; exact hp_ds
    exact (hyfan1 hp_E1).2 (hxfan1 hpaff)
  have key : ∀ a b : Set (V3 × V3), a ∈ (hypermapOfFan x V E hfanE).faceSet →
      b ∈ (hypermapOfFan x V E hfanE).faceSet →
      dartsetLeadsIntoFan x V E a = dartsetLeadsIntoFan x V E b → a = b := by
    intro a b ha hb hab
    by_cases ha_ds : a = ds
    · rw [ha_ds] at hab ⊢
      by_cases hb_ds : b = ds
      · exact hb_ds.symm
      · exact (contra b hb hb_ds hab.symm).elim
    · by_cases hb_ds : b = ds
      · rw [hb_ds] at hab ⊢
        exact (contra a ha ha_ds hab).elim
      · have hT_a := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 a
            hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
           hf10, hf20, hf30, hE1, ⟨ha, ha_ds⟩⟩
        dsimp only at hT_a
        obtain ⟨ya, hya_eq, _hya_mem⟩ := hT_a
        have hT_b := TRANF x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 b
            hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hds1.symm, hds2.symm,
           hf10, hf20, hf30, hE1, ⟨hb, hb_ds⟩⟩
        dsimp only at hT_b
        obtain ⟨yb, hyb_eq, _hyb_mem⟩ := hT_b
        have hD_a := DOMAIN_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2
          f10 f20 f30 a hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
           hf10, hf20, hf30, hE1, ⟨ha, ha_ds⟩⟩
        dsimp only at hD_a
        rw [hya_eq] at hD_a
        have hmem_a1 : (hypermapOfFan x V E1 hfan1).face ya ∈
            (hypermapOfFan x V E1 hfan1).faceSet :=
          hD_a.1.1
        have hD_b := DOMAIN_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2
          f10 f20 f30 b hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
           hf10, hf20, hf30, hE1, ⟨hb, hb_ds⟩⟩
        dsimp only at hD_b
        rw [hyb_eq] at hD_b
        have hmem_b1 : (hypermapOfFan x V E1 hfan1).face yb ∈
            (hypermapOfFan x V E1 hfan1).faceSet :=
          hD_b.1.1
        have hL_a := dartset_leads_into_fan_eq_fanadd x V E E1 ds f1 f2 f3 v u w
          ds1 ds2 f10 f20 f30 a hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
           hf10, hf20, hf30, hE1, ⟨ha, ha_ds⟩, hmin⟩
        dsimp only at hL_a
        rw [hya_eq] at hL_a
        have hL_b := dartset_leads_into_fan_eq_fanadd x V E E1 ds f1 f2 f3 v u w
          ds1 ds2 f10 f20 f30 b hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w, hds1, hds2,
           hf10, hf20, hf30, hE1, ⟨hb, hb_ds⟩, hmin⟩
        dsimp only at hL_b
        rw [hyb_eq] at hL_b
        have hlead : dartsetLeadsIntoFan x V E1 ((hypermapOfFan x V E1 hfan1).face ya) =
            dartsetLeadsIntoFan x V E1 ((hypermapOfFan x V E1 hfan1).face yb) := by
          rw [hL_a, hL_b, hab]
        have htc : dartsetLeadsIntoFan x V E1
            ((hypermapOfFan x V E1 hfan1).face ya) ∈
            topologicalComponentYfan x V E1 :=
          dartset_leads_into_is_topological_component_yfan hfan1 hcard1 hfan801 hmem_a1
        obtain ⟨w0, ⟨_hw0_mem, _hw0_eq⟩, hw0_uniq⟩ :=
          hbij1 (dartsetLeadsIntoFan x V E1 ((hypermapOfFan x V E1 hfan1).face ya)) htc
        have hwa : (hypermapOfFan x V E1 hfan1).face ya = w0 :=
          hw0_uniq ((hypermapOfFan x V E1 hfan1).face ya) ⟨hmem_a1, rfl⟩
        have hwb : (hypermapOfFan x V E1 hfan1).face yb = w0 :=
          hw0_uniq ((hypermapOfFan x V E1 hfan1).face yb) ⟨hmem_b1, hlead⟩
        have hface_eq : (hypermapOfFan x V E1 hfan1).face ya =
            (hypermapOfFan x V E1 hfan1).face yb := hwa.trans hwb.symm
        have htranfeq : (if h : (∃ g : Set (V3 × V3), ∃ z' : V3 × V3,
              g = (hypermapOfFan x V E1 hfan1).face z' ∧ z' ∈ a)
            then Classical.choose h else ∅) =
            (if h : (∃ g : Set (V3 × V3), ∃ z' : V3 × V3,
              g = (hypermapOfFan x V E1 hfan1).face z' ∧ z' ∈ b)
            then Classical.choose h else ∅) :=
          hya_eq.trans (hface_eq.trans hyb_eq.symm)
        exact INJ_TRANF_FACE_DELETE_DS x V E E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20
          f30 a b hfanE hfan1
          ⟨hfanE, hcard, hfan80, hds, hds3, hsub, hf1f2, hf2f3, hf3ne,
           hf1v, hf2u, hf3w, hvu, huw, hwv, hsigma, hf1u, hf2w,
           hds1.symm, hds2.symm, hf10, hf20, hf30, hE1, ⟨ha, ha_ds⟩,
           ⟨hb, hb_ds⟩, htranfeq⟩
  intro s hs
  obtain ⟨f, hfmem, hfeq⟩ := version_JUTSTKG x V E s hfanE hcard hfan80 hs
  refine ⟨f, ⟨hfmem, hfeq.symm⟩, ?_⟩
  intro g ⟨hgmem, hgeq⟩
  exact key g f hgmem hfmem (hgeq.symm.trans hfeq.symm)

/-! ## `aff_gt` 与球的径向性（Conforming.hl:9915-9987） -/

/-- HOL Conforming.hl :9915-9941 `RADIAL_AFF_GT_1_2`

HOL 原文：
```
!x u v r.
     (DISJOINT {(x:real^B)} {u,v} /\ (r > &0) ) ==>
     radial_norm r x (aff_gt {x} {u,v} INTER normball x r)
```

编码说明（缺口）：HOL 在任意维 `real^B` 上陈述；repo 的 `radialNorm`
（Kepler/Geom/Volume.lean:27）与 `affGt`（Kepler/Geom/Aff.lean:39）均为
`V3` 专用，故特化到 `V3`。`normball x r` ↦ `Metric.ball x r`；
`DISJOINT` ↦ `Disjoint`。

证明思路：展开 `radialNorm`。包含性由 `affGt` 的显式刻画
`aff_gt_1_2` 与凸性/球凸性给出；径向封闭性由 `aff_gt_1_2` 的系数
`(t1,t2,t3)` 经线性缩放保持（`0 < t2, 0 < t3`），并用
`t * ‖u‖ < r` 与 `norm_smul` 控制球内。

候选已有引理：
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Metric.ball_subset_ball`
  （Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:534）
- `Convex`/`convex_ball`、`norm_smul`、`norm_add_le`（Mathlib）
- 缺口：HOL 原证明用的 `aff_normball`（vol1.hl）未移植 -/
theorem RADIAL_AFF_GT_1_2 (x u v : V3) (r : ℝ) :
    Disjoint ({x} : Set V3) {u, v} ∧ 0 < r →
      radialNorm r x (affGt ({x} : Set V3) {u, v} ∩ Metric.ball x r) := by
  sorry

/-- HOL Conforming.hl :9950-9987 `RADIAL_NORM_CO`

HOL 原文：
```
!r r' (x:real^3) C. r' <= r /\ &0< r' ==> (radial_norm r x (C INTER (normball x r))) ==> (radial_norm r' x (C INTER (normball x r')))
```

编码说明：`normball x r` ↦ `Metric.ball x r`；`radial_norm` ↦
`radialNorm`（Kepler/Geom/Volume.lean:27）。

证明思路：由 `NORMBALL_SUBSET`（Mathlib `Metric.ball_subset_ball`）得
`ball x r' ⊆ ball x r`，故包含性沿 `∩` 传递；径向封闭性对
`u ∈ C ∩ ball x r'` 与缩放系数 `t`，把 `t` 换成 `t * r / r'`，用
`r' ≤ r`、`0 < r'` 与 `norm_smul`/`inv` 计算验证新点仍在
`C ∩ ball x r'`。

候选已有引理：
- `radialNorm`（Kepler/Geom/Volume.lean:27）
- `Metric.ball_subset_ball`
  （Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:534）
- `Real.lt_inv`、`Real.mul_inv_cancel`、`norm_smul`（Mathlib）
- 缺口：`NORMBALL_SUBSET` 为 Mathlib 一般结论，已跳过 -/
theorem RADIAL_NORM_CO (r r' : ℝ) (x : V3) (C : Set V3) :
    r' ≤ r ∧ 0 < r' →
      radialNorm r x (C ∩ Metric.ball x r) →
        radialNorm r' x (C ∩ Metric.ball x r') := by
  sorry

/-! ## `tranf` 与 `tran` 的像及方位角不变性（Conforming.hl:9988-10303） -/

/-- HOL Conforming.hl :9988-10116 `tranf_eq_image_of_tran`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0.
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
/\ ds0 IN face_set(hypermap1_of_fanx (x,V,E)) DELETE ds
==> tranf x V E E1 ds0= IMAGE (tran x V E1) ds0
```

编码说明：`tran` 在点对编码下为恒等（见文件头），故
`IMAGE (tran x V E1) ds0 = ds0`；`tranf` 内联为局部 `let`（见文件头），
结论编码为 `tranf ds0 = (fun y => y) '' ds0`。额外携带 `hfan`、`hfan1`。

证明思路：`tranf ds0` 是 `E1` 的一个面，且其元素是 `ds0` 中元素在
`tran`（恒等）下的像；由 `DARTSET_LEADS_INTO_FAN` 与
`dartset_leads_into_fan_eq_fanadd` 证明 `face y ⊆ ds0` 及反向包含，
`Set.Subset.antisymm` 收口。

候选已有引理：
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `unique_tranf_fan`（Kepler/Text/ConformingAuto14.lean:171）
- `dartset_leads_into_fan_eq_fanadd`（本文件上文）
- `TRAN_COMMUTATIVE_F1_FAN`（Kepler/Text/ConformingAuto13.lean:570）
- `Set.image_id`（Mathlib）
- 缺口：`tran`/`tranf`（Conforming.hl:4097-4101）未移植 -/
theorem tranf_eq_image_of_tran (x : V3) (V : Set V3)
    (E E1 : Set (Set V3)) (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3)
    (v u w : V3) (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3)
    (ds0 : Set (V3 × V3)) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
    let tranf : Set (V3 × V3) → Set (V3 × V3) := fun s =>
      if h : (∃ g : Set (V3 × V3), ∃ z : V3 × V3,
          g = (hypermapOfFan x V E1 hfan1).face z ∧ z ∈ s)
      then Classical.choose h else ∅;
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
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} →
      tranf ds0 = (fun y : V3 × V3 => y) '' ds0 := by
  sorry

/-- HOL Conforming.hl :10117-10303 `azim_fanadd_eq`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 ds f1 f2 f3 v u w ds1 ds2 f10 f20 f30 ds0 y.
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
/\ ds0 IN face_set(hypermap1_of_fanx (x,V,E)) DELETE ds
/\ y IN ds0
==> azim_fan x V E1 (pr2 (tran x V E1 y)) (pr3 (tran x V E1 y))
= azim_fan x V E (pr2 y) (pr3 y)
```

编码说明：`tran` 在点对编码下为恒等（见文件头），故
`pr2 (tran x V E1 y)`/`pr3 (tran x V E1 y)` 编码为 `y.1`/`y.2`；
`azim_fan` ↦ `azimFan`；`face_set ... DELETE ds` ↦ `faceSet \ {ds}`。
额外携带 `hfan`、`hfan1`。

证明思路：由 `y ∈ ds0 ∈ faceSet \ {ds}` 得 `y` 是 `E` 的面 `ds0` 中
的 dart；`tran` 为恒等，故只需证 `E` 与 `E1 = E ∪ {{v,w}}` 在 `y` 处
的 `sigmaFan` 相同。分 `v' ∉ {v,w}`、`v' = v`、`v' = w` 讨论，分别用
`SIGMA_FAN_OF_FANADD1`、`SIGMA_FAN_OF_FANADD_AT_POINT4/5`；再由
`remark1_fan` 保证邻接非退化，`azimFan` 展开收口。

候选已有引理：
- `SIGMA_FAN_OF_FANADD1`（Kepler/Text/ConformingAuto10.lean:197）
- `SIGMA_FAN_OF_FANADD_AT_POINT4`
  （Kepler/Text/ConformingAuto11.lean:681）
- `SIGMA_FAN_OF_FANADD_AT_POINT5`
  （Kepler/Text/ConformingAuto11.lean:830）
- `EQ_PAIR_IMP_EQ_4_FAN`（Kepler/Text/PlanarityAuto15.lean:546）
- `TRANF`（Kepler/Text/ConformingAuto13.lean:145）
- `azimFan`（Kepler/Text/Fan.lean:177）
- 缺口：`tran`（Conforming.hl:4097）未移植；`remark1_fan` 的 port 位置
  需由 worker 确认 -/
theorem azim_fanadd_eq (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (ds : Set (V3 × V3)) (f1 f2 f3 : V3 × V3) (v u w : V3)
    (ds1 ds2 : Set (V3 × V3)) (f10 f20 f30 : V3 × V3) (ds0 : Set (V3 × V3))
    (y : V3 × V3) (hfan : FAN x V E) (hfan1 : FAN x V E1) :
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
    ds0 ∈ (hypermapOfFan x V E hfan).faceSet \ {ds} ∧
    y ∈ ds0 →
      azimFan x V E1 y.1 y.2 = azimFan x V E y.1 y.2 := by
  sorry

end Kepler.Text
