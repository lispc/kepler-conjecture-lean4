/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 8
(Conforming.hl:1719-2099).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 8, Conforming.hl:1719-2099):
- `SUM_CARD_FACE_NODE_DART_FAN` (1719)
- `nonconformin_fan_imp_n_fan_ge0` (1806)
- `nonconformin_fan_imp_exist_face_gt_3` (1819)
- `exists_face_in_face_set` (1843)
- `identity_face_in_face_set` (1857)
- `condition_f1_eq_fan` (1868)
- `nonconformin_fan_imp_exist_3point_in_face` (1880)
- `condition_aff_gt_subset_yfan` (2009)
- `segment_subset_aff_gt_union` (2031)
- `SEGMENT_CONNECTED` (2094)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48, `face_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).faceSet`, `node_set` as
  `(hypermapOfFan x V E hfan).nodeSet`, `dart` (the dart set) as
  `(hypermapOfFan x V E hfan).darts` (a `Finset`), and `face
  (hypermap1_of_fanx (x,V,E)) f` as `(hypermapOfFan x V E hfan).face f`,
  with pair darts `V3 × V3`. Because `hypermapOfFan` requires an explicit
  `hfan : FAN x V E` witness (HOL's `hypermap_of_fan` is total), every
  face/node-set theorem below carries an extra explicit `(hfan : FAN x V E)`
  argument; this is the only deviation from the HOL signatures. In
  particular `exists_face_in_face_set`/`identity_face_in_face_set` (whose
  HOL statements have no `FAN` hypothesis) acquire this argument as well.
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`; HOL `f1_fan` ↔ `f1Fan` (ConformingDefs.lean:87);
  HOL `sigma_fan` ↔ `sigmaFan` (Fan.lean:67); HOL `fan80` ↔ `fan80`
  (Fan.lean:227); HOL `N_FAN` ↔ `nFan` (ConformingDefs.lean:204).
- HOL `conforming_fan (x,V,E)` ↔ `conformingFan x V E hfan`
  (ConformingDefs.lean:184); HOL `CARD f` ↔ `f.ncard` (`f` a set), HOL
  `CARD (dart H)` ↔ `H.darts.card`.
- HOL `aff_gt` ↔ `affGt` (Kepler/Geom/Aff.lean:39); HOL `yfan`/`xfan` ↔
  `yfan`/`xfan` (Kepler/Text/Fan.lean:158/154); HOL `coplanar` ↔
  `Coplanar` (Kepler/Geom/Coplanar.lean:23); HOL `segment [a,b]` ↔
  `segment ℝ a b` (Mathlib closed segment, cf. PlanarityAuto7.lean:34).
- HOL `sum (f) g` (set sum) ↔ `∑ᶠ y ∈ f, g y` (finsum); HOL `&2 * ...`
  ↔ `2 * ...`, `&4` ↔ `4`.
- HOL `connected(segment [a,b])` ↔ `IsConnected (segment ℝ a b)`
  (Mathlib/Topology/Connected/Basic.lean:55).
- None of the ten statements is already available as a named Mathlib
  theorem (the only Mathlib-general one, `SEGMENT_CONNECTED`, is not
  packaged in Mathlib; its ingredients `convex_segment` +
  `Convex.isConnected` are). All others mention the repo-specific
  `FAN`/`hypermapOfFan`/`affGt`/`yfan` vocabulary, so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.AffGtCut
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto2
import Kepler.Text.ConformingAuto6
import Kepler.Text.ConformingAuto7

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

/-! ## Euler 计数恒等式（Conforming.hl:1719-1804） -/

/-- HOL Conforming.hl :1719-1804 `SUM_CARD_FACE_NODE_DART_FAN`

HOL 原文：
```
!x V E.
     FAN (x,V,E) /\ conforming_fan (x,V,E)
     ==> &2 * &(CARD (face_set (hypermap1_of_fanx (x,V,E))))  +
 &2 * &(CARD (node_set (hypermap1_of_fanx (x,V,E))))  -
 &(CARD (dart (hypermap1_of_fanx (x,V,E)))) = &4
```

编码说明：`face_set`/`node_set` ↔ `H.faceSet`/`H.nodeSet`（集合的集合，
用 `Set.ncard`）；HOL `dart H`（dart 集合）↔ `H.darts : Finset (V3×V3)`，
用 `.card`。`FAN ∧ conforming_fan` 拆成 `hfan : FAN x V E` 与
`hconf : conformingFan x V E hfan`。

证明思路：由 `conformingFan` 拆出 `conformingSolidAngleFan`，用
`SUM_SOL_IN_FACE_SET_EQ_4PI` 得面集上 `sol` 之和为 `4π`；再用
`conformingSolidAngleFan` 把每个 `sol` 换成 `2π + ∑ azim - π`，配合
`SUM_EQ`/`SUM_ADD`/`SUM_CONST` 与
`SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN`（节点集上 `azim` 和为 `2π`）以及
`DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET`（dart 集是面/节点集的并）
收口，最后用 `π ≠ 0` 消去 `π` 得到计数恒等式。

候选已有引理：
- `SUM_SOL_IN_FACE_SET_EQ_4PI`（Kepler/Text/ConformingAuto6.lean:735）
- `conformingSolidAngleFan`（Kepler/Text/ConformingDefs.lean:141）
- `SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN`（Kepler/Text/ConformingAuto7.lean:543）
- `SUM_AZIM_FAN_OF_NODE_EQ_SUM_AZIM_I_FAN`（Kepler/Text/ConformingAuto7.lean:422）
- `DART_EQ_UNIONS_FACE_SET_NODE_SET_EDGE_SET`（Kepler/Text/ConformingAuto6.lean:768）
- `faceSet_finite`（Kepler/Text/Hypermap.lean:1016）、`nodeSet_finite`（同:1013）
- `face_eq_of_mem`（Kepler/Text/Hypermap.lean:2486，HOL `lemma_face_identity`）、
  `node_eq_of_mem`（同:2482，HOL `lemma_node_identity`）
- `FINITE_FACE_FAN`（Kepler/Text/PlanarityAuto14.lean:693）、
  `FINITE_NODE_FAN`（Kepler/Text/ConformingAuto7.lean:103）
- 缺口：HOL `SUM_EQ`/`SUM_ADD`/`SUM_CONST`/`SUM_SUB`/`SUM_UNIONS_NONZERO`
  未单列移植，用 Mathlib `finsum_congr`/`finsum_add_distrib`/
  `finsum_sub_distrib`/`finsum_const` 与 `finsum_mem_eq_finite_toFinset_sum`
  （cf. Kepler/Text/ConformingAuto1.lean:818）替代 -/
private theorem finsum_mem_const_real {α : Type*} {s : Set α} (hs : s.Finite) (c : ℝ) :
    (∑ᶠ _ ∈ s, c) = c * (s.ncard : ℝ) := by
  rw [finsum_mem_eq_finite_toFinset_sum (fun _ : α => c) hs, Finset.sum_const,
    nsmul_eq_mul, ← Set.ncard_eq_toFinset_card s hs, mul_comm]

private theorem hypermap_faceSet_pairwiseDisjoint {α : Type*} [DecidableEq α]
    (H : Hypermap α) : H.faceSet.PairwiseDisjoint id := by
  intro a ha b hb hne
  simp only [Hypermap.faceSet, setOfOrbits, Set.mem_setOf_eq] at ha hb
  obtain ⟨xa, -, rfl⟩ := ha
  obtain ⟨xb, -, rfl⟩ := hb
  rcases orbitMap_disjoint_or_eq H.faceMap_permutes xa xb with h | h
  · exact Set.disjoint_iff_inter_eq_empty.mpr h
  · exact absurd h hne

private theorem hypermap_nodeSet_pairwiseDisjoint {α : Type*} [DecidableEq α]
    (H : Hypermap α) : H.nodeSet.PairwiseDisjoint id := by
  intro a ha b hb hne
  simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq] at ha hb
  obtain ⟨xa, -, rfl⟩ := ha
  obtain ⟨xb, -, rfl⟩ := hb
  rcases orbitMap_disjoint_or_eq H.nodeMap_permutes xa xb with h | h
  · exact Set.disjoint_iff_inter_eq_empty.mpr h
  · exact absurd h hne

private theorem hypermap_face_finite_of_mem {α : Type*} [DecidableEq α]
    (H : Hypermap α) {a : Set α} (ha : a ∈ H.faceSet) : a.Finite := by
  simp only [Hypermap.faceSet, setOfOrbits, Set.mem_setOf_eq] at ha
  obtain ⟨x, -, rfl⟩ := ha
  exact Hypermap.face_finite H x

private theorem hypermap_node_finite_of_mem {α : Type*} [DecidableEq α]
    (H : Hypermap α) {a : Set α} (ha : a ∈ H.nodeSet) : a.Finite := by
  simp only [Hypermap.nodeSet, setOfOrbits, Set.mem_setOf_eq] at ha
  obtain ⟨x, -, rfl⟩ := ha
  exact Hypermap.node_finite H x

theorem SUM_CARD_FACE_NODE_DART_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) (hconf : conformingFan x V E hfan) :
    2 * ((hypermapOfFan x V E hfan).faceSet.ncard : ℝ) +
        2 * ((hypermapOfFan x V E hfan).nodeSet.ncard : ℝ) -
        ((hypermapOfFan x V E hfan).darts.card : ℝ) = 4 := by
  classical
  let H := hypermapOfFan x V E hfan
  let g : V3 × V3 → ℝ := fun y => azimFan x V E y.1 y.2
  have hcardV : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard := hconf.1
  have hsol : ∀ f ∈ H.faceSet,
      sol x (dartsetLeadsIntoFan x V E f) =
        2 * Real.pi + ∑ᶠ y ∈ f, (g y - Real.pi) := by
    intro f hf
    have h := hconf.2.2.2.2.1 f hf
    simpa [g] using h.2.2
  have hsum_sol : (∑ᶠ f ∈ H.faceSet,
      sol x (dartsetLeadsIntoFan x V E f)) = 4 * Real.pi :=
    SUM_SOL_IN_FACE_SET_EQ_4PI hfan hconf
  have hsum4 : (∑ᶠ f ∈ H.faceSet,
      (2 * Real.pi + ∑ᶠ y ∈ f, (g y - Real.pi))) = 4 * Real.pi := by
    rw [← hsum_sol]
    exact finsum_mem_congr rfl (fun f hf => (hsol f hf).symm)
  have hsplit : (∑ᶠ f ∈ H.faceSet,
        (2 * Real.pi + ∑ᶠ y ∈ f, (g y - Real.pi))) =
      (∑ᶠ f ∈ H.faceSet, 2 * Real.pi) +
        (∑ᶠ f ∈ H.faceSet, ∑ᶠ y ∈ f, (g y - Real.pi)) :=
    finsum_mem_add_distrib H.faceSet_finite
  have hconstF : (∑ᶠ _ ∈ H.faceSet, 2 * Real.pi) =
      2 * Real.pi * (H.faceSet.ncard : ℝ) :=
    finsum_mem_const_real H.faceSet_finite (2 * Real.pi)
  have hface_part : (∑ᶠ f ∈ H.faceSet, ∑ᶠ y ∈ f, (g y - Real.pi)) =
      ∑ᶠ y ∈ (↑H.darts : Set (V3 × V3)), (g y - Real.pi) := by
    have hsu : (⋃₀ H.faceSet) = (↑H.darts : Set (V3 × V3)) := by
      change (⋃₀ setOfOrbits H.darts H.faceMap) = ↑H.darts
      exact (sUnion_setOfOrbits H.faceMap_permutes).symm
    rw [← finsum_mem_sUnion (hypermap_faceSet_pairwiseDisjoint H) H.faceSet_finite
      (fun a ha => hypermap_face_finite_of_mem H ha)]
    rw [hsu]
  have hdarts_sub : (∑ᶠ y ∈ (↑H.darts : Set (V3 × V3)), (g y - Real.pi)) =
      (∑ᶠ y ∈ (↑H.darts : Set (V3 × V3)), g y) -
        Real.pi * (H.darts.card : ℝ) := by
    rw [finsum_mem_sub_distrib g (fun _ => Real.pi) H.darts.finite_toSet]
    congr 1
    rw [finsum_mem_const_real H.darts.finite_toSet Real.pi]
    simp
  have hnode_part : (∑ᶠ f ∈ H.nodeSet, ∑ᶠ y ∈ f, g y) =
      ∑ᶠ y ∈ (↑H.darts : Set (V3 × V3)), g y := by
    have hsu : (⋃₀ H.nodeSet) = (↑H.darts : Set (V3 × V3)) := by
      change (⋃₀ setOfOrbits H.darts H.nodeMap) = ↑H.darts
      exact (sUnion_setOfOrbits H.nodeMap_permutes).symm
    rw [← finsum_mem_sUnion (hypermap_nodeSet_pairwiseDisjoint H) H.nodeSet_finite
      (fun a ha => hypermap_node_finite_of_mem H ha)]
    rw [hsu]
  have hdarts_g : (∑ᶠ y ∈ (↑H.darts : Set (V3 × V3)), g y) =
      2 * Real.pi * (H.nodeSet.ncard : ℝ) := by
    rw [← hnode_part]
    rw [finsum_mem_congr rfl
      (fun f hf => SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN hfan hf hcardV)]
    exact finsum_mem_const_real H.nodeSet_finite (2 * Real.pi)
  have hmain : 4 * Real.pi = 2 * Real.pi * (H.faceSet.ncard : ℝ) +
      (2 * Real.pi * (H.nodeSet.ncard : ℝ) -
        Real.pi * (H.darts.card : ℝ)) := by
    rw [← hsum4, hsplit, hconstF, hface_part, hdarts_sub, hdarts_g]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h' : Real.pi * 4 = Real.pi *
      (2 * (H.faceSet.ncard : ℝ) +
        (2 * (H.nodeSet.ncard : ℝ) - (H.darts.card : ℝ))) := by
    rw [mul_comm Real.pi 4, hmain]
    ring
  have h'' : (4 : ℝ) = 2 * (H.faceSet.ncard : ℝ) +
      (2 * (H.nodeSet.ncard : ℝ) - (H.darts.card : ℝ)) :=
    mul_left_cancel₀ hpi h'
  show 2 * (H.faceSet.ncard : ℝ) + 2 * (H.nodeSet.ncard : ℝ) -
      (H.darts.card : ℝ) = 4
  linarith

/-! ## 非 conforming 扇的存在性结果（Conforming.hl:1806-2007） -/

/-- HOL Conforming.hl :1806-1817 `nonconformin_fan_imp_n_fan_ge0`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ~(conforming_fan (x,V,E))
==> N_FAN(x,V,E)> 0
```

编码说明：`N_FAN` ↔ `nFan`；`conforming_fan` ↔ `conformingFan x V E hfan`；
`CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`。

证明思路：对结论取逆否（`~(0 < n) ↔ n = 0`，HOL `ARITH_RULE`），
把 `nFan x V E hfan = 0` 代入 `DWFBRQY`，得到 `conformingFan`，与
`hnconf` 矛盾。

候选已有引理：
- `DWFBRQY`（Kepler/Text/ConformingAuto2.lean:256）
- `nFan`（Kepler/Text/ConformingDefs.lean:204）
- `conformingFan`（Kepler/Text/ConformingDefs.lean:184）
- 缺口：无 -/
theorem nonconformin_fan_imp_n_fan_ge0 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hnconf : ¬ conformingFan x V E hfan) :
    0 < nFan x V E hfan := by
  by_contra h
  have hn : nFan x V E hfan = 0 := Nat.eq_zero_of_not_pos h
  exact hnconf (DWFBRQY x V E hfan hcard hfan80 hn)

/-- HOL Conforming.hl :1819-1841 `nonconformin_fan_imp_exist_face_gt_3`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool).
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ~(conforming_fan (x,V,E))
==> ?ds. ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
```

编码说明：`face_set` ↔ `H.faceSet`，`ds` 为 `Set (V3 × V3)`，
`CARD ds > 3` ↔ `3 < ds.ncard`。

证明思路：先由 `nonconformin_fan_imp_n_fan_ge0` 得 `0 < nFan`；展开
`nFan` 为面集上的自然数和，对「所有面 `CARD f - 3 = 0`」作排中分裂：
若成立则由 `NSUM_EQ_0_IFF` 得 `nFan = 0`，矛盾；否则取使
`f.ncard - 3 ≠ 0` 的面 `f`，由 `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`
得 `3 ≤ f.ncard`，从而 `3 < f.ncard`。

候选已有引理：
- `nonconformin_fan_imp_n_fan_ge0`（本文件上文，HOL :1806）
- `nFan`（Kepler/Text/ConformingDefs.lean:204）
- `NSUM_EQ_0_IFF`（Kepler/Text/ConformingAuto1.lean:818）
- `CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN`（Kepler/Text/PlanarityAuto15.lean:139）
- 缺口：无 -/
theorem nonconformin_fan_imp_exist_face_gt_3 {x : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hnconf : ¬ conformingFan x V E hfan) :
    ∃ ds : Set (V3 × V3),
      ds ∈ (hypermapOfFan x V E hfan).faceSet ∧ 3 < ds.ncard := by
  have hpos : 0 < nFan x V E hfan :=
    nonconformin_fan_imp_n_fan_ge0 hfan hcard hfan80 hnconf
  by_contra h
  push Not at h
  have hzero : ∀ f, f ∈ (hypermapOfFan x V E hfan).faceSet → f.ncard - 3 = 0 := by
    intro f hf
    have hge : 3 ≤ f.ncard := CARD_FACE_SET_GE_3_FULLY_SURROUNDED_FAN hfan hcard hf
    have hle : f.ncard ≤ 3 := h f hf
    omega
  have hn0 : nFan x V E hfan = 0 := by
    simp only [nFan]
    exact (NSUM_EQ_0_IFF
      (Hypermap.faceSet_finite (hypermapOfFan x V E hfan))).mpr hzero
  omega

/-- HOL Conforming.hl :1843-1855 `exists_face_in_face_set`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
 ds IN face_set(hypermap1_of_fanx (x,V,E))
==> ?f1. f1 IN ds
```

编码说明：`face_set` ↔ `H.faceSet`。HOL 陈述无 `FAN` 前提，但本仓库
`hypermapOfFan` 需要显式 `hfan : FAN x V E`，故补此参数（唯一偏差）。

证明思路：由 `Hypermap.face_representation` 把 `ds ∈ H.faceSet` 化为
`∃ x ∈ H.darts, ds = H.face x`；`H.face x = orbitMap H.faceMap x` 含
`x`（`mem_orbitMap_self`，对应 HOL 取 `POWER 0`），取 `f1 = x` 即得。

候选已有引理：
- `Hypermap.face_representation`（Kepler/Text/Hypermap.lean:2794）
- `Hypermap.orbitMap`（Kepler/Text/Hypermap.lean:708）、
  `Hypermap.mem_orbitMap_self`（同:713）
- `Hypermap.setOfOrbits`（Kepler/Text/Hypermap.lean:981）、
  `Hypermap.PermutesOn.mem_iff_orbitMap_mem_setOfOrbits`（同:2756）
- 缺口：无 -/
theorem exists_face_in_face_set {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet) :
    ∃ f1, f1 ∈ ds := by
  obtain ⟨d, _hd, rfl⟩ := (hypermapOfFan x V E hfan).face_representation hds
  exact ⟨d, mem_orbitMap_self _ d⟩

/-- HOL Conforming.hl :1857-1866 `identity_face_in_face_set`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds f1.
 ds IN face_set(hypermap1_of_fanx (x,V,E))
/\ f1 IN ds
==> ds= face (hypermap1_of_fanx (x,V,E))  f1
```

编码说明：`face_set`/`face` ↔ `H.faceSet`/`H.face`。HOL 陈述无 `FAN`
前提，故补显式 `hfan : FAN x V E`（唯一偏差）。

证明思路：由 `face_representation` 得 `ds = H.face x` 且 `f1 ∈ H.face x`；
再用 `H.face_eq_of_mem`（HOL `lemma_face_identity`）得
`H.face x = H.face f1`，回代即 `ds = H.face f1`。

候选已有引理：
- `Hypermap.face_representation`（Kepler/Text/Hypermap.lean:2794）
- `Hypermap.face_eq_of_mem`（Kepler/Text/Hypermap.lean:2486，HOL `lemma_face_identity`）
- `Hypermap.face`（Kepler/Text/Hypermap.lean:846）
- 缺口：无 -/
theorem identity_face_in_face_set {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {f1 : V3 × V3}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hf1 : f1 ∈ ds) :
    ds = (hypermapOfFan x V E hfan).face f1 := by
  obtain ⟨d, _hd, rfl⟩ := (hypermapOfFan x V E hfan).face_representation hds
  exact (hypermapOfFan x V E hfan).face_eq_of_mem hf1

/-- HOL Conforming.hl :1868-1878 `condition_f1_eq_fan`

HOL 原文：
```
!x V E v u w.
FAN(x,V,E)
/\ {u,w} IN E /\ {v,u} IN E
/\ sigma_fan x V E u w = v
==> f1_fan x V E (x,v,u,sigma_fan x V E v u)=(x,u,w,v)
```

编码说明：四元组 dart `(x,v,u,·)` ↔ 点对 `(v,u)`，`(x,u,w,v)` ↔ `(u,w)`；
`f1_fan` ↔ `f1Fan`（`f1Fan x V E (v,u) = (u, inverse1SigmaFan x V E u v)`）。

证明思路：展开 `f1Fan`，结论化为 `inverse1SigmaFan x V E u v = w`；由
`INVERSE1_SIGMA_FAN`（第三分量，顶点 `u`）与 `hsigma : sigmaFan x V E u w = v`
即得。

候选已有引理：
- `INVERSE1_SIGMA_FAN`（Kepler/Text/Fan.lean:821）
- `f1Fan`（Kepler/Text/ConformingDefs.lean:87）
- `inverse1SigmaFan`（Kepler/Text/Fan.lean:240）
- 缺口：无 -/
theorem condition_f1_eq_fan {x v u w : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E)
    (huw : {u, w} ∈ E) (hvu : {v, u} ∈ E)
    (hsigma : sigmaFan x V E u w = v) :
    f1Fan x V E (v, u) = (u, w) := by
  have hinv : inverse1SigmaFan x V E u (sigmaFan x V E u w) = w :=
    (INVERSE1_SIGMA_FAN (v := u) hfan).2.2 w huw
  unfold f1Fan
  rw [← hsigma, hinv]

private theorem f1Fan_eq_fFanPair_of_dart1_auto8 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    f1Fan x V E d = fFanPair x V E d := by
  have hba : {d.2, d.1} ∈ E := by
    have h : {d.1, d.2} ∈ E := hd
    rwa [Set.pair_comm] at h
  simp only [f1Fan, fFanPair]
  rw [inverse_sigma_fan_eq_inverse1 hfan hba]

private theorem hypermapOfFan_faceMap_eq_auto8 {x : V3} {V : Set V3}
    {E : Set (Set V3)} (hfan : FAN x V E) {d : V3 × V3}
    (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).faceMap d = fFanPair x V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by
    simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-- HOL Conforming.hl :1880-2007 `nonconformin_fan_imp_exist_3point_in_face`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ds IN face_set(hypermap1_of_fanx (x,V,E)) /\ CARD ds >3
==> ?f1 f2 f3. {f1,f2,f3} SUBSET ds /\ f1_fan x V E f1=f2 /\ f1_fan x V E f2 =f3 /\ ~(f1_fan x V E f3 =f1)
/\ {pr2 f2, pr2 f3} IN E
/\ ~({pr2 f3, pr2 f1 } IN E)
/\ {pr2 f1, pr2 f2 } IN E
/\ sigma_fan x V E (pr2 f2) (pr2 f3)=pr2 f1
/\ pr2 f3= pr3 f2
/\ pr2 f2= pr3 f1
```

编码说明：四元组 dart ↔ `V3 × V3`，`pr2 y`/`pr3 y` ↦ `y.1`/`y.2`；
`f1_fan` ↔ `f1Fan`；`{f1,f2,f3} SUBSET ds` ↔
`({f1, f2, f3} : Set (V3 × V3)) ⊆ ds`。

证明思路：由 `exists_face_in_face_set` 取 `f1 ∈ ds`，令
`f2 = f1Fan x V E f1`、`f3 = f1Fan x V E f2`、`f4 = f1Fan x V E f3`；用
`condition_f1_fan_in_face_set` 把 `f2,f3,f4` 落在 `ds` 内，用
`f_fan_no_fix` 排除退化，再由 `CARD ds > 3`（`card_orbit_le`）得
`f3 ≠ f1`；对 `f4 = f1` 分裂，取三元组后用 `PROPERTIES_TRIANGLE_FAN`、
`SIGMA_FAN`、`condition_f1_eq_fan` 及 dart 分量关系收口。

候选已有引理：
- `exists_face_in_face_set`（本文件上文，HOL :1843）
- `condition_f1_fan_in_face_set`（Kepler/Text/PlanarityAuto14.lean:741）
- `condition_f1_eq_fan`（本文件上文，HOL :1868）
- `PROPERTIES_TRIANGLE_FAN`（Kepler/Text/PlanarityAuto14.lean:368）
- `f_fan_no_fix`（Kepler/Text/Fan.lean:1022）、`SIGMA_FAN`（同:317）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）、
  `face_subset_darts`（Kepler/Text/Hypermap.lean:854）
- `card_orbit_le`（Kepler/Text/Hypermap.lean:1115）
- 缺口：HOL `hypermap_of_fan_rep`、`dartset_fully_surrounded_is_non_isolated_fan`、
  `face_subset_dart_fan`、`properties_of_f1_fan`、`remark1_fan`、
  `MONO_SIGMA_FAN` 未以该名移植（由上述 dart/hypermap 层引理替代） -/
theorem nonconformin_fan_imp_exist_3point_in_face {x : V3} {V : Set V3}
    {E : Set (Set V3)} {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hcard : ∀ v : V3, v ∈ V → 1 < (setOfEdge v V E).ncard)
    (hfan80 : fan80 x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).faceSet)
    (hds3 : 3 < ds.ncard) :
    ∃ f1 f2 f3 : V3 × V3,
      ({f1, f2, f3} : Set (V3 × V3)) ⊆ ds ∧
        f1Fan x V E f1 = f2 ∧
        f1Fan x V E f2 = f3 ∧
        f1Fan x V E f3 ≠ f1 ∧
        {f2.1, f3.1} ∈ E ∧
        {f3.1, f1.1} ∉ E ∧
        {f1.1, f2.1} ∈ E ∧
        sigmaFan x V E f2.1 f3.1 = f1.1 ∧
        f3.1 = f2.2 ∧
        f2.1 = f1.2 := by
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdf : dartOfFan V E = dart1OfFan V E :=
    dartOfFan_eq_dart1_of_surrounded hfan hcard
  obtain ⟨d, hdH, hface⟩ := Hypermap.face_representation H hds
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hd_dart1 : d ∈ dart1OfFan V E := by
    change d ∈ (↑H.darts : Set (V3 × V3)) at hdH
    simpa [hdarts] using hdH
  have hd_mem : d ∈ ds := by
    rw [hface]; exact Hypermap.mem_face_self H d
  let f2 : V3 × V3 := f1Fan x V E d
  let f3 : V3 × V3 := f1Fan x V E f2
  let f4 : V3 × V3 := f1Fan x V E f3
  have hfm : ∀ {p : V3 × V3}, p ∈ dart1OfFan V E →
      H.faceMap p = f1Fan x V E p := by
    intro p hp
    change (hypermapOfFan x V E hfan).faceMap p = f1Fan x V E p
    rw [hypermapOfFan_faceMap_eq_auto8 hfan hp,
        f1Fan_eq_fFanPair_of_dart1_auto8 hfan hp]
  have hf1fan : f1Fan x V E d = fFanPair x V E d :=
    f1Fan_eq_fFanPair_of_dart1_auto8 hfan hd_dart1
  have hf2_mem : f2 ∈ ds :=
    condition_f1_fan_in_face_set (y := f2) (y1 := d) hfan
      (by show f1Fan x V E d = fFanPair x V E d; exact hf1fan) hds hdf hd_mem
  have hf2_dart1 : f2 ∈ dart1OfFan V E := by
    have h := fFanPair_mem_dart1 hfan hd_dart1
    rwa [← hf1fan] at h
  have hf2fan : f1Fan x V E f2 = fFanPair x V E f2 :=
    f1Fan_eq_fFanPair_of_dart1_auto8 hfan hf2_dart1
  have hf3_mem : f3 ∈ ds :=
    condition_f1_fan_in_face_set (y := f3) (y1 := f2) hfan
      (by show f1Fan x V E f2 = fFanPair x V E f2; exact hf2fan) hds hdf hf2_mem
  have hf3_dart1 : f3 ∈ dart1OfFan V E := by
    have h := fFanPair_mem_dart1 hfan hf2_dart1
    rwa [← hf2fan] at h
  have hf2eq : H.faceMap d = f2 := hfm hd_dart1
  have hf3eq : H.faceMap f2 = f3 := hfm hf2_dart1
  have hf4eq : H.faceMap f3 = f4 := hfm hf3_dart1
  have hf4ne : f4 ≠ d := by
    intro hf4d
    have hfix : (H.faceMap ^ 3) d = d := by
      rw [pow_succ', pow_succ', pow_succ', Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      simp only [pow_zero, Equiv.Perm.one_apply]
      rw [hf2eq, hf3eq, hf4eq, hf4d]
    have hle : (H.face d).ncard ≤ 3 := by
      rw [Hypermap.face]
      exact card_orbit_le H.faceMap (by norm_num : (3 : ℕ) ≠ 0) hfix
    rw [← hface] at hle
    omega
  have hba : {d.2, d.1} ∈ E := by
    have h : {d.1, d.2} ∈ E := hd_dart1
    rwa [Set.pair_comm] at h
  have hf2fst : f2.1 = d.2 := rfl
  have hf3fst : f3.1 = f2.2 := rfl
  have hf2snd : f2.2 = inverse1SigmaFan x V E d.2 d.1 := rfl
  have hsigma_bc : sigmaFan x V E d.2 f3.1 = d.1 := by
    rw [hf3fst, hf2snd]
    exact (INVERSE1_SIGMA_FAN (v := d.2) hfan).2.1 d.1 hba
  have he_bc : {d.2, f3.1} ∈ E := by
    rw [hf3fst, hf2snd]
    exact (INVERSE1_SIGMA_FAN (v := d.2) hfan).1 d.1 hba
  have hne : {f3.1, d.1} ∉ E := by
    intro hca
    have htri := PROPERTIES_TRIANGLE_FAN (x := x) (v := d.1) (u := d.2) (w := f3.1)
      hfan hd_dart1 he_bc hca hsigma_bc hcard hfan80
    obtain ⟨hsig_ab, hsig_ca⟩ := htri
    have hf3snd : f3.2 = inverse1SigmaFan x V E f2.2 f2.1 := rfl
    have hf3snd' : f3.2 = inverse1SigmaFan x V E f3.1 d.2 := by
      rw [hf3snd, hf2fst, hf3fst]
    have hinv_ca : inverse1SigmaFan x V E f3.1 d.2 = d.1 := by
      have h := (INVERSE1_SIGMA_FAN (v := f3.1) hfan).2.2 d.1 hca
      rwa [hsig_ca] at h
    have hf3snd_val : f3.2 = d.1 := hf3snd'.trans hinv_ca
    have hf4fst : f4.1 = f3.2 := rfl
    have hf4snd : f4.2 = inverse1SigmaFan x V E f3.2 f3.1 := rfl
    have hinv_ab : inverse1SigmaFan x V E d.1 f3.1 = d.2 := by
      have h := (INVERSE1_SIGMA_FAN (v := d.1) hfan).2.2 d.2 hd_dart1
      rwa [hsig_ab] at h
    have hf4snd_val : f4.2 = d.2 := by
      rw [hf4snd, hf3snd_val, hinv_ab]
    have hf4eqd : f4 = d := by
      have h1 : f4.1 = d.1 := by rw [hf4fst, hf3snd_val]
      exact Prod.ext h1 hf4snd_val
    exact hf4ne hf4eqd
  have hsub : ({d, f2, f3} : Set (V3 × V3)) ⊆ ds := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact hd_mem
    · exact hf2_mem
    · exact hf3_mem
  refine ⟨d, f2, f3, hsub, rfl, rfl, hf4ne, ?_, hne, ?_, ?_, rfl, rfl⟩
  · simpa [f2, f1Fan] using he_bc
  · show {d.1, f2.1} ∈ E
    rw [hf2fst]
    exact hd_dart1
  · simpa [f2, f1Fan] using hsigma_bc

/-! ## aff_gt 与 yfan/线段的几何结果（Conforming.hl:2009-2099） -/

/-- HOL Conforming.hl :2009-2029 `condition_aff_gt_subset_yfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v u w.
FAN(x,V,E) /\ {v,u} IN E /\ {u,w} IN E
/\ sigma_fan x V E u w = v
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ fan80(x,V,E)
/\ ~({w,v} IN E)
==> aff_gt {x} {v,w} SUBSET yfan (x,V,E)
```

编码说明：`aff_gt` ↔ `affGt`；`yfan` ↔ `yfan`；`SUBSET` ↔ `⊆`。

证明思路：展开 `yfan` 为 `univ \ xfan`，把包含化为
`affGt {x} {v,w} ∩ xfan x V E = ∅`，对后件取逆否；再用
`AFF_GT_CUT_XFAN_IMP_EDGE_FAN`（若割锥与 `xfan` 相交则 `{w,v} ∈ E`）与
`hwv` 矛盾。

候选已有引理：
- `AFF_GT_CUT_XFAN_IMP_EDGE_FAN`（Kepler/Text/AffGtCut.lean:669）
- `yfan`（Kepler/Text/Fan.lean:158）、`xfan`（Kepler/Text/Fan.lean:154）
- `affGt`（Kepler/Geom/Aff.lean:39）
- 缺口：无 -/
theorem condition_aff_gt_subset_yfan {x v u w : V3} {V : Set V3}
    {E : Set (Set V3)}
    (hfan : FAN x V E) (hvu : {v, u} ∈ E) (huw : {u, w} ∈ E)
    (hsigma : sigmaFan x V E u w = v)
    (hcard : ∀ z : V3, z ∈ V → 1 < (setOfEdge z V E).ncard)
    (hfan80 : fan80 x V E) (hwv : {w, v} ∉ E) :
    affGt ({x} : Set V3) {v, w} ⊆ yfan x V E := by
  intro y hy
  simp only [yfan, Set.mem_sdiff, Set.mem_univ, true_and]
  intro hyx
  have hNE : ¬(affGt {x} {v, w} ∩ xfan x V E = ∅) := by
    intro h
    have hy' : y ∈ affGt {x} {v, w} ∩ xfan x V E := ⟨hy, hyx⟩
    rw [h] at hy'
    exact hy'
  have hE : {v, w} ∈ E :=
    AFF_GT_CUT_XFAN_IMP_EDGE_FAN hfan hvu huw hsigma hcard hfan80 hNE
  exact hwv (by rwa [Set.pair_comm] at hE)

/-- HOL Conforming.hl :2031-2092 `segment_subset_aff_gt_union`

HOL 原文：
```
!x:real^3 y z v u w.
~coplanar{x,v,u,w}
/\ y IN aff_gt {x} {v, u, w}
/\ z IN aff_gt {x} {w, v}
==> segment[y,z] SUBSET aff_gt {x} {w, v} UNION aff_gt {x} {v, u, w}
```

编码说明：`coplanar` ↔ `Coplanar`；`aff_gt` ↔ `affGt`；HOL
`segment[y,z]` ↔ `segment ℝ y z`；`UNION`/`SUBSET` ↔ `∪`/`⊆`。

证明思路：展开 `segment` 为 `(1-t)•y + t•z`；用 `aff_gt_1_2` 把
`z ∈ affGt {x} {w,v}` 展开，用 `AFF_GT_1_3` 把 `y ∈ affGt {x} {v,u,w}`
展开；由 `notcoplanar_disjoints` 得各点互异，把组合式合并为
`affGt {x} {v,u,w}` 的系数（`t<1` 时）或退化到 `z`（`t=1` 时），
逐项用 `REAL_LT_MUL`/`REAL_LE_MUL` 证系数为正。

候选已有引理：
- `notcoplanar_disjoints`（Kepler/Text/PlanarityAuto11.lean:1259）
- `AFF_GT_1_3`（Kepler/Text/PlanarityAuto11.lean:1029）
- `aff_gt_1_2`（Kepler/Text/Planarity.lean:165）
- `Coplanar`（Kepler/Geom/Coplanar.lean:23）
- 缺口：无 -/
theorem segment_subset_aff_gt_union {x y z v u w : V3}
    (hcop : ¬ Coplanar ({x, v, u, w} : Set V3))
    (hy : y ∈ affGt ({x} : Set V3) {v, u, w})
    (hz : z ∈ affGt ({x} : Set V3) {w, v}) :
    segment ℝ y z ⊆
      affGt ({x} : Set V3) {w, v} ∪ affGt ({x} : Set V3) {v, u, w} := by
  intro p hp
  have hdis13 : Disjoint ({x} : Set V3) ({v, u, w} : Set V3) :=
    (notcoplanar_disjoints x v u w hcop).2.2.2.1
  have hdiswv : Disjoint ({x} : Set V3) ({w, v} : Set V3) :=
    (notcoplanar_disjoints x v u w hcop).2.2.2.2.2.2.2
  rw [AFF_GT_1_3 x v u w hdis13] at hy
  obtain ⟨t1, t2, t3, t4, ht2, ht3, ht4, hsumy, hy_eq⟩ := hy
  have hz_exp := hz
  rw [aff_gt_1_2 (x := x) (v := w) (w := v) hdiswv] at hz_exp
  obtain ⟨s1, s2, s3, hs2, hs3, hsumz, hz_eq⟩ := hz_exp
  rw [segment] at hp
  obtain ⟨a, b, ha0, hb0, hab, hp_eq⟩ := hp
  by_cases hb1 : b = 1
  · left
    have haz : a = 0 := by linarith
    have hpz : p = z := by
      rw [← hp_eq, haz, hb1, zero_smul, one_smul, zero_add]
    rw [hpz]
    exact hz
  · right
    have hb_le : b ≤ 1 := by linarith
    have hb_lt : b < 1 := lt_of_le_of_ne hb_le hb1
    have ha_pos : 0 < a := by linarith
    rw [AFF_GT_1_3 x v u w hdis13]
    refine ⟨a * t1 + b * s1, a * t2 + b * s3, a * t3, a * t4 + b * s2,
      ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    · positivity
    · positivity
    · have hfac : (a * t1 + b * s1) + (a * t2 + b * s3) + a * t3 +
          (a * t4 + b * s2) = a * (t1 + t2 + t3 + t4) + b * (s1 + s2 + s3) := by
        ring
      rw [hfac, hsumy, hsumz, mul_one, mul_one, hab]
    · rw [← hp_eq, hy_eq, hz_eq]
      module

/-- HOL Conforming.hl :2094-2099 `SEGMENT_CONNECTED`

HOL 原文：
```
!a b. connected(segment [a,b])
```

编码说明：HOL `connected s` ↔ Mathlib `IsConnected s`
（Mathlib/Topology/Connected/Basic.lean:55）；`segment [a,b]` ↔
`segment ℝ a b`。

证明思路：`segment ℝ a b` 凸（`convex_segment`），且非空
（`left_mem_segment`/`right_mem_segment`），由 `Convex.isConnected` 得
`IsConnected (segment ℝ a b)`。HOL 用 `CONVEX_CONNECTED` +
`SEGMENT_CONVEX_HULL` + `CONVEX_CONVEX_HULL`。

候选已有引理：
- `convex_segment`（Mathlib/Analysis/Convex/Basic.lean:164）
- `Convex.isConnected`（Mathlib/Analysis/Convex/PathConnected.lean:88）
- `left_mem_segment`（Mathlib/Analysis/Convex/Segment.lean:105）、
  `right_mem_segment`（同:108）
- `IsConnected`（Mathlib/Topology/Connected/Basic.lean:55）
- 缺口：Mathlib 无与 HOL `SEGMENT_CONNECTED` 同名/同形的整句引理
  （本陈述为 Mathlib-general，但未预打包），故保留 -/
theorem SEGMENT_CONNECTED (a b : V3) : IsConnected (segment ℝ a b) := by
  sorry

end Kepler.Text
