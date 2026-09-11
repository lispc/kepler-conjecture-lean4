/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 7
(Conforming.hl:1478-1718).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 7, Conforming.hl:1478-1718):
- `FINITE_NODE_FAN` (1478)
- `lemma_node_identity_fan` (1487)
- `node_subset_dart_fan` (1497)
- `rep_node_set_fan` (1511)
- `properties_of_elements_in_node_fully_surroundedfan` (1551)
- `lemma_card_node_eq_set_of_orbits` (1569)
- `mono_cyclic_power_sigma_fan` (1597)
- `SUM_AZIM_FAN_OF_NODE_EQ_SUM_AZIM_I_FAN` (1626)
- `exists_point_in_node` (1679)
- `SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN` (1687)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `FAN(x,V,E)` ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL
  `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `hypermap1_of_fanx (x,V,E)` is NOT ported; as in
  Kepler/Text/PlanarityComponent.lean:37-48, `node_set
  (hypermap1_of_fanx (x,V,E))` is encoded as
  `(hypermapOfFan x V E hfan).nodeSet`, and `node
  (hypermap1_of_fanx (x,V,E)) y` as `(hypermapOfFan x V E hfan).node y`,
  with pair darts `V3 × V3`. Because `hypermapOfFan` requires an explicit
  `hfan : FAN x V E` witness (HOL's `hypermap_of_fan` is total), every
  node-set theorem below carries an extra explicit `(hfan : FAN x V E)`
  argument; this is the only deviation from the HOL signatures. In
  particular `FINITE_NODE_FAN` (whose HOL statement has no `FAN`
  hypothesis) acquires this argument as well.
- HOL quadruple darts `real^3#real^3#real^3#real^3` are encoded as pair
  darts `V3 × V3` (Kepler/Text/PlanarityComponent.lean:37-48); `pr2 y`/
  `pr3 y` ↦ `y.1`/`y.2`; HOL `d_fan` ↔ `dartOfFan` (Kepler/Text/Fan.lean:90);
  HOL `d1_fan` ↔ `dart1OfFan` (Kepler/Text/Fan.lean:86).
- HOL `power_map_points sigma_fan x V E v u n` ↔ `(sigmaFan x V E v)^[n] u`
  (Kepler/Text/ConformingAuto1.lean:50; Kepler/Text/TopologyFan.lean:132).
- HOL `sum (0..n-1) g` (set sum over `{0,…,n-1}`) ↔
  `∑ i ∈ Finset.range n, g i` (cf. Kepler/Text/TopologyFan.lean:681);
  HOL `sum f g` (set sum) ↔ `∑ᶠ y ∈ f, g y` (`open scoped BigOperators`).
- HOL `azim_i_fan` ↔ `azimIfan` (Kepler/Text/TopologyFan.lean:511);
  HOL `azim_fan` ↔ `azimFan` (Kepler/Text/Fan.lean:177, alias
  Kepler/Text/TopologyFan.lean:3484); HOL `set_of_orbits_points_fan` ↔
  `setOfOrbitsPointsFan` (Kepler/Text/TopologyFan.lean:115).
- `azim_fan`/`azim_i_fan` use the apex-parameterized `azimFan`/`azimIfan`
  of `Kepler.Text`; both `Kepler.Text.azimFan` and `Kepler.Text.Fan.azimFan`
  are in scope but have identical bodies.
- None of the ten statements is Mathlib-general: every one mentions the
  repo-specific `FAN`/`Hypermap.nodeSet`/`azimFan`/`sigmaFan` vocabulary,
  so nothing is skipped.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

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

/-! ## 节点集的有限性与表示（Conforming.hl:1478-1568） -/

/-- HOL Conforming.hl :1478-1486 `FINITE_NODE_FAN`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
ds IN node_set(hypermap1_of_fanx (x,V,E))
==> FINITE ds
```

编码说明：`node_set (hypermap1_of_fanx …)` ↔
`(hypermapOfFan x V E hfan).nodeSet`。HOL 陈述没有 `FAN` 前提，但本仓库
`hypermapOfFan` 需要显式 `hfan : FAN x V E`，故补此参数（唯一偏差）。

证明思路：`node_representation` 把 `ds ∈ H.nodeSet` 化为 `∃ x ∈ H.darts,
ds = H.node x`；再用 `node_finite`（或直接 `nodeSet_finite` 的成员）得到
`ds.Finite`。

候选已有引理：
- `Hypermap.nodeSet_finite`（Kepler/Text/Hypermap.lean:1013）
- `Hypermap.node_representation`（Kepler/Text/Hypermap.lean:2790）
- `Hypermap.node_finite`（Kepler/Text/Hypermap.lean:866）
- 缺口：无 -/
theorem FINITE_NODE_FAN {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).nodeSet) : ds.Finite := by
  obtain ⟨y, -, rfl⟩ := (hypermapOfFan x V E hfan).node_representation hds
  exact (hypermapOfFan x V E hfan).node_finite y

/-- HOL Conforming.hl :1487-1496 `lemma_node_identity_fan`

HOL 原文：
```
!x V E f y.  f IN (node_set (hypermap1_of_fanx (x,V,E)) )
 /\ y IN f
==> f= node (hypermap1_of_fanx (x,V,E)) y
```

编码说明：`node_set`/`node` ↔ `H.nodeSet`/`H.node y`；`y` 是 pair dart
`V3 × V3`。

证明思路：`node_representation` 给出 `f = H.node x` 且 `x ∈ H.darts`；
由 `y ∈ f = H.node x` 用 `node_eq_of_mem`（HOL `lemma_orbit_identity` +
`hypermap_lemma`）得 `H.node x = H.node y`，故 `f = H.node y`。

候选已有引理：
- `Hypermap.node_representation`（Kepler/Text/Hypermap.lean:2790）
- `Hypermap.node_eq_of_mem`（Kepler/Text/Hypermap.lean:2482）
- `orbitMap_eq_of_mem`（Kepler/Text/Hypermap.lean:1207）
- 缺口：无 -/
theorem lemma_node_identity_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {f : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hf : f ∈ (hypermapOfFan x V E hfan).nodeSet) (hy : y ∈ f) :
    f = (hypermapOfFan x V E hfan).node y := by
  obtain ⟨z, -, rfl⟩ := (hypermapOfFan x V E hfan).node_representation hf
  exact (hypermapOfFan x V E hfan).node_eq_of_mem hy

/-- HOL Conforming.hl :1497-1510 `node_subset_dart_fan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds.
FAN(x,V,E)
/\ ds IN node_set(hypermap1_of_fanx (x,V,E))
==> ds SUBSET d_fan (x,V,E)
```

编码说明：HOL `d_fan` ↔ `dartOfFan V E`（Kepler/Text/Fan.lean:90）；
`SUBSET` ↔ `⊆`。

证明思路：`node_representation` 给 `ds = H.node x`；`node_subset_darts`
给 `H.node x ⊆ ↑H.darts`，而 `(finite_dart1_fan hfan).coe_toFinset`
把 `↑H.darts` 化为 `dart1OfFan V E`，最后 `dart1OfFan ⊆ dartOfFan`。

候选已有引理：
- `Hypermap.node_representation`（Kepler/Text/Hypermap.lean:2790）
- `Hypermap.node_subset_darts`（Kepler/Text/Hypermap.lean:851）
- `finite_dart1_fan`（Kepler/Text/Fan.lean:858）
- `dartOfFan`/`dart1OfFan`（Kepler/Text/Fan.lean:86-91）
- 缺口：无 -/
theorem node_subset_dart_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hds : ds ∈ (hypermapOfFan x V E hfan).nodeSet) :
    ds ⊆ dartOfFan V E := by
  obtain ⟨y, hy, rfl⟩ := (hypermapOfFan x V E hfan).node_representation hds
  intro d hd
  have h1 : d ∈ (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) :=
    (hypermapOfFan x V E hfan).node_subset_darts hy hd
  have h2 : (↑(hypermapOfFan x V E hfan).darts : Set (V3 × V3)) = dart1OfFan V E :=
    (finite_dart1_fan hfan).coe_toFinset
  rw [h2] at h1
  rw [dartOfFan, Set.mem_union]
  exact Or.inr h1

/-- `hypermapOfFan` 的 `nodeMap` 在 `dart1OfFan` 上就是 `nFanPair`
（ConformingAuto1 中 private 引理的本文件副本）。 -/
private theorem hypermapOfFan_nodeMap_eq_ca7 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) :
    (hypermapOfFan x V E hfan).nodeMap d = nFanPair x V E d := by
  unfold hypermapOfFan extendPerm
  simp only [Equiv.ofBijective_apply]
  unfold Kepler.Text.Fan.res
  rw [if_pos (by
    simpa [(finite_dart1_fan hfan).coe_toFinset] using hd)]

/-- `nodeMap` 的迭代在 `dart1OfFan` 上保持首分量并沿 `sigmaFan` 递推
（ConformingAuto1 中 private 引理的本文件副本）。 -/
private theorem hypermapOfFan_nodeMap_iterate_ca7 {x : V3} {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN x V E) {d : V3 × V3} (hd : d ∈ dart1OfFan V E) (n : ℕ) :
    ((hypermapOfFan x V E hfan).nodeMap^[n]) d =
      (d.1, (sigmaFan x V E d.1)^[n] d.2) := by
  have hmem_iter : ∀ k : ℕ, (nFanPair x V E)^[k] d ∈ dart1OfFan V E := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ihk => rw [Function.iterate_succ_apply']; exact nFanPair_mem_dart1 hfan ihk
  have hmain : ∀ k : ℕ,
      ((hypermapOfFan x V E hfan).nodeMap^[k]) d = (nFanPair x V E)^[k] d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact hypermapOfFan_nodeMap_eq_ca7 hfan (hmem_iter k)
  rw [hmain n, nFanPair_iterate]

/-- HOL Conforming.hl :1511-1550 `rep_node_set_fan`

HOL 原文：
```
!x V E f y. FAN (x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ f IN (node_set (hypermap1_of_fanx (x,V,E)) )
 /\ y IN f
==> f = {z| ?i. i >= 0 /\ z=(x, pr2 y,power_map_points (sigma_fan) x V E (pr2 y) (pr3 y) i, power_map_points (sigma_fan) x V E (pr2 y) (pr3 y) (SUC i))}
```

编码说明：四元组 `(x, pr2 y, pm i, pm (SUC i))` 的收缩 dart 是
`(pr2 y, pm i)`，故 RHS ↔ `{z : V3 × V3 | ∃ i : ℕ, 0 ≤ i ∧
z = (y.1, (sigmaFan x V E y.1)^[i] y.2)}`；`power_map_points sigma_fan`
↔ `(sigmaFan x V E ·)^[·]`。`i >= 0` 对 `i : ℕ` 恒真，保留以对齐原文。

证明思路：先用 `lemma_node_identity_fan` 把 `f` 化为 `H.node y`，展开
`node`/`orbitMap` 得 `z ∈ f ↔ ∃ n, (H.nodeMap^[n]) y = z`；再把
`nodeMap` 迭代化为 `nFanPair` 迭代（`(H.nodeMap^[n]) (v,u) =
(v, σ_v^[n] u)`，需在本文件重证 ConformingAuto1 中的 private 引理），
最后用 `nFanPair_iterate` 收口。

候选已有引理：
- `lemma_node_identity_fan`（本文件上文，HOL :1487）
- `Hypermap.node`（Kepler/Text/Hypermap.lean:843）、`orbitMap`
  （Kepler/Text/Hypermap.lean:708）
- `nFanPair_iterate`（Kepler/Text/Fan.lean:1048）
- `hypermapOfFan_nodeMap_eq_ca1` / `hypermapOfFan_nodeMap_iterate_ca1`
  （Kepler/Text/ConformingAuto1.lean:684/694；private，跨文件不可用，需重证）
- 缺口：HOL `into_domain_power_efn_fan`（fan.hl:2694）、
  `power_n_fan`（fan.hl:1005）未移植 -/
theorem rep_node_set_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {f : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard)
    (hf : f ∈ (hypermapOfFan x V E hfan).nodeSet) (hy : y ∈ f) :
    f = {z : V3 × V3 | ∃ i : ℕ, 0 ≤ i ∧
      z = (y.1, (sigmaFan x V E y.1)^[i] y.2)} := by
  have _ := hcard
  let H : Hypermap (V3 × V3) := hypermapOfFan x V E hfan
  have hdarts : (↑H.darts : Set (V3 × V3)) = dart1OfFan V E := by
    change (↑(finite_dart1_fan hfan).toFinset : Set (V3 × V3)) = dart1OfFan V E
    exact (finite_dart1_fan hfan).coe_toFinset
  have hy_dart1 : y ∈ dart1OfFan V E := by
    have hy_darts : y ∈ H.darts := by
      obtain ⟨z, hz, hzf⟩ := H.node_representation hf
      rw [hzf] at hy
      exact H.node_subset_darts hz hy
    have : y ∈ (↑H.darts : Set (V3 × V3)) := hy_darts
    rwa [hdarts] at this
  rw [lemma_node_identity_fan hfan hf hy]
  ext z
  simp only [Hypermap.node, orbitMap, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Nat.zero_le n, by
      rw [← hn, Equiv.Perm.coe_pow, hypermapOfFan_nodeMap_iterate_ca7 hfan hy_dart1 n]⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, by
      rw [Equiv.Perm.coe_pow, hypermapOfFan_nodeMap_iterate_ca7 hfan hy_dart1 i]⟩

/-- HOL Conforming.hl :1551-1568 `properties_of_elements_in_node_fully_surroundedfan`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) ds y.
FAN(x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) >1)
/\ ds IN node_set(hypermap1_of_fanx (x,V,E))
/\ y IN ds
==> {pr2 y, pr3 y} IN E
```

编码说明：`{pr2 y, pr3 y}` ↔ `{y.1, y.2}`。

证明思路：`node_subset_dart_fan` 给 `ds ⊆ dartOfFan V E`，故
`y ∈ dartOfFan V E`；由 hcard 用 `dartOfFan_eq_dart1_of_surrounded` 得
`dartOfFan = dart1OfFan`，即 `{y.1, y.2} ∈ E`。

候选已有引理：
- `node_subset_dart_fan`（本文件上文，HOL :1497）
- `dartOfFan_eq_dart1_of_surrounded`（Kepler/Text/Fan.lean:1084）
- `dart1OfFan`（Kepler/Text/Fan.lean:86）
- 缺口：无 -/
theorem properties_of_elements_in_node_fully_surroundedfan
    {x : V3} {V : Set V3} {E : Set (Set V3)}
    {ds : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard)
    (hds : ds ∈ (hypermapOfFan x V E hfan).nodeSet) (hy : y ∈ ds) :
    {y.1, y.2} ∈ E := by
  have hy_dart : y ∈ dartOfFan V E := node_subset_dart_fan hfan hds hy
  rw [dartOfFan_eq_dart1_of_surrounded hfan hcard] at hy_dart
  simpa only [dart1OfFan, Set.mem_setOf_eq] using hy_dart

/-- HOL Conforming.hl :1569-1596 `lemma_card_node_eq_set_of_orbits`

HOL 原文：
```
!x V E f y. FAN (x,V,E)
/\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ f IN (node_set (hypermap1_of_fanx (x,V,E)) )
 /\ y IN f
==> CARD {z| ?i. i >= 0 /\ z=(x, pr2 y,power_map_points (sigma_fan) x V E (pr2 y) (pr3 y) i, power_map_points (sigma_fan) x V E (pr2 y) (pr3 y) (SUC i))}= CARD( set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) ((pr2 y):real^3) ((pr3 y):real^3)
)
```

编码说明：`CARD` ↔ `.ncard`；`set_of_orbits_points_fan` ↔
`setOfOrbitsPointsFan`；收缩后的 LHS 集合为
`{z : V3 × V3 | ∃ i : ℕ, 0 ≤ i ∧ z = (y.1, (sigmaFan x V E y.1)^[i] y.2)}`。

证明思路：`Prod.snd` 在该集合上单射（首分量固定为 `y.1`），其像恰为
`setOfOrbitsPointsFan x V E y.1 y.2`，故用 `Set.ncard_image_of_injective`
（或 `Set.ncard_congr`）得两侧基数相等。

候选已有引理：
- `rep_node_set_fan`（本文件上文，HOL :1511）
- `setOfOrbitsPointsFan`（Kepler/Text/TopologyFan.lean:115）
- `Set.ncard_image_of_injective`（Mathlib/Data/Set/Card.lean:830）
- `Set.ncard_congr`（Mathlib/Data/Set/Card.lean:906）
- 缺口：HOL `BIJECTIONS_CARD_EQ` 未移植 -/
theorem lemma_card_node_eq_set_of_orbits {x : V3} {V : Set V3} {E : Set (Set V3)}
    {f : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard)
    (hf : f ∈ (hypermapOfFan x V E hfan).nodeSet) (hy : y ∈ f) :
    ({z : V3 × V3 | ∃ i : ℕ, 0 ≤ i ∧
        z = (y.1, (sigmaFan x V E y.1)^[i] y.2)}).ncard =
      (setOfOrbitsPointsFan x V E y.1 y.2).ncard := by
  have _ := hcard
  have _ := hf
  have _ := hy
  apply Set.ncard_congr (fun z _ => z.2)
  · rintro z ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩
  · rintro z z' hz hz' h
    obtain ⟨i, -, rfl⟩ := hz
    obtain ⟨i', -, rfl⟩ := hz'
    exact Prod.ext rfl h
  · rintro w ⟨i, rfl⟩
    exact ⟨(y.1, (sigmaFan x V E y.1)^[i] y.2), ⟨i, Nat.zero_le i, rfl⟩, rfl⟩

/-! ## σ-迭代单循环性与节点上的角和（Conforming.hl:1597-1717） -/

/-- HOL Conforming.hl :1597-1625 `mono_cyclic_power_sigma_fan`

HOL 原文：
```
!x V E v u i j. FAN(x,V,E)/\ {v,u} IN E /\
           i IN 0..CARD (set_of_edge (v) V E) - 1 /\
           j IN 0..CARD (set_of_edge (v) V E) - 1 /\
           power_map_points sigma_fan x V E (v) (u) i =
           power_map_points sigma_fan x V E (v) (u) j
           ==> i = j
```

编码说明：HOL `i IN 0..n-1` ↔ `i ≤ n - 1`（`0 ≤ i` 对 `i : ℕ` 恒真）；
`power_map_points sigma_fan x V E v u i` ↔ `(sigmaFan x V E v)^[i] u`。

证明思路：对 `i`、`j` 三歧（`i = j` / `i < j` / `j < i`）。不等情形由
`hi`/`hj` 把 `≤ ncard - 1` 转成 `< ncard`，再用
`cyclic_power_sigmaFan`（`j < i < ncard` ⟹ 迭代不等）与 `heq` 矛盾，
最后 `omega` 收尾。

候选已有引理：
- `cyclic_power_sigmaFan`（Kepler/Text/TopologyFan.lean:405）
- `power_map_points_edge_fan`（Kepler/Text/ConformingAuto1.lean:676）
- 缺口：无 -/
theorem mono_cyclic_power_sigma_fan {x : V3} {V : Set V3} {E : Set (Set V3)}
    {v u : V3} (hfan : FAN x V E) (hvu : {v, u} ∈ E)
    (i j : ℕ)
    (hi : i ≤ (setOfEdge v V E).ncard - 1)
    (hj : j ≤ (setOfEdge v V E).ncard - 1)
    (heq : (sigmaFan x V E v)^[i] u = (sigmaFan x V E v)^[j] u) :
    i = j := by
  have hu_mem : u ∈ setOfEdge v V E :=
    (properties_of_setOfEdge_fan x V E v u hfan).mp hvu
  have hpos : 0 < (setOfEdge v V E).ncard :=
    (Set.ncard_pos (remark_finite_fan1 v V E hfan.2.2.1.1)).mpr ⟨u, hu_mem⟩
  rcases lt_trichotomy i j with hij | heqij | hji
  · exfalso
    exact (cyclic_power_sigmaFan x V E hfan hvu j i (by omega) hij) heq.symm
  · exact heqij
  · exfalso
    exact (cyclic_power_sigmaFan x V E hfan hvu i j (by omega) hji) heq

/-- HOL Conforming.hl :1626-1678 `SUM_AZIM_FAN_OF_NODE_EQ_SUM_AZIM_I_FAN`

HOL 原文：
```
!x V E f y. FAN (x,V,E) /\ f IN node_set (hypermap1_of_fanx (x,V,E)) /\ y IN f /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
                  ==> sum (0..CARD (set_of_edge (pr2 y) V E) - 1) (\i. azim_i_fan x V E (pr2 y) (pr3 y) i) =
                      sum f (\y1. azim_fan x V E (pr2 y1) (pr3 y1))
```

编码说明：`sum (0..n-1)` ↔ `∑ i ∈ Finset.range n, …`；`sum f g`
（集合和）↔ `∑ᶠ y1 ∈ f, …`；`azim_i_fan` ↔ `azimIfan`；`azim_fan` ↔
`azimFan`；`pr2 y1`/`pr3 y1` ↔ `y1.1`/`y1.2`。

证明思路：用 `rep_node_set_fan` 把 `f` 写成 σ-轨道像集，从而把集合和
`sum f` 化为 σ-迭代参数上的 `Finset.range` 和；`mono_cyclic_power_sigma_fan`
说明 `i ↦ pm i` 在 `range ncard` 上单射，再用 `Finset.sum_image` 换元；
两侧被加项由 `azimIfan`/`azimFan` 定义逐项相等（`azim_i_fan` 即第 i 步
角增量）。

候选已有引理：
- `rep_node_set_fan`（本文件上文，HOL :1511）
- `properties_of_elements_in_node_fully_surroundedfan`（本文件上文，HOL :1551）
- `mono_cyclic_power_sigma_fan`（本文件上文，HOL :1597）
- `azimIfan`（Kepler/Text/TopologyFan.lean:511）
- `azimFan`（Kepler/Text/Fan.lean:177）
- `Finset.sum_image`（Mathlib）、`Set.ncard` 相关
- 缺口：HOL `SUM_IMAGE`/`SIMP_ORBITS_POINTS_FAN`/`remark1_fan` 未单列移植 -/
theorem SUM_AZIM_FAN_OF_NODE_EQ_SUM_AZIM_I_FAN
    {x : V3} {V : Set V3} {E : Set (Set V3)}
    {f : Set (V3 × V3)} {y : V3 × V3}
    (hfan : FAN x V E)
    (hf : f ∈ (hypermapOfFan x V E hfan).nodeSet) (hy : y ∈ f)
    (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard) :
    (∑ i ∈ Finset.range ((setOfEdge y.1 V E).ncard),
        azimIfan x V E y.1 y.2 i) =
      ∑ᶠ y1 ∈ f, azimFan x V E y1.1 y1.2 := by
  set n := (setOfEdge y.1 V E).ncard with hn
  have hvu : {y.1, y.2} ∈ E :=
    properties_of_elements_in_node_fully_surroundedfan hfan hcard hf hy
  have hy1V : y.1 ∈ V :=
    hfan.1 (Set.mem_sUnion.mpr ⟨{y.1, y.2}, hvu, by simp⟩)
  have hu_mem : y.2 ∈ setOfEdge y.1 V E :=
    (properties_of_setOfEdge_fan x V E y.1 y.2 hfan).mp hvu
  have hn_pos : 0 < n := by
    rw [hn]
    exact (Set.ncard_pos (remark_finite_fan1 y.1 V E hfan.2.2.1.1)).mpr ⟨y.2, hu_mem⟩
  have hperiod : (sigmaFan x V E y.1)^[n] y.2 = y.2 := by
    rw [hn]
    exact order_power_sigmaFan x V E hfan hvu rfl
  let g : ℕ → V3 × V3 := fun i => (y.1, (sigmaFan x V E y.1)^[i] y.2)
  have hg_mod : ∀ i : ℕ, g i = g (i % n) := by
    intro i
    apply Prod.ext
    · rfl
    · show (sigmaFan x V E y.1)^[i] y.2 =
        (sigmaFan x V E y.1)^[i % n] y.2
      conv_lhs =>
        rw [show i = i % n + n * (i / n) from (Nat.mod_add_div i n).symm]
      rw [Function.iterate_add_apply, Nat.mul_comm n (i / n),
        show (sigmaFan x V E y.1)^[i / n * n] y.2 = y.2 from
          fix_point_sigmaFan x V E y.1 y.2 (i / n) n hperiod]
  have hf_eq : f = g '' (Finset.range n : Set ℕ) := by
    rw [rep_node_set_fan hfan hcard hf hy]
    ext z
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨i % n,
        by simp only [Finset.mem_coe, Finset.mem_range]; exact Nat.mod_lt i hn_pos,
        (hg_mod i).symm⟩
    · rintro ⟨i, _, rfl⟩
      exact ⟨i, Nat.zero_le i, rfl⟩
  have hbij : Set.BijOn g (Finset.range n : Set ℕ) f := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [hf_eq]
      exact ⟨i, hi, rfl⟩
    · intro i hi j hj heq
      have hi' : i < n := by simpa using hi
      have hj' : j < n := by simpa using hj
      have h2 : (sigmaFan x V E y.1)^[i] y.2 =
          (sigmaFan x V E y.1)^[j] y.2 := by
        have := congrArg Prod.snd heq
        simpa [g] using this
      exact mono_cyclic_power_sigma_fan hfan hvu i j
        (by omega) (by omega) h2
    · intro z hz
      rw [hf_eq] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      exact ⟨i, hi, rfl⟩
  rw [← finsum_mem_finset_eq_sum (fun i => azimIfan x V E y.1 y.2 i)
    (Finset.range n)]
  refine finsum_mem_eq_of_bijOn g hbij ?_
  intro i _
  have hterm : azimIfan x V E y.1 y.2 i =
      azimFan x V E y.1 ((sigmaFan x V E y.1)^[i] y.2) := by
    unfold azimIfan azimFan
    rw [if_pos (hcard y.1 hy1V), Function.iterate_succ_apply']
  rw [hterm]

/-- HOL Conforming.hl :1679-1686 `exists_point_in_node`

HOL 原文：
```
!x V E f. f IN node_set (hypermap1_of_fanx (x,V,E))
==> ?y. y IN f
```

编码说明：`node_set` ↔ `H.nodeSet`。

证明思路：`node_representation` 给出 `f = H.node x` 且 `x ∈ H.darts`；
`mem_node_self` 给出 `x ∈ H.node x`，取 `y = x` 即得。

候选已有引理：
- `Hypermap.node_representation`（Kepler/Text/Hypermap.lean:2790）
- `Hypermap.mem_node_self`（Kepler/Text/Hypermap.lean:859）
- 缺口：无 -/
theorem exists_point_in_node {x : V3} {V : Set V3} {E : Set (Set V3)}
    {f : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hf : f ∈ (hypermapOfFan x V E hfan).nodeSet) : ∃ y, y ∈ f := by
  obtain ⟨y, -, rfl⟩ := (hypermapOfFan x V E hfan).node_representation hf
  exact ⟨y, (hypermapOfFan x V E hfan).mem_node_self y⟩

/-- HOL Conforming.hl :1687-1717 `SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN`

HOL 原文：
```
!x V E f. FAN (x,V,E) /\ f IN node_set (hypermap1_of_fanx (x,V,E)) /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
                  ==>
                      sum f (\y. azim_fan x V E (pr2 y) (pr3 y))= &2 * pi
```

编码说明：`sum f g` ↔ `∑ᶠ y ∈ f, …`；`&2 * pi` ↔ `2 * Real.pi`；
`azim_fan` ↔ `azimFan`。

证明思路：由 `exists_point_in_node` 取 `y ∈ f`，用
`SUM_AZIM_FAN_OF_NODE_EQ_SUM_AZIM_I_FAN` 把 LHS 化为
`∑ i ∈ range ncard, azimIfan …`，再用 `SUM_AZIMS_EQ_2PI_FAN`（仓库
`sum_azims_eq_2pi`）收口。后者需 `setOfEdge y.1 ≠ {y.2}`，由
`properties_of_elements_in_node_fully_surroundedfan`（`{y.1,y.2} ∈ E`）
与 hcard 推出。

候选已有引理：
- `exists_point_in_node`（本文件上文，HOL :1679）
- `SUM_AZIM_FAN_OF_NODE_EQ_SUM_AZIM_I_FAN`（本文件上文，HOL :1626）
- `sum_azims_eq_2pi`（Kepler/Text/TopologyFan.lean:679，HOL `SUM_AZIMS_EQ_2PI_FAN`）
- `properties_of_elements_in_node_fully_surroundedfan`（本文件上文，HOL :1551）
- 缺口：HOL `remark1_fan` 未单列移植 -/
theorem SUM_AZIM_FAN_OF_NODE_EQ_2PI_I_FAN
    {x : V3} {V : Set V3} {E : Set (Set V3)} {f : Set (V3 × V3)}
    (hfan : FAN x V E)
    (hf : f ∈ (hypermapOfFan x V E hfan).nodeSet)
    (hcard : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard) :
    (∑ᶠ y ∈ f, azimFan x V E y.1 y.2) = 2 * Real.pi := by
  sorry
