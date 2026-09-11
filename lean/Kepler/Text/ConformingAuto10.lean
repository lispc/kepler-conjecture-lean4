/-
Port of the HOL Light Flyspeck `Conforming.hl` top-level theorems, batch 10
(Conforming.hl:2357-2633).

Source: `reference/flyspeck/text_formalization/fan/Conforming.hl`
(Flyspeck book formalization, Hoang Le Truong, 2010); persistent copies
`lean/scripts/conforming.hl` and
`/dev/shm/kepler-ref/flyspeck/text_formalization/fan/Conforming.hl`.

Coverage (batch 10, Conforming.hl:2357-2633):
- `condition_set_of_edge_eq_empty` (2357)
- `SET_OF_EDGE_INVARIANT` (2374)
- `expand_unions` (2381)
- `SIGMA_FAN_OF_FANADD1` (2394)
- `add_edge_graph` (2431)
- `not_in_set_of_edge` (2443)
- `set_of_only_edge` (2453)
- `set_of_only_edge1` (2462)
- `SIGMA_FAN_OF_FANADD_AT_POINT1` (2475)
- `SIGMA_FAN_OF_FANADD_AT_POINT2` (2577)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33).
- HOL `set_of_edge v V E` ↔ `setOfEdge v V E` (Kepler/Text/Fan.lean:62);
  HOL `sigma_fan` ↔ `sigmaFan` (Kepler/Text/Fan.lean:67); HOL `FAN(x,V,E)`
  ↔ `FAN x V E` (Kepler/Text/Fan.lean:56); HOL `fan80` ↔ `fan80`
  (Kepler/Text/Fan.lean:227).
- HOL `CARD (set_of_edge v V E) > 1` ↔ `1 < (setOfEdge v V E).ncard`
  (repo convention, cf. Kepler/Text/PlanarityDarts.lean:94).
- HOL `UNIONS E` ↔ `⋃₀ E` (`Set.sUnion`); `E UNION {{v,w}}` ↔
  `E ∪ {({v, w} : Set V3)}`; `{}` ↔ `∅`.
- HOL `condition_set_of_edge_eq_empty` and `expand_unions` are polymorphic
  in the point type `A`; the repo's `setOfEdge` is fixed to `V3`, so the
  ported statements are specialised to `V3` (the only instantiation used by
  the Flyspeck development). `expand_unions` is moreover Mathlib-general
  (`Set.sUnion_singleton`, Mathlib/Data/Set/Lattice.lean:853); it is kept
  here for batch completeness so the worker pool has the named target.
- The HOL proof of `SET_OF_EDGE_INVARIANT` uses `SET_OF_EDGE_UNION_GRAPH`
  (ported in ConformingAuto9.lean:344), and the `SIGMA_FAN_OF_FANADD*`
  proofs use `add_edge_imp_card_set_edge_ge1_fan`
  (ConformingAuto9.lean:376) and `add_edge_graph` (ConformingAuto9.lean:471).
  ConformingAuto9 is deliberately NOT imported here: HOL re-binds the name
  `add_edge_graph` at Conforming.hl:2431 (a different statement from
  ConformingAuto9's :2304), so importing both would duplicate the
  declaration. Proofs needing the batch-9 lemmas must restate them locally
  or use the Mathlib primitives directly.
- HOL `remark1_fan` (fan.hl:423) and `UNIQUE_SIGMA_FAN` (fan.hl:2107) are
  not ported under those names; the `SIGMA_FAN_OF_FANADD*` proof sketches
  note the closest available substitutes.
- Apart from `expand_unions` (see above) none of the ten statements is
  already in Mathlib; the rest mention the repo-specific
  `setOfEdge`/`sigmaFan`/`FAN`/`fan80` vocabulary.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 邻接集与并集的基本引理（Conforming.hl:2357-2468） -/

/-- HOL Conforming.hl :2357-2369 `condition_set_of_edge_eq_empty`

HOL 原文：
```
!v:A V E2.
~(v IN UNIONS E2)
==> set_of_edge v V E2= {}
```

编码说明：`UNIONS E2` ↔ `⋃₀ E2`；`set_of_edge` ↔ `setOfEdge`
（Fan.lean:62）；`{}` ↔ `∅`。HOL 对点类型 `A` 多态，仓库的 `setOfEdge`
固定为 `V3`，故此处特化到 `V3`。

证明思路：`setOfEdge v V E2` 展开为 `{w | {v,w} ∈ E2 ∧ w ∈ V}`。设 `w`
属于该集，则 `{v,w} ∈ E2`，取见证 `{v,w}` 由 `Set.mem_sUnion` 得
`v ∈ ⋃₀ E2`，与 `v ∉ ⋃₀ E2` 矛盾；由
`Set.eq_empty_iff_forall_not_mem` 得集合为空。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.mem_sUnion`、`Set.eq_empty_iff_forall_not_mem`、`Set.pair_comm`（Mathlib） -/
theorem condition_set_of_edge_eq_empty (v : V3) (V : Set V3) (E2 : Set (Set V3)) :
    v ∉ ⋃₀ E2 → setOfEdge v V E2 = ∅ := by
  intro h
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  rw [setOfEdge] at hw
  exact h (Set.mem_sUnion.mpr ⟨{v, w}, hw.1, by simp⟩)

/-- HOL Conforming.hl :2374-2378 `SET_OF_EDGE_INVARIANT`

HOL 原文：
```
!v V E1 E2.
~(v IN UNIONS E2)
==> set_of_edge v V (E1 UNION E2)= (set_of_edge v V E1)
```

编码说明：`UNIONS E2` ↔ `⋃₀ E2`；`UNION` ↔ `∪`；`set_of_edge` ↔
`setOfEdge`（Fan.lean:62）。

证明思路：由 `SET_OF_EDGE_UNION_GRAPH` 把
`setOfEdge v V (E1 ∪ E2)` 拆成 `setOfEdge v V E1 ∪ setOfEdge v V E2`；由
`condition_set_of_edge_eq_empty` 得 `v ∉ ⋃₀ E2` 时第二项为 `∅`，再用
`Set.union_empty` 收尾。

候选已有引理：
- `condition_set_of_edge_eq_empty`（本文件上文）
- `SET_OF_EDGE_UNION_GRAPH`（Kepler/Text/ConformingAuto9.lean:344；本文件未 import，需就地重述）
- `Set.union_empty`（Mathlib） -/
theorem SET_OF_EDGE_INVARIANT (v : V3) (V : Set V3) (E1 E2 : Set (Set V3)) :
    v ∉ ⋃₀ E2 → setOfEdge v V (E1 ∪ E2) = setOfEdge v V E1 := by
  intro h
  have hunion : setOfEdge v V (E1 ∪ E2) =
      setOfEdge v V E1 ∪ setOfEdge v V E2 := by
    ext w
    simp only [setOfEdge, Set.mem_setOf_eq, Set.mem_union, or_and_right]
  rw [hunion, condition_set_of_edge_eq_empty v V E2 h, Set.union_empty]

/-- HOL Conforming.hl :2381-2391 `expand_unions`

HOL 原文：
```
!v w:A. UNIONS {{v,w}}= {v,w}
```

编码说明：`UNIONS {{v,w}}` ↔ `⋃₀ ({{v, w}} : Set (Set V3))`。HOL 对点
类型 `A` 多态，此处特化到 `V3`。该命题是 Mathlib-general，Mathlib 的
`Set.sUnion_singleton`（Mathlib/Data/Set/Lattice.lean:853）即为它；此处
保留命名目标以维持 batch 完整性。

证明思路：`⋃₀ {s} = s`，直接 `exact Set.sUnion_singleton _`（或 `simp`）。

候选已有引理：
- `Set.sUnion_singleton`（Mathlib/Data/Set/Lattice.lean:853）
- `Set.sUnion_pair`（Mathlib/Data/Set/Lattice.lean:925） -/
theorem expand_unions (v w : V3) :
    ⋃₀ ({{v, w}} : Set (Set V3)) = {v, w} := by
  exact Set.sUnion_singleton _

/-- HOL Conforming.hl :2394-2423 `SIGMA_FAN_OF_FANADD1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 v w.
FAN(x,V,E)/\ FAN(x,V,E1)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
 /\ ~({v,w} IN E)
/\ E UNION {{v,w}}=E1
==> (!v1 w1. {v1,w1} IN E /\ ~(v1 IN {v,w})==> sigma_fan x V E1 v1 w1 = sigma_fan x V E v1 w1)
```

编码说明：`CARD (set_of_edge v V E) > 1` ↔
`1 < (setOfEdge v V E).ncard`；`E UNION {{v,w}}` ↔
`E ∪ {({v, w} : Set V3)}`；`sigma_fan` ↔ `sigmaFan`（Fan.lean:67）。HOL
内层 `!v` 与外层参数 `v` 同名（遮蔽），Lean 侧改名为 `v'`（alpha 等价）。

证明思路：对 `v1,w1` 取 `{v1,w1} ∈ E`；由
`add_edge_imp_card_set_edge_ge1_fan` 得 `1 < (setOfEdge v1 V E1).ncard`，
故 `setOfEdge v1 V E1 ≠ {w1}`；由 `SET_OF_EDGE_INVARIANT`（`v1 ∉ ⋃₀ {{v,w}}`
由 `expand_unions` 与 `v1 ∉ {v,w}` 给出）得
`setOfEdge v1 V E1 = setOfEdge v1 V E`；对 `E1` 用 `UNIQUE_SIGMA_FAN`、
对 `E` 用 `SIGMA_FAN` 即得 σ 值相等。

候选已有引理：
- `SET_OF_EDGE_INVARIANT`、`expand_unions`（本文件上文）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）
- 缺口：`remark1_fan`（fan.hl:423）、`UNIQUE_SIGMA_FAN`（fan.hl:2107）未移植 -/
private lemma setOfEdge_eq_of_add_edge (V : Set V3) (E E1 : Set (Set V3))
    (v w v1 : V3) (hE1 : E ∪ {{v, w}} = E1) (hv1 : v1 ∉ ({v, w} : Set V3)) :
    setOfEdge v1 V E1 = setOfEdge v1 V E := by
  ext u
  simp only [setOfEdge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨he, hu⟩
    rw [← hE1] at he
    rcases he with he | he
    · exact ⟨he, hu⟩
    · simp only [Set.mem_singleton_iff] at he
      exact absurd (he ▸ (by simp : v1 ∈ ({v1, u} : Set V3))) hv1
  · rintro ⟨he, hu⟩
    exact ⟨by rw [← hE1]; exact Or.inl he, hu⟩

theorem SIGMA_FAN_OF_FANADD1 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v w : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    ({v, w} : Set V3) ∉ E ∧
    E ∪ {{v, w}} = E1 →
    ∀ v1 w1 : V3, ({v1, w1} : Set V3) ∈ E ∧ v1 ∉ ({v, w} : Set V3) →
      sigmaFan x V E1 v1 w1 = sigmaFan x V E v1 w1 := by
  rintro ⟨-, -, -, -, hE1⟩ v1 w1 ⟨-, hv1⟩
  have h := setOfEdge_eq_of_add_edge V E E1 v w v1 hE1 hv1
  simp only [sigmaFan, h]

/-- HOL Conforming.hl :2431-2441 `add_edge_graph`

HOL 原文：
```
!v w E E1.
E UNION {{v,w}}=E1
==> {w,v} IN E1/\ {v,w}IN E1
```

编码说明：`E UNION {{v,w}}` ↔ `E ∪ {({v, w} : Set V3)}`；`E1` 为
`Set (Set V3)`，故 `{w,v}`/`{v,w}` 是 `Set V3` 的元素。注意 HOL 在
Conforming.hl:2304 与 :2431 两次以同名 `add_edge_graph` 绑定不同命题；
本文件对应 :2431 版本，且不 import ConformingAuto9（避免声明重名）。

证明思路：由 `h : E ∪ {{v,w}} = E1` 得 `{v,w} ∈ E1`
（`Set.mem_union_right` + `Set.mem_singleton`）；又 `{w,v} = {v,w}`
（`Set.pair_comm`），故 `{w,v} ∈ E1`。

候选已有引理：
- `Set.mem_union_right`、`Set.mem_singleton_iff`、`Set.pair_comm`（Mathlib） -/
theorem add_edge_graph (v w : V3) (E E1 : Set (Set V3)) :
    E ∪ {{v, w}} = E1 →
      ({w, v} : Set V3) ∈ E1 ∧ ({v, w} : Set V3) ∈ E1 := by
  intro h
  constructor
  · rw [← h]
    exact Set.mem_union_right E (by simp [Set.pair_comm])
  · rw [← h]
    exact Set.mem_union_right E (by simp)

/-- HOL Conforming.hl :2443-2449 `not_in_set_of_edge`

HOL 原文：
```
!v w V E. ~({w,v} IN E)
==> ~(w IN set_of_edge v V E)
```

编码说明：`set_of_edge` ↔ `setOfEdge`（Fan.lean:62）；`{w,v}` ↔
`({w, v} : Set V3)`。

证明思路：若 `w ∈ setOfEdge v V E`，则 `{v,w} ∈ E`，由 `Set.pair_comm`
得 `{w,v} ∈ E`，与 `{w,v} ∉ E` 矛盾。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.pair_comm`（Mathlib） -/
theorem not_in_set_of_edge (v w : V3) (V : Set V3) (E : Set (Set V3)) :
    ({w, v} : Set V3) ∉ E → w ∉ setOfEdge v V E := by
  intro h hw
  rw [setOfEdge, Set.mem_setOf_eq] at hw
  exact h ((Set.pair_comm v w) ▸ hw.1)

/-- HOL Conforming.hl :2453-2459 `set_of_only_edge`

HOL 原文：
```
!v w V. w IN V ==> set_of_edge v V {{v, w}}={w}
```

编码说明：`set_of_edge v V {{v, w}}` ↔
`setOfEdge v V ({{v, w}} : Set (Set V3))`；`{w}` ↔ `{w} : Set V3`。

证明思路：由 `w ∈ V` 且 `{v,w} ∈ {{v,w}}` 得 `w ∈ setOfEdge v V {{v,w}}`；
反之若 `u ∈ setOfEdge v V {{v,w}}`，则 `{v,u} = {v,w}`，由
`Set.pair_eq_pair_iff`（或 `Set.ext` + `simp`）与 `u ∈ V` 得 `u = w`，
故集合等于 `{w}`。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.pair_eq_pair_iff`、`Set.mem_singleton_iff`、`Set.ext`（Mathlib） -/
theorem set_of_only_edge (v w : V3) (V : Set V3) :
    w ∈ V → setOfEdge v V ({{v, w}} : Set (Set V3)) = {w} := by
  intro hw
  ext u
  simp only [setOfEdge, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨he, -⟩
    rcases (Set.pair_eq_pair_iff.mp he) with ⟨-, huw⟩ | ⟨hvw, huv⟩
    · exact huw
    · rw [huv, hvw]
  · rintro rfl
    exact ⟨by simp, hw⟩

/-- HOL Conforming.hl :2462-2468 `set_of_only_edge1`

HOL 原文：
```
!v w V. v IN V ==> set_of_edge w V {{v, w}}={v}
```

编码说明：`set_of_edge w V {{v, w}}` ↔
`setOfEdge w V ({{v, w}} : Set (Set V3))`；`{v}` ↔ `{v} : Set V3`。

证明思路：由 `v ∈ V` 且 `{w,v} = {v,w} ∈ {{v,w}}` 得
`v ∈ setOfEdge w V {{v,w}}`；反之若 `u ∈ setOfEdge w V {{v,w}}`，则
`{w,u} = {v,w}`，由 `Set.pair_eq_pair_iff` 与 `u ∈ V` 得 `u = v`，故
集合等于 `{v}`。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.pair_eq_pair_iff`、`Set.mem_singleton_iff`、`Set.pair_comm`（Mathlib） -/
theorem set_of_only_edge1 (v w : V3) (V : Set V3) :
    v ∈ V → setOfEdge w V ({{v, w}} : Set (Set V3)) = {v} := by
  intro hv
  ext u
  simp only [setOfEdge, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨he, -⟩
    rcases (Set.pair_eq_pair_iff.mp he) with ⟨hwv, huw⟩ | ⟨-, huv⟩
    · exact huw.trans hwv
    · exact huv
  · intro hu
    rw [hu]
    exact ⟨Set.pair_comm w v, hv⟩

/-! ## 加边对 σ 映射的影响（Conforming.hl:2475-2633） -/

/-- HOL Conforming.hl :2475-2572 `SIGMA_FAN_OF_FANADD_AT_POINT1`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 v u w.
FAN(x,V,E)/\ FAN(x,V,E1)
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E UNION {{v,w}}=E1
==> sigma_fan x V E1 v w = sigma_fan x V E v u
```

编码说明：`CARD (set_of_edge v V E) > 1` ↔
`1 < (setOfEdge v V E).ncard`；`E UNION {{v,w}}` ↔
`E ∪ {({v, w} : Set V3)}`；`fan80` ↔ `fan80`（Fan.lean:227）。HOL 内层
`!v` 与外层参数 `v` 同名（遮蔽），Lean 侧改名为 `v'`（alpha 等价）。

证明思路：由 `sigma_fan x V E u w = v` 与 `SIGMA_FAN` 得
`v ∈ setOfEdge u V E`；由 `add_edge_imp_card_set_edge_ge1_fan` 与
`SET_OF_EDGE_INVARIANT` 在 `E1 = E ∪ {{v,w}}` 上比较
`setOfEdge v V E` 与 `setOfEdge v V E1`（用 `add_edge_graph` 与
`not_in_set_of_edge` 排除 `w`，用 `set_of_only_edge` 定位唯一邻居），再对
`E1` 用 `UNIQUE_SIGMA_FAN` 把结论化为 `sigmaFan x V E v u ∈
setOfEdge v V E1`；角度比较用 `angle_is_small_fan`、`sum4_azim_fan`、
`azim_compl`、`AZIM_EQ_0_PI_EQ_COPLANAR`（`azim_eq_zero_iff` 替代）与
`fan80` 的凸性不等式。

候选已有引理：
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）、`fan80`（Kepler/Text/Fan.lean:227）
- `add_edge_graph`、`not_in_set_of_edge`、`set_of_only_edge`、
  `SET_OF_EDGE_INVARIANT`（本文件上文）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `angle_is_small_fan`（Kepler/Text/PlanarityAngle.lean:490）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296，AZIM_EQ_0_PI_EQ_COPLANAR 替代）
- 缺口：`remark1_fan`（fan.hl:423）、`UNIQUE_SIGMA_FAN`（fan.hl:2107）未移植 -/
theorem SIGMA_FAN_OF_FANADD_AT_POINT1 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v u w : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    fan80 x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    E ∪ {{v, w}} = E1 →
      sigmaFan x V E1 v w = sigmaFan x V E v u := by
  sorry

/-- HOL Conforming.hl :2577-2633 `SIGMA_FAN_OF_FANADD_AT_POINT2`

HOL 原文：
```
!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) E1 v u w.
FAN(x,V,E)/\ FAN(x,V,E1)
/\ {v,u} IN E /\ {u,w} IN E /\ ~({w,v} IN E)
/\ sigma_fan x V E u w = v
/\ fan80(x,V,E)
 /\ (!v. v IN V==>CARD (set_of_edge v V E) > 1)
/\ E UNION {{v,w}}=E1
==> sigma_fan x V E1 v u = w
```

编码说明：与 `SIGMA_FAN_OF_FANADD_AT_POINT1` 相同，仅结论换成
`sigmaFan x V E1 v u = w`；HOL 内层 `!v` 与外层参数 `v` 同名（遮蔽），
Lean 侧改名为 `v'`（alpha 等价）。

证明思路：由 `add_edge_graph` 得 `{v,w} ∈ E1`；由 `add_edge_imp_card_set_edge_ge1_fan`
得 `1 < (setOfEdge v V E1).ncard`，故 `setOfEdge v V E1 ≠ {u}`；对 `E1`
用 `UNIQUE_SIGMA_FAN` 把结论化为 `w ∈ setOfEdge v V E1`，由
`SET_OF_EDGE_INVARIANT` 与 `{v,w} ∈ E1` 给出；若 `setOfEdge v V E = {u}`
则与 `hcard` 及 `sigma_fan x V E u w = v` 矛盾，否则由 `SIGMA_FAN` 的
角度最小性（`angle_is_small_fan`、`sum4_azim_fan`、`azim_compl`）收尾。

候选已有引理：
- `SIGMA_FAN`（Kepler/Text/Fan.lean:317）、`fan80`（Kepler/Text/Fan.lean:227）
- `add_edge_graph`、`SET_OF_EDGE_INVARIANT`（本文件上文）
- `add_edge_imp_card_set_edge_ge1_fan`（Kepler/Text/ConformingAuto9.lean:376）
- `angle_is_small_fan`（Kepler/Text/PlanarityAngle.lean:490）
- `sum4_azim_fan`（Kepler/Text/TopologyFan.lean:1105）
- `properties_fully_surrounded`（Kepler/Text/Planarity.lean:2370）
- `azim_compl`（Kepler/Geom/AzimLemmas.lean:318）
- `azim_eq_zero_iff`（Kepler/Geom/AzimLemmas.lean:296，AZIM_EQ_0_PI_EQ_COPLANAR 替代）
- 缺口：`remark1_fan`（fan.hl:423）、`UNIQUE_SIGMA_FAN`（fan.hl:2107）未移植 -/
theorem SIGMA_FAN_OF_FANADD_AT_POINT2 (x : V3) (V : Set V3) (E E1 : Set (Set V3))
    (v u w : V3) :
    FAN x V E ∧ FAN x V E1 ∧
    ({v, u} : Set V3) ∈ E ∧ ({u, w} : Set V3) ∈ E ∧ ({w, v} : Set V3) ∉ E ∧
    sigmaFan x V E u w = v ∧
    fan80 x V E ∧
    (∀ v' : V3, v' ∈ V → 1 < (setOfEdge v' V E).ncard) ∧
    E ∪ {{v, w}} = E1 →
      sigmaFan x V E1 v u = w := by
  sorry

end Kepler.Text
