/-
LocalAuto7W22b: W22b — `fully_surrounded_imp_fan80`（HOL add_triangle:260，证明体 3 行）
+ 其 5 个未移植依赖。

## 件表

| # | 件 | = HOL | 行 |
|---|---|---|---|
| 1 | `p22b_inE_imp_in_dart` | `inE_imp_in_dart` | 3 |
| 2 | `p22b_azimDart_dart1` | `azim_dart1_eq_azim` | ~10 |
| 3 | `p22b_fs_dartOfFan_eq` | `fully_surrounded_dart_of_fan_eq` | ~18 |
| 4 | `p22b_fs_azimDart_eq` | `fully_surrounded_azim_dart_eq_azim` | ~10 |
| 5 | **`p22b_azimDart_pos`** | **`AZIM_DART_POS`**（`0 < azimDart`，`0 < azim` 半的真证点） | ~55 |
| 6 | **`p22b_fully_surrounded_imp_fan80`** | `fully_surrounded_imp_fan80` | ~12 |

## `AZIM_DART_POS` 的陈述与「1 价」探针（**不需要度前提**）

`azimDart V E d = if d.1 = d.2 then 2π else azimFan 0 V E d.1 d.2`，
`azimFan x V E v w = if 1 < (setOfEdge v V E).ncard then azim x v w (sigmaFan x V E v w) else 2π`
（本批 `#print` 原文，`logs/probe_w22b2.log`）。

⇒ **1 价顶点**（`setOfEdge v V E = {w}`，`ncard = 1`）处 `azimDart = 2π ≠ 0`（走 **else 分支**，
`azim` 根本不被求值），孤立点自环亦 `2π`。故 HOL 原形（只带 `FAN`）在 Lean 下**为真**，
**不需要**度 ≥ 2 前提；HOL `2640-2678` 的 else 分支也确实是 `MATCH_MP_TAC REAL_LT_MUL`
+ `PI_POS`（即 `2π > 0`），**不是**矛盾支。

唯一非平凡支是 `1 < ncard`：`0 ≤ azim`（`azim_nonneg`）+ `azim ≠ 0`（若 `= 0` 则
`unique_azim0_point_fan`（Fan.lean:456）给 `d.2 = sigmaFan …`，撞 `SIGMA_FAN` 的
`sigmaFan … ≠ d.2`）。

W22a / W21 / W13A–F / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22a

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-! ## 1. `{v,u} ∈ E ⇒ (v,u) ∈ dartOfFan` -/

/-- `dart1OfFan V E = {d | {d.1,d.2} ∈ E}`（Fan.lean:86）⇒ 边即 dart。 -/
theorem p22b_inE_imp_in_dart {V : Set V3} {E : Set (Set V3)} {v u : V3}
    (h : {v, u} ∈ E) : (v, u) ∈ dartOfFan V E :=
  Set.mem_union_right _ h

/-! ## 2. `azimDart` 在 dart1 上等于 `azim 0 v u (sigmaFan …)` -/

/-- `d ∈ dart1OfFan` 且 `1 < ncard` ⇒ `azimDart` 展开为 `azim 0 d.1 d.2 (sigmaFan …)`
（HOL `azim_dart1_eq_azim`）。 -/
theorem p22b_azimDart_dart1 {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hfan : FAN 0 V E) (hd : d ∈ dart1OfFan V E)
    (hcard : 1 < (setOfEdge d.1 V E).ncard) :
    azimDart V E d = azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2) := by
  have hne : d.1 ≠ d.2 := edge_ne_of_fan hfan hd
  unfold Fan.azimDart Fan.azimFan
  rw [if_neg hne, if_pos hcard]

/-! ## 3. `FullySurrounded ⇒ dartOfFan = dart1OfFan`（无孤立点） -/

/-- HOL `fully_surrounded_dart_of_fan_eq`：`FullySurrounded` 排除孤立点，
故 `dartOfFan` 的自环部分为空。 -/
theorem p22b_fs_dartOfFan_eq {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) :
    dartOfFan V E = dart1OfFan V E := by
  have hempty : {d : V3 × V3 | d.1 = d.2 ∧ d.1 ∈ V ∧ setOfEdge d.1 V E = ∅} = ∅ := by
    ext d
    constructor
    · rintro ⟨-, h1V, hiso⟩
      obtain ⟨w, hw⟩ := p22a_fs_has_edge hfs d.1 h1V
      have hmem : w ∈ setOfEdge d.1 V E :=
        (properties_of_setOfEdge_fan 0 V E d.1 w hfan).mp hw
      rw [hiso] at hmem
      exact absurd hmem (Set.notMem_empty w)
    · intro h
      exact absurd h (Set.notMem_empty d)
  unfold dartOfFan
  rw [hempty, Set.empty_union]

/-! ## 4. `FullySurrounded` 下 `azimDart` 的 `azim` 形 -/

/-- HOL `fully_surrounded_azim_dart_eq_azim`：`d ∈ dartOfFan` 时
`azimDart = azim 0 d.1 d.2 (sigmaFan …)`。 -/
theorem p22b_fs_azimDart_eq {V : Set V3} {E : Set (Set V3)} {d : V3 × V3}
    (hfan : FAN 0 V E) (hfs : FullySurrounded V E) (hd : d ∈ dartOfFan V E) :
    azimDart V E d = azim 0 d.1 d.2 (sigmaFan 0 V E d.1 d.2) := by
  have hd1 : d ∈ dart1OfFan V E := by
    rw [← p22b_fs_dartOfFan_eq hfan hfs]
    exact hd
  have hd1V : d.1 ∈ V :=
    hfan.1 (Set.mem_sUnion_of_mem (Set.mem_insert d.1 {d.2}) hd1)
  exact p22b_azimDart_dart1 hfan hd1 (p22a_fs_ncard_gt1 hfan hfs d.1 hd1V)

/-! ## 5. `AZIM_DART_POS`：`0 < azimDart` -/

/-- **HOL `AZIM_DART_POS`**（hypermap_and_fan.hl:2627）：`FAN` + `d ∈ dartOfFan`
⇒ `0 < azimDart`。**不需要度前提**（1 价/孤立走 `2π` 分支，见文件头探针）；
`1 < ncard` 支用 `azim_nonneg` + `unique_azim0_point_fan` 反证 `azim ≠ 0`。 -/
theorem p22b_azimDart_pos {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E) :
    ∀ d ∈ dartOfFan V E, 0 < azimDart V E d := by
  intro d hd
  unfold Fan.azimDart Fan.azimFan
  by_cases heq : d.1 = d.2
  · rw [if_pos heq]
    linarith [Real.pi_pos]
  · rw [if_neg heq]
    by_cases hcard : 1 < (setOfEdge d.1 V E).ncard
    · rw [if_pos hcard]
      have hd1 : d ∈ dart1OfFan V E := by
        have hu := hd
        unfold dartOfFan at hu
        rcases hu with hiso | h1
        · exact absurd hiso.1 heq
        · exact h1
      have hmem : d.2 ∈ setOfEdge d.1 V E :=
        (properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mp hd1
      have hne : setOfEdge d.1 V E ≠ {d.2} := by
        intro h
        rw [h, Set.ncard_singleton] at hcard
        omega
      obtain ⟨hσmem, hσne, -⟩ := SIGMA_FAN hne hfan hmem
      have hw : {d.1, d.2} ∈ E :=
        (properties_of_setOfEdge_fan 0 V E d.1 d.2 hfan).mpr hmem
      have hwσ : {d.1, sigmaFan 0 V E d.1 d.2} ∈ E :=
        (properties_of_setOfEdge_fan 0 V E d.1 (sigmaFan 0 V E d.1 d.2) hfan).mpr hσmem
      refine lt_of_le_of_ne (azim_nonneg _ _ _ _) ?_
      intro h0
      exact (Ne.symm hσne) (unique_azim0_point_fan hfan hw hwσ h0.symm)
    · rw [if_neg hcard]
      linarith [Real.pi_pos]

/-! ## 6. 装配：`fully_surrounded_imp_fan80` -/

/-- **HOL `fully_surrounded_imp_fan80`**：`FAN` + `FullySurrounded` ⇒ `fan80 0 V E`
（`0 <` 半 = 件 5，`< π` 半 = `FullySurrounded` 本身，桥 = 件 4）。 -/
theorem p22b_fully_surrounded_imp_fan80 {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hfs : FullySurrounded V E) : fan80 0 V E := by
  intro v u hvu
  have hd : (v, u) ∈ dartOfFan V E := p22b_inE_imp_in_dart hvu
  have heq := p22b_fs_azimDart_eq hfan hfs hd
  rw [← heq]
  exact ⟨p22b_azimDart_pos hfan (v, u) hd, hfs (v, u) hd⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22b_inE_imp_in_dart
#print axioms Kepler.Text.p22b_azimDart_dart1
#print axioms Kepler.Text.p22b_fs_dartOfFan_eq
#print axioms Kepler.Text.p22b_fs_azimDart_eq
#print axioms Kepler.Text.p22b_azimDart_pos
#print axioms Kepler.Text.p22b_fully_surrounded_imp_fan80

end Kepler.Text
