/-
LocalAuto7W22a: W22a — `fully_surrounded_imp_conforming` 的**条件形**
（唯一槽 `fan80`；其余三前提由 `PIIJBJK` + `yk6_fs_ncard_gt1` 就地供给）。

## 件

`p22a_fully_surrounded_imp_conforming`：
`FAN 0 V E → FullySurrounded V E → fan80 0 V E → conformingFan 0 V E hfan`

HOL `fully_surrounded_imp_conforming`（`add_triangle-compiled.hl:652`，证明体 3 行）
= `PIIJBJK` + `fully_surrounded_imp_fan80` + `fully_surrounded_card_set_of_edge1`。
本件：`PIIJBJK`（`ConformingAuto21:903`，std3）直接给出 `conformingFan` 的五合取，
只需它的三前提：

* `FAN x V E` —— 前件；
* `∀ v' ∈ V, 1 < (setOfEdge v' V E).ncard` —— **HOL `fully_surrounded_card_set_of_edge1`
  的逐点形**：树内 `yk6_fs_ncard_gt1`（TameLp:7727）是**逐 dart 形**，本件补「每点有邻居」
  （由 `FullySurrounded` 在 `dartOfFan` 的自环分支上排除孤立点，~12 行）后逐点提升；
* `fan80 x V E` —— **唯一显式槽**（W22b 的目标）。

## 同批 TameLp 可见性（1 行，陈述零改）

`yk6_fs_ncard_gt1`（`:7727`）`private theorem` → `theorem`。

W21 / W13A–F / LA2 / LA9 / Conforming* 零改动。
-/
import Kepler.Text.LocalAuto7W21
import Kepler.Text.ConformingDefs
import Kepler.Text.ConformingAuto21

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-- **`FullySurrounded` ⇒ 每点有邻居**（HOL `fully_surrounded_card_set_of_edge1` 的
孤立点排除步）：若 `v ∈ V` 无邻边，则自环 `(v,v) ∈ dartOfFan`，而 `azimDart (v,v) = 2π`，
撞 `FullySurrounded` 的 `< π`。 -/
theorem p22a_fs_has_edge {V : Set V3} {E : Set (Set V3)} (hfs : FullySurrounded V E) :
    ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  intro v hv
  by_contra hcon
  have hiso : setOfEdge v V E = ∅ := by
    rw [show setOfEdge v V E = {w : V3 | {v, w} ∈ E ∧ w ∈ V} from rfl]
    ext w
    constructor
    · intro hw
      exact absurd ⟨w, hw.1⟩ hcon
    · intro hw
      exact hw.elim
  have hd : (v, v) ∈ dartOfFan V E :=
    Set.mem_union_left _ ⟨rfl, hv, hiso⟩
  have hπ := hfs (v, v) hd
  have h2pi : azimDart V E (v, v) = 2 * Real.pi := by
    unfold azimDart
    rw [if_pos rfl]
  rw [h2pi] at hπ
  linarith [Real.pi_pos]

/-- **HOL `fully_surrounded_card_set_of_edge1`（逐点形）**：
`FullySurrounded V E → ∀ v ∈ V, 1 < (setOfEdge v V E).ncard`
（`yk6_fs_ncard_gt1` 的逐 dart 形 + `p22a_fs_has_edge` 提升到每点）。 -/
theorem p22a_fs_ncard_gt1 {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    (hfs : FullySurrounded V E) : ∀ v ∈ V, 1 < (setOfEdge v V E).ncard := by
  intro v hv
  obtain ⟨w, hw⟩ := p22a_fs_has_edge hfs v hv
  exact yk6_fs_ncard_gt1 hfan hfs (show (v, w) ∈ dart1OfFan V E from hw)

/-- **HOL `fully_surrounded_imp_conforming`（条件形）**：`FAN` + `FullySurrounded` +
**`fan80`（唯一槽）** ⇒ `conformingFan`。证明 = `PIIJBJK`（三前提齐）。 -/
theorem p22a_fully_surrounded_imp_conforming {V : Set V3} {E : Set (Set V3)}
    (hfan : FAN 0 V E) (hfs : FullySurrounded V E) (h80 : fan80 0 V E) :
    conformingFan 0 V E hfan :=
  PIIJBJK 0 V E hfan ⟨hfan, p22a_fs_ncard_gt1 hfan hfs, h80⟩

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22a_fs_has_edge
#print axioms Kepler.Text.p22a_fs_ncard_gt1
#print axioms Kepler.Text.p22a_fully_surrounded_imp_conforming

end Kepler.Text
