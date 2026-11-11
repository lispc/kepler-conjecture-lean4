/-
  Kepler.Text.Reduction4K4C0 — K4-C0 第一轮：`ifbetwn_indexf`
  （reduction4.hl:3948-4045）。

  **`indexf0` 判词（免重落）**：tame_list.hl 的两件 `indexf0` 在库已覆盖：
  · :1473 `indexf x y [] = 0` —— 定义级 `simp [indexf]`（本文件不另立）；
  · :1542 `MEM x s ∧ MEM y s ∧ indexf x y s = 0 ⇒ x = y` —— 在库
    `Kepler.Text.Reduction4.indexf_eq_zero`（Reduction4.lean:782，同名同形）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5BetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4

open Kepler.Text.Reduction5 (ifbetwn indexf)

/-- HOL `indexf0`（tame_list.hl:1473）：`indexf x y [] = 0`。
（:1542 的第二件 `indexf0` = 在库 `indexf_eq_zero`，不另立。） -/
theorem indexf0 {α : Type} [DecidableEq α] (x y : α) :
    indexf x y ([] : List α) = 0 := by
  simp [indexf]

/-- HOL `ifbetwn_indexf`（reduction4.hl:3948-3967）：
`MEM x s ∧ MEM y s ∧ MEM z s ∧ uniq s ⇒
 (MEM y (ifbetwn s x z) ↔ 0 < indexf x y s ∧ indexf x y s ≤ indexf x z s)`。 -/
theorem ifbetwnIndexf {α : Type} [DecidableEq α] {s : List α} {x y z : α}
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hnd : s.Nodup) :
    y ∈ ifbetwn s x z ↔ 0 < indexf x y s ∧ indexf x y s ≤ indexf x z s := by
  by_cases hxz : x = z
  · have hzz : ifbetwn s x z = [] := by
      rw [hxz]; exact ifbetwnRefl s z
    rw [hzz]
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨hpos, hle⟩
    rw [hxz] at hpos hle
    rw [indexfRefl hz] at hle
    omega
  · unfold ifbetwn
    rw [if_pos (⟨hx, hz, hxz⟩ : x ∈ s ∧ z ∈ s ∧ x ≠ z)]
    rw [List.mem_append, List.mem_singleton]
    constructor
    · rintro (hbet | hyz)
      · have h := (Kepler.Text.Reduction5.indexfBetwnEq hxz hnd hx hz).mp hbet
        exact ⟨h.1, Nat.le_of_lt h.2⟩
      · subst hyz
        refine ⟨?_, Nat.le_refl _⟩
        exact Nat.pos_of_ne_zero (fun h0 => hxz (indexf_eq_zero hx hz h0))
    · rintro ⟨hpos, hle⟩
      by_cases hyz : y = z
      · exact Or.inr hyz
      · left
        have hlt : indexf x y s < indexf x z s := by
          rcases Nat.lt_or_eq_of_le hle with h | h
          · exact h
          · exact absurd ((indexfInj hx hy hz).mp h) hyz
        exact (Kepler.Text.Reduction5.indexfBetwnEq hxz hnd hx hz).mpr ⟨hpos, hlt⟩

end Kepler.Text.Reduction4

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction4.indexf0
#print axioms Kepler.Text.Reduction4.ifbetwnIndexf
