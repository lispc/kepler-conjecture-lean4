/-
  Kepler.Text.Reduction1W2a — J4 Wave W2 批 1a（编排者按车道冻结包
  `DELIVERY_W2A_ROTATE.md` 收口）：`size_rotate_to`（HOL reduction1.hl:1423）
  + `mem_rotate_to2`（:1576）。

  路线（冻结包 §2 自建，绕开 `splitAt_is_prefix` 的 `is_prefix` 形）：
  `splitAtRec` 三层归纳自建精确分解
  `splitAtSpec : splitAt c as = (bef, aft) → c ∈ as → as = bef ++ c :: aft`，
  两件各 5–8 行。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.TameList54

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Text.TameSpine (rotateTo)

/-! ## §1 `splitAt` 精确分解（`splitAtRec` 归纳） -/

/-- `splitAtRec` 的精确分解（广义 `bs`）：命中时 `bs ++ as = bef ++ c :: aft`。 -/
private theorem splitAtRecSpec {α : Type} [BEq α] [LawfulBEq α] {c : α}
    (bs as : List α) (bef aft : List α) (hc : c ∈ as)
    (h : Kepler.Graphs.splitAtRec c bs as = (bef, aft)) :
    bs ++ as = bef ++ c :: aft := by
  revert bs bef aft hc h
  induction as with
  | nil =>
    intro bs bef aft hc h
    simp at hc
  | cons a t ih =>
    intro bs bef aft hc h
    simp only [Kepler.Graphs.splitAtRec] at h
    by_cases hca : (a == c) = true
    · rw [if_pos hca] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [eq_of_beq hca]
    · rw [if_neg hca] at h
      have hct : c ∈ t := by
        rcases List.mem_cons.mp hc with hca' | hct
        · have hh : (a == c) = true := by rw [hca']; exact beq_self_eq_true a
          exact absurd hh hca
        · exact hct
      have := ih (bs ++ [a]) bef aft hct h
      rw [List.append_assoc] at this
      simpa using this

/-- `splitAt` 的精确分解：`c ∈ as` 时 `as = bef ++ c :: aft`。 -/
theorem splitAtSpec {α : Type} [BEq α] [LawfulBEq α] {c : α} {as bef aft : List α}
    (h : Kepler.Graphs.splitAt c as = (bef, aft)) (hc : c ∈ as) :
    as = bef ++ c :: aft := by
  have := splitAtRecSpec [] as bef aft hc h
  simpa using this

/-! ## §2 两件 rotate_to -/

/-- **HOL `size_rotate_to`**（reduction1.hl:1423）：
`MEM v vs ∧ uniq vs ⇒ |rotate_to vs v| = |vs|`。 -/
theorem sizeRotateTo {α : Type} [BEq α] [LawfulBEq α] {vs : List α} {v : α}
    (hv : v ∈ vs) (hnd : vs.Nodup) : (rotateTo vs v).length = vs.length := by
  have hspec : vs = (Kepler.Graphs.splitAt v vs).1 ++ v :: (Kepler.Graphs.splitAt v vs).2 :=
    splitAtSpec rfl hv
  unfold Kepler.Text.TameSpine.rotateTo
  conv_rhs => rw [hspec]
  simp only [List.length_cons, List.length_append]
  omega

/-- **HOL `mem_rotate_to2`**（reduction1.hl:1576）：
`MEM v vs ∧ uniq vs ⇒ (MEM u vs ↔ MEM u (rotate_to vs v))`。 -/
theorem memRotateTo2 {α : Type} [BEq α] [LawfulBEq α] {vs : List α} {v u : α}
    (hv : v ∈ vs) (hnd : vs.Nodup) : u ∈ vs ↔ u ∈ rotateTo vs v := by
  have hspec : vs = (Kepler.Graphs.splitAt v vs).1 ++ v :: (Kepler.Graphs.splitAt v vs).2 :=
    splitAtSpec rfl hv
  unfold Kepler.Text.TameSpine.rotateTo
  conv_lhs => rw [hspec]
  constructor
  · intro hu
    rcases List.mem_append.mp hu with hb | hva
    · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hb))
    · rcases List.mem_cons.mp hva with hvu | ha
      · exact hvu ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl ha))
  · intro hu
    rcases List.mem_cons.mp hu with hvu | h'
    · exact hvu ▸ List.mem_append.mpr (Or.inr List.mem_cons_self)
    · rcases List.mem_append.mp h' with ha | hb
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ ha))
      · exact List.mem_append.mpr (Or.inl hb)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.splitAtSpec
#print axioms Kepler.Text.Reduction1.sizeRotateTo
#print axioms Kepler.Text.Reduction1.memRotateTo2
