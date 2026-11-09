/-
  Kepler.Text.Reduction3Thm9 — J 战役 T9 纯列表批（4 件：replace 成员族）。

  ┌─ 逐件对账（reduction3.hl）──────────────────────────────────────
  │   mem_replace   :3096 → t9_mem_replace
  │   mem_replace3  :3111 → t9_mem_replace3（核心，单归纳证成一般成员刻画）
  │   replace_filter2 :3079 → t9_replace_filter2
  │   replace_filter3 :3126 → t9_replace_filter3
  │ 依赖 def 就位性：树 `Kepler.Graphs.replace`（ListAux.lean:55）与 HOL
  │ `replace`（tame_defs.hl:317）逐字同形（首现替换、`if z == x`）。
  │ 世界匹配：`uniq ↦ List.Nodup`、`MEM ↦ ∈`、`filter ↦ List.filter`；
  │ BEq 由 `[LawfulBEq]` 与 `=` 对齐（`beq_iff_eq`）。无第二定义族。
  │ 门禁：零 J2（纯列表，无 AQ/assumption 依赖）；J3 门禁不适用。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」；
  │ if 重写：真支 `if_pos (beq_iff_eq.mpr h)`、假支 `if_neg (… beq_iff_eq.mp)`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Graphs.ListAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

/-! ## §A 核心：`replace` 的一般成员刻画（mem_replace3 的推广）

`uniq xs` 下，`h ∈ replace old news xs ↔ (h ∈ news ∧ old ∈ xs) ∨ (h ∈ xs ∧ h ≠ old)`。
`old ∈ xs` 不必前提（不在时 `replace` 原样返回，两边的 `h ∈ news ∧ False` 自动消去）。 -/
theorem t9_mem_replace_gen {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (hnd : xs.Nodup) (h old : α) (news : List α) :
    h ∈ Kepler.Graphs.replace old news xs
      ↔ (h ∈ news ∧ old ∈ xs) ∨ (h ∈ xs ∧ h ≠ old) := by
  induction xs with
  | nil =>
    simp [Kepler.Graphs.replace]
  | cons z zs ih =>
    obtain ⟨hznot, hnd'⟩ := List.nodup_cons.mp hnd
    rw [Kepler.Graphs.replace]
    by_cases hz : z = old
    · -- 首元素即 old：结果 = news ++ zs
      rw [if_pos (beq_iff_eq.mpr hz)]
      have hmemz : h ∈ z :: zs ↔ (h = z ∨ h ∈ zs) := by
        simp only [List.mem_cons]
      have holdz : old ∈ z :: zs := List.mem_cons.mpr (Or.inl hz.symm)
      rw [hmemz]
      simp only [List.mem_append]
      constructor
      · rintro (hn | hm)
        · exact Or.inl ⟨hn, holdz⟩
        · exact Or.inr ⟨Or.inr hm, fun he => hznot ((he.trans hz.symm) ▸ hm)⟩
      · rintro (⟨hn, _⟩ | ⟨hmo | hm, hne⟩)
        · exact Or.inl hn
        · exact absurd (hmo.trans hz) hne
        · exact Or.inr hm
    · -- 首元素不是 old：结果 = z :: replace old news zs
      rw [if_neg (fun hcon : (z == old) = true => hz (beq_iff_eq.mp hcon))]
      have ih' := ih hnd'
      have hzcons : h ∈ z :: Kepler.Graphs.replace old news zs
          ↔ (h = z ∨ h ∈ Kepler.Graphs.replace old news zs) := by
        simp only [List.mem_cons]
      have hmemz : h ∈ z :: zs ↔ (h = z ∨ h ∈ zs) := by
        simp only [List.mem_cons]
      have holdz : old ∈ z :: zs ↔ old ∈ zs := by
        simp only [List.mem_cons]
        constructor
        · rintro (he | hm)
          · exact absurd he.symm hz
          · exact hm
        · exact fun hm => Or.inr hm
      rw [hzcons, ih', hmemz, holdz]
      have hfact : h = z → h ≠ old := fun he hzo => hz (he ▸ hzo)
      grind

/-! ## §B `mem_replace3`（reduction3.hl:3111） -/

/-- HOL `mem_replace3`（reduction3.hl:3111）：
`uniq xs ∧ MEM old xs ==> (MEM h (replace old news xs) ↔ MEM h news ∨ (MEM h xs ∧ ~(h = old)))`。 -/
theorem t9_mem_replace3 {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (h old : α) (news : List α) (hnd : xs.Nodup)
    (hold : old ∈ xs) :
    h ∈ Kepler.Graphs.replace old news xs ↔ h ∈ news ∨ (h ∈ xs ∧ h ≠ old) := by
  rw [t9_mem_replace_gen xs hnd h old news]
  grind

/-! ## §C `mem_replace`（reduction3.hl:3096） -/

/-- HOL `mem_replace`（reduction3.hl:3096）：
`uniq xs ∧ MEM old xs ==> (MEM h (replace old news xs) ↔ MEM h (replace old [] xs) ∨ MEM h news)`。 -/
theorem t9_mem_replace {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (h old : α) (news : List α) (hnd : xs.Nodup)
    (hold : old ∈ xs) :
    h ∈ Kepler.Graphs.replace old news xs
      ↔ h ∈ Kepler.Graphs.replace old [] xs ∨ h ∈ news := by
  rw [t9_mem_replace_gen xs hnd h old news]
  rw [t9_mem_replace_gen xs hnd h old []]
  simp only [List.not_mem_nil, false_and]
  grind

/-! ## §D `replace_filter2`（reduction3.hl:3079） -/

/-- HOL `replace_filter2`（reduction3.hl:3079）：
`P old ∧ uniq xs ==> (MEM u (replace old (filter P news) (filter P xs))
↔ MEM u (filter P (replace old news xs)))`。 -/
theorem t9_replace_filter2 {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (P : α → Bool) (u old : α) (news : List α)
    (hP : P old = true) (hnd : xs.Nodup) :
    u ∈ Kepler.Graphs.replace old (news.filter P) (xs.filter P)
      ↔ u ∈ (Kepler.Graphs.replace old news xs).filter P := by
  have hndf : (xs.filter P).Nodup := List.Pairwise.filter P hnd
  simp only [List.mem_filter]
  rw [t9_mem_replace_gen (xs.filter P) hndf u old (news.filter P)]
  rw [t9_mem_replace_gen xs hnd u old news]
  simp only [List.mem_filter, hP]
  grind

/-! ## §E `replace_filter3`（reduction3.hl:3126） -/

/-- HOL `replace_filter3`（reduction3.hl:3126）：
`P old ∧ uniq xs ∧ MEM old xs ==>
((MEM u (replace old [] (filter P xs)) ∨ MEM u (filter P news))
 ↔ MEM u (filter P (replace old news xs)))`。 -/
theorem t9_replace_filter3 {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (P : α → Bool) (u old : α) (news : List α)
    (hP : P old = true) (hnd : xs.Nodup) (hold : old ∈ xs) :
    (u ∈ Kepler.Graphs.replace old [] (xs.filter P) ∨ u ∈ news.filter P)
      ↔ u ∈ (Kepler.Graphs.replace old news xs).filter P := by
  simp only [List.mem_filter]
  rw [t9_mem_replace_gen (xs.filter P) (List.Pairwise.filter P hnd) u old []]
  rw [t9_mem_replace_gen xs hnd u old news]
  simp only [List.mem_filter, hP, List.not_mem_nil, false_and]
  grind

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t9_mem_replace_gen
#print axioms Kepler.Text.Reduction3.t9_mem_replace3
#print axioms Kepler.Text.Reduction3.t9_mem_replace
#print axioms Kepler.Text.Reduction3.t9_replace_filter2
#print axioms Kepler.Text.Reduction3.t9_replace_filter3
