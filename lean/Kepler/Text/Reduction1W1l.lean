/-
  Kepler.Text.Reduction1W1l — J4 Wave W1 批 6 §2（编排者按车道冻结包
  `DELIVERY_W1L_S2_FROZEN.md` 收口，2026-11-10）：
  `containsUnacceptableEdge_explicit`（HOL `reduction1.hl:401-:477`，77 HOL）。

  结构：E0/E1 空表/一元素支 `simp`；E2 `[a,b]` 用 `ltIffNeOfLe` 把 `<` 槽
  互化成 `≠`；E3 长度 ≥ 3 用 §1 的 aux（`v := a`，槽由 `hmono 0` 供给）+
  ∃ 拆分平移（`edgeShift`）+ `2 ≤` 算术归一。

  DIFFERS：`EL` ↦ `getElem!`（C2）；`HD e` ↦ `e[0]!`；`sizel` ↦ `List.length`；
  `N x y`（Bool 当 Prop）↦ `N x y = true`；全程 `Nat`（本链只 import Plane，
  `ℕ` 记号不可用）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W1k

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (containsUnacceptableEdge containsUnacceptableEdgeSnd)

/-- `a ≤ b ⇒ a < b ↔ a ≠ b`（W1k 私件的本地副本，跨文件不可见）。 -/
private theorem ltIffNeOfLe' {a b : Nat} (h : a ≤ b) : a < b ↔ a ≠ b := by
  constructor <;> intro h' <;> omega

/-- 尾表平移：`(a::b::c::u')` 上的 ∃ 支 ⟺ 首三元组支 ∨ `(b::c::u')` 上的 ∃ 支。 -/
private theorem edgeShift {N : Nat → Nat → Bool} {a b c : Nat} {u' : List Nat} :
    (∃ i, i + 2 < (a :: b :: c :: u').length ∧
        (a :: b :: c :: u')[i]! ≠ (a :: b :: c :: u')[i + 1]! ∧
        (a :: b :: c :: u')[i + 1]! ≠ (a :: b :: c :: u')[i + 2]! ∧
        N (a :: b :: c :: u')[i + 1]! (a :: b :: c :: u')[i + 2]! = true) ↔
      ((a ≠ b ∧ b ≠ c ∧ N b c = true) ∨
        (∃ j, j + 2 < (b :: c :: u').length ∧
          (b :: c :: u')[j]! ≠ (b :: c :: u')[j + 1]! ∧
          (b :: c :: u')[j + 1]! ≠ (b :: c :: u')[j + 2]! ∧
          N (b :: c :: u')[j + 1]! (b :: c :: u')[j + 2]! = true)) := by
  constructor
  · rintro ⟨i, hi, h1, h2, hN⟩
    cases i with
    | zero =>
      simp only [Nat.zero_add, List.getElem!_cons_zero, List.getElem!_cons_succ] at h1 h2 hN
      exact Or.inl ⟨h1, h2, hN⟩
    | succ j =>
      right
      have hj : j + 2 < (b :: c :: u').length := by
        simp only [List.length_cons] at hi ⊢
        omega
      refine ⟨j, hj, ?_, ?_, ?_⟩
      · simpa only [List.getElem!_cons_succ] using h1
      · simpa only [List.getElem!_cons_succ] using h2
      · simpa only [List.getElem!_cons_succ] using hN
  · rintro (⟨hab, hbc, hN⟩ | ⟨j, hj, h1, h2, hN⟩)
    · refine ⟨0, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simpa only [Nat.zero_add, List.getElem!_cons_zero, List.getElem!_cons_succ] using hab
      · simpa only [Nat.zero_add, List.getElem!_cons_zero, List.getElem!_cons_succ] using hbc
      · simpa only [Nat.zero_add, List.getElem!_cons_zero, List.getElem!_cons_succ] using hN
    · refine ⟨j + 1, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at hj ⊢; omega
      · simpa only [List.getElem!_cons_succ] using h1
      · simpa only [List.getElem!_cons_succ] using h2
      · simpa only [List.getElem!_cons_succ] using hN

/-- **HOL `containsUnacceptableEdge_explicit`**（`reduction1.hl:401-:477`）：
单调性 ⇒ `containsUnacceptableEdge` 的显式形。 -/
theorem containsUnacceptableEdgeExplicit {N : Nat → Nat → Bool} {e : List Nat}
    (hmono : ∀ i, i + 1 < e.length → e[i]! ≤ e[i + 1]!) :
    (containsUnacceptableEdge N e = true ↔
      2 ≤ e.length ∧
        ((e[0]! ≠ e[1]! ∧ N e[0]! e[1]! = true) ∨
         (∃ i, i + 2 < e.length ∧ e[i]! ≠ e[i + 1]! ∧ e[i + 1]! ≠ e[i + 2]! ∧
           N e[i + 1]! e[i + 2]! = true))) := by
  cases e with
  | nil =>
    simp only [containsUnacceptableEdge, List.length_nil]
    simp
  | cons a t =>
    cases t with
    | nil =>
      simp only [containsUnacceptableEdge, List.length_cons, List.length_nil]
      simp
    | cons b u =>
      cases u with
      | nil =>
        -- e = [a, b]
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
        have hab : a < b ↔ a ≠ b := by
          have h0 : a ≤ b := by simpa using hmono 0 (by simp)
          simpa using ltIffNeOfLe' h0
        have hC : containsUnacceptableEdge N (a :: b :: []) = true ↔
            (a < b ∧ N a b = true) := by
          have hred : containsUnacceptableEdge N (a :: b :: []) =
              (if (a < b ∧ N a b = true) then true else false) := by
            rw [containsUnacceptableEdge, containsUnacceptableEdgeSnd]
          rw [hred]
          by_cases hP : (a < b ∧ N a b = true)
          · rw [if_pos hP]; simp [hP]
          · rw [if_neg hP]; simp [hP]
        have hR : (2 ≤ (a :: b :: ([] : List Nat)).length ∧
              (((a ≠ b ∧ N a b = true) ∨
                (∃ i, i + 2 < (a :: b :: ([] : List Nat)).length ∧
                  (a :: b :: ([] : List Nat))[i]! ≠ (a :: b :: ([] : List Nat))[i + 1]! ∧
                  (a :: b :: ([] : List Nat))[i + 1]! ≠ (a :: b :: ([] : List Nat))[i + 2]! ∧
                  N (a :: b :: ([] : List Nat))[i + 1]! (a :: b :: ([] : List Nat))[i + 2]! = true))))
            ↔ (a ≠ b ∧ N a b = true) := by
          have hno : ¬ (∃ i, i + 2 < (a :: b :: ([] : List Nat)).length) := by
            rintro ⟨i, hi⟩
            simp only [List.length_cons, List.length_nil] at hi
            omega
          constructor
          · rintro ⟨-, h | ⟨i, hi, -⟩⟩
            · exact h
            · exact absurd ⟨i, hi⟩ hno
          · rintro h
            exact ⟨by simp, Or.inl h⟩
        simp only [List.getElem!_cons_succ] at hR
        rw [hC, hR]
        constructor
        · rintro ⟨hlt, hN⟩
          exact ⟨hab.mp hlt, hN⟩
        · rintro ⟨hne, hN⟩
          exact ⟨hab.mpr hne, hN⟩
      | cons c u' =>
        -- e = a :: b :: c :: u'
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
        have hab : a < b ↔ a ≠ b := by
          have h0 : a ≤ b := by simpa using hmono 0 (by simp)
          simpa using ltIffNeOfLe' h0
        have hlen2 : 2 ≤ (a :: b :: c :: u').length := by
          simp only [List.length_cons]; omega
        have hlen2t : 2 ≤ (b :: c :: u').length := by
          simp only [List.length_cons]; omega
        have hmonoT : ∀ i, i + 1 < (b :: c :: u').length →
            (b :: c :: u')[i]! ≤ (b :: c :: u')[i + 1]! := by
          intro i hi
          have h1 : i + 1 + 1 < (a :: b :: c :: u').length := by
            simp only [List.length_cons] at hi ⊢; omega
          have h2 := hmono (i + 1) h1
          simpa only [List.getElem!_cons_succ] using h2
        have hvT : (b :: c :: u') = [] ∨
            (a < (b :: c :: u')[0]! ↔ a ≠ (b :: c :: u')[0]!) := Or.inr (by
          have h0 : a ≤ b := by simpa using hmono 0 (by simp)
          simpa only [List.getElem!_cons_zero] using ltIffNeOfLe' h0)
        have hA := containsUnacceptableEdgeSndExplicitAux (N := N) (b :: c :: u') a hmonoT hvT
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hA
        have hC : containsUnacceptableEdge N (a :: b :: c :: u') = true ↔
            (a < b ∧ N a b = true) ∨
              containsUnacceptableEdgeSnd N a (b :: c :: u') = true := by
          have hred : containsUnacceptableEdge N (a :: b :: c :: u') =
              (if (a < b ∧ N a b = true) then true
                else containsUnacceptableEdgeSnd N a (b :: c :: u')) := by
            rw [containsUnacceptableEdge]
          rw [hred]
          constructor
          · intro h
            by_cases hP : (a < b ∧ N a b = true)
            · exact Or.inl hP
            · right
              rwa [if_neg hP] at h
          · rintro (hP | h)
            · simp [if_pos hP]
            · by_cases hP : (a < b ∧ N a b = true)
              · simp [if_pos hP]
              · rw [if_neg hP]; exact h
        have hs := edgeShift (N := N) (a := a) (b := b) (c := c) (u' := u')
        simp only [List.getElem!_cons_succ] at hs
        rw [hC, hA, hs]
        constructor
        · rintro (⟨hlt, hN⟩ | ⟨-, (⟨hab', h1, hN⟩ | ⟨j, hj, h1, h2, hN⟩)⟩)
          · exact ⟨hlen2, Or.inl ⟨hab.mp hlt, hN⟩⟩
          · exact ⟨hlen2, Or.inr (Or.inl ⟨hab', h1, hN⟩)⟩
          · exact ⟨hlen2, Or.inr (Or.inr ⟨j, hj, h1, h2, hN⟩)⟩
        · rintro ⟨-, (⟨hne, hN⟩ | ⟨hab', h1, hN⟩ | ⟨j, hj, h1, h2, hN⟩)⟩
          · exact Or.inl ⟨hab.mpr hne, hN⟩
          · exact Or.inr ⟨hlen2t, Or.inl ⟨hab', h1, hN⟩⟩
          · exact Or.inr ⟨hlen2t, Or.inr ⟨j, hj, h1, h2, hN⟩⟩

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.containsUnacceptableEdgeExplicit
