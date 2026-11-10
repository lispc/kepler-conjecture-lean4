/-
  Kepler.Text.Reduction1W1k — J4 Wave W1 批 6 §1（编排者按车道冻结包
  `DELIVERY_W1K_S1_FROZEN.md` 收口，2026-11-10）：
  `containsUnacceptableEdgeSnd_explicit`（HOL `reduction1.hl:318-:400`，83 HOL）。

  车道冻结包的核心设计（采信）：Snd 的 `else` 支把起点改为次元 ⇒ 归纳必须对
  **任意起点 `v`**；而「`v < e[0]! ↔ v ≠ e[0]!`」槽在递归后由**单调性**供给
  （`ltIffNeOfLe : a ≤ b ⇒ a < b ↔ a ≠ b`）。故先证带泛化起点的
  `containsUnacceptableEdgeSndExplicitAux`，§1 本体由 `hhd` 直给该槽。

  DIFFERS：`EL` ↦ `getElem!`（C2）；`sizel` ↦ `List.length`；
  `N x y`（Bool 当 Prop）↦ `N x y = true`。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Graphs.Plane

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Graphs (containsUnacceptableEdgeSnd)

/-- `a ≤ b ⇒ a < b ↔ a ≠ b`（单调性把 `<` 槽转成 `≠` 槽）。 -/
private theorem ltIffNeOfLe {a b : Nat} (h : a ≤ b) : a < b ↔ a ≠ b := by
  constructor <;> intro h' <;> omega

/-- 尾表平移：`(a::b::c::u')` 上的 ∃ 支 ⟺ 首三元组支 ∨ `(b::c::u')` 上的 ∃ 支。 -/
private theorem sndShift {N : Nat → Nat → Bool} {a b c : Nat} {u' : List Nat} :
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

/-- **HOL `containsUnacceptableEdgeSnd_explicit` 的泛化起点形**（车道冻结包 §1
陈述逐字）：`e = [] ∨ v < e[0]! ↔ v ≠ e[0]!` 槽供递归后由单调性再供给。 -/
theorem containsUnacceptableEdgeSndExplicitAux {N : Nat → Nat → Bool} :
    ∀ (e : List Nat) (v : Nat),
      (∀ i, i + 1 < e.length → e[i]! ≤ e[i + 1]!) →
      (e = [] ∨ (v < e[0]! ↔ v ≠ e[0]!)) →
      (containsUnacceptableEdgeSnd N v e = true ↔
        2 ≤ e.length ∧
          ((v ≠ e[0]! ∧ e[0]! ≠ e[1]! ∧ N e[0]! e[1]! = true) ∨
           (∃ i, i + 2 < e.length ∧ e[i]! ≠ e[i + 1]! ∧ e[i + 1]! ≠ e[i + 2]! ∧
             N e[i + 1]! e[i + 2]! = true))) := by
  intro e
  induction e with
  | nil =>
    intro v hmono hv
    simp only [containsUnacceptableEdgeSnd, List.length_nil]
    simp
  | cons a t ih =>
    intro v hmono hv
    cases t with
    | nil =>
      simp only [containsUnacceptableEdgeSnd, List.length_cons, List.length_nil]
      simp
    | cons b u =>
      cases u with
      | nil =>
        -- e = [a, b]
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
        have hv' : v < a ↔ v ≠ a := by
          have hne : (a :: b :: ([] : List Nat)) ≠ [] := by simp
          exact hv.resolve_left hne
        have hab : a < b ↔ a ≠ b := by
          have h0 : a ≤ b := by simpa using hmono 0 (by simp)
          simpa using ltIffNeOfLe h0
        have hC : containsUnacceptableEdgeSnd N v (a :: b :: []) = true ↔
            (v < a ∧ a < b ∧ N a b = true) := by
          have hred : containsUnacceptableEdgeSnd N v (a :: b :: []) =
              (if (v < a ∧ a < b ∧ N a b = true) then true else false) := by
            rw [containsUnacceptableEdgeSnd, containsUnacceptableEdgeSnd]
          rw [hred]
          by_cases hP : (v < a ∧ a < b ∧ N a b = true)
          · rw [if_pos hP]; simp [hP]
          · rw [if_neg hP]; simp [hP]
        have hR : (2 ≤ (a :: b :: ([] : List Nat)).length ∧
              (((v ≠ a ∧ a ≠ b ∧ N a b = true) ∨
                (∃ i, i + 2 < (a :: b :: ([] : List Nat)).length ∧
                  (a :: b :: ([] : List Nat))[i]! ≠ (a :: b :: ([] : List Nat))[i + 1]! ∧
                  (a :: b :: ([] : List Nat))[i + 1]! ≠ (a :: b :: ([] : List Nat))[i + 2]! ∧
                  N (a :: b :: ([] : List Nat))[i + 1]! (a :: b :: ([] : List Nat))[i + 2]! = true))))
            ↔ (v ≠ a ∧ a ≠ b ∧ N a b = true) := by
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
        · rintro ⟨hva, hab', hN⟩
          exact ⟨hv'.mp hva, hab.mp hab', hN⟩
        · rintro ⟨hva, hab', hN⟩
          exact ⟨hv'.mpr hva, hab.mpr hab', hN⟩
      | cons c u' =>
        -- e = a :: b :: c :: u'
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
        have hv' : v < a ↔ v ≠ a := hv.resolve_left (by simp)
        have hab : a < b ↔ a ≠ b := by
          have h0 : a ≤ b := by simpa using hmono 0 (by simp)
          simpa using ltIffNeOfLe h0
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
          simpa only [List.getElem!_cons_zero] using ltIffNeOfLe h0)
        have hC : containsUnacceptableEdgeSnd N v (a :: b :: c :: u') = true ↔
            (v < a ∧ a < b ∧ N a b = true) ∨
              containsUnacceptableEdgeSnd N a (b :: c :: u') = true := by
          have hred : containsUnacceptableEdgeSnd N v (a :: b :: c :: u') =
              (if (v < a ∧ a < b ∧ N a b = true) then true
                else containsUnacceptableEdgeSnd N a (b :: c :: u')) := by
            rw [containsUnacceptableEdgeSnd]
          rw [hred]
          constructor
          · intro h
            by_cases hP : (v < a ∧ a < b ∧ N a b = true)
            · exact Or.inl hP
            · right
              rwa [if_neg hP] at h
          · rintro (hP | h)
            · simp [if_pos hP]
            · by_cases hP : (v < a ∧ a < b ∧ N a b = true)
              · simp [if_pos hP]
              · rw [if_neg hP]; exact h
        have hi' := ih a hmonoT hvT
        simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hi'
        have hs := sndShift (N := N) (a := a) (b := b) (c := c) (u' := u')
        simp only [List.getElem!_cons_succ] at hs
        rw [hC, hi', hs]
        constructor
        · rintro (⟨hva, hab', hN⟩ | ⟨-, (⟨hab', h1, hN⟩ | ⟨j, hj, h1, h2, hN⟩)⟩)
          · exact ⟨hlen2, Or.inl ⟨hv'.mp hva, hab.mp hab', hN⟩⟩
          · exact ⟨hlen2, Or.inr (Or.inl ⟨hab', h1, hN⟩)⟩
          · exact ⟨hlen2, Or.inr (Or.inr ⟨j, hj, h1, h2, hN⟩)⟩
        · rintro ⟨-, (⟨hva, hab', hN⟩ | ⟨hab', h1, hN⟩ | ⟨j, hj, h1, h2, hN⟩)⟩
          · exact Or.inl ⟨hv'.mpr hva, hab.mpr hab', hN⟩
          · exact Or.inr ⟨hlen2t, Or.inl ⟨hab', h1, hN⟩⟩
          · exact Or.inr ⟨hlen2t, Or.inr ⟨j, hj, h1, h2, hN⟩⟩

/-- **HOL `containsUnacceptableEdgeSnd_explicit`**（`reduction1.hl:318-:400`）：
单调性 + `v < HD e ↔ v ≠ HD e` ⇒ Snd 判据的显式形。 -/
theorem containsUnacceptableEdgeSndExplicit {N : Nat → Nat → Bool} {e : List Nat} {v : Nat}
    (hmono : ∀ i, i + 1 < e.length → e[i]! ≤ e[i + 1]!)
    (hhd : e ≠ [] → (v < e.head! ↔ v ≠ e.head!)) :
    (containsUnacceptableEdgeSnd N v e = true ↔
      2 ≤ e.length ∧
        ((v ≠ e.head! ∧ e.head! ≠ e[1]! ∧ N e.head! e[1]! = true) ∨
         (∃ i, i + 2 < e.length ∧ e[i]! ≠ e[i + 1]! ∧
               e[i + 1]! ≠ e[i + 2]! ∧ N e[i + 1]! e[i + 2]! = true))) := by
  by_cases he : e = []
  · subst he
    simp only [containsUnacceptableEdgeSnd, List.length_nil]
    simp
  · have hv : e = [] ∨ (v < e[0]! ↔ v ≠ e[0]!) := Or.inr (by
      have h := hhd he
      rwa [List.head!_eq_getElem!] at h)
    have h0 := containsUnacceptableEdgeSndExplicitAux (N := N) e v hmono hv
    rwa [List.head!_eq_getElem!]

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.containsUnacceptableEdgeSndExplicit
