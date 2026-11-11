/-
  Kepler.Text.Reduction5J5UvnsGetD — U1a：getD 层微件（U 段第一小波）。
  只含 5 条通用 getD 引理 + 探针；不碰 U1 主线（见 DELIVERY-nb56）。

  纪律：零公理、零占位证明；私有重落（不改既有文件）。
-/

import Kepler.Text.Reduction3Thm6D2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

/-- `getD` 沿 append 的拆分式。 -/
theorem uvnsGetDAppend (l m : List (Option ℕ)) (j : ℕ) :
    (l ++ m).getD j none =
      if h : j < l.length then l.getD j none else m.getD (j - l.length) none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rw [List.getD_eq_getElem?_getD]

/-- `nseq`（`replicate n none`）后接 `[some z]` 的逐位取值。 -/
theorem uvnsGetDRepZV (zv n t : ℕ) :
    (List.replicate n (none : Option ℕ) ++ [some zv]).getD t none =
      if t = n then some zv else none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split
  · rename_i h
    simp only [List.length_replicate] at h
    rw [List.getElem?_replicate, if_pos h, if_neg (by omega : t ≠ n)]
    rfl
  · rename_i h
    simp only [List.length_replicate] at h ⊢
    cases h' : t - n with
    | zero =>
      have htn : t = n := by omega
      rw [if_pos htn]
      simp
    | succ k =>
      have htn : t ≠ n := by omega
      rw [if_neg htn]
      simp

/-- `[some y] ++ nseq ++ [some z]` 的首位（`j ≥ 1` 归约到中段）。 -/
theorem uvnsGetDHeadRepCons (y z n j : ℕ) :
    ([some y] ++ List.replicate n (none : Option ℕ) ++ [some z]).getD j none =
      if j = 0 then some y
      else (List.replicate n (none : Option ℕ) ++ [some z]).getD (j - 1) none := by
  cases j with
  | zero => simp
  | succ k => simp

/-- `map some` 的逐位取值（界内）。 -/
theorem uvnsGetDMapSome {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    (l.map some).getD j none = some (l.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- `take 1` 的单元形（`Thm6D2:148` 同名件为 private，私有重落）。 -/
theorem uvnsGetDTakeOne {α : Type} (l : List α) (h : 0 < l.length) :
    l.take 1 = [l[0]'h] := by
  cases l with
  | nil => simp at h
  | cons a t => rfl

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.uvnsGetDAppend
#print axioms Kepler.Text.Reduction5.uvnsGetDRepZV
#print axioms Kepler.Text.Reduction5.uvnsGetDHeadRepCons
#print axioms Kepler.Text.Reduction5.uvnsGetDMapSome
#print axioms Kepler.Text.Reduction5.uvnsGetDTakeOne
