/-
  Kepler.Text.Reduction1W1e — J4 Wave W1 批 5（**编排者按车道冻结包收口**，
  2026-11-10）：
  `el_showDups0`（`reduction1.hl:626-:648`）+ `el_enum_of_vertex_list`（`:649-:675`）。
  剩余 `dart_neighbors`/`duplicateEdge_next`（67+31 HOL）留批 5b——
  两件走图级 `neighbors`/`duplicateEdge` 定义展开 + `good_faces_v3`，与
  `el_*` 的 `showDups0` 归纳层不同机制。
  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
  DIFFERS：HOL `EL` ↦ `getElem!`（约定 C2）；`the (EL i vs)` ↦ `vs[i]!.getD 0`。
  雷区（车道 W1E 发现，编排者采纳）：**`cases hb : b`（带方程名）不自动替换
  上下文里的 `b`**——本件一律改用无方程名 `cases b`（替换自动发生）；
  `rw [showDups]` 无方程引理可用 ⇒ 走 rfl 式 cons 桥（`showDupsConsNone/Some`）
  + `simp only [enumOfVertexList]` 展开。
-/
import Kepler.Graphs.EnumeratorProps
import Kepler.Text.TameSpine.TameList4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Text.TameSpine (showDups0 showDups indexf enumOfVertexList)

/-- `showDups` 的 cons 展开（rfl 桥；`rw [showDups]` 无方程引理可用）。 -/
private theorem showDupsConsNone (bs : List (Option ℕ)) :
    showDups (none :: bs) = showDups0 0 (none :: bs) := rfl

/-- `showDups` 的 cons 展开（rfl 桥）。 -/
private theorem showDupsConsSome (c : ℕ) (bs : List (Option ℕ)) :
    showDups (some c :: bs) = showDups0 c (some c :: bs) := rfl

/-! ## §1 `el_showDups0`（reduction1.hl:626-648） -/

/-- **HOL `el_showDups0`**：
`j < sizel t ∧ isSome (EL j t) ⇒
EL j (MAP (λu. indexf v u f) (showDups0 (the h) t)) = indexf v (the (EL j t)) f`。
路线：`t` 归纳 + 无方程名 `cases b`（自动替换）+ `cases j`。 -/
theorem elShowDups0 : ∀ (t : List (Option ℕ)) (h v : ℕ) (f : List ℕ) (j : ℕ),
    j < t.length → (t[j]!).isSome →
      ((showDups0 h t).map (fun u => indexf v u f))[j]! = indexf v (t[j]!.getD 0) f := by
  intro t
  induction t with
  | nil => intro h v f j hj _; exact absurd hj (by simp)
  | cons b bs ih =>
    intro h v f j hj hs
    cases j with
    | zero =>
      rw [List.getElem!_cons_zero] at hs ⊢
      cases b with
      | none =>
        rw [showDups0, List.map_cons, List.getElem!_cons_zero]
        exact absurd hs (by simp)
      | some c =>
        rw [showDups0, List.map_cons, List.getElem!_cons_zero, Option.getD_some]
    | succ j' =>
      have hs' : (bs[j']!).isSome := by
        rw [← List.getElem!_cons_succ]; exact hs
      have hj' : j' < bs.length := by
        rw [List.length_cons] at hj; omega
      cases b with
      | none =>
        rw [showDups0, List.map_cons, List.getElem!_cons_succ,
          List.getElem!_cons_succ]
        exact ih h v f j' hj' hs'
      | some c =>
        rw [showDups0, List.map_cons, List.getElem!_cons_succ,
          List.getElem!_cons_succ]
        exact ih c v f j' hj' hs'

/-! ## §2 `el_enum_of_vertex_list`（reduction1.hl:649-675） -/

/-- **HOL `el_enum_of_vertex_list`**：
`i < sizel vs ∧ isSome (EL i vs) ⇒
EL i (enum_of_VertexList f v vs) = indexf v (the (EL i vs)) f`。
路线：`enumOfVertexList` def 展开（`simp only`）→ `showDups` cons rfl 桥 →
`showDups0` 方程 → 首元/后继分别与 §1 收口。 -/
theorem elEnumOfVertexList {vs : List (Option ℕ)} {v : ℕ} {f : List ℕ} {i : ℕ}
    (hi : i < vs.length) (hs : (vs[i]!).isSome) :
    (enumOfVertexList f v vs)[i]! = indexf v (vs[i]!.getD 0) f := by
  cases vs with
  | nil => exact absurd hi (by simp)
  | cons b bs =>
    cases i with
    | zero =>
      rw [List.getElem!_cons_zero] at hs ⊢
      cases b with
      | none =>
        simp only [enumOfVertexList]
        rw [showDupsConsNone, showDups0, List.map_cons, List.getElem!_cons_zero]
        rfl
      | some c =>
        simp only [enumOfVertexList]
        rw [showDupsConsSome c bs, showDups0, List.map_cons, List.getElem!_cons_zero,
          Option.getD_some]
    | succ i' =>
      have hs' : (bs[i']!).isSome := by
        rw [← List.getElem!_cons_succ]; exact hs
      have hi' : i' < bs.length := by
        rw [List.length_cons] at hi; omega
      cases b with
      | none =>
        simp only [enumOfVertexList]
        rw [showDupsConsNone, showDups0, List.map_cons, List.getElem!_cons_succ,
          List.getElem!_cons_succ]
        exact elShowDups0 bs 0 v f i' hi' hs'
      | some c =>
        simp only [enumOfVertexList]
        rw [showDupsConsSome c bs, showDups0, List.map_cons, List.getElem!_cons_succ,
          List.getElem!_cons_succ]
        exact elShowDups0 bs c v f i' hi' hs'

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三、零未证公理） -/
#print axioms Kepler.Text.Reduction1.elShowDups0
#print axioms Kepler.Text.Reduction1.elEnumOfVertexList
