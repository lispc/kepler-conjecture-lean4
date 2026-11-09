/-
  Kepler.Text.Reduction3Thm6D — T6D 批（T6 板最后两件）。

  ┌─ 件目（逐件对账）─────────────────────────────────────────────
  │   size_dest_triple0_cons2  reduction3.hl:2015 → §B sizeDestTriple0Cons2
  │   size_vs                  reduction3.hl:2055 → 另立 Reduction3Thm6D2.lean
  │ （两件合计预估超 450 行，按工单拆两文件；D2 import 本文件。）
  │ HOL 路线：cons2 = dest_triple0 展开 + dest_triple0_cat + 三分支
  │ indexf 算术（indexf_refl / next_el_indexf / size_betwn + indexf0）。
  │ 链侧落法：`rw [destTriple0Cat]` 把新增末段拆出，长度三分支后 omega。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]` / `rw [if_pos/if_neg]`；
  │ indexf 全用 Reduction5.indexf（Spine 桥走 indexf_eq_spine）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm6C
import Kepler.Text.TameSpine.TameList3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core indexf)
open Kepler.Text.Reduction4 (indexfRefl indexf_eq_zero indexf_lt_length_of_mem)

/-! ## §0 私有辅助（T6/T6B/T6C 同体私件复制；private 不跨文件可见） -/

/-- `destTriple0` 的 cons 展开方程（rfl 级；T6/T6C 同体）。 -/
private theorem destTriple0_cons_eq (f : List ℕ) (s : List (Option ℕ)) (u v n : ℕ)
    (ts : List (ℕ × ℕ × ℕ)) :
    destTriple0 f s ((u, v, n) :: ts) =
      (let ns := List.replicate n (none : Option ℕ)
       if s = [] then destTriple0 f ([some u] ++ ns ++ [some v]) ts
       else
         let u0 := (s.getLastD none).getD 0
         if u0 = u then destTriple0 f (s ++ ns ++ [some v]) ts
         else if nextEl f u0 = u then
           destTriple0 f (s ++ [some u] ++ ns ++ [some v]) ts
         else
           destTriple0 f (s ++ (between f u0 u).map some ++ [some u] ++ ns
             ++ [some v]) ts) := rfl

private theorem getLastD_append_of_ne {α : Type} (d : α) (a : List α) {b : List α}
    (h : b ≠ []) : (a ++ b).getLastD d = b.getLastD d := by
  induction a generalizing d with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    cases b with
    | nil => exact (h rfl).elim
    | cons y ys => rw [List.getLastD_cons, List.getLastD_cons]

/-- `size_betwn` 链口径（T6C 同名件为 private，此处现推 2 行）。 -/
private theorem sizeBetwnChain {s : List ℕ} {x y : ℕ} (hnd : s.Nodup)
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = indexf x y s - 1 := by
  rw [Kepler.Text.TameSpine.sizeBetwn hnd hx hy hne, indexf_eq_spine]

/-- `destTriple0` 在非空 sofar 上恒返回非空表。 -/
private theorem destTriple0NeNil (f : List ℕ) (uvns : List (ℕ × ℕ × ℕ))
    (sofar : List (Option ℕ)) (h : sofar ≠ []) :
    destTriple0 f sofar uvns ≠ [] := by
  induction uvns generalizing sofar with
  | nil =>
    rw [destTriple0Nil]
    exact h
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    rw [destTriple0_cons_eq]
    dsimp only
    rw [if_neg h]
    by_cases h1 : (sofar.getLastD none).getD 0 = u
    · rw [if_pos h1]
      exact ih _ (by simp)
    · rw [if_neg h1]
      by_cases h2 : nextEl f ((sofar.getLastD none).getD 0) = u
      · rw [if_pos h2]
        exact ih _ (by simp)
      · rw [if_neg h2]
        exact ih _ (by simp)

/-- cons2 形末元：`destTriple0 f [some w] ((u,v,n)::uvns)` 的末元 =
`destTriple0 f [some v] uvns` 的末元（首步追加 `[some v]` + `destTriple0Cat`）。 -/
private theorem destTriple0LastOfCons (f : List ℕ) (u v w n : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) :
    (destTriple0 f [some w] ((u, v, n) :: uvns)).getLastD none
      = (destTriple0 f [some v] uvns).getLastD none := by
  rw [destTriple0_cons_eq]
  dsimp only
  rw [if_neg (by simp : ([some w] : List (Option ℕ)) ≠ [])]
  rw [show (([some w] : List (Option ℕ)).getLastD none).getD 0 = w from rfl]
  have hcat : ∀ s : List (Option ℕ), s ≠ [] →
      (destTriple0 f (s ++ [some v]) uvns).getLastD none
        = (destTriple0 f [some v] uvns).getLastD none := by
    intro s hs
    rw [destTriple0Cat uvns f s [some v] (by simp)]
    exact getLastD_append_of_ne none s
      (destTriple0NeNil f uvns [some v] (by simp))
  by_cases h1 : w = u
  · rw [if_pos h1]
    exact hcat _ (by simp)
  · rw [if_neg h1]
    by_cases h2 : nextEl f w = u
    · rw [if_pos h2]
      exact hcat _ (by simp)
    · rw [if_neg h2]
      exact hcat _ (by simp)

/-- `getLastD none = some a` 反推有序末元。 -/
private theorem getLast_eq_of_getLastD {β : Type} {l : List (Option β)} {a : β}
    (hne : l ≠ []) (h : l.getLastD none = some a) : l.getLast hne = some a := by
  have h2 : l.getLast? = some (some a) := by
    rw [List.getLastD_eq_getLast?] at h
    cases hl : l.getLast? with
    | none =>
      rw [hl] at h
      exact absurd h (by simp)
    | some z =>
      rw [hl] at h
      have hz : z = some a := by simpa using h
      rw [hz]
  rw [List.getLast?_eq_some_getLast hne] at h2
  exact Option.some.inj h2

/-- 末元已知时 `l = l.dropLast ++ [末元]`（`dropLast_concat_getLast` 转写）。 -/
private theorem eq_dropLast_append_of_getLastD {β : Type} {l : List (Option β)} {a : β}
    (hne : l ≠ []) (h : l.getLastD none = some a) :
    l = l.dropLast ++ [some a] := by
  conv_lhs => rw [← List.dropLast_concat_getLast hne]
  rw [getLast_eq_of_getLastD hne h]

/-! ## §B `size_dest_triple0_cons2`（reduction3.hl:2015）

`dest_triple0` 在 `sofar = [SOME w]` 上走一步的长度账：三分支分别以
`indexf_refl`（`w = u`）、`next_el_indexf`（`next_el f w = u`）、
`size_betwn + indexf0`（一般支）收口。 -/

/-- HOL `size_dest_triple0_cons2`（reduction3.hl:2015）。 -/
theorem sizeDestTriple0Cons2 (f : List ℕ) (u v w n : ℕ)
    (uvns : List (ℕ × ℕ × ℕ)) (hnd : f.Nodup) (hlt : 1 < f.length)
    (hu : u ∈ f) (hv : v ∈ f) (hw : w ∈ f) :
    (destTriple0 f [some w] ((u, v, n) :: uvns)).length
      = n + 1 + indexf w u f + (destTriple0 f [some v] uvns).length := by
  have hcat : ∀ s : List (Option ℕ), s ≠ [] →
      (destTriple0 f (s ++ [some v]) uvns).length
        = s.length + (destTriple0 f [some v] uvns).length := by
    intro s hs
    rw [destTriple0Cat uvns f s [some v] (by simp), List.length_append]
  rw [destTriple0_cons_eq]
  dsimp only
  rw [if_neg (by simp : ([some w] : List (Option ℕ)) ≠ [])]
  rw [show (([some w] : List (Option ℕ)).getLastD none).getD 0 = w from rfl]
  by_cases h1 : w = u
  · rw [if_pos h1]
    subst h1
    rw [hcat _ (by simp), indexfRefl hu]
    simp only [List.length_append, List.length_cons, List.length_replicate,
      List.length_nil]
    omega
  · rw [if_neg h1]
    by_cases h2 : nextEl f w = u
    · rw [if_pos h2]
      rw [hcat _ (by simp)]
      have hidx : indexf w u f = 1 := by
        rw [indexf_eq_spine]
        exact Kepler.Text.TameSpine.nextElIndexf hw hu hnd h2 hlt
      rw [hidx]
      simp only [List.length_append, List.length_cons, List.length_replicate,
        List.length_nil]
      omega
    · rw [if_neg h2]
      have hwne : w ≠ u := h1
      rw [hcat _ (by simp)]
      have hbet : (between f w u).length = indexf w u f - 1 :=
        sizeBetwnChain hnd hw hu hwne
      have hpos : 0 < indexf w u f :=
        Nat.pos_of_ne_zero (fun hz => hwne (indexf_eq_zero hw hu hz))
      simp only [List.length_append, List.length_cons, List.length_replicate,
        List.length_map, List.length_nil]
      omega

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.sizeDestTriple0Cons2
