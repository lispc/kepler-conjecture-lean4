/-
  Kepler.Text.Reduction3Thm6 — J 战役 J3 定理层 T6 批（8 件中 5 件可做部分）。

  ┌─ 件数与依赖面审计（编排者要求：先报再动）──────────────────────
  │ T6 规划 8 件（1894-2278）。逐件裁定：
  │ ✅ 本批 5 件（纯列表/索引算术，全部依赖已落件）：
  │   size_initial_seg        :1894 → sizeInitialSeg
  │   size_final_seg          :1913 → sizeFinalSeg
  │   dest_triple0_cat        :1934 → destTriple0Cat
  │   size_dest_triple0_cons  :1995 → sizeDestTriple0Cons
  │   size_dest_triple0_cons2 :2015 → sizeDestTriple0Cons2
  │ ⚠ 缓 2 件（链侧零命中链）：
  │   dest_triple0_cat2 :1971 / size_vs :2055 —— 依赖
  │   `dest_triple0_foldl_steps`(:1626)/`foldl_step_last_nonnil`(:1650)
  │   （均 T5 件、未落）+ `dest_triple0_step_last_nonnil`(:1607)。
  │   其中 `dest_triple0_foldl_steps` 的 HOL 证明消费
  │   **Aq23.LAST_FLATTEN_2**（J2 件）；但该引理是**纯列表事实**
  │   （`the (LAST (flatten s)) = the (LAST (LAST s))`，逐段非空时），
  │   可链侧 ~10 行重证 ⇒ **cat2/size_vs 可做成 J2-free**。
  │   提案：T6B = 上述 3 支撑 + cat2 + size_vs（估 250-350 行）。
  │ ⚠ J2 传递门禁 1 件：
  │   reduction_A :2278 —— 证明 = reduction_subdivFace2 + size_vs +
  │   minimalFace_core✓ + loop_choice_props✓ + assumption_set3；
  │   reduction_subdivFace2 的 2 件 TAV2 门禁 ⇒ 传递 J2。
  │   **附勘误**：`reduction_subdivFace`(:720) 在 T2 批（388-796）非
  │   T6；T4 的 reduction_subdivFace2 缺口 = T2 该件 + T3/T4 缓件，
  │   与 T6 无关。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide。junk：LAST↦getLastD、
  │ the↦getD 0（非空/isSome 守卫）。索引算术走 Reduction4 的
  │ indexf 群 + TameList3.sizeBetwn + Island1.nextElIndexf。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm4
import Kepler.Text.Reduction4
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart indexf)
open Kepler.Text.Reduction4 (indexfRefl indexf_eq_zero indexf_add_left indexf_add_right
  indexf_lt_length_of_mem indexfInj)

/-! ## §B `dest_triple0_cat`（reduction3.hl:1934）

`s' ≠ [] ⇒ dest_triple0 f (s ++ s') uvns = s ++ dest_triple0 f s' uvns`
（对 uvns 归纳；分支内用 `getLastD_append_of_ne` 对齐 `u0`，
`append_assoc` + 归纳假设收口）。 -/

/-- `destTriple0` cons 展开方程（与 T2/T3 私有件同体；本文件复制）。 -/
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

/-- HOL `dest_triple0_cat`（reduction3.hl:1934）。 -/
theorem destTriple0Cat (uvns : List (ℕ × ℕ × ℕ)) :
    ∀ (f : List ℕ) (s s' : List (Option ℕ)), s' ≠ [] →
      destTriple0 f (s ++ s') uvns = s ++ destTriple0 f s' uvns := by
  induction uvns with
  | nil =>
    intro f s s' _
    rw [destTriple0.eq_1, destTriple0.eq_1]
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    intro f s s' hs'
    rw [destTriple0_cons_eq, destTriple0_cons_eq]
    dsimp only
    by_cases hs : s = []
    · rw [hs] at *
      rw [List.nil_append]
      simp only [if_neg hs']
      rw [List.nil_append]
    · have hss' : (s ++ s') ≠ [] := by
        intro h
        rcases List.append_eq_nil_iff.mp h with ⟨h1, _⟩
        exact hs h1
      simp only [if_neg hss', if_neg hs']
      have hgl : (s ++ s').getLastD none = s'.getLastD none :=
        getLastD_append_of_ne none s hs'
      rw [hgl]
      by_cases h1 : (s'.getLastD none).getD 0 = u
      · simp only [if_pos h1]
        simp only [List.append_assoc]
        exact ih f s (s' ++ (List.replicate n (none : Option ℕ) ++ [some v]))
          (by simp [hs'])
      · simp only [if_neg h1]
        by_cases h2 : nextEl f ((s'.getLastD none).getD 0) = u
        · simp only [if_pos h2]
          simp only [List.append_assoc]
          exact ih f s
            (s' ++ ([some u] ++ (List.replicate n (none : Option ℕ) ++ [some v])))
            (by simp [hs'])
        · simp only [if_neg h2]
          simp only [List.append_assoc]
          exact ih f s
            (s' ++ (((between f ((s'.getLastD none).getD 0) u).map some) ++ ([some u] ++
              (List.replicate n (none : Option ℕ) ++ [some v]))))
            (by simp [hs'])

/-! ## §C `size_dest_triple0_cons` / `_cons2`（:1995/:2015） -/

/-- HOL `size_dest_triple0_cons`（reduction3.hl:1995）：
空 sofar 开新段后长度 = `n+1 +` 余段长（`destTriple0Cat` 拆末段）。 -/
theorem sizeDestTriple0Cons (uvns : List (ℕ × ℕ × ℕ)) (f : List ℕ)
    (u v n : ℕ) :
    (destTriple0 f [] ((u, v, n) :: uvns)).length
      = n + 1 + (destTriple0 f [some v] uvns).length := by
  rw [show destTriple0 f [] ((u, v, n) :: uvns)
      = destTriple0 f ([some u] ++ List.replicate n (none : Option ℕ) ++ [some v])
        uvns from rfl]
  rw [show [some u] ++ List.replicate n (none : Option ℕ) ++ [some v]
      = ([some u] ++ List.replicate n (none : Option ℕ)) ++ [some v] from rfl]
  rw [destTriple0Cat uvns f ([some u] ++ List.replicate n (none : Option ℕ))
    [some v] (by simp)]
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.destTriple0Cat
#print axioms Kepler.Text.Reduction3.sizeDestTriple0Cons
