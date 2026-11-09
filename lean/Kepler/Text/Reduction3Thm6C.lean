/-
  Kepler.Text.Reduction3Thm6C — T6C 主体（foldl 族 + size 族，6/7 件）。

  ┌─ 件目（T6C 第一部分；size_vs 移至 T6D）──────────────────────
  │   dest_triple0_step_paired  :1583 → §A（rfl 级配对形重述）
  │   dest_triple0_foldl_steps  :1626(GSYM) → §B
  │   foldl_step_last_nonnil    :1650 → §C
  │   dest_triple0_cat2         :1971 → §D
  │   size_initial_seg          :1894 → §E1（indexf_eq_spine/T6B 桥）
  │   size_final_seg            :1913 → §E2
  │   size_dest_triple0_cons2   :2015 → §E3
  │ `size_vs`(:2055，~200 HOL 行)另立 T6D。
  │ **新机器报告**：`dest_triple0_step_paired` 为 foldl_steps 的账实前置
  │ （T5 未曾落），本文件就地落成 rfl 级（约 15 行），不构成新理论。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]`（rw 只首匹配）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm6B
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core indexf)
open Kepler.Text.Reduction4 (indexfRefl indexf_eq_zero indexf_add_left)

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

/-! ## §0 辅助（sizeBetwn 链口径包装；复用 indexf_eq_spine） -/

private theorem sizeBetwnChain {s : List ℕ} {x y : ℕ} (hnd : s.Nodup)
    (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (between s x y).length = indexf x y s - 1 := by
  rw [Kepler.Text.TameSpine.sizeBetwn hnd hx hy hne, indexf_eq_spine]

/-! ## §A `dest_triple0_step_paired`（reduction3.hl:1583）

`destTriple0Step` 的配对投影重述（无模式绑定）——foldl 族的账实前置，
HOL 证明只是 FORALL_PAIR + 定义展开，Lean 侧 rfl 级。 -/

/-- HOL `dest_triple0_step_paired`（reduction3.hl:1583）。 -/
theorem destTriple0StepPaired (f : List ℕ) (s : List (List (Option ℕ)))
    (u v n : ℕ) :
    destTriple0Step f s (u, v, n) =
      (let ns := List.replicate n (none : Option ℕ)
       if s.flatten = [] then [[some u] ++ ns ++ [some v]]
       else
         let u0 := ((s.getLastD []).getLastD none).getD 0
         let b := (between f u0 u).map some
         if u0 = u then s ++ [ns ++ [some v]]
         else if nextEl f u0 = u then s ++ [[some u] ++ ns ++ [some v]]
         else s ++ [b ++ [some u] ++ ns ++ [some v]]) := rfl

/-! ## §B `dest_triple0_foldl_steps`（reduction3.hl:1626，GSYM 方向）

`dest_triple0 f (flatten s) uvns = flatten (foldl (dest_triple0_step f) s uvns)`，
前提 `s ≠ [] → LAST s ≠ []`（段表非空时末段非空）。
归纳 + `destTriple0StepLastNonnil`（步进结果恒非空尾）+ `lastFlattenLast`
（flatten 末元 = 末段末元，对齐 u0 条件）。 -/

/-- HOL `dest_triple0_foldl_steps` 的 GSYM 形（reduction3.hl:1626）。 -/
theorem destTriple0FoldlSteps (uvns : List (ℕ × ℕ × ℕ)) :
    ∀ (f : List ℕ) (s : List (List (Option ℕ))),
      (s ≠ [] → s.getLastD [] ≠ []) →
      destTriple0 f s.flatten uvns
        = (List.foldl (destTriple0Step f) s uvns).flatten := by
  induction uvns with
  | nil =>
    intro f s _
    rw [destTriple0.eq_1]
    rfl
  | cons t ts ih =>
    obtain ⟨u, v, n⟩ := t
    intro f s hs
    rw [destTriple0_cons_eq]
    dsimp only
    -- RHS foldl 展开与 IH
    rw [List.foldl_cons]
    have hstep_ne : (destTriple0Step f s (u, v, n)) ≠ [] := by
      intro h
      have hz := destTriple0StepLastNonnil f s (u, v, n)
      rw [h] at hz
      exact hz rfl
    have hstep_last : (destTriple0Step f s (u, v, n)).getLastD [] ≠ [] :=
      destTriple0StepLastNonnil f s (u, v, n)
    have hIH := ih f (destTriple0Step f s (u, v, n))
      (fun _ => hstep_last)
    rw [← hIH]
    by_cases h0 : s.flatten = []
    · simp only [if_pos h0]
      -- step s 落在第一分支：[[some u] ++ ns ++ [some v]]
      have hstep : destTriple0Step f s (u, v, n)
          = [[some u] ++ List.replicate n (none : Option ℕ) ++ [some v]] := by
        simp only [destTriple0StepPaired]
        simp [h0]
      rw [hstep]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    · simp only [if_neg h0]
      -- flatten 非空 ⇒ 步进的 u0 与 LHS 的 u0 经 lastFlattenLast 对齐
      have hsne : s ≠ [] := by
        intro h
        apply h0
        rw [h]
        rfl
      have hslast : s.getLastD [] ≠ [] := hs hsne
      have hun : s.flatten.getLastD none = (s.getLastD []).getLastD none :=
        lastFlattenLast s hsne hslast
      -- LHS 的 u0 经 hun 改写为 step 的 u0
      rw [hun]
      by_cases h1 : ((s.getLastD []).getLastD none).getD 0 = u
      · simp only [if_pos h1]
        have hstep : destTriple0Step f s (u, v, n)
            = s ++ [List.replicate n (none : Option ℕ) ++ [some v]] := by
          simp only [destTriple0StepPaired, if_neg h0, if_pos h1]
        rw [hstep]
        simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
      · simp only [if_neg h1]
        by_cases h2 : nextEl f (((s.getLastD []).getLastD none).getD 0) = u
        · simp only [if_pos h2]
          have hstep : destTriple0Step f s (u, v, n)
              = s ++ [[some u] ++ List.replicate n (none : Option ℕ) ++ [some v]] := by
            simp only [destTriple0StepPaired]
            rw [if_neg h0]
            simp only [if_neg h1, if_pos h2]
          rw [hstep]
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.append_assoc]
        · simp only [if_neg h2]
          have hstep : destTriple0Step f s (u, v, n)
              = s ++ [(between f (((s.getLastD []).getLastD none).getD 0) u).map some
                  ++ [some u] ++ List.replicate n (none : Option ℕ) ++ [some v]] := by
            simp only [destTriple0StepPaired]
            rw [if_neg h0]
            simp only [if_neg h1, if_neg h2]
          rw [hstep]
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.append_assoc]

/-! ## §C `foldl_step_last_nonnil`（reduction3.hl:1650）

foldl 结果末段为空 ⇒ 输入段表为空（对段表归纳；剩余用例由
`destTriple0StepLastNonnil` 矛盾收口）。 -/

/-- HOL `foldl_step_last_nonnil`（reduction3.hl:1650）。 -/
theorem foldlStepLastNonnil :
    ∀ (a : List (ℕ × ℕ × ℕ)) (f : List ℕ) (s : List (List (Option ℕ))),
      (List.foldl (destTriple0Step f) s a).getLastD [] = [] → a = []
  | [], _, _ => by intro _; rfl
  | t :: ts, f, s => by
    intro h
    rw [List.foldl_cons] at h
    have hts : ts = [] := foldlStepLastNonnil ts f (destTriple0Step f s t) h
    subst hts
    rw [List.foldl_nil] at h
    exact absurd h (destTriple0StepLastNonnil f s t)

/-! ## §D `dest_triple0_cat2`（reduction3.hl:1971）

全程走 foldl：`foldl (a++b) = foldl (foldl a) b`（`List.foldl_append`）
+ 两侧 `destTriple0FoldlSteps` GSYM + `destTriple0Cat` 拆 `[some h]` 尾段。 -/

/-- HOL `dest_triple0_cat2`（reduction3.hl:1971）。 -/
theorem destTriple0Cat2 (f : List ℕ) (s : List (List (Option ℕ)))
    (a b : List (ℕ × ℕ × ℕ)) (a' : List (Option ℕ)) (h : ℕ)
    (hne : a ≠ []) (hs : s ≠ [] → s.getLastD [] ≠ [])
    (hsplit : destTriple0 f s.flatten a = a' ++ [some h]) :
    destTriple0 f s.flatten (a ++ b) = a' ++ destTriple0 f [some h] b := by
  have hfoldl_last : (List.foldl (destTriple0Step f) s a).getLastD [] ≠ [] := by
    intro hz
    exact hne (foldlStepLastNonnil a f s hz)
  have hfoldl_ne : (List.foldl (destTriple0Step f) s a) ≠ [] := by
    intro hz
    rw [hz] at hfoldl_last
    exact hfoldl_last rfl
  have hfl : (List.foldl (destTriple0Step f) s a).flatten = a' ++ [some h] := by
    rw [← destTriple0FoldlSteps a f s hs]
    exact hsplit
  rw [destTriple0FoldlSteps (a ++ b) f s hs, List.foldl_append,
    ← destTriple0FoldlSteps b f (List.foldl (destTriple0Step f) s a)
      (fun _ => hfoldl_last), hfl]
  exact destTriple0Cat b f a' [some h] (by simp)

/-! ## §E size 三件（indexf_eq_spine 桥就位后全装配） -/

/-- HOL `size_initial_seg`（reduction3.hl:1894）。 -/
theorem sizeInitialSeg (f : List ℕ) (u v : ℕ) (s : List (Option ℕ))
    (hv : v ∈ f) (hu : u ∈ f) (hnd : f.Nodup)
    (hs : s = if v = u then [] else some v :: (between f v u).map some) :
    s.length = indexf v u f := by
  subst hs
  by_cases h : v = u
  · rw [if_pos h, h, indexfRefl hu]
    rfl
  · rw [if_neg h, List.length_cons, List.length_map,
      sizeBetwnChain hnd hv hu h]
    have hne : indexf v u f ≠ 0 := fun hz => h (indexf_eq_zero hv hu hz)
    omega

/-- HOL `size_final_seg`（reduction3.hl:1913）。 -/
theorem sizeFinalSeg (f : List ℕ) (v' u0 : ℕ) (s : List (Option ℕ))
    (hv' : v' ∈ f) (hu0 : u0 ∈ f) (hnd : f.Nodup)
    (hs : s = if v' = u0 then []
          else (between f v' u0).map some ++ [some u0]) :
    s.length = indexf v' u0 f := by
  subst hs
  by_cases h : v' = u0
  · rw [if_pos h, h, indexfRefl hu0]
    rfl
  · rw [if_neg h, List.length_append, List.length_map, List.length_singleton,
      sizeBetwnChain hnd hv' hu0 h]
    have hne : indexf v' u0 f ≠ 0 := fun hz => h (indexf_eq_zero hv' hu0 hz)
    omega

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.destTriple0StepPaired
#print axioms Kepler.Text.Reduction3.destTriple0FoldlSteps
#print axioms Kepler.Text.Reduction3.foldlStepLastNonnil
#print axioms Kepler.Text.Reduction3.destTriple0Cat2
#print axioms Kepler.Text.Reduction3.sizeInitialSeg
#print axioms Kepler.Text.Reduction3.sizeFinalSeg
