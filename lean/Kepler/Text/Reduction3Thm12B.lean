/-
  Kepler.Text.Reduction3Thm12B — T12b 单件：`prebatch_suc_explicit`（reduction3.hl:5064）。

  ┌─ 前置核查（本轮 #check 机器证据在文件尾）──────────────────────
  │ 依赖已全部就位：`t12_prebatch_suc`(:4927) / `t12_prebatch1`(:5037) /
  │ `t12_destTriple0StepRconsPaired`(:4985) / `t12_destTriple0RconsPaired`(:4953)
  │ / `prebatchZero`(D1) / `kepler.Text.TameSpine.betwnNil`（TameList53:175，
  │ HOL `betwn_nil`）。
  └────────────────────────────────────────────────────────────────

  ┌─ 随手复核：nfgtrans_suc(:4735) 现状（本轮不动它）────────────────
  │ T11 已落 `nfgtrans1`/`nfgtransAdd`（驼峰，Reduction3Thm11）✓；
  │ `Kbwpbhq.transform_count_not`（KBWPBHQ.hl:85）内容 =
  │ `j < transform_count → ¬final_list (rtrans j)`，树内即
  │ `Kepler.Text.Reduction4.transformCount_not`（#check 见文件尾）✓。
  │ **结论：仍 BLOCKED，但新的唯一硬门禁是 `Reduction3.AQIUNPP`**
  │ （reduction3.hl 本地件：`good_list L ∧ good_list_nodes L ∧
  │ marked_list L N r x → marked_list L (ntrans i) (rtrans i) x`；
  │ HOL 证体 = `Tame_list.AQIUNPP3` + **`Reduction2.transform_assumption_v2_lemma`**，
  │ 即 J2/TAV2 塔——树内未落且非本层可绕）。附带一处本树适配差：
  │ `nfgtransAdd` 多一个 `hfinal : finalList L (rtrans … (transformCount …))`
  │ 槽（T11 适配），消费时需另行供给。二者都超出 T12b 范围。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释正文禁字面「减斜杠」；
  │ if 重写一律 `simp only [if_pos/if_neg]`（rw 只首匹配）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm12
import Kepler.Text.Reduction3Thm11
import Kepler.Text.TameSpine.TameList53

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (GoodList listPairs nextEl findFaceDarts)
open Kepler.Graphs (between fgraph)
open Kepler.Text.Reduction5 (Dart core finalList transformCount ytrans ztrans)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-! ## §0 辅助 -/

/-- 段表末段非空 ⇒ `flatten` 非空。 -/
private theorem t12b_flatten_ne_nil {l : List (List (Option ℕ))}
    (h : l.getLastD [] ≠ []) : l.flatten ≠ [] := by
  intro hf
  cases l with
  | nil => exact h (by rfl)
  | cons a t =>
    have hne : (a :: t) ≠ [] := List.cons_ne_nil _ _
    have hmem : (a :: t).getLastD [] ∈ (a :: t) := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
      simp only [Option.getD_some]
      exact List.getLast_mem hne
    exact h (List.flatten_eq_nil_iff.mp hf _ hmem)

/-- `destTriple0Step` 结果的末元素 = 三元组的第三分量（`some v`）。 -/
private theorem t12b_step_last_succ (f : List ℕ) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (hg : GoodList L)
    (hgn : GoodListNodesTl L hg) (hir : (hypermapOfList L hg).IsRestricted)
    (hm : markedList L hg N r x) (hnf : ¬ finalList L r) (i : ℕ)
    (hi : i < transformCount L N r x) :
    ((prebatch f L N r x (i + 1)).getLastD []).getLastD none
      = some (ztrans L N r x i).1 := by
  rw [t12_prebatch_suc f L N r x i hg hgn hir hm hnf hi]
  unfold destTriple0Step
  dsimp only
  by_cases h0 : (prebatch f L N r x i).flatten = []
  · rw [if_pos h0]
    simp only [List.getLastD_cons, List.getLastD_nil]
    rw [List.getLastD_concat]
  · rw [if_neg h0]
    by_cases h1 : (((prebatch f L N r x i).getLastD []).getLastD none).getD 0
        = (ytrans L N r x i).1
    · rw [if_pos h1]
      rw [List.getLastD_concat, List.getLastD_concat]
    · rw [if_neg h1]
      by_cases h2 : nextEl f ((((prebatch f L N r x i).getLastD []).getLastD none).getD 0)
          = (ytrans L N r x i).1
      · rw [if_pos h2]
        rw [List.getLastD_concat, List.getLastD_concat]
      · rw [if_neg h2]
        rw [List.getLastD_concat, List.getLastD_concat]

/-- `prebatch i`（`0 < i`）的末元素 = `some (ztrans (i-1)).1`。 -/
private theorem t12b_prebatch_last (f : List ℕ) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (hg : GoodList L)
    (hgn : GoodListNodesTl L hg) (hir : (hypermapOfList L hg).IsRestricted)
    (hm : markedList L hg N r x) (hnf : ¬ finalList L r) (i : ℕ)
    (hpos : 0 < i) (hlt : i < transformCount L N r x) :
    ((prebatch f L N r x i).getLastD []).getLastD none
      = some (ztrans L N r x (i - 1)).1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hjlt : j < transformCount L N r x := by omega
  simpa using t12b_step_last_succ f L N r x hg hgn hir hm hnf j hjlt

/-! ## §A `prebatch_suc_explicit`（reduction3.hl:5064） -/

/-- HOL `prebatch_suc_explicit`（reduction3.hl:5064）：
`0 < i ∧ i < transform_count` 下，`prebatch (SUC i)` 的显式弧段拼接形。
`cat/a ++ b` 折算按 Lean 左结合；`PRE i ↦ i - 1`；`nseq ↦ replicate`。 -/
theorem t12_prebatch_suc_explicit (i : ℕ) (f : List ℕ) (L : fgraph ℕ)
    (N : List (List Dart)) (r : List Dart) (x : Dart) (hg : GoodList L)
    (hgn : GoodListNodesTl L hg) (hir : (hypermapOfList L hg).IsRestricted)
    (hm : markedList L hg N r x) (hnf : ¬ finalList L r)
    (huniq : f.Nodup)
    (hy : ∀ j, j < transformCount L N r x → (ytrans L N r x j).1 ∈ f)
    (hz : ∀ j, j < transformCount L N r x → (ztrans L N r x j).1 ∈ f)
    (hpos : 0 < i) (hlt : i < transformCount L N r x) :
    prebatch f L N r x (i + 1) =
      prebatch f L N r x i ++
        [ (if (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1 then []
           else (between f (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1).map some
             ++ [some (ytrans L N r x i).1])
          ++ List.replicate (between (findFaceDarts L x) (ytrans L N r x i)
              (ztrans L N r x i)).length (none : Option ℕ)
          ++ [some (ztrans L N r x i).1] ] := by
  -- 先展开 LHS：prebatch (i+1) = step (prebatch i) triple_i
  have hi1 : i - 1 < transformCount L N r x := by omega
  have hflat : (prebatch f L N r x i).flatten ≠ [] := by
    apply t12b_flatten_ne_nil
    intro hnil
    have hlast := t12b_prebatch_last f L N r x hg hgn hir hm hnf i hpos hlt
    rw [hnil] at hlast
    simp at hlast
  rw [t12_prebatch_suc f L N r x i hg hgn hir hm hnf hlt]
  rw [t12_destTriple0StepRconsPaired f (prebatch f L N r x i)
    ((ytrans L N r x i).1, (ztrans L N r x i).1,
     (between (findFaceDarts L x) (ytrans L N r x i)
       (ztrans L N r x i)).length) (fun h => absurd h hflat)]
  rw [List.append_cancel_left_eq, List.singleton_inj]
  -- 展开 destTriple0Rcons（s = prebatch i），用末元素恒等式收口
  have hu0 : (((prebatch f L N r x i).getLastD []).getLastD none).getD 0
      = (ztrans L N r x (i - 1)).1 := by
    rw [t12b_prebatch_last f L N r x hg hgn hir hm hnf i hpos hlt]
    rfl
  unfold destTriple0Rcons
  dsimp only
  rw [if_neg hflat, hu0]
  by_cases hcond : (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
  · simp only [if_pos hcond]
    rfl
  · simp only [if_neg hcond]
    by_cases hnext : nextEl f (ztrans L N r x (i - 1)).1 = (ytrans L N r x i).1
    · simp only [if_pos hnext]
      have hne : (ztrans L N r x (i - 1)).1 ≠ (ytrans L N r x i).1 := hcond
      have hu0mem : (ztrans L N r x (i - 1)).1 ∈ f := hz (i - 1) hi1
      have humem : (ytrans L N r x i).1 ∈ f := hy i hlt
      have hbet : between f (ztrans L N r x (i - 1)).1 (ytrans L N r x i).1 = [] :=
        (Kepler.Text.TameSpine.betwnNil huniq hne hu0mem humem).mpr hnext.symm
      rw [hbet]
      rfl
    · simp only [if_neg hnext]

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.t12_prebatch_suc_explicit

-- nfgtrans_suc 复核（本轮不动该件，仅核前置真声明）
#check @Kepler.Text.Reduction3.nfgtrans1
#check @Kepler.Text.Reduction3.nfgtransAdd
#check @Kepler.Text.Reduction4.transformCount_not
