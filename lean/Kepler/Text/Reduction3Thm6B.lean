/-
  Kepler.Text.Reduction3Thm6B — T6B 支撑三件（编排者 2026-11-10 批准）。

  ┌─ 逐件对账 ────────────────────────────────────────────────────
  │   Aq23.LAST_FLATTEN_2（reduction3.hl:1626 foldl_steps 消费）
  │     → §A lastFlattenLast（+ concat 形原语）——纯列表事实，
  │       **链侧化即解 T5 的 Aq 门禁一半**。
  │   dest_triple0_step_last_nonnil reduction3.hl:1607 → §B
  │     （destTriple0Step 结果恒以非空段收尾）。
  │   indexf 双常量桥（TameSpine.indexf vs Reduction5.indexf）
  │     → §C indexf_eq_spine（idxOf 实例桥 + by_cases 对齐 ite）。
  │ 纪律：零 axiom/sorry/admit/native_decide；注释框行尾禁「减斜杠」；
  │ 「rw 只改首匹配」——本文件的 if 重写一律 `simp only [if_pos/if_neg]`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3Thm6
import Kepler.Text.TameSpine.TameList3
import Kepler.Text.MoreLemma2Island1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction3

open Kepler.Assembly (nextEl prevEl)
open Kepler.Graphs (between)
open Kepler.Text.Reduction5 (Dart indexf)

/-! ## §0 辅助 -/

private theorem getLastD_append_of_ne {α : Type} (d : α) (a : List α) {b : List α}
    (h : b ≠ []) : (a ++ b).getLastD d = b.getLastD d := by
  induction a generalizing d with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    cases b with
    | nil => exact (h rfl).elim
    | cons y ys => rw [List.getLastD_cons, List.getLastD_cons]

/-! ## §A `LAST_FLATTEN_2` 链侧化（AQ23 纯列表事实，解 T5 Aq 门禁一半）

`LAST (flatten r) = LAST (LAST r)`（`r ≠ []`、末段非空）。 -/

/-- concat 形原语：`flatten (pre ++ [last])` 的末元 = `last` 的末元。 -/
theorem lastFlattenLastConcat (pre : List (List (Option ℕ)))
    (last : List (Option ℕ)) (h : last ≠ []) :
    (pre ++ [last]).flatten.getLastD none = last.getLastD none := by
  rw [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  exact getLastD_append_of_ne none _ h

/-- HOL `AQ23.LAST_FLATTEN_2`：`~(r=[]) ∧ ~(LAST r = []) ==>
LAST (flatten r) = LAST (LAST r)`（junk 缺省形：`getLastD []`/`getLastD none`）。 -/
theorem lastFlattenLast (r : List (List (Option ℕ))) (hne : r ≠ [])
    (hlne : r.getLastD [] ≠ []) :
    r.flatten.getLastD none = (r.getLastD []).getLastD none := by
  have hget : r.getLastD [] = List.getLast r hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  have hdecomp : r.dropLast ++ [r.getLastD []] = r := by
    rw [hget]
    exact List.dropLast_concat_getLast hne
  conv_lhs => rw [← hdecomp]
  exact lastFlattenLastConcat r.dropLast (r.getLastD []) hlne

/-! ## §B `dest_triple0_step_last_nonnil`（reduction3.hl:1607）

`destTrip0Step` 的任何结果段表以非空段收尾（四分支全部新增非空段）。 -/

/-- HOL `dest_triple0_step_last_nonnil`（reduction3.hl:1607）。 -/
theorem destTriple0StepLastNonnil (f : List ℕ)
    (s : List (List (Option ℕ))) (t : ℕ × ℕ × ℕ) :
    (destTriple0Step f s t).getLastD [] ≠ [] := by
  obtain ⟨u, v, n⟩ := t
  unfold destTriple0Step
  dsimp only
  by_cases h0 : s.flatten = []
  · simp only [if_pos h0]
    simp
  · simp only [if_neg h0]
    by_cases h1 : ((s.getLastD []).getLastD none).getD 0 = u
    · simp only [if_pos h1]
      rw [List.getLastD_concat]
      simp
    · simp only [if_neg h1]
      by_cases h2 : nextEl f (((s.getLastD []).getLastD none).getD 0) = u
      · simp only [if_pos h2]
        rw [List.getLastD_concat]
        simp
      · simp only [if_neg h2]
        rw [List.getLastD_concat]
        simp

/-! ## §C `indexf_eq_spine`（双常量桥：`Reduction5.indexf` = `TameSpine.indexf`）

同体定义，差异仅在实例来源（链侧 `[DecidableEq]` → 派生 BEq；Spine 侧
显式 `[BEq][LawfulBEq]`）。桥分两步：`idxOf` 实例桥（LawfulBEq 判等两向
= decide）+ `by_cases` 对齐两处 ite。 -/

/-- `idxOf` 在 lawful-BEq 与由 DecidableEq 派生的 BEq 下同值。 -/
private theorem idxOf_eq_derived {α : Type} [b : BEq α] [lb : LawfulBEq α]
    [de : DecidableEq α] (z : α) (s : List α) :
    @List.idxOf α b z s = @List.idxOf α (@instBEqOfDecidableEq α de) z s := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.idxOf_cons]
    have hbeq : @BEq.beq α b a z = decide (a = z) := by
      by_cases h : a = z
      · have hb : @BEq.beq α b a z = true := beq_iff_eq.mpr h
        rw [hb, decide_eq_true_eq.mpr h]
      · have hb : @BEq.beq α b a z = false := beq_eq_false_iff_ne.mpr h
        rw [hb, decide_eq_false_iff_not.mpr h]
    have hbeq' : @BEq.beq α (@instBEqOfDecidableEq α de) a z = decide (a = z) := rfl
    rw [hbeq, hbeq', ih]

/-- 双常量桥：链 `indexf` = Spine `indexf`。 -/
theorem indexf_eq_spine {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (x y : α) (s : List α) :
    indexf x y s = Kepler.Text.TameSpine.indexf x y s := by
  unfold Kepler.Text.Reduction5.indexf Kepler.Text.TameSpine.indexf
  by_cases h : x ∈ s ∧ y ∈ s
  · simp only [if_pos h]
    rw [idxOf_eq_derived y s, idxOf_eq_derived x s]
  · simp only [if_neg h]

end Kepler.Text.Reduction3

-- 探针（编译即执行）
#print axioms Kepler.Text.Reduction3.lastFlattenLast
#print axioms Kepler.Text.Reduction3.destTriple0StepLastNonnil
#print axioms Kepler.Text.Reduction3.indexf_eq_spine
