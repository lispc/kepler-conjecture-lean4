/-
  Kepler.Text.PwssratRotateBase — W2-b P2-pre patch1：PWSSRAT/DANGEYJ rotate
  底座（split_at 分解事实 + `next_el_rotate_to_eq`，mem_uniq:171 的
  Pwssrat.next_el_rotate_to_eq 依赖件）。

  ┌─ 归属对账（HOL Light Flyspeck `text_formalization/tame/`）────────
  │ PWSSRAT.hl:122 `next_el_rotate_to_eq` → nextElRotateToEq
  │ DANGEYJ.hl:621 `HD_FST_SPLIT`     → hdFstSplit
  │ DANGEYJ.hl:110 `SND_EMPTY_INDEXL` → sndEmptyIndexl
  │ PWSSRAT.hl:92  `sizel0_not_nil` / DANGEYJ.hl:616 `mem_imp_not_nil`
  │   （inline 吸收，List.length_pos_iff / mem 常识）
  │ 本批未含（patch2 候选）：rotate_rot_indexl / next_el_rotate /
  │ next_el_power_rotate / take_index_fst_split / HD_SND_NTH_SPLIT_AT /
  │ INDEXL_EQ_SND_EMPTY 双向形（已含 → 单向）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与折算 ──────────────────────────────────────────────────
  │ `split_at`/`split_at_rec` ↦ `Kepler.Graphs.splitAt/splitAtRec`
  │   （ListAux:16/:22）；`rotate_to` ↦ `Kepler.Text.Reduction3.rotateTo`
  │   （Reduction3DefsNewVertex:54 逐字）；`indexl` ↦ `List.idxOf`；
  │ `next_el` ↦ `nextEl`（GoodListDefs:37）；`sizel` ↦ `List.length`；
  │ `HD` ↦ `headD d`（junk 支规避 Inhabited）；`uniq` ↦ `List.Nodup`。
  │ 环安全：唯一 import = Kepler.Text.Reduction3DefsNewVertex（零
  │   TameSpine 零 Assembly 主模块）。零 axiom/sorry/admit/native_decide。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction3DefsNewVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4Idx

open Kepler.Graphs (splitAt splitAtRec)
open Kepler.Text.Reduction3 (rotateTo)

/-! ## §1 splitAtRec 累积器一般化（DANGEYJ APPEND_FST_SPLIT 内容件） -/

/-- splitAtRec 一步展开（`a ≠ x` 支；HOL DANGEYJ APPEND_FST_SPLIT 同内容）。 -/
theorem splitAtRec_cons_ne {α : Type*} [BEq α] [LawfulBEq α] {x a : α}
    (hax : ¬ (a = x)) (bs as : List α) :
    splitAtRec x bs (a :: as) = splitAtRec x (bs ++ [a]) as := by
  simp [splitAtRec, beq_iff_eq, hax]

/-- splitAtRec 累积器一般化主事实：`x ∈ r`、`x ∉ bs` ⇒ 存在 `fst` 使
`r = fst ++ x :: (splitAtRec x bs r).2` 且 `(splitAtRec x bs r).1 = bs ++ fst`。
（bs := [] 即得 `split_at` 分解。） -/
theorem splitAtRec_exists_append {α : Type*} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (r : List α), ∀ (bs : List α), x ∈ r → x ∉ bs →
      ∃ fst : List α, r = fst ++ x :: (splitAtRec x bs r).2 ∧
        (splitAtRec x bs r).1 = bs ++ fst := by
  intro r
  induction r with
  | nil => exact fun bs h _ => absurd h (by simp)
  | cons a as ih =>
    intro bs hmem hbs
    by_cases hax : a = x
    · subst hax
      refine ⟨[], ?_, ?_⟩
      · simp [splitAtRec]
      · simp [splitAtRec]
    · have hxas : x ∈ as := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hax
        · exact h
      have hxbs' : x ∉ bs ++ [a] := by
        intro hc
        rcases List.mem_append.mp hc with h | h
        · exact hbs h
        · simp only [List.mem_singleton] at h
          exact hax h.symm
      obtain ⟨fst, hreq, hfst⟩ := ih (bs ++ [a]) hxas hxbs'
      refine ⟨a :: fst, ?_, ?_⟩
      · rw [splitAtRec_cons_ne hax bs as]
        exact congrArg (fun l => a :: l) hreq
      · rw [splitAtRec_cons_ne hax bs as, hfst, List.append_assoc,
          List.singleton_append]

/-- `x ∉ r` 支：`splitAt x r = (r, [])`（junk 支两库同约定）。 -/
theorem splitAtRec_of_not_mem {α : Type*} [BEq α] [LawfulBEq α] {x : α} :
    ∀ (r : List α), ∀ (bs : List α), x ∉ r → x ∉ bs →
      splitAtRec x bs r = (bs ++ r, []) := by
  intro r
  induction r with
  | nil => intro bs _ _; simp [splitAtRec]
  | cons a as ih =>
    intro bs hr hbs
    have hax : ¬ (a = x) := fun hc => hr (hc ▸ List.mem_cons.mpr (Or.inl rfl))
    have hxas : x ∉ as := fun hc => hr (List.mem_cons.mpr (Or.inr hc))
    have hxbs' : x ∉ bs ++ [a] := by
      intro hc
      rcases List.mem_append.mp hc with h | h
      · exact hbs h
      · simp only [List.mem_singleton] at h
        exact hax h.symm
    rw [splitAtRec, if_neg (by intro hc; exact hax (beq_iff_eq.mp hc)),
      ih (bs ++ [a]) hxas hxbs']
    simp [List.cons_append]

theorem splitAt_of_not_mem {α : Type*} [BEq α] [LawfulBEq α] {x : α}
    {r : List α} (h : x ∉ r) : splitAt x r = (r, []) := by
  have h2 := splitAtRec_of_not_mem r [] h (by simp)
  rw [show splitAt x r = splitAtRec x [] r from rfl, h2, List.nil_append]


/-! ## §2 HD_FST_SPLIT（DANGEYJ:621）与 SND_EMPTY 判据（bs := [] 实例形） -/

/-- **HOL `HD_FST_SPLIT`**（DANGEYJ.hl:621-:627）：fst 非空时其头 = r 头。
折算取 `headD d` 形（HOL `HD` 的 junk 支；`d` 任意缺省元）。 -/
theorem hdFstSplit {α : Type*} [BEq α] [LawfulBEq α] {x : α} {r : List α}
    (h : (splitAt x r).1 ≠ []) (d : α) :
    (splitAt x r).1.headD d = r.headD d := by
  by_cases hmem : x ∈ r
  · obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
    have hne : (splitAtRec x [] r).1 ≠ [] := h
    have hfst' : (splitAtRec x [] r).1 = fst := by
      rw [hfst, List.nil_append]
    rw [hfst'] at hne
    rw [show (splitAt x r).1 = fst from hfst', hreq]
    cases fst with
    | nil => exact absurd rfl hne
    | cons b bs => simp [List.cons_append]
  · rw [splitAt_of_not_mem hmem] at h ⊢

/-- **HOL `SND_EMPTY_INDEXL`**（DANGEYJ.hl:110-:135）：
`x ∈ r`、`Nodup r`、`(split_at x r).snd = []` ⇒ `indexl x r = sizel r - 1`。
折算：`indexl` ↦ `List.idxOf`。 -/
theorem sndEmptyIndexl {α : Type*} [BEq α] [LawfulBEq α] {x : α}
    {r : List α} (hmem : x ∈ r) (hnd : r.Nodup)
    (hsnd : (splitAt x r).2 = []) : r.idxOf x = r.length - 1 := by
  obtain ⟨fst, hreq, hfst⟩ := splitAtRec_exists_append r [] hmem (by simp)
  have h2 : (splitAtRec x [] r).2 = [] := hsnd
  have hnd' : (fst ++ x :: (splitAtRec x [] r).2).Nodup := by
    rw [← hreq]
    exact hnd
  rw [h2] at hnd'
  have hdis : List.Disjoint fst [x] := List.disjoint_of_nodup_append hnd'
  have hxf : x ∉ fst := fun hc => hdis hc (List.mem_singleton.mpr rfl)
  rw [hreq, h2, List.idxOf_append_of_notMem hxf,
    List.idxOf_cons_eq (l := []) rfl, List.length_append,
    List.length_singleton, Nat.add_zero]
  omega

end Kepler.Text.Reduction4Idx

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零 sorryAx）。 -/
#print axioms Kepler.Text.Reduction4Idx.splitAtRec_exists_append
#print axioms Kepler.Text.Reduction4Idx.hdFstSplit
#print axioms Kepler.Text.Reduction4Idx.sndEmptyIndexl
