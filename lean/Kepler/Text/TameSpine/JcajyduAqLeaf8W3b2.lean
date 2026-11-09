/-
  JcajyduAqLeaf8W3b2 — AQ8 波 3b-i-2：GSUBGOAL#3「提 finer part」的
  **可独立闭环内核**（连续段 parts 细化）+ 缺口机器证据。

  ┌─ 侦察结论（15 分钟小侦察，机器证据 logs/probe_w3b2.log）─────────
  │ HOL GSUBGOAL#3（AQ8.hl:1010 附近）：
  │   `!u. MEM u (parts L s) ==> ?v. MEM v (parts L r) /\
  │     (!a. MEM a u ==> MEM a v) /\ FST (HD u) = FST (HD v)`
  │ 其中 `s = [z] ++ betwn r z y ++ [y]`（r 的**连续闭弧**）。
  │ 数学内核：s 是 r 的连续段 ⇒ s 的 parts 是 r 的 parts 的**细化**
  │ ⇒ 每个 u ∈ parts s 本身就是一个 v ∈ parts r（取 v := u 即可）。
  │ 载体：`partsCat`（TameList9:1030）——「junction 处有断点 ⇒
  │ parts 分裂」，两次即得 `parts r = parts a ++ parts s ++ parts b`。
  │ 侦察判定：`partsInNode`/`partsNodeInversePower`（TameList10:392/341）
  │ **不需要**（它们给 part 内同 node，不是实现本步的工具）；真正缺口是
  │ **几何分解** `∃ a b, r = a ++ s ++ b` + 两处断点（见 §3 缺口清单）。
  └────────────────────────────────────────────────────────────────

  ┌─ 本波件目（可独立闭环，零 condition 槽）───────────────────────
  │ ① aqs_partsContiguousRefine  连续段细化（generic，`partsCat` ×2）
  │ ② aq8w3b2_partsRefineOfSplit GSUBGOAL#3 的逐字形（取 v := u）
  └────────────────────────────────────────────────────────────────

  ┌─ 缺口（下一波；已在 §3 列清并给候选载体）─────────────────────
  │ 从 `s = [z] ++ betwn r z y ++ [y]` 推出 `∃ a b, r = a ++ s ++ b`
  │ 与两处断点：`betwnTakeDrop`（TameList3:986）/ `betwnRot`
  │ （JcajyduBetwnRot:179）为候选；y 端断点
  │ `nextEl r y ≠ fList L (eList y)` 库内无（`nextRNotEqF` 是非 e 版），
  │ 估 60–100 行（见 DELIVERY §AQ8W3b2-4）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算）─────────────────────────────────────────────
  │ ① `MEM u (parts L s) ==> MEM u (parts L r)`：本件给「u 本身即 r 的
  │    part」，比 HOL 的「∃v 含 u」更强；GSUBGOAL#3 形在其上 rfl 收口。
  │ ② `FST o HD` ↦ `fun p => p.head!.1`；`uniq` ↦ `Nodup`；逐字。
  │ ③ 断点谓词 `~(next_el … = f_list L (e_list …))` ↦
  │    `nextEl … ≠ fList L (eList …)`（逐字）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件：`aqs_`（跨叶）/`aq8w3b2_`；私件 `aq8w3b2_`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W3b

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 基本件（本版 Lean 无公开名，逐条私证） -/

/-- 连接的末元（右半非空）。 -/
private theorem aq8w3b2_getLast!_append {α : Type*} [Inhabited α] (s : List α)
    {t : List α} (ht : t ≠ []) : (s ++ t).getLast! = t.getLast! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast!_eq_getLast?_getD, List.getLast?_append]
  cases h : t.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp h) ht
  | some x => simp

/-- 非空表 `getLast!` 是成员。 -/
private theorem aq8w3b2_getLast!Mem {α : Type*} [Inhabited α] {l : List α}
    (h : l ≠ []) : l.getLast! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rw [List.getLast!_cons_eq_getLastD]; exact List.getLastD_mem_cons

/-! ## §1 连续段细化（`partsCat` ×2） -/

/-- **连续段细化**：若 `r = a ++ s ++ b`（`a`/`s`/`b` 均非空、`r` 无重）、
且 junction 两处有断点——`a.getLast!` 与 `s.getLast!` 处
`nextEl r · ≠ fList L (eList ·)`——则 `s` 的每个 part **本身就是** `r` 的 part
（`parts r = parts a ++ parts s ++ parts b`）。

这是 HOL GSUBGOAL#3（`∀ u ∈ parts L s, ∃ v ∈ parts L r, u ⊆ v ∧
FST(HD u) = FST(HD v)`）的**强形内核**：取 `v := u` 即得。 -/
theorem aqs_partsContiguousRefine (L : fgraph ℕ) (hL : GoodList L)
    {r a s b : List (ℕ × ℕ)} (hsplit : r = a ++ s ++ b)
    (ha : a ≠ []) (hs : s ≠ []) (hb : b ≠ []) (hr : r.Nodup)
    (hbrk1 : nextEl r a.getLast! ≠ fList L (eList a.getLast!))
    (hbrk2 : nextEl r s.getLast! ≠ fList L (eList s.getLast!)) :
    ∀ u ∈ partsSpine L s, u ∈ partsSpine L r := by
  have hsplit' : r = a ++ (s ++ b) := by rw [hsplit, List.append_assoc]
  have hsbnd : (s ++ b).Nodup :=
    List.Sublist.nodup (by rw [hsplit']; exact List.sublist_append_right a (s ++ b)) hr
  have hsnd : s.Nodup := List.Sublist.nodup (List.sublist_append_left s b) hsbnd
  have hbnd : b.Nodup := List.Sublist.nodup (List.sublist_append_right s b) hsbnd
  have hlastsb : (s ++ b).getLast! = b.getLast! := aq8w3b2_getLast!_append s hb
  have hlastne : s.getLast! ≠ (s ++ b).getLast! := by
    intro hcon
    have h1 : s.getLast! ∈ s := aq8w3b2_getLast!Mem hs
    have h2 : (s ++ b).getLast! ∈ b := by
      rw [hlastsb]; exact aq8w3b2_getLast!Mem hb
    rw [← hcon] at h2
    exact ((List.nodup_append.mp hsbnd).2.2 _ h1 _ h2) rfl
  -- `s` 末元在 `r` 内与在 `s ++ b` 内后继一致（`nextElCat2`）
  have hnextEq : nextEl (s ++ b) s.getLast! = nextEl r s.getLast! := by
    have hmem : s.getLast! ∈ s ++ b :=
      List.mem_append.mpr (Or.inl (aq8w3b2_getLast!Mem hs))
    have h2 := nextElCat2 (s := a) (t := s ++ b) (x := s.getLast!)
      (by rw [← hsplit']; exact hr) hmem hlastne
    rw [← hsplit'] at h2
    exact h2.symm
  have hbrk2' : nextEl (s ++ b) s.getLast! ≠ fList L (eList s.getLast!) := by
    rw [hnextEq]; exact hbrk2
  have hsbne : s ++ b ≠ [] :=
    List.ne_nil_of_length_pos (by
      rw [List.length_append]
      have := List.length_pos_of_ne_nil hs
      omega)
  -- 两次 `partsCat`
  have h1 : partsSpine L r = partsSpine L a ++ partsSpine L (s ++ b) :=
    partsCat L (r := r) (u := a) (v := s ++ b) (x := a.getLast!) hsplit' rfl ha hsbne hbrk1 hr
  have h2 : partsSpine L (s ++ b) = partsSpine L s ++ partsSpine L b :=
    partsCat L (r := s ++ b) (u := s) (v := b) (x := s.getLast!) rfl rfl hs hb hbrk2' hsbnd
  intro u hu
  rw [h1, h2]
  simp only [List.mem_append]
  exact Or.inr (Or.inl hu)

/-! ## §2 GSUBGOAL#3 逐字形（取 `v := u`） -/

/-- **HOL GSUBGOAL#3**（AQ8.hl:1010 附近）的连续段形：
`∀ u ∈ parts L s, ∃ v ∈ parts L r, (∀ a ∈ u, a ∈ v) ∧ (HD u).1 = (HD v).1`。

由 §1 取 `v := u`（含自反、`head!` 相等 rfl）即得。**几何分解**
（`∃ a b, r = a ++ s ++ b` + 两断点）为下一波缺口（§3/DELIVERY）。 -/
theorem aq8w3b2_partsRefineOfSplit (L : fgraph ℕ) (hL : GoodList L)
    {r a s b : List (ℕ × ℕ)} (hsplit : r = a ++ s ++ b)
    (ha : a ≠ []) (hs : s ≠ []) (hb : b ≠ []) (hr : r.Nodup)
    (hbrk1 : nextEl r a.getLast! ≠ fList L (eList a.getLast!))
    (hbrk2 : nextEl r s.getLast! ≠ fList L (eList s.getLast!)) :
    ∀ u ∈ partsSpine L s,
      ∃ v ∈ partsSpine L r, (∀ x ∈ u, x ∈ v) ∧ (u.head!).1 = (v.head!).1 := by
  intro u hu
  exact ⟨u, aqs_partsContiguousRefine L hL hsplit ha hs hb hr hbrk1 hbrk2 u hu,
    fun x hx => hx, rfl⟩

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：两件全 ⊆ 标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aqs_partsContiguousRefine
#print axioms Kepler.Text.TameSpine.aq8w3b2_partsRefineOfSplit
