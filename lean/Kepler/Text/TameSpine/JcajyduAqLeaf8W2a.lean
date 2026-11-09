/-
  JcajyduAqLeaf8W2a — AQ8 波 2a-i：`last_parts_z1_not_y1` + `last_parts_z1_not_z1`。

  ┌─ 件目与 HOL 锚 ───────────────────────────────────────────────
  │ ① aq8w2a_lastPartsZ1NotY1   AQ8.hl:1397（52 行）
  │ ② aq8w2a_lastPartsZ1NotZ1   AQ8.hl:1449（57 行）
  │ ③ aqs_fstYNeFstZ            公共提升件（QRDYXYJ_list 的 FST 分量；
  │    原 W1a 私件 aq8w1_fstYNeFstZ 的公开形，W2a-i/ii 与后续波共用）
  └────────────────────────────────────────────────────────────────

  ┌─ 命名（编排者规则）───────────────────────────────────────────
  │ z1 族消费者实测：AQ9/AQ12/AQ13 均 0 次，仅 AQ8 自身（13 处）
  │ ⇒ `aq8w2a_` 前缀。`aqs_fstYNeFstZ` 为跨件公共件（W1a 私件提升），
  │ 用中立 `aqs_`。
  └────────────────────────────────────────────────────────────────

  ┌─ 内容级去重（全 3 名；全闭包负探针 probe_aq8w2ai.log）────────
  │ ① 目标名 `aq8w2a_lastPartsZ1NotY1/NotZ1`、`aqs_fstYNeFstZ` 与旧
  │    驼峰名 `lastPartsZ1NotY1/NotZ1` 全 Unknown（import 到
  │    JcajyduAqLeaf8W1b + Split1C/TameList10/TameList7/TameList59；
  │    AGENTS §7.1 #18）。
  │ ② z1 两件零命中；引擎全在库且标准三（probe_aq8w2ai.log）：
  │    `fstEqNextYtransV0` / `fstEqPrevZtransV0`（W0.5）、`partsFst`
  │    （TameList10:442）、`normalListPartsNextLast`（TameList10:463）、
  │    `prevRNotEqF`（Split1C:100）、`nextElPrevElUniq`
  │    （JcajyduRed2Trans:94）、`normalListNormal`/`markedTranslate`/
  │    `qrdyxyjList`（W1a 已消费链）。
  │ ③ **无条件/常态形**：两件均无 condition 槽（W1b 的 IsMarked 解禁
  │    路径复用；不拖 marked 全槽之外的任何槽）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算；语义逐字对齐消费点）───────────────────────────
  │ ① HOL 命名 y/y1/z/z1 + 四条等式前件；Lean 折叠为具体项：
  │    y ↦ lYSpine L r x，y1 ↦ nextEl r (lYSpine L r x)，
  │    z ↦ lZSpine L N r x，z1 ↦ prevEl r (lZSpine L N r x)。
  │ ② `LAST p` ↦ `p.getLast!`；`MEM z1 p` 保留为显式槽 `hz1p`。
  │ ③ 结论 `~(LAST p = y1)` ↦ `p.getLast! ≠ nextEl r (lYSpine L r x)`；
  │    `~(LAST p = z1)` ↦ `p.getLast! ≠ prevEl r (lZSpine L N r x)`。
  └────────────────────────────────────────────────────────────────

  ┌─ 路线（HOL 逐句）─────────────────────────────────────────────
  │ not_y1：反设 LAST p = y1。`partsFst` 给 z1.1 = HD.1、LAST.1 = HD.1；
  │ `fstEqNextYtransV0` 给 y1.1 = y.1；`fstEqPrevZtransV0` 给 z1.1 = z.1；
  │ 串成 y.1 = z.1，撞 QRDYXYJ_list 的 FST 分量（aqs_fstYNeFstZ）。
  │ not_z1：反设 LAST p = z1。`normalListPartsNextLast` 给
  │ nextEl r LAST = fList LAST ⇒（代入 + `nextElPrevElUniq`）z = fList z1，
  │ 撞 `prevRNotEqF`（fList z1 ≠ z）。
  └────────────────────────────────────────────────────────────────

  ┌─ 纪律 ────────────────────────────────────────────────────────
  │ 零 axiom/sorry/admit/native_decide；注释框行内禁「减斜杠」；
  │ 公开件前缀见命名节，私件 `aq8w2a_`。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.TameSpine.JcajyduAqLeaf8W1b
import Kepler.Text.TameSpine.JcajyduAqSplit1C
import Kepler.Text.TameSpine.JcajyduRed2Trans
import Kepler.Text.TameSpine.TameList10
import Kepler.Text.TameSpine.TameList7
import Kepler.Text.TameSpine.TameList18
import Kepler.Text.TameSpine.TameList59

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (nextEl prevEl eList fList nList listOfDarts listPairs
  findFaceDarts GoodList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)

/-! ## §0 私件与公共 FST 分量 -/

/-- `s ≠ [] ⇒ s.getLast! ∈ s`（per-file-private 约定零共享）。 -/
private theorem aq8w2a_getLastMem {α : Type} [Inhabited α] {s : List α}
    (h : s ≠ []) : s.getLast! ∈ s := by
  have hpos : 0 < s.length := List.length_pos_of_ne_nil h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  simp

/-- HOL `QRDYXYJ_list`（tame_list.hl:10307）的 FST 分量：
`~(FST (l'y L r x) = FST (l'z L N r x))`。
供给 = `markedTranslate` 的 IsMarked/非 final 证人 + `qrdyxyjList`。
（W1a 私件 `aq8w1_fstYNeFstZ` 的公开提升，供 W2a-i/ii 与后续波共用。） -/
theorem aqs_fstYNeFstZ (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r) :
    (lYSpine L r x).1 ≠ (lZSpine L N r x).1 := by
  have hn : NormalListSpine hL N := hm.1.2.1
  have hnf := normalListNormal hL hgn hm.1.1 hn
  have htr := markedTranslate L hL hgn hunL hm hf hnf
  exact (qrdyxyjList L hL hgn hunL hm hf (hnf := hnf)
    htr.2.2.2.2.2.1 htr.2.2.2.2.2.2.1).2.2.2.2

/-! ## §1 `last_parts_z1_not_y1`（HOL AQ8.hl:1397） -/

/-- HOL `last_parts_z1_not_y1`（AQ8.hl:1397）：part 末元 ≠ y1（= nextEl r l'y）。
反设相等 ⇒ FST 链 y.1 = y1.1 = HD.1 = z1.1 = z.1，撞 QRDYXYJ_list。 -/
theorem aq8w2a_lastPartsZ1NotY1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hz1p : prevEl r (lZSpine L N r x) ∈ p) :
    p.getLast! ≠ nextEl r (lYSpine L r x) := by
  intro hLAST
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hn : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  have hpne : p ≠ [] := partsAllNonnil L hr1 hr2 p hp
  have hlastmem : p.getLast! ∈ p := aq8w2a_getLastMem hpne
  have h1 : (prevEl r (lZSpine L N r x)).1 = p.head!.1 := partsFst L hL hn hrN hp hz1p
  have h2 : (p.getLast!).1 = p.head!.1 := partsFst L hL hn hrN hp hlastmem
  have hfstNext := fstEqNextYtransV0 L hL hgn hm hf
  have hfstPrev := fstEqPrevZtransV0 L hL hgn hm hf
  have hY1Head : (nextEl r (lYSpine L r x)).1 = p.head!.1 := by
    rw [← hLAST]
    exact h2
  exact aqs_fstYNeFstZ L hL hgn hunL hm hf
    (hfstNext.symm.trans (hY1Head.trans (h1.symm.trans hfstPrev)))

/-! ## §2 `last_parts_z1_not_z1`（HOL AQ8.hl:1449） -/

/-- HOL `last_parts_z1_not_z1`（AQ8.hl:1449）：part 末元 ≠ z1（= prevEl r l'z）。
反设相等 ⇒ nextEl r z1 = fList z1，`nextElPrevElUniq` 给 nextEl r z1 = z，
撞 `prevRNotEqF`（fList z1 ≠ z）。 -/
theorem aq8w2a_lastPartsZ1NotZ1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)} {x : ℕ × ℕ}
    {p : List (ℕ × ℕ)}
    (hm : MarkedListSpineFull hL N r x) (hf : ¬finalListSpine L r)
    (hp : p ∈ partsSpine L r) (hz1p : prevEl r (lZSpine L N r x) ∈ p) :
    p.getLast! ≠ prevEl r (lZSpine L N r x) := by
  intro hLAST
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1.1
  have hn : NormalListSpine hL N := hm.1.2.1
  have hrN : r ∈ N := hm.1.2.2.1
  obtain ⟨hr1, hr2⟩ := normalListUniqNonnil hn hrN
  have hnl : nextEl r p.getLast! = fList L p.getLast! :=
    normalListPartsNextLast L hL hn hrN hp
  have hprev : nextEl r (prevEl r (lZSpine L N r x)) = lZSpine L N r x :=
    nextElPrevElUniq hr1 _
  rw [hLAST, hprev] at hnl
  exact prevRNotEqF L hL hgn hunL hm hf hnl.symm

end Kepler.Text.TameSpine

-- 探针（编译即执行；目标：三件全标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.aqs_fstYNeFstZ
#print axioms Kepler.Text.TameSpine.aq8w2a_lastPartsZ1NotY1
#print axioms Kepler.Text.TameSpine.aq8w2a_lastPartsZ1NotZ1
