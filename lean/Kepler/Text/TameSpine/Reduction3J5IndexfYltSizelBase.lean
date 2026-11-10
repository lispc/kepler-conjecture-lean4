/-
  Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelBase — tame-corr nb14：双怪件
  `indexf_y_lt_sizel`（more_lemma2:427）/ `indexf_y_lt_sizel_pre`（:890）的
  第①段（基座）：`core` 的 uniq / 长度 / parts 首顶点单射 / 基数界。

  ┌─ 归属对账（HOL `more_lemma2.hl` 第①段，:441-:466）─────────────────
  │ `quotient_all_uniq` → `core` 无重（HOL `uniq (core L r)`）；
  │ `Seq.size_map`（FST∘HD）→ `sizel (core L r) = sizel (parts L r)`；
  │ `uniq_imp_inj` → parts 的首顶点映射单射（原子 ↔ 顶点一一）；
  │ `card_le_size` → `CARD (set_of_list (parts L r)) ≤ sizel (parts L r)`。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5PowerCoreFace
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.MoreLemma2Island2
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.MoreLemma2PartsFst
import Kepler.Text.MoreLemma2QuotientAlt
import Kepler.Text.ChainBridgeParts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart core parts quotientList finalList rtrans ytrans ztrans
  transformCount indexf)

/-- 非空表 `headD` = `head!`（局部辅件；ChainBridgeParts 的同名件是 private）。 -/
private theorem headD_eq_headBang_local {α : Type} [Inhabited α] {l : List α}
    (h : l ≠ []) (d : α) : l.headD d = l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- **HOL `more_lemma2.hl` 第①段：`core` 无重**
（`quotient_all_uniq` 于 `core L r ∈ quotientList L N`）。 -/
theorem coreNodupOfMarked (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) : (core L r).Nodup := by
  have hq := Kepler.Text.MoreLemma2a23.quotientAllUniq L hL hm
  have hmem : core L r ∈ quotientList L N := by
    show ((parts L r).map (fun l => (l.headD (0, 0)).1)) ∈
      Kepler.Text.Reduction5.quotientList L N
    unfold Kepler.Text.Reduction5.quotientList Kepler.Text.Reduction5.coreList
    exact List.mem_map.mpr ⟨parts L r, List.mem_map.mpr ⟨r, hm.2.2.1, rfl⟩, rfl⟩
  exact hq (core L r) hmem

/-- **HOL `Seq.size_map` 步骤**：`sizel (core L r) = sizel (parts L r)`。 -/
theorem coreLengthEqParts (L : fgraph ℕ) (r : List Dart) :
    (core L r).length = (parts L r).length := by
  show ((parts L r).map (fun l => (l.headD (0, 0)).1)).length = (parts L r).length
  rw [List.length_map]

/-- **HOL `uniq_imp_inj` 步骤**：`parts` 上「首顶点（FST of HD）」单射——两个
原子首顶点相同则原子相同。证 = `core` 无重 + `uniqImpInj`。 -/
theorem partsHeadFstInj (L : fgraph ℕ) (hL : GoodList L)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {p q : List Dart} (hp : p ∈ parts L r) (hq : q ∈ parts L r)
    (h : p.head!.1 = q.head!.1) : p = q := by
  have hnd := coreNodupOfMarked L hL hm
  have hnd' : ((parts L r).map (fun l : List Dart => (l.headD (0, 0)).1)).Nodup := hnd
  have hpne : p ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r p hp
  have hqne : q ≠ [] := Kepler.Text.MoreLemma2Island2.partsAllNonnil L r q hq
  have hh : (fun l : List Dart => (l.headD (0, 0)).1) p
      = (fun l : List Dart => (l.headD (0, 0)).1) q := by
    show (p.headD (0, 0)).1 = (q.headD (0, 0)).1
    rw [headD_eq_headBang_local hpne, headD_eq_headBang_local hqne]
    exact h
  exact Kepler.Text.TameSpine.uniqImpInj hnd' hp hq hh

/-- **HOL `card_le_size` 于 parts**：`CARD (set_of_list (parts L r)) ≤ sizel (parts L r)`。 -/
theorem partsToFinsetCardLe (L : fgraph ℕ) (r : List Dart) :
    (parts L r).toFinset.card ≤ (parts L r).length :=
  Kepler.Text.MoreLemma2Island1.cardLeSize (parts L r)

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.coreNodupOfMarked
#print axioms Kepler.Text.TameSpine.coreLengthEqParts
#print axioms Kepler.Text.TameSpine.partsHeadFstInj
#print axioms Kepler.Text.TameSpine.partsToFinsetCardLe
