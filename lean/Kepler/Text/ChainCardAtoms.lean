/-
  Kepler.Text.ChainCardAtoms — more_lemma2 尾部：HOL `card_atoms_of_loop`
  （tame_list.hl:10243-:10304）的链层移植；`QRDYXYJ_list` 装配前置 3/3。

  ┌─ HOL 原文（reference/flyspeck/text_formalization/tame/tame_list.hl:10243）──
  │ !L N r.
  │   good_list L /\ good_list_nodes L /\ normal_list L N /\
  │   is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\ MEM r N
  │   ==>
  │   CARD (atoms_of_loop (hypermap_of_list L) (loop_of_list r)) = sizel (parts L r)
  └────────────────────────────────────────────────────────────────

  ┌─ 普查（本车道 2026-11-09：载体就位表 + 判定）───────────────────
  │ HOL 名                Spine 件              链层对应            桥
  │ atoms_of_loop         Hypermap.atomsOfLoop  **同一**            零桥（Dart = ℕ×ℕ abbrev，
  │                                                            Loop 类型同一）
  │ set_of_list (parts)   setOfListSpine/长度   不需要（Spine 证体内部件）—
  │ parts                 partsSpine            Reduction5.parts    `ChainBridge.parts_eq_partsSpine`
  │ normal_list           NormalListSpine       ChainLists.normalList `ChainBridge.normalList_iff_…`
  │ loop_of_list          loopOfListSpine       ChainMarkedQ.loopOfList 定义即同（defeq）
  │ sizel                 length               **length**          链层口径（批 12 记账）
  │ is_edge_nondegenerate EdgeNondegenerate    **同一**            零桥
  │ all uniq L            ∀ l ∈ L, l.Nodup     **同一**            显式入参（同 Spine）
  │ **判定：可做，零新机器**——Spine `cardAtomsOfLoop`（TameList18:172）实测
  │ `[propext, Classical.choice, Quot.sound]`（不吃 TameList16:1109 sorry），
  │ 两桥（`parts_eq_partsSpine` / `normalList_iff_normalListSpine`）均已落库；
  │ 链层版 = 桥换元 ∘ Spine 件，实测实现 ~10 行（本文件总计 ~80 行含记档）。
  └────────────────────────────────────────────────────────────────

  ┌─ 载体与 DIFFERS（与 `ChainMarkedTranslate` 同款口径）───────────
  │ ① `hgn : GoodListNodesTl L hL`（HOL `good_list_nodes L`）显式入参但
  │    **不使用**（Spine 同：`_hgn`）——保留以逐字对齐 HOL 前提表。
  │ ② `hunL : ∀ l ∈ L, l.Nodup`（HOL `all uniq L`）：HOL 由 marked_list +
  │    `simple_hypermap_all_uniq` 内部取得；本件前提只有 `normal_list`，
  │    该路径不适用，故按 `TameList17/18` 先例显式化
  │    （`all uniq L` 不可由 `GoodList L` 推出，GoodListDefs:38/:72）。
  │ ③ `sizel (parts L r)` ↦ `(parts L r).length`；`CARD (set_of_list …)` 侧
  │    的 `toFinset`/`ncard` 机器全在 Spine 证体内，链层不重建。
  │ ④ 证明路线：链层谓词 → 两桥 → Spine `cardAtomsOfLoop`（公开陈述零 Spine 谓词）。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；不改任何既有陈述；
  注释正文不含「连字符紧跟斜杠」二字序列；comment-depth 0。
-/

import Kepler.Text.ChainMarkedQ
import Kepler.Text.TameSpine.TameList18

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainCardAtoms

open Kepler.Assembly (GoodList listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart parts)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.ChainMarkedQ (loopOfList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (NormalListSpine loopOfListSpine partsSpine cardAtomsOfLoop)
open Kepler.Text.ChainBridge (parts_eq_partsSpine normalList_iff_normalListSpine)
open Kepler.Text (Hypermap Loop)

/-! ## §1 `card_atoms_of_loop`（HOL tame_list.hl:10243-:10304）

`CARD (atoms_of_loop (hypermap_of_list L) (loop_of_list r)) = sizel (parts L r)`：
BIJ `p ↦ atom (loop_of_list r) (LAST p)`（Spine 证体 `atomsOfLoopBijOnParts`）
给出两侧等势；链层只需 `parts ↔ partsSpine` 与 `normalList ↔ NormalListSpine`
两桥（均已落库）折回链载体。 -/

/-- **HOL `card_atoms_of_loop`**（tame_list.hl:10243）
`good_list L /\ good_list_nodes L /\ normal_list L N /\
 is_edge_nondegenerate (hypermap_of_list L) /\ all uniq L /\ MEM r N ==>
 CARD (atoms_of_loop (hypermap_of_list L) (loop_of_list r)) = sizel (parts L r)`。
`hgn` 保留但不使用（Spine `_hgn` 同）；`hunL` = HOL `all uniq L`（DIFFERS-②）。 -/
theorem cardAtomsOfLoopChain (L : fgraph ℕ) (hL : GoodList L)
    (_hgn : GoodListNodesTl L hL) {N : List (List Dart)}
    (hn : normalList L hL N)
    (hnedg : (hypermapOfList L hL).EdgeNondegenerate)
    (hunL : ∀ l ∈ L, l.Nodup)
    {r : List Dart} (hr : r ∈ N) :
    ((hypermapOfList L hL).atomsOfLoop (loopOfList r)).ncard
      = (parts L r).length := by
  rw [parts_eq_partsSpine L r]
  exact cardAtomsOfLoop L hL _hgn ((normalList_iff_normalListSpine L hL N).mp hn) hnedg hunL hr

end Kepler.Text.ChainCardAtoms

/-! 公理审计锚（本文件编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.ChainCardAtoms.cardAtomsOfLoopChain
