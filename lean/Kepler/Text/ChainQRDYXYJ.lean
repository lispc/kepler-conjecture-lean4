/-
  Kepler.Text.ChainQRDYXYJ — more_lemma2 尾部封口：HOL `QRDYXYJ_list`
  （tame_list.hl:10307-:10341）的链层组装。

  ┌─ HOL 原文（reference/flyspeck/text_formalization/tame/tame_list.hl:10307）──
  │ !L N r x.
  │   good_list L /\ good_list_nodes L /\ marked_list L N r x /\ ~(final_list L r)
  │   ==>
  │   l'm L r x < l'q L N r x /\
  │   l'q L N r x < sizel (parts L r) /\
  │   SUC (l'm L r x) < l'p L N r x + l'q L N r x /\
  │   ~(FST (l'y L r x) = FST x) /\
  │   ~(FST (l'y L r x) = FST (l'z L N r x))
  └────────────────────────────────────────────────────────────────

  ┌─ 组装路线（Spine `TameList17.qrdyxyjList` 逐槽对照见 DELIVERY 续-§1）──
  │ `Hypermap.parameters`（= HOL `lemmaParameters`, hypermap.hl:12217，实测
  │ 标准三）五合取 + 四个链层 hyp 桥（`ChainMarkedTranslate.hypMLmChain`/
  │ `hypPLpChain`/`hypYLChain`/`hypZLzChain`，`2c0a6429`）+ 本 lane
  │ `ChainCardAtoms.cardAtomsOfLoopChain`（`75bc538a`）换 `(parts L r).length`
  │ + 两条 `memHypermapOfListNode`/`node_eq_of_mem` FST 反证。
  │ **不消费** `markedConclusion`（Spine 同：`qrdyxyjList` 自己取 `hsc`）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（相对 HOL；与 Spine `qrdyxyjList` 的槽位差异）───────────
  │ ① `l'm`/`l'y`/`l'p`/`l'z` 取**链层** `Reduction5.lm`/`ly`/`lp`/`lz`
  │    （`minNum`=epsilon 口径），Spine 版取 `lMSpine` 族（`sInf`）。
  │    两者在空集 junk 支不同，故四个 hyp 桥带非空前提（见 `2c0a6429` 文件头）。
  │ ② `l'q` = `hyp'q` 直接回引（tame_defs2.hl:455-456）：Lean 侧 `Hypermap.hypQ`
  │    带 `IsMarked`/`¬finalLoops` 证明参，故结论写作 `hypQ hmk hl`（rfl 级，
  │    不新造 `lq` 载体）。Spine 版多一层 `lQSpine … := hypQ …` 别名（rfl）。
  │ ③ `hnf : IsNormalFamily` / `hmk : IsMarked` / `hl : ¬mem finalLoops`
  │    显式入参——`IsMarked` 的链层推导受上游 `TameList16:1109` sorry 阻塞
  │    （`2c0a6429` ③⑥），Spine `qrdyxyjList` 同款折算（零改写）。
  │ ④ **无 `hs : sList = sListSpine` 槽**：`ly`/`lz` 的 dart 成员性由
  │    `memFListPower`（`(fList)^[i] d ∈ listOfDarts`）直达，不需要
  │    `MarkedListSpineFull` 转换 ⇒ 比预定方案少一个前提（更强）。
  │ ⑤ `sizel` ↦ `List.length`；`SUC n` ↦ `n + 1`；`FST` ↦ `.1`；`~=` ↦ `≠`。
  └────────────────────────────────────────────────────────────────

  **纪律**：零 axiom/sorry/admit/native_decide；不改任何既有陈述；
  注释正文不含「连字符紧跟斜杠」二字序列；comment-depth 0。
-/

import Kepler.Text.ChainCardAtoms
import Kepler.Text.ChainMarkedTranslate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.ChainQRDYXYJ

open Kepler.Assembly (GoodList eList fList nextEl listOfDarts)
open Kepler.Graphs (fgraph)
open Kepler.Text.Reduction5 (Dart finalList parts)
open Kepler.Text.ChainLists (markedList normalList)
open Kepler.Text.ChainMarkedQ (loopOfList loopFamilyOfList)
open Kepler.Text.TameLp (hypermapOfList GoodListNodesTl)
open Kepler.Text.TameSpine (splitConditionListSpine
  splitConditionListOfDarts memHypermapOfListNode memFListPower)
open Kepler.Text.ChainMarkedTranslate (hypMLmChain hypPLpChain hypYLChain hypZLzChain
  markedListSplitOfMarked)
open Kepler.Text.ChainCardAtoms (cardAtomsOfLoopChain)
open Kepler.Text (Hypermap Loop)

/-- **HOL `QRDYXYJ_list`**（tame_list.hl:10307-:10341）链层形。
`Hypermap.parameters`（= `lemmaParameters`）+ 四桥 + `cardAtomsOfLoopChain`
+ 两条 FST 反证。`l'q` 取 `hypQ hmk hl`（HOL `l'q` 定义即 `hyp'q` 回引）。 -/
theorem qRDYXYJListChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : markedList L hL N r x) (hf : ¬ finalList L r)
    {hnf : (hypermapOfList L hL).IsNormalFamily (loopFamilyOfList N)}
    (hmk : (hypermapOfList L hL).IsMarked (loopFamilyOfList N) hnf (loopOfList r) x)
    (hl : loopOfList r ∉ (hypermapOfList L hL).finalLoops (loopFamilyOfList N)) :
    Reduction5.lm L r x < (hypermapOfList L hL).hypQ hmk hl ∧
      (hypermapOfList L hL).hypQ hmk hl < (parts L r).length ∧
      Reduction5.lm L r x + 1 < Reduction5.lp L N r x + (hypermapOfList L hL).hypQ hmk hl ∧
      (Reduction5.ly L r x).1 ≠ x.1 ∧
      (Reduction5.ly L r x).1 ≠ (Reduction5.lz L N r x).1 := by
  have hsc : splitConditionListSpine hL N r x := markedListSplitOfMarked L hL hm hf
  have hnedg : (hypermapOfList L hL).EdgeNondegenerate := hm.1.edgeNondegenerate
  obtain ⟨h1, h2, h3, h4, h5⟩ := Hypermap.parameters (hypermapOfList L hL) hmk hl
  rw [hypMLmChain L hL hgn hunL hm hf] at h1 h3
  rw [hypPLpChain L hL hgn hunL hm hf] at h3
  rw [cardAtomsOfLoopChain L hL hgn hm.2.1 hnedg hunL hm.2.2.1] at h2
  rw [hypYLChain L hL hgn hunL hm hf] at h4 h5
  rw [hypZLzChain L hL hgn hunL hm hf] at h5
  have hxd : x ∈ listOfDarts L := splitConditionListOfDarts hsc
  have hyD : Reduction5.ly L r x ∈ listOfDarts L := by
    show (fList L)^[Nat.succ (Reduction5.lm L r x)] x ∈ listOfDarts L
    exact memFListPower L hL hxd (Nat.succ (Reduction5.lm L r x))
  have hzD : Reduction5.lz L N r x ∈ listOfDarts L := by
    show (fList L)^[Nat.succ (Reduction5.lp L N r x)] (Reduction5.ly L r x) ∈ listOfDarts L
    exact memFListPower L hL hyD (Nat.succ (Reduction5.lp L N r x))
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · -- `FST (l'y) ≠ FST x`
    intro hcon
    have hny : Reduction5.ly L r x ∈ (hypermapOfList L hL).node x :=
      (memHypermapOfListNode hL hgn hxd).mpr ⟨hcon.symm, hyD⟩
    exact h4 ((hypermapOfList L hL).node_eq_of_mem hny).symm
  · -- `FST (l'y) ≠ FST (l'z)`
    intro hcon
    have hny : Reduction5.ly L r x ∈ (hypermapOfList L hL).node (Reduction5.lz L N r x) :=
      (memHypermapOfListNode hL hgn hzD).mpr ⟨hcon.symm, hyD⟩
    exact h5 ((hypermapOfList L hL).node_eq_of_mem hny).symm

end Kepler.Text.ChainQRDYXYJ

/-! 公理审计锚（本文件编译即执行；预期 = 标准三，零 sorryAx。） -/
#print axioms Kepler.Text.ChainQRDYXYJ.qRDYXYJListChain
