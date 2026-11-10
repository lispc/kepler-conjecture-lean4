/-
  Kepler.Text.TameSpine.Reduction3ChainTower — chain 侧塔层 i 包装
  （aq13 wrap1 (b) 段探针成型件；编排者按台账续828 裁决落库，定理体逐字取自
  `probe_chainTower-wrap1.lean`）。

  · `rtransStateComp`：状态复合（定义级，`iterate_succ_apply'` 一步）。
  · `sListEqSpineOfMarked`：**hs 槽供给件**——chain `markedList` + `¬final_list` ⇒
    `sList = sListSpine`。两表仅差 `lm`（minNum/epsilon）与 `lMSpine`（sInf），
    非空集上相等，经公开件 `hypMLmChain`（ChainMarkedTranslate）与 `hypMLm`
    （TameList12）过 `hypM` 传递即得。使 `ncvibwuV0FullChain` / `qcdvkeaV0` /
    `ncvibwuV0MemChain` 的 hs 槽对一切「有 marked + ¬final」的调用方可消。
  · `ncvibwuTowerI`：HOL NCVIBWU.hl:1463 的 chain 逐字通用 i 形（零载体槽）。
  · `qcdvkeaTowerI`：HOL QCDVKEA.hl:64 的 chain 逐字通用 i 形（零载体槽）。

  塔层 chain markedList 由 `AqiunppSlot` 的状态 i 实例直供（零桥）；`hunL` 自
  `isRestrictedAllUniq`（chain markedList 首合取 IsRestricted）导出。
  ⇒ chain 塔两件的前提集 = HOL 原文前提集（TAV2 ↦ AqiunppSlot）。

  只读消费（既有文件零触碰）。纪律：零公理、零占位证明、零反射式判定。
-/

import Kepler.Text.TameSpine.Reduction3QcdvkeaV0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList lz rtrans ntrans ztrans ytrans transformList)

/-- 状态复合（定义级）：状态 i 的一步 = 状态 (i+1)。 -/
theorem rtransStateComp (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart)
    (x : Dart) (i : ℕ) :
    rtrans L (ntrans L N r x i) (rtrans L N r x i) x 1 = rtrans L N r x (i + 1) := by
  have hpair : (ntrans L N r x i, rtrans L N r x i)
      = (transformList L x)^[i] (N, r) := by
    rw [Prod.mk.injEq]
    exact ⟨rfl, rfl⟩
  show ((transformList L x)^[1] (ntrans L N r x i, rtrans L N r x i)).2
      = ((transformList L x)^[i + 1] (N, r)).2
  rw [hpair, Function.iterate_succ_apply' (transformList L x) i (N, r),
    Function.iterate_one]

/-- **hs 槽供给件**：chain `markedList` + `¬final_list` ⇒ `sList = sListSpine`。 -/
theorem sListEqSpineOfMarked (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (hunL : ∀ l ∈ L, l.Nodup)
    {N : List (List Dart)} {r : List Dart} {d : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r d) (hf : ¬ finalList L r) :
    Kepler.Text.ChainLists.sList L r d = sListSpine L r d := by
  have hnext : nextEl r d = fList L d := hm.2.2.2.2.2.1
  have hsc : splitConditionListSpine hL N r d :=
    Kepler.Text.ChainMarkedTranslate.markedListSplitOfMarked L hL hm hf
  have hlm : Kepler.Text.Reduction5.lm L r d = lMSpine L r d :=
    (Kepler.Text.ChainMarkedTranslate.hypMLmChain L hL hgn hunL hm hf).symm.trans
      (hypMLm L hL hgn hunL hnext hsc)
  unfold Kepler.Text.ChainLists.sList sListSpine
  rw [hlm, List.range'_eq_map_range, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.add_comm 1 i]

/-- chain 塔层 NCVIBWU（HOL NCVIBWU.hl:1463 的 chain 逐字形；零载体槽）。 -/
theorem ncvibwuTowerI (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hfI : ¬ finalList L (rtrans L N r x i))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {j : ℕ}
    (hj : j ≤ indexf w (ztrans L N r x i) f) :
    (nextEl f)^[j] w ∈ rtrans L N r x (i + 1) ∧
      indexf w ((nextEl f)^[j] w) (rtrans L N r x (i + 1)) = j := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hmI := haq hgn N r x hm i
  have hsI := sListEqSpineOfMarked L hL hgn hunL hmI hfI
  obtain ⟨hmem, hidx⟩ := ncvibwuV0FullChain L hL hgn hunL haq
    (N := ntrans L N r x i) (r := rtrans L N r x i) hmI hsI hfI hfind hw (j := j) hj
  rw [rtransStateComp L N r x i] at hmem hidx
  exact ⟨hmem, hidx⟩

/-- chain 塔层 QCDVKEA（HOL QCDVKEA.hl:64 的 chain 逐字形；零载体槽）。 -/
theorem qcdvkeaTowerI (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf2 : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) :
    indexf w (ztrans L N r x i) f ≤ indexf w (ytrans L N r x (i + 1)) f := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hmI := haq hgn N r x hm i
  have hfI : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.finalListInduct i hf2
  have hsI := sListEqSpineOfMarked L hL hgn hunL hmI hfI
  rw [← rtransStateComp L N r x i] at hf2
  have h := qcdvkeaV0 L hL hgn hunL haq
    (N := ntrans L N r x i) (r := rtrans L N r x i) hmI hsI hf2 hfind hw
  rw [rtransStateComp L N r x i] at h
  exact h

end Kepler.Text.TameSpine

-- 公理审计锚（编译即执行；预期标准三，零 sorryAx）
#print axioms Kepler.Text.TameSpine.rtransStateComp
#print axioms Kepler.Text.TameSpine.sListEqSpineOfMarked
#print axioms Kepler.Text.TameSpine.ncvibwuTowerI
#print axioms Kepler.Text.TameSpine.qcdvkeaTowerI
