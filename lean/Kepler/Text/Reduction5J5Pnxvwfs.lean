/-
  Kepler.Text.Reduction5J5Pnxvwfs — J5-2 首段（chain 载体）：
  `Pnxvwfs.PNXVWFS1` / `PNXVWFS2`（PNXVWFS.hl:120 / :160）的链层形，以及吃它们的两件
  K1 浅段件 `final_assumption_fsty_core`（reduction4.hl:587）与
  `final_assumption_fstz_core`（:611）——均为 HOL 原文形，无额外槽。

  ┌─ 归属对账（HOL Light Flyspeck）───────────────────────────────────
  │ PNXVWFS.hl:120 `PNXVWFS1` → `pnxvwfs1`：
  │   transform_assumption_v2 L ∧ good_list ∧ good_list_nodes ∧
  │   ¬final_list L (rtrans L N r x i) ∧ marked_list L N r x ⇒ MEM (ytrans L N r x i) r
  │ PNXVWFS.hl:160 `PNXVWFS2` → `pnxvwfs2`：同上，ytrans 换 ztrans
  │ reduction4.hl:587 `final_assumption_fsty_core`（24L）→ `finalAssumptionFstyCore`：
  │   good_list ∧ good_list_nodes ∧ is_restricted ∧ newvertex_prepped ∧ marked_list ∧
  │   ¬final_list ∧ transform_count L N r x = k ⇒
  │   (∀ i. i < k ⇒ MEM (FST (ytrans L N r x i)) (core L r))
  │ reduction4.hl:611 `final_assumption_fstz_core`（24L）→ `finalAssumptionFstzCore`：
  │   同前件 ⇒ (∀ i. i < k ⇒ MEM (FST (ztrans L N r x i)) (core L r))
  │ `transform_assumption_v2 L` ↦ `AqiunppSlot`（同 Reduction3ChainTower 口径）。
  └────────────────────────────────────────────────────────────────

  ┌─ 上游与桥 ────────────────────────────────────────────────────────
  │ PNXVWFS 两件的 spine 形 `pnxvwfs1Spine` / `pnxvwfs2Spine` 由 tame-corr 于
  │ `861dc12d` 落库（TameSpine/Reduction3Pnxvwfs，标准三），带 spine 塔族单槽
  │ `hta : transformAssumptionSpine L hL`。本文件的链层形 = spine 件 + 桥：
  │ · `hta` ← `transformAssumptionSpineOfAqiunpp`（Reduction5J5Tav2Bridge，由 `haq` 供）；
  │ · marked_list：`markedList_iff_markedListSpineFull`，`sList` 槽 ←
  │   `sListEqSpineOfMarked`（需 ¬final_list L r；由 ¬final_list L (rtrans i) 经
  │   `finalListInduct` 逐步降到状态 0 得）；
  │ · `rtransEqSpine` / `ntransEqSpine` 把链侧第 i 状态换成 spine 侧第 i 状态；
  │ · `lyEqSpine` / `lzEqSpine`（于状态 i，chain marked 由 `haq` 供）把 l'y / l'z 换成
  │   spine 形，即 ytrans i = ytransSpine i、ztrans i = ztransSpine i。
  │ 公开陈述零 spine 谓词，spine 只出现在证体内（同 ChainMarkedTranslate /
  │ Reduction5J5SplitNorm 路线）。
  │ 两件浅段件与 HOL 证体同路线：`final_assumption_mem_fst_core` + PNXVWFS1 / 2 +
  │ `transform_count_not`。
  └────────────────────────────────────────────────────────────────

  ┌─ 对在库槽版件的影响 ──────────────────────────────────────────────
  │ `finalAssumptionsNotNextCore0IOfSlots`（Reduction5J5NotNextCore）的槽 ① `hpnx1`
  │ 现在可由本文件消：`fun i hnfi => pnxvwfs1 L hL hgn haq i hnfi hm`。
  │ 该件的槽 ②（KBWPBHQ1）不受影响，仍缺上游。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零改动；既有文件零触碰。
-/

import Kepler.Text.Reduction5J5Tav2Bridge
import Kepler.Text.TameSpine.Reduction3Pnxvwfs
import Kepler.Text.Reduction5Qcdvkea
import Kepler.Text.Reduction3DefsNewVertex
import Kepler.Text.Reduction4
import Kepler.Text.Reduction4Subseg4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)
open Kepler.Text.TameSpine (ntransSpine rtransSpine ytransSpine ztransSpine finalListSpine
  MarkedListSpineFull lYSpine lZSpine)

/-- 第 i 状态非 final ⇒ 初始状态非 final（`finalListInduct` 逐步下降；私有支件）。 -/
private theorem notFinalBase (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) :
    ∀ i, ¬ finalList L (rtrans L N r x i) → ¬ finalList L r
  | 0, h => h
  | i + 1, h => notFinalBase L N r x i (finalListInduct i h)

/-- chain marked + 第 i 状态非 final ⇒ spine 侧的全套入参（私有打包件）：
`all uniq L`、spine marked、spine TAV2、状态 i 的迭代等式与 spine 侧非 final。 -/
private theorem spineInputs (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hnfi : ¬ finalList L (rtrans L N r x i)) (hm : markedList L hL N r x) :
    (∀ l ∈ L, l.Nodup) ∧ MarkedListSpineFull hL N r x ∧
      ntrans L N r x i = ntransSpine L N r x i ∧
      rtrans L N r x i = rtransSpine L N r x i ∧
      ¬ finalListSpine L (rtransSpine L N r x i) := by
  have hunL : ∀ l ∈ L, l.Nodup := Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hm.1
  have hf : ¬ finalList L r := notFinalBase L N r x i hnfi
  have hs := Kepler.Text.TameSpine.sListEqSpineOfMarked L hL hgn hunL hm hf
  have hrt : rtrans L N r x i = rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
  refine ⟨hunL,
    (Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x hs).mp hm,
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i, hrt, ?_⟩
  rw [← hrt]
  exact fun h => hnfi ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L _).mpr h)

/-- **HOL `Pnxvwfs.PNXVWFS1`**（PNXVWFS.hl:120）：第 i 状态非 final 时，ytrans i 仍在
初始环 r 上。 -/
theorem pnxvwfs1 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hnfi : ¬ finalList L (rtrans L N r x i)) (hm : markedList L hL N r x) :
    ytrans L N r x i ∈ r := by
  obtain ⟨hunL, hmS, -, hrt, hfS⟩ := spineInputs L hL hgn haq i hnfi hm
  have h := Kepler.Text.TameSpine.pnxvwfs1Spine L hL
    (transformAssumptionSpineOfAqiunpp L hL haq) hgn hunL hmS i hfS
  -- ytrans i = ytransSpine i
  have hly : Kepler.Text.Reduction5.ly L (rtrans L N r x i) x = lYSpine L (rtrans L N r x i) x :=
    Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL (haq hgn N r x hm i) hnfi
  have hy : ytrans L N r x i = ytransSpine L N r x i := by
    show Kepler.Text.Reduction5.ly L (rtrans L N r x i) x = lYSpine L (rtransSpine L N r x i) x
    rw [hly, hrt]
  rw [hy]
  exact h

/-- **HOL `Pnxvwfs.PNXVWFS2`**（PNXVWFS.hl:160）：第 i 状态非 final 时，ztrans i 仍在
初始环 r 上。 -/
theorem pnxvwfs2 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (i : ℕ)
    (hnfi : ¬ finalList L (rtrans L N r x i)) (hm : markedList L hL N r x) :
    ztrans L N r x i ∈ r := by
  obtain ⟨hunL, hmS, hnt, hrt, hfS⟩ := spineInputs L hL hgn haq i hnfi hm
  have h := Kepler.Text.TameSpine.pnxvwfs2Spine L hL
    (transformAssumptionSpineOfAqiunpp L hL haq) hgn hunL hmS i hfS
  -- ztrans i = ztransSpine i
  have hlz : lz L (ntrans L N r x i) (rtrans L N r x i) x
      = lZSpine L (ntrans L N r x i) (rtrans L N r x i) x :=
    Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL (haq hgn N r x hm i) hnfi
  have hz : ztrans L N r x i = ztransSpine L N r x i := by
    show lz L (ntrans L N r x i) (rtrans L N r x i) x
      = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
    rw [hlz, hnt, hrt]
  rw [hz]
  exact h

/-- **HOL `final_assumption_fsty_core`**（reduction4.hl:587）：i < transform_count 时
FST (ytrans i) 在 core L r 里。 -/
theorem finalAssumptionFstyCore (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    ∀ i, i < k → (ytrans L N r x i).1 ∈ core L r := by
  intro i hik
  have hnfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  exact Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm _
    (pnxvwfs1 L hL hgn haq i hnfi hm)

/-- **HOL `final_assumption_fstz_core`**（reduction4.hl:611）：i < transform_count 时
FST (ztrans i) 在 core L r 里。 -/
theorem finalAssumptionFstzCore (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart} (k : ℕ)
    (hnv : Kepler.Text.Reduction3.newvertexPrepped L N r x)
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k) :
    ∀ i, i < k → (ztrans L N r x i).1 ∈ core L r := by
  intro i hik
  have hnfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by rw [hk]; exact hik)
  exact Kepler.Text.Reduction4Idx.finalAssumptionMemFstCore L hL hm _
    (pnxvwfs2 L hL hgn haq i hnfi hm)

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.pnxvwfs1
#print axioms Kepler.Text.Reduction5.pnxvwfs2
#print axioms Kepler.Text.Reduction5.finalAssumptionFstyCore
#print axioms Kepler.Text.Reduction5.finalAssumptionFstzCore
