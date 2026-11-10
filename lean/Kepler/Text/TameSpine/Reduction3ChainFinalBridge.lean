/-
  Kepler.Text.TameSpine.Reduction3ChainFinalBridge — tame-corr nb9：任务 3
  （给 J4/aq13 装配用的无槽形传送件）。

  ┌─ 归属对账─────────────────────────────────────────────────────
  │ ① `markedSpineFullOfChainAlways`：chain `markedList` ⇒ spine
  │    `MarkedListSpineFull`，**无 ¬final 前提、无 hs 槽**。
  │    证：¬final 支 = nb8 markedSpineFullOfChain；
  │    final 支 = markedListCore_iff_markedListSpine（核心 7 合取，免 hs）
  │    + 后两合取逐支：`finalListSpine → FlagListSpine` 走链侧 h8 +
  │    flagList_iff_flagListSpine（免 hs 桥）；`¬finalListSpine →
  │    SFlagListSpine` 在 final 支真空（absurd），故 sFlagList 的 hs 槽
  │    永不触发。
  │ ② 三条 `…OfAq`：aq13 新桥 `transformAssumptionSpineOfAqiunpp`
  │    （Reduction5J5Tav2Bridge:86，AqiunppSlot → transformAssumptionSpine）
  │    代入 nb8 三条链世界形（pnxvwfs1Chain / kbwpbhq1Chain /
  │    obdatybChain）的 `hta` 槽——**单槽（haq）形**，供 J4/aq13 无槽消费。
  │    另给 `transformCountEqSpineOfAq`（transformCount 桥的单槽形）。
  │ 陈述与 nb8 各件逐字同（仅少 hta 前提）；零新数学。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）────────────────────────────────────────────
  │ 双载体桥接层（chain `markedList` ↔ spine `MarkedListSpineFull`）；
  │ 消费件：markedSpineFullOfChain（nb8）/ markedListCore_iff_markedListSpine
  │ / flagList_iff_flagListSpine（ChainBridge）/ sFlagList_iff_sFlagListSpine
  │ / transformAssumptionSpineOfAqiunpp（aq13 J5-2）/
  │ pnxvwfs1Chain、kbwpbhq1Chain、obdatybChain、transformCountEqSpine（nb8）。
  │ 零 Dart 载体件。默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3ObdatybChain
import Kepler.Text.TameSpine.Reduction3Kbwpbhq1Chain
import Kepler.Text.Reduction5J5Tav2Bridge

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList rtrans ntrans ytrans ztrans transformCount)

/-- **无槽传送件**：chain `markedList` ⇒ spine `MarkedListSpineFull`
（无 ¬final 前提、无 hs 槽）。证见文件头 ①。 -/
theorem markedSpineFullOfChainAlways (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) :
    MarkedListSpineFull hL N r x := by
  by_cases hfr : finalList L r
  · have hfin : finalListSpine L r := hfr
    have hcore : MarkedListSpine hL N r x :=
      (Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine L hL N r x).mp
        ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.1⟩
    refine ⟨hcore, ?_, ?_⟩
    · intro hf
      exact (Kepler.Text.ChainBridge.flagList_iff_flagListSpine L N).mp
        (hm.2.2.2.2.2.2.2.1 hf)
    · intro hf
      exact absurd hfin hf
  · exact (markedSpineFullOfChain L hL hgn haq hm 0 hfr).1

/-- `pnxvwfs1Chain` 的单槽（haq）形（hta 由 aq13 桥
`transformAssumptionSpineOfAqiunpp` 供给）。 -/
theorem pnxvwfs1ChainOfAq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ytrans L N r x i ∈ r :=
  pnxvwfs1Chain L hL hgn haq (Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq) hm i hf

/-- `kbwpbhq1Chain` 的单槽（haq）形。 -/
theorem kbwpbhq1ChainOfAq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {u : Dart} (hur : u ∈ r) (huf : u ∈ findFaceDarts L x) :
    (∃ i, ytrans L N r x i = u ∧ i < transformCount L N r x)
      ↔ ¬ (nextEl (Kepler.Text.ChainLists.findList N u) u = fList L u) :=
  kbwpbhq1Chain L hL hgn haq (Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq) hm hur huf

/-- `obdatybChain` 的单槽（haq）形。 -/
theorem obdatybChainOfAq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {d : Dart} (hdf : d ∈ findFaceDarts L x) (hdN : d ∈ N.flatten) :
    d ∈ r :=
  obdatybChain L hL hgn haq (Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq) hm hdf hdN

/-- `transformCountEqSpine` 的单槽（haq）形。 -/
theorem transformCountEqSpineOfAq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hf : ¬ finalList L r) :
    transformCount L N r x = transformCountSpine L N r x :=
  transformCountEqSpine L hL hgn haq (Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq)
    hm hf

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.markedSpineFullOfChainAlways
#print axioms Kepler.Text.TameSpine.pnxvwfs1ChainOfAq
#print axioms Kepler.Text.TameSpine.kbwpbhq1ChainOfAq
#print axioms Kepler.Text.TameSpine.obdatybChainOfAq
#print axioms Kepler.Text.TameSpine.transformCountEqSpineOfAq
