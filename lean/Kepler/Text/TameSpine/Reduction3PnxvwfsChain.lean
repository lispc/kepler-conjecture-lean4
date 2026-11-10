/-
  Kepler.Text.TameSpine.Reduction3PnxvwfsChain — tame-corr nb8：任务 4
  跨世界桥核实结论的落地件：两枚通用桥助件 + PNXVWFS1 的链世界形
  `pnxvwfs1Chain`（aq13 F3 `hpnx1` 槽形）。

  ┌─ 桥核实结论（本轮实测）───────────────────────────────────────
  │ 载体级桥全部现成：`rtransEqSpine` / `ntransEqSpine`
  │ （ChainSpineBridge:152/160，经 transformIterEqSpine）、`lyEqSpine`
  │ （ChainSpineBridge:88）、`lzEqSpine`（:99）、
  │ `finalList_iff_finalListSpine`（ChainBridge/Reduction3DefsAssumptionInst:106，
  │ = Iff.rfl）、`markedList_iff_markedListSpineFull`
  │ （ChainBridgeParts:230，带 hs 槽）、`sListEqSpineOfMarked`
  │ （Reduction3ChainTower:50，chain marked + ¬final@0 供 hs）、
  │ `finalListInduct1Spine`（nb2，下传 ¬final@0）。
  │ **假设级桥不存在**：spine 件吃 `transformAssumptionSpine L hL`
  │ （HOL transform_assumption_v2 陈述形），链侧上游只有
  │ `AqiunppSlot L hL`（Reduction4Subseg9:64，AQIUNPP 结论形），
  │ 库内零互推件（全树 grep 实测：同时提及两者的仅 QcdvkeaTower 头注）。
  │ 故链世界形携带**双 TAV2 槽**（haq + hta）：`hta` 即 HOL 原文的
  │ transform_assumption_v2 前提本身，库内由 `transformAssumptionOfAq`
  │ （JcajyduAqTowerBase:329，13 个 aqNConcl 叶）供给，非新增债。
  │ aq13 F3（599ab6ea）消 `hpnx1` 槽需在其前提中加入 `hta`（或先落
  │ haq→hta 桥——final 态下链侧 `minNum ∅` 与 spine 侧 `sInf ∅` 的
  │ junk 值不同，非顺手件）。
  └────────────────────────────────────────────────────────────────

  ┌─ 归属对账─────────────────────────────────────────────────────
  │ ① `markedSpineFullOfChain`（桥助件）：chain marked + ¬final@i ⇒
  │    spine `MarkedListSpineFull` ∧ spine 形 ¬final@i。证 = rtransEqSpine
  │    → finalListInduct1Spine 下传 ¬final@0 → sListEqSpineOfMarked 供 hs
  │    → markedList_iff_markedListSpineFull。
  │ ② `ytransEqSpineOfNotFinal`（桥助件）：chain marked + ¬final@i ⇒
  │    `ytrans i = ytransSpine i`。证 = lyEqSpine@(i)（haq 供塔层 marked）
  │    + rtransEqSpine。
  │ ③ `pnxvwfs1Chain`（HOL `Pnxvwfs.PNXVWFS1`，PNXVWFS.hl:120-157 的链
  │    世界逐字形）：`markedList L N r x ∧ ¬final (rtrans i) ⇒
  │    MEM (ytrans i) r`。证 = ① + ② + pnxvwfs1Spine（nb7）。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）───────────────────────────────────────────
  │ 双载体桥接件（chain `markedList`/`rtrans`/`ytrans`/`ly`/`finalList`
  │ ↔ spine `MarkedListSpineFull`/`rtransSpine`/`lYSpine`/`finalListSpine`），
  │ 消费件同上桥件 + pnxvwfs1Spine（nb7）+ finalListInduct1Spine（nb2）；
  │ 零 Dart-default 载体件（Dart := ℕ × ℕ abbrev，桥两侧同实例）。
  │ 默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Pnxvwfs
import Kepler.Text.TameSpine.Reduction3ChainTower
import Kepler.Text.ChainSpineBridge
import Kepler.Text.ChainBridgeParts

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList rtrans ntrans ytrans ztrans)

/-- **桥助件**：chain `markedList` + `¬final (rtrans i)` ⇒ spine
`MarkedListSpineFull` ∧ spine 形 `¬final (rtransSpine i)`。
证 = rtransEqSpine 换 r 形 → finalListInduct1Spine 下传 ¬final@0
（rtrans 0 ≡ r 定义级）→ sListEqSpineOfMarked 供 hs →
markedList_iff_markedListSpineFull。 -/
theorem markedSpineFullOfChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    MarkedListSpineFull hL N r x
      ∧ ¬ finalListSpine L (rtransSpine L N r x i) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hrt : rtrans L N r x i = rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
  have hfS : ¬ finalListSpine L (rtransSpine L N r x i) := by
    rw [← hrt]
    exact hf
  have hf0S : ¬ finalListSpine L (rtransSpine L N r x 0) :=
    finalListInduct1Spine L N r x i hfS 0 (Nat.zero_le i)
  rw [show rtransSpine L N r x 0 = r from rfl] at hf0S
  have hs := sListEqSpineOfMarked L hL hgn hunL hm hf0S
  exact ⟨(Kepler.Text.ChainBridge.markedList_iff_markedListSpineFull L hL N r x
    hs).mp hm, hfS⟩

/-- **桥助件**：chain `markedList` + `¬final (rtrans i)` ⇒
`ytrans i = ytransSpine i`。证 = lyEqSpine@(i)（haq 供塔层 marked）+
rtransEqSpine。 -/
theorem ytransEqSpineOfNotFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ytrans L N r x i = ytransSpine L N r x i := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hrt : rtrans L N r x i = rtransSpine L N r x i :=
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i
  have hly : Kepler.Text.Reduction5.ly L (rtrans L N r x i) x
      = lYSpine L (rtrans L N r x i) x :=
    Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL (haq hgn N r x hm i) hf
  show Kepler.Text.Reduction5.ly L (rtrans L N r x i) x
      = lYSpine L (rtransSpine L N r x i) x
  rw [hly, hrt]

/-- **HOL `Pnxvwfs.PNXVWFS1`**（PNXVWFS.hl:120-157）链世界逐字形：
`markedList L N r x ∧ ¬final (rtrans i) ⇒ MEM (ytrans i) r`。
双 TAV2 槽：`haq`（链侧 AQIUNPP 结论形，Reduction4Subseg9:64）+
`hta`（spine TAV2，即 HOL transform_assumption_v2 陈述形本身）。
证 = 两枚桥助件 + pnxvwfs1Spine（nb7）。 -/
theorem pnxvwfs1Chain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hta : transformAssumptionSpine L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x i)) :
    ytrans L N r x i ∈ r := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  obtain ⟨hmS, hfS⟩ := markedSpineFullOfChain L hL hgn haq hm i hf
  rw [ytransEqSpineOfNotFinal L hL hgn haq hm i hf]
  exact pnxvwfs1Spine L hL hta hgn hunL hmS i hfS

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.markedSpineFullOfChain
#print axioms Kepler.Text.TameSpine.ytransEqSpineOfNotFinal
#print axioms Kepler.Text.TameSpine.pnxvwfs1Chain
