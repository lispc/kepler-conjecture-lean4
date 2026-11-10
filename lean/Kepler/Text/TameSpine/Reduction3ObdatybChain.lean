/-
  Kepler.Text.TameSpine.Reduction3ObdatybChain — tame-corr nb8：OBDATYB 的
  链世界形 `obdatybChain`（J4 `oldnewVertexDisjointOfObdatyb` 的 `hOb` 槽形）。

  ┌─ 归属对账─────────────────────────────────────────────────────
  │ `obdatybChain`（HOL `Obdatyb.OBDATYB`，OBDATYB.hl:113-190 的链世界
  │ 逐字形，与 J4 `hOb` 槽（Reduction1W2g:232，1185cc9a）同形）：
  │ `markedList L N r x ∧ MEM d (find_face L x) ∧ MEM d (flatten N) ⇒
  │ MEM d r`。证（按 r 是否 final 二分）：
  │ · final 支：markedListCore_iff_markedListSpine（ChainBridgeParts:210，
  │   免 hs 槽）取核 7 合取 + obdatybFinalSpine（nb8）——**零 TAV2 消费**；
  │ · ¬final 支：markedSpineFullOfChain（nb8 桥助件）+ obdatybSpine（nb8）。
  │ 双 TAV2 槽（haq + hta）口径同 `pnxvwfs1Chain`（见 Reduction3PnxvwfsChain
  │ 文件头）：HOL OBDATYB 与 oldnew_vertex_disjoint 原文均带
  │ transform_assumption_v2 前提，J4 槽版因槽内零消费而省去，消槽时须补回。
  └────────────────────────────────────────────────────────────────

  ┌─ 世界选择记账（R1）───────────────────────────────────────────
  │ 双载体桥接件（chain `markedList`/`finalList` ↔ spine `MarkedListSpine`/
  │ `MarkedListSpineFull`/`finalListSpine`）；消费件：
  │ markedListCore_iff_markedListSpine / markedSpineFullOfChain（nb8）/
  │ obdatybFinalSpine / obdatybSpine（nb8）/ isRestrictedAllUniq；
  │ 零 Dart-default 载体件。默认心跳、linter 全开。
  └────────────────────────────────────────────────────────────────

  纪律：零禁词（无公理、零占位证明、零反射式判定）；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3Obdatyb
import Kepler.Text.TameSpine.Reduction3PnxvwfsChain

set_option autoImplicit false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts fList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList rtrans)

/-- **HOL `Obdatyb.OBDATYB`**（OBDATYB.hl:113-190）链世界逐字形：
`markedList L N r x ∧ MEM d (find_face L x) ∧ MEM d (flatten N) ⇒ MEM d r`。
双 TAV2 槽（haq + hta）。证：final r 支取核 7 合取 + obdatybFinalSpine
（零 TAV2 消费）；¬final 支经桥助件 + obdatybSpine。 -/
theorem obdatybChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hta : transformAssumptionSpine L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {d : Dart} (hdf : d ∈ findFaceDarts L x) (hdN : d ∈ N.flatten) :
    d ∈ r := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  by_cases hfr : finalList L r
  · have hcore : MarkedListSpine hL N r x :=
      (Kepler.Text.ChainBridge.markedListCore_iff_markedListSpine L hL N r x).mp
        ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.1⟩
    exact obdatybFinalSpine L hL hcore hfr hdf
  · obtain ⟨hmS, -⟩ := markedSpineFullOfChain L hL hgn haq hm 0 hfr
    exact obdatybSpine L hL hta hgn hunL hmS hdf hdN

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.obdatybChain
