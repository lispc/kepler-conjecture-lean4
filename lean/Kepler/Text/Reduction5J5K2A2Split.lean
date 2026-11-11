/-
  Kepler.Text.Reduction5J5K2A2Split — Lane A2.2（nb49）：
  AQ8 两件 uniq 的链层桥 + `zNotEqYtransV0` + `split_normal_list` 本体。

  ┌─ 归属对账（HOL）────────────────────────────────────────────────
  │ ① `z_not_eq_ytrans_v0`（HOJODCM.hl:89）→ `zNotEqYtransV0`
  │ ② `uniq_fst_split_normal_parts`（AQ8.hl:2382）→ `uniqFstSplitNormalParts`
  │ ③ `uniq_snd_split_normal_parts`（AQ8.hl:530）→ `uniqSndSplitNormalParts`
  │ ④ `final_assumption_split_normal_list`（reduction4.hl:1094）
  │    → `finalAssumptionSplitNormalList`
  └────────────────────────────────────────────────────────────────

  ┌─ 路线 ────────────────────────────────────────────────────────
  │ ②③ 的 spine 主定理已落库：
  │   `aq8w4d_uniqFstSplitNormalParts`（JcajyduAqLeaf8W4d:200）
  │   `aq8w3ae_coreSNDNodup`（JcajyduAqLeaf8W3ae:256）
  │   链层 = 三桥换元（`parts_eq_partsSpine` / `splitNormalListEqSpine` /
  │   `lyEqSpine`/`lzEqSpine`）+ `coreEqPartsHeadFst`。
  │ ① `finalAssumptionYNeZ`（`0 < transformCount` 由
  │   `transformCountNon0OfMarked` 供）。
  └────────────────────────────────────────────────────────────────
-/

import Kepler.Text.Reduction5J5K2A2Final
import Kepler.Text.TameSpine.JcajyduAqLeaf8W4d
import Kepler.Text.TameSpine.JcajyduAqLeaf8W3ae
import Kepler.Text.TameSpine.Reduction3J5CorePartsWiring
import Kepler.Text.Reduction5J5Shallow
import Kepler.Text.Reduction5J5IdxSplit
import Kepler.Text.ChainBridgeParts
import Kepler.Text.ChainSpineBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts)

/-- **HOL `HOJODCM.z_not_eq_ytrans_v0`**（HOJODCM.hl:89）：
`ztrans 0 ≠ ytrans 0`。由 `finalAssumptionYNeZ`（i=0）+ `transformCount ≠ 0` 对称收口。 -/
theorem zNotEqYtransV0 (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) :
    ztrans L N r x 0 ≠ ytrans L N r x 0 := by
  intro h
  have hk0 : 0 < transformCount L N r x :=
    Nat.pos_of_ne_zero (transformCountNon0OfMarked L hL hgn haq hm hnf)
  exact finalAssumptionYNeZ L hL hgn hres haq (transformCount L N r x) hm hnf rfl
    0 hk0 h.symm

/-- **HOL `AQ8.uniq_fst_split_normal_parts`**（AQ8.hl:2382）：
`uniq (core L (FST split))`。spine 主定理 `aq8w4d_uniqFstSplitNormalParts`
+ 三桥换元。 -/
theorem uniqFstSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) :
    (core L (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).1).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r :=
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have h := Kepler.Text.TameSpine.aq8w4d_uniqFstSplitNormalParts L hL hgn hmS hfS
  simpa only [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine,
    ← Kepler.Text.TameSpine.coreEqPartsHeadFst] using h

/-- **HOL `AQ8.uniq_snd_split_normal_parts`**（AQ8.hl:530）：
`uniq (core L (SND split))`。spine 主定理 `aq8w3ae_coreSNDNodup` + 三桥换元。 -/
theorem uniqSndSplitNormalParts (L : fgraph ℕ) (hL : GoodList L)
    (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (hres : (Kepler.Text.TameLp.hypermapOfList L hL).IsRestricted)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    (hnf : ¬ finalList L r) :
    (core L (splitNormalList L r (findFaceDarts L (Kepler.Text.Reduction5.ly L r x))
      (Kepler.Text.Reduction5.ly L r x) (prevEl r (lz L N r x))).2).Nodup := by
  have hunL : ∀ l ∈ L, l.Nodup :=
    Kepler.Text.TameSpine.isRestrictedAllUniq L hL hgn hres
  have hmS : Kepler.Text.TameSpine.MarkedListSpineFull hL N r x :=
    Kepler.Text.TameSpine.markedSpineFullOfChainAlways L hL hgn haq hm
  have hfS : ¬ Kepler.Text.TameSpine.finalListSpine L r :=
    fun h => hnf ((Kepler.Text.ChainBridge.finalList_iff_finalListSpine L r).mpr h)
  have h := Kepler.Text.TameSpine.aq8w3ae_coreSNDNodup L hL hgn hmS hfS
  simpa only [← Kepler.Text.ChainSpineBridge.lyEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL hm hnf,
    ← Kepler.Text.ChainSpineBridge.splitNormalListEqSpine,
    ← Kepler.Text.ChainBridge.parts_eq_partsSpine,
    ← Kepler.Text.TameSpine.coreEqPartsHeadFst] using h

end Kepler.Text.Reduction5

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零占位依赖项）。
A2.2 本轮交三件上游（两 uniq + zNotEq）；`finalAssumptionSplitNormalList` 本体
（HOL :1094–1275）的 `bet = []` 支仍需 `hlast`/`hhead`/`nextElLastHd` 链，
按 AGENTS §7 止损，精确卡点见 DELIVERY-nb49 §2。 -/
#print axioms Kepler.Text.Reduction5.zNotEqYtransV0
#print axioms Kepler.Text.Reduction5.uniqFstSplitNormalParts
#print axioms Kepler.Text.Reduction5.uniqSndSplitNormalParts
