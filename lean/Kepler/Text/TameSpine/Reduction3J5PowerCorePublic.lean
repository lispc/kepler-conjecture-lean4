/-
  Kepler.Text.TameSpine.Reduction3J5PowerCorePublic — tame-corr nb13：把
  `Reduction3J5PowerCore` 内的两条私有链桥（`cases2Chain` /
  `betwnZtranYtransSucConstChain`）与其共用换词件 `ztransEqSpineOfNotFinal`
  公开化，供后续消费者（`indexf_y_lt_sizel` 两怪件及其下游）直接引用。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ `cases2Chain` = HOL `Kbwpbhq.CASES2`（KBWPBHQ.hl:935）链层形；
  │ `betwnZtranYtransSucConstChain` = HOL
  │   `Kbwpbhq.betwn_ztran_ytrans_suc_const`（KBWPBHQ.hl:623）链层形；
  │ 两者证体 = spine 件 + `transformCountEqSpineOfAq` / `indexf_eq_spine` /
  │ `ztrans`/`ytrans` 换词。原私有副本仍在 `Reduction3J5PowerCore` 内
  │ （不改既有文件）；本文件是其公开形，后续消费者用本文件即可。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5PowerCore
import Kepler.Text.TameSpine.Reduction3KbwpbhqCases2
import Kepler.Text.TameSpine.Reduction3KbwpbhqBetwn
import Kepler.Text.TameSpine.Reduction3PnxvwfsChain
import Kepler.Text.TameSpine.Reduction3ChainFinalBridge
import Kepler.Text.Reduction3Thm6B
import Kepler.Text.Reduction4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList core rtrans ntrans ytrans ztrans
  transformCount indexf)

/-- 链层 `transform_count = k > 0` ⇒ 初始状态非 final（HOL `transform_count_not`@0）。 -/
private theorem notFinalOfTransformCountPosPub (L : fgraph ℕ) {N : List (List Dart)}
    {r : List Dart} {x : Dart} {k : ℕ}
    (hk : transformCount L N r x = k) (hk0 : 0 < k) : ¬ finalList L r := by
  have h0 : ¬ finalList L (rtrans L N r x 0) :=
    Kepler.Text.Reduction4.transformCount_not 0 (by rw [hk]; omega)
  rw [Kepler.Text.Reduction5.rtrans_zero] at h0
  exact h0

/-- 链层第 i 状态非 final ⇒ `ztrans i` 与 spine 形相等（公开形；
`ytrans` 的同款桥在 `Reduction3PnxvwfsChain.ytransEqSpineOfNotFinal`）。 -/
theorem ztransEqSpineOfNotFinal (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hfi : ¬ finalList L (rtrans L N r x i)) :
    ztrans L N r x i = ztransSpine L N r x i := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  show Kepler.Text.Reduction5.lz L (Kepler.Text.Reduction5.ntrans L N r x i)
      (Kepler.Text.Reduction5.rtrans L N r x i) x
    = lZSpine L (ntransSpine L N r x i) (rtransSpine L N r x i) x
  rw [Kepler.Text.ChainSpineBridge.lzEqSpine L hL hgn hunL
      (haq hgn N r x hm i) hfi,
    Kepler.Text.ChainSpineBridge.ntransEqSpine L hL hgn hunL haq hm i,
    Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm i]

/-- **链桥（公开形）：HOL `Kbwpbhq.CASES2`**（KBWPBHQ.hl:935）。 -/
theorem cases2Chain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) w f) :
    (nextEl r)^[n] (ztrans L N r x (k - 1))
      = (nextEl f)^[n] (ztrans L N r x (k - 1)) := by
  have hf : ¬ finalList L r := notFinalOfTransformCountPosPub L hk hk0
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hta : transformAssumptionSpine L hL :=
    Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
  have hmS : MarkedListSpineFull hL N r x :=
    markedSpineFullOfChainAlways L hL hgn haq hm
  have htc : transformCountSpine L N r x = k := by
    rw [← transformCountEqSpineOfAq L hL hgn haq hm hf, hk]
  have hfi : ¬ finalList L (rtrans L N r x (k - 1)) :=
    Kepler.Text.Reduction4.transformCount_not (k - 1) (by rw [hk]; omega)
  have hzEq : ztrans L N r x (k - 1) = ztransSpine L N r x (k - 1) :=
    ztransEqSpineOfNotFinal L hL hgn haq hm (k - 1) hfi
  have hn' : n ≤ Kepler.Text.TameSpine.indexf
      (Kepler.Text.TameSpine.ztransSpine L N r x (k - 1)) w f := by
    rw [← hzEq, ← Kepler.Text.Reduction3.indexf_eq_spine]
    exact hn
  have h := cases2Spine L hL hta hgn hunL hmS hfind hw hk0 htc hn'
  rwa [← hzEq] at h

/-- **链桥（公开形）：HOL `Kbwpbhq.betwn_ztran_ytrans_suc_const`**
（KBWPBHQ.hl:623）。 -/
theorem betwnZtranYtransSucConstChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (i : ℕ)
    (hf : ¬ finalList L (rtrans L N r x (i + 1)))
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f) (hw : nextEl f x = w)
    {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x i) (ytrans L N r x (i + 1)) f) :
    (nextEl r)^[n] (ztrans L N r x i) = (nextEl f)^[n] (ztrans L N r x i) := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hta : transformAssumptionSpine L hL :=
    Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
  have hmS : MarkedListSpineFull hL N r x :=
    markedSpineFullOfChainAlways L hL hgn haq hm
  have hfi : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction5.finalListInduct i hf
  have hzEq : ztrans L N r x i = ztransSpine L N r x i :=
    ztransEqSpineOfNotFinal L hL hgn haq hm i hfi
  have hyEq : ytrans L N r x (i + 1) = ytransSpine L N r x (i + 1) :=
    ytransEqSpineOfNotFinal L hL hgn haq hm (i + 1) hf
  have hfSpine : ¬ finalListSpine L (rtransSpine L N r x (i + 1)) := by
    rw [← Kepler.Text.ChainSpineBridge.rtransEqSpine L hL hgn hunL haq hm (i + 1)]
    exact hf
  have hn' : n ≤ Kepler.Text.TameSpine.indexf
      (Kepler.Text.TameSpine.ztransSpine L N r x i)
      (Kepler.Text.TameSpine.ytransSpine L N r x (i + 1)) f := by
    rw [← hzEq, ← hyEq, ← Kepler.Text.Reduction3.indexf_eq_spine]
    exact hn
  have h := betwnZtranYtransSucConstSpine L hL hta hgn hunL hmS i hfSpine hfind hw hn'
  rwa [← hzEq] at h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.ztransEqSpineOfNotFinal
#print axioms Kepler.Text.TameSpine.cases2Chain
#print axioms Kepler.Text.TameSpine.betwnZtranYtransSucConstChain
