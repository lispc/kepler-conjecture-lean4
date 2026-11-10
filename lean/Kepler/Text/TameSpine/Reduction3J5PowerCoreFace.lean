/-
  Kepler.Text.TameSpine.Reduction3J5PowerCoreFace — tame-corr nb13：J5-5 族第五件
  `next_power_core_w_face`（more_lemma2.hl:2098）的链层形 + 其前置链桥
  `indexfConstLe`（PBFLHET.hl:409 的链层形）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ :2098 `next_power_core_w_face` → `nextPowerCoreWFace`：
  │   `good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ∧
  │    n ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) f ∧ find_face L x = f ∧ next_el f x = w
  │    ⇒ (next_el (core L r) POWER n) (FST w) = FST ((next_el f POWER n) w)`
  │   （与 `next_power_core_w` 的差异：上界用 f 而非 r，右端 iterate 用 f 而非 r。）
  │ 前置 `indexf_const_le_indexf_ytrans`（PBFLHET.hl:409，v0 形）：
  │   `MEM d r ∧ indexf w d r ≤ Kepler.Text.Reduction5.indexf w (ytrans 0) r ⇒ indexf w d r = indexf w d f`。
  └────────────────────────────────────────────────────────────────

  路线（HOL 同构）：`indexfConstLe` 于 d := ytrans 0 得
  `indexf w y r = indexf w y f`，把上界从 f 换到 r；再用族件 2
  （`nextPowerCoreW`）与 `nextElPowerTransEqFv0` 把右端 r-iterate 换成 f-iterate。
  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5PowerCore
import Kepler.Text.TameSpine.Reduction3Pbflhet1
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5TwelveT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart finalList core ytrans transformCount indexf)

/-- **链桥：HOL `Pbflhet.indexf_const_le_indexf_ytrans`**（PBFLHET.hl:409）链层
v0 形：`MEM d r ∧ indexf w d r ≤ Kepler.Text.Reduction5.indexf w (ytrans 0) r ⇒ indexf w d r = indexf w d f`。
证 = spine 件 `indexfConstLeIndexfYtransSpine`@0 + `ytrans` 换词 + `indexf_eq_spine`。 -/
theorem indexfConstLeIndexfYtransChain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {d : Dart} (hd : d ∈ r)
    (hle : Kepler.Text.Reduction5.indexf w d r
      ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r) :
    Kepler.Text.Reduction5.indexf w d r = Kepler.Text.Reduction5.indexf w d f := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hta : transformAssumptionSpine L hL :=
    Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
  have hmS : MarkedListSpineFull hL N r x :=
    markedSpineFullOfChainAlways L hL hgn haq hm
  have hys : ytrans L N r x 0 = ytransSpine L N r x 0 :=
    ytransEqSpineOfNotFinal L hL hgn haq hm 0 (by
      show ¬ finalList L r
      exact hf)
  have hdS : d ∈ rtransSpine L N r x 0 := by
    show d ∈ r
    exact hd
  have hleS' : Kepler.Text.Reduction5.indexf w d (rtransSpine L N r x 0)
      ≤ Kepler.Text.Reduction5.indexf w (ytransSpine L N r x 0)
        (rtransSpine L N r x 0) := by
    rw [← hys]
    show Kepler.Text.Reduction5.indexf w d r
      ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r
    exact hle
  have hleS : Kepler.Text.TameSpine.indexf w d (rtransSpine L N r x 0)
      ≤ Kepler.Text.TameSpine.indexf w (ytransSpine L N r x 0)
        (rtransSpine L N r x 0) := by
    simpa only [Kepler.Text.Reduction3.indexf_eq_spine] using hleS'
  have hS := indexfConstLeIndexfYtransSpine L hL hta hgn hmS 0 (by
    show ¬ finalListSpine L r
    exact hf) hfind hw hdS hleS
  show Kepler.Text.Reduction5.indexf w d (rtransSpine L N r x 0)
    = Kepler.Text.Reduction5.indexf w d f
  simpa only [← Kepler.Text.Reduction3.indexf_eq_spine] using hS

/-- **HOL `More_lemma2.next_power_core_w_face`**（more_lemma2.hl:2098-2119）：
`good_list ∧ good_list_nodes ∧ marked_list L N r x ∧ ¬final_list L r ∧
  n ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) f ∧ find_face L x = f ∧ next_el f x = w
  ⇒ (next_el (core L r) POWER n) (FST w) = FST ((next_el f POWER n) w)`。 -/
theorem nextPowerCoreWFace (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {n : ℕ}
    (hn : n ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) f) :
    (nextEl (core L r))^[n] w.1 = ((nextEl f)^[n] w).1 := by
  have hyr : ytrans L N r x 0 ∈ r :=
    Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm hf
  have hyEq : Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r
      = Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) f :=
    indexfConstLeIndexfYtransChain L hL hgn haq hm hf hfind hw hyr (Nat.le_refl _)
  have hn' : n ≤ Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := by
    rw [hyEq]
    exact hn
  have hcore := nextPowerCoreW L hL hgn haq hm hf hfind hw hn'
  have hpow : (nextEl r)^[n] w = (nextEl f)^[n] w := by
    have h := Kepler.Text.Reduction5.nextElPowerTransEqFv0 hL hgn haq hm hf
      (by rw [hfind]; exact hw) hn'
    rwa [hfind] at h
  rw [← hpow]
  exact hcore


/-- **链桥：HOL `Kbwpbhq.next_el_const_le_indexf_y0`**（KBWPBHQ.hl:441）链层形
（`npm` 记档：HOL 证体在怪物 `indexf_y_lt_sizel` 的原子子集步处消费）：
`¬final r ∧ d ∈ r ∧ indexf w d r < indexf w (ytrans 0) r ⇒ nextEl r d = fList L d`。 -/
theorem nextElConstLeIndexfY0Chain (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {d : Dart} (hd : d ∈ r)
    (hlt : Kepler.Text.Reduction5.indexf w d r
      < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r) :
    nextEl r d = fList L d := by
  have hunL : ∀ l ∈ L, l.Nodup := isRestrictedAllUniq L hL hgn hm.1
  have hta : transformAssumptionSpine L hL :=
    Kepler.Text.Reduction5.transformAssumptionSpineOfAqiunpp L hL haq
  have hmS : MarkedListSpineFull hL N r x :=
    markedSpineFullOfChainAlways L hL hgn haq hm
  have ht0 : transformCount L N r x ≠ 0 :=
    Kepler.Text.Reduction5.transformCountNon0OfMarked L hL hgn haq hm hf
  have htc : 0 < transformCountSpine L N r x := by
    rw [← transformCountEqSpineOfAq L hL hgn haq hm hf]
    exact Nat.pos_of_ne_zero ht0
  have hys : ytrans L N r x 0 = ytransSpine L N r x 0 :=
    ytransEqSpineOfNotFinal L hL hgn haq hm 0 (by
      show ¬ finalList L r
      exact hf)
  have hdS : d ∈ rtransSpine L N r x 0 := by
    show d ∈ r
    exact hd
  have hltR : Kepler.Text.Reduction5.indexf w d (rtransSpine L N r x 0)
      < Kepler.Text.Reduction5.indexf w (ytransSpine L N r x 0)
        (rtransSpine L N r x 0) := by
    rw [← hys]
    show Kepler.Text.Reduction5.indexf w d r
      < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r
    exact hlt
  have hltS : Kepler.Text.TameSpine.indexf w d (rtransSpine L N r x 0)
      < Kepler.Text.TameSpine.indexf w (ytransSpine L N r x 0)
        (rtransSpine L N r x 0) := by
    simpa only [Kepler.Text.Reduction3.indexf_eq_spine] using hltR
  exact nextElConstLeIndexfY0Spine L hL hta hgn hmS hfind hw htc hdS hltS

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三 [propext, Classical.choice,
Quot.sound]，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfConstLeIndexfYtransChain
#print axioms Kepler.Text.TameSpine.nextElConstLeIndexfY0Chain
#print axioms Kepler.Text.TameSpine.nextPowerCoreWFace
