/-
  Kepler.Text.TameSpine.Reduction3J5SingletonAtomSubset — tame-corr nb16：双怪件
  第②段组装 `singletonAtomSubset`（HOL more_lemma2:470-:607 的子集步）。

  ┌─ 归属对账 ─────────────────────────────────────────────────────
  │ HOL：`{p | ∃d, p=[d] ∧ d ∈ r ∧ indexf w d r < q} ⊆ set_of_list (parts L r)`。
  │ Lean：`∀ d ∈ r, indexf w d r < q → [d] ∈ parts L r`（q = indexf w (ytrans 0) r）。
  │ 路线：`hlast` = `nextElConstLeIndexfY0Chain`（nb13 绿）+ `edgeNondegFXorNi`
  │ 反证；`hhead` 的 d=w 支用 marked 合取 6 + 边非退化@x，d≠w 支用
  │ `indexfPrevSucc`（nb16 绿）把 pd 的 indexf 拉到 q 以下再走同一件；
  │ `memPartsSingleton`（nb14 绿）收口。
  └────────────────────────────────────────────────────────────────

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfPrevSucc
import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelAtom
import Kepler.Text.TameSpine.Reduction3J5PowerCoreFace
import Kepler.Text.TameSpine.TameList8
import Kepler.Text.MoreLemma2a23
import Kepler.Text.MoreLemma2Naming
import Kepler.Text.MoreLemma2Island3
import Kepler.Text.Reduction5BetwnBase

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts eList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart parts finalList ytrans indexf)

/-- **双怪件第②段**：`indexf w d r < indexf w (ytrans 0) r` 的 dart 都是
单点 atom。 -/
theorem singletonAtomSubset (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x) (hf : ¬ finalList L r)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {d : Dart} (hd : d ∈ r)
    (hlt : Kepler.Text.Reduction5.indexf w d r
      < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r) :
    [d] ∈ parts L r := by
  have hnd : r.Nodup := (List.nodup_flatten.mp hm.2.1.1).1 r hm.2.2.1
  have hloop := hm.2.1.2.2.2.1 r hm.2.2.1
  have hdarts : ∀ e ∈ r, e ∈ listOfDarts L := fun e he => (hloop e he).1
  have hxr : x ∈ r := hm.2.2.2.1
  have hwx : w = nextEl r x := by
    rw [← hw, ← hfind]
    exact hm.2.2.2.2.2.1.symm
  have hwr : w ∈ r := by
    rw [hwx]
    exact Kepler.Text.TameLp.nextEl_mem_of_mem hxr
  have hnextd := nextElConstLeIndexfY0Chain L hL hgn haq hm hf hfind hw hd hlt
  have hlast : d = r.getLast! ∨ nextEl r d ≠ fList L (eList d) :=
    Or.inr (by
      rw [hnextd]
      exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hm.1.edgeNondegenerate (hdarts d hd))
  have hhead : d = r.head!
      ∨ nextEl r (Kepler.Assembly.prevEl r d)
        ≠ fList L (eList (Kepler.Assembly.prevEl r d)) := by
    by_cases hdw : d = w
    · -- d = w：用 x 的边非退化
      have hprevw : Kepler.Assembly.prevEl r w = x := by
        rw [hwx]
        exact Kepler.Text.TameLp.prevEl_nextEl hnd hxr
      refine Or.inr ?_
      rw [hdw, hprevw, hm.2.2.2.2.2.1]
      exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hm.1.edgeNondegenerate (hdarts x hxr)
    · -- d ≠ w：pd = prevEl r d，indexfPrevSucc 拉到 q 以下
      have hpd : Kepler.Assembly.prevEl r d ∈ r :=
        Kepler.Text.TameLp.prevEl_mem_of_mem hd
      have hnextpd : nextEl r (Kepler.Assembly.prevEl r d) = d :=
        Kepler.Text.TameLp.nextEl_prevEl hnd hd
      have hyr : ytrans L N r x 0 ∈ r :=
        Kepler.Text.MoreLemma2Naming.ytransMemRtrans L hL hm hf
      have hqlt : Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r < r.length :=
        Kepler.Text.Reduction5.indexfLtSizel hwr hyr
      have hltlen : Kepler.Text.Reduction5.indexf w d r < r.length :=
        Nat.lt_trans hlt hqlt
      have hltpd : Kepler.Text.Reduction5.indexf w (Kepler.Assembly.prevEl r d) r
          < Kepler.Text.Reduction5.indexf w (ytrans L N r x 0) r := by
        have h := indexfPrevSucc hwr hpd hnd (fun hc => hdw hc.symm) hnextpd hltlen
        omega
      have hnextpd' := nextElConstLeIndexfY0Chain L hL hgn haq hm hf hfind hw hpd hltpd
      refine Or.inr ?_
      rw [hnextpd']
      exact Kepler.Text.MoreLemma2Island3.edgeNondegFXorNi L hL hm.1.edgeNondegenerate (hdarts (Kepler.Assembly.prevEl r d) hpd)
  exact memPartsSingleton L hnd hd hhead hlast

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.singletonAtomSubset
