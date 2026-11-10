/-
  Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelPreCount — tame-corr nb20：
  `indexf_y_lt_sizel_pre`（more_lemma2:890）计数段的**核心恒等式**：
  `indexf zk x f + 1 = indexf zk (next_el f x) f`
  （`indexfPrevSucc` 在 f 上的实例化；`zk = ztrans (k-1)`）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelPreSetup
import Kepler.Text.TameSpine.Reduction3J5IndexfPrevSucc
import Kepler.Text.TameSpine.TameList8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl fList findFaceDarts listOfDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart ztrans transformCount indexf)

/-- **`_pre` 计数核心**：`zk = ztrans (k-1)` 时
`indexf zk x f + 1 = indexf zk (nextEl f x) f`（`f = find_face L x`）。 -/
theorem preIndexfZkXSucc (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k)
    {f : List Dart} (hfind : findFaceDarts L x = f)
    (hne : ztrans L N r x (k - 1) ≠ nextEl f x)
    (hlt : Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) (nextEl f x) f
      < f.length) :
    Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) x f + 1
      = Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) (nextEl f x) f := by
  have hzkf : ztrans L N r x (k - 1) ∈ f := by
    rw [← hfind]
    exact preZkMemF L hL hgn haq hm hk hk0
  have hxf : x ∈ f := by
    rw [← hfind]
    exact (Kepler.Text.TameLp.dart_in_face L x).mpr
      (Kepler.Text.MoreLemma2a23.markedListOfDart L hL hm)
  have hfnd : f.Nodup := by
    rw [← hfind]
    exact Kepler.Text.TameLp.findFaceDarts_nodup hL.1 x
  exact indexfPrevSucc (r := f) (w := ztrans L N r x (k - 1)) (pd := x)
    (d := nextEl f x) hzkf hxf hfnd hne rfl hlt

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.preIndexfZkXSucc
