/-
  Kepler.Text.Reduction4K4C1 — J 战役 K4 Lane C1：K4 辅助三件。
  （reduction4.hl:3274 corei_reduction / :4507 _fy / :4600 _zx）

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction4
import Kepler.Text.Reduction5J5Termination
import Kepler.Text.Reduction5J5M2Core
import Kepler.Text.Reduction4Subseg8
import Kepler.Text.Reduction5BetwnBase
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction1W2e
import Kepler.Text.Reduction3Thm1
import Kepler.Text.ChainSpineBridge
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction4

open Kepler.Graphs (Face Graph fgraph between)
open Kepler.Assembly (GoodList findFaceDarts nextEl prevEl)
open Kepler.Text.Reduction5
  (Dart core ntrans rtrans ytrans ztrans transformCount finalList ftrans)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- HOL `corei_reduction`（reduction4.hl:3274-3313）：
`i = 0` 情形的 `next_el core` 不等式沿 `trans_add` 推广到所有 `i < k`。 -/
theorem coreiReduction
    (h0 : ∀ (L : fgraph ℕ) (hL : GoodList L) (N : List (List Dart))
      (r : List Dart) (x : Dart),
      GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted →
      markedList L hL N r x →
      ¬ finalList L r →
      between (findFaceDarts L x) (ytrans L N r x 0) (ztrans L N r x 0) = [] →
      ¬(nextEl (core L r) (ytrans L N r x 0).1 = (ztrans L N r x 0).1)) :
    ∀ (L : fgraph ℕ) (hL : GoodList L) (N : List (List Dart)) (r : List Dart)
      (x : Dart) (k : ℕ),
      GoodListNodesTl L hL →
      (hypermapOfList L hL).IsRestricted →
      markedList L hL N r x →
      ¬ finalList L r →
      transformCount L N r x = k →
      ∀ i : ℕ, i < k →
        between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
        ¬(nextEl (core L (rtrans L N r x i)) (ytrans L N r x i).1
          = (ztrans L N r x i).1) := by
  intro L hL N r x k hgn hres hm hnf hk i hi hbet
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  have hnf_i : ¬ finalList L (rtrans L N r x i) :=
    Kepler.Text.Reduction4.transformCount_not i (by omega)
  have hm_i : markedList L hL (ntrans L N r x i) (rtrans L N r x i) x :=
    haq hgn N r x hm i
  have hta := Kepler.Text.Reduction3.transAdd L N r x i 0
  rw [Nat.zero_add] at hta
  have hbet' : between (findFaceDarts L x)
      (ytrans L (ntrans L N r x i) (rtrans L N r x i) x 0)
      (ztrans L (ntrans L N r x i) (rtrans L N r x i) x 0) = [] := by
    rw [← hta.2.2.1, ← hta.2.2.2]
    exact hbet
  have h := h0 L hL (ntrans L N r x i) (rtrans L N r x i) x hgn hres hm_i hnf_i hbet'
  simpa only [Kepler.Text.Reduction5.rtrans_zero, ← hta.2.2.1, ← hta.2.2.2] using h

end Kepler.Text.Reduction4

/-! 公理审计锚（编译即执行；预期标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction4.coreiReduction
