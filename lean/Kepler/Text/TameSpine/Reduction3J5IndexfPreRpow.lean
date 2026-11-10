/-
  Kepler.Text.TameSpine.Reduction3J5IndexfPreRpow — tame-corr nb22：`_pre` f 侧子集
  换算第 1 步：f 侧幂等式转 r 侧（`cases2Chain`，界 `≤` 形）。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfPowAdd
import Kepler.Text.TameSpine.Reduction3J5PowerCorePublic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList nextEl findFaceDarts)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.Reduction5 (Dart ztrans transformCount indexf)

/-- **`_pre` 换算第 1 步**：若 `d = (next_el f)^j zk` 且 `j ≤ indexf zk w f`，
则 `d = (next_el r)^j zk`（`CASES2` 链形，`≤` 界）。 -/
theorem preRpowEq (L : fgraph ℕ) (hL : GoodList L)
    (hgn : GoodListNodesTl L hL)
    (haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    {N : List (List Dart)} {r : List Dart} {x : Dart}
    (hm : Kepler.Text.ChainLists.markedList L hL N r x)
    {k : ℕ} (hk : transformCount L N r x = k) (hk0 : 0 < k)
    {f : List Dart} {w : Dart} (hfind : findFaceDarts L x = f)
    (hw : nextEl f x = w) {d : Dart} (j : ℕ)
    (hj : j ≤ Kepler.Text.Reduction5.indexf (ztrans L N r x (k - 1)) w f)
    (hfpow : (nextEl f)^[j] (ztrans L N r x (k - 1)) = d) :
    (nextEl r)^[j] (ztrans L N r x (k - 1)) = d := by
  have h := cases2Chain L hL hgn haq hm hfind hw hk hk0 hj
  rw [hfpow] at h
  exact h

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.preRpowEq
