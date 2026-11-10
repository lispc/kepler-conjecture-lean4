/-
  Kepler.Text.TameSpine.Reduction3J5IndexfPowAdd — tame-corr nb21：`_pre` f 侧子集
  换算的第 2 步：`indexf w ((next_el r)^j zk) r = indexf w zk r + j`。

  纪律：零公理、零占位证明、零反射式判定；主仓 tracked 零写入。
-/

import Kepler.Text.TameSpine.Reduction3J5IndexfYltSizelPreCount
import Kepler.Text.MoreLemma2Island1
import Kepler.Text.Reduction5Kbwpbhq

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.TameSpine

open Kepler.Graphs (fgraph)
open Kepler.Assembly (nextEl)
open Kepler.Text.Reduction5 (Dart indexf)

/-- **`_pre` 换算第 2 步**：`indexf w ((nextEl r)^j zk) r = indexf w zk r + j`
（`zk` 的 j 次迭代在 r 上的 indexf 是可加的）。 -/
theorem indexfPowAdd {r : List Dart} {w zk : Dart}
    (hw : w ∈ r) (hzk : zk ∈ r) (hnd : r.Nodup) {j : ℕ}
    (hsum : Kepler.Text.Reduction5.indexf w zk r + j < r.length) :
    Kepler.Text.Reduction5.indexf w ((nextEl r)^[j] zk) r
      = Kepler.Text.Reduction5.indexf w zk r + j := by
  have hd : (nextEl r)^[j] zk ∈ r := memPowerNextEl hzk j
  have hjlen : j < r.length := by omega
  have hdj : Kepler.Text.Reduction5.indexf zk ((nextEl r)^[j] zk) r = j :=
    Kepler.Text.MoreLemma2Island1.nextElnIndexf hzk hd hnd
      ((Kepler.Text.Reduction5.iterateInstEq r zk j).symm) hjlen
  have hsum' : Kepler.Text.Reduction5.indexf w zk r
      + Kepler.Text.Reduction5.indexf zk ((nextEl r)^[j] zk) r < r.length := by
    rw [hdj]
    exact hsum
  have h := Kepler.Text.Reduction4.indexf_add_sum hw hzk hd hsum'
  rw [hdj] at h
  exact h.symm

end Kepler.Text.TameSpine

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理）。 -/
#print axioms Kepler.Text.TameSpine.indexfPowAdd
