/-
  Kepler.Text.Reduction5J5HfSupply — J5-9 ① 号勾：hF 供给与 `jcajyduOfK4`（SF-106 后）。

  构造：`hFTameSpine = fun hK10 => reductionF hK10 hrreAll hrreSAll hcsnl`，
  三槽均按 SF-106 前提承载形逐点供料：
  · hrreAll  ← W5b `rRtransEqThm`（24e18012）
  · hrreSAll ← nb46 `rRtransEqToSpine`（5ef698e8）+ 内部 `TameSpine.aqiunpp` 造 AqiunppSlot
  · hcsnl    ← 8b `coreSplitNormalListThm`（cb1396fe）
  装配：`jcajyduOfK4 = jcajyduTameSpine hFTameSpine hK4`（只吃 hK4）。

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction3Thm19
import Kepler.Text.Reduction5Ml1W5bBwd
import Kepler.Text.Reduction5J5K2A2Up
import Kepler.Text.Reduction5Ml1W4
import Kepler.Text.TameSpine.JcajyduAssembly
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)
open Kepler.Text.ChainLists (markedList)

/-- **J5-9 hF 供给**：`reductionF` 三槽的前提承载形逐点供料
（`assumptionSetK10Full → restrictedHypermapsArePlaneGraphsV4`）。 -/
theorem hFTameSpine :
    Kepler.Text.Reduction3.assumptionSetK10Full →
      Kepler.Text.TameSpine.restrictedHypermapsArePlaneGraphsV4 := by
  intro hK10
  refine Kepler.Text.Reduction3.reductionF hK10 ?_ ?_ ?_
  · -- hrreAll：W5b
    intro L hL hgn N' r' y hm hnf
    exact rRtransEqThm L hL hgn hm hnf
  · -- hrreSAll：nb46 桥 + W5b（AqiunppSlot 由 aqiunpp 内部构造）
    intro L hL hgn N' r' y hm hnf
    exact rRtransEqToSpine L hL hgn hm.1
      (fun hgn' N'' r'' x'' hm'' i =>
        Kepler.Text.TameSpine.aqiunpp L hL hgn' N'' r'' x'' hm'' i)
      hm hnf (rRtransEqThm L hL hgn hm hnf)
  · -- hcsnl：8b coreSplitNormalListThm
    intro L hL N' r' y hgn hm hnf
    exact coreSplitNormalListThm L hL hgn hm hnf

/-- **J5-9 装配（只吃 `hK4`）**：`jcajyduTameSpine` 的 `hF` 槽由 `hFTameSpine` 供给，
结论与 `Kepler.Text.TameSpine.jcajyduTameSpine` 同形。 -/
theorem jcajyduOfK4
    (hK4 : (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart)
              (k : ℕ), reductionK4Asm Kepler.Text.Reduction3.GoodNodesSlot
                Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot
                L N r x k → reductionK4Concl L N r x k) →
        Kepler.Text.Reduction3.assumptionSetK10Full)
    {α : Type*} [DecidableEq α] (H : Kepler.Text.Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Kepler.Graphs.Graph, Kepler.Graphs.PlaneGraphs g ∧
      Kepler.Text.TameCorrList.GoodGraphV4 g ∧
      ∃ H' : Kepler.Text.Hypermap (ℕ × ℕ),
        Kepler.Text.TameLp.IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' :=
  Kepler.Text.TameSpine.jcajyduTameSpine hFTameSpine hK4 H hres

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.hFTameSpine
#print axioms Kepler.Text.Reduction5.jcajyduOfK4
