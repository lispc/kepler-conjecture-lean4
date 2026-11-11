/-
  Kepler.Text.Reduction5J5UvnsMainWiring — U 段合成：`uvnsMainOfU2`
  （`k3UvnsMainSlot` 的两合取接线，只留 J4 的 U2 一个显式槽）。

  **ERRATA（路径）**：派单指定落点 `Reduction5J5UvnsCombined.lean` 已存在
  （nb53 的 `finalAssumptionUvnsCombinedOfSlots`，76ef16de 落库）——
  本件改用新名 `Reduction5J5UvnsMainWiring.lean`，既有文件零触碰。

  接线：
  ① 有序支（hVs'）= `hU2` 原样（同一 `{v} hprev` 形）；
  ② pairs 支（hUvns）= `uvnsPairsOfWalk … hnNil hprev`（U3，bad42751）。
  `hnNil/hnFy/hnZx/hIdxSnd` 四前提只是透传，不在此件重证。

  纪律：零公理、零占位证明；主仓 tracked 零改动。
-/

import Kepler.Text.Reduction5J5UvnsU3
import Kepler.Text.Reduction5J5UvnsSlot

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **U 段合成**：`k3UvnsMainSlot`（十前提形）由 U2（有序支槽）+ U3
（pairs 支，在库）装配。 -/
theorem uvnsMainOfU2
    (hU2 : ∀ (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
      (hres : (hypermapOfList L hL).IsRestricted)
      {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
      (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
      (hk : transformCount L N r x = k)
      {v : ℕ} (hprev : (prevEl (core L r) v, v) = x),
      ∀ i, i + 1 < ((Kepler.Text.Reduction3.destTripleFull (core L r) v
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).filterMap id).length →
        indexf v (((Kepler.Text.Reduction3.destTripleFull (core L r) v
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).filterMap id).getD i 0) (core L r) <
        indexf v (((Kepler.Text.Reduction3.destTripleFull (core L r) v
          (Kepler.Text.Reduction3.coreTripleV4 L N r x)).filterMap id).getD (i + 1) 0)
          (core L r)) :
    k3UvnsMainSlot := by
  intro L hL hgn hres N r x k hm hnf hk hnNil hnFy hnZx hIdxSnd v hprev
  refine ⟨?_, ?_⟩
  · exact hU2 L hL hgn hres hm hnf hk hprev
  · exact uvnsPairsOfWalk L hL hgn hres hm hnf hk hnNil hprev

end Kepler.Text.Reduction5

#print axioms Kepler.Text.Reduction5.uvnsMainOfU2
