/-
  Kepler.Text.Reduction5J5JcajyduFinal — **会师接线**（U 段收官 → k3UvnsSlot → J5-9）。

  ┌─ 件表 ─────────────────────────────────────────────────────────
  │ `finalAssumptionUvnsCombined` : `k3UvnsMainSlot`
  │   = `uvnsMainOfU2 uvnsVsOrdered`（U 段收官：有序支 + pairs 支）
  │ `k3UvnsSlotInstance` : `k3UvnsSlot`
  │   = `k3UvnsOfSlots finalAssumptionUvnsCombined`
  │ `jcajyduReduction5` : J5-9 结论（Assembly stub 的 Reduction5 侧）
  │   = `jcajyduFinalShape finalAssumptionUvnsCombined H hres`
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改已落库陈述/定义。
-/
import Kepler.Text.Reduction5J5UvnsU2
import Kepler.Text.Reduction5J5UvnsMainWiring
import Kepler.Text.Reduction5J5UvnsSlot
import Kepler.Text.Reduction5J5SxC
import Kepler.Text.Reduction5J5FinalShape

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

/-- **U 段收官**：HOL `final_assumption_uvns_combined` 的无条件形
（= `k3UvnsMainSlot`；有序支 `uvnsVsOrdered` + pairs 支 `uvnsPairsOfWalk`）。 -/
theorem finalAssumptionUvnsCombined : k3UvnsMainSlot :=
  uvnsMainOfU2 uvnsVsOrdered

/-- **hUvns 槽实例**：四件供料由 `k3UvnsOfSlots` 直投（U 段主定理唯一槽已消）。 -/
theorem k3UvnsSlotInstance : k3UvnsSlot :=
  k3UvnsOfSlots finalAssumptionUvnsCombined

/-- **J5-9 会师结论**（Assembly `jcajydu` stub 的 Reduction5 侧）：
`restricted → 平面图 g ∧ GoodGraphV4 g ∧ Iso`。 -/
theorem jcajyduReduction5 {α : Type*} [DecidableEq α]
    (H : Kepler.Text.Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Kepler.Graphs.Graph, Kepler.Graphs.PlaneGraphs g ∧
      Kepler.Text.TameCorrList.GoodGraphV4 g ∧
      ∃ H' : Kepler.Text.Hypermap (ℕ × ℕ),
        Kepler.Text.TameLp.IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' :=
  jcajyduFinalShape finalAssumptionUvnsCombined H hres

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.finalAssumptionUvnsCombined
#print axioms Kepler.Text.Reduction5.k3UvnsSlotInstance
#print axioms Kepler.Text.Reduction5.jcajyduReduction5
