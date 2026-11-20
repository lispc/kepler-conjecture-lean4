import Kepler.Interval.Cases.IysBase
import Kepler.Interval.PosTree
import Kepler.Interval.CertBool
import Kepler.Interval.Cases.IysD4Leaves

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! IYOUOBF-sharpv2 IysD4 family tree (auto-generated): the bisection
cover of `iysEdgeBox` with the 1 leaf positivites. -/

namespace Kepler.Interval.Cases
open Kepler.Interval

/-- The IysD4 family bisection tree. -/
def iysD4Tree : PosTree 6 IysD4Expr :=
  (.leaf kBoxIysD4_0 iysD4_leaf0_pos)

/-- The family cover: every split is the exact dyadic bisection
(one kernel `decide` over `coversB`). -/
theorem iysD4Covers : iysD4Tree.covers :=
  PosTree.coversB_sound _ (by decide +kernel)

/-- The family positivity: `IysD4Expr > 0` on the whole family box. -/
theorem iysD4_pos (ρ : Fin 6 → ℝ) (hρ : boxMem iysEdgeBox ρ) :
    0 < IExpr.evalReal IysD4Expr ρ :=
  iysD4Tree.sound iysEdgeBox iysD4Covers
    (by intro i; fin_cases i <;> exact
      ⟨by decide +kernel, by decide +kernel⟩) ρ hρ

#print axioms iysD4_pos

end Kepler.Interval.Cases
