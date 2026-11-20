import Kepler.Interval.Cases.IysBase
import Kepler.Interval.PosTree
import Kepler.Interval.CertBool
import Kepler.Interval.Cases.IysD1Leaves

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! IYOUOBF-sharpv2 IysD1 family tree (auto-generated): the bisection
cover of `iysZoneBox` with the 3 leaf positivites. -/

namespace Kepler.Interval.Cases
open Kepler.Interval

/-- The IysD1 family bisection tree. -/
def iysD1Tree : PosTree 6 (.neg IysD1Expr) :=
  (.node ![⟨⟨48103633715, -34⟩, ⟨759250125, -28⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, ⟨⟨1, 1⟩, ⟨8804682957, -32⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩] 3 (.leaf kBoxIysD1_0 iysD1_leaf0_pos) (.node ![⟨⟨48103633715, -34⟩, ⟨759250125, -28⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, ⟨⟨17394617549, -33⟩, ⟨8804682957, -32⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩, ⟨⟨1, 1⟩, ⟨1, 1⟩⟩] 0 (.leaf kBoxIysD1_1 iysD1_leaf1_pos) (.leaf kBoxIysD1_2 iysD1_leaf2_pos)))

/-- The family cover: every split is the exact dyadic bisection
(one kernel `decide` over `coversB`). -/
theorem iysD1Covers : iysD1Tree.covers :=
  PosTree.coversB_sound _ (by decide +kernel)

/-- The family positivity: `(.neg IysD1Expr) > 0` on the whole family box. -/
theorem iysD1_pos (ρ : Fin 6 → ℝ) (hρ : boxMem iysZoneBox ρ) :
    0 < IExpr.evalReal (.neg IysD1Expr) ρ :=
  iysD1Tree.sound iysZoneBox iysD1Covers
    (by intro i; fin_cases i <;> exact
      ⟨by decide +kernel, by decide +kernel⟩) ρ hρ

#print axioms iysD1_pos

end Kepler.Interval.Cases
