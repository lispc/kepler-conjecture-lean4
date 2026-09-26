/- TIMING MODULE arm=skel (emit_fold2.py; scratch, 不入包). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

open Kepler.Interval

def Expr : IExpr 6 :=
  (.sub (.const ⟨1, 0⟩) (.add (.const ⟨1, 0⟩) (.const ⟨1, 0⟩)))

def Box : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

def P : TMParams := ⟨[], [], []⟩

theorem t : checkPosTMHull Expr Box P = false := by
  decide

end Kepler.Interval.Cases
