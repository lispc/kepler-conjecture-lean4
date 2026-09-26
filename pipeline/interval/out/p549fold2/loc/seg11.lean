/- TIMING MODULE arm=seg1 (emit_fold2.py; scratch, 不入包). -/
import Kepler.Interval.CertTM

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Kepler.Interval.Cases

open Kepler.Interval

def Expr : IExpr 6 :=
  (.div (.sub (.mul (.add (.mul (.const ⟨0, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.mul (.const ⟨4, 0⟩) (.div (.const ⟨0, 0⟩) (.add (.const ⟨1, 0⟩) (.mul (.const ⟨1, 0⟩) (.const ⟨1, 0⟩))) 0))) (.const ⟨2, 0⟩)) (.mul (.mul (.const ⟨4, 0⟩) (.trans .arctanK (.const ⟨1, 0⟩) 2048 (-64))) (.const ⟨0, 0⟩))) (.mul (.const ⟨2, 0⟩) (.const ⟨2, 0⟩)) (-64))

def Box : Fin 6 → DInterval :=
  ![⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩, ⟨⟨21088289427, -33⟩, ⟨2705829397, -30⟩⟩]

def P : TMParams := ⟨[], [⟨(-80), (-80), (-80)⟩, ⟨(-80), (-80), (-80)⟩], []⟩

theorem t : checkPosTMHull Expr Box P = false := by
  decide

end Kepler.Interval.Cases
