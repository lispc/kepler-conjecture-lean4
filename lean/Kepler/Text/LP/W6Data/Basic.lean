/-
  Kepler/Text/LP/W6Data/Basic — W6-A light-tree helpers.

  Deliberately independent of Kepler.Assembly: this module and the W6Data
  tree only import Kepler.Text.LP.LPSchema (no import cycle).
-/
import Kepler.Text.LP.LPSchema

namespace Kepler.Text.LP

-- Number of split nodes in a certificate tree (light-shape statistic).
mutual
  def LpCaseTree.countSplits : LpCaseTree → Nat
    | .terminal _ => 0
    | .split _ cs => 1 + LpCaseTree.countSplitsList cs

  def LpCaseTree.countSplitsList : List LpCaseTree → Nat
    | [] => 0
    | c :: cs => c.countSplits + LpCaseTree.countSplitsList cs
end

-- W6-A light contract: every terminal carries empty constraint tables.
mutual
  def LpCaseTree.constraintsEmpty : LpCaseTree → Bool
    | .terminal t =>
        t.constraints.isEmpty && t.targetVariables.isEmpty &&
          t.variableBounds.isEmpty
    | .split _ cs => LpCaseTree.constraintsEmptyList cs

  def LpCaseTree.constraintsEmptyList : List LpCaseTree → Bool
    | [] => true
    | c :: cs => c.constraintsEmpty && LpCaseTree.constraintsEmptyList cs
end

/-- Graph id of a light certificate: hypermap first token, `_` removed. -/
def LpGraphCert.graphId (g : LpGraphCert) : String :=
  lpHypermapId g.hypermapString

end Kepler.Text.LP
