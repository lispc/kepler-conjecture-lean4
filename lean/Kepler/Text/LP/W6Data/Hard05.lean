/-
  Hard05 — W6-A light LP certificate data (machine generated, do not edit).

  Generator: `tools/gen_w6_lean.py` from `tools/dump_w6_light.py` output.
  Source: reference/flyspeck/formal_lp/glpk/binary/{easy,hard}_*.dat
  + hard_7.tar.gz member (39 Marshal files, 19,715 graphs, 43,078 terminals).

  W6-A contract: only the split-tree shape is carried. Terminal
  constraints / targetVariables / variableBounds are `[]` (not carried;
  W6-B+ adds the constraint semantics). Splits carry splitType + splitFace.
-/
import Kepler.Text.LP.W6Data.Basic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Kepler.Text.LP.W6Data.Hard05

open Kepler.Text.LP

def data : List LpGraphCert := [
  ⟨"100126458338 18 5 0 1 2 3 4 5 0 4 5 6 7 3 5 4 3 3 1 0 8 3 8 0 7 3 5 3 9 3 9 3 2 3 9 2 10 3 10 2 11 3 11 2 1 3 11 1 8 3 6 5 9 3 8 7 12 3 12 7 6 3 6 9 10 3 11 8 12 3 10 11 12 3 12 6 10 ", .split ⟨.pent, [0, 1, 2, 3, 4]⟩ [.split ⟨.pent, [0, 4, 5, 6, 7]⟩ [.split ⟨.tri, [5, 4, 3]⟩ [.split ⟨.s218, [5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [4]⟩ [.split ⟨.s218, [3]⟩ [.split ⟨.mid, [3, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p6, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩]], .split ⟨.tri, [12, 7, 6]⟩ [.split ⟨.s218, [5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [4]⟩ [.split ⟨.tri, [11, 2, 1]⟩ [.split ⟨.s218, [3]⟩ [.split ⟨.mid, [3, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [11]⟩ [.split ⟨.mid, [11, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [2]⟩ [.split ⟨.mid, [2, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [12]⟩ [.split ⟨.mid, [12, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [7]⟩ [.split ⟨.mid, [7, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [6]⟩ [.split ⟨.mid, [6, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [1]⟩ [.split ⟨.mid, [1, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.tri, [9, 3, 2]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.s236, [4]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.high, [4]⟩ [.split ⟨.tri, [6, 5, 9]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.tri, [10, 11, 12]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [10, 2, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [12, 6, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [8, 0, 7]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.edge, [2, 1, 11]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.edge, [1, 11, 2]⟩ [.split ⟨.addBig, [11, 1, 8]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p5, false, [], [], []⟩]]]]]]]]]]]]]]]]], .split ⟨.s218, [3]⟩ [.split ⟨.mid, [3, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [12]⟩ [.split ⟨.mid, [12, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [7]⟩ [.split ⟨.mid, [7, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [6]⟩ [.split ⟨.mid, [6, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.tri, [9, 3, 2]⟩ [.terminal ⟨.p6, false, [], [], []⟩, .split ⟨.tri, [12, 6, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [6, 9, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [10, 11, 12]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [9, 2, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s236, [4]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.high, [4]⟩ [.terminal ⟨.p5, false, [], [], []⟩]]]]]]]]]]]], .terminal ⟨.p4, false, [], [], []⟩]], .split ⟨.s218, [5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [4]⟩ [.split ⟨.tri, [11, 2, 1]⟩ [.split ⟨.s218, [3]⟩ [.split ⟨.mid, [3, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [11]⟩ [.split ⟨.mid, [11, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [2]⟩ [.split ⟨.mid, [2, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [1]⟩ [.split ⟨.mid, [1, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.tri, [6, 5, 9]⟩ [.terminal ⟨.p6, false, [], [], []⟩, .split ⟨.tri, [10, 2, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [9, 2, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s236, [4]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.high, [4]⟩ [.split ⟨.tri, [10, 11, 12]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p7, false, [], [], []⟩]]]]]]]]]], .split ⟨.s218, [3]⟩ [.split ⟨.mid, [3, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.tri, [6, 5, 9]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.tri, [9, 2, 10]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.tri, [10, 2, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [10, 11, 12]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [6, 9, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [12, 6, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s236, [4]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .split ⟨.high, [4]⟩ [.terminal ⟨.p5, false, [], [], []⟩]]]]]]]]]], .terminal ⟨.p4, false, [], [], []⟩]]]], .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p5, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩], .terminal ⟨.p3, false, [], [], []⟩, .split ⟨.pent, [0, 4, 5, 6, 7]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩], .terminal ⟨.p3, false, [], [], []⟩, .split ⟨.pent, [0, 4, 5, 6, 7]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩], .split ⟨.pent, [0, 4, 5, 6, 7]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩], .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]⟩
]

theorem data_length : data.length = 1 := rfl

/-- Literal terminal count from the dumper (not kernel-reduced:
the hard trees are too large for `decide`; see W6A_REPORT). -/
def terminalCount : Nat := 105

/-- Literal infeasible-terminal count from the dumper. -/
def infeasibleCount : Nat := 0

/-- Literal split-node count from the dumper. -/
def splitCount : Nat := 81

end Kepler.Text.LP.W6Data.Hard05
