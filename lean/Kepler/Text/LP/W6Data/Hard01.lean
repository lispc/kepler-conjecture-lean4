/-
  Hard01 — W6-A light LP certificate data (machine generated, do not edit).

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

namespace Kepler.Text.LP.W6Data.Hard01

open Kepler.Text.LP

def data : List LpGraphCert := [
  ⟨"179189825656 21 4 0 1 2 3 3 0 3 4 3 4 3 2 3 4 2 5 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ", .split ⟨.quad, [0, 1, 2, 3]⟩ [.terminal ⟨.p3, true, [], [], []⟩, .split ⟨.tri, [9, 0, 4]⟩ [.split ⟨.s218, [0]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [1]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [3]⟩ [.split ⟨.s236, [3]⟩ [.split ⟨.s218, [2]⟩ [.split ⟨.mid, [3, 2]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.tri, [4, 2, 5]⟩ [.split ⟨.s218, [9]⟩ [.split ⟨.mid, [3, 9]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [4]⟩ [.split ⟨.mid, [3, 4]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [5]⟩ [.split ⟨.mid, [3, 5]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.tri, [4, 3, 2]⟩ [.split ⟨.tri, [0, 3, 4]⟩ [.split ⟨.tri, [8, 1, 0]⟩ [.split ⟨.edge, [2, 5, 4]⟩ [.split ⟨.addBig, [5, 2, 6]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [5, 4, 2]⟩ [.split ⟨.addBig, [4, 5, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [4, 2, 5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]], .terminal ⟨.p5, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩]]]], .terminal ⟨.p4, false, [], [], []⟩]], .split ⟨.high, [3]⟩ [.split ⟨.tri, [4, 2, 5]⟩ [.split ⟨.tri, [4, 3, 2]⟩ [.split ⟨.tri, [0, 3, 4]⟩ [.split ⟨.tri, [8, 1, 0]⟩ [.split ⟨.edge, [2, 5, 4]⟩ [.split ⟨.addBig, [5, 2, 6]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [5, 4, 2]⟩ [.split ⟨.addBig, [4, 5, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [4, 2, 5]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]], .split ⟨.tri, [6, 2, 1]⟩ [.terminal ⟨.p6, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩]]], .terminal ⟨.p4, false, [], [], []⟩]]], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p5, false, [], [], []⟩, .split ⟨.tri, [9, 0, 4]⟩ [.split ⟨.tri, [4, 2, 5]⟩ [.split ⟨.tri, [4, 3, 2]⟩ [.split ⟨.tri, [0, 3, 4]⟩ [.split ⟨.s218, [9]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [4]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [0]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [2]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.s218, [5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.tri, [8, 1, 0]⟩ [.split ⟨.tri, [6, 2, 1]⟩ [.split ⟨.s218, [3]⟩ [.split ⟨.s236, [3]⟩ [.split ⟨.s218, [8]⟩ [.split ⟨.mid, [3, 8]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [1]⟩ [.split ⟨.mid, [3, 1]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [6]⟩ [.split ⟨.mid, [3, 6]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [0, 4, 9]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]]], .split ⟨.high, [3]⟩ [.split ⟨.edge, [2, 5, 4]⟩ [.split ⟨.addBig, [5, 2, 6]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [5, 4, 2]⟩ [.split ⟨.addBig, [4, 5, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [0, 4, 9]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]]]], .terminal ⟨.p4, false, [], [], []⟩], .split ⟨.s218, [8]⟩ [.terminal ⟨.p3, false, [], [], []⟩, .split ⟨.s218, [1]⟩ [.terminal ⟨.p3, false, [], [], []⟩, .split ⟨.edge, [0, 4, 9]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]]], .split ⟨.tri, [6, 2, 1]⟩ [.split ⟨.s218, [6]⟩ [.terminal ⟨.p3, false, [], [], []⟩, .split ⟨.s218, [1]⟩ [.terminal ⟨.p3, false, [], [], []⟩, .split ⟨.edge, [2, 5, 4]⟩ [.split ⟨.addBig, [5, 2, 6]⟩ [.terminal ⟨.p3, false, [], [], []⟩], .split ⟨.edge, [5, 4, 2]⟩ [.split ⟨.addBig, [4, 5, 10]⟩ [.terminal ⟨.p4, false, [], [], []⟩], .split ⟨.edge, [4, 2, 5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]]]], .terminal ⟨.p3, false, [], [], []⟩]]]]]]], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩]]⟩
]

theorem data_length : data.length = 1 := rfl

/-- Literal terminal count from the dumper (not kernel-reduced:
the hard trees are too large for `decide`; see W6A_REPORT). -/
def terminalCount : Nat := 58

/-- Literal infeasible-terminal count from the dumper. -/
def infeasibleCount : Nat := 1

/-- Literal split-node count from the dumper. -/
def splitCount : Nat := 71

end Kepler.Text.LP.W6Data.Hard01
