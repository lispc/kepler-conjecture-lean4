/-
  Hard13 — W6-A light LP certificate data (machine generated, do not edit).

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

namespace Kepler.Text.LP.W6Data.Hard13

open Kepler.Text.LP

def data : List LpGraphCert := [
  ⟨"242652038506 20 4 0 1 2 3 3 0 3 4 3 4 3 5 3 5 3 2 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 4 10 4 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ", .split ⟨.quad, [0, 1, 2, 3]⟩ [.split ⟨.quad, [10, 4, 5, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩], .split ⟨.quad, [10, 4, 5, 11]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩], .split ⟨.quad, [10, 4, 5, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩], .split ⟨.quad, [10, 4, 5, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩], .split ⟨.quad, [10, 4, 5, 11]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]]⟩
]

theorem data_length : data.length = 1 := rfl

/-- Literal terminal count from the dumper (not kernel-reduced:
the hard trees are too large for `decide`; see W6A_REPORT). -/
def terminalCount : Nat := 25

/-- Literal infeasible-terminal count from the dumper. -/
def infeasibleCount : Nat := 0

/-- Literal split-node count from the dumper. -/
def splitCount : Nat := 6

end Kepler.Text.LP.W6Data.Hard13
