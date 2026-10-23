/-
  Hard07 — W6-A light LP certificate data (machine generated, do not edit).

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

namespace Kepler.Text.LP.W6Data.Hard07

open Kepler.Text.LP

def data : List LpGraphCert := [
  ⟨"39599353438 18 4 0 1 2 3 4 0 3 4 5 3 4 3 2 4 1 0 6 7 4 6 0 5 8 3 2 1 9 3 9 1 7 3 4 2 10 3 10 2 9 3 7 6 8 3 8 5 11 3 11 5 4 3 11 4 10 3 9 7 12 3 12 7 8 3 12 8 11 3 10 9 12 3 12 11 10 ", .split ⟨.quad, [0, 1, 2, 3]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.quad, [0, 3, 4, 5]⟩ [.terminal ⟨.p4, false, [], [], []⟩, .split ⟨.quad, [1, 0, 6, 7]⟩ [.split ⟨.quad, [6, 0, 5, 8]⟩ [.terminal ⟨.p5, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p3, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩], .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩, .terminal ⟨.p4, false, [], [], []⟩]⟩
]

theorem data_length : data.length = 1 := rfl

/-- Literal terminal count from the dumper (not kernel-reduced:
the hard trees are too large for `decide`; see W6A_REPORT). -/
def terminalCount : Nat := 17

/-- Literal infeasible-terminal count from the dumper. -/
def infeasibleCount : Nat := 0

/-- Literal split-node count from the dumper. -/
def splitCount : Nat := 4

end Kepler.Text.LP.W6Data.Hard07
