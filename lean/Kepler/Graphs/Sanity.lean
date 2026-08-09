/-
Small sanity tests for the ported Flyspeck-Tame graph enumeration core.

All checks use kernel-checkable `decide`/`rfl` only (no `native_decide`,
no `sorry`). Expected values are derived from the Isabelle semantics by hand;
see the comments. The `#eval` smoke tests at the end are NOT part of any proof.
-/
import Kepler.Graphs.TameEnum

namespace Kepler.Graphs

/-! ## Constant tables (`Tame.thy`) -/

example : squanderVertex 0 3 = 6177 := rfl
example : squanderFace 5 = 4819 := rfl
example : squanderTarget = 15410 := rfl
example : excessTCount = 6295 := rfl

/-! ## `enumerator` (`Enumerator.thy`)

`enumerator inner outer`: `nmax = outer - 2`, `k = inner - 3`; results are
`[0] ++ is ++ [outer - 1]` with `is` weakly increasing, entries `≤ nmax`. -/

example : enumerator 3 3 = [[0, 0, 2], [0, 1, 2]] := by decide
example : enumerator 3 4 = [[0, 0, 3], [0, 1, 3], [0, 2, 3]] := by decide
example : enumerator 4 3 = [[0, 0, 0, 2], [0, 0, 1, 2], [0, 1, 1, 2]] := by decide

/-! ## `Seed` (`Plane.thy`) -/

example : (List.range 4).all (fun p => (Seed p).countVertices == p + 3) := by decide
example : (List.range 4).all (fun p => (nonFinals (Seed p)).length == 1) := by decide

/-! ## One step of `next_plane` on `Seed 0`

By hand from the Isabelle semantics: the single nonfinal face of `Seed 0` is
`[2, 1, 0]`, the minimal vertex is `2`, only `i = 3` is tried
(`maxGon 0 = 3`), and both enumeration entries survive the duplicate-edge
filter. `[0, 0, 2]` inserts one new vertex (4-vertex graph, still nonfinal);
`[0, 1, 2]` just makes the face final (3-vertex final graph). -/

example : (next_plane 0 (Seed 0)).map Graph.countVertices = [4, 3] := by decide

-- The acceptance-criterion form of the same check:
example : next_plane 0 (Seed 0) ≠ [] ∧
    (next_plane 0 (Seed 0)).all (fun g => decide (3 ≤ g.countVertices)) := by decide

/-! ## One step of `next_tame` on `Seed 0`

Same generation as above, but `next_tame` filters out final graphs that fail
`is_tame`; the 3-vertex final graph fails `tame10` (`13 ≤ 3` is false), so
only the 4-vertex (nonfinal) graph survives. -/

example : (next_tame 0 (Seed 0)).map Graph.countVertices = [4] := by decide

/-! ## Smoke tests (`#eval` only — not part of any proof) -/

-- Number of children of `Seed 0` under `next_tame 0`:
#eval (next_tame 0 (Seed 0)).length

-- Total number of grandchildren (two steps of `next_tame 0`):
#eval ((next_tame 0 (Seed 0)).flatMap (next_tame 0)).length

-- Their vertex counts:
#eval ((next_tame 0 (Seed 0)).flatMap (next_tame 0)).map Graph.countVertices

end Kepler.Graphs
