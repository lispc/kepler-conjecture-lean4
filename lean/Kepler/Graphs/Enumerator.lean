/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Enumerator.thy`.

Source: `reference/afp-flyspeck-tame/Enumerator.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

The `enumTab` iarray cache is NOT ported (per project plan): `enum` just
computes `enumerator` directly.
-/
import Kepler.Graphs.Graph

namespace Kepler.Graphs

/-- Function iteration, mirroring Isabelle's `(f ^^ n) x`:
`iterate f 0 x = x`, `iterate f (n+1) x = f (iterate f n x)`. -/
private def iterate (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterate f n x)

/-- `Enumerator.thy: enumBase`. -/
def enumBase (nmax : Nat) : List (List Nat) :=
  (List.range (nmax + 1)).map (fun i => [i])

/-- `Enumerator.thy: enumAppend`. `[last is ..< Suc nmax]` is
`List.range' (last is) (nmax + 1 - last is)`; `last is` ↦ `is.getLast!`
(the lists generated here are always nonempty). -/
def enumAppend (nmax : Nat) (iss : List (List Nat)) : List (List Nat) :=
  iss.flatMap fun is =>
    (List.range' is.getLast! (nmax + 1 - is.getLast!)).map (fun n => is ++ [n])

/-- `Enumerator.thy: enumerator`. Precondition `inner ≥ 3` (as in Isabelle). -/
def enumerator (inner outer : Nat) : List (List Nat) :=
  let nmax := outer - 2
  let k := inner - 3
  (iterate (enumAppend nmax) k (enumBase nmax)).map (fun is => [0] ++ is ++ [outer - 1])

/-- `Enumerator.thy: enum`. The Isabelle version dispatches to the `enumTab`
iarray cache for `inner, outer < 9`; we always compute `enumerator` directly
(the cache is extensionally equal to `enumerator`). -/
def enum (inner outer : Nat) : List (List Nat) := enumerator inner outer

/-- `Enumerator.thy: hideDupsRec`. -/
def hideDupsRec [BEq α] (a : α) : List α → List (Option α)
  | [] => []
  | b :: bs => (if a == b then none else some b) :: hideDupsRec b bs

/-- `Enumerator.thy: hideDups`. -/
def hideDups [BEq α] : List α → List (Option α)
  | [] => []
  | b :: bs => some b :: hideDupsRec b bs

/-- `Enumerator.thy: indexToVertexList`. Precondition `hd is = 0`. -/
def indexToVertexList (f : Face) (v : Vertex) (is : List Nat) : List (Option Vertex) :=
  hideDups (is.map (fun k => f.nextVertices k v))

end Kepler.Graphs
