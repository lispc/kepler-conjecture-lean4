/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Plane1.thy`.

Source: `reference/afp-flyspeck-tame/Plane1.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).
-/
import Kepler.Graphs.Plane

namespace Kepler.Graphs

/-- `Plane1.thy: minimalFace`. The (first) nonfinal face with the fewest vertices. -/
def minimalFace (fs : List Face) : Face := minimal (fun f => f.vertices.length) fs

/-- `Plane1.thy: minimalVertex`. The (first) vertex of `f` of minimal height. -/
def minimalVertex (g : Graph) (f : Face) : Vertex := minimal (height g) f.vertices

/-- `Plane1.thy: next_plane`. -/
def next_plane (p : Nat) (g : Graph) : List Graph :=
  let fs := nonFinals g
  if fs.isEmpty then []
  else
    let f := minimalFace fs
    let v := minimalVertex g f
    (List.range' 3 (maxGon p - 2)).flatMap fun i => generatePolygon i v f g

/-- `Plane1.thy: PlaneGraphsP`. -/
def PlaneGraphsP (p : Nat) : Graph → Prop :=
  fun g => RTranCl (next_plane p) (Seed p) g ∧ g.final

/-- `Plane1.thy: PlaneGraphs`. -/
def PlaneGraphs : Graph → Prop := fun g => ∃ p, PlaneGraphsP p g

end Kepler.Graphs
