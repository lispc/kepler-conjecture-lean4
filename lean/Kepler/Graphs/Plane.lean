/-
Port of the Isabelle AFP "Flyspeck-Tame" theories `RTranCl.thy` and `Plane.thy`.

Source: `reference/afp-flyspeck-tame/{RTranCl,Plane}.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

`containsDuplicateEdge'` is annotated in `Plane.thy` as an equivalent
alternative definition; per the project plan only `containsDuplicateEdge`
is ported.
-/
import Kepler.Graphs.Enumerator
import Kepler.Graphs.FaceDivision

namespace Kepler.Graphs

/-- `RTranCl.thy: RTranCl`. Reflexive transitive closure of the relation
induced by a successor-list function: `g' ∈ succs g`. -/
inductive RTranCl (succs : Graph → List Graph) : Graph → Graph → Prop
  | refl : RTranCl succs g g
  | succs : g' ∈ succs g → RTranCl succs g' g'' → RTranCl succs g g''

/-- `Plane.thy: maxGon`. -/
def maxGon (p : Nat) : Nat := p + 3

/-- `Plane.thy: duplicateEdge`. -/
def duplicateEdge (g : Graph) (f : Face) (a b : Vertex) : Bool :=
  decide (2 ≤ directedLength f a b ∧ 2 ≤ directedLength f b a ∧ b ∈ neighbors g a)

/-- `Plane.thy: containsUnacceptableEdgeSnd`. -/
def containsUnacceptableEdgeSnd (N : Nat → Nat → Bool) (v : Nat) : List Nat → Bool
  | [] => false
  | w :: ws =>
    match ws with
    | [] => false
    | w' :: _ =>
      if v < w ∧ w < w' ∧ N w w' then true
      else containsUnacceptableEdgeSnd N w ws

/-- `Plane.thy: containsUnacceptableEdge`. -/
def containsUnacceptableEdge (N : Nat → Nat → Bool) : List Nat → Bool
  | [] => false
  | v :: vs =>
    match vs with
    | [] => false
    | w :: _ =>
      if v < w ∧ N v w then true
      else containsUnacceptableEdgeSnd N v vs

/-- `Plane.thy: containsDuplicateEdge`. -/
def containsDuplicateEdge (g : Graph) (f : Face) (v : Vertex) (is : List Nat) : Bool :=
  containsUnacceptableEdge (fun i j => duplicateEdge g f (f.nextVertices i v) (f.nextVertices j v)) is

/-- `Plane.thy: generatePolygon`. -/
def generatePolygon (n : Nat) (v : Vertex) (f : Face) (g : Graph) : List Graph :=
  let enumeration := enumerator n f.vertices.length
  let enumeration := enumeration.filter (fun is => !containsDuplicateEdge g f v is)
  let vertexLists := enumeration.map (indexToVertexList f v)
  vertexLists.map (subdivFace g f)

/-- `Plane.thy: next_plane0`. `[3..<Suc (maxGon p)]` is `List.range' 3 (maxGon p - 2)`. -/
def next_plane0 (p : Nat) (g : Graph) : List Graph :=
  if g.final then []
  else (nonFinals g).flatMap fun f => f.vertices.flatMap fun v =>
    (List.range' 3 (maxGon p - 2)).flatMap fun i => generatePolygon i v f g

/-- `Plane.thy: Seed`. -/
def Seed (p : Nat) : Graph := graph (maxGon p)

/-- `Plane.thy: PlaneGraphs0`. (Isabelle `graph set` ↦ `Graph → Prop`.) -/
def PlaneGraphs0 : Graph → Prop :=
  fun g => ∃ p, RTranCl (next_plane0 p) (Seed p) g ∧ g.final

end Kepler.Graphs
