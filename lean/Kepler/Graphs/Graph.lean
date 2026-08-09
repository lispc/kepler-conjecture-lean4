/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Graph.thy`.

Source: `reference/afp-flyspeck-tame/Graph.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Type correspondences:
- `vertex = nat`                    ↦ `Vertex := Nat`
- `facetype = Final | Nonfinal`     ↦ `Face.isFinal : Bool` (`true ↔ Final`)
- `face = Face (vertex list) facetype` ↦ `structure Face`
- `graph = Graph (face list) nat (face list list) (nat list)` ↦ `structure Graph`

Boundary conventions (Isabelle's `!` and `hd`/`last` return `undefined` when out
of range; the generator never triggers these cases — see `Invariants.thy`):
- list indexing `xs ! i` ↦ `xs.getD i <default>` / `xs[i]!`
- `hd` ↦ `List.head!`, `last` ↦ `List.getLast!`
-/
import Kepler.Graphs.Rotation

namespace Kepler.Graphs

/-- `Graph.thy: type_synonym vertex = nat`. -/
abbrev Vertex := Nat

/-- `Graph.thy: datatype face = Face (vertex list) facetype`.
`isFinal = true` corresponds to Isabelle's `Final`, `false` to `Nonfinal`. -/
structure Face where
  vertices : List Vertex
  isFinal : Bool
  deriving BEq, Repr, DecidableEq

instance : Inhabited Face := ⟨⟨[], false⟩⟩

/-- `Graph.thy: final :: face ⇒ bool`. -/
def Face.final (f : Face) : Bool := f.isFinal

/-- `Graph.thy: setFinal`. -/
def setFinal (f : Face) : Face := { f with isFinal := true }

/-- `Graph.thy: nextElem`. Successor of `x` in the list, wrapping around
via the base value `b` at the end. -/
def nextElem [BEq α] : List α → α → α → α
  | [], b, _ => b
  | a :: as, b, x =>
    if x == a then (match as with | [] => b | a' :: _ => a')
    else nextElem as b x

/-- `Graph.thy: nextVertex` (`f ∙ v`). `hd vs` is mapped to `List.head!`;
faces in this development always have ≥ 3 vertices. -/
def Face.nextVertex (f : Face) (v : Vertex) : Vertex :=
  nextElem f.vertices f.vertices.head! v

/-- `Graph.thy: nextVertices` (`f^n ∙ v`): `n`-fold application of `nextVertex`. -/
def Face.nextVertices (f : Face) (n : Nat) (v : Vertex) : Vertex :=
  match n with
  | 0 => v
  | n + 1 => f.nextVertex (f.nextVertices n v)

/-- `Graph.thy: prevVertex` (`f⁻¹ ∙ v`). -/
def Face.prevVertex (f : Face) (v : Vertex) : Vertex :=
  nextElem f.vertices.reverse f.vertices.getLast! v

/-- `Graph.thy: triangle`. -/
def triangle (f : Face) : Bool := f.vertices.length == 3

/-- `Graph.thy: datatype graph = Graph (face list) nat (face list list) (nat list)`. -/
structure Graph where
  faces : List Face
  countVertices : Nat
  faceListAt : List (List Face)
  heights : List Nat
  deriving BEq, Repr, DecidableEq

/-- `Graph.thy: vertices (Graph fs n f h) = [0 ..< n]`. -/
def Graph.vertices (g : Graph) : List Vertex := List.range g.countVertices

/-- `Graph.thy: facesAt`. `faceListAt g ! v` is mapped to `getD v []`;
in the generator `v < countVertices g = (faceListAt g).length`, so the default
is never used (Isabelle returns `undefined` out of range). -/
def Graph.facesAt (g : Graph) (v : Vertex) : List Face := g.faceListAt.getD v []

/-- `Graph.thy: height`. Same boundary convention as `facesAt`. -/
def height (g : Graph) (v : Vertex) : Nat := g.heights.getD v 0

/-- `Graph.thy: graph`. The wheel with `n` rim vertices: a final face and its
nonfinal reverse. -/
def graph (n : Nat) : Graph :=
  let vs := List.range n
  let fs := [Face.mk vs true, Face.mk vs.reverse false]
  ⟨fs, n, List.replicate n fs, List.replicate n 0⟩

/-- `Graph.thy: finals`. -/
def finals (g : Graph) : List Face := g.faces.filter Face.final

/-- `Graph.thy: nonFinals`. -/
def nonFinals (g : Graph) : List Face := g.faces.filter (fun f => !f.final)

/-- `Graph.thy: countNonFinals`. -/
def countNonFinals (g : Graph) : Nat := (nonFinals g).length

/-- `Graph.thy: finalGraph` (`final :: graph ⇒ bool`). -/
def Graph.final (g : Graph) : Bool := (nonFinals g).isEmpty

/-- `Graph.thy: finalVertex`. -/
def finalVertex (g : Graph) (v : Vertex) : Bool := (g.facesAt v).all Face.final

/-- `Graph.thy: degree`. -/
def degree (g : Graph) (v : Vertex) : Nat := (g.facesAt v).length

/-- `Graph.thy: tri`. -/
def tri (g : Graph) (v : Vertex) : Nat :=
  ((g.facesAt v).filter (fun f => f.final && f.vertices.length == 3)).length

/-- `Graph.thy: quad`. -/
def quad (g : Graph) (v : Vertex) : Nat :=
  ((g.facesAt v).filter (fun f => f.final && f.vertices.length == 4)).length

/-- `Graph.thy: except`. -/
def except (g : Graph) (v : Vertex) : Nat :=
  ((g.facesAt v).filter (fun f => f.final && decide (5 ≤ f.vertices.length))).length

/-- `Graph.thy: vertextype`. -/
def vertextype (g : Graph) (v : Vertex) : Nat × Nat × Nat :=
  (tri g v, quad g v, except g v)

/-- `Graph.thy: exceptionalVertex`. -/
def exceptionalVertex (g : Graph) (v : Vertex) : Bool := except g v != 0

/-- `Graph.thy: neighbors`. -/
def neighbors (g : Graph) (v : Vertex) : List Vertex :=
  (g.facesAt v).map (fun f => f.nextVertex v)

/-- `Graph.thy: nextFace`. -/
def nextFace (g : Graph) (v : Vertex) (f : Face) : Face :=
  let fs := g.facesAt v
  if fs.isEmpty then f else nextElem fs fs.head! f

/-- `Graph.thy: directedLength`. Precondition: `a`, `b` occur in `f`. -/
def directedLength (f : Face) (a b : Vertex) : Nat :=
  if a == b then 0 else (between f.vertices a b).length + 1

end Kepler.Graphs
