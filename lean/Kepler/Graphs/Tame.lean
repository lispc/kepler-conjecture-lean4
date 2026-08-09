/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Tame.thy`.

Source: `reference/afp-flyspeck-tame/Tame.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

The tame conditions `tame9a`–`tame12o` are ported as executable `Bool`
predicates (Isabelle `bool`). `tame13a` quantifies over weight assignments
`w : face ⇒ nat`; it is ported as a `Prop` (`∃ w : Face → Nat, …`), together
with an executable checker `admissibleCheck`/`tame13aCheck` taking the weight
witness as a list parallel to `faces g` — this is the intended certificate
format for the future "certificate + checker" pipeline.
-/
import Kepler.Graphs.Plane1

namespace Kepler.Graphs

/-! ## Constants (`Tame.thy`, §Constants) -/

/-- `Tame.thy: squanderTarget`. -/
def squanderTarget : Nat := 15410

/-- `Tame.thy: excessTCount` (a). -/
def excessTCount : Nat := 6295

/-- `Tame.thy: squanderVertex` (b). Constant table, values copied verbatim. -/
def squanderVertex (p q : Nat) : Nat :=
  if p = 0 ∧ q = 3 then 6177
  else if p = 0 ∧ q = 4 then 9696
  else if p = 1 ∧ q = 2 then 6557
  else if p = 1 ∧ q = 3 then 6176
  else if p = 2 ∧ q = 1 then 7967
  else if p = 2 ∧ q = 2 then 4116
  else if p = 2 ∧ q = 3 then 12846
  else if p = 3 ∧ q = 1 then 3106
  else if p = 3 ∧ q = 2 then 8165
  else if p = 4 ∧ q = 0 then 3466
  else if p = 4 ∧ q = 1 then 3655
  else if p = 5 ∧ q = 0 then 395
  else if p = 5 ∧ q = 1 then 11354
  else if p = 6 ∧ q = 0 then 6854
  else if p = 7 ∧ q = 0 then 14493
  else squanderTarget

/-- `Tame.thy: squanderFace` (d). -/
def squanderFace (n : Nat) : Nat :=
  if n = 3 then 0
  else if n = 4 then 2058
  else if n = 5 then 4819
  else if n = 6 then 7120
  else squanderTarget

/-! ## Separated sets of vertices (`Tame.thy`, §Separated) -/

/-- `Tame.thy: separated₂`. (Isabelle `vertex set` ↦ `Vertex → Prop`.) -/
def separated₂ (g : Graph) (V : Vertex → Prop) : Prop :=
  ∀ v, V v → ∀ f ∈ g.facesAt v, ¬V (f.nextVertex v)

/-- `Tame.thy: separated₃`. The set equality `V f ∩ V = {v}` is rendered as
the pointwise biconditional. -/
def separated₃ (g : Graph) (V : Vertex → Prop) : Prop :=
  ∀ v, V v → ∀ f ∈ g.facesAt v, f.vertices.length ≤ 4 →
    ∀ x, (x ∈ f.vertices ∧ V x) ↔ x = v

/-- `Tame.thy: separated`. -/
def separated (g : Graph) (V : Vertex → Prop) : Prop :=
  separated₂ g V ∧ separated₃ g V

/-! ## Admissible weight assignments (`Tame.thy`, §Admissible), as `Prop`s -/

/-- `Tame.thy: admissible₁`. -/
def admissible₁ (w : Face → Nat) (g : Graph) : Prop :=
  ∀ f ∈ g.faces, squanderFace f.vertices.length ≤ w f

/-- `Tame.thy: admissible₂`. -/
def admissible₂ (w : Face → Nat) (g : Graph) : Prop :=
  ∀ v ∈ g.vertices, except g v = 0 →
    squanderVertex (tri g v) (quad g v) ≤ ((g.facesAt v).map w).sum

/-- `Tame.thy: admissible₃`. -/
def admissible₃ (w : Face → Nat) (g : Graph) : Prop :=
  ∀ v ∈ g.vertices, vertextype g v = (5, 0, 1) →
    excessTCount ≤ (((g.facesAt v).filter triangle).map w).sum

/-- `Tame.thy: admissible`. -/
def admissible (w : Face → Nat) (g : Graph) : Prop :=
  admissible₁ w g ∧ admissible₂ w g ∧ admissible₃ w g

/-! ## Executable checkers for admissibility, with the weight witness given
as a list `ws` parallel to `faces g` (certificate format).

NOTE: `weightOf` looks a face up in `faces g` with `List.lookup`, i.e. it
returns the weight at the FIRST occurrence. If `faces g` contains two equal
faces, the checker's `w` is the first-position weight everywhere, while the
positional sum in `tame13aCheck` uses each position's own weight. Graphs in
this development have distinct faces (an invariant of the enumeration), so
the two views agree on all reachable graphs. -/

/-- Weight function reconstructed from the positional witness list. -/
def weightOf (ws : List Nat) (g : Graph) (f : Face) : Nat :=
  ((g.faces.zip ws).lookup f).getD 0

/-- Executable counterpart of `admissible₁`. -/
def admissible₁Check (ws : List Nat) (g : Graph) : Bool :=
  g.faces.all (fun f => decide (squanderFace f.vertices.length ≤ weightOf ws g f))

/-- Executable counterpart of `admissible₂`. -/
def admissible₂Check (ws : List Nat) (g : Graph) : Bool :=
  g.vertices.all fun v =>
    if except g v = 0 then
      decide (squanderVertex (tri g v) (quad g v) ≤ ((g.facesAt v).map (weightOf ws g)).sum)
    else true

/-- Executable counterpart of `admissible₃`. -/
def admissible₃Check (ws : List Nat) (g : Graph) : Bool :=
  g.vertices.all fun v =>
    if vertextype g v = (5, 0, 1) then
      decide (excessTCount ≤ (((g.facesAt v).filter triangle).map (weightOf ws g)).sum)
    else true

/-- Executable counterpart of `admissible` (for the witness `ws`). -/
def admissibleCheck (ws : List Nat) (g : Graph) : Bool :=
  ws.length == g.faces.length &&
  admissible₁Check ws g && admissible₂Check ws g && admissible₃Check ws g

/-! ## Tameness (`Tame.thy`, §TameDef) -/

/-- `Tame.thy: tame9a`. -/
def tame9a (g : Graph) : Bool :=
  g.faces.all (fun f => decide (3 ≤ f.vertices.length ∧ f.vertices.length ≤ 6))

/-- `Tame.thy: tame10`. -/
def tame10 (g : Graph) : Bool :=
  decide (13 ≤ g.countVertices ∧ g.countVertices ≤ 15)

/-- `Tame.thy: tame10ub`. -/
def tame10ub (g : Graph) : Bool := decide (g.countVertices ≤ 15)

/-- `Tame.thy: tame11a`. -/
def tame11a (g : Graph) : Bool :=
  g.vertices.all (fun v => decide (3 ≤ degree g v))

/-- `Tame.thy: tame11b`. -/
def tame11b (g : Graph) : Bool :=
  g.vertices.all (fun v => decide (degree g v ≤ if except g v = 0 then 7 else 6))

/-- `Tame.thy: tame12o`. -/
def tame12o (g : Graph) : Bool :=
  g.vertices.all fun v =>
    if except g v ≠ 0 ∧ degree g v = 6 then decide (vertextype g v = (5, 0, 1))
    else true

/-- `Tame.thy: tame13a`. There exists an admissible weight assignment of total
weight less than the target. (`Prop`: quantifies over `Face → Nat`.) -/
def tame13a (g : Graph) : Prop :=
  ∃ w : Face → Nat, admissible w g ∧ (g.faces.map w).sum < squanderTarget

/-- Executable counterpart of `tame13a` for a weight witness `ws` given
positionally along `faces g`. -/
def tame13aCheck (ws : List Nat) (g : Graph) : Bool :=
  admissibleCheck ws g && decide (ws.sum < squanderTarget)

/-- `Tame.thy: tame`. -/
def tame (g : Graph) : Prop :=
  tame9a g ∧ tame10 g ∧ tame11a g ∧ tame11b g ∧ tame12o g ∧ tame13a g

end Kepler.Graphs
