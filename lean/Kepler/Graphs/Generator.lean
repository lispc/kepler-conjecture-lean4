/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `Generator.thy`.

Source: `reference/afp-flyspeck-tame/Generator.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

All arithmetic is on `Nat`, so subtractions (e.g. in `excessAtType`) are
truncated — exactly matching Isabelle's `nat` semantics.
-/
import Kepler.Graphs.Tame

namespace Kepler.Graphs

/-- `Generator.thy: faceSquanderLowerBound`. -/
def faceSquanderLowerBound (g : Graph) : Nat :=
  ((finals g).map (fun f => squanderFace f.vertices.length)).sum

/-- `Generator.thy: d3_const`. -/
def d3_const : Nat := squanderFace 3

/-- `Generator.thy: d4_const`. -/
def d4_const : Nat := squanderFace 4

/-- `Generator.thy: excessAtType`. The subtractions are truncated (`Nat`),
as in Isabelle. -/
def excessAtType (t q e : Nat) : Nat :=
  if e = 0 then
    if 7 < t + q then squanderTarget
    else squanderVertex t q - t * d3_const - q * d4_const
  else if t + q + e ≠ 6 then 0
  else if t = 5 then excessTCount
  else squanderTarget

/-- `Generator.thy: ExcessAt`. -/
def ExcessAt (g : Graph) (v : Vertex) : Nat :=
  if !finalVertex g v then 0
  else excessAtType (tri g v) (quad g v) (except g v)

/-- `Generator.thy: ExcessTable`, in the form of its `[code]` lemma
(`map_filter`), which is extensionally equal to the definition. -/
def ExcessTable (g : Graph) (vs : List Vertex) : List (Vertex × Nat) :=
  vs.filterMap fun v =>
    let e := ExcessAt g v
    if 0 < e then some (v, e) else none

/-- `Generator.thy: deleteAround`, in the form of its `[code]` lemma
(extensionally equal to the definition by `nextV2`). -/
def deleteAround (g : Graph) (v : Vertex) (ps : List (Vertex × Nat)) :
    List (Vertex × Nat) :=
  let ws := (g.facesAt v).flatMap fun f =>
    let n := f.nextVertex v
    if f.vertices.length = 4 then [n, f.nextVertex n] else [n]
  removeKeyList ws ps

/-- `Generator.thy: length_deleteAround`. -/
theorem length_deleteAround (g : Graph) (v : Vertex) (ps : List (Vertex × Nat)) :
    (deleteAround g v ps).length ≤ ps.length :=
  length_removeKeyList _ _

/-- `Generator.thy: ExcessNotAtRec`.

Isabelle defines this by well-founded recursion on the length of the list
(`termination by measure size`, using `length_deleteAround`). To keep the
function reducible by the Lean KERNEL (needed for `decide`-based checking;
`WellFounded.fix` does not reduce in the kernel), we define it via a
fuel-bounded structural recursion `ExcessNotAtRecAux` with
`fuel = length ps + 1`, and prove as theorems that it satisfies exactly the
Isabelle recursion equations (`ExcessNotAtRec_nil`, `ExcessNotAtRec_cons`). -/
def ExcessNotAtRecAux : Nat → List (Vertex × Nat) → Graph → Nat
  | 0, _, _ => 0
  | _ + 1, [], _ => 0
  | n + 1, (x, y) :: ps, g =>
    max (ExcessNotAtRecAux n ps g) (y + ExcessNotAtRecAux n (deleteAround g x ps) g)

/-- One-step unfolding of `ExcessNotAtRecAux`. -/
theorem ExcessNotAtRecAux_succ_cons (n : Nat) (x : Vertex) (y : Nat)
    (ps : List (Vertex × Nat)) (g : Graph) :
    ExcessNotAtRecAux (n + 1) ((x, y) :: ps) g =
      max (ExcessNotAtRecAux n ps g)
        (y + ExcessNotAtRecAux n (deleteAround g x ps) g) := rfl

/-- Fuel irrelevance: any two fuels `≥ length qs` give the same result. -/
theorem ExcessNotAtRecAux_eq (g : Graph) :
    ∀ (m n : Nat) (qs : List (Vertex × Nat)), qs.length ≤ m → qs.length ≤ n →
      ExcessNotAtRecAux m qs g = ExcessNotAtRecAux n qs g := by
  intro m
  induction m with
  | zero =>
    intro n qs hm _
    cases qs with
    | nil => cases n <;> rfl
    | cons p ps => simp at hm
  | succ m ih =>
    intro n qs hm hn
    cases n with
    | zero =>
      cases qs with
      | nil => rfl
      | cons p ps => simp at hn
    | succ n =>
      cases qs with
      | nil => rfl
      | cons p ps =>
        obtain ⟨x, y⟩ := p
        have hlen : ((x, y) :: ps).length = ps.length + 1 := rfl
        rw [hlen] at hm hn
        have hps := Nat.le_of_succ_le_succ hm
        have hpsn := Nat.le_of_succ_le_succ hn
        rw [ExcessNotAtRecAux_succ_cons m x y ps g,
            ExcessNotAtRecAux_succ_cons n x y ps g,
            ih n ps hps hpsn,
            ih n (deleteAround g x ps)
              (Nat.le_trans (length_deleteAround g x ps) hps)
              (Nat.le_trans (length_deleteAround g x ps) hpsn)]

/-- `Generator.thy: ExcessNotAtRec`. -/
def ExcessNotAtRec (qs : List (Vertex × Nat)) (g : Graph) : Nat :=
  ExcessNotAtRecAux (qs.length + 1) qs g

/-- The Isabelle equation `ExcessNotAtRec [] = (λg. 0)`. -/
theorem ExcessNotAtRec_nil (g : Graph) : ExcessNotAtRec [] g = 0 := rfl

/-- The Isabelle equation
`ExcessNotAtRec ((x,y)#ps) = (λg. max (ExcessNotAtRec ps g) (y + ExcessNotAtRec (deleteAround g x ps) g))`. -/
theorem ExcessNotAtRec_cons (x : Vertex) (y : Nat) (ps : List (Vertex × Nat)) (g : Graph) :
    ExcessNotAtRec ((x, y) :: ps) g =
      max (ExcessNotAtRec ps g) (y + ExcessNotAtRec (deleteAround g x ps) g) := by
  show ExcessNotAtRecAux (ps.length + 2) ((x, y) :: ps) g = _
  rw [ExcessNotAtRecAux_succ_cons (ps.length + 1) x y ps g,
      ExcessNotAtRecAux_eq g (ps.length + 1) ((deleteAround g x ps).length + 1)
        (deleteAround g x ps)
        (Nat.le_trans (length_deleteAround g x ps) (Nat.le_succ ps.length))
        (Nat.le_succ _)]
  rfl

/-- `Generator.thy: ExcessNotAt`. -/
def ExcessNotAt (g : Graph) (v_opt : Option Vertex) : Nat :=
  let ps := ExcessTable g g.vertices
  match v_opt with
  | none => ExcessNotAtRec ps g
  | some v => ExcessNotAtRec (deleteAround g v ps) g

/-- `Generator.thy: squanderLowerBound`. -/
def squanderLowerBound (g : Graph) : Nat :=
  faceSquanderLowerBound g + ExcessNotAt g none

/-- `Generator.thy: is_tame13a`. -/
def is_tame13a (g : Graph) : Bool := decide (squanderLowerBound g < squanderTarget)

/-- `Generator.thy: notame`. -/
def notame (g : Graph) : Bool := !(tame10ub g && tame11b g)

/-- `Generator.thy: notame7`. -/
def notame7 (g : Graph) : Bool := !(tame10ub g && tame11b g && is_tame13a g)

/-- `Generator.thy: generatePolygonTame`. -/
def generatePolygonTame (n : Nat) (v : Vertex) (f : Face) (g : Graph) : List Graph :=
  let enumeration := enum n f.vertices.length
  let enumeration := enumeration.filter (fun is => !containsDuplicateEdge g f v is)
  let vertexLists := enumeration.map (indexToVertexList f v)
  (vertexLists.map (subdivFace g f)).filter (fun g' => !notame g')

/-- `Generator.thy: polysizes`. -/
def polysizes (p : Nat) (g : Graph) : List Nat :=
  let lb := squanderLowerBound g
  (List.range' 3 (maxGon p - 2)).filter (fun n => decide (lb + squanderFace n < squanderTarget))

/-- `Generator.thy: next_tame0`. -/
def next_tame0 (p : Nat) (g : Graph) : List Graph :=
  let fs := nonFinals g
  if fs.isEmpty then []
  else
    let f := minimalFace fs
    let v := minimalVertex g f
    (polysizes p g).flatMap fun i => generatePolygonTame i v f g

end Kepler.Graphs
