/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `FaceDivision.thy`.

Source: `reference/afp-flyspeck-tame/FaceDivision.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).
-/
import Kepler.Graphs.Graph

namespace Kepler.Graphs

/-- `FaceDivision.thy: split_face`. -/
def split_face (f : Face) (ram₁ ram₂ : Vertex) (newVs : List Vertex) : Face × Face :=
  let vs := f.vertices
  let f₁ := [ram₁] ++ between vs ram₁ ram₂ ++ [ram₂]
  let f₂ := [ram₂] ++ between vs ram₂ ram₁ ++ [ram₁]
  (Face.mk (newVs.reverse ++ f₁) false, Face.mk (f₂ ++ newVs) false)

/-- `FaceDivision.thy: replacefacesAt`. -/
def replacefacesAt (ns : List Nat) (f : Face) (fs : List Face)
    (F : List (List Face)) : List (List Face) :=
  mapAt ns (replace f fs) F

/-- `FaceDivision.thy: makeFaceFinalFaceList`. -/
def makeFaceFinalFaceList (f : Face) (fs : List Face) : List Face :=
  replace f [setFinal f] fs

/-- `FaceDivision.thy: makeFaceFinal`. -/
def makeFaceFinal (f : Face) (g : Graph) : Graph :=
  ⟨makeFaceFinalFaceList f g.faces,
   g.countVertices,
   g.faceListAt.map (makeFaceFinalFaceList f),
   g.heights⟩

/-- `FaceDivision.thy: heightsNewVertices`. -/
def heightsNewVertices (h₁ h₂ n : Nat) : List Nat :=
  (List.range n).map (fun i => min (h₁ + i + 1) (h₂ + n - i))

/-- `FaceDivision.thy: splitFace`. `h ! ramᵢ` ↦ `h.getD ramᵢ 0`
(`ramᵢ < countVertices g = h.length` in the generator). -/
def splitFace (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face) (newVs : List Vertex) :
    Face × Face × Graph :=
  let fs := g.faces
  let n := g.countVertices
  let h := g.heights
  let vs₁ := between oldF.vertices ram₁ ram₂
  let vs₂ := between oldF.vertices ram₂ ram₁
  let (f₁, f₂) := split_face oldF ram₁ ram₂ newVs
  let Fs := replacefacesAt vs₁ oldF [f₁] g.faceListAt
  let Fs := replacefacesAt vs₂ oldF [f₂] Fs
  let Fs := replacefacesAt [ram₁] oldF [f₂, f₁] Fs
  let Fs := replacefacesAt [ram₂] oldF [f₁, f₂] Fs
  let Fs := Fs ++ List.replicate newVs.length [f₁, f₂]
  (f₁, f₂,
   ⟨replace oldF [f₂] fs ++ [f₁],
    n + newVs.length,
    Fs,
    h ++ heightsNewVertices (h.getD ram₁ 0) (h.getD ram₂ 0) newVs.length⟩)

/-- `FaceDivision.thy: subdivFace'`. -/
def subdivFace' (g : Graph) (f : Face) (u : Vertex) (n : Nat) :
    List (Option Vertex) → Graph
  | [] => makeFaceFinal f g
  | vo :: vos =>
    match vo with
    | none => subdivFace' g f u (n + 1) vos
    | some v =>
      if f.nextVertex u == v && n == 0 then
        subdivFace' g f v 0 vos
      else
        let ws := List.range' g.countVertices n
        let (_, f₂, g') := splitFace g u v f ws
        subdivFace' g' f₂ v 0 vos

/-- `FaceDivision.thy: subdivFace`. `the (hd vos)` ↦ `vos.head!.get!`;
`vos` produced by `indexToVertexList` is always nonempty with `Some` head. -/
def subdivFace (g : Graph) (f : Face) (vos : List (Option Vertex)) : Graph :=
  subdivFace' g f vos.head!.get! 0 vos.tail

end Kepler.Graphs
