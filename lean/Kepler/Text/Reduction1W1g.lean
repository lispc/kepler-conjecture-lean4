/-
  Kepler.Text.Reduction1W1g — J4 Wave W1 批 5b：`dart_neighbors`
  （`reduction1.hl:220-:286`）。装配链见文件末注。
  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction1W1f
import Kepler.Text.TameCorrList
import Kepler.Graphs.FaceDivisionProps2

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (listOfDarts listPairs)
open Kepler.Graphs (fgraph Graph Face Vertex neighbors is_nextElem is_nextElem_a
  is_nextElem_edges_eq)
open Kepler.Text.TameCorrList (GoodFacesV3 VerticesSet2Eq verticesSet2 facesAtV2)

/-- HOL `dart_neighbors` 的**第一半**（`v ∈ verticesSet2 g` 侧）：
`w ∈ neighbors g v ↔ (v,w) ∈ list_of_darts (fgraph g)`。

装配链：
`neighbors` def → `facesAt`（经 `GoodFacesV3` 的 Perm 换到 `faces.filter`）→
`Face.edges`（定义体）→ `is_nextElem_edges_eq` → `listPairsIsNextElem`（`3d27ec9d`）
→ `listOfDarts`/`fgraph` def。 -/
theorem memNeighborsIffDarts {g : Graph} {v w : Vertex}
    (hun : ∀ l ∈ g.fgraph, l.Nodup) (hgf : GoodFacesV3 g)
    (hv : v ∈ verticesSet2 g) :
    w ∈ neighbors g v ↔ (v, w) ∈ listOfDarts g.fgraph := by
  have hface : ∀ f, f ∈ g.facesAt v ↔ f ∈ g.faces.filter (fun f => v ∈ f.vertices) := by
    intro f
    exact ((hgf v hv).mem_iff).symm
  have hnod : ∀ f ∈ g.faces, f.vertices.Nodup := by
    intro f hf
    exact hun f.vertices (by
      show f.vertices ∈ g.faces.map Face.vertices
      exact List.mem_map.mpr ⟨f, hf, rfl⟩)
  have h1 : w ∈ neighbors g v ↔ ∃ f ∈ g.facesAt v, f.nextVertex v = w := by
    simp [Kepler.Graphs.neighbors, List.mem_map]
  have h2 : (v, w) ∈ listOfDarts g.fgraph ↔
      ∃ f ∈ g.faces, (v, w) ∈ listPairs f.vertices := by
    simp only [Kepler.Assembly.listOfDarts, Kepler.Graphs.Graph.fgraph,
      List.mem_flatten, List.mem_map]
    constructor
    · rintro ⟨l, ⟨m, ⟨f, hf, rfl⟩, rfl⟩, hd⟩
      exact ⟨f, hf, hd⟩
    · rintro ⟨f, hf, hd⟩
      exact ⟨listPairs f.vertices, ⟨f.vertices, ⟨f, hf, rfl⟩, rfl⟩, hd⟩
  rw [h1, h2]
  constructor
  · rintro ⟨f, hf, hnext⟩
    rw [hface] at hf
    obtain ⟨hff, hfv⟩ := List.mem_filter.mp hf
    refine ⟨f, hff, (listPairsIsNextElem f.vertices v w).mpr ?_⟩
    exact (is_nextElem_edges_eq (hnod f hff)).mp (by
      show v ∈ f.vertices ∧ f.nextVertex v = w
      exact ⟨of_decide_eq_true hfv, hnext⟩)
  · rintro ⟨f, hf, hd⟩
    have his : is_nextElem f.vertices v w := (listPairsIsNextElem f.vertices v w).mp hd
    have hnv : v ∈ f.vertices := is_nextElem_a his
    have hedge : (v, w) ∈ f.edges := (is_nextElem_edges_eq (hnod f hf)).mpr his
    have hnxt : f.nextVertex v = w := by
      have h := hedge
      simp only [Kepler.Graphs.Face.edges, Set.mem_setOf_eq] at h
      exact h.2
    refine ⟨f, ?_, hnxt⟩
    rw [hface]
    exact List.mem_filter.mpr ⟨hf, decide_eq_true hnv⟩

/-- HOL `dart_neighbors` 的**第二半**：dart 成员性蕴含 `v ∈ verticesSet2 g`
（`VerticesSet2Eq` 反推）。 -/
theorem vertexMemOfDarts {g : Graph} {v w : Vertex} (hvs : VerticesSet2Eq g)
    (hd : (v, w) ∈ listOfDarts g.fgraph) : v ∈ verticesSet2 g := by
  rw [hvs]
  have h2 : ∃ f ∈ g.faces, (v, w) ∈ listPairs f.vertices := by
    simp only [Kepler.Assembly.listOfDarts, Kepler.Graphs.Graph.fgraph,
      List.mem_flatten, List.mem_map] at hd
    obtain ⟨l, ⟨m, ⟨f, hf, rfl⟩, rfl⟩, hl⟩ := hd
    exact ⟨f, hf, hl⟩
  obtain ⟨f, hf, hl⟩ := h2
  simp only [Kepler.Text.TameLp.elementsOfList, Kepler.Text.TameLp.listOfElements,
    Kepler.Graphs.Graph.fgraph, Set.mem_setOf_eq]
  exact List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨f.vertices,
    List.mem_map.mpr ⟨f, hf, rfl⟩,
    is_nextElem_a ((listPairsIsNextElem f.vertices v w).mp hl)⟩)

/-- **HOL `dart_neighbors`**（`reduction1.hl:220-:286`）逐槽折算：
`all uniq (fgraph g) ∧ good_faces_v3 g ∧ vertices_set2 g = elements_of_list (fgraph g) →
 (v ∈ vertices_set2 g ∧ w ∈ set_of_list (neighbors g v) ↔ MEM (v,w) (list_of_darts (fgraph g)))` -/
theorem dartNeighbors {g : Graph} {w v : Vertex}
    (hun : ∀ l ∈ g.fgraph, l.Nodup) (hgf : GoodFacesV3 g) (hvs : VerticesSet2Eq g) :
    (v ∈ verticesSet2 g ∧ w ∈ neighbors g v) ↔ (v, w) ∈ listOfDarts g.fgraph := by
  constructor
  · rintro ⟨hv, hw⟩
    exact (memNeighborsIffDarts hun hgf hv).mp hw
  · intro hd
    exact ⟨vertexMemOfDarts hvs hd, (memNeighborsIffDarts hun hgf
      (vertexMemOfDarts hvs hd)).mpr hd⟩

end Kepler.Text.Reduction1

/-! 公理审计锚 -/
#print axioms Kepler.Text.Reduction1.dartNeighbors
