/-
Port of block A (lines 1–715) of the Isabelle AFP "Flyspeck-Tame" theory
`Invariants.thy`.

Source: `reference/afp-flyspeck-tame/Invariants.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Conventions follow `FaceDivisionProps*.lean`: set equality / emptiness of an
intersection are rendered as membership (non-)implications; `distinct` ↦
`List.Nodup`; `f ∈ ℱ g` ↦ `f ∈ g.faces`, `v ∈ 𝒱 f` ↦ `v ∈ f.vertices`,
`v ∈ 𝒱 g` ↦ `v ∈ g.vertices`, `f ∈ set (facesAt g v)` ↦ `f ∈ g.facesAt v`;
`final f` / `¬ final f` ↦ `f.final = true` / `f.final = false`.
-/
import Kepler.Graphs.FaceDivisionProps4
import Kepler.Graphs.Plane

namespace Kepler.Graphs

/-! ### Rotation of face into normal form -/

section NormFaceDefs

/-- Invariants.thy: minVertex -/
def minVertex (f : Face) : Vertex := min_list f.vertices

/-- Invariants.thy: normFace -/
def normFace (f : Face) : List Vertex := verticesFrom f (minVertex f)

/-- Invariants.thy: normFaces -/
def normFaces (fl : List Face) : List (List Vertex) := fl.map normFace

/-- Invariants.thy: normFaces_distinct -/
theorem normFaces_distinct {fl : List Face} (h : (normFaces fl).Nodup) : fl.Nodup := by
  induction fl with
  | nil => exact List.nodup_nil
  | cons f fs ih =>
    simp only [normFaces, List.map_cons, List.nodup_cons] at h ⊢
    exact ⟨fun hf => h.1 (List.mem_map.mpr ⟨f, hf, rfl⟩), ih h.2⟩

end NormFaceDefs

/-! ### Minimal (plane) graph properties -/

section MinGraphProps

/-- Invariants.thy: minGraphProps' -/
def minGraphProps' (g : Graph) : Prop :=
  ∀ f ∈ g.faces, 2 < f.vertices.length ∧ f.vertices.Nodup

/-- Invariants.thy: edges_sym -/
def edges_sym (g : Graph) : Prop :=
  ∀ a b, (a, b) ∈ g.edges → (b, a) ∈ g.edges

/-- Invariants.thy: faceListAt_len -/
def faceListAt_len (g : Graph) : Prop :=
  g.faceListAt.length = g.countVertices

/-- Invariants.thy: facesAt_eq (membership form of the set equality) -/
def facesAt_eq (g : Graph) : Prop :=
  ∀ v ∈ g.vertices, ∀ f, f ∈ g.facesAt v ↔ f ∈ g.faces ∧ v ∈ f.vertices

/-- Invariants.thy: facesAt_distinct -/
def facesAt_distinct (g : Graph) : Prop :=
  ∀ v ∈ g.vertices, (normFaces (g.facesAt v)).Nodup

/-- Invariants.thy: faces_distinct -/
def faces_distinct (g : Graph) : Prop :=
  (normFaces g.faces).Nodup

/-- Invariants.thy: faces_subset (membership form of the inclusion) -/
def faces_subset (g : Graph) : Prop :=
  ∀ f ∈ g.faces, ∀ v ∈ f.vertices, v ∈ g.vertices

/-- Invariants.thy: edges_disj (membership form of the empty intersection) -/
def edges_disj (g : Graph) : Prop :=
  ∀ f ∈ g.faces, ∀ f' ∈ g.faces, f ≠ f' → ∀ e ∈ f.edges, e ∉ f'.edges

/-- Invariants.thy: face_face_op (membership form of `ℰ f ≠ (ℰ f')⁻¹`) -/
def face_face_op (g : Graph) : Prop :=
  g.faces.length ≠ 2 →
    ∀ f ∈ g.faces, ∀ f' ∈ g.faces, f ≠ f' →
      ∃ e : Vertex × Vertex,
        (e ∈ f.edges ∧ (e.2, e.1) ∉ f'.edges) ∨ (e ∉ f.edges ∧ (e.2, e.1) ∈ f'.edges)

/-- Invariants.thy: one_final_but -/
def one_final_but (g : Graph) (E : Set (Vertex × Vertex)) : Prop :=
  ∀ f ∈ g.faces, f.final = false →
    ∀ a b : Vertex, (a, b) ∈ f.edges → (a, b) ∉ E →
      (b, a) ∈ E ∨ ∃ f' ∈ g.faces, f'.final = true ∧ (b, a) ∈ f'.edges

/-- Invariants.thy: one_final -/
def one_final (g : Graph) : Prop := one_final_but g ∅

/-- Invariants.thy: minGraphProps -/
def minGraphProps (g : Graph) : Prop :=
  minGraphProps' g ∧ facesAt_eq g ∧ faceListAt_len g ∧ facesAt_distinct g ∧
    faces_distinct g ∧ faces_subset g ∧ edges_sym g ∧ edges_disj g ∧ face_face_op g

/-- Invariants.thy: inv -/
def inv (g : Graph) : Prop :=
  minGraphProps g ∧ one_final g ∧ 2 ≤ g.faces.length

/-- Invariants.thy: facesAt_distinctI -/
theorem facesAt_distinctI {g : Graph}
    (h : ∀ v ∈ g.vertices, (normFaces (g.facesAt v)).Nodup) : facesAt_distinct g :=
  h

/-- Invariants.thy: minGraphProps2 -/
theorem minGraphProps2 {g : Graph} {f : Face} (h : minGraphProps g)
    (hf : f ∈ g.faces) : 2 < f.vertices.length :=
  (h.1 f hf).1

/-- Invariants.thy: mgp_vertices3 -/
theorem mgp_vertices3 {g : Graph} {f : Face} (h : minGraphProps g)
    (hf : f ∈ g.faces) : 3 ≤ f.vertices.length :=
  minGraphProps2 h hf

/-- Invariants.thy: mgp_vertices_nonempty -/
theorem mgp_vertices_nonempty {g : Graph} {f : Face} (h : minGraphProps g)
    (hf : f ∈ g.faces) : f.vertices ≠ [] :=
  List.ne_nil_of_length_pos (by have := minGraphProps2 h hf; omega)

/-- Invariants.thy: minGraphProps3 -/
theorem minGraphProps3 {g : Graph} {f : Face} (h : minGraphProps g)
    (hf : f ∈ g.faces) : f.vertices.Nodup :=
  (h.1 f hf).2

/-- Invariants.thy: minGraphProps4 -/
theorem minGraphProps4 {g : Graph} (h : minGraphProps g) :
    g.faceListAt.length = g.countVertices :=
  h.2.2.1

/-- Invariants.thy: minGraphProps5 -/
theorem minGraphProps5 {g : Graph} {v : Vertex} {f : Face} (h : minGraphProps g)
    (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) : f ∈ g.faces :=
  ((h.2.1 v hv f).mp hf).1

/-- Invariants.thy: minGraphProps6 -/
theorem minGraphProps6 {g : Graph} {v : Vertex} {f : Face} (h : minGraphProps g)
    (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) : v ∈ f.vertices :=
  ((h.2.1 v hv f).mp hf).2

/-- Invariants.thy: minGraphProps9 -/
theorem minGraphProps9 {g : Graph} {f : Face} {v : Vertex} (h : minGraphProps g)
    (hf : f ∈ g.faces) (hv : v ∈ f.vertices) : v ∈ g.vertices :=
  h.2.2.2.2.2.1 f hf v hv

/-- Invariants.thy: minGraphProps7 -/
theorem minGraphProps7 {g : Graph} {f : Face} {v : Vertex} (h : minGraphProps g)
    (hf : f ∈ g.faces) (hv : v ∈ f.vertices) : f ∈ g.facesAt v :=
  (h.2.1 v (minGraphProps9 h hf hv) f).mpr ⟨hf, hv⟩

/-- Invariants.thy: minGraphProps_facesAt_eq -/
theorem minGraphProps_facesAt_eq {g : Graph} {v : Vertex} (h : minGraphProps g)
    (hv : v ∈ g.vertices) :
    {f | f ∈ g.facesAt v} = {f | f ∈ g.faces ∧ v ∈ f.vertices} :=
  Set.ext fun f => h.2.1 v hv f

/-- Invariants.thy: mgp_dist_facesAt -/
@[simp]
theorem mgp_dist_facesAt {g : Graph} {v : Vertex} (h : minGraphProps g)
    (hv : v ∈ g.vertices) : (g.facesAt v).Nodup :=
  normFaces_distinct (h.2.2.2.1 v hv)

/-- Invariants.thy: minGraphProps8 -/
theorem minGraphProps8 {g : Graph} {v : Vertex} (h : minGraphProps g)
    (hv : v ∈ g.vertices) : (normFaces (g.facesAt v)).Nodup :=
  h.2.2.2.1 v hv

/-- Invariants.thy: minGraphProps8a -/
theorem minGraphProps8a {g : Graph} {v : Vertex} (h : minGraphProps g)
    (hv : v ∈ g.vertices) : (normFaces (g.faceListAt[v]!)).Nodup := by
  have hlt : v < g.faceListAt.length := by
    rw [minGraphProps4 h]
    exact List.mem_range.mp hv
  rw [getElem!_pos g.faceListAt v hlt]
  have hd : g.facesAt v = g.faceListAt[v] := (List.getElem_eq_getD []).symm
  rw [← hd]
  exact minGraphProps8 h hv

/-- Invariants.thy: minGraphProps8a' -/
theorem minGraphProps8a' {g : Graph} {v : Vertex} (h : minGraphProps g)
    (hv : v < g.countVertices) : (normFaces (g.faceListAt[v]!)).Nodup :=
  minGraphProps8a h (List.mem_range.mpr hv)

/-- Invariants.thy: minGraphProps9' -/
theorem minGraphProps9' {g : Graph} {f : Face} {v : Vertex} (h : minGraphProps g)
    (hf : f ∈ g.faces) (hv : v ∈ f.vertices) : v < g.countVertices :=
  List.mem_range.mp (minGraphProps9 h hf hv)

/-- Invariants.thy: minGraphProps10 -/
theorem minGraphProps10 {g : Graph} {a b : Vertex} (h : minGraphProps g)
    (hab : (a, b) ∈ g.edges) : (b, a) ∈ g.edges :=
  h.2.2.2.2.2.2.1 a b hab

/-- Invariants.thy: minGraphProps11 -/
theorem minGraphProps11 {g : Graph} (h : minGraphProps g) :
    (normFaces g.faces).Nodup :=
  h.2.2.2.2.1

/-- Invariants.thy: minGraphProps11' -/
theorem minGraphProps11' {g : Graph} (h : minGraphProps g) : g.faces.Nodup :=
  normFaces_distinct (minGraphProps11 h)

/-- Invariants.thy: minGraphProps12 -/
theorem minGraphProps12 {g : Graph} {f : Face} {a b : Vertex} (h : minGraphProps g)
    (hf : f ∈ g.faces) (hab : (a, b) ∈ f.edges) : (b, a) ∉ f.edges := by
  intro hba
  have hd : f.vertices.Nodup := minGraphProps3 h hf
  have hlen : 2 < f.vertices.length := minGraphProps2 h hf
  have hab' : is_nextElem f.vertices a b := (is_nextElem_edges_eq hd).mp hab
  have hba' : is_nextElem f.vertices b a := (is_nextElem_edges_eq hd).mp hba
  have e1 : f.nextVertex a = b := is_nextElem2 hd (is_nextElem_a hab') hab'
  have e2 : f.nextVertex b = a := is_nextElem2 hd (is_nextElem_a hba') hba'
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem (is_nextElem_a hab')
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem (is_nextElem_a hba')
  have hia' : f.vertices[i]! = a := by rw [getElem!_pos f.vertices i hi]; exact hia
  have hjb' : f.vertices[j]! = b := by rw [getElem!_pos f.vertices j hj]; exact hjb
  have hn : 0 < f.vertices.length := by omega
  -- The successor of `f.vertices[k]!` sits at index `k + 1` (mod the length).
  have step : ∀ x y : Vertex, ∀ k : Nat, k < f.vertices.length →
      f.vertices[k]! = x → f.nextVertex x = y →
      (k + 1 < f.vertices.length ∧ y = f.vertices[k + 1]!) ∨
        (k + 1 = f.vertices.length ∧ y = f.vertices[0]!) := by
    intro x y k hk hxk ex
    by_cases hlast : f.vertices.getLast! = x
    · refine Or.inr ⟨?_, ?_⟩
      · have e : f.vertices[k]! = f.vertices[f.vertices.length - 1]! := by
          rw [hxk, ← hlast, List.getLast!_eq_getElem!]
        have kk : k = f.vertices.length - 1 :=
          (List.getElem!_inj hk (by omega) hd).mp e
        omega
      · rw [← ex, ← hlast]
        show nextElem f.vertices f.vertices.head! f.vertices.getLast! = _
        rw [nextElem_last hd, List.head!_eq_getElem!]
    · have hk1 : k + 1 < f.vertices.length := by
        by_contra hc
        have kk : k = f.vertices.length - 1 := by omega
        apply hlast
        rw [List.getLast!_eq_getElem!, ← kk]
        exact hxk
      exact Or.inl ⟨hk1, by
        rw [← ex]
        show nextElem f.vertices f.vertices.head! x = _
        exact nextElem_eq_getElem!_succ_of_Nodup hd hk hlast hxk⟩
  obtain ⟨hi1, eb⟩ | ⟨hi1, eb⟩ := step a b i hi hia' e1
  · have hj' : j = i + 1 := (List.getElem!_inj hj hi1 hd).mp (hjb'.trans eb)
    obtain ⟨hj1, ea⟩ | ⟨hj1, ea⟩ := step b a j hj hjb' e2
    · have hh : i = j + 1 := (List.getElem!_inj hi hj1 hd).mp (hia'.trans ea)
      omega
    · have hh : i = 0 := (List.getElem!_inj hi hn hd).mp (hia'.trans ea)
      omega
  · have hj' : j = 0 := (List.getElem!_inj hj hn hd).mp (hjb'.trans eb)
    obtain ⟨hj1, ea⟩ | ⟨hj1, ea⟩ := step b a j hj hjb' e2
    · have hh : i = j + 1 := (List.getElem!_inj hi hj1 hd).mp (hia'.trans ea)
      omega
    · omega

/-- Invariants.thy: minGraphProps7' -/
theorem minGraphProps7' {g : Graph} {f : Face} {v : Vertex} (h : minGraphProps g)
    (hf : f ∈ g.faces) (hv : v ∈ f.vertices) : f ∈ g.faceListAt[v]! := by
  have hlt : v < g.faceListAt.length := by
    rw [minGraphProps4 h]
    exact minGraphProps9' h hf hv
  rw [getElem!_pos g.faceListAt v hlt, List.getElem_eq_getD []]
  exact minGraphProps7 h hf hv

/-- Invariants.thy: mgp_edges_disj -/
theorem mgp_edges_disj {g : Graph} {f f' : Face} {uv : Vertex × Vertex}
    (h : minGraphProps g) (hne : f ≠ f') (hf : f ∈ g.faces) (hf' : f' ∈ g.faces)
    (huv : uv ∈ f.edges) : uv ∉ f'.edges :=
  h.2.2.2.2.2.2.2.1 f hf f' hf' hne uv huv

/-- Invariants.thy: one_final_but_antimono -/
theorem one_final_but_antimono {g : Graph} {E E' : Set (Vertex × Vertex)}
    (h : one_final_but g E) (hsub : E ⊆ E') : one_final_but g E' := by
  intro f hf hfin a b hab hnot
  rcases h f hf hfin a b hab (fun he => hnot (hsub he)) with he | hr
  · exact Or.inl (hsub he)
  · exact Or.inr hr

/-- Invariants.thy: one_final_antimono -/
theorem one_final_antimono {g : Graph} {E : Set (Vertex × Vertex)}
    (h : one_final g) : one_final_but g E :=
  one_final_but_antimono h (Set.empty_subset E)

/-- Invariants.thy: inv_two_faces -/
theorem inv_two_faces {g : Graph} (h : inv g) : 2 ≤ g.faces.length :=
  h.2.2

/-- Invariants.thy: inv_mgp -/
@[simp]
theorem inv_mgp {g : Graph} (h : inv g) : minGraphProps g :=
  h.1

/-- Invariants.thy: makeFaceFinal_id -/
@[simp]
theorem makeFaceFinal_id {f : Face} {g : Graph} (hf : f.final = true) :
    makeFaceFinal f g = g := by
  obtain ⟨fs, n, F, hh⟩ := g
  have hsf : setFinal f = f := (setFinal_eq_iff f).mpr hf
  have hmc : makeFaceFinalFaceList f = id := by
    funext x
    show replace f [setFinal f] x = x
    rw [hsf, replace_id]
  show (⟨makeFaceFinalFaceList f fs, n, F.map (makeFaceFinalFaceList f), hh⟩ : Graph) =
    ⟨fs, n, F, hh⟩
  rw [hmc]
  simp

/-- Invariants.thy: inv_one_finalD' -/
theorem inv_one_finalD' {g : Graph} {f : Face} {a b : Vertex} (h : inv g)
    (hf : f ∈ g.faces) (hfin : f.final = false) (hab : (a, b) ∈ f.edges) :
    ∃ f' ∈ g.faces, f'.final = true ∧ f' ≠ f ∧ (b, a) ∈ f'.edges := by
  rcases h.2.1 f hf hfin a b hab (by simp) with he | ⟨f', hf', hfin', hed⟩
  · simp at he
  · refine ⟨f', hf', hfin', ?_, hed⟩
    intro e
    subst e
    simp [hfin] at hfin'

/-- Invariants.thy: mgp_no_loop -/
@[simp]
theorem mgp_no_loop {g : Graph} {f : Face} {v : Vertex} (h : minGraphProps g)
    (hf : f ∈ g.faces) (hv : v ∈ f.vertices) : f.nextVertex v ≠ v :=
  distinct_no_loop1 (minGraphProps3 h hf) hv (by have := minGraphProps2 h hf; omega)

/-- Invariants.thy: mgp_facesAt_no_loop -/
theorem mgp_facesAt_no_loop {g : Graph} {v : Vertex} {f : Face} (h : minGraphProps g)
    (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) : f.nextVertex v ≠ v :=
  mgp_no_loop h (minGraphProps5 h hv hf) (minGraphProps6 h hv hf)

/-- Invariants.thy: edge_pres_faceAt -/
theorem edge_pres_faceAt {g : Graph} {u v : Vertex} {f : Face} (h : minGraphProps g)
    (hu : u ∈ g.vertices) (hf : f ∈ g.facesAt u) (huv : (u, v) ∈ f.edges) :
    f ∈ g.facesAt v :=
  minGraphProps7 h (minGraphProps5 h hu hf) (in_edges_in_vertices huv).2

/-- Invariants.thy: in_facesAt_nextVertex -/
theorem in_facesAt_nextVertex {g : Graph} {v : Vertex} {f : Face} (h : minGraphProps g)
    (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) : f ∈ g.facesAt (f.nextVertex v) :=
  edge_pres_faceAt h hv hf (nextVertex_in_edges (minGraphProps6 h hv hf))

/-- Invariants.thy: mgp_edge_face_ex -/
theorem mgp_edge_face_ex {g : Graph} {u v : Vertex} {f : Face} (h : minGraphProps g)
    (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) (huv : (u, v) ∈ f.edges) :
    ∃ f' ∈ g.facesAt v, (v, u) ∈ f'.edges := by
  have hfg : f ∈ g.faces := minGraphProps5 h hv hf
  have hg : (u, v) ∈ g.edges := ⟨f, hfg, huv⟩
  obtain ⟨f', hf', hvu⟩ := minGraphProps10 h hg
  exact ⟨f', minGraphProps7 h hf' (in_edges_in_vertices hvu).1, hvu⟩

/-- Invariants.thy: nextVertex_in_graph -/
theorem nextVertex_in_graph {g : Graph} {v : Vertex} {f : Face} (h : minGraphProps g)
    (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) : f.nextVertex v ∈ g.vertices :=
  minGraphProps9 h (minGraphProps5 h hv hf) (nextVertex_in_face (minGraphProps6 h hv hf))

/-- Invariants.thy: mgp_nextVertex_face_ex2 -/
theorem mgp_nextVertex_face_ex2 {g : Graph} {v : Vertex} {f : Face}
    (h : minGraphProps g) (hv : v ∈ g.vertices) (hf : f ∈ g.facesAt v) :
    ∃ f' ∈ g.facesAt (f.nextVertex v), f'.nextVertex (f.nextVertex v) = v := by
  have hvf : v ∈ f.vertices := minGraphProps6 h hv hf
  obtain ⟨f', hf', huv⟩ := mgp_edge_face_ex h (nextVertex_in_graph h hv hf)
    (in_facesAt_nextVertex h hv hf) (nextVertex_in_edges hvf)
  exact ⟨f', hf', (edges_face_eq.mp huv).1⟩

/-- Invariants.thy: inv_finals_nonempty -/
theorem inv_finals_nonempty {g : Graph} (h : inv g) : finals g ≠ [] := by
  intro hf
  have hmg : minGraphProps g := h.1
  have hlen : 2 ≤ g.faces.length := h.2.2
  obtain ⟨f, fs, hfs⟩ : ∃ f fs, g.faces = f :: fs := by
    cases hfc : g.faces with
    | nil => rw [hfc] at hlen; simp at hlen
    | cons f fs => exact ⟨f, fs, rfl⟩
  have hfmem : f ∈ g.faces := by rw [hfs]; exact List.mem_cons_self
  have hfn : f.final = false := by
    by_contra hc
    have hft : f.final = true := by revert hc; cases f.final <;> simp
    have hm : f ∈ finals g := List.mem_filter.mpr ⟨hfmem, hft⟩
    rw [hf] at hm
    exact List.not_mem_nil hm
  have hvne : f.vertices ≠ [] := mgp_vertices_nonempty hmg hfmem
  obtain ⟨v, hvf⟩ : ∃ v, v ∈ f.vertices := by
    cases hv : f.vertices with
    | nil => exact absurd hv hvne
    | cons v vs => exact ⟨v, List.mem_cons_self⟩
  obtain ⟨f', hf'mem, hfin', -, -⟩ := inv_one_finalD' h hfmem hfn (nextVertex_in_edges hvf)
  have hm : f' ∈ finals g := List.mem_filter.mpr ⟨hf'mem, hfin'⟩
  rw [hf] at hm
  exact List.not_mem_nil hm

end MinGraphProps

/-! ### containsDuplicateEdge -/

section ContainsDuplicateEdge

/-- Invariants.thy: containsUnacceptableEdgeSnd' -/
def containsUnacceptableEdgeSnd' (N : Nat → Nat → Bool) (is : List Nat) : Prop :=
  ∃ k : Nat, k < is.length - 2 ∧
    N is[k + 1]! is[k + 2]! = true ∧ is[k]! < is[k + 1]! ∧ is[k + 1]! < is[k + 2]!

/-- Invariants.thy: containsUnacceptableEdgeSnd_eq -/
theorem containsUnacceptableEdgeSnd_eq (N : Nat → Nat → Bool) (v : Nat) (is : List Nat) :
    containsUnacceptableEdgeSnd N v is = true ↔ containsUnacceptableEdgeSnd' N (v :: is) := by
  induction is generalizing v with
  | nil => simp [containsUnacceptableEdgeSnd, containsUnacceptableEdgeSnd']
  | cons i is ih =>
    cases is with
    | nil => simp [containsUnacceptableEdgeSnd, containsUnacceptableEdgeSnd']
    | cons i' is' =>
      show (if v < i ∧ i < i' ∧ N i i' = true then (true : Bool)
            else containsUnacceptableEdgeSnd N i (i' :: is')) = true ↔
        containsUnacceptableEdgeSnd' N (v :: i :: i' :: is')
      by_cases hc : v < i ∧ i < i' ∧ N i i' = true
      · rw [if_pos hc]
        constructor
        · intro _
          refine ⟨0, by simp, ?_, ?_, ?_⟩
          · show N i i' = true
            exact hc.2.2
          · show (v :: i :: i' :: is')[0]! < (v :: i :: i' :: is')[1]!
            simpa using hc.1
          · show (v :: i :: i' :: is')[1]! < (v :: i :: i' :: is')[2]!
            simpa using hc.2.1
        · intro _
          rfl
      · rw [if_neg hc, ih]
        constructor
        · rintro ⟨k, hk, hN, h1, h2⟩
          refine ⟨k + 1, by simp only [List.length_cons] at hk ⊢; omega, ?_, ?_, ?_⟩
          · simpa only [List.getElem!_cons_succ] using hN
          · simpa only [List.getElem!_cons_succ] using h1
          · simpa only [List.getElem!_cons_succ] using h2
        · rintro ⟨k, hk, hN, h1, h2⟩
          cases k with
          | zero =>
            simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at hN h1 h2
            exact absurd ⟨h1, h2, hN⟩ hc
          | succ k' =>
            refine ⟨k', by simp only [List.length_cons] at hk ⊢; omega, ?_, ?_, ?_⟩
            · simpa only [List.getElem!_cons_succ] using hN
            · simpa only [List.getElem!_cons_succ] using h1
            · simpa only [List.getElem!_cons_succ] using h2

/-- Plane.thy: containsDuplicateEdge' (ported here for the equivalence lemmas of
Invariants.thy; Isabelle's Boolean coercions are rendered as `= true`). -/
def containsDuplicateEdge' (g : Graph) (f : Face) (v : Vertex) (is : List Nat) : Prop :=
  2 ≤ is.length ∧
    ((∃ k : Nat, k < is.length - 2 ∧
        duplicateEdge g f (f.nextVertices is[k + 1]! v) (f.nextVertices is[k + 2]! v) = true ∧
        is[k]! < is[k + 1]! ∧ is[k + 1]! < is[k + 2]!) ∨
      (duplicateEdge g f (f.nextVertices is[0]! v) (f.nextVertices is[1]! v) = true ∧
        is[0]! < is[1]!))

/-- Invariants.thy: containsDuplicateEdge_eq1 -/
theorem containsDuplicateEdge_eq1 (g : Graph) (f : Face) (v : Vertex) (is : List Nat) :
    containsDuplicateEdge g f v is = true ↔ containsDuplicateEdge' g f v is := by
  cases is with
  | nil => simp [containsDuplicateEdge, containsUnacceptableEdge, containsDuplicateEdge']
  | cons a is =>
    cases is with
    | nil => simp [containsDuplicateEdge, containsUnacceptableEdge, containsDuplicateEdge']
    | cons aa lista =>
      simp only [containsDuplicateEdge, containsUnacceptableEdge]
      by_cases hc : a < aa ∧
          duplicateEdge g f (f.nextVertices a v) (f.nextVertices aa v) = true
      · rw [if_pos hc]
        constructor
        · intro _
          refine ⟨by simp, Or.inr ⟨?_, ?_⟩⟩
          · show duplicateEdge g f (f.nextVertices (a :: aa :: lista)[0]! v)
                (f.nextVertices (a :: aa :: lista)[1]! v) = true
            simpa using hc.2
          · show (a :: aa :: lista)[0]! < (a :: aa :: lista)[1]!
            simpa using hc.1
        · intro _
          rfl
      · rw [if_neg hc, containsUnacceptableEdgeSnd_eq]
        constructor
        · intro h
          exact ⟨by simp, Or.inl h⟩
        · intro h
          obtain ⟨-, hdisj⟩ := h
          rcases hdisj with h | ⟨hN, hlt⟩
          · exact h
          · simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hN hlt
            exact absurd ⟨hlt, hN⟩ hc

/-- Invariants.thy: containsDuplicateEdge_eq. In Isabelle both sides are `bool`
functions and extensionally equal; here `containsDuplicateEdge'` is a `Prop`
(the Boolean coercion is rendered as `= true`), so the equality is stated
pointwise as an `Iff`. -/
theorem containsDuplicateEdge_eq (g : Graph) (f : Face) (v : Vertex) (is : List Nat) :
    containsDuplicateEdge g f v is = true ↔ containsDuplicateEdge' g f v is :=
  containsDuplicateEdge_eq1 g f v is

end ContainsDuplicateEdge

/-! ### replacefacesAt -/

section ReplacefacesAt

/-- Invariants.thy: replacefacesAt2 -/
def replacefacesAt2 : List Nat → Face → List Face → List (List Face) → List (List Face)
  | [], _, _, F => F
  | n :: ns, f, fs, F =>
    if n < F.length then replacefacesAt2 ns f fs (F.set n (replace f fs F[n]!))
    else replacefacesAt2 ns f fs F

/-- Invariants.thy: replacefacesAt_eq -/
theorem replacefacesAt_eq (ns : List Nat) (oldf : Face) (newfs : List Face)
    (F : List (List Face)) :
    replacefacesAt ns oldf newfs F = replacefacesAt2 ns oldf newfs F := by
  induction ns generalizing F with
  | nil => rfl
  | cons n ns ih =>
    simp only [replacefacesAt, mapAt, replacefacesAt2]
    by_cases h : n < F.length
    · rw [dif_pos h, if_pos h, getElem!_pos F n h]
      exact ih _
    · rw [dif_neg h, if_neg h]
      exact ih _

/-- Auxiliary: `getElem!` on `List.set` at the updated index. -/
theorem getElem!_set_self {α : Type*} [Inhabited α] {l : List α} {i : Nat} {a : α}
    (h : i < l.length) : (l.set i a)[i]! = a := by
  rw [getElem!_pos _ i (by rw [List.length_set]; exact h), List.getElem_set_self]

/-- Auxiliary: `getElem!` on `List.set` at a different index. -/
theorem getElem!_set_ne {α : Type*} [Inhabited α] {l : List α} {i j : Nat} {a : α}
    (h : i ≠ j) : (l.set j a)[i]! = l[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h),
    List.getElem!_eq_getElem?_getD]

/-- Invariants.thy: replacefacesAt2_notin -/
theorem replacefacesAt2_notin {i : Nat} {is : List Nat} {olfF : Face} {newFs : List Face}
    {Fss : List (List Face)} (hi : i ∉ is) :
    (replacefacesAt2 is olfF newFs Fss)[i]! = Fss[i]! := by
  induction is generalizing Fss with
  | nil => rfl
  | cons j js ih =>
    simp only [List.mem_cons, not_or] at hi
    simp only [replacefacesAt2]
    by_cases hj : j < Fss.length
    · rw [if_pos hj, ih hi.2, getElem!_set_ne hi.1]
    · rw [if_neg hj, ih hi.2]

/-- Invariants.thy: replacefacesAt2_in -/
theorem replacefacesAt2_in {i : Nat} {is : List Nat} {olfF : Face} {newFs : List Face}
    {Fss : List (List Face)} (hi : i ∈ is) (hd : is.Nodup) (hlt : i < Fss.length) :
    (replacefacesAt2 is olfF newFs Fss)[i]! = replace olfF newFs Fss[i]! := by
  revert hlt hd hi
  induction is generalizing Fss with
  | nil => intro hi hd hlt; simp at hi
  | cons j js ih =>
    intro hi hd hlt
    simp only [List.mem_cons] at hi
    simp only [List.nodup_cons] at hd
    simp only [replacefacesAt2]
    by_cases hj : j < Fss.length
    · rw [if_pos hj]
      rcases hi with rfl | hjs
      · rw [replacefacesAt2_notin hd.1, getElem!_set_self hj]
      · have hij : i ≠ j := fun e => hd.1 (e ▸ hjs)
        rw [ih (Fss := Fss.set j (replace olfF newFs Fss[j]!)) hjs hd.2
          (by rw [List.length_set]; exact hlt), getElem!_set_ne hij]
    · rw [if_neg hj]
      rcases hi with rfl | hjs
      · exact absurd hlt hj
      · exact ih hjs hd.2 hlt

/-- Invariants.thy: distinct_replacefacesAt21 -/
theorem distinct_replacefacesAt21 {i : Nat} {is : List Nat} {olfF : Face}
    {newFs : List Face} {Fss : List (List Face)} (hlt : i < Fss.length) (hi : i ∈ is)
    (hd : is.Nodup) (hF : Fss[i]!.Nodup) (hN : newFs.Nodup)
    (hsub : ∀ x ∈ Fss[i]!, x ∈ newFs → x = olfF) :
    ((replacefacesAt2 is olfF newFs Fss)[i]!).Nodup := by
  rw [replacefacesAt2_in hi hd hlt]
  exact distinct_replace hF hN hsub

/-- Invariants.thy: distinct_replacefacesAt22 -/
theorem distinct_replacefacesAt22 {i : Nat} {is : List Nat} {olfF : Face}
    {newFs : List Face} {Fss : List (List Face)} (hlt : i < Fss.length) (hi : i ∉ is)
    (hd : is.Nodup) (hF : Fss[i]!.Nodup) (hN : newFs.Nodup)
    (hsub : ∀ x ∈ Fss[i]!, x ∈ newFs → x = olfF) :
    ((replacefacesAt2 is olfF newFs Fss)[i]!).Nodup := by
  rw [replacefacesAt2_notin hi]
  exact hF

/-- Invariants.thy: distinct_replacefacesAt2_2 -/
theorem distinct_replacefacesAt2_2 {i : Nat} {is : List Nat} {olfF : Face}
    {newFs : List Face} {Fss : List (List Face)} (hlt : i < Fss.length) (hd : is.Nodup)
    (hF : Fss[i]!.Nodup) (hN : newFs.Nodup)
    (hsub : ∀ x ∈ Fss[i]!, x ∈ newFs → x = olfF) :
    ((replacefacesAt2 is olfF newFs Fss)[i]!).Nodup := by
  by_cases hi : i ∈ is
  · exact distinct_replacefacesAt21 hlt hi hd hF hN hsub
  · exact distinct_replacefacesAt22 hlt hi hd hF hN hsub

/-- Invariants.thy: replacefacesAt2_nth1 -/
theorem replacefacesAt2_nth1 {k : Nat} {ns : List Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} (hk : k ∉ ns) :
    (replacefacesAt2 ns oldf newfs F)[k]! = F[k]! :=
  replacefacesAt2_notin hk

/-- Invariants.thy: replacefacesAt2_nth1' -/
theorem replacefacesAt2_nth1' {k : Nat} {ns : List Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} (hk : k ∈ ns) (hlt : k < F.length) (hd : ns.Nodup) :
    (replacefacesAt2 ns oldf newfs F)[k]! = replace oldf newfs F[k]! :=
  replacefacesAt2_in hk hd hlt

/-- Invariants.thy: replacefacesAt2_nth2 -/
theorem replacefacesAt2_nth2 {k : Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} (hk : k < F.length) :
    (replacefacesAt2 [k] oldf newfs F)[k]! = replace oldf newfs F[k]! := by
  simp only [replacefacesAt2, if_pos hk]
  exact getElem!_set_self hk

/-- Invariants.thy: replacefacesAt2_length -/
@[simp]
theorem replacefacesAt2_length {nvs : List Nat} {f' : Face} {f'' : List Face}
    {vs : List (List Face)} :
    (replacefacesAt2 nvs f' f'' vs).length = vs.length := by
  induction nvs generalizing vs with
  | nil => rfl
  | cons n ns ih =>
    simp only [replacefacesAt2]
    by_cases h : n < vs.length
    · rw [if_pos h, ih, List.length_set]
    · rw [if_neg h, ih]

/-- Invariants.thy: replacefacesAt2_nth -/
theorem replacefacesAt2_nth {k : Nat} {ns : List Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} (hk : k ∈ ns) (hlt : k < F.length) (ho : oldf ∉ newfs)
    (hF : F[k]!.Nodup) (hN : newfs.Nodup)
    (hsub : oldf ∈ F[k]! → ∀ x ∈ newfs, x ∈ F[k]! → x = oldf) :
    (replacefacesAt2 ns oldf newfs F)[k]! = replace oldf newfs F[k]! := by
  revert hsub hF hlt hk
  induction ns generalizing F with
  | nil => intro hk hlt hF hsub; simp at hk
  | cons n ns ih =>
    intro hk hlt hF hsub
    simp only [List.mem_cons] at hk
    simp only [replacefacesAt2]
    by_cases hn : n < F.length
    · rw [if_pos hn]
      by_cases hkn : k = n
      · subst hkn
        have hself : (F.set k (replace oldf newfs F[k]!))[k]! = replace oldf newfs F[k]! :=
          getElem!_set_self (l := F) (a := replace oldf newfs F[k]!) hlt
        have hsubR : oldf ∈ (F.set k (replace oldf newfs F[k]!))[k]! →
            ∀ x ∈ newfs, x ∈ (F.set k (replace oldf newfs F[k]!))[k]! → x = oldf := by
          intro hoR x hxn hxR
          rw [hself] at hoR hxR
          rw [distinct_set_replace hF oldf] at hoR
          by_cases hoF : oldf ∈ F[k]!
          · rw [if_pos hoF] at hoR
            rcases hoR with ⟨-, hne⟩ | hnw
            · exact absurd rfl hne
            · exact absurd hnw ho
          · rw [if_neg hoF] at hoR
            exact absurd hoR hoF
        by_cases hks : k ∈ ns
        · rw [ih (F := F.set k (replace oldf newfs F[k]!)) hks
            (by rw [List.length_set]; exact hlt)
            (by rw [hself]; exact replace_distinct hF hN hsub) hsubR, hself,
            replace_replace ho hF]
        · rw [replacefacesAt2_notin hks, hself]
      · rcases hk with rfl | hks
        · exact absurd rfl hkn
        · have hne : (F.set n (replace oldf newfs F[n]!))[k]! = F[k]! :=
            getElem!_set_ne hkn
          rw [ih (F := F.set n (replace oldf newfs F[n]!)) hks
            (by rw [List.length_set]; exact hlt) (by rw [hne]; exact hF)
            (by rw [hne]; exact hsub), hne]
    · rw [if_neg hn]
      rcases hk with rfl | hks
      · exact absurd hlt hn
      · exact ih hks hlt hF hsub

/-- Invariants.thy: replacefacesAt_notin -/
theorem replacefacesAt_notin {i : Nat} {is : List Nat} {olfF : Face} {newFs : List Face}
    {Fss : List (List Face)} (hi : i ∉ is) :
    (replacefacesAt is olfF newFs Fss)[i]! = Fss[i]! := by
  rw [replacefacesAt_eq]
  exact replacefacesAt2_notin hi

/-- Invariants.thy: replacefacesAt_in -/
theorem replacefacesAt_in {i : Nat} {is : List Nat} {olfF : Face} {newFs : List Face}
    {Fss : List (List Face)} (hi : i ∈ is) (hd : is.Nodup) (hlt : i < Fss.length) :
    (replacefacesAt is olfF newFs Fss)[i]! = replace olfF newFs Fss[i]! := by
  rw [replacefacesAt_eq]
  exact replacefacesAt2_in hi hd hlt

/-- Invariants.thy: replacefacesAt_length -/
@[simp]
theorem replacefacesAt_length {nvs : List Nat} {f' f'' : Face} {vs : List (List Face)} :
    (replacefacesAt nvs f' [f''] vs).length = vs.length := by
  rw [replacefacesAt_eq]
  exact replacefacesAt2_length

/-- Invariants.thy: replacefacesAt_nth2 -/
theorem replacefacesAt_nth2 {k : Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} (hk : k < F.length) :
    (replacefacesAt [k] oldf newfs F)[k]! = replace oldf newfs F[k]! := by
  rw [replacefacesAt_eq]
  exact replacefacesAt2_nth2 hk

/-- Invariants.thy: replacefacesAt_nth -/
theorem replacefacesAt_nth {k : Nat} {ns : List Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} (hk : k ∈ ns) (hlt : k < F.length) (ho : oldf ∉ newfs)
    (hF : F[k]!.Nodup) (hN : newfs.Nodup)
    (hsub : oldf ∈ F[k]! → ∀ x ∈ newfs, x ∈ F[k]! → x = oldf) :
    (replacefacesAt ns oldf newfs F)[k]! = replace oldf newfs F[k]! := by
  rw [replacefacesAt_eq]
  exact replacefacesAt2_nth hk hlt ho hF hN hsub

/-- Invariants.thy: replacefacesAt2_5 -/
theorem replacefacesAt2_5 {x : Face} {ns : List Nat} {oldf : Face} {newfs : List Face}
    {F : List (List Face)} {k : Nat}
    (h : x ∈ (replacefacesAt2 ns oldf newfs F)[k]!) : x ∈ F[k]! ∨ x ∈ newfs := by
  induction ns generalizing F with
  | nil => exact Or.inl h
  | cons n ns ih =>
    simp only [replacefacesAt2] at h
    by_cases hn : n < F.length
    · rw [if_pos hn] at h
      rcases ih h with h | h
      · by_cases hkn : k = n
        · subst hkn
          rw [getElem!_set_self (l := F) (a := replace oldf newfs F[k]!) hn] at h
          rcases replace5 h with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rw [getElem!_set_ne hkn] at h
          exact Or.inl h
      · exact Or.inr h
    · rw [if_neg hn] at h
      exact ih h

/-- Invariants.thy: replacefacesAt_Nil -/
@[simp]
theorem replacefacesAt_Nil (f : Face) (fs : List Face) (F : List (List Face)) :
    replacefacesAt [] f fs F = F :=
  rfl

/-- Invariants.thy: replacefacesAt_Cons -/
@[simp]
theorem replacefacesAt_Cons (n : Nat) (ns : List Nat) (f : Face) (fs : List Face)
    (F : List (List Face)) :
    replacefacesAt (n :: ns) f fs F =
      if n < F.length then replacefacesAt ns f fs (F.set n (replace f fs F[n]!))
      else replacefacesAt ns f fs F := by
  simp only [replacefacesAt, mapAt]
  by_cases h : n < F.length
  · rw [dif_pos h, if_pos h, getElem!_pos F n h]
  · rw [dif_neg h, if_neg h]

/-- Invariants.thy: len_nth_repAt -/
@[simp]
theorem len_nth_repAt {is : List Nat} {x y : Face} {xs : List (List Face)} {i : Nat}
    (hi : i < xs.length) : (replacefacesAt is x [y] xs)[i]!.length = (xs[i]!).length := by
  rw [replacefacesAt_eq]
  revert hi
  induction is generalizing xs with
  | nil => intro hi; rfl
  | cons n ns ih =>
    intro hi
    simp only [replacefacesAt2]
    by_cases hn : n < xs.length
    · rw [if_pos hn, ih (xs := xs.set n (replace x [y] xs[n]!))
        (by rw [List.length_set]; exact hi)]
      by_cases hin : i = n
      · subst hin
        rw [getElem!_set_self (l := xs) (a := replace x [y] xs[i]!) hn]
        exact length_replace1
      · rw [getElem!_set_ne hin]
    · rw [if_neg hn, ih hi]

end ReplacefacesAt

/-! ### normFace -/

section NormFace

/-- Invariants.thy: minVertex_in -/
theorem minVertex_in {f : Face} (h : f.vertices ≠ []) : minVertex f ∈ f.vertices :=
  min_list_mem h

/-- Invariants.thy: minVertex_eq_if_vertices_eq (membership form of the set equality) -/
theorem minVertex_eq_if_vertices_eq {f f' : Face}
    (h : ∀ v, v ∈ f.vertices ↔ v ∈ f'.vertices) : minVertex f = minVertex f' := by
  by_cases hf : f.vertices = []
  · have hf' : f'.vertices = [] := by
      by_contra hne
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
      rw [hf] at h
      exact absurd ((h w).mpr hw) List.not_mem_nil
    simp [minVertex, hf, hf']
  · have hf' : f'.vertices ≠ [] := by
      intro hne
      rw [hne] at h
      apply hf
      rw [List.eq_nil_iff_forall_not_mem]
      intro v hv
      exact List.not_mem_nil ((h v).mp hv)
    apply le_antisymm
    · exact min_list_le ((h _).mpr (min_list_mem hf'))
    · exact min_list_le ((h _).mp (min_list_mem hf))

/-- Invariants.thy: normFace_replace_in -/
theorem normFace_replace_in {a oldF : Face} {newFs fs : List Face}
    (h : normFace a ∈ normFaces (replace oldF newFs fs)) :
    normFace a ∈ normFaces newFs ∨ normFace a ∈ normFaces fs := by
  obtain ⟨x, hx, hxa⟩ := List.mem_map.mp h
  rcases replace5 hx with hx | hx
  · exact Or.inr (List.mem_map.mpr ⟨x, hx, hxa⟩)
  · exact Or.inl (List.mem_map.mpr ⟨x, hx, hxa⟩)

/-- Invariants.thy: distinct_replace_norm -/
theorem distinct_replace_norm {fs newFs : List Face} {oldF : Face}
    (hd : (normFaces fs).Nodup) (hdn : (normFaces newFs).Nodup)
    (hsub : ∀ x ∈ normFaces fs, x ∉ normFaces newFs) :
    (normFaces (replace oldF newFs fs)).Nodup := by
  induction fs with
  | nil => exact List.nodup_nil
  | cons f fs ih =>
    simp only [normFaces, List.map_cons, List.nodup_cons] at hd
    by_cases hf : f = oldF
    · subst hf
      have h1 : replace f newFs (f :: fs) = newFs ++ fs := by simp [replace]
      rw [h1]
      show ((newFs ++ fs).map normFace).Nodup
      rw [List.map_append, List.nodup_append]
      refine ⟨hdn, hd.2, ?_⟩
      intro x hx y hy hxy
      exact hsub y (List.mem_cons_of_mem _ hy) (hxy ▸ hx)
    · have h1 : replace oldF newFs (f :: fs) = f :: replace oldF newFs fs := by
        simp [replace, hf]
      rw [h1]
      show (normFace f :: normFaces (replace oldF newFs fs)).Nodup
      rw [List.nodup_cons]
      refine ⟨?_, ih hd.2 (fun x hx => hsub x (List.mem_cons_of_mem _ hx))⟩
      intro hm
      rcases normFace_replace_in hm with h | h
      · exact hsub (normFace f) List.mem_cons_self h
      · exact hd.1 h

/-- Invariants.thy: distinct_replacefacesAt1_norm -/
theorem distinct_replacefacesAt1_norm {i : Nat} {is : List Nat} {oldF : Face}
    {newFs : List Face} {Fss : List (List Face)} (hlt : i < Fss.length) (hi : i ∈ is)
    (hd : is.Nodup) (hF : (normFaces Fss[i]!).Nodup) (hN : (normFaces newFs).Nodup)
    (hsub : ∀ x ∈ normFaces Fss[i]!, x ∉ normFaces newFs) :
    (normFaces ((replacefacesAt is oldF newFs Fss)[i]!)).Nodup := by
  rw [replacefacesAt_in hi hd hlt]
  exact distinct_replace_norm hF hN hsub

/-- Invariants.thy: distinct_replacefacesAt2_norm -/
theorem distinct_replacefacesAt2_norm {i : Nat} {is : List Nat} {oldF : Face}
    {newFs : List Face} {Fss : List (List Face)} (hlt : i < Fss.length) (hi : i ∉ is)
    (hd : is.Nodup) (hF : (normFaces Fss[i]!).Nodup) (hN : (normFaces newFs).Nodup)
    (hsub : ∀ x ∈ normFaces Fss[i]!, x ∉ normFaces newFs) :
    (normFaces ((replacefacesAt is oldF newFs Fss)[i]!)).Nodup := by
  rw [replacefacesAt_notin hi]
  exact hF

/-- Invariants.thy: distinct_replacefacesAt_norm -/
theorem distinct_replacefacesAt_norm {i : Nat} {is : List Nat} {olfF : Face}
    {newFs : List Face} {Fss : List (List Face)} (hlt : i < Fss.length) (hd : is.Nodup)
    (hF : (normFaces Fss[i]!).Nodup) (hN : (normFaces newFs).Nodup)
    (hsub : ∀ x ∈ normFaces Fss[i]!, x ∉ normFaces newFs) :
    (normFaces ((replacefacesAt is olfF newFs Fss)[i]!)).Nodup := by
  by_cases hi : i ∈ is
  · exact distinct_replacefacesAt1_norm hlt hi hd hF hN hsub
  · exact distinct_replacefacesAt2_norm hlt hi hd hF hN hsub

/-- Invariants.thy: normFace_in_cong -/
theorem normFace_in_cong {g : Graph} {f : Face} (hne : f.vertices ≠ [])
    (hmg : minGraphProps g) (h : normFace f ∈ normFaces g.faces) :
    ∃ f' ∈ g.faces, cong f.vertices f'.vertices := by
  obtain ⟨f', hf', hff'⟩ := List.mem_map.mp h
  refine ⟨f', hf', ?_⟩
  have c1 : cong f.vertices (normFace f) := verticesFrom_congs (minVertex_in hne)
  have hne' : f'.vertices ≠ [] := mgp_vertices_nonempty hmg hf'
  have c2 : cong f'.vertices (normFace f') := verticesFrom_congs (minVertex_in hne')
  rw [← hff'] at c1
  exact cong_trans c1 (cong_sym c2)

/-- Invariants.thy: normFace_neq -/
theorem normFace_neq {f f' : Face} {a : Vertex} (ha : a ∈ f.vertices)
    (ha' : a ∉ f'.vertices) (hne : f'.vertices ≠ []) : normFace f ≠ normFace f' := by
  intro e
  have haf : a ∈ normFace f :=
    (set_verticesFrom (minVertex_in (List.ne_nil_of_mem ha)) a).mpr ha
  have haf' : a ∉ normFace f' := fun hx => ha' ((set_verticesFrom (minVertex_in hne) a).mp hx)
  exact haf' (e ▸ haf)

/-- Invariants.thy: split_face_f12_f21_neq_norm -/
theorem split_face_f12_f21_neq_norm {oldF f12 f21 : Face} {ram₁ ram₂ : Vertex}
    {vs : List Vertex} (hp : pre_split_face oldF ram₁ ram₂ vs)
    (holdF : 2 < oldF.vertices.length) (h12 : 2 < f12.vertices.length)
    (h21 : 2 < f21.vertices.length)
    (hsplit : (f12, f21) = split_face oldF ram₁ ram₂ vs) :
    normFace f12 ≠ normFace f21 := by
  have hf12 : f12.vertices =
      vs.reverse ++ (ram₁ :: between oldF.vertices ram₁ ram₂ ++ [ram₂]) := by
    have h1 : f12 = (split_face oldF ram₁ ram₂ vs).1 := congrArg Prod.fst hsplit
    rw [h1]
    rfl
  have hf21 : f21.vertices =
      (ram₂ :: between oldF.vertices ram₂ ram₁ ++ [ram₁]) ++ vs := by
    have h2 : f21 = (split_face oldF ram₁ ram₂ vs).2 := congrArg Prod.snd hsplit
    rw [h2]
    rfl
  have hd : oldF.vertices.Nodup := hp.1
  have mem_vertices_of_B12 : ∀ x ∈ between oldF.vertices ram₁ ram₂,
      x ∈ oldF.vertices := by
    intro x hx
    have hxv : x ∈ verticesFrom oldF ram₁ := by
      rw [verticesFrom_ram1 hp]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
    exact (set_verticesFrom hp.2.2.2.1 x).mp hxv
  have mem_vertices_of_B21 : ∀ x ∈ between oldF.vertices ram₂ ram₁,
      x ∈ oldF.vertices := by
    intro x hx
    have hxv : x ∈ verticesFrom oldF ram₁ := by
      rw [verticesFrom_ram1 hp]
      exact List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
    exact (set_verticesFrom hp.2.2.2.1 x).mp hxv
  cases hB21 : between oldF.vertices ram₂ ram₁ with
  | nil =>
    cases hB12 : between oldF.vertices ram₁ ram₂ with
    | nil =>
      exfalso
      have hvf : verticesFrom oldF ram₁ = [ram₁, ram₂] := by
        have h := verticesFrom_ram1 hp
        rw [hB12, hB21] at h
        simpa using h
      have hlen : (verticesFrom oldF ram₁).length = oldF.vertices.length :=
        verticesFrom_length hd hp.2.2.2.1
      rw [hvf] at hlen
      simp at hlen
      omega
    | cons a lista =>
      have haB : a ∈ between oldF.vertices ram₁ ram₂ := by
        rw [hB12]
        exact List.mem_cons_self
      apply normFace_neq (f := f12) (f' := f21) (a := a)
      · rw [hf12, hB12]
        exact List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
      · rw [hf21, hB21]
        intro ha
        have ha' : a = ram₂ ∨ a = ram₁ ∨ a ∈ vs := by
          rcases List.mem_append.mp ha with ha | ha
          · rcases List.mem_cons.mp ha with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl (by simpa using h))
          · exact Or.inr (Or.inr ha)
        rcases ha' with rfl | rfl | hav
        · exact between_not_r2 hd haB
        · exact between_not_r1 hd haB
        · exact hp.2.2.1 a (mem_vertices_of_B12 a haB) hav
      · rw [hf21]
        simp
  | cons b listb =>
    have hbB : b ∈ between oldF.vertices ram₂ ram₁ := by
      rw [hB21]
      exact List.mem_cons_self
    apply Ne.symm
    apply normFace_neq (f := f21) (f' := f12) (a := b)
    · rw [hf21, hB21]
      exact List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))
    · rw [hf12]
      intro hb
      rcases List.mem_append.mp hb with hbv | hb
      · exact hp.2.2.1 b (mem_vertices_of_B21 b hbB) (List.mem_reverse.mp hbv)
      · rcases List.mem_cons.mp hb with hbr1 | hb
        · exact between_not_r2 (ram₁ := ram₂) (ram₂ := ram₁) hd (hbr1 ▸ hbB)
        · rcases List.mem_append.mp hb with hb12 | hb2
          · have hdn : (verticesFrom oldF ram₁).Nodup :=
              verticesFrom_distinct hd hp.2.2.2.1
            rw [verticesFrom_ram1 hp] at hdn
            have h2 := (List.nodup_cons.mp hdn).2
            have h3 := List.nodup_append.mp h2
            exact h3.2.2 b hb12 b (List.mem_cons_of_mem _ hbB) rfl
          · rw [List.mem_singleton] at hb2
            exact between_not_r1 (ram₁ := ram₂) (ram₂ := ram₁) hd (hb2 ▸ hbB)
    · rw [hf12]
      simp

/-- Invariants.thy: normFace_in -/
theorem normFace_in {f : Face} {fs : List Face} (h : f ∈ fs) :
    normFace f ∈ normFaces fs :=
  List.mem_map.mpr ⟨f, h, rfl⟩

end NormFace

end Kepler.Graphs
