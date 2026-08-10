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

end ReplacefacesAt

end Kepler.Graphs
