/-
Port of the third block (lines 1847–3454) of the Isabelle AFP
"Flyspeck-Tame" theory `FaceDivisionProps.thy`: the `splitFace` section.

Source: `reference/afp-flyspeck-tame/FaceDivisionProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Correspondence notes: as in `FaceDivisionProps2.lean`
(`hd`/`last`/`butlast` ↦ `List.head!`/`List.getLast!`/`List.dropLast`,
`distinct` ↦ `List.Nodup`, set intersections with `{}` rendered as
membership non-implications).  `set xs` coercions in set equalities are
rendered as `{x | x ∈ xs}` set comprehensions.  The definition
`pre_splitFace` and `Edges` live in this block of the source file and are
ported here.
-/
import Kepler.Graphs.FaceDivisionProps2
import Mathlib.Data.Set.Finite.Basic

namespace Kepler.Graphs

/-! ### splitFace -/

section SplitFaceGraph

/-- FaceDivisionProps.thy: pre_splitFace.  The set intersection emptiness
conditions are rendered as membership non-implications, per project
convention. -/
def pre_splitFace (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face)
    (nvs : List Vertex) : Prop :=
  oldF ∈ g.faces ∧ oldF.final = false ∧ oldF.vertices.Nodup ∧ nvs.Nodup ∧
    (∀ x ∈ g.vertices, x ∉ nvs) ∧ (∀ x ∈ oldF.vertices, x ∉ nvs) ∧
    ram₁ ∈ oldF.vertices ∧ ram₂ ∈ oldF.vertices ∧ ram₁ ≠ ram₂ ∧
    (((ram₁, ram₂) ∉ oldF.edges ∧ (ram₂, ram₁) ∉ oldF.edges ∧
      (ram₁, ram₂) ∉ g.edges ∧ (ram₂, ram₁) ∉ g.edges) ∨ nvs ≠ [])

/-- FaceDivisionProps.thy: pre_splitFace_pre_split_face -/
theorem pre_splitFace_pre_split_face {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {nvs : List Vertex} (h : pre_splitFace g ram₁ ram₂ oldF nvs) :
    pre_split_face oldF ram₁ ram₂ nvs :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1⟩

/-- FaceDivisionProps.thy: pre_splitFace_oldF -/
theorem pre_splitFace_oldF {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {nvs : List Vertex} (h : pre_splitFace g ram₁ ram₂ oldF nvs) :
    oldF ∈ g.faces := h.1

/-- Auxiliary: symmetry of `pre_splitFace` in `ram₁ ram₂`
(the source file inline-unfolds the definition instead). -/
theorem pre_splitFace_symI {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {nvs : List Vertex} (h : pre_splitFace g ram₁ ram₂ oldF nvs) :
    pre_splitFace g ram₂ ram₁ oldF nvs := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.1, fun e => h.2.2.2.2.2.2.2.2.1 e.symm, ?_⟩
  rcases h.2.2.2.2.2.2.2.2.2 with ⟨h1, h2, h3, h4⟩ | h
  · exact Or.inl ⟨h2, h1, h4, h3⟩
  · exact Or.inr h

/-- FaceDivisionProps.thy: splitFace_split_face -/
theorem splitFace_split_face {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f₁ f₂ : Face} {newVs : List Vertex} (_h : oldF ∈ g.faces)
    (hsplit : (f₁, f₂, newGraph) = splitFace g ram₁ ram₂ oldF newVs) :
    (f₁, f₂) = split_face oldF ram₁ ram₂ newVs := by
  have h1 : f₁ = (split_face oldF ram₁ ram₂ newVs).1 := congrArg Prod.fst hsplit
  have h2 : f₂ = (split_face oldF ram₁ ram₂ newVs).2 := congrArg (fun p => p.2.1) hsplit
  exact Prod.ext h1 h2

/-- FaceDivisionProps.thy: split_face_empty_ram2_ram1_in_f12 -/
theorem split_face_empty_ram2_ram1_in_f12 {f12 f21 oldF : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face oldF ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face oldF ram₁ ram₂ []) :
    (ram₂, ram₁) ∈ f12.edges := by
  have hvs : f12.vertices = ram₁ :: between oldF.vertices ram₁ ram₂ ++ [ram₂] := by
    have hf : f12 = (split_face oldF ram₁ ram₂ []).1 := congrArg Prod.fst hsplit
    rw [hf]; rfl
  have hd : f12.vertices.Nodup := split_face_distinct1 hsplit hp
  have hram2 : ram₂ ∈ f12.vertices := by
    rw [hvs]; exact List.mem_append_right _ List.mem_cons_self
  have hlast : f12.vertices.getLast! = ram₂ := by rw [hvs, getLast!_concat]
  have hnext : f12.nextVertex ram₂ = ram₁ := by
    rw [nextElem_suc2 hd hlast hram2, hvs,
      List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
  exact edges_face_eq.mpr ⟨hnext, hram2⟩

/-- FaceDivisionProps.thy: split_face_empty_ram2_ram1_in_f12' -/
theorem split_face_empty_ram2_ram1_in_f12' {oldF : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face oldF ram₁ ram₂ []) :
    (ram₂, ram₁) ∈ (split_face oldF ram₁ ram₂ []).1.edges :=
  split_face_empty_ram2_ram1_in_f12 hp rfl

/-- FaceDivisionProps.thy: splitFace_empty_ram2_ram1_in_f12 -/
theorem splitFace_empty_ram2_ram1_in_f12 {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face}
    (hp : pre_splitFace g ram₁ ram₂ oldF [])
    (hsplit : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF []) :
    (ram₂, ram₁) ∈ f12.edges :=
  split_face_empty_ram2_ram1_in_f12 (pre_splitFace_pre_split_face hp)
    (splitFace_split_face hp.1 hsplit)

/-- FaceDivisionProps.thy: splitFace_f12_new_vertices -/
theorem splitFace_f12_new_vertices {g newGraph : Graph} {ram₁ ram₂ v : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (hsplit : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs)
    (hv : v ∈ newVs) : v ∈ f12.vertices := by
  have hf : f12 = (split_face oldF ram₁ ram₂ newVs).1 := congrArg Prod.fst hsplit
  rw [hf]
  show v ∈ newVs.reverse ++ _
  exact List.mem_append_left _ (List.mem_reverse.mpr hv)

/-- FaceDivisionProps.thy: splitFace_add_vertices_direct -/
@[simp]
theorem splitFace_add_vertices_direct (g : Graph) (ram₁ ram₂ : Vertex) (oldF : Face)
    (n : Nat) :
    (splitFace g ram₁ ram₂ oldF (List.range' g.countVertices n)).2.2.vertices =
      g.vertices ++ List.range' g.countVertices n := by
  show List.range (g.countVertices + (List.range' g.countVertices n).length) = _
  rw [List.length_range', Graph.vertices, List.range_add, List.range'_eq_map_range]

/-- FaceDivisionProps.thy: splitFace_delete_oldF -/
theorem splitFace_delete_oldF {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (hsplit : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs)
    (h1 : oldF ≠ f12) (h2 : oldF ≠ f21) (hd : g.faces.Nodup) :
    oldF ∉ newGraph.faces := by
  have e1 : f12 = (split_face oldF ram₁ ram₂ newVs).1 := congrArg Prod.fst hsplit
  have e2 : f21 = (split_face oldF ram₁ ram₂ newVs).2 := congrArg (fun p => p.2.1) hsplit
  have hf : newGraph.faces =
      replace oldF [(split_face oldF ram₁ ram₂ newVs).2] g.faces ++
        [(split_face oldF ram₁ ram₂ newVs).1] :=
    congrArg (fun p => p.2.2.faces) hsplit
  rw [hf]
  intro hin
  rcases List.mem_append.mp hin with hin | hin
  · by_cases holdF : oldF ∈ g.faces
    · rw [mem_replace_singleton_of_nodup hd holdF] at hin
      rcases hin with hin | ⟨_, hin⟩
      · exact h2 (hin.trans e2.symm)
      · exact hin rfl
    · rw [replace2 holdF] at hin
      exact holdF hin
  · exact h1 ((List.mem_singleton.mp hin).trans e1.symm)

/-- FaceDivisionProps.thy: splitFace_faces_1 -/
theorem splitFace_faces_1 {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (hsplit : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs)
    (holdF : oldF ∈ g.faces) :
    {x | x ∈ newGraph.faces} ∪ {oldF} = {f12, f21} ∪ {x | x ∈ g.faces} := by
  have e1 : f12 = (split_face oldF ram₁ ram₂ newVs).1 := congrArg Prod.fst hsplit
  have e2 : f21 = (split_face oldF ram₁ ram₂ newVs).2 := congrArg (fun p => p.2.1) hsplit
  have hf : newGraph.faces =
      replace oldF [(split_face oldF ram₁ ram₂ newVs).2] g.faces ++
        [(split_face oldF ram₁ ram₂ newVs).1] :=
    congrArg (fun p => p.2.2.faces) hsplit
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · rintro (hx | rfl)
    · rw [hf] at hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases replace5 hx with hx | hx
        · exact Or.inr hx
        · exact Or.inl (Or.inr ((List.mem_singleton.mp hx).trans e2.symm))
      · exact Or.inl (Or.inl ((List.mem_singleton.mp hx).trans e1.symm))
    · exact Or.inr holdF
  · rintro (⟨rfl | rfl⟩ | hx)
    · exact Or.inl (by rw [hf, e1]; exact List.mem_append_right _ List.mem_cons_self)
    · exact Or.inl (by
        rw [hf, e2]
        exact List.mem_append_left _ (replace3 holdF List.mem_cons_self))
    · by_cases hxo : x = oldF
      · exact Or.inr hxo
      · exact Or.inl (by rw [hf]; exact List.mem_append_left _ (replace4 hx (Ne.symm hxo)))

/-- FaceDivisionProps.thy: splitFace_distinct1 -/
theorem splitFace_distinct1 {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {nvs : List Vertex} (hp : pre_splitFace g ram₁ ram₂ oldF nvs) :
    (splitFace g ram₁ ram₂ oldF nvs).2.1.vertices.Nodup :=
  split_face_distinct2' (pre_splitFace_pre_split_face hp)

/-- FaceDivisionProps.thy: splitFace_distinct2 -/
theorem splitFace_distinct2 {g : Graph} {ram₁ ram₂ : Vertex} {oldF : Face}
    {nvs : List Vertex} (hp : pre_splitFace g ram₁ ram₂ oldF nvs) :
    (splitFace g ram₁ ram₂ oldF nvs).1.vertices.Nodup :=
  split_face_distinct1' (pre_splitFace_pre_split_face hp)

/-- FaceDivisionProps.thy: splitFace_add_f21' -/
theorem splitFace_add_f21' {g' : Graph} {v a : Vertex} {f' : Face} {nvl : List Vertex}
    (hf : f' ∈ g'.faces) :
    (splitFace g' v a f' nvl).2.1 ∈ (splitFace g' v a f' nvl).2.2.faces := by
  show (split_face f' v a nvl).2 ∈
    replace f' [(split_face f' v a nvl).2] g'.faces ++ [(split_face f' v a nvl).1]
  exact List.mem_append_left _ (replace3 hf List.mem_cons_self)

/-- FaceDivisionProps.thy: split_face_help -/
@[simp]
theorem split_face_help (f' : Face) (v a : Vertex) (nvl : List Vertex) :
    1 < (split_face f' v a nvl).1.vertices.length := by
  show 1 < (nvl.reverse ++ (v :: between f'.vertices v a ++ [a])).length
  simp only [List.length_append, List.length_cons, List.length_reverse]
  omega

/-- FaceDivisionProps.thy: split_face_help' -/
@[simp]
theorem split_face_help' (f' : Face) (v a : Vertex) (nvl : List Vertex) :
    1 < (split_face f' v a nvl).2.vertices.length := by
  show 1 < ((a :: between f'.vertices a v ++ [v]) ++ nvl).length
  simp only [List.length_append, List.length_cons]
  omega

/-- FaceDivisionProps.thy: splitFace_split -/
theorem splitFace_split {g : Graph} {v a : Vertex} {f f' : Face} {nvl : List Vertex}
    (h : f ∈ (splitFace g v a f' nvl).2.2.faces) :
    f ∈ g.faces ∨ f = (splitFace g v a f' nvl).1 ∨
      f = (splitFace g v a f' nvl).2.1 := by
  have h' : f ∈ replace f' [(split_face f' v a nvl).2] g.faces ++
      [(split_face f' v a nvl).1] := h
  rcases List.mem_append.mp h' with h | h
  · rcases replace5 h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (List.mem_singleton.mp h))
  · exact Or.inr (Or.inl (List.mem_singleton.mp h))

/-- FaceDivisionProps.thy: pre_FaceDiv_between1 -/
theorem pre_FaceDiv_between1 {g' : Graph} {ram₁ ram₂ : Vertex} {f : Face}
    (hp : pre_splitFace g' ram₁ ram₂ f []) :
    between f.vertices ram₁ ram₂ ≠ [] := by
  have hpre : pre_split_face f ram₁ ram₂ [] := pre_splitFace_pre_split_face hp
  have hpb : pre_between f.vertices ram₁ ram₂ := pre_split_face_p_between hpre
  have hedge : (ram₁, ram₂) ∉ f.edges := by
    rcases hp.2.2.2.2.2.2.2.2.2 with h | h
    · exact h.1
    · exact (h rfl).elim
  have hne : ¬ is_nextElem f.vertices ram₁ ram₂ :=
    fun h => hedge ((is_nextElem_edges_eq hpb.1).mpr h)
  exact fun hb => hne (is_nextElem_between_empty' hb hpb.1 hpb.2.1 hpb.2.2.1 hpb.2.2.2)

/-- FaceDivisionProps.thy: pre_FaceDiv_between2 -/
theorem pre_FaceDiv_between2 {g' : Graph} {ram₁ ram₂ : Vertex} {f : Face}
    (hp : pre_splitFace g' ram₁ ram₂ f []) :
    between f.vertices ram₂ ram₁ ≠ [] :=
  pre_FaceDiv_between1 (pre_splitFace_symI hp)


/-- FaceDivisionProps.thy: split_face_empty_ram1_ram2_in_f21 -/
theorem split_face_empty_ram1_ram2_in_f21 {f12 f21 oldF : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face oldF ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face oldF ram₁ ram₂ []) :
    (ram₁, ram₂) ∈ f21.edges := by
  have hvs : f21.vertices = ram₂ :: between oldF.vertices ram₂ ram₁ ++ [ram₁] := by
    have hf : f21 = (split_face oldF ram₁ ram₂ []).2 := congrArg Prod.snd hsplit
    rw [hf]
    show (([ram₂] ++ between oldF.vertices ram₂ ram₁) ++ [ram₁]) ++ [] =
      ram₂ :: between oldF.vertices ram₂ ram₁ ++ [ram₁]
    exact List.append_nil _
  have hd : f21.vertices.Nodup := split_face_distinct2 hsplit hp
  have hram1 : ram₁ ∈ f21.vertices := by
    rw [hvs]; exact List.mem_append_right _ List.mem_cons_self
  have hlast : f21.vertices.getLast! = ram₁ := by rw [hvs, getLast!_concat]
  have hnext : f21.nextVertex ram₁ = ram₂ := by
    rw [nextElem_suc2 hd hlast hram1, hvs,
      List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
  exact edges_face_eq.mpr ⟨hnext, hram1⟩

/-- FaceDivisionProps.thy: split_face_empty_ram1_ram2_in_f21' -/
theorem split_face_empty_ram1_ram2_in_f21' {oldF : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face oldF ram₁ ram₂ []) :
    (ram₁, ram₂) ∈ (split_face oldF ram₁ ram₂ []).2.edges :=
  split_face_empty_ram1_ram2_in_f21 hp rfl

/-- FaceDivisionProps.thy: splitFace_empty_ram1_ram2_in_f21 -/
theorem splitFace_empty_ram1_ram2_in_f21 {g newGraph : Graph} {ram₁ ram₂ : Vertex}
    {oldF f12 f21 : Face}
    (hp : pre_splitFace g ram₁ ram₂ oldF [])
    (hsplit : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF []) :
    (ram₁, ram₂) ∈ f21.edges :=
  split_face_empty_ram1_ram2_in_f21 (pre_splitFace_pre_split_face hp)
    (splitFace_split_face hp.1 hsplit)

/-- FaceDivisionProps.thy: splitFace_f21_new_vertices -/
theorem splitFace_f21_new_vertices {g newGraph : Graph} {ram₁ ram₂ v : Vertex}
    {oldF f12 f21 : Face} {newVs : List Vertex}
    (hsplit : (f12, f21, newGraph) = splitFace g ram₁ ram₂ oldF newVs)
    (hv : v ∈ newVs) : v ∈ f21.vertices := by
  have hf : f21 = (split_face oldF ram₁ ram₂ newVs).2 := congrArg (fun p => p.2.1) hsplit
  rw [hf]
  show v ∈ (([ram₂] ++ between oldF.vertices ram₂ ram₁) ++ [ram₁]) ++ newVs
  exact List.mem_append_right _ hv

end SplitFaceGraph

/-! ### Edges -/

section EdgesSection

/-- FaceDivisionProps.thy: Edges -/
def Edges (vs : List Vertex) : Set (Vertex × Vertex) := {p | is_sublist [p.1, p.2] vs}

/-- Auxiliary: no two-element sublist of the empty list. -/
private theorem not_is_sublist_pair_nil {a b : Vertex} :
    ¬ is_sublist [a, b] ([] : List Vertex) := by
  rintro ⟨as, bs, h⟩
  have h2 := congrArg List.length h
  simp only [List.length_nil, List.length_append, List.length_cons] at h2
  omega

/-- FaceDivisionProps.thy: Edges_Nil -/
@[simp]
theorem Edges_Nil : Edges ([] : List Vertex) = ∅ := by
  ext ⟨a, b⟩
  simp only [Edges, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact not_is_sublist_pair_nil

/-- FaceDivisionProps.thy: Edges_rev -/
theorem Edges_rev (zs : List Vertex) :
    Edges zs.reverse = {p | (p.2, p.1) ∈ Edges zs} :=
  Set.ext fun ⟨a, b⟩ => is_sublist_rev

/-- FaceDivisionProps.thy: in_Edges_rev -/
@[simp]
theorem in_Edges_rev {a b : Vertex} {zs : List Vertex} :
    (a, b) ∈ Edges zs.reverse ↔ (b, a) ∈ Edges zs := is_sublist_rev

/-- FaceDivisionProps.thy: notinset_notinEdge1 -/
theorem notinset_notinEdge1 {x y : Vertex} {xs : List Vertex} (h : x ∉ xs) :
    (x, y) ∉ Edges xs := fun he => h (is_sublist_in he)

/-- FaceDivisionProps.thy: notinset_notinEdge2 -/
theorem notinset_notinEdge2 {x y : Vertex} {xs : List Vertex} (h : y ∉ xs) :
    (x, y) ∉ Edges xs := fun he => h (is_sublist_in1 he)

/-- FaceDivisionProps.thy: in_Edges_in_set -/
theorem in_Edges_in_set {x y : Vertex} {vs : List Vertex} (h : (x, y) ∈ Edges vs) :
    x ∈ vs ∧ y ∈ vs := ⟨is_sublist_in h, is_sublist_in1 h⟩

/-- FaceDivisionProps.thy: edges_conv_Edges -/
theorem edges_conv_Edges {f : Face} (hd : f.vertices.Nodup) :
    f.edges = Edges f.vertices ∪
      (if f.vertices = [] then ∅ else {(f.vertices.getLast!, f.vertices.head!)}) := by
  ext ⟨a, b⟩
  rw [is_nextElem_edges_eq hd]
  by_cases hnil : f.vertices = []
  · rw [hnil, Edges_Nil, if_pos rfl, Set.union_empty]
    constructor
    · rintro (h | ⟨h, -, -⟩)
      · exact absurd h not_is_sublist_pair_nil
      · exact absurd rfl h
    · intro h
      exact False.elim ((Set.mem_empty_iff_false _).mp h)
  · rw [if_neg hnil]
    simp only [Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨-, h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr (Prod.ext h1 h2)
    · rintro (h | h)
      · exact Or.inl h
      · simp only [Prod.mk.injEq] at h
        exact Or.inr ⟨hnil, h.1, h.2⟩

/-- FaceDivisionProps.thy: Edges_Cons -/
theorem Edges_Cons {x : Vertex} {xs : List Vertex} :
    Edges (x :: xs) = if xs = [] then ∅ else Edges xs ∪ {(x, xs.head!)} := by
  ext ⟨a, b⟩
  simp only [Edges, Set.mem_setOf_eq]
  by_cases hxs : xs = []
  · subst hxs
    rw [if_pos rfl]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨as, bs, h⟩
    have h2 := congrArg List.length h
    simp only [List.length_cons, List.length_nil, List.length_append] at h2
    omega
  · rw [if_neg hxs]
    simp only [Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨as, bs, h⟩
      cases as with
      | nil =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exact Or.inr (Prod.ext h1.symm (by rw [h2, List.head!_cons]))
      | cons a' as' =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact Or.inl ⟨as', bs, h.2⟩
    · rintro (h | h)
      · obtain ⟨as, bs, h⟩ := h
        exact ⟨x :: as, bs, by simp only [List.cons_append, h]⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨ha, hb⟩ := h
        refine ⟨[], xs.tail, ?_⟩
        rw [ha, hb]
        show x :: xs = x :: xs.head! :: xs.tail
        rw [List.cons_head!_tail hxs]

/-- FaceDivisionProps.thy: Edges_append -/
theorem Edges_append (xs ys : List Vertex) :
    Edges (xs ++ ys) = if xs = [] then Edges ys
      else if ys = [] then Edges xs
      else Edges xs ∪ Edges ys ∪ {(xs.getLast!, ys.head!)} := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, Edges_Cons, if_neg (List.cons_ne_nil _ _)]
    by_cases hys : ys = []
    · subst hys
      simp only [List.append_nil, ↓reduceIte]
      rw [Edges_Cons]
    · rw [if_neg hys, if_neg (List.append_ne_nil_of_right_ne_nil _ hys), ih]
      by_cases hxs : xs = []
      · subst hxs
        have hgl : (x :: ([] : List Vertex)).getLast! = x := rfl
        simp only [List.nil_append, ↓reduceIte, Edges_Cons, hgl, Set.empty_union]
      · have hgl : (x :: xs).getLast! = xs.getLast! := getLast!_append_right [x] hxs
        rw [if_neg hxs, if_neg hys, Edges_Cons, if_neg hxs,
          List.head!_append _ hxs, hgl]
        ext ⟨p, q⟩
        simp only [Set.mem_union]
        constructor
        · rintro (((h | h) | h) | h)
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
          · exact Or.inl (Or.inl (Or.inr h))
        · rintro (((h | h) | h) | h)
          · exact Or.inl (Or.inl (Or.inl h))
          · exact Or.inr h
          · exact Or.inl (Or.inl (Or.inr h))
          · exact Or.inl (Or.inr h)

/-- Auxiliary: a nodup list cannot contain both `[a,b]` and `[b,a]` as
sublists (used for `Edges_rev_disj`). -/
private theorem Edges_not_rev_aux {a b : Vertex} {xs : List Vertex} (hd : xs.Nodup)
    (h1 : (a, b) ∈ Edges xs) (h2 : (b, a) ∈ Edges xs) : False := by
  induction xs with
  | nil =>
    rw [Edges_Nil] at h1
    exact (Set.mem_empty_iff_false _).mp h1
  | cons x xs ih =>
    rw [List.nodup_cons] at hd
    obtain ⟨hx, hd⟩ := hd
    by_cases hxs : xs = []
    · subst hxs
      rw [Edges_Cons, if_pos rfl] at h1
      exact (Set.mem_empty_iff_false _).mp h1
    · rw [Edges_Cons, if_neg hxs] at h1 h2
      simp only [Set.mem_union, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2b, h2a⟩
      · exact ih hd h1 h2
      · exact hx (h2b ▸ (in_Edges_in_set h1).2)
      · exact hx (h1a ▸ (in_Edges_in_set h2).2)
      · exact hx ((h2b.symm.trans h1b).symm ▸ List.head!_mem_self hxs)

/-- FaceDivisionProps.thy: Edges_rev_disj -/
theorem Edges_rev_disj {xs : List Vertex} (hd : xs.Nodup) :
    Edges xs.reverse ∩ Edges xs = ∅ := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, in_Edges_rev, Set.mem_empty_iff_false, iff_false, not_and]
  exact Edges_not_rev_aux hd

/-- FaceDivisionProps.thy: disj_sets_disj_Edges.  The empty set intersection
is rendered as a membership non-implication, per project convention. -/
theorem disj_sets_disj_Edges {xs ys : List Vertex}
    (h : ∀ x, x ∈ xs → x ∉ ys) : Edges xs ∩ Edges ys = ∅ := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  exact h a (in_Edges_in_set h1).1 (in_Edges_in_set h2).1

/-- FaceDivisionProps.thy: disj_sets_disj_Edges2 -/
theorem disj_sets_disj_Edges2 {xs ys : List Vertex}
    (h : ∀ x, x ∈ ys → x ∉ xs) : Edges xs ∩ Edges ys = ∅ :=
  disj_sets_disj_Edges fun x hxs hys => h x hys hxs

/-- FaceDivisionProps.thy: finite_Edges -/
theorem finite_Edges (xs : List Vertex) : (Edges xs).Finite := by
  induction xs with
  | nil => rw [Edges_Nil]; exact Set.finite_empty
  | cons x xs ih =>
    rw [Edges_Cons]
    by_cases hxs : xs = []
    · rw [if_pos hxs]; exact Set.finite_empty
    · rw [if_neg hxs]; exact Set.Finite.union ih (Set.finite_singleton _)

end EdgesSection

/-! ### split_face edges -/

section SplitFaceEdges

/-- FaceDivisionProps.thy: edges_split_face1 -/
theorem edges_split_face1 {f : Face} {u v : Vertex} {vs : List Vertex}
    (hp : pre_split_face f u v vs) :
    (split_face f u v vs).1.edges =
      Edges (v :: vs.reverse ++ [u]) ∪ Edges (u :: between f.vertices u v ++ [v]) := by
  have hd : (split_face f u v vs).1.vertices.Nodup := split_face_distinct1' hp
  have hne : (split_face f u v vs).1.vertices ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _
      (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  have hlast : (split_face f u v vs).1.vertices.getLast! = v := by
    show (vs.reverse ++ (([u] ++ between f.vertices u v) ++ [v])).getLast! = v
    rw [getLast!_append_right _
      (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))]
    exact getLast!_concat _ _
  by_cases hvs : vs = []
  · subst hvs
    have hhead : (split_face f u v []).1.vertices.head! = u := by
      show (([] : List Vertex).reverse ++ (u :: between f.vertices u v ++ [v])).head! = u
      rw [List.reverse_nil, List.nil_append,
        List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
    have h1 : Edges (v :: ([] : List Vertex).reverse ++ [u]) = {(v, u)} := by
      rw [List.reverse_nil]
      show Edges ([v] ++ [u]) = {(v, u)}
      rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
      have e1 : Edges [v] = ∅ := by rw [Edges_Cons, if_pos rfl]
      have e2 : Edges [u] = ∅ := by rw [Edges_Cons, if_pos rfl]
      have e3 : ([v] : List Vertex).getLast! = v := rfl
      have e4 : ([u] : List Vertex).head! = u := List.head!_cons _ _
      rw [e1, e2, e3, e4, Set.empty_union, Set.empty_union]
    rw [edges_conv_Edges hd, if_neg hne, hlast, hhead, h1]
    exact Set.union_comm _ _
  · have hrev : vs.reverse ≠ [] := fun h => hvs (List.reverse_eq_nil_iff.mp h)
    have hhead : (split_face f u v vs).1.vertices.head! = vs.reverse.head! := by
      show (vs.reverse ++ (([u] ++ between f.vertices u v) ++ [v])).head! = vs.reverse.head!
      exact List.head!_append _ hrev
    have hgl : (v :: vs.reverse).getLast! = vs.reverse.getLast! :=
      getLast!_append_right [v] hrev
    have h2 : Edges (v :: vs.reverse ++ [u]) =
        Edges vs.reverse ∪ {(v, vs.reverse.head!)} ∪ {(vs.reverse.getLast!, u)} := by
      rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
      rw [Edges_Cons, if_neg hrev, hgl]
      have e2 : Edges [u] = ∅ := by rw [Edges_Cons, if_pos rfl]
      have e4 : ([u] : List Vertex).head! = u := List.head!_cons _ _
      rw [e2, e4, Set.union_empty]
    have h3 : Edges (split_face f u v vs).1.vertices =
        Edges vs.reverse ∪ Edges (u :: between f.vertices u v ++ [v]) ∪
          {(vs.reverse.getLast!, u)} := by
      show Edges (vs.reverse ++ (u :: between f.vertices u v ++ [v])) = _
      rw [Edges_append, if_neg hrev,
        if_neg (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))]
      rw [List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
    rw [edges_conv_Edges hd, if_neg hne, hlast, hhead, h3, h2]
    ext ⟨a, b⟩
    simp only [Set.mem_union]
    constructor
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))

/-- FaceDivisionProps.thy: edges_split_face2 -/
theorem edges_split_face2 {f : Face} {u v : Vertex} {vs : List Vertex}
    (hp : pre_split_face f u v vs) :
    (split_face f u v vs).2.edges =
      Edges (u :: vs ++ [v]) ∪ Edges (v :: between f.vertices v u ++ [u]) := by
  have hd : (split_face f u v vs).2.vertices.Nodup := split_face_distinct2' hp
  have hX' : (v :: between f.vertices v u) ++ [u] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  have hne : (split_face f u v vs).2.vertices ≠ [] :=
    List.append_ne_nil_of_left_ne_nil hX' _
  by_cases hvs : vs = []
  · subst hvs
    have hlast : (split_face f u v []).2.vertices.getLast! = u := by
      show ((((v :: between f.vertices v u) ++ [u])) ++ []).getLast! = u
      rw [List.append_nil]
      exact getLast!_concat _ _
    have hhead : (split_face f u v []).2.vertices.head! = v := by
      show ((((v :: between f.vertices v u) ++ [u])) ++ []).head! = v
      rw [List.append_nil, List.head!_append _ (List.cons_ne_nil _ _), List.head!_cons]
    have h3 : Edges (split_face f u v []).2.vertices =
        Edges (v :: between f.vertices v u ++ [u]) := by
      show Edges ((((v :: between f.vertices v u) ++ [u])) ++ []) = _
      rw [List.append_nil]
    have h2 : Edges (u :: ([] : List Vertex) ++ [v]) = {(u, v)} := by
      show Edges ([u] ++ [v]) = {(u, v)}
      rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
      have e1 : Edges [u] = ∅ := by rw [Edges_Cons, if_pos rfl]
      have e2 : Edges [v] = ∅ := by rw [Edges_Cons, if_pos rfl]
      have e3 : ([u] : List Vertex).getLast! = u := rfl
      have e4 : ([v] : List Vertex).head! = v := List.head!_cons _ _
      rw [e1, e2, e3, e4, Set.empty_union, Set.empty_union]
    rw [edges_conv_Edges hd, if_neg hne, hlast, hhead, h3, h2]
    exact Set.union_comm _ _
  · have hlast : (split_face f u v vs).2.vertices.getLast! = vs.getLast! := by
      show ((((v :: between f.vertices v u) ++ [u])) ++ vs).getLast! = vs.getLast!
      exact getLast!_append_right _ hvs
    have hhead : (split_face f u v vs).2.vertices.head! = v := by
      show ((((v :: between f.vertices v u) ++ [u])) ++ vs).head! = v
      rw [List.head!_append _ hX', List.head!_append _ (List.cons_ne_nil _ _),
        List.head!_cons]
    have hgl : (u :: vs).getLast! = vs.getLast! := getLast!_append_right [u] hvs
    have h2 : Edges (u :: vs ++ [v]) =
        Edges vs ∪ {(u, vs.head!)} ∪ {(vs.getLast!, v)} := by
      rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
      rw [Edges_Cons, if_neg hvs, hgl]
      have e2 : Edges [v] = ∅ := by rw [Edges_Cons, if_pos rfl]
      have e4 : ([v] : List Vertex).head! = v := List.head!_cons _ _
      rw [e2, e4, Set.union_empty]
    have h3 : Edges (split_face f u v vs).2.vertices =
        Edges (v :: between f.vertices v u ++ [u]) ∪ Edges vs ∪ {(u, vs.head!)} := by
      show Edges ((((v :: between f.vertices v u) ++ [u])) ++ vs) = _
      rw [Edges_append, if_neg hX', if_neg hvs]
      rw [getLast!_concat]
    rw [edges_conv_Edges hd, if_neg hne, hlast, hhead, h3, h2]
    ext ⟨a, b⟩
    simp only [Set.mem_union]
    constructor
    · rintro (((h | h) | h) | h)
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    · rintro (((h | h) | h) | h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inl h))


end SplitFaceEdges

end Kepler.Graphs