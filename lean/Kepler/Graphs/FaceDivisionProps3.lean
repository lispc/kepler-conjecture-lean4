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
import Mathlib.Tactic.Tauto

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

/-- Auxiliary: a nodup list cannot contain `[a, a]` as a sublist. -/
private theorem nodup_not_is_sublist_self {a : α} {vs : List α} (hd : vs.Nodup) :
    ¬ is_sublist [a, a] vs := by
  rintro ⟨as, bs, h⟩
  have hd' : (as ++ [a, a] ++ bs).Nodup := h ▸ hd
  have h1 : (as ++ [a, a]).Nodup := (List.nodup_append.mp hd').1
  have h2 : [a, a].Nodup := (List.nodup_append.mp h1).2.1
  exact (List.nodup_cons.mp h2).1 List.mem_cons_self

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

/-- FaceDivisionProps.thy: Edges_compl -/
theorem Edges_compl {vs : List Vertex} {x y : Vertex} (hd : vs.Nodup)
    (hx : x ∈ vs) (hy : y ∈ vs) (hxy : x ≠ y) :
    Edges (x :: between vs x y ++ [y]) ∩ Edges (y :: between vs y x ++ [x]) = ∅ := by
  have hpb : pre_between vs x y := ⟨hd, hx, hy, hxy⟩
  have hd1 : (x :: between vs x y ++ [y]).Nodup := between_distinct_r12 hd hxy
  have hd2 : (y :: between vs y x ++ [x]).Nodup := between_distinct_r12 hd (Ne.symm hxy)
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  have ha : a = x ∨ a = y := by
    have ha1 := (in_Edges_in_set h1).1
    have ha2 := (in_Edges_in_set h2).1
    rcases List.mem_append.mp ha1 with ha1 | ha1
    · rcases List.mem_cons.mp ha1 with ha1 | ha1
      · exact Or.inl ha1
      · have hay : a ≠ y := fun e => between_not_r2 hd (e ▸ ha1)
        have hax : a ≠ x := fun e => between_not_r1 hd (e ▸ ha1)
        have hny : a ∉ between vs y x := between_inter_empty hpb ha1
        rcases List.mem_append.mp ha2 with ha2 | ha2
        · rcases List.mem_cons.mp ha2 with ha2 | ha2
          · exact absurd ha2 hay
          · exact absurd ha2 hny
        · exact absurd (List.mem_singleton.mp ha2) hax
    · exact Or.inr (List.mem_singleton.mp ha1)
  have hb : b = x ∨ b = y := by
    have hb1 := (in_Edges_in_set h1).2
    have hb2 := (in_Edges_in_set h2).2
    rcases List.mem_append.mp hb1 with hb1 | hb1
    · rcases List.mem_cons.mp hb1 with hb1 | hb1
      · exact Or.inl hb1
      · have hby : b ≠ y := fun e => between_not_r2 hd (e ▸ hb1)
        have hbx : b ≠ x := fun e => between_not_r1 hd (e ▸ hb1)
        have hny : b ∉ between vs y x := between_inter_empty hpb hb1
        rcases List.mem_append.mp hb2 with hb2 | hb2
        · rcases List.mem_cons.mp hb2 with hb2 | hb2
          · exact absurd hb2 hby
          · exact absurd hb2 hny
        · exact absurd (List.mem_singleton.mp hb2) hbx
    · exact Or.inr (List.mem_singleton.mp hb1)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact nodup_not_is_sublist_self hd1 h1
  · exact is_sublist_notlast hd2 (getLast!_concat _ _).symm h2
  · exact is_sublist_notlast hd1 (getLast!_concat _ _).symm h1
  · exact nodup_not_is_sublist_self hd1 h1

/-- FaceDivisionProps.thy: Edges_disj -/
theorem Edges_disj {vs : List Vertex} {x y z : Vertex} (hd : vs.Nodup)
    (hx : x ∈ vs) (hz : z ∈ vs) (hxy : x ≠ y) (hyz : y ≠ z)
    (hy : y ∈ between vs x z) :
    Edges (x :: between vs x y ++ [y]) ∩ Edges (y :: between vs y z ++ [z]) = ∅ := by
  have hyv : y ∈ vs := inbetween_inset hy
  by_cases hxz : x = z
  · subst hxz
    exact Edges_compl hd hx hyv hxy
  · have hpb_xy : pre_between vs x y := ⟨hd, hx, hyv, hxy⟩
    have hpb_yz : pre_between vs y z := ⟨hd, hyv, hz, hyz⟩
    have hpb_xz : pre_between vs x z := ⟨hd, hx, hz, hxz⟩
    have hcong : cong vs (rotate_to vs x) := cong_rotate_to hx
    have hdR : (rotate_to vs x).Nodup := (cong_distinct hcong).mp hd
    set T := (splitAt x vs).2 ++ (splitAt x vs).1 with hT
    have hRv : rotate_to vs x = x :: T := rfl
    have hdT : T.Nodup := (List.nodup_cons.mp (hRv ▸ hdR)).2
    have hxT : x ∉ T := (List.nodup_cons.mp (hRv ▸ hdR)).1
    have hzT : z ∈ T := by
      have hzR : z ∈ rotate_to vs x := (cong_mem hcong).mp hz
      rw [hRv] at hzR
      rcases List.mem_cons.mp hzR with h | h
      · exact absurd h.symm hxz
      · exact h
    have hyT : y ∈ T := by
      have hyR : y ∈ rotate_to vs x := (cong_mem hcong).mp hyv
      rw [hRv] at hyR
      rcases List.mem_cons.mp hyR with h | h
      · exact absurd h.symm hxy
      · exact h
    have hbxz : between vs x z = between (rotate_to vs x) x z := between_congs hpb_xz hcong
    have hbxy : between vs x y = between (rotate_to vs x) x y := between_congs hpb_xy hcong
    have hbyz : between vs y z = between (rotate_to vs x) y z := between_congs hpb_yz hcong
    have hspx : splitAt x (rotate_to vs x) = ([], T) := by
      rw [hRv]; exact splitAt_self_cons _ _
    have hbR_xz : between (rotate_to vs x) x z = (splitAt z T).1 := by
      rw [between_def, hspx, if_pos (List.contains_iff_mem.mpr hzT)]
    have hbR_xy : between (rotate_to vs x) x y = (splitAt y T).1 := by
      rw [between_def, hspx, if_pos (List.contains_iff_mem.mpr hyT)]
    have hyS : y ∈ (splitAt z T).1 := by
      rw [hbxz, hbR_xz] at hy
      exact hy
    obtain ⟨Ay1, Ay2, hA⟩ := List.append_of_mem hyS
    have hTdec : T = Ay1 ++ y :: (Ay2 ++ z :: (splitAt z T).2) := by
      conv_lhs => rw [splitAt_ram hzT]
      rw [hA]
      simp [List.append_assoc]
    have hdT' : (Ay1 ++ y :: (Ay2 ++ z :: (splitAt z T).2)).Nodup := by
      rw [← hTdec]; exact hdT
    have hspy : splitAt y T = (Ay1, Ay2 ++ z :: (splitAt z T).2) :=
      (splitAt_dist_ram hdT hTdec).symm
    have hRdec : rotate_to vs x = (x :: Ay1) ++ y :: (Ay2 ++ z :: (splitAt z T).2) := by
      rw [hRv]
      conv_lhs => rw [hTdec]
      rfl
    have hspyR : splitAt y (rotate_to vs x) = (x :: Ay1, Ay2 ++ z :: (splitAt z T).2) :=
      (splitAt_dist_ram hdR hRdec).symm
    have hzmem : z ∈ Ay2 ++ z :: (splitAt z T).2 :=
      List.mem_append_right _ List.mem_cons_self
    have hb1 : z ∉ (splitAt y T).1 := by
      rw [hspy]
      intro hm
      exact (List.nodup_append.mp hdT').2.2 z hm z (List.mem_cons_of_mem _ hzmem) rfl
    have hb2 : z ∈ (splitAt y T).2 := by
      rw [hspy]; exact hzmem
    have hb3 : ∀ w ∈ (splitAt y T).1, w ∉ (splitAt z (splitAt y T).2).1 := by
      intro w ham
      rw [hspy] at ham ⊢
      intro hm
      have h2 : w ∈ Ay2 ++ z :: (splitAt z T).2 := splitAt_in_fst hm
      exact (List.nodup_append.mp hdT').2.2 w ham w (List.mem_cons_of_mem _ h2) rfl
    have hfactA : x ∉ between (rotate_to vs x) y z := by
      rw [between_def, hspyR, if_pos (List.contains_iff_mem.mpr hzmem)]
      intro hm
      exact hxT (by
        rw [hTdec]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (splitAt_in_fst hm)))
    have hfact_a : x ∉ between vs y z := by
      rw [hbyz]; exact hfactA
    have hfact_b : z ∉ between vs x y := by
      rw [hbxy, hbR_xy]; exact hb1
    have hfact_c : ∀ w ∈ between vs x y, w ∉ between vs y z := by
      intro w hw
      rw [hbxy, hbR_xy] at hw
      rw [hbyz, between_def, hspyR, if_pos (List.contains_iff_mem.mpr hzmem)]
      show w ∉ (splitAt z (Ay2 ++ z :: (splitAt z T).2)).1
      have hsnd : (splitAt y T).2 = Ay2 ++ z :: (splitAt z T).2 := congrArg Prod.snd hspy
      exact hsnd ▸ hb3 w hw
    -- final case analysis
    have hd1 : (x :: between vs x y ++ [y]).Nodup := between_distinct_r12 hd hxy
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    have ha : a = y := by
      have ham1 := (in_Edges_in_set h1).1
      have ham2 := (in_Edges_in_set h2).1
      rcases List.mem_append.mp ham1 with ham1 | ham1
      · rcases List.mem_cons.mp ham1 with ham1 | ham1
        · subst ham1
          rcases List.mem_append.mp ham2 with ham2 | ham2
          · rcases List.mem_cons.mp ham2 with ham2 | ham2
            · exact absurd ham2 hxy
            · exact absurd ham2 hfact_a
          · exact absurd (List.mem_singleton.mp ham2) hxz
        · have hay : a ≠ y := fun e => between_not_r2 hd (e ▸ ham1)
          have haz : a ≠ z := fun e => hfact_b (e ▸ ham1)
          have hany : a ∉ between vs y z := hfact_c a ham1
          rcases List.mem_append.mp ham2 with ham2 | ham2
          · rcases List.mem_cons.mp ham2 with ham2 | ham2
            · exact absurd ham2 hay
            · exact absurd ham2 hany
          · exact absurd (List.mem_singleton.mp ham2) haz
      · exact List.mem_singleton.mp ham1
    have hb : b = y := by
      have hbm1 := (in_Edges_in_set h1).2
      have hbm2 := (in_Edges_in_set h2).2
      rcases List.mem_append.mp hbm1 with hbm1 | hbm1
      · rcases List.mem_cons.mp hbm1 with hbm1 | hbm1
        · subst hbm1
          rcases List.mem_append.mp hbm2 with hbm2 | hbm2
          · rcases List.mem_cons.mp hbm2 with hbm2 | hbm2
            · exact absurd hbm2 hxy
            · exact absurd hbm2 hfact_a
          · exact absurd (List.mem_singleton.mp hbm2) hxz
        · have hby : b ≠ y := fun e => between_not_r2 hd (e ▸ hbm1)
          have hbz : b ≠ z := fun e => hfact_b (e ▸ hbm1)
          have hbny : b ∉ between vs y z := hfact_c b hbm1
          rcases List.mem_append.mp hbm2 with hbm2 | hbm2
          · rcases List.mem_cons.mp hbm2 with hbm2 | hbm2
            · exact absurd hbm2 hby
            · exact absurd hbm2 hbny
          · exact absurd (List.mem_singleton.mp hbm2) hbz
      · exact List.mem_singleton.mp hbm1
    subst ha; subst hb
    exact nodup_not_is_sublist_self hd1 h1

/-- FaceDivisionProps.thy: Edges_between_edges (source line 2246; proved
before `edges_conv_Un_Edges` here since the latter uses it). -/
theorem Edges_between_edges {f : Face} {a b u v : Vertex} {vs : List Vertex}
    (h : (a, b) ∈ Edges (u :: between f.vertices u v ++ [v]))
    (hp : pre_split_face f u v vs) : (a, b) ∈ f.edges := by
  have hpb : pre_between f.vertices u v := pre_split_face_p_between hp
  rcases pre_between_before hpb with hb | hb
  · have hsub : is_sublist (u :: between f.vertices u v ++ [v]) f.vertices := by
      refine ⟨(splitAt u f.vertices).1, (splitAt v f.vertices).2, ?_⟩
      conv_lhs => rw [between_vs hb hpb]
      simp [List.append_assoc]
    exact (is_nextElem_edges_eq hp.1).mpr
      (is_nextElem_sublistI (is_sublist_trans h hsub))
  · obtain ⟨as, bs, cs, hbtw, hvs⟩ := between_eq2 hpb hb
    have hlen : as.length + 1 ≤ f.vertices.length := by
      rw [hvs]; simp [List.length_append]
    have hsplit : f.vertices = (as ++ [v]) ++ (bs ++ [u] ++ cs) := by
      rw [hvs]; simp [List.append_assoc]
    have hR : f.vertices.rotate (as.length + 1) = (bs ++ [u] ++ cs) ++ (as ++ [v]) := by
      rw [List.rotate_eq_drop_append_take hlen, hsplit]
      have hl : (as ++ [v]).length = as.length + 1 := by simp
      rw [← hl, List.drop_left, List.take_left]
    have hsubL : is_sublist (u :: between f.vertices u v ++ [v])
        (f.vertices.rotate (as.length + 1)) := by
      refine ⟨bs, [], ?_⟩
      rw [List.append_nil, hR, hbtw]
      simp [List.append_assoc]
    exact (is_nextElem_edges_eq hp.1).mpr
      ((is_nextElem_rotate_eq (m := as.length + 1)).mp
        (is_nextElem_sublistI (is_sublist_trans h hsubL)))

/-- FaceDivisionProps.thy: edges_conv_Un_Edges -/
theorem edges_conv_Un_Edges {f : Face} {x y : Vertex} (hd : f.vertices.Nodup)
    (hx : x ∈ f.vertices) (hy : y ∈ f.vertices) (hxy : x ≠ y) :
    f.edges = Edges (x :: between f.vertices x y ++ [y]) ∪
      Edges (y :: between f.vertices y x ++ [x]) := by
  ext ⟨a, b⟩
  constructor
  · intro h
    have hpb : pre_between f.vertices x y := ⟨hd, hx, hy, hxy⟩
    rcases is_nextElem_or hpb ((is_nextElem_edges_eq hd).mp h) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    rcases h with h | h
    · exact Edges_between_edges h
        ⟨hd, List.nodup_nil, fun x' _ h' => List.not_mem_nil h', hx, hy, hxy⟩
    · exact Edges_between_edges h
        ⟨hd, List.nodup_nil, fun x' _ h' => List.not_mem_nil h', hy, hx, Ne.symm hxy⟩

end EdgesSection

/-- Auxiliary: `List.head!` of a `reverse` (no direct Isabelle counterpart). -/
private theorem head!_reverse_eq_getLast! [Inhabited α] : ∀ l : List α,
    l.reverse.head! = l.getLast! := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l' =>
      rw [List.reverse_cons]
      have hne : (b :: l').reverse ≠ [] :=
        fun h => List.cons_ne_nil _ _ (List.reverse_eq_nil_iff.mp h)
      rw [List.head!_append _ hne, ih]
      exact (getLast!_append_right [a] (List.cons_ne_nil _ _)).symm

/-- Auxiliary: `List.getLast!` of a `reverse` (no direct Isabelle
counterpart). -/
private theorem getLast!_reverse_eq_head! [Inhabited α] (l : List α) :
    l.reverse.getLast! = l.head! := by
  cases l with
  | nil => rfl
  | cons a l =>
    rw [List.reverse_cons, getLast!_concat]
    rfl

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


/-- FaceDivisionProps.thy: split_face_edges_f12 -/
theorem split_face_edges_f12 {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs vs1 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs)
    (hvs : vs ≠ []) (hvs1 : vs1 = between f.vertices ram₁ ram₂) (hvs1ne : vs1 ≠ []) :
    f12.edges = {(vs.head!, ram₁), (ram₁, vs1.head!), (vs1.getLast!, ram₂),
        (ram₂, vs.getLast!)} ∪ Edges vs.reverse ∪ Edges vs1 := by
  have hrev : vs.reverse ≠ [] := fun h => hvs (List.reverse_eq_nil_iff.mp h)
  have hf12 : f12 = (split_face f ram₁ ram₂ vs).1 := congrArg Prod.fst hsplit
  have e1 : Edges (ram₂ :: vs.reverse ++ [ram₁]) =
      (Edges vs.reverse ∪ {(ram₂, vs.getLast!)}) ∪ {(vs.head!, ram₁)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hrev]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₂ :: vs.reverse).getLast! = vs.reverse.getLast! :=
      getLast!_append_right [ram₂] hrev
    have g3 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, head!_reverse_eq_getLast!, getLast!_reverse_eq_head!, Set.union_empty]
  have e2 : Edges (ram₁ :: vs1 ++ [ram₂]) =
      (Edges vs1 ∪ {(ram₁, vs1.head!)}) ∪ {(vs1.getLast!, ram₂)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs1ne]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₁ :: vs1).getLast! = vs1.getLast! := getLast!_append_right [ram₁] hvs1ne
    have g3 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  rw [hf12, edges_split_face1 hp, ← hvs1, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (((h | h) | h) | ((h | h) | h))
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
  · rintro (((h | h | h | h) | h) | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f12_vs -/
theorem split_face_edges_f12_vs {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs1 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ [])
    (hvs1 : vs1 = between f.vertices ram₁ ram₂) (hvs1ne : vs1 ≠ []) :
    f12.edges = {(ram₂, ram₁), (ram₁, vs1.head!), (vs1.getLast!, ram₂)} ∪ Edges vs1 := by
  have hf12 : f12 = (split_face f ram₁ ram₂ []).1 := congrArg Prod.fst hsplit
  have e1 : Edges (ram₂ :: ([] : List Vertex).reverse ++ [ram₁]) = {(ram₂, ram₁)} := by
    rw [List.reverse_nil]
    show Edges ([ram₂] ++ [ram₁]) = {(ram₂, ram₁)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₂] : List Vertex).getLast! = ram₂ := rfl
    have g4 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  have e2 : Edges (ram₁ :: vs1 ++ [ram₂]) =
      (Edges vs1 ∪ {(ram₁, vs1.head!)}) ∪ {(vs1.getLast!, ram₂)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs1ne]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₁ :: vs1).getLast! = vs1.getLast! := getLast!_append_right [ram₁] hvs1ne
    have g3 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  rw [hf12, edges_split_face1 hp, ← hvs1, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | ((h | h) | h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((h | h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f12_bet -/
theorem split_face_edges_f12_bet {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs)
    (hvs : vs ≠ []) (hbet : between f.vertices ram₁ ram₂ = []) :
    f12.edges = {(vs.head!, ram₁), (ram₁, ram₂), (ram₂, vs.getLast!)} ∪
      Edges vs.reverse := by
  have hrev : vs.reverse ≠ [] := fun h => hvs (List.reverse_eq_nil_iff.mp h)
  have hf12 : f12 = (split_face f ram₁ ram₂ vs).1 := congrArg Prod.fst hsplit
  have e1 : Edges (ram₂ :: vs.reverse ++ [ram₁]) =
      (Edges vs.reverse ∪ {(ram₂, vs.getLast!)}) ∪ {(vs.head!, ram₁)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hrev]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₂ :: vs.reverse).getLast! = vs.reverse.getLast! :=
      getLast!_append_right [ram₂] hrev
    have g3 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, head!_reverse_eq_getLast!, getLast!_reverse_eq_head!, Set.union_empty]
  have e2 : Edges (ram₁ :: [] ++ [ram₂]) = {(ram₁, ram₂)} := by
    show Edges ([ram₁] ++ [ram₂]) = {(ram₁, ram₂)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₁] : List Vertex).getLast! = ram₁ := rfl
    have g4 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  rw [hf12, edges_split_face1 hp, hbet, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
  · rintro ((h | h | h) | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f12_bet_vs -/
theorem split_face_edges_f12_bet_vs {f f12 f21 : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face f ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ [])
    (hbet : between f.vertices ram₁ ram₂ = []) :
    f12.edges = {(ram₂, ram₁), (ram₁, ram₂)} := by
  have hf12 : f12 = (split_face f ram₁ ram₂ []).1 := congrArg Prod.fst hsplit
  have e1 : Edges (ram₂ :: ([] : List Vertex).reverse ++ [ram₁]) = {(ram₂, ram₁)} := by
    rw [List.reverse_nil]
    show Edges ([ram₂] ++ [ram₁]) = {(ram₂, ram₁)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₂] : List Vertex).getLast! = ram₂ := rfl
    have g4 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  have e2 : Edges (ram₁ :: [] ++ [ram₂]) = {(ram₁, ram₂)} := by
    show Edges ([ram₁] ++ [ram₂]) = {(ram₁, ram₂)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₁] : List Vertex).getLast! = ram₁ := rfl
    have g4 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  rw [hf12, edges_split_face1 hp, hbet, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- FaceDivisionProps.thy: split_face_edges_f12_subset -/
theorem split_face_edges_f12_subset {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs) (hvs : vs ≠ []) :
    {(vs.head!, ram₁), (ram₂, vs.getLast!)} ∪ Edges vs.reverse ⊆ f12.edges := by
  by_cases hbet : between f.vertices ram₁ ram₂ = []
  · rw [split_face_edges_f12_bet hp hsplit hvs hbet]
    intro p hp'
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hp' ⊢
    rcases hp' with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr h
  · rw [split_face_edges_f12 hp hsplit hvs rfl hbet]
    intro p hp'
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hp' ⊢
    rcases hp' with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (Or.inr h)

/-- FaceDivisionProps.thy: split_face_edges_f21 -/
theorem split_face_edges_f21 {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs vs2 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs)
    (hvs : vs ≠ []) (hvs2 : vs2 = between f.vertices ram₂ ram₁) (hvs2ne : vs2 ≠ []) :
    f21.edges = {(vs2.getLast!, ram₁), (ram₁, vs.head!), (vs.getLast!, ram₂),
        (ram₂, vs2.head!)} ∪ Edges vs ∪ Edges vs2 := by
  have hf21 : f21 = (split_face f ram₁ ram₂ vs).2 := congrArg Prod.snd hsplit
  have e1 : Edges (ram₁ :: vs ++ [ram₂]) =
      (Edges vs ∪ {(ram₁, vs.head!)}) ∪ {(vs.getLast!, ram₂)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₁ :: vs).getLast! = vs.getLast! := getLast!_append_right [ram₁] hvs
    have g3 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  have e2 : Edges (ram₂ :: vs2 ++ [ram₁]) =
      (Edges vs2 ∪ {(ram₂, vs2.head!)}) ∪ {(vs2.getLast!, ram₁)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs2ne]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₂ :: vs2).getLast! = vs2.getLast! := getLast!_append_right [ram₂] hvs2ne
    have g3 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  rw [hf21, edges_split_face2 hp, ← hvs2, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (((h | h) | h) | ((h | h) | h))
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl h))
  · rintro (((h | h | h | h) | h) | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f21_vs -/
theorem split_face_edges_f21_vs {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs2 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ [])
    (hvs2 : vs2 = between f.vertices ram₂ ram₁) (hvs2ne : vs2 ≠ []) :
    f21.edges = {(vs2.getLast!, ram₁), (ram₁, ram₂), (ram₂, vs2.head!)} ∪ Edges vs2 := by
  have hf21 : f21 = (split_face f ram₁ ram₂ []).2 := congrArg Prod.snd hsplit
  have e1 : Edges (ram₁ :: [] ++ [ram₂]) = {(ram₁, ram₂)} := by
    show Edges ([ram₁] ++ [ram₂]) = {(ram₁, ram₂)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₁] : List Vertex).getLast! = ram₁ := rfl
    have g4 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  have e2 : Edges (ram₂ :: vs2 ++ [ram₁]) =
      (Edges vs2 ∪ {(ram₂, vs2.head!)}) ∪ {(vs2.getLast!, ram₁)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs2ne]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₂ :: vs2).getLast! = vs2.getLast! := getLast!_append_right [ram₂] hvs2ne
    have g3 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  rw [hf21, edges_split_face2 hp, ← hvs2, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | ((h | h) | h))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inl h)
  · rintro ((h | h | h) | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f21_bet -/
theorem split_face_edges_f21_bet {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs)
    (hvs : vs ≠ []) (hbet : between f.vertices ram₂ ram₁ = []) :
    f21.edges = {(ram₁, vs.head!), (vs.getLast!, ram₂), (ram₂, ram₁)} ∪ Edges vs := by
  have hf21 : f21 = (split_face f ram₁ ram₂ vs).2 := congrArg Prod.snd hsplit
  have e1 : Edges (ram₁ :: vs ++ [ram₂]) =
      (Edges vs ∪ {(ram₁, vs.head!)}) ∪ {(vs.getLast!, ram₂)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₁ :: vs).getLast! = vs.getLast! := getLast!_append_right [ram₁] hvs
    have g3 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  have e2 : Edges (ram₂ :: [] ++ [ram₁]) = {(ram₂, ram₁)} := by
    show Edges ([ram₂] ++ [ram₁]) = {(ram₂, ram₁)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₂] : List Vertex).getLast! = ram₂ := rfl
    have g4 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  rw [hf21, edges_split_face2 hp, hbet, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((h | h | h) | h)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f21_bet_vs -/
theorem split_face_edges_f21_bet_vs {f f12 f21 : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face f ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ [])
    (hbet : between f.vertices ram₂ ram₁ = []) :
    f21.edges = {(ram₁, ram₂), (ram₂, ram₁)} := by
  have hf21 : f21 = (split_face f ram₁ ram₂ []).2 := congrArg Prod.snd hsplit
  have e1 : Edges (ram₁ :: [] ++ [ram₂]) = {(ram₁, ram₂)} := by
    show Edges ([ram₁] ++ [ram₂]) = {(ram₁, ram₂)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₁] : List Vertex).getLast! = ram₁ := rfl
    have g4 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  have e2 : Edges (ram₂ :: [] ++ [ram₁]) = {(ram₂, ram₁)} := by
    show Edges ([ram₂] ++ [ram₁]) = {(ram₂, ram₁)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₂] : List Vertex).getLast! = ram₂ := rfl
    have g4 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  rw [hf21, edges_split_face2 hp, hbet, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- FaceDivisionProps.thy: split_face_edges_f21_subset -/
theorem split_face_edges_f21_subset {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs) (hvs : vs ≠ []) :
    {(vs.getLast!, ram₂), (ram₁, vs.head!)} ∪ Edges vs ⊆ f21.edges := by
  by_cases hbet : between f.vertices ram₂ ram₁ = []
  · rw [split_face_edges_f21_bet hp hsplit hvs hbet]
    intro p hp'
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hp' ⊢
    rcases hp' with (h | h) | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rw [split_face_edges_f21 hp hsplit hvs rfl hbet]
    intro p hp'
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hp' ⊢
    rcases hp' with (h | h) | h
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr h)

/-- FaceDivisionProps.thy: verticesFrom_ram1 -/
theorem verticesFrom_ram1 {f : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs) :
    verticesFrom f ram₁ = ram₁ :: between f.vertices ram₁ ram₂ ++ ram₂ ::
      between f.vertices ram₂ ram₁ := by
  have hpb : pre_between f.vertices ram₁ ram₂ := pre_split_face_p_between hp
  have hd : f.vertices.Nodup := hpb.1
  set S1 := (splitAt ram₁ f.vertices).1 with hS1
  set S2 := (splitAt ram₁ f.vertices).2 with hS2
  have hvs : f.vertices = S1 ++ ram₁ :: S2 := splitAt_ram hpb.2.1
  show ram₁ :: S2 ++ S1 = ram₁ :: between f.vertices ram₁ ram₂ ++ ram₂ ::
    between f.vertices ram₂ ram₁
  rcases pre_between_before hpb with hb | hb
  · obtain ⟨B12, D2, hB⟩ : ∃ B D, splitAt ram₂ S2 = (B, D) := ⟨_, _, rfl⟩
    have hS2eq : S2 = B12 ++ ram₂ :: D2 := by
      have h := splitAt_ram (before_dist_r2 hd hb)
      rw [hB] at h
      exact h
    have hsp2 : splitAt ram₂ f.vertices = (S1 ++ ram₁ :: B12, D2) := by
      apply (splitAt_dist_ram hd ?_).symm
      conv_lhs => rw [hvs]
      conv_lhs => rw [hS2eq]
      simp [List.append_assoc]
    have hb12 : between f.vertices ram₁ ram₂ = B12 := by
      rw [between_simp1 hb hpb]
      exact congrArg Prod.fst hB
    have hb21 : between f.vertices ram₂ ram₁ = D2 ++ S1 := by
      rw [between_simp2 hb hpb, hsp2]
    rw [hb12, hb21, hS2eq]
    simp [List.append_assoc]
  · obtain ⟨Bp, D21, hB⟩ : ∃ B D, splitAt ram₂ S1 = (B, D) := ⟨_, _, rfl⟩
    have hS1eq : S1 = Bp ++ ram₂ :: D21 := by
      have h := splitAt_ram (before_dist_r1 hd hb)
      rw [hB] at h
      exact h
    have hsp2 : splitAt ram₂ f.vertices = (Bp, D21 ++ ram₁ :: S2) := by
      apply (splitAt_dist_ram hd ?_).symm
      conv_lhs => rw [hvs]
      conv_lhs => rw [hS1eq]
      simp [List.append_assoc]
    have hb12 : between f.vertices ram₁ ram₂ = S2 ++ Bp := by
      rw [between_simp2 hb (pre_between_symI hpb), hsp2]
    have hram1 : ram₁ ∉ D21 := by
      intro hm
      have h2 : (splitAt ram₂ S1).2 = D21 := congrArg Prod.snd hB
      have hmS1 : ram₁ ∈ S1 := splitAt_in_snd (h2.symm ▸ hm)
      exact splitAt_distinct_ram_fst hd hmS1
    have hsp1 : (splitAt ram₁ (D21 ++ ram₁ :: S2)).1 = D21 := by
      simp [splitAt_append_of_not_mem hram1, splitAt_self_cons]
    have hb21 : between f.vertices ram₂ ram₁ = D21 := by
      rw [between_simp1 hb (pre_between_symI hpb), hsp2]
      exact hsp1
    rw [hb12, hb21, hS1eq]
    simp [List.append_assoc]

/-- Auxiliary: a two-element sublist of a two-element list is the list itself
(no direct Isabelle counterpart). -/
private theorem eq_of_is_sublist_pair_pair {a b x y : Vertex}
    (h : is_sublist [a, b] [x, y]) : (a, b) = (x, y) := by
  obtain ⟨as, bs, h'⟩ := h
  have hlen := congrArg List.length h'
  simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  have ha0 : as = [] := List.length_eq_zero_iff.mp (by omega)
  have hb0 : bs = [] := List.length_eq_zero_iff.mp (by omega)
  subst ha0; subst hb0
  simp only [List.nil_append, List.append_nil, List.cons.injEq] at h'
  exact Prod.ext h'.1.symm h'.2.1.symm

/-- FaceDivisionProps.thy: split_face_edges_f_vs1_vs2 -/
theorem split_face_edges_f_vs1_vs2 {f : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hbet1 : between f.vertices ram₁ ram₂ = [])
    (hbet2 : between f.vertices ram₂ ram₁ = []) :
    f.edges = {(ram₂, ram₁), (ram₁, ram₂)} := by
  have hd : f.vertices.Nodup := hp.1
  have hpb : pre_between f.vertices ram₁ ram₂ := pre_split_face_p_between hp
  have hram1 : ram₁ ∈ f.vertices := hpb.2.1
  have hvf : verticesFrom f ram₁ = [ram₁, ram₂] := by
    rw [verticesFrom_ram1 hp, hbet1, hbet2]
    rfl
  ext ⟨a, b⟩
  rw [is_nextElem_edges_eq hd]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases is_nextElem_or hpb h with h | h
    · rw [hbet1] at h
      exact Or.inr (eq_of_is_sublist_pair_pair h)
    · rw [hbet2] at h
      exact Or.inl (eq_of_is_sublist_pair_pair h)
  · intro h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [verticesFrom_is_nextElem hram1, hvf]
      exact Or.inr ⟨List.cons_ne_nil _ _, (getLast!_concat [b] a).symm,
        (List.head!_cons _ _).symm⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [verticesFrom_is_nextElem hram1, hvf]
      exact Or.inl is_sublist_id

/-- FaceDivisionProps.thy: split_face_edges_f_vs1 -/
theorem split_face_edges_f_vs1 {f : Face} {ram₁ ram₂ : Vertex} {vs vs2 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hbet1 : between f.vertices ram₁ ram₂ = [])
    (hvs2 : vs2 = between f.vertices ram₂ ram₁) (hvs2ne : vs2 ≠ []) :
    f.edges = {(vs2.getLast!, ram₁), (ram₁, ram₂), (ram₂, vs2.head!)} ∪ Edges vs2 := by
  have hd : f.vertices.Nodup := hp.1
  have e1 : Edges (ram₁ :: [] ++ [ram₂]) = {(ram₁, ram₂)} := by
    show Edges ([ram₁] ++ [ram₂]) = {(ram₁, ram₂)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₁] : List Vertex).getLast! = ram₁ := rfl
    have g4 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  have e2 : Edges (ram₂ :: vs2 ++ [ram₁]) =
      (Edges vs2 ∪ {(ram₂, vs2.head!)}) ∪ {(vs2.getLast!, ram₁)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs2ne]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₂ :: vs2).getLast! = vs2.getLast! := getLast!_append_right [ram₂] hvs2ne
    have g3 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  rw [edges_conv_Un_Edges hd hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2, hbet1, ← hvs2, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | ((h | h) | h))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inl h)
  · rintro ((h | h | h) | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f_vs2 -/
theorem split_face_edges_f_vs2 {f : Face} {ram₁ ram₂ : Vertex} {vs vs1 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hvs1 : vs1 = between f.vertices ram₁ ram₂) (hvs1ne : vs1 ≠ [])
    (hbet2 : between f.vertices ram₂ ram₁ = []) :
    f.edges = {(ram₂, ram₁), (ram₁, vs1.head!), (vs1.getLast!, ram₂)} ∪ Edges vs1 := by
  have hd : f.vertices.Nodup := hp.1
  have e1 : Edges (ram₁ :: vs1 ++ [ram₂]) =
      (Edges vs1 ∪ {(ram₁, vs1.head!)}) ∪ {(vs1.getLast!, ram₂)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs1ne]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₁ :: vs1).getLast! = vs1.getLast! := getLast!_append_right [ram₁] hvs1ne
    have g3 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  have e2 : Edges (ram₂ :: [] ++ [ram₁]) = {(ram₂, ram₁)} := by
    show Edges ([ram₂] ++ [ram₁]) = {(ram₂, ram₁)}
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _)]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g3 : ([ram₂] : List Vertex).getLast! = ram₂ := rfl
    have g4 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, g4, Set.empty_union, Set.empty_union]
  rw [edges_conv_Un_Edges hd hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2, ← hvs1, hbet2, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inl h)
  · rintro ((h | h | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f -/
theorem split_face_edges_f {f : Face} {ram₁ ram₂ : Vertex} {vs vs1 vs2 : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hvs1 : vs1 = between f.vertices ram₁ ram₂) (hvs1ne : vs1 ≠ [])
    (hvs2 : vs2 = between f.vertices ram₂ ram₁) (hvs2ne : vs2 ≠ []) :
    f.edges = {(vs2.getLast!, ram₁), (ram₁, vs1.head!), (vs1.getLast!, ram₂),
        (ram₂, vs2.head!)} ∪ Edges vs1 ∪ Edges vs2 := by
  have hd : f.vertices.Nodup := hp.1
  have e1 : Edges (ram₁ :: vs1 ++ [ram₂]) =
      (Edges vs1 ∪ {(ram₁, vs1.head!)}) ∪ {(vs1.getLast!, ram₂)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs1ne]
    have g1 : Edges [ram₂] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₁ :: vs1).getLast! = vs1.getLast! := getLast!_append_right [ram₁] hvs1ne
    have g3 : ([ram₂] : List Vertex).head! = ram₂ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  have e2 : Edges (ram₂ :: vs2 ++ [ram₁]) =
      (Edges vs2 ∪ {(ram₂, vs2.head!)}) ∪ {(vs2.getLast!, ram₁)} := by
    rw [Edges_append, if_neg (List.cons_ne_nil _ _), if_neg (List.cons_ne_nil _ _),
      Edges_Cons, if_neg hvs2ne]
    have g1 : Edges [ram₁] = ∅ := by rw [Edges_Cons, if_pos rfl]
    have g2 : (ram₂ :: vs2).getLast! = vs2.getLast! := getLast!_append_right [ram₂] hvs2ne
    have g3 : ([ram₁] : List Vertex).head! = ram₁ := List.head!_cons _ _
    rw [g1, g2, g3, Set.union_empty]
  rw [edges_conv_Un_Edges hd hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2, ← hvs1, ← hvs2, e1, e2]
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (((h | h) | h) | ((h | h) | h))
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl h))
  · rintro (((h | h | h | h) | h) | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: split_face_edges_f12_f21_vs -/
theorem split_face_edges_f12_f21_vs {f f12 f21 : Face} {ram₁ ram₂ : Vertex}
    (hp : pre_split_face f ram₁ ram₂ [])
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ []) :
    f12.edges ∪ f21.edges = f.edges ∪ {(ram₂, ram₁), (ram₁, ram₂)} := by
  by_cases hbet1 : between f.vertices ram₁ ram₂ = []
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · rw [split_face_edges_f12_bet_vs hp hsplit hbet1,
        split_face_edges_f21_bet_vs hp hsplit hbet2,
        split_face_edges_f_vs1_vs2 hp hbet1 hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [split_face_edges_f12_bet_vs hp hsplit hbet1,
        split_face_edges_f21_vs hp hsplit rfl hbet2,
        split_face_edges_f_vs1 hp hbet1 rfl hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · rw [split_face_edges_f12_vs hp hsplit rfl hbet1,
        split_face_edges_f21_bet_vs hp hsplit hbet2,
        split_face_edges_f_vs2 hp rfl hbet1 hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [split_face_edges_f12_vs hp hsplit rfl hbet1,
        split_face_edges_f21_vs hp hsplit rfl hbet2,
        split_face_edges_f hp rfl hbet1 rfl hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- FaceDivisionProps.thy: split_face_edges_f12_f21 -/
theorem split_face_edges_f12_f21 {f f12 f21 : Face} {ram₁ ram₂ : Vertex} {vs : List Vertex}
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs) (hvs : vs ≠ []) :
    f12.edges ∪ f21.edges = f.edges ∪
      {(vs.head!, ram₁), (ram₁, vs.head!), (vs.getLast!, ram₂), (ram₂, vs.getLast!)} ∪
      Edges vs ∪ Edges vs.reverse := by
  by_cases hbet1 : between f.vertices ram₁ ram₂ = []
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · rw [split_face_edges_f12_bet hp hsplit hvs hbet1,
        split_face_edges_f21_bet hp hsplit hvs hbet2,
        split_face_edges_f_vs1_vs2 hp hbet1 hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [split_face_edges_f12_bet hp hsplit hvs hbet1,
        split_face_edges_f21 hp hsplit hvs rfl hbet2,
        split_face_edges_f_vs1 hp hbet1 rfl hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · rw [split_face_edges_f12 hp hsplit hvs rfl hbet1,
        split_face_edges_f21_bet hp hsplit hvs hbet2,
        split_face_edges_f_vs2 hp rfl hbet1 hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · rw [split_face_edges_f12 hp hsplit hvs rfl hbet1,
        split_face_edges_f21 hp hsplit hvs rfl hbet2,
        split_face_edges_f hp rfl hbet1 rfl hbet2]
      ext p
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto

/-- FaceDivisionProps.thy: split_face_edges_f12_f21_sym -/
theorem split_face_edges_f12_f21_sym {g : Graph} {f f12 f21 : Face} {ram₁ ram₂ a b : Vertex}
    {vs : List Vertex} (_hf : f ∈ g.faces)
    (hp : pre_split_face f ram₁ ram₂ vs)
    (hsplit : (f12, f21) = split_face f ram₁ ram₂ vs) :
    ((a, b) ∈ f12.edges ∨ (a, b) ∈ f21.edges) ↔
      ((a, b) ∈ f.edges ∨
        (((b, a) ∈ f12.edges ∨ (b, a) ∈ f21.edges) ∧
          ((a, b) ∈ f12.edges ∨ (a, b) ∈ f21.edges))) := by
  by_cases hvs : vs = []
  · subst hvs
    have h := split_face_edges_f12_f21_vs hp hsplit
    have h2 := Set.ext_iff.mp h (a, b)
    have h3 := Set.ext_iff.mp h (b, a)
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at h2 h3 ⊢
    constructor
    · intro hQ
      rcases h2.mp hQ with hP | ⟨h1, h2'⟩ | ⟨h1, h2'⟩
      · exact Or.inl hP
      · exact Or.inr ⟨h3.mpr (Or.inr (Or.inr ⟨h2', h1⟩)), hQ⟩
      · exact Or.inr ⟨h3.mpr (Or.inr (Or.inl ⟨h2', h1⟩)), hQ⟩
    · rintro (hP | ⟨-, hQ⟩)
      · exact h2.mpr (Or.inl hP)
      · exact hQ
  · have h := split_face_edges_f12_f21 hp hsplit hvs
    have h2 := Set.ext_iff.mp h (a, b)
    have h3 := Set.ext_iff.mp h (b, a)
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at h2 h3 ⊢
    constructor
    · intro hQ
      rcases h2.mp hQ with ((hP | hS) | hEV) | hER
      · exact Or.inl hP
      · have hSB : (b = vs.head! ∧ a = ram₁) ∨ (b = ram₁ ∧ a = vs.head!) ∨
            (b = vs.getLast! ∧ a = ram₂) ∨ (b = ram₂ ∧ a = vs.getLast!) := by
          rcases hS with ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩ | ⟨h1, h2'⟩
          · exact Or.inr (Or.inl ⟨h2', h1⟩)
          · exact Or.inl ⟨h2', h1⟩
          · exact Or.inr (Or.inr (Or.inr ⟨h2', h1⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨h2', h1⟩))
        exact Or.inr ⟨h3.mpr (Or.inl (Or.inl (Or.inr hSB))), hQ⟩
      · exact Or.inr ⟨h3.mpr (Or.inr (in_Edges_rev.mpr hEV)), hQ⟩
      · exact Or.inr ⟨h3.mpr (Or.inl (Or.inr (in_Edges_rev.mp hER))), hQ⟩
    · rintro (hP | ⟨-, hQ⟩)
      · exact h2.mpr (Or.inl (Or.inl (Or.inl hP)))
      · exact hQ

/-- FaceDivisionProps.thy: splitFace_edges_g'_help -/
theorem splitFace_edges_g'_help {g g' : Graph} {ram₁ ram₂ : Vertex} {f f12 f21 : Face}
    {vs : List Vertex}
    (hp : pre_splitFace g ram₁ ram₂ f vs)
    (hsplit : (f12, f21, g') = splitFace g ram₁ ram₂ f vs) (hvs : vs ≠ []) :
    g'.edges = g.edges ∪ f.edges ∪ Edges vs ∪ Edges vs.reverse ∪
      {(ram₂, vs.getLast!), (vs.head!, ram₁), (ram₁, vs.head!), (vs.getLast!, ram₂)} := by
  have hp' : pre_split_face f ram₁ ram₂ vs := pre_splitFace_pre_split_face hp
  have split : (f12, f21) = split_face f ram₁ ram₂ vs := splitFace_split_face hp.1 hsplit
  have hf12 : f12 = (split_face f ram₁ ram₂ vs).1 := congrArg Prod.fst hsplit
  have hf21 : f21 = (split_face f ram₁ ram₂ vs).2 := congrArg (fun p => p.2.1) hsplit
  have hfaces : g'.faces = replace f [f21] g.faces ++ [f12] := by
    have h : g'.faces = replace f [(split_face f ram₁ ram₂ vs).2] g.faces ++
        [(split_face f ram₁ ram₂ vs).1] := congrArg (fun p => p.2.2.faces) hsplit
    rw [← hf12, ← hf21] at h
    exact h
  have hg' : g'.edges = {p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} ∪ f12.edges := by
    ext p
    constructor
    · rintro ⟨a, ha, hpa⟩
      rw [hfaces] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, hpa⟩
      · rw [List.mem_singleton.mp ha] at hpa
        exact Or.inr hpa
    · rintro (⟨a, ha, hpa⟩ | hpa)
      · show ∃ a ∈ g'.faces, p ∈ a.edges
        rw [hfaces]
        exact ⟨a, List.mem_append_left _ ha, hpa⟩
      · show ∃ a ∈ g'.faces, p ∈ a.edges
        rw [hfaces]
        exact ⟨f12, List.mem_append_right _ List.mem_cons_self, hpa⟩
  rw [hg']
  have hb1 : ∀ p ∈ ({p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} : Set (Vertex × Vertex)),
      p ∈ g.edges ∨ p ∈ f21.edges := by
    intro p hpp
    obtain ⟨a, ha, hpa⟩ := hpp
    rcases replace5 ha with ha | ha
    · exact Or.inl ⟨a, ha, hpa⟩
    · rw [List.mem_singleton.mp ha] at hpa
      exact Or.inr hpa
  have hb2 : ∀ p ∈ g.edges, p ∈ ({p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} : Set _) ∨
      p ∈ f.edges := by
    intro p hpp
    obtain ⟨a, ha, hpa⟩ := hpp
    by_cases haf : a = f
    · exact Or.inr (haf ▸ hpa)
    · exact Or.inl ⟨a, replace4 ha (fun e => haf e.symm), hpa⟩
  have hb3 : ∀ p ∈ f21.edges, p ∈ ({p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} : Set _) :=
    fun p hpp => ⟨f21, replace3 (pre_splitFace_oldF hp) List.mem_cons_self, hpp⟩

  by_cases hbet1 : between f.vertices ram₁ ram₂ = []
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · have e12 := split_face_edges_f12_bet hp' split hvs hbet1
      have e21 := split_face_edges_f21_bet hp' split hvs hbet2
      have ef := split_face_edges_f_vs1_vs2 hp' hbet1 hbet2
      rw [e12, ef]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl (Or.inl (Or.inl (Or.inl hG)))
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with (h | h | h) | h
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl h))))
            · exact Or.inl (Or.inl (Or.inr h))
        · rcases h12 with (h | h | h) | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h))))
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr h)
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with ((((hG | hF) | hEV) | hER) | hS)
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with h | h
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inr h))))
            · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
        · rcases hF with h | h
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inr h))))
          · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
        · exact Or.inl (hb3 p (by rw [e21]; exact Or.inr hEV))
        · exact Or.inr (Or.inr hER)
        · rcases hS with h | h | h | h
          · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
          · exact Or.inr (Or.inl (Or.inl h))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl h)))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inl h))))
    · have e12 := split_face_edges_f12_bet hp' split hvs hbet1
      have e21 := split_face_edges_f21 hp' split hvs rfl hbet2
      have ef := split_face_edges_f_vs1 hp' hbet1 rfl hbet2
      rw [e12, ef]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl (Or.inl (Or.inl (Or.inl hG)))
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with ((h | h | h | h) | h) | h
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl h)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr h))))))
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h))))
        · rcases h12 with (h | h | h) | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl h))))))
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr h)
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with ((((hG | hF) | hEV) | hER) | hS)
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with (h | h | h) | h
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inl h))))
            · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))))
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inr h))
        · rcases hF with (h | h | h) | h
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inl h))))
          · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inr h))
        · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr hEV)))
        · exact Or.inr (Or.inr hER)
        · rcases hS with h | h | h | h
          · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
          · exact Or.inr (Or.inl (Or.inl h))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inl h)))))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))))
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · have e12 := split_face_edges_f12 hp' split hvs rfl hbet1
      have e21 := split_face_edges_f21_bet hp' split hvs hbet2
      have ef := split_face_edges_f_vs2 hp' rfl hbet1 hbet2
      rw [e12, ef]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl (Or.inl (Or.inl (Or.inl hG)))
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with (h | h | h) | h
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl h)))))
            · exact Or.inl (Or.inl (Or.inr h))
        · rcases h12 with ((h | h | h | h) | h) | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl h))))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr h))))))
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h))))
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with ((((hG | hF) | hEV) | hER) | hS)
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with (h | h | h) | h
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inr h))))
            · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl h))))
            · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h)))))
            · exact Or.inr (Or.inr h)
        · rcases hF with (h | h | h) | h
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inr h))))
          · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl h))))
          · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h)))))
          · exact Or.inr (Or.inr h)
        · exact Or.inl (hb3 p (by rw [e21]; exact Or.inr hEV))
        · exact Or.inr (Or.inl (Or.inr hER))
        · rcases hS with h | h | h | h
          · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h)))))
          · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl h)))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inl h))))
    · have e12 := split_face_edges_f12 hp' split hvs rfl hbet1
      have e21 := split_face_edges_f21 hp' split hvs rfl hbet2
      have ef := split_face_edges_f hp' rfl hbet1 rfl hbet2
      rw [e12, ef]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl (Or.inl (Or.inl (Or.inl hG)))
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with ((h | h | h | h) | h) | h
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl h))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))))))
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr h))))
        · rcases h12 with ((h | h | h | h) | h) | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl h)))))))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))))))
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr h)))))
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with ((((hG | hF) | hEV) | hER) | hS)
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with ((h | h | h | h) | h) | h
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inl h))))
            · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl h))))
            · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h)))))
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))))
            · exact Or.inr (Or.inr h)
            · exact Or.inl (hb3 p (by rw [e21]; exact Or.inr h))
        · rcases hF with ((h | h | h | h) | h) | h
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inl h))))
          · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl h))))
          · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h)))))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))))
          · exact Or.inr (Or.inr h)
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inr h))
        · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inr hEV)))
        · exact Or.inr (Or.inl (Or.inr hER))
        · rcases hS with h | h | h | h
          · exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h)))))
          · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inl h)))))
          · exact Or.inl (hb3 p (by rw [e21]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))))

/-- FaceDivisionProps.thy: pre_splitFace_edges_f_in_g -/
theorem pre_splitFace_edges_f_in_g {g : Graph} {ram₁ ram₂ : Vertex} {f : Face}
    {vs : List Vertex} (hp : pre_splitFace g ram₁ ram₂ f vs) : f.edges ⊆ g.edges :=
  fun _ hpp => ⟨f, hp.1, hpp⟩

/-- FaceDivisionProps.thy: pre_splitFace_edges_f_in_g2 -/
theorem pre_splitFace_edges_f_in_g2 {g : Graph} {ram₁ ram₂ : Vertex} {f : Face}
    {vs : List Vertex} {x : Vertex × Vertex} (hp : pre_splitFace g ram₁ ram₂ f vs)
    (hx : x ∈ f.edges) : x ∈ g.edges :=
  pre_splitFace_edges_f_in_g hp hx

/-- FaceDivisionProps.thy: splitFace_edges_g' -/
theorem splitFace_edges_g' {g g' : Graph} {ram₁ ram₂ : Vertex} {f f12 f21 : Face}
    {vs : List Vertex}
    (hp : pre_splitFace g ram₁ ram₂ f vs)
    (hsplit : (f12, f21, g') = splitFace g ram₁ ram₂ f vs) (hvs : vs ≠ []) :
    g'.edges = g.edges ∪ Edges vs ∪ Edges vs.reverse ∪
      {(ram₂, vs.getLast!), (vs.head!, ram₁), (ram₁, vs.head!), (vs.getLast!, ram₂)} := by
  have h := splitFace_edges_g'_help hp hsplit hvs
  rw [h]
  have hsub : f.edges ⊆ g.edges := pre_splitFace_edges_f_in_g hp
  ext p
  have hsubp : p ∈ f.edges → p ∈ g.edges := fun hpp => hsub hpp
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hsubp ⊢
  tauto


/-- FaceDivisionProps.thy: splitFace_edges_g'_vs -/
theorem splitFace_edges_g'_vs {g g' : Graph} {ram₁ ram₂ : Vertex} {f f12 f21 : Face}
    (hp : pre_splitFace g ram₁ ram₂ f [])
    (hsplit : (f12, f21, g') = splitFace g ram₁ ram₂ f []) :
    g'.edges = g.edges ∪ {(ram₁, ram₂), (ram₂, ram₁)} := by
  have hp' : pre_split_face f ram₁ ram₂ [] := pre_splitFace_pre_split_face hp
  have split : (f12, f21) = split_face f ram₁ ram₂ [] := splitFace_split_face hp.1 hsplit
  have hf12 : f12 = (split_face f ram₁ ram₂ []).1 := congrArg Prod.fst hsplit
  have hf21 : f21 = (split_face f ram₁ ram₂ []).2 := congrArg (fun p => p.2.1) hsplit
  have hfaces : g'.faces = replace f [f21] g.faces ++ [f12] := by
    have h : g'.faces = replace f [(split_face f ram₁ ram₂ []).2] g.faces ++
        [(split_face f ram₁ ram₂ []).1] := congrArg (fun p => p.2.2.faces) hsplit
    rw [← hf12, ← hf21] at h
    exact h
  have hg' : g'.edges = {p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} ∪ f12.edges := by
    ext p
    constructor
    · rintro ⟨a, ha, hpa⟩
      rw [hfaces] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, hpa⟩
      · rw [List.mem_singleton.mp ha] at hpa
        exact Or.inr hpa
    · rintro (⟨a, ha, hpa⟩ | hpa)
      · show ∃ a ∈ g'.faces, p ∈ a.edges
        rw [hfaces]
        exact ⟨a, List.mem_append_left _ ha, hpa⟩
      · show ∃ a ∈ g'.faces, p ∈ a.edges
        rw [hfaces]
        exact ⟨f12, List.mem_append_right _ List.mem_cons_self, hpa⟩
  rw [hg']
  have hb1 : ∀ p ∈ ({p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} : Set (Vertex × Vertex)),
      p ∈ g.edges ∨ p ∈ f21.edges := by
    intro p hpp
    obtain ⟨a, ha, hpa⟩ := hpp
    rcases replace5 ha with ha | ha
    · exact Or.inl ⟨a, ha, hpa⟩
    · rw [List.mem_singleton.mp ha] at hpa
      exact Or.inr hpa
  have hb2 : ∀ p ∈ g.edges, p ∈ ({p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} : Set _) ∨
      p ∈ f.edges := by
    intro p hpp
    obtain ⟨a, ha, hpa⟩ := hpp
    by_cases haf : a = f
    · exact Or.inr (haf ▸ hpa)
    · exact Or.inl ⟨a, replace4 ha (fun e => haf e.symm), hpa⟩
  have hb3 : ∀ p ∈ f21.edges, p ∈ ({p | ∃ a ∈ replace f [f21] g.faces, p ∈ a.edges} : Set _) :=
    fun p hpp => ⟨f21, replace3 (pre_splitFace_oldF hp) List.mem_cons_self, hpp⟩
  have hb4 : ∀ p ∈ f.edges, p ∈ g.edges :=
    fun p hpp => pre_splitFace_edges_f_in_g hp hpp
  by_cases hbet1 : between f.vertices ram₁ ram₂ = []
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · have e12 := split_face_edges_f12_bet_vs hp' split hbet1
      have e21 := split_face_edges_f21_bet_vs hp' split hbet2
      have ef := split_face_edges_f_vs1_vs2 hp' hbet1 hbet2
      rw [e12]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl hG
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        · rcases h12 with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hG | hF
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with h | h
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inr h)))
            · exact Or.inr (Or.inr h)
        · rcases hF with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inr h)))
    · have e12 := split_face_edges_f12_bet_vs hp' split hbet1
      have e21 := split_face_edges_f21_vs hp' split rfl hbet2
      have ef := split_face_edges_f_vs1 hp' hbet1 rfl hbet2
      rw [e12]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl hG
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with (h | h | h) | h
            · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inl h))))
            · exact Or.inr (Or.inl h)
            · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inr (Or.inr h)))))
            · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inr h)))
        · rcases h12 with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hG | hF
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with (h | h | h) | h
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inl (Or.inl h))))
            · exact Or.inr (Or.inr h)
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inr h)))))
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inr h)))
        · rcases hF with h | h
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
  · by_cases hbet2 : between f.vertices ram₂ ram₁ = []
    · have e12 := split_face_edges_f12_vs hp' split rfl hbet1
      have e21 := split_face_edges_f21_bet_vs hp' split hbet2
      have ef := split_face_edges_f_vs2 hp' rfl hbet1 hbet2
      rw [e12]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl hG
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
        · rcases h12 with (h | h | h) | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inr (Or.inl h)))))
          · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inr (Or.inr h)))))
          · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inr h)))
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hG | hF
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with (h | h | h) | h
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inr h)))
            · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
            · exact Or.inr (Or.inr h)
        · rcases hF with h | h
          · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inl h)))
          · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inr h)))
    · have e12 := split_face_edges_f12_vs hp' split rfl hbet1
      have e21 := split_face_edges_f21_vs hp' split rfl hbet2
      have ef := split_face_edges_f hp' rfl hbet1 rfl hbet2
      rw [e12]
      ext p
      constructor
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hR | h12
        · rcases hb1 p hR with hG | hF21
          · exact Or.inl hG
          · rw [e21] at hF21
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF21
            rcases hF21 with (h | h | h) | h
            · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inl (Or.inl h)))))
            · exact Or.inr (Or.inl h)
            · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h)))))))
            · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inr h)))
        · rcases h12 with (h | h | h) | h
          · exact Or.inr (Or.inr h)
          · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inl (Or.inr (Or.inl h))))))
          · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h)))))))
          · exact Or.inl ((hb4 p (by rw [ef]; exact Or.inl (Or.inr h))))
      · intro h
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at h
        rcases h with hG | hF
        · rcases hb2 p hG with hR | hF
          · exact Or.inl hR
          · rw [ef] at hF
            simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq] at hF
            rcases hF with ((h | h | h | h) | h) | h
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inl (Or.inl h))))
            · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inr h)))))
            · exact Or.inr (Or.inr h)
            · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inr h)))
        · rcases hF with h | h
          · exact Or.inl ((hb3 p (by rw [e21]; exact Or.inl (Or.inr (Or.inl h)))))
          · exact Or.inr (Or.inl (Or.inl h))

/-- FaceDivisionProps.thy: splitFace_edges_incr -/
theorem splitFace_edges_incr {g g' : Graph} {ram₁ ram₂ : Vertex} {f f₁ f₂ : Face}
    {vs : List Vertex}
    (hp : pre_splitFace g ram₁ ram₂ f vs)
    (hsplit : (f₁, f₂, g') = splitFace g ram₁ ram₂ f vs) :
    g.edges ⊆ g'.edges := by
  cases vs with
  | nil =>
    rw [splitFace_edges_g'_vs hp hsplit]
    exact fun p hpp => Or.inl hpp
  | cons v vs' =>
    rw [splitFace_edges_g' hp hsplit (List.cons_ne_nil _ _)]
    exact fun p hpp => Or.inl (Or.inl (Or.inl hpp))

/-- FaceDivisionProps.thy: snd_snd_splitFace_edges_incr -/
theorem snd_snd_splitFace_edges_incr {g : Graph} {v₁ v₂ : Vertex} {f : Face}
    {vs : List Vertex} (hp : pre_splitFace g v₁ v₂ f vs) :
    g.edges ⊆ (splitFace g v₁ v₂ f vs).2.2.edges :=
  splitFace_edges_incr hp rfl

end SplitFaceEdges

end Kepler.Graphs