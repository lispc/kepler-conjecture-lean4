/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `ScoreProps.thy`.

Source: `reference/afp-flyspeck-tame/ScoreProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Properties of the lower-bound machinery (`squanderLowerBound`, `ExcessAt`,
`ExcessNotAt`): the `deleteAround` lemmas, the `ExcessNotAtRecList` witness
function, and the separating/sum-distribution lemmas.

Correspondence notes:
- Isabelle `vertex set` arguments are rendered as predicates `Vertex → Prop`
  or list membership, following the `Tame.lean` conventions; set
  equalities/inclusions/empty intersections are rendered pointwise.
- `isTable` (Isabelle `ListAux.thy`) and `noExceptionals` (Isabelle
  `Graph.thy`) were not needed by the definition layer, so they are ported
  here where they are first used.
- The Lean `deleteAround` (`Generator.lean`) is already in the `[code]` form,
  so `deleteAround'`/`deleteAround_eq` hold by `rfl`.
-/
import Kepler.Graphs.TameProps
import Kepler.Graphs.PlaneProps
import Kepler.Graphs.ListSum
import Kepler.Graphs.TameEnum

namespace Kepler.Graphs

/-! ### `removeKeyList` helpers (auxiliary, for the `deleteAround` lemmas) -/

/-- Auxiliary: `removeKeyList` with an empty second argument. -/
theorem removeKeyList_nil_right [BEq α] (ws : List α) :
    removeKeyList ws ([] : List (α × β)) = [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [removeKeyList, removeKey, ih]

/-- Auxiliary: `removeKeyList` is a filter on the first components. -/
theorem removeKeyList_eq_filter [BEq α] (ws : List α) (ps : List (α × β)) :
    removeKeyList ws ps = ps.filter (fun p => ws.all (fun w => w != p.1)) := by
  induction ws generalizing ps with
  | nil => simp [removeKeyList]
  | cons w ws ih =>
    simp only [removeKeyList, removeKey, ih, List.all_cons]
    rw [List.filter_filter]

/-- Auxiliary: membership in `removeKeyList`. -/
theorem mem_removeKeyList [BEq α] [LawfulBEq α] {ws : List α} {ps : List (α × β)}
    {p : α × β} :
    p ∈ removeKeyList ws ps ↔ p ∈ ps ∧ p.1 ∉ ws := by
  rw [removeKeyList_eq_filter, List.mem_filter]
  constructor
  · intro ⟨hps, hall⟩
    refine ⟨hps, fun h => ?_⟩
    rw [List.all_eq_true] at hall
    have h := hall p.1 h
    simp at h
  · intro ⟨hps, hnot⟩
    refine ⟨hps, ?_⟩
    rw [List.all_eq_true]
    intro w hw
    rw [bne_iff_ne]
    exact fun e => hnot (e ▸ hw)

/-- Auxiliary: `removeKeyList` on a `cons`. -/
theorem removeKeyList_cons [BEq α] [LawfulBEq α] (ws : List α) (p : α × β)
    (ps : List (α × β)) :
    removeKeyList ws (p :: ps) =
      if p.1 ∈ ws then removeKeyList ws ps else p :: removeKeyList ws ps := by
  rw [removeKeyList_eq_filter, removeKeyList_eq_filter, List.filter_cons]
  by_cases h : p.1 ∈ ws
  · have hfalse : (ws.all fun w => w != p.1) = false := by
      cases hall : ws.all fun w => w != p.1 with
      | false => rfl
      | true =>
        rw [List.all_eq_true] at hall
        have h := hall p.1 h
        simp at h
    rw [if_pos h]
    simp [hfalse]
  · have htrue : (ws.all fun w => w != p.1) = true := by
      rw [List.all_eq_true]
      intro w hw
      rw [bne_iff_ne]
      exact fun e => h (e ▸ hw)
    rw [if_neg h]
    simp [htrue]

/-! ### `deleteAround` lemmas -/

/-- Unfolding bridge: the Lean `deleteAround` is already in the `[code]` form
(Isabelle proves this via `nextV2`). -/
theorem deleteAround_eq_removeKeyList (g : Graph) (a : Vertex)
    (ps : List (Vertex × Nat)) :
    deleteAround g a ps =
      removeKeyList ((g.facesAt a).flatMap fun f =>
        let n := f.nextVertex a
        if f.vertices.length = 4 then [n, f.nextVertex n] else [n]) ps := rfl

/-- ScoreProps.thy: deleteAround_empty -/
@[simp]
theorem deleteAround_empty (g : Graph) (a : Vertex) : deleteAround g a [] = [] := by
  rw [deleteAround_eq_removeKeyList]
  exact removeKeyList_nil_right _

open Classical in
/-- ScoreProps.thy: deleteAroundCons -/
theorem deleteAroundCons (g : Graph) (a : Vertex) (p : Vertex × Nat)
    (ps : List (Vertex × Nat)) :
    deleteAround g a (p :: ps) =
      (if ∃ f ∈ g.facesAt a,
          (f.vertices.length = 4 ∧
            (p.1 = f.nextVertex a ∨ p.1 = f.nextVertex (f.nextVertex a))) ∨
          (f.vertices.length ≠ 4 ∧ p.1 = f.nextVertex a)
       then deleteAround g a ps
       else p :: deleteAround g a ps) := by
  rw [deleteAround_eq_removeKeyList, deleteAround_eq_removeKeyList,
    removeKeyList_cons]
  have hiff : p.1 ∈ (g.facesAt a).flatMap (fun f =>
        let n := f.nextVertex a
        if f.vertices.length = 4 then [n, f.nextVertex n] else [n]) ↔
      ∃ f ∈ g.facesAt a,
        (f.vertices.length = 4 ∧
          (p.1 = f.nextVertex a ∨ p.1 = f.nextVertex (f.nextVertex a))) ∨
        (f.vertices.length ≠ 4 ∧ p.1 = f.nextVertex a) := by
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨f, hf, hm⟩
      refine ⟨f, hf, ?_⟩
      by_cases h4 : f.vertices.length = 4
      · rw [if_pos h4] at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        exact Or.inl ⟨h4, hm⟩
      · rw [if_neg h4] at hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        exact Or.inr ⟨h4, hm⟩
    · rintro ⟨f, hf, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩
      · exact ⟨f, hf, by
          rw [if_pos h4]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact hm⟩
      · exact ⟨f, hf, by
          rw [if_neg h4]
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact hm⟩
  by_cases h : p.1 ∈ (g.facesAt a).flatMap (fun f =>
      let n := f.nextVertex a
      if f.vertices.length = 4 then [n, f.nextVertex n] else [n])
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hex => h (hiff.mpr hex))]

/-- ScoreProps.thy: deleteAround_subset -/
theorem deleteAround_subset (g : Graph) (a : Vertex) (ps : List (Vertex × Nat)) :
    deleteAround g a ps ⊆ ps := by
  rw [deleteAround_eq_removeKeyList]
  exact removeKeyList_subset _ _

/-- ScoreProps.thy: distinct_deleteAround -/
theorem distinct_deleteAround (g : Graph) (a : Vertex) {ps : List (Vertex × Nat)}
    (hd : (ps.map Prod.fst).Nodup) :
    ((deleteAround g a ps).map Prod.fst).Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, List.nodup_cons] at hd
    obtain ⟨hp, hd'⟩ := hd
    have hnotin : p.1 ∉ (deleteAround g a ps).map Prod.fst := by
      intro h
      rw [List.mem_map] at h
      obtain ⟨q, hq, hqp⟩ := h
      exact hp (List.mem_map.mpr ⟨q, deleteAround_subset g a ps hq, hqp⟩)
    rw [deleteAroundCons]
    split
    · exact ih hd'
    · exact List.nodup_cons.mpr ⟨hnotin, ih hd'⟩

/-- ScoreProps.thy: deleteAround' (alternative definition). In Lean this is
exactly how `deleteAround` is defined. -/
def deleteAround' (g : Graph) (v : Vertex) (ps : List (Vertex × Nat)) :
    List (Vertex × Nat) :=
  let fs := g.facesAt v
  let vs := fun f =>
    let n1 := f.nextVertex v
    let n2 := f.nextVertex n1
    if f.vertices.length = 4 then [n1, n2] else [n1]
  let ws := fs.flatMap vs
  removeKeyList ws ps

/-- ScoreProps.thy: deleteAround_eq -/
theorem deleteAround_eq (g : Graph) (v : Vertex) (ps : List (Vertex × Nat)) :
    deleteAround g v ps = deleteAround' g v ps := rfl

/-- ScoreProps.thy: deleteAround_nextVertex -/
theorem deleteAround_nextVertex {g : Graph} {a : Vertex} {f : Face}
    {ps : List (Vertex × Nat)} {n : Nat} (hf : f ∈ g.facesAt a) :
    (f.nextVertex a, n) ∉ deleteAround g a ps := by
  rw [deleteAround_eq_removeKeyList, mem_removeKeyList]
  rintro ⟨-, hnot⟩
  apply hnot
  rw [List.mem_flatMap]
  exact ⟨f, hf, by
    by_cases h4 : f.vertices.length = 4
    · rw [if_pos h4]
      simp
    · rw [if_neg h4]
      simp⟩

/-- ScoreProps.thy: deleteAround_nextVertex_nextVertex -/
theorem deleteAround_nextVertex_nextVertex {g : Graph} {a : Vertex} {f : Face}
    {ps : List (Vertex × Nat)} {n : Nat} (hf : f ∈ g.facesAt a)
    (h4 : f.vertices.length = 4) :
    (f.nextVertex (f.nextVertex a), n) ∉ deleteAround g a ps := by
  rw [deleteAround_eq_removeKeyList, mem_removeKeyList]
  rintro ⟨-, hnot⟩
  apply hnot
  rw [List.mem_flatMap]
  exact ⟨f, hf, by
    rw [if_pos h4]
    simp⟩

/-- ScoreProps.thy: deleteAround_prevVertex -/
theorem deleteAround_prevVertex {g : Graph} {a : Vertex} {f : Face}
    {ps : List (Vertex × Nat)} {n : Nat}
    (mgp : minGraphProps g) (ag : a ∈ g.vertices) (hf : f ∈ g.facesAt a) :
    (f.prevVertex a, n) ∉ deleteAround g a ps := by
  have hfg : f ∈ g.faces := minGraphProps5 mgp ag hf
  have hav : a ∈ f.vertices := minGraphProps6 mgp ag hf
  have hd : f.vertices.Nodup := minGraphProps3 mgp hfg
  have e1 : (f.prevVertex a, a) ∈ f.edges := prevVertex_in_edges hd hav
  obtain ⟨f', hf', e⟩ := mgp_edge_face_ex mgp ag hf e1
  have h1 := deleteAround_nextVertex (g := g) (a := a) (f := f') (ps := ps) (n := n) hf'
  have h2 : f'.nextVertex a = f.prevVertex a := (edges_face_eq.mp e).1
  rwa [h2] at h1

/-- ScoreProps.thy: deleteAround_separated. The set inclusion
`𝒱 f ∩ set (map fst (deleteAround g a ps)) ⊆ {a}` is rendered pointwise. -/
theorem deleteAround_separated {g : Graph} {a : Vertex} {f : Face}
    {ps : List (Vertex × Nat)}
    (mgp : minGraphProps g) (fin : g.final = true) (ag : a ∈ g.vertices)
    (h4 : f.vertices.length ≤ 4) (hf : f ∈ g.facesAt a) :
    ∀ x, x ∈ f.vertices → x ∈ (deleteAround g a ps).map Prod.fst → x = a := by
  have hfg : f ∈ g.faces := minGraphProps5 mgp ag hf
  have af : a ∈ f.vertices := minGraphProps6 mgp ag hf
  have d : f.vertices.Nodup := minGraphProps3 mgp hfg
  have hlen : 2 < f.vertices.length := minGraphProps2 mgp hfg
  have h34 : f.vertices.length = 3 ∨ f.vertices.length = 4 := by omega
  intro x hxf hx
  rcases h34 with h3 | h4'
  · have hverts := vertices_triangle h3 af d
    have hprev := triangle_nextVertex_prevVertex h3 af d
    have hxs : x = a ∨ x = f.nextVertex a ∨ x = f.prevVertex a := by
      have : x ∈ ({a, f.nextVertex a, f.nextVertex (f.nextVertex a)} : Set Vertex) := by
        rw [← hverts]
        exact hxf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with rfl | h1 | h2
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (h2.trans hprev))
    rcases hxs with rfl | rfl | rfl
    · rfl
    · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hx
      have hqeq : q = (f.nextVertex a, q.2) := Prod.ext hqp rfl
      exact (deleteAround_nextVertex (n := q.2) hf (hqeq ▸ hq)).elim
    · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hx
      have hqeq : q = (f.prevVertex a, q.2) := Prod.ext hqp rfl
      exact (deleteAround_prevVertex (n := q.2) mgp ag hf (hqeq ▸ hq)).elim
  · have hverts := vertices_quad h4' af d
    have hprev := quad_nextVertex_prevVertex h4' af d
    have hxs : x = a ∨ x = f.nextVertex a ∨ x = f.nextVertex (f.nextVertex a) ∨
        x = f.prevVertex a := by
      have : x ∈ ({a, f.nextVertex a, f.nextVertex (f.nextVertex a),
          f.nextVertex (f.nextVertex (f.nextVertex a))} : Set Vertex) := by
        rw [← hverts]
        exact hxf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with rfl | h1 | h2 | h3'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr (h3'.trans hprev)))
    rcases hxs with rfl | rfl | rfl | rfl
    · rfl
    · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hx
      have hqeq : q = (f.nextVertex a, q.2) := Prod.ext hqp rfl
      exact (deleteAround_nextVertex (n := q.2) hf (hqeq ▸ hq)).elim
    · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hx
      have hqeq : q = (f.nextVertex (f.nextVertex a), q.2) := Prod.ext hqp rfl
      exact (deleteAround_nextVertex_nextVertex (n := q.2) hf h4' (hqeq ▸ hq)).elim
    · obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hx
      have hqeq : q = (f.prevVertex a, q.2) := Prod.ext hqp rfl
      exact (deleteAround_prevVertex (n := q.2) mgp ag hf (hqeq ▸ hq)).elim

/-! ### `separated` lemmas -/

/-- ScoreProps.thy: the `[iff]` lemma `separated g {}`. -/
theorem separated_empty (g : Graph) : separated g (fun _ => False) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

/-- ScoreProps.thy: separated_insert. The set `insert a V` is rendered as the
predicate `fun x => x = a ∨ V x`; the subset premise `V ⊆ 𝒱 g` and the
`∩`-equalities are rendered pointwise. -/
theorem separated_insert {g : Graph} {a : Vertex} {V : Vertex → Prop}
    (mgp : minGraphProps g) (ha : a ∈ g.vertices)
    (Vg : ∀ v, V v → v ∈ g.vertices)
    (ps : separated g V)
    (s2 : ∀ f ∈ g.facesAt a, ¬ V (f.nextVertex a))
    (s3 : ∀ f ∈ g.facesAt a, f.vertices.length ≤ 4 →
      ∀ x, x ∈ f.vertices → V x → x = a) :
    separated g (fun x => x = a ∨ V x) := by
  refine ⟨?_, ?_⟩
  · intro v hv f hf
    rcases hv with rfl | hv
    · exact fun h => h.elim (mgp_facesAt_no_loop mgp ha hf) (s2 f hf)
    · have hvg : v ∈ g.vertices := Vg v hv
      have h1 : f.nextVertex v ≠ a := by
        intro hfa
        obtain ⟨f', hf', hff⟩ := mgp_nextVertex_face_ex2 mgp hvg hf
        rw [hfa] at hf' hff
        exact s2 f' hf' (hff ▸ hv)
      exact fun h => h.elim h1 (ps.1 v hv f hf)
  · intro v hv f hf h4 x
    rcases hv with rfl | hv
    · constructor
      · rintro ⟨hxf, rfl | hxv⟩
        · rfl
        · exact s3 f hf h4 x hxf hxv
      · intro hxa
        subst hxa
        exact ⟨minGraphProps6 mgp ha hf, Or.inl rfl⟩
    · have hvg : v ∈ g.vertices := Vg v hv
      have hsep3 := ps.2 v hv f hf h4
      by_cases hav : a = v
      · subst v
        constructor
        · rintro ⟨hxf, rfl | hxv⟩
          · rfl
          · exact (hsep3 x).mp ⟨hxf, hxv⟩
        · intro hxa
          subst hxa
          exact ⟨minGraphProps6 mgp ha hf, Or.inl rfl⟩
      · have haf : a ∉ f.vertices := by
          intro ha2
          have hfg : f ∈ g.faces := minGraphProps5 mgp hvg hf
          have hfa : f ∈ g.facesAt a := minGraphProps7 mgp hfg ha2
          have hva := s3 f hfa h4 v (minGraphProps6 mgp hvg hf) hv
          exact hav hva.symm
        constructor
        · rintro ⟨hxf, rfl | hxv⟩
          · exact absurd hxf haf
          · exact (hsep3 x).mp ⟨hxf, hxv⟩
        · intro hxv
          subst hxv
          exact ⟨minGraphProps6 mgp hvg hf, Or.inr hv⟩

/-! ### `ExcessNotAtRecList` -/

/-- ScoreProps.thy: ExcessNotAtRecList. Well-founded recursion on the length
of the list (Isabelle: `termination by (relation "measure size")`, using
`length_deleteAround`). -/
def ExcessNotAtRecList : List (Vertex × Nat) → Graph → List Vertex
  | [], _ => []
  | (x, y) :: ps, g =>
    if ExcessNotAtRec ps g ≤ y + ExcessNotAtRec (deleteAround g x ps) g then
      x :: ExcessNotAtRecList (deleteAround g x ps) g
    else ExcessNotAtRecList ps g
termination_by ps _ => ps.length
decreasing_by
  · exact Nat.lt_of_le_of_lt (length_deleteAround g x ps) (Nat.lt_succ_self _)
  · exact Nat.lt_succ_self _

/-- The Isabelle equation `ExcessNotAtRecList [] = (λg. [])`. -/
@[simp]
theorem ExcessNotAtRecList_nil (g : Graph) : ExcessNotAtRecList [] g = [] := by
  simp [ExcessNotAtRecList]

/-- The Isabelle equation for `ExcessNotAtRecList ((x,y)#ps)`. -/
theorem ExcessNotAtRecList_cons (x : Vertex) (y : Nat) (ps : List (Vertex × Nat))
    (g : Graph) :
    ExcessNotAtRecList ((x, y) :: ps) g =
      if ExcessNotAtRec ps g ≤ y + ExcessNotAtRec (deleteAround g x ps) g then
        x :: ExcessNotAtRecList (deleteAround g x ps) g
      else ExcessNotAtRecList ps g := by
  simp [ExcessNotAtRecList]

/-- `ListAux.thy: isTable` (not ported in `ListAux.lean`; first needed here). -/
def isTable (E : Vertex → Nat) (vs : List Vertex) (ps : List (Vertex × Nat)) :
    Prop :=
  ∀ p ∈ ps, p.2 = E p.1 ∧ p.1 ∈ vs

/-- ListAux.thy: isTable_eq -/
theorem isTable_eq {E : Vertex → Nat} {vs : List Vertex} {a : Vertex} {b : Nat}
    {ps : List (Vertex × Nat)} (h : isTable E vs ((a, b) :: ps)) : b = E a :=
  (h (a, b) (List.mem_cons_self)).1

/-- ListAux.thy: isTable_Cons -/
theorem isTable_Cons {E : Vertex → Nat} {vs : List Vertex} {a : Vertex} {b : Nat}
    {ps : List (Vertex × Nat)} (h : isTable E vs ((a, b) :: ps)) : isTable E vs ps :=
  fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- ListAux.thy: isTable_subset -/
theorem isTable_subset {E : Vertex → Nat} {vs : List Vertex} {ws ps : List (Vertex × Nat)}
    (hsub : ps ⊆ ws) (h : isTable E vs ws) : isTable E vs ps :=
  fun p hp => h p (hsub hp)

/-- ScoreProps.thy: isTable_deleteAround -/
theorem isTable_deleteAround {E : Vertex → Nat} {vs : List Vertex} {a : Vertex}
    {b : Nat} {ps : List (Vertex × Nat)} {g : Graph}
    (h : isTable E vs ((a, b) :: ps)) : isTable E vs (deleteAround g a ps) :=
  isTable_subset (deleteAround_subset g a ps) (isTable_Cons h)

/-- ScoreProps.thy: ListSum_ExcessNotAtRecList -/
theorem ListSum_ExcessNotAtRecList {E : Vertex → Nat} {vs : List Vertex} {g : Graph}
    {ps : List (Vertex × Nat)} :
    isTable E vs ps → ExcessNotAtRec ps g = ∑ₗ p ∈ ExcessNotAtRecList ps g, E p := by
  induction ps, g using ExcessNotAtRecList.induct with
  | case1 g => intro _; rw [ExcessNotAtRec_nil]; simp
  | case2 x y ps g hc ih =>
    intro ht
    have hb : y = E x := isTable_eq ht
    have H1 := ih (isTable_deleteAround ht)
    rw [ExcessNotAtRec_cons, ExcessNotAtRecList_cons, if_pos hc, max_eq_right hc,
      ListSum_cons, ← hb, ← H1]
  | case3 x y ps g hc ih =>
    intro ht
    have H2 := ih (isTable_Cons ht)
    rw [ExcessNotAtRec_cons, ExcessNotAtRecList_cons, if_neg hc,
      max_eq_left (Nat.le_of_not_ge hc), ← H2]

/-- ScoreProps.thy: ExcessNotAtRecList_subset (rendered as `List.Subset`). -/
theorem ExcessNotAtRecList_subset {g : Graph} {ps : List (Vertex × Nat)} :
    ExcessNotAtRecList ps g ⊆ ps.map Prod.fst := by
  induction ps, g using ExcessNotAtRecList.induct with
  | case1 g => simp
  | case2 x y ps g hc ih =>
    rw [ExcessNotAtRecList_cons, if_pos hc]
    have h1 : ExcessNotAtRecList (deleteAround g x ps) g ⊆ ps.map Prod.fst := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (ih hv)
      exact List.mem_map_of_mem (deleteAround_subset g x ps hp)
    exact List.cons_subset_cons x h1
  | case3 x y ps g hc ih =>
    rw [ExcessNotAtRecList_cons, if_neg hc]
    exact List.subset_cons_of_subset x ih

/-- ScoreProps.thy: separated_ExcessNotAtRecList. `set (ExcessNotAtRecList ps g)`
is rendered as the membership predicate. -/
theorem separated_ExcessNotAtRecList {g : Graph} {E : Vertex → Nat}
    {ps : List (Vertex × Nat)} (mgp : minGraphProps g) (fin : g.final = true) :
    isTable E g.vertices ps → separated g (· ∈ ExcessNotAtRecList ps g) := by
  revert mgp fin
  induction ps, g using ExcessNotAtRecList.induct with
  | case1 g =>
    intro _ _ _
    rw [ExcessNotAtRecList_nil]
    exact ⟨fun v hv => (List.not_mem_nil hv).elim, fun v hv => (List.not_mem_nil hv).elim⟩
  | case2 x y ps g hc ih =>
    intro mgp fin ht
    have hxg : x ∈ g.vertices := (ht (x, y) (List.mem_cons_self)).2
    have pS : separated g (· ∈ ExcessNotAtRecList (deleteAround g x ps) g) :=
      ih mgp fin (isTable_deleteAround ht)
    have Vg : ∀ v, v ∈ ExcessNotAtRecList (deleteAround g x ps) g →
        v ∈ g.vertices := by
      intro v hv
      obtain ⟨p, hp, hpx⟩ := List.mem_map.mp (ExcessNotAtRecList_subset hv)
      have hps : p ∈ ps := deleteAround_subset g x ps hp
      exact hpx ▸ (ht p (List.mem_cons_of_mem _ hps)).2
    have s2' : ∀ f ∈ g.facesAt x,
        ¬ (f.nextVertex x ∈ ExcessNotAtRecList (deleteAround g x ps) g) := by
      intro f hf hmem
      obtain ⟨p, hp, hpx⟩ := List.mem_map.mp (ExcessNotAtRecList_subset hmem)
      have hpeq : p = (f.nextVertex x, p.2) := Prod.ext hpx rfl
      exact deleteAround_nextVertex (n := p.2) hf (hpeq ▸ hp)
    have s3' : ∀ f ∈ g.facesAt x, f.vertices.length ≤ 4 →
        ∀ v, v ∈ f.vertices → v ∈ ExcessNotAtRecList (deleteAround g x ps) g →
          v = x := by
      intro f hf h4 v hvf hv
      exact deleteAround_separated mgp fin hxg h4 hf v hvf
        (ExcessNotAtRecList_subset hv)
    rw [ExcessNotAtRecList_cons, if_pos hc]
    have hconv := separated_insert mgp hxg Vg pS s2' s3'
    refine ⟨fun v hv f hf => ?_, fun v hv f hf h4 x' => ?_⟩
    · simp only [List.mem_cons]
      exact hconv.1 v (List.mem_cons.mp hv) f hf
    · simp only [List.mem_cons]
      exact hconv.2 v (List.mem_cons.mp hv) f hf h4 x'
  | case3 x y ps g hc ih =>
    intro mgp fin ht
    rw [ExcessNotAtRecList_cons, if_neg hc]
    exact ih mgp fin (isTable_Cons ht)

/-- ScoreProps.thy: isTable_ExcessTable -/
theorem isTable_ExcessTable (g : Graph) (vs : List Vertex) :
    isTable (ExcessAt g) vs (ExcessTable g vs) := by
  intro p hp
  rw [ExcessTable, List.mem_filterMap] at hp
  obtain ⟨v, hv, hsome⟩ := hp
  by_cases he : 0 < ExcessAt g v
  · simp only [he, if_true, Option.some.injEq] at hsome
    subst hsome
    exact ⟨rfl, hv⟩
  · simp only [he, if_false, reduceCtorEq] at hsome

/-- ScoreProps.thy: ExcessTable_subset -/
theorem ExcessTable_subset (g : Graph) (vs : List Vertex) :
    (ExcessTable g vs).map Prod.fst ⊆ vs := by
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  rw [ExcessTable, List.mem_filterMap] at hp
  obtain ⟨v, hv, hsome⟩ := hp
  by_cases he : 0 < ExcessAt g v
  · simp only [he, if_true, Option.some.injEq] at hsome
    subst hsome
    change v = x at hpx
    subst hpx
    exact hv
  · simp only [he, if_false, reduceCtorEq] at hsome

/-- ScoreProps.thy: distinct_ExcessNotAtRecList -/
theorem distinct_ExcessNotAtRecList {g : Graph} {ps : List (Vertex × Nat)} :
    (ps.map Prod.fst).Nodup → (ExcessNotAtRecList ps g).Nodup := by
  induction ps, g using ExcessNotAtRecList.induct with
  | case1 g => intro _; simp
  | case2 x y ps g hc ih =>
    intro hd
    rw [List.map_cons, List.nodup_cons] at hd
    obtain ⟨hx, hd'⟩ := hd
    have H1 : (ExcessNotAtRecList (deleteAround g x ps) g).Nodup :=
      ih (distinct_deleteAround g x hd')
    have hnotin : x ∉ ExcessNotAtRecList (deleteAround g x ps) g := by
      intro h
      obtain ⟨p, hp, hpx⟩ := List.mem_map.mp (ExcessNotAtRecList_subset h)
      exact hx (List.mem_map.mpr ⟨p, deleteAround_subset g x ps hp, hpx⟩)
    rw [ExcessNotAtRecList_cons, if_pos hc, List.nodup_cons]
    exact ⟨hnotin, H1⟩
  | case3 x y ps g hc ih =>
    intro hd
    rw [List.map_cons, List.nodup_cons] at hd
    rw [ExcessNotAtRecList_cons, if_neg hc]
    exact ih hd.2

/-! ### `ExcessTable_cont` / `ExcessTable'` (alternative definition) -/

/-- ScoreProps.thy: ExcessTable_cont -/
def ExcessTable_cont (E : Vertex → Nat) : List Vertex → List (Vertex × Nat)
  | [] => []
  | v :: vs =>
    let vi := E v
    if 0 < vi then (v, vi) :: ExcessTable_cont E vs else ExcessTable_cont E vs

/-- ScoreProps.thy: ExcessTable' -/
def ExcessTable' (g : Graph) (vs : List Vertex) : List (Vertex × Nat) :=
  ExcessTable_cont (ExcessAt g) vs

/-- One-step unfolding of `ExcessTable_cont`. -/
theorem ExcessTable_cont_cons (E : Vertex → Nat) (v : Vertex) (vs : List Vertex) :
    ExcessTable_cont E (v :: vs) =
      if 0 < E v then (v, E v) :: ExcessTable_cont E vs
      else ExcessTable_cont E vs := rfl

/-- Auxiliary (Isabelle proves this inline by `induct vs; auto`):
the first components of `ExcessTable_cont E vs` are contained in `vs`. -/
theorem ExcessTable_cont_subset (E : Vertex → Nat) (vs : List Vertex) :
    (ExcessTable_cont E vs).map Prod.fst ⊆ vs := by
  induction vs with
  | nil => simp [ExcessTable_cont]
  | cons v vs ih =>
    intro x hx
    rw [ExcessTable_cont_cons] at hx
    by_cases h : 0 < E v
    · rw [if_pos h, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem v (ih hx)
    · rw [if_neg h] at hx
      exact List.mem_cons_of_mem v (ih hx)

/-- ScoreProps.thy: distinct_ExcessTable_cont -/
theorem distinct_ExcessTable_cont (g : Graph) {vs : List Vertex} (hd : vs.Nodup) :
    ((ExcessTable_cont (ExcessAt g) vs).map Prod.fst).Nodup := by
  induction vs with
  | nil => simp [ExcessTable_cont]
  | cons v vs ihv =>
    rw [List.nodup_cons] at hd
    obtain ⟨hv, hd'⟩ := hd
    have IH := ihv hd'
    have hnotin : v ∉ (ExcessTable_cont (ExcessAt g) vs).map Prod.fst :=
      fun h => hv (ExcessTable_cont_subset _ _ h)
    rw [ExcessTable_cont_cons]
    by_cases h : 0 < ExcessAt g v
    · rw [if_pos h, List.map_cons, List.nodup_cons]
      exact ⟨hnotin, IH⟩
    · rw [if_neg h]
      exact IH

/-- ScoreProps.thy: ExcessTable_cont_eq. Isabelle's list comprehension
`[(v, E v). v \<leftarrow> [v\<leftarrow>vs . 0 < E v]]`. -/
theorem ExcessTable_cont_eq (E : Vertex → Nat) (vs : List Vertex) :
    ExcessTable_cont E vs =
      ((vs.filter fun v => 0 < E v).map fun v => (v, E v)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : 0 < E v <;>
      simp [ExcessTable_cont_cons, List.filter_cons, List.map_cons, h, ih]

/-- Auxiliary: a `filterMap` with an `if` is a `filter` followed by a `map`. -/
private theorem filterMap_if_some_eq_filter_map {α β : Type*} (p : α → Prop)
    [DecidablePred p] (F : α → β) (vs : List α) :
    (vs.filterMap fun v => if p v then some (F v) else none) =
      (vs.filter p).map F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : p v <;>
      simp [List.filterMap_cons, List.filter_cons, List.map_cons, h, ih]

/-- ScoreProps.thy: ExcessTable_eq (stated pointwise; Isabelle has a
function equality). -/
theorem ExcessTable_eq (g : Graph) (vs : List Vertex) :
    ExcessTable g vs = ExcessTable' g vs := by
  unfold ExcessTable ExcessTable'
  rw [ExcessTable_cont_eq]
  exact filterMap_if_some_eq_filter_map (fun v => 0 < ExcessAt g v)
    (fun v => (v, ExcessAt g v)) vs

/-- ScoreProps.thy: distinct_ExcessTable -/
theorem distinct_ExcessTable {g : Graph} {vs : List Vertex} (hd : vs.Nodup) :
    ((ExcessTable g vs).map Prod.fst).Nodup := by
  rw [ExcessTable_eq]
  exact distinct_ExcessTable_cont g hd

/-- ScoreProps.thy: ExcessNotAt_eq. `set V ⊆ set (vertices g)` and
`separated g (set V)` are rendered pointwise. -/
theorem ExcessNotAt_eq {g : Graph} (mgp : minGraphProps g) (fin : g.final = true) :
    ∃ V : List Vertex, ExcessNotAt g none = ∑ₗ v ∈ V, ExcessAt g v ∧
      separated g (· ∈ V) ∧ (∀ v ∈ V, v ∈ g.vertices) ∧ V.Nodup := by
  refine ⟨ExcessNotAtRecList (ExcessTable g g.vertices) g, ?_, ?_, ?_, ?_⟩
  · exact ListSum_ExcessNotAtRecList (isTable_ExcessTable g g.vertices)
  · exact separated_ExcessNotAtRecList mgp fin (isTable_ExcessTable g g.vertices)
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (ExcessNotAtRecList_subset hv)
    exact ExcessTable_subset g g.vertices (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · exact distinct_ExcessNotAtRecList (distinct_ExcessTable List.nodup_range)

/-- ScoreProps.thy: excess_eq. Isabelle's `b t q` is `squanderVertex t q`,
`d 3`/`d 4` are `d3_const`/`d4_const`. The case split on `q` (`arith` +
`simp` in Isabelle) is done by splitting both variables into the cases
`0..7`; each concrete case is a closed `Nat` computation. -/
theorem excess_eq {t q : Nat} (h : t + q ≤ 7) :
    excessAtType t q 0 + t * d3_const + q * d4_const = squanderVertex t q := by
  have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; omega)

/-- ScoreProps.thy: excess_eq1 -/
theorem excess_eq1 {g : Graph} {v : Vertex} (pl : inv g) (fin : g.final = true)
    (hg : tame g) (he : except g v = 0) (hv : v ∈ g.vertices) :
    ExcessAt g v + tri g v * d3_const + quad g v * d4_const =
      squanderVertex (tri g v) (quad g v) := by
  have hfv : finalVertex g v = true := finalVertexI pl fin hv
  have hnot : ¬ (!finalVertex g v) = true := by simp [hfv]
  unfold ExcessAt
  rw [if_neg hnot, he]
  exact excess_eq (faceCountMax_bound hg hv)

/-! ### Separating -/

/-- ScoreProps.thy: separating -/
def separating {α β : Type*} (V : Set α) (F : α → Set β) : Prop :=
  ∀ v1 ∈ V, ∀ v2 ∈ V, v1 ≠ v2 → F v1 ∩ F v2 = ∅

/-- ScoreProps.thy: separating_insert1 -/
theorem separating_insert1 {α β : Type*} {V : Set α} {F : α → Set β} {a : α}
    (h : separating (insert a V) F) : separating V F :=
  fun v1 h1 v2 h2 hne =>
    h v1 (Set.mem_insert_of_mem _ h1) v2 (Set.mem_insert_of_mem _ h2) hne

/-- ScoreProps.thy: separating_insert2 -/
theorem separating_insert2 {α β : Type*} {V : Set α} {F : α → Set β} {a v : α}
    (h : separating (insert a V) F) (ha : a ∉ V) (hv : v ∈ V) :
    F a ∩ F v = ∅ :=
  h a (Set.mem_insert _ _) v (Set.mem_insert_of_mem _ hv) (fun e => ha (e ▸ hv))

/-- ScoreProps.thy: sum_disj_Union. Stated over `Finset`s (finiteness is then
automatic); `separating` is taken on the coerced sets, as in Isabelle. -/
theorem sum_disj_Union {α β : Type*} [DecidableEq α] [DecidableEq β] (V : Finset α)
    (F : α → Finset β) (w : β → Nat)
    (hsep : separating (↑V : Set α) (fun a => (↑(F a) : Set β))) :
    ∑ v ∈ V, ∑ f ∈ F v, w f = ∑ f ∈ V.biUnion F, w f := by
  rw [Finset.sum_biUnion]
  intro v1 hv1 v2 hv2 hne
  show Disjoint (F v1) (F v2)
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.coe_inj, Finset.coe_inter,
    Finset.coe_empty]
  exact hsep v1 hv1 v2 hv2 hne

/-- Auxiliary bridge: `List.filter` with a decidable `Prop` commutes with
`List.toFinset` (the naive `List.toFinset_filter` introduces a `decide`
normal form that does not match `Finset.filter`'s). -/
private theorem toFinset_filter_prop {α : Type*} [DecidableEq α] (p : α → Prop)
    [DecidablePred p] (l : List α) :
    (l.filter p).toFinset = l.toFinset.filter p := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter,
    decide_eq_true_eq]

/-- ScoreProps.thy: separated_separating. `set V` is rendered as the
set-builder `{v | v ∈ V}`, and `set (facesAt g v) ∩ P` as a set-builder. -/
theorem separated_separating {g : Graph} {V : List Vertex} {P : Face → Prop}
    (Vg : ∀ v ∈ V, v ∈ g.vertices) (pS : separated g (· ∈ V))
    (noex : ∀ f, P f → f.vertices.length ≤ 4) :
    separating {v | v ∈ V} (fun v => {f | f ∈ g.facesAt v ∧ P f}) := by
  intro v1 hv1 v2 hv2 hne
  rw [Set.eq_empty_iff_forall_notMem]
  intro f hf
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hf
  obtain ⟨⟨hf1, hpf⟩, hf2, -⟩ := hf
  have hl : f.vertices.length ≤ 4 := noex f hpf
  have h1 : v1 ∈ f.vertices := ((pS.2 v1 hv1 f hf1 hl v1).mpr rfl).1
  have h12 : v1 = v2 := (pS.2 v2 hv2 f hf2 hl v1).mp ⟨h1, hv1⟩
  exact hne h12

/-- ScoreProps.thy: ListSum_V_F_eq_ListSum_F -/
theorem ListSum_V_F_eq_ListSum_F {g : Graph} {V : List Vertex} (P : Face → Prop)
    [DecidablePred P]
    (pl : inv g) (pS : separated g (· ∈ V)) (dist : V.Nodup)
    (V_subset : ∀ v ∈ V, v ∈ g.vertices)
    (noex : ∀ f, P f → f.vertices.length ≤ 4) (w : Face → Nat) :
    (∑ₗ v ∈ V, ∑ₗ f ∈ (g.facesAt v).filter P, w f) =
      ∑ₗ f ∈ g.faces.filter (fun f => ∃ v ∈ V, f ∈ g.facesAt v ∧ P f), w f := by
  have mgp : minGraphProps g := inv_mgp pl
  have s := separated_separating V_subset pS noex
  have hdist : ∀ v ∈ V, ((g.facesAt v).filter P).Nodup :=
    fun v hv => (mgp_dist_facesAt mgp (V_subset v hv)).filter P
  have hsep : separating (↑V.toFinset : Set Vertex)
      (fun v => (↑((g.facesAt v).toFinset.filter P) : Set Face)) := by
    intro v1 hv1 v2 hv2 hne
    have h := s v1 (by simpa using hv1) v2 (by simpa using hv2) hne
    rw [Set.eq_empty_iff_forall_notMem] at h ⊢
    intro f hf
    apply h f
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter,
      List.mem_toFinset] at hf
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact hf
  have h1 : (∑ₗ v ∈ V, ∑ₗ f ∈ (g.facesAt v).filter P, w f) =
      ∑ v ∈ V.toFinset, ∑ f ∈ (g.facesAt v).toFinset.filter P, w f := by
    rw [ListSum_conv_sum dist]
    exact Finset.sum_congr rfl fun v hv => by
      rw [ListSum_conv_sum (hdist v (List.mem_toFinset.mp hv)),
        toFinset_filter_prop]
  have h2 : (∑ v ∈ V.toFinset, ∑ f ∈ (g.facesAt v).toFinset.filter P, w f) =
      ∑ f ∈ V.toFinset.biUnion (fun v => (g.facesAt v).toFinset.filter P), w f :=
    sum_disj_Union _ _ _ hsep
  have h3 : (∑ f ∈ V.toFinset.biUnion (fun v => (g.facesAt v).toFinset.filter P),
        w f) =
      ∑ f ∈ g.faces.toFinset.filter (fun f => ∃ v ∈ V, f ∈ g.facesAt v ∧ P f),
        w f := by
    congr 1
    ext f
    simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter]
    constructor
    · rintro ⟨v, hv, hf, hpf⟩
      exact ⟨minGraphProps5 mgp (V_subset v hv) hf, v, hv, hf, hpf⟩
    · rintro ⟨-, v, hv, hf, hpf⟩
      exact ⟨v, hv, hf, hpf⟩
  have h4 : (∑ f ∈ g.faces.toFinset.filter
        (fun f => ∃ v ∈ V, f ∈ g.facesAt v ∧ P f), w f) =
      ∑ₗ f ∈ g.faces.filter (fun f => ∃ v ∈ V, f ∈ g.facesAt v ∧ P f), w f := by
    rw [ListSum_conv_sum ((minGraphProps11' mgp).filter _), toFinset_filter_prop]
  exact h1.trans (h2.trans (h3.trans h4))

/-- `Graph.thy: noExceptionals` (not ported in `Graph.lean`; first needed
here). Isabelle's set argument is rendered as a predicate. -/
def noExceptionals (g : Graph) (V : Vertex → Prop) : Prop :=
  ∀ v, V v → exceptionalVertex g v = false

/-- ScoreProps.thy: separated_disj_Union2 -/
theorem separated_disj_Union2 {g : Graph} {V : List Vertex} (w : Face → Nat)
    (pl : inv g) (fin : g.final = true) (ne : noExceptionals g (· ∈ V))
    (pS : separated g (· ∈ V)) (dist : V.Nodup)
    (V_subset : ∀ v ∈ V, v ∈ g.vertices) :
    (∑ₗ v ∈ V, ∑ₗ f ∈ g.facesAt v, w f) =
      ∑ₗ f ∈ g.faces.filter (fun f => ∃ v ∈ V, f ∈ g.facesAt v), w f := by
  have hP : ∀ v ∈ V, ∀ f ∈ g.facesAt v, f.vertices.length ≤ 4 :=
    fun v hv f hf => not_exceptional pl fin (V_subset v hv) hf (ne v hv)
  have h := ListSum_V_F_eq_ListSum_F (fun f => f.vertices.length ≤ 4) pl pS dist
    V_subset (fun f hf => hf) w
  have hflt : ∀ v ∈ V,
      (g.facesAt v).filter (fun f => f.vertices.length ≤ 4) = g.facesAt v :=
    fun v hv => List.filter_eq_self.mpr fun f hf => decide_eq_true (hP v hv f hf)
  have hflt2 : g.faces.filter
        (fun f => ∃ v ∈ V, f ∈ g.facesAt v ∧ f.vertices.length ≤ 4) =
      g.faces.filter (fun f => ∃ v ∈ V, f ∈ g.facesAt v) := by
    apply List.filter_congr
    intro f _
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨v, hv, hf, -⟩
      exact ⟨v, hv, hf⟩
    · rintro ⟨v, hv, hf⟩
      exact ⟨v, hv, hf, hP v hv f hf⟩
  have heq : (∑ₗ v ∈ V, ∑ₗ f ∈ (g.facesAt v).filter (fun f => f.vertices.length ≤ 4),
        w f) =
      ∑ₗ v ∈ V, ∑ₗ f ∈ g.facesAt v, w f :=
    ListSum_eq (fun v hv => by rw [hflt v hv])
  rw [heq, hflt2] at h
  exact h

/-- ScoreProps.thy: squanderFace_distr2. Isabelle's `d |vertices f|` is
`squanderFace f.vertices.length`; `d 3`/`d 4` are `d3_const`/`d4_const`. -/
theorem squanderFace_distr2 {g : Graph} {V : List Vertex}
    (pl : inv g) (fin : g.final = true) (ne : noExceptionals g (· ∈ V))
    (pS : separated g (· ∈ V)) (dist : V.Nodup)
    (V_subset : ∀ v ∈ V, v ∈ g.vertices) :
    (∑ₗ f ∈ g.faces.filter (fun f => ∃ v ∈ V, f ∈ g.facesAt v),
        squanderFace f.vertices.length) =
      ∑ₗ v ∈ V, (tri g v * d3_const + quad g v * d4_const) := by
  have mgp : minGraphProps g := inv_mgp pl
  rw [← separated_disj_Union2 (fun f => squanderFace f.vertices.length) pl fin ne pS
    dist V_subset]
  apply ListSum_eq
  intro v hv
  have hvg : v ∈ g.vertices := V_subset v hv
  have hfin_all : ∀ f ∈ g.facesAt v, f.final = true :=
    fun f hf => plane_final_facesAt pl fin hvg hf
  have d : ∀ f ∈ g.facesAt v, f.vertices.length = 3 ∨ f.vertices.length = 4 := by
    intro f hf
    have hle : f.vertices.length ≤ 4 := not_exceptional pl fin hvg hf (ne v hv)
    have hge : 3 ≤ f.vertices.length :=
      planeN4 pl (minGraphProps5 mgp hvg hf)
    omega
  have hsplit : (∑ₗ f ∈ g.facesAt v, squanderFace f.vertices.length) =
      (∑ₗ f ∈ (g.facesAt v).filter (fun f => f.vertices.length = 3),
        squanderFace f.vertices.length) +
      (∑ₗ f ∈ (g.facesAt v).filter (fun f => f.vertices.length = 4),
        squanderFace f.vertices.length) := by
    apply ListSum_disj_union
    · exact (mgp_dist_facesAt mgp hvg).filter _
    · exact (mgp_dist_facesAt mgp hvg).filter _
    · exact mgp_dist_facesAt mgp hvg
    · intro x
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · intro hx
        rcases d x hx with h3 | h4
        · exact Or.inl ⟨hx, h3⟩
        · exact Or.inr ⟨hx, h4⟩
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩)
        · exact hx
        · exact hx
    · intro x hx3 hx4
      simp only [List.mem_filter, decide_eq_true_eq] at hx3 hx4
      omega
  have h3sum : (∑ₗ f ∈ (g.facesAt v).filter (fun f => f.vertices.length = 3),
        squanderFace f.vertices.length) =
      ((g.facesAt v).filter (fun f => f.vertices.length = 3)).length * d3_const := by
    rw [← listsum_const]
    apply ListSum_eq
    intro f hf
    simp only [List.mem_filter, decide_eq_true_eq] at hf
    rw [hf.2]
    rfl
  have h4sum : (∑ₗ f ∈ (g.facesAt v).filter (fun f => f.vertices.length = 4),
        squanderFace f.vertices.length) =
      ((g.facesAt v).filter (fun f => f.vertices.length = 4)).length * d4_const := by
    rw [← listsum_const]
    apply ListSum_eq
    intro f hf
    simp only [List.mem_filter, decide_eq_true_eq] at hf
    rw [hf.2]
    rfl
  have htri : tri g v =
      ((g.facesAt v).filter (fun f => f.vertices.length = 3)).length := by
    unfold tri
    congr 1
    apply List.filter_congr
    intro f hf
    rw [hfin_all f hf, Bool.true_and, beq_eq_decide]
  have hquad : quad g v =
      ((g.facesAt v).filter (fun f => f.vertices.length = 4)).length := by
    unfold quad
    congr 1
    apply List.filter_congr
    intro f hf
    rw [hfin_all f hf, Bool.true_and, beq_eq_decide]
  rw [hsplit, h3sum, h4sum, htri, hquad]

/-- ScoreProps.thy: separated_subset. The subset `V1 ⊆ V2` is rendered
pointwise. -/
theorem separated_subset {g : Graph} {V1 V2 : Vertex → Prop}
    (hsub : ∀ v, V1 v → V2 v) (h : separated g V2) : separated g V1 := by
  refine ⟨fun v hv f hf => ?_, fun v hv f hf h4 x => ?_⟩
  · exact fun h1 => h.1 v (hsub v hv) f hf (hsub _ h1)
  · have h2 := h.2 v (hsub v hv) f hf h4 x
    constructor
    · rintro ⟨hxf, h1x⟩
      exact h2.mp ⟨hxf, hsub x h1x⟩
    · intro hxv
      subst hxv
      exact ⟨(h2.mpr rfl).1, hv⟩

end Kepler.Graphs
