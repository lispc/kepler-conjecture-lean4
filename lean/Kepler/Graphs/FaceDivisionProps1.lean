/-
Port of the first block (lines 1–1131) of the Isabelle AFP "Flyspeck-Tame"
theory `FaceDivisionProps.thy`: the `Finality`, `is_prefix`, `is_sublist`,
`is_nextElem`, `nextElem`/`sublist`/`is_nextElem`, `before` and `between`
sections — everything up to (excluding) the `between is_nextElem`
subsubsection.

Source: `reference/afp-flyspeck-tame/FaceDivisionProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Correspondence notes:
- `hd`/`last`/`butlast` ↦ `List.head!`/`List.getLast!`/`List.dropLast`
  (as in `Graph.lean`); list indexing `xs ! i` ↦ `xs[i]!`.
- `distinct` ↦ `List.Nodup`; set equalities and empty set intersections are
  rendered as membership (non-)implications, per project convention.
- The definitions `is_prefix`, `is_sublist`, `is_nextElem`, `before` and
  `pre_between` live in this block of the source file and are ported here.
-/
import Kepler.Graphs.GraphProps
import Kepler.Graphs.FaceDivision
import Kepler.Graphs.RotationLemmas
import Mathlib.Data.List.Rotate

namespace Kepler.Graphs

variable {α : Type _}

/-! ### Auxiliary `getLast!`/`head!`/`getElem!` helpers (no Isabelle counterpart) -/

section AuxHelpers

/-- `getLast!` of an append with a nonempty right part. -/
theorem getLast!_append_right [Inhabited α] (as : List α) {bs : List α} (h : bs ≠ []) :
    (as ++ bs).getLast! = bs.getLast! := by
  have hb : 0 < bs.length := List.length_pos_iff.mpr h
  rw [List.getLast!_eq_getElem!, List.getLast!_eq_getElem!]
  have hlen : (as ++ bs).length - 1 = bs.length - 1 + as.length := by
    rw [List.length_append]; omega
  rw [hlen,
    getElem!_pos (as ++ bs) (bs.length - 1 + as.length) (by rw [List.length_append]; omega),
    getElem!_pos bs (bs.length - 1) (Nat.sub_lt hb Nat.one_pos)]
  exact (List.getElem_append_right' as (Nat.sub_lt hb Nat.one_pos)).symm

/-- `getLast!` of a concatenation. -/
theorem getLast!_concat [Inhabited α] (as : List α) (a : α) :
    (as ++ [a]).getLast! = a := by
  rw [getLast!_append_right as (List.cons_ne_nil _ _)]
  rfl

/-- `getLast!` of a nonempty list is a member. -/
theorem getLast!_mem [Inhabited α] {l : List α} (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_of_getLast? (List.getLast?_eq_some_getLast h)]
  exact List.getLast_mem h

/-- `head!` of a nonempty list is a member. -/
theorem head!_mem [Inhabited α] {l : List α} (h : l ≠ []) : l.head! ∈ l := by
  rw [← List.cons_head!_tail h]
  exact List.mem_cons_self

/-- `dropLast`/`getLast!` decomposition of a nonempty list. -/
theorem dropLast_concat_getLast! [Inhabited α] {l : List α} (h : l ≠ []) :
    l.dropLast ++ [l.getLast!] = l := by
  rw [List.getLast!_of_getLast? (List.getLast?_eq_some_getLast h)]
  exact List.dropLast_concat_getLast h

/-- `getElem!` on an append, left part. -/
theorem getElem!_append_left [Inhabited α] {l₁ l₂ : List α} {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂)[i]! = l₁[i]! := by
  rw [getElem!_pos (l₁ ++ l₂) i (by rw [List.length_append]; omega), getElem!_pos l₁ i h,
    List.getElem_append_left]

/-- `getElem!` on an append, right part. -/
theorem getElem!_append_right [Inhabited α] {l₁ l₂ : List α} {i : Nat}
    (h : l₁.length ≤ i) (hi : i - l₁.length < l₂.length) :
    (l₁ ++ l₂)[i]! = l₂[i - l₁.length]! := by
  have hb : i < (l₁ ++ l₂).length := by rw [List.length_append]; omega
  rw [getElem!_pos (l₁ ++ l₂) i hb, getElem!_pos l₂ (i - l₁.length) hi,
    List.getElem_append_right h]

/-- `getElem!` of a rotated list. -/
theorem getElem!_rotate [Inhabited α] (l : List α) (n k : Nat)
    (h : k < (l.rotate n).length) :
    (l.rotate n)[k]! = l[(k + n) % l.length]! := by
  have hl : 0 < l.length := by
    have := h
    rw [List.length_rotate] at this
    omega
  rw [getElem!_pos (l.rotate n) k h, getElem!_pos l ((k + n) % l.length) (Nat.mod_lt _ hl),
    List.getElem_rotate]

end AuxHelpers

/-! ### Finality -/

section Finality

/-- `Graph.thy: edges` (`ℰ g = ⋃ f ∈ set (faces g). ℰ f`). Not ported in the
definition layer; introduced here for `edges_makeFaceFinal`. -/
def Graph.edges (g : Graph) : Set (Vertex × Vertex) :=
  {p | ∃ f ∈ g.faces, p ∈ f.edges}

/-- FaceDivisionProps.thy: vertices_makeFaceFinal -/
theorem vertices_makeFaceFinal (f : Face) (g : Graph) :
    (makeFaceFinal f g).vertices = g.vertices := rfl

/-- FaceDivisionProps.thy: edges_makeFaceFinal -/
theorem edges_makeFaceFinal (f : Face) (g : Graph) :
    (makeFaceFinal f g).edges = g.edges := by
  apply Set.ext
  intro p
  show (∃ f' ∈ makeFaceFinalFaceList f g.faces, p ∈ f'.edges) ↔
    ∃ f' ∈ g.faces, p ∈ f'.edges
  unfold makeFaceFinalFaceList
  constructor
  · rintro ⟨f', hf', hp⟩
    rcases replace5 hf' with h | h
    · exact ⟨f', h, hp⟩
    · rw [List.mem_singleton] at h
      subst h
      by_cases hf : f ∈ g.faces
      · exact ⟨f, hf, by rwa [edges_setFinal] at hp⟩
      · rw [replace2 hf] at hf'
        exact ⟨setFinal f, hf', hp⟩
  · rintro ⟨f', hf', hp⟩
    by_cases hff : f' = f
    · have hf : f ∈ g.faces := hff ▸ hf'
      refine ⟨setFinal f, replace3 hf (List.mem_singleton_self _), ?_⟩
      rw [edges_setFinal]
      rwa [hff] at hp
    · exact ⟨f', replace4 hf' (Ne.symm hff), hp⟩

/-- FaceDivisionProps.thy: in_set_repl_setFin -/
theorem in_set_repl_setFin {f f' : Face} {fs : List Face}
    (hf : f ∈ fs) (hfin : f.final = true) : f ∈ replace f' [setFinal f'] fs := by
  induction fs with
  | nil => exact absurd hf List.not_mem_nil
  | cons z zs ih =>
    rw [List.mem_cons] at hf
    simp only [replace]
    by_cases hz : z = f'
    · subst hz
      rw [if_pos (beq_self_eq_true _)]
      rcases hf with rfl | hf
      · exact List.mem_append_left _
          (by rw [(setFinal_eq_iff f).mpr hfin]; exact List.mem_singleton_self _)
      · exact List.mem_append_right _ hf
    · have hb : ¬ (z == f') = true := fun h => hz (beq_iff_eq.mp h)
      rw [if_neg hb, List.mem_cons]
      rcases hf with rfl | hf
      · exact Or.inl rfl
      · exact Or.inr (ih hf)

/-- FaceDivisionProps.thy: in_set_repl -/
theorem in_set_repl [BEq α] [LawfulBEq α] {f f' : α} {fs' fs : List α}
    (hf : f ∈ fs) (hne : f ≠ f') : f ∈ replace f' fs' fs :=
  replace4 hf (Ne.symm hne)

/-- FaceDivisionProps.thy: makeFaceFinals_preserve_finals -/
theorem makeFaceFinals_preserve_finals {f f' : Face} {g : Graph}
    (hf : f ∈ finals g) : f ∈ finals (makeFaceFinal f' g) := by
  rw [finals, List.mem_filter] at hf
  rw [finals, List.mem_filter]
  exact ⟨in_set_repl_setFin hf.1 hf.2, hf.2⟩

/-- FaceDivisionProps.thy: len_faces_makeFaceFinal -/
@[simp]
theorem len_faces_makeFaceFinal (f : Face) (g : Graph) :
    (makeFaceFinal f g).faces.length = g.faces.length :=
  length_replace1

/-- FaceDivisionProps.thy: len_finals_makeFaceFinal -/
theorem len_finals_makeFaceFinal {f : Face} {g : Graph}
    (hf : f ∈ g.faces) (hfin : f.final = false) :
    (finals (makeFaceFinal f g)).length = (finals g).length + 1 := by
  have h := length_filter_replace1 (P := Face.final) (x := f) (ys := [setFinal f])
    (xs := g.faces) hf hfin
  rw [show ([setFinal f].filter Face.final) = [setFinal f] from by
    rw [List.filter_cons_of_pos (final_setFinal f), List.filter_nil]] at h
  simpa [finals, makeFaceFinal, makeFaceFinalFaceList] using h

/-- FaceDivisionProps.thy: len_nonFinals_makeFaceFinal -/
theorem len_nonFinals_makeFaceFinal {f : Face} {g : Graph}
    (hfin : f.final = false) (hf : f ∈ g.faces) :
    (nonFinals (makeFaceFinal f g)).length = (nonFinals g).length - 1 := by
  have h := length_filter_replace2 (P := fun f => !f.final) (x := f) (ys := [setFinal f])
    (xs := g.faces) hf (by simp [hfin])
  rw [show ([setFinal f].filter (fun f => !f.final)) = [] from by
    rw [List.filter_cons_of_neg (by simp [Face.final, setFinal]), List.filter_nil]] at h
  simpa [nonFinals, makeFaceFinal, makeFaceFinalFaceList] using h

/-- Auxiliary: membership in `replace x [z] xs` for nodup `xs`
(special case of ListAux.thy `distinct_set_replace`). -/
theorem mem_replace_singleton_of_nodup [BEq α] [LawfulBEq α] {x y z : α} {xs : List α}
    (hd : xs.Nodup) (hx : x ∈ xs) :
    y ∈ replace x [z] xs ↔ y = z ∨ (y ∈ xs ∧ y ≠ x) := by
  induction xs with
  | nil => exact absurd hx List.not_mem_nil
  | cons a as ih =>
    rw [List.mem_cons] at hx
    have hd' : as.Nodup := (List.nodup_cons.mp hd).2
    have ha : a ∉ as := (List.nodup_cons.mp hd).1
    by_cases hax : a = x
    · subst hax
      simp only [replace, beq_self_eq_true, ↓reduceIte]
      rw [List.singleton_append, List.mem_cons, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inr h, fun h' => ha (h' ▸ h)⟩
      · rintro (rfl | ⟨h, hne⟩)
        · exact Or.inl rfl
        · rcases h with rfl | h
          · exact absurd rfl hne
          · exact Or.inr h
    · have hb : ¬ (a == x) = true := fun h => hax (beq_iff_eq.mp h)
      simp only [replace, if_neg hb, List.mem_cons]
      have hxs : x ∈ as := hx.resolve_left (fun h => hax h.symm)
      rw [ih hd' hxs]
      constructor
      · rintro (rfl | rfl | ⟨h, hne⟩)
        · exact Or.inr ⟨Or.inl rfl, hax⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inr h, hne⟩
      · rintro (rfl | ⟨h, hne⟩)
        · exact Or.inr (Or.inl rfl)
        · rcases h with rfl | h
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨h, hne⟩)

/-- FaceDivisionProps.thy: set_finals_makeFaceFinal (membership form) -/
@[simp]
theorem set_finals_makeFaceFinal {f y : Face} {g : Graph}
    (hd : g.faces.Nodup) (hf : f ∈ g.faces) :
    y ∈ finals (makeFaceFinal f g) ↔ y = setFinal f ∨ y ∈ finals g := by
  have hmem := mem_replace_singleton_of_nodup (x := f) (y := y) (z := setFinal f) hd hf
  show y ∈ (replace f [setFinal f] g.faces).filter Face.final ↔
    y = setFinal f ∨ y ∈ g.faces.filter Face.final
  rw [List.mem_filter, hmem, List.mem_filter]
  constructor
  · rintro ⟨h1, hyf⟩
    rcases h1 with rfl | ⟨h, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h, hyf⟩
  · rintro (rfl | ⟨h, hyf⟩)
    · exact ⟨Or.inl rfl, final_setFinal f⟩
    · by_cases hyf' : y = f
      · subst hyf'
        exact ⟨Or.inl ((setFinal_eq_iff _).mpr hyf).symm, hyf⟩
      · exact ⟨Or.inr ⟨h, hyf'⟩, hyf⟩

/-- Equation lemmas for `splitFace` (auxiliary). -/
theorem splitFace_fst_snd (g : Graph) (i j : Vertex) (f' : Face) (ns : List Vertex) :
    (splitFace g i j f' ns).2.1 = (split_face f' i j ns).2 := rfl

/-- Equation lemmas for `splitFace` (auxiliary). -/
theorem splitFace_snd_snd_faces (g : Graph) (i j : Vertex) (f' : Face) (ns : List Vertex) :
    (splitFace g i j f' ns).2.2.faces =
      replace f' [(split_face f' i j ns).2] g.faces ++ [(split_face f' i j ns).1] := rfl

/-- FaceDivisionProps.thy: splitFace_preserve_final -/
theorem splitFace_preserve_final {f f' : Face} {g : Graph} {i j : Vertex} {ns : List Vertex}
    (hf : f ∈ finals g) (hfin : f'.final = false) :
    f ∈ finals (splitFace g i j f' ns).2.2 := by
  rw [finals, List.mem_filter] at hf
  rw [finals, List.mem_filter, splitFace_snd_snd_faces]
  refine ⟨List.mem_append_left _ (in_set_repl hf.1 ?_), hf.2⟩
  intro h
  subst h
  rw [hfin] at hf
  exact absurd hf.2 (by decide)

/-- FaceDivisionProps.thy: splitFace_nonFinal_face -/
theorem splitFace_nonFinal_face {g : Graph} {i j : Vertex} {f' : Face} {ns : List Vertex} :
    (splitFace g i j f' ns).2.1.final = false := rfl

/-- Equation lemmas for `subdivFace'` (auxiliary). -/
theorem subdivFace'_nil (g : Graph) (f : Face) (u : Vertex) (n : Nat) :
    subdivFace' g f u n [] = makeFaceFinal f g := rfl

/-- Equation lemmas for `subdivFace'` (auxiliary). -/
theorem subdivFace'_cons_none (g : Graph) (f : Face) (u : Vertex) (n : Nat)
    (vos : List (Option Vertex)) :
    subdivFace' g f u n (none :: vos) = subdivFace' g f u (n + 1) vos := rfl

/-- Equation lemmas for `subdivFace'` (auxiliary). -/
theorem subdivFace'_cons_some (g : Graph) (f : Face) (u : Vertex) (n : Nat) (v : Vertex)
    (vos : List (Option Vertex)) :
    subdivFace' g f u n (some v :: vos) =
      if f.nextVertex u == v && n == 0 then subdivFace' g f v 0 vos
      else subdivFace' (splitFace g u v f (List.range' g.countVertices n)).2.2
        (splitFace g u v f (List.range' g.countVertices n)).2.1 v 0 vos := rfl

/-- FaceDivisionProps.thy: subdivFace'_preserve_finals -/
theorem subdivFace'_preserve_finals {f : Face} :
    ∀ {g : Graph} {f' : Face} {u : Vertex} {n : Nat} {vos : List (Option Vertex)},
      f ∈ finals g → f'.final = false → f ∈ finals (subdivFace' g f' u n vos) := by
  intro g f' u n vos
  induction vos generalizing g f' u n with
  | nil =>
    intro hf _
    rw [subdivFace'_nil]
    exact makeFaceFinals_preserve_finals hf
  | cons vo vos ih =>
    intro hf hfin
    cases vo with
    | none =>
      rw [subdivFace'_cons_none]
      exact ih hf hfin
    | some v =>
      rw [subdivFace'_cons_some]
      by_cases hcond : (f'.nextVertex u == v && n == 0) = true
      · rw [if_pos hcond]
        exact ih hf hfin
      · rw [if_neg hcond]
        exact ih (splitFace_preserve_final hf hfin) splitFace_nonFinal_face

/-- FaceDivisionProps.thy: subdivFace_pres_finals -/
theorem subdivFace_pres_finals {f f' : Face} {g : Graph} {vos : List (Option Vertex)}
    (hf : f ∈ finals g) (hfin : f'.final = false) :
    f ∈ finals (subdivFace g f' vos) :=
  subdivFace'_preserve_finals hf hfin

end Finality

/-! ### is_prefix -/

section IsPrefix

/-- FaceDivisionProps.thy: is_prefix -/
def is_prefix (ls vs : List α) : Prop := ∃ bs, vs = ls ++ bs

/-- FaceDivisionProps.thy: is_prefix_add -/
theorem is_prefix_add {ls vs as : List α} (h : is_prefix ls vs) :
    is_prefix (as ++ ls) (as ++ vs) := by
  obtain ⟨bs, rfl⟩ := h
  exact ⟨bs, (List.append_assoc _ _ _).symm⟩

/-- FaceDivisionProps.thy: is_prefix_hd -/
@[simp]
theorem is_prefix_hd [Inhabited α] {l : α} {vs : List α} :
    is_prefix [l] vs ↔ l = vs.head! ∧ vs ≠ [] := by
  constructor
  · rintro ⟨bs, rfl⟩
    exact ⟨rfl, List.cons_ne_nil _ _⟩
  · rintro ⟨rfl, hvs⟩
    exact ⟨vs.tail, (List.cons_head!_tail hvs).symm⟩

/-- FaceDivisionProps.thy: is_prefix_f -/
@[simp]
theorem is_prefix_f {a : α} {as vs : List α} :
    is_prefix (a :: as) (a :: vs) ↔ is_prefix as vs := by
  constructor
  · rintro ⟨bs, h⟩
    exact ⟨bs, (List.cons.inj h).2⟩
  · rintro ⟨bs, rfl⟩
    exact ⟨bs, rfl⟩

/-- FaceDivisionProps.thy: splitAt_is_prefix -/
theorem splitAt_is_prefix [BEq α] [LawfulBEq α] {ram : α} {vs : List α} (h : ram ∈ vs) :
    is_prefix ((splitAt ram vs).1 ++ [ram]) vs :=
  ⟨(splitAt ram vs).2, by
    conv_lhs => rw [splitAt_ram h]
    simp [List.append_assoc]⟩

end IsPrefix

/-! ### is_sublist -/

section IsSublist

/-- FaceDivisionProps.thy: is_sublist -/
def is_sublist (ls vs : List α) : Prop := ∃ as bs, vs = as ++ ls ++ bs

/-- FaceDivisionProps.thy: is_prefix_sublist -/
theorem is_prefix_sublist {ls vs : List α} (h : is_prefix ls vs) : is_sublist ls vs := by
  obtain ⟨bs, rfl⟩ := h
  exact ⟨[], bs, rfl⟩

/-- FaceDivisionProps.thy: is_sublist_trans -/
theorem is_sublist_trans {as bs cs : List α} (h1 : is_sublist as bs)
    (h2 : is_sublist bs cs) : is_sublist as cs := by
  obtain ⟨a₁, b₁, rfl⟩ := h1
  obtain ⟨a₂, b₂, rfl⟩ := h2
  exact ⟨a₂ ++ a₁, b₁ ++ b₂, by simp [List.append_assoc]⟩

/-- FaceDivisionProps.thy: is_sublist_add -/
theorem is_sublist_add {as bs xs ys : List α} (h : is_sublist as bs) :
    is_sublist as (xs ++ bs ++ ys) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨xs ++ a, b ++ ys, by simp [List.append_assoc]⟩

/-- FaceDivisionProps.thy: is_sublist_rec -/
theorem is_sublist_rec [DecidableEq α] {xs ys : List α} :
    is_sublist xs ys ↔
      if ys.length < xs.length then False
      else if xs = ys.take xs.length then True else is_sublist xs ys.tail := by
  by_cases h1 : ys.length < xs.length
  · rw [if_pos h1]
    constructor
    · intro hsub
      obtain ⟨as, bs, h⟩ := hsub
      rw [h, List.length_append, List.length_append] at h1
      omega
    · exact False.elim
  · rw [if_neg h1]
    by_cases h2 : xs = ys.take xs.length
    · rw [if_pos h2]
      constructor
      · intro _; trivial
      · intro _
        refine ⟨[], ys.drop xs.length, ?_⟩
        have h3 : ys = ys.take xs.length ++ ys.drop xs.length :=
          (List.take_append_drop _ _).symm
        rw [← h2] at h3
        rw [List.nil_append]
        exact h3
    · rw [if_neg h2]
      constructor
      · rintro ⟨as, bs, h⟩
        have hne : as ≠ [] := by
          intro ha
          subst ha
          rw [List.nil_append] at h
          apply h2
          rw [h]
          exact (List.take_left' rfl).symm
        obtain ⟨a, as', rfl⟩ := List.exists_cons_of_ne_nil hne
        refine ⟨as', bs, ?_⟩
        rw [h]
        rfl
      · rintro ⟨as, bs, h⟩
        have hxs : xs ≠ [] := by
          intro hx
          subst hx
          exact h2 (by simp)
        have hys : ys ≠ [] := by
          intro hy
          subst hy
          rw [List.length_nil] at h1
          exact hxs (List.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h1))
        obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil hys
        refine ⟨y :: as, bs, ?_⟩
        rw [List.tail_cons] at h
        rw [h]
        rfl

/-- FaceDivisionProps.thy: not_sublist_len -/
@[simp]
theorem not_sublist_len {xs ys : List α} (h : ys.length < xs.length) :
    ¬ is_sublist xs ys := by
  rintro ⟨as, bs, hsub⟩
  rw [hsub, List.length_append, List.length_append] at h
  omega

/-- FaceDivisionProps.thy: is_sublist_simp -/
@[simp]
theorem is_sublist_simp {a v : α} {as vs : List α} (h : a ≠ v) :
    is_sublist (a :: as) (v :: vs) ↔ is_sublist (a :: as) vs := by
  constructor
  · rintro ⟨rs, ts, hsub⟩
    have hne : rs ≠ [] := by
      intro hr
      subst hr
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at hsub
      exact h hsub.1.symm
    obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.cons_append, List.cons.injEq] at hsub
    exact ⟨rs', ts, hsub.2⟩
  · rintro ⟨rs, ts, hsub⟩
    exact ⟨v :: rs, ts, by rw [hsub]; rfl⟩

/-- FaceDivisionProps.thy: is_sublist_id -/
@[simp]
theorem is_sublist_id {vs : List α} : is_sublist vs vs :=
  ⟨[], [], by simp⟩

/-- FaceDivisionProps.thy: is_sublist_in -/
theorem is_sublist_in {a : α} {as vs : List α} (h : is_sublist (a :: as) vs) : a ∈ vs := by
  obtain ⟨rs, ts, rfl⟩ := h
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

/-- FaceDivisionProps.thy: is_sublist_in1 -/
theorem is_sublist_in1 {x y : α} {vs : List α} (h : is_sublist [x, y] vs) : y ∈ vs := by
  obtain ⟨rs, ts, rfl⟩ := h
  simp

/-- FaceDivisionProps.thy: is_sublist_notlast -/
@[simp]
theorem is_sublist_notlast [Inhabited α] {x y : α} {vs : List α}
    (hd : vs.Nodup) (hx : x = vs.getLast!) : ¬ is_sublist [x, y] vs := by
  rintro ⟨rs, ts, hsub⟩
  have hvs : vs = (rs ++ [x]) ++ y :: ts := by
    rw [hsub]
    simp [List.append_assoc]
  have hxa : x ∈ rs ++ [x] := List.mem_append_right _ List.mem_cons_self
  have hxb : x ∈ y :: ts := by
    have hgl : vs.getLast! = (y :: ts).getLast! := by
      rw [hvs]
      exact getLast!_append_right _ (List.cons_ne_nil _ _)
    have hx' : x = (y :: ts).getLast! := by rw [hx, hgl]
    rw [hx']
    exact getLast!_mem (List.cons_ne_nil _ _)
  have hdn : ((rs ++ [x]) ++ y :: ts).Nodup := hvs ▸ hd
  exact (List.nodup_append.mp hdn).2.2 x hxa x hxb rfl

/-- FaceDivisionProps.thy: is_sublist_nth1 -/
theorem is_sublist_nth1 [Inhabited α] {x y : α} {ls : List α}
    (h : is_sublist [x, y] ls) :
    ∃ i j, i < ls.length ∧ j < ls.length ∧ ls[i]! = x ∧ ls[j]! = y ∧ i + 1 = j := by
  obtain ⟨as, bs, hsub⟩ := h
  refine ⟨as.length, as.length + 1, ?_, ?_, ?_, ?_, rfl⟩
  · rw [hsub]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [hsub]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [hsub, getElem!_append_left (by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega),
      getElem!_append_right (Nat.le_refl _) (by simp)]
    rw [Nat.sub_self]
    rfl
  · rw [hsub, getElem!_append_left (by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    have e := getElem!_append_right (l₁ := as) (l₂ := [x, y]) (i := as.length + 1)
      (by omega) (by simp)
    rw [show as.length + 1 - as.length = 1 from by omega] at e
    rw [e]
    rfl

/-- FaceDivisionProps.thy: is_sublist_nth2 -/
theorem is_sublist_nth2 [Inhabited α] {x y : α} {ls : List α}
    (h : ∃ i j, i < ls.length ∧ j < ls.length ∧ ls[i]! = x ∧ ls[j]! = y ∧ i + 1 = j) :
    is_sublist [x, y] ls := by
  obtain ⟨i, j, hi, hj, hix, hjy, rfl⟩ := h
  refine ⟨ls.take i, ls.drop (i + 2), ?_⟩
  have h1 : ls.take (i + 1) = ls.take i ++ [ls[i]!] := by
    rw [getElem!_pos ls i hi]
    exact List.take_succ_eq_append_getElem hi
  have h2 : ls.take (i + 2) = ls.take (i + 1) ++ [ls[i + 1]!] := by
    rw [getElem!_pos ls (i + 1) hj]
    exact List.take_succ_eq_append_getElem hj
  have h3 : ls = ls.take (i + 2) ++ ls.drop (i + 2) :=
    (List.take_append_drop (i + 2) ls).symm
  rw [h2, h1, hix, hjy] at h3
  exact h3.trans (by simp [List.append_assoc])

/-- FaceDivisionProps.thy: is_sublist_tl -/
theorem is_sublist_tl {a : α} {as vs : List α} (h : is_sublist (a :: as) vs) :
    is_sublist as vs := by
  obtain ⟨rs, ts, rfl⟩ := h
  exact ⟨rs ++ [a], ts, by simp [List.append_assoc]⟩

/-- FaceDivisionProps.thy: is_sublist_hd -/
theorem is_sublist_hd {a : α} {as vs : List α} (h : is_sublist (a :: as) vs) :
    is_sublist [a] vs := by
  obtain ⟨rs, ts, rfl⟩ := h
  exact ⟨rs, as ++ ts, by simp [List.append_assoc]⟩

/-- FaceDivisionProps.thy: is_sublist_hd_eq -/
@[simp]
theorem is_sublist_hd_eq {a : α} {vs : List α} : is_sublist [a] vs ↔ a ∈ vs := by
  constructor
  · rintro ⟨rs, ts, rfl⟩
    simp
  · intro h
    obtain ⟨s, t, rfl⟩ := List.append_of_mem h
    exact ⟨s, t, by simp [List.append_assoc]⟩

/-- FaceDivisionProps.thy: is_sublist_distinct_prefix -/
theorem is_sublist_distinct_prefix {v : α} {as vs : List α}
    (h : is_sublist (v :: as) (v :: vs)) (hd : (v :: vs).Nodup) : is_prefix as vs := by
  obtain ⟨rs, ts, hsub⟩ := h
  have hv : v ∉ vs := (List.nodup_cons.mp hd).1
  have hnot : ¬ is_sublist (v :: as) vs := fun hs => hv (is_sublist_in hs)
  have hrs : rs = [] := by
    cases rs with
    | nil => rfl
    | cons r rs' =>
      exfalso
      simp only [List.cons_append, List.cons.injEq] at hsub
      exact hnot ⟨rs', ts, hsub.2⟩
  subst hrs
  simp only [List.nil_append, List.cons_append, List.cons.injEq] at hsub
  exact ⟨ts, hsub.2⟩

/-- FaceDivisionProps.thy: is_sublist_distinct -/
theorem is_sublist_distinct {as vs : List α} (h : is_sublist as vs) (hd : vs.Nodup) :
    as.Nodup := by
  obtain ⟨rs, ts, rfl⟩ := h
  exact (List.nodup_append.mp (List.nodup_append.mp hd).1).2.1

/-- FaceDivisionProps.thy: is_sublist_y_hd -/
theorem is_sublist_y_hd [Inhabited α] {x y : α} {vs : List α}
    (hd : vs.Nodup) (hy : y = vs.head!) : ¬ is_sublist [x, y] vs := by
  rintro ⟨rs, ts, hsub⟩
  have hvs : vs = (rs ++ [x]) ++ y :: ts := by
    rw [hsub]
    simp [List.append_assoc]
  have hyb : y ∈ y :: ts := List.mem_cons_self
  have hya : y ∈ rs ++ [x] := by
    have hh : vs.head! = (rs ++ [x]).head! := by
      rw [hvs]
      exact List.head!_append _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
    have hy' : y = (rs ++ [x]).head! := by rw [hy, hh]
    rw [hy']
    exact head!_mem (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  have hdn : ((rs ++ [x]) ++ y :: ts).Nodup := hvs ▸ hd
  exact (List.nodup_append.mp hdn).2.2 y hya y hyb rfl

/-- FaceDivisionProps.thy: is_sublist_at1 -/
theorem is_sublist_at1 [Inhabited α] {x y : α} {as bs : List α}
    (hd : (as ++ bs).Nodup) (h : is_sublist [x, y] (as ++ bs))
    (hx : x ≠ as.getLast!) : is_sublist [x, y] as ∨ is_sublist [x, y] bs := by
  obtain ⟨rs, ts, hsub⟩ := h
  -- hsub : as ++ bs = (rs ++ [x, y]) ++ ts
  have hsub' : (rs ++ [x, y]) ++ ts = as ++ bs := hsub.symm
  rw [List.append_eq_append_iff] at hsub'
  rcases hsub' with ⟨mid, hm1, hm2⟩ | ⟨mid, hm1, hm2⟩
  · -- as = (rs ++ [x, y]) ++ mid
    exact Or.inl ⟨rs, mid, hm1⟩
  · -- rs ++ [x, y] = as ++ mid, bs = mid ++ ts
    cases mid with
    | nil =>
      rw [List.append_nil] at hm1
      exact Or.inl ⟨rs, [], by rw [← hm1]; simp⟩
    | cons m mid' =>
      rw [List.append_eq_append_iff] at hm1
      rcases hm1 with ⟨w, hw1, hw2⟩ | ⟨w, hw1, hw2⟩
      · -- as = rs ++ w, [x, y] = w ++ m :: mid'
        cases w with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hw2
          obtain ⟨rfl, rfl⟩ := hw2
          exact Or.inr ⟨[], ts, by rw [hm2]; rfl⟩
        | cons w₁ w' =>
          simp only [List.cons_append, List.cons.injEq] at hw2
          obtain ⟨rfl, hw2⟩ := hw2
          cases w' with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hw2
            obtain ⟨rfl, rfl⟩ := hw2
            exfalso
            apply hx
            rw [hw1]
            exact (getLast!_concat rs x).symm
          | cons w₂ w'' =>
            simp only [List.cons_append, List.cons.injEq] at hw2
            simp at hw2
      · -- rs = as ++ w, m :: mid' = w ++ [x, y]
        exact Or.inr ⟨w, ts, by rw [hm2, hw2]⟩

/-- FaceDivisionProps.thy: is_sublist_at4 -/
theorem is_sublist_at4 [Inhabited α] {x y : α} {as bs : List α}
    (hd : (as ++ bs).Nodup) (h : is_sublist [x, y] (as ++ bs))
    (hne : as ≠ []) (hx : x = as.getLast!) : y = bs.head! := by
  obtain ⟨rs, ts, hsub⟩ := h
  have hvs : as ++ bs = rs ++ x :: y :: ts := by
    rw [hsub]
    simp [List.append_assoc]
  have has : as = as.dropLast ++ [x] := by
    rw [hx]
    exact (dropLast_concat_getLast! hne).symm
  have hvs2 : as ++ bs = as.dropLast ++ x :: bs := by
    conv_lhs => rw [has]
    simp [List.append_assoc]
  have hbs : bs = y :: ts := (dist_at hd hvs2 hvs).2
  rw [hbs]
  rfl

/-- FaceDivisionProps.thy: is_sublist_at5 -/
theorem is_sublist_at5 [Inhabited α] {x y : α} {as bs : List α}
    (hd : (as ++ bs).Nodup) (h : is_sublist [x, y] (as ++ bs)) :
    is_sublist [x, y] as ∨ is_sublist [x, y] bs ∨ x = as.getLast! ∧ y = bs.head! := by
  by_cases hne : as = []
  · subst hne
    simp only [List.nil_append] at h
    exact Or.inr (Or.inl h)
  · by_cases hx : x = as.getLast!
    · exact Or.inr (Or.inr ⟨hx, is_sublist_at4 hd h hne hx⟩)
    · rcases is_sublist_at1 hd h hx with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)

/-- FaceDivisionProps.thy: is_sublist_rev -/
theorem is_sublist_rev {a b : α} {zs : List α} :
    is_sublist [a, b] zs.reverse ↔ is_sublist [b, a] zs := by
  constructor
  · rintro ⟨as, bs, h⟩
    refine ⟨bs.reverse, as.reverse, ?_⟩
    have : zs = (as ++ [a, b] ++ bs).reverse := by rw [← List.reverse_reverse zs, h]
    rw [this]
    simp [List.reverse_append]
  · rintro ⟨as, bs, h⟩
    refine ⟨bs.reverse, as.reverse, ?_⟩
    rw [h]
    simp [List.reverse_append]

/-- FaceDivisionProps.thy: is_sublist_at5' -/
@[simp]
theorem is_sublist_at5' [Inhabited α] {x y : α} {as bs : List α}
    (ha : as.Nodup) (hb : bs.Nodup) (hdis : ∀ x ∈ as, x ∉ bs)
    (h : is_sublist [x, y] (as ++ bs)) :
    is_sublist [x, y] as ∨ is_sublist [x, y] bs ∨ x = as.getLast! ∧ y = bs.head! :=
  is_sublist_at5 (List.nodup_append.mpr ⟨ha, hb, fun a ha b hb he => hdis a ha (he ▸ hb)⟩) h

/-- FaceDivisionProps.thy: splitAt_is_sublist1R -/
@[simp]
theorem splitAt_is_sublist1R [BEq α] [LawfulBEq α] {ram : α} {vs : List α}
    (h : ram ∈ vs) : is_sublist ((splitAt ram vs).1 ++ [ram]) vs :=
  ⟨[], (splitAt ram vs).2, by
    conv_lhs => rw [splitAt_ram h]
    simp [List.append_assoc]⟩

/-- FaceDivisionProps.thy: splitAt_is_sublist2R -/
@[simp]
theorem splitAt_is_sublist2R [BEq α] [LawfulBEq α] {ram : α} {vs : List α}
    (h : ram ∈ vs) : is_sublist (ram :: (splitAt ram vs).2) vs :=
  ⟨(splitAt ram vs).1, [], by
    conv_lhs => rw [splitAt_ram h]
    simp⟩

end IsSublist


/-! ### is_nextElem -/

section IsNextElem

/-- FaceDivisionProps.thy: is_nextElem -/
def is_nextElem [Inhabited α] (xs : List α) (x y : α) : Prop :=
  is_sublist [x, y] xs ∨ (xs ≠ [] ∧ x = xs.getLast! ∧ y = xs.head!)

/-- FaceDivisionProps.thy: is_nextElem_a -/
theorem is_nextElem_a [Inhabited α] {a b : α} {vs : List α} (h : is_nextElem vs a b) :
    a ∈ vs := by
  rcases h with h | ⟨hne, hx, -⟩
  · exact is_sublist_in h
  · rw [hx]
    exact getLast!_mem hne

/-- FaceDivisionProps.thy: is_nextElem_b -/
theorem is_nextElem_b [Inhabited α] {a b : α} {vs : List α} (h : is_nextElem vs a b) :
    b ∈ vs := by
  rcases h with h | ⟨hne, -, hy⟩
  · exact is_sublist_in1 h
  · rw [hy]
    exact head!_mem hne

/-- FaceDivisionProps.thy: is_nextElem_last_hd -/
theorem is_nextElem_last_hd [Inhabited α] {x y : α} {vs : List α}
    (hd : vs.Nodup) (h : is_nextElem vs x y) (hx : x = vs.getLast!) :
    y = vs.head! := by
  rcases h with h | ⟨-, -, hy⟩
  · exact absurd h (is_sublist_notlast hd hx)
  · exact hy

/-- FaceDivisionProps.thy: is_nextElem_last_ne -/
theorem is_nextElem_last_ne [Inhabited α] {x y : α} {vs : List α}
    (h : is_nextElem vs x y) (hx : x = vs.getLast!) : vs ≠ [] := by
  rcases h with h | ⟨hne, -, -⟩
  · intro hvs
    subst hvs
    obtain ⟨as, bs, hsub⟩ := h
    simp at hsub
  · exact hne

/-- FaceDivisionProps.thy: is_nextElem_sublistI -/
theorem is_nextElem_sublistI [Inhabited α] {x y : α} {vs : List α}
    (h : is_sublist [x, y] vs) : is_nextElem vs x y := Or.inl h

/-- FaceDivisionProps.thy: is_nextElem_nth1 -/
theorem is_nextElem_nth1 [Inhabited α] {x y : α} {ls : List α}
    (h : is_nextElem ls x y) :
    ∃ i j, i < ls.length ∧ j < ls.length ∧ ls[i]! = x ∧ ls[j]! = y ∧
      (i + 1) % ls.length = j := by
  rcases h with h | ⟨hne, hx, hy⟩
  · obtain ⟨i, j, hi, hj, hix, hjy, hij⟩ := is_sublist_nth1 h
    exact ⟨i, j, hi, hj, hix, hjy, by rw [← hij]; exact Nat.mod_eq_of_lt (by omega)⟩
  · have hl : 0 < ls.length := List.length_pos_iff.mpr hne
    refine ⟨ls.length - 1, 0, by omega, hl, ?_, ?_, ?_⟩
    · exact List.getLast!_eq_getElem!.symm.trans hx.symm
    · exact List.head!_eq_getElem!.symm.trans hy.symm
    · have : ls.length - 1 + 1 = ls.length := by omega
      rw [this]
      exact Nat.mod_self _

/-- FaceDivisionProps.thy: is_nextElem_nth2 -/
theorem is_nextElem_nth2 [Inhabited α] {x y : α} {ls : List α}
    (h : ∃ i j, i < ls.length ∧ j < ls.length ∧ ls[i]! = x ∧ ls[j]! = y ∧
      (i + 1) % ls.length = j) : is_nextElem ls x y := by
  obtain ⟨i, j, hi, hj, hix, hjy, hij⟩ := h
  by_cases hcase : i + 1 = ls.length
  · have hj0 : j = 0 := by rw [← hij, hcase]; exact Nat.mod_self _
    refine Or.inr ⟨?_, ?_, ?_⟩
    · intro hnil
      subst hnil
      simp at hi
    · have hi' : i = ls.length - 1 := by omega
      rw [hi'] at hix
      rw [← List.getLast!_eq_getElem!] at hix
      exact hix.symm
    · rw [hj0] at hjy
      rw [← List.head!_eq_getElem!] at hjy
      exact hjy.symm
  · have hj' : j = i + 1 := by
      have hlt : i + 1 < ls.length := by omega
      rw [Nat.mod_eq_of_lt hlt] at hij
      exact hij.symm
    exact Or.inl (is_sublist_nth2 ⟨i, j, hi, hj, hix, hjy, hj'.symm⟩)

/-- FaceDivisionProps.thy: is_nextElem_rotate1_aux -/
theorem is_nextElem_rotate1_aux [Inhabited α] {x y : α} {ls : List α} {m : Nat}
    (h : is_nextElem (ls.rotate m) x y) : is_nextElem ls x y := by
  set n := m % ls.length with hn
  have hrot : ls.rotate m = ls.rotate n := (List.rotate_mod ls m).symm
  rw [hrot] at h
  obtain ⟨i, j, hi, hj, hix, hjy, hij⟩ := is_nextElem_nth1 h
  rw [List.length_rotate] at hi hj hij
  have hl : 0 < ls.length := by omega
  have hix' : ls[(i + n) % ls.length]! = x := by
    rw [← getElem!_rotate ls n i (by rw [List.length_rotate]; exact hi)]
    exact hix
  have hjy' : ls[(j + n) % ls.length]! = y := by
    rw [← getElem!_rotate ls n j (by rw [List.length_rotate]; exact hj)]
    exact hjy
  apply is_nextElem_nth2
  refine ⟨(i + n) % ls.length, (j + n) % ls.length, Nat.mod_lt _ hl, Nat.mod_lt _ hl,
    hix', hjy', ?_⟩
  have e1 : ((i + n) % ls.length + 1) % ls.length = (i + 1 + n) % ls.length := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  have e2 : (j + n) % ls.length = (i + 1 + n) % ls.length := by
    conv_lhs => rw [← hij]
    exact Nat.mod_add_mod _ _ _
  rw [e1, ← e2]

/-- FaceDivisionProps.thy: is_nextElem_rotate_eq -/
@[simp]
theorem is_nextElem_rotate_eq [Inhabited α] {x y : α} {ls : List α} {m : Nat} :
    is_nextElem (ls.rotate m) x y ↔ is_nextElem ls x y := by
  constructor
  · exact is_nextElem_rotate1_aux
  · intro h
    by_cases hnil : ls = []
    · subst hnil
      rw [List.rotate_nil]
      exact h
    · have hl : 0 < ls.length := List.length_pos_iff.mpr hnil
      have hback : (ls.rotate m).rotate (ls.length - m % ls.length) = ls := by
        rw [List.rotate_rotate]
        have key : m + (ls.length - m % ls.length) = ls.length * (m / ls.length + 1) := by
          have h1 := Nat.mod_lt m hl
          have h2 := Nat.div_add_mod m ls.length
          have h3 : ls.length * (m / ls.length + 1) =
              ls.length * (m / ls.length) + ls.length := Nat.mul_succ _ _
          omega
        rw [key, ← List.rotate_mod, Nat.mul_mod_right, List.rotate_zero]
      rw [← hback] at h
      exact is_nextElem_rotate1_aux h

/-- FaceDivisionProps.thy: is_nextElem_congs_eq -/
theorem is_nextElem_congs_eq [Inhabited α] {x y : α} {ls ms : List α}
    (h : cong ls ms) : is_nextElem ls x y ↔ is_nextElem ms x y := by
  obtain ⟨n, rfl⟩ := h
  exact is_nextElem_rotate_eq.symm

/-- FaceDivisionProps.thy: is_nextElem_rev -/
@[simp]
theorem is_nextElem_rev [Inhabited α] {a b : α} {zs : List α} :
    is_nextElem zs.reverse a b ↔ is_nextElem zs b a := by
  unfold is_nextElem
  rw [is_sublist_rev, List.reverse_ne_nil_iff, getLast!_reverse, head!_reverse]
  constructor
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h3, h2⟩
  · rintro (h | ⟨h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h3, h2⟩

/-- FaceDivisionProps.thy: is_nextElem_circ -/
theorem is_nextElem_circ [Inhabited α] {a b : α} {xs : List α}
    (hd : xs.Nodup) (h1 : is_nextElem xs a b) (h2 : is_nextElem xs b a) :
    xs.length ≤ 2 := by
  obtain ⟨i, j, hi, hj, hia, hjb, hij⟩ := is_nextElem_nth1 h1
  obtain ⟨i', j', hi', hj', hia', hjb', hij'⟩ := is_nextElem_nth1 h2
  have hjj' : i = j' :=
    (List.getElem!_inj hi hj' hd).mp (hia.trans hjb'.symm)
  have hii' : j = i' :=
    (List.getElem!_inj hj hi' hd).mp (hjb.trans hia'.symm)
  subst hjj'
  subst hii'
  by_contra hcon
  push Not at hcon
  have hc1 : j = i + 1 ∨ (i + 1 = xs.length ∧ j = 0) := by
    have hle : i + 1 ≤ xs.length := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at hij
      exact Or.inl hij.symm
    · exact Or.inr ⟨heq, by rw [← hij, heq]; exact Nat.mod_self _⟩
  have hc2 : i = j + 1 ∨ (j + 1 = xs.length ∧ i = 0) := by
    have hle : j + 1 ≤ xs.length := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at hij'
      exact Or.inl hij'.symm
    · exact Or.inr ⟨heq, by rw [← hij', heq]; exact Nat.mod_self _⟩
  rcases hc1 with h | ⟨h, h'⟩ <;> rcases hc2 with h2 | ⟨h2, h2'⟩ <;> omega

end IsNextElem

/-! ### nextElem, sublist, is_nextElem -/

section NextElemSublist

/-- FaceDivisionProps.thy: is_sublist_eq -/
theorem is_sublist_eq [BEq α] [LawfulBEq α] [Inhabited α] {c x y : α} {vs : List α}
    (hd : vs.Nodup) (hc : c ≠ y) : (nextElem vs c x = y) ↔ is_sublist [x, y] vs := by
  constructor
  · intro hfn
    rcases nextElem_cases hfn with ⟨-, h2⟩ | ⟨-, -, h2, -⟩ | ⟨us, ws, h3, -⟩
    · exact absurd h2.symm hc
    · exact absurd h2.symm hc
    · exact ⟨us, ws, h3⟩
  · rintro ⟨as, bs, hvs⟩
    have hxa : x ∉ as := by
      have hd' : ((as ++ [x, y]) ++ bs).Nodup := hvs ▸ hd
      have hdis := (List.nodup_append.mp (List.nodup_append.mp hd').1).2.2
      intro hx2
      exact hdis x hx2 x List.mem_cons_self rfl
    rw [hvs, List.append_assoc, nextElem_append hxa]
    show nextElem (x :: y :: bs) c x = y
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true x)]

/-- FaceDivisionProps.thy: is_nextElem1 -/
theorem is_nextElem1 [BEq α] [LawfulBEq α] [Inhabited α] {x y : α} {vs : List α}
    (hd : vs.Nodup) (hx : x ∈ vs) (hfn : nextElem vs vs.head! x = y) :
    is_nextElem vs x y := by
  rcases nextElem_cases hfn with ⟨h1, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨us, ws, h3, -⟩
  · exact absurd hx h1
  · exact Or.inr ⟨h1, h2, h3⟩
  · exact Or.inl ⟨us, ws, h3⟩

/-- FaceDivisionProps.thy: is_nextElem2 -/
theorem is_nextElem2 [BEq α] [LawfulBEq α] [Inhabited α] {x y : α} {vs : List α}
    (hd : vs.Nodup) (hx : x ∈ vs) (h : is_nextElem vs x y) :
    nextElem vs vs.head! x = y := by
  rcases h with h | ⟨-, hxl, hyh⟩
  · by_cases hyhd : y = vs.head!
    · obtain ⟨as, bs, h1⟩ := h
      exfalso
      rw [hyhd] at h1
      cases as with
      | nil =>
        have h2 : vs = x :: (vs.head! :: bs) := h1.trans (by simp)
        have hhd : vs.head! = x := by
          have e := congrArg List.head! h2
          rwa [List.head!_cons] at e
        rw [hhd] at h2
        have hd' : (x :: x :: bs).Nodup := h2 ▸ hd
        exact (List.nodup_cons.mp hd').1 List.mem_cons_self
      | cons a as' =>
        have h2 : vs = a :: (as' ++ x :: vs.head! :: bs) := h1.trans (by simp [List.append_assoc])
        have hhd : vs.head! = a := by
          have e := congrArg List.head! h2
          rwa [List.head!_cons] at e
        rw [hhd] at h2
        have hd' : (a :: (as' ++ x :: a :: bs)).Nodup := h2 ▸ hd
        have hna := (List.nodup_cons.mp hd').1
        exact hna (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact (is_sublist_eq hd (Ne.symm hyhd)).mpr h
  · rw [hxl, hyh]
    exact nextElem_last hd

/-- FaceDivisionProps.thy: nextElem_is_nextElem -/
theorem nextElem_is_nextElem [BEq α] [LawfulBEq α] [Inhabited α] {x y : α} {xs : List α}
    (hd : xs.Nodup) (hx : x ∈ xs) :
    is_nextElem xs x y ↔ nextElem xs xs.head! x = y :=
  ⟨is_nextElem2 hd hx, is_nextElem1 hd hx⟩

/-- FaceDivisionProps.thy: nextElem_congs_eq -/
theorem nextElem_congs_eq [BEq α] [LawfulBEq α] [Inhabited α] {x : α} {xs ys : List α}
    (heq : cong xs ys) (hd : xs.Nodup) (hx : x ∈ xs) :
    nextElem xs xs.head! x = nextElem ys ys.head! x := by
  generalize hy : nextElem xs xs.head! x = y
  have h1 : is_nextElem xs x y := is_nextElem1 hd hx hy
  have h2 : is_nextElem ys x y := (is_nextElem_congs_eq heq).mp h1
  have hd' : ys.Nodup := (cong_distinct heq).mp hd
  have hx' : x ∈ ys := (cong_mem heq).mp hx
  exact (is_nextElem2 hd' hx' h2).symm

/-- FaceDivisionProps.thy: is_sublist_is_nextElem -/
theorem is_sublist_is_nextElem [BEq α] [LawfulBEq α] [Inhabited α] {x y : α} {as vs : List α}
    (hd : vs.Nodup) (hne : is_nextElem vs x y) (hsub : is_sublist as vs)
    (hxin : x ∈ as) (hxnl : x ≠ as.getLast!) : is_sublist [x, y] as := by
  have hasne : as ≠ [] := List.ne_nil_of_mem hxin
  obtain ⟨rs, ts, hvs⟩ := hsub
  have hxnlv : x ≠ vs.getLast! := by
    cases ts with
    | nil =>
      have h1 : vs = rs ++ as := by rw [hvs]; simp
      intro h
      apply hxnl
      rw [h, h1]
      exact getLast!_append_right _ hasne
    | cons t ts' =>
      have h1 : vs = (rs ++ as) ++ t :: ts' := by rw [hvs]
      intro h
      have hxl : vs.getLast! ∈ t :: ts' := by
        have e : vs.getLast! = (t :: ts').getLast! := by
          rw [h1]
          exact getLast!_append_right _ (List.cons_ne_nil _ _)
        rw [e]
        exact getLast!_mem (List.cons_ne_nil _ _)
      rw [← h] at hxl
      have hd' : ((rs ++ as) ++ t :: ts').Nodup := h1 ▸ hd
      have hdis := (List.nodup_append.mp hd').2.2
      exact hdis x (List.mem_append_right _ hxin) x hxl rfl
  have hsubvs : is_sublist [x, y] vs := by
    rcases hne with h | ⟨-, hxl, -⟩
    · exact h
    · exact absurd hxl hxnlv
  have h1 : vs = rs ++ (as ++ ts) := by rw [hvs]; simp [List.append_assoc]
  have hd1 : (rs ++ (as ++ ts)).Nodup := h1 ▸ hd
  have hxnrs : x ∉ rs := by
    intro h
    exact (List.nodup_append.mp hd1).2.2 x h x (List.mem_append_left _ hxin) rfl
  have hxnts : x ∉ ts :=
    fun h => (List.nodup_append.mp (List.nodup_append.mp hd1).2.1).2.2 x hxin x h rfl
  have hnotrs : ¬ is_sublist [x, y] rs := fun hs => hxnrs (is_sublist_in hs)
  have hnotts : ¬ is_sublist [x, y] ts := fun hs => hxnts (is_sublist_in hs)
  have hsub1 : is_sublist [x, y] (rs ++ (as ++ ts)) := h1 ▸ hsubvs
  have hsub2 : is_sublist [x, y] (as ++ ts) := by
    by_cases hrs : rs = []
    · subst hrs
      simpa using hsub1
    · have hxnlrs : x ≠ rs.getLast! := by
        intro h
        apply hxnrs
        rw [h]
        exact getLast!_mem hrs
      rcases is_sublist_at1 hd1 hsub1 hxnlrs with h2 | h2
      · exact absurd h2 hnotrs
      · exact h2
  rcases is_sublist_at1 (List.nodup_append.mp hd1).2.1 hsub2 hxnl with h3 | h3
  · exact h3
  · exact absurd h3 hnotts

end NextElemSublist


/-! ### before -/

section Before

/-- FaceDivisionProps.thy: before -/
def before (vs : List α) (ram₁ ram₂ : α) : Prop :=
  ∃ a b c, vs = a ++ ram₁ :: b ++ ram₂ :: c

variable [BEq α] [LawfulBEq α]

/-- FaceDivisionProps.thy: before_dist_fst_fst -/
@[simp]
theorem before_dist_fst_fst {ram₁ ram₂ : α} {vs : List α}
    (h : before vs ram₁ ram₂) (hd : vs.Nodup) :
    (splitAt ram₂ (splitAt ram₁ vs).1).1 = (splitAt ram₁ (splitAt ram₂ vs).1).1 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨h1, -, h3, -, -, -⟩ := splitAt_dist_ram_all hd hvs
  rw [congrArg Prod.fst h3.symm, congrArg Prod.fst h1.symm]

/-- FaceDivisionProps.thy: before_dist_fst_snd -/
@[simp]
theorem before_dist_fst_snd {ram₁ ram₂ : α} {vs : List α}
    (h : before vs ram₁ ram₂) (hd : vs.Nodup) :
    (splitAt ram₂ (splitAt ram₁ vs).2).1 = (splitAt ram₁ (splitAt ram₂ vs).1).2 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨h1, -, -, h4, -, -⟩ := splitAt_dist_ram_all hd hvs
  rw [congrArg Prod.fst h4.symm, congrArg Prod.snd h1.symm]

/-- FaceDivisionProps.thy: before_dist_snd_fst -/
@[simp]
theorem before_dist_snd_fst {ram₁ ram₂ : α} {vs : List α}
    (h : before vs ram₁ ram₂) (hd : vs.Nodup) :
    (splitAt ram₂ (splitAt ram₁ vs).1).2 = (splitAt ram₁ (splitAt ram₂ vs).2).2 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨-, h2, h3, -, -, -⟩ := splitAt_dist_ram_all hd hvs
  rw [congrArg Prod.snd h3.symm, congrArg Prod.snd h2.symm]

/-- FaceDivisionProps.thy: before_dist_snd_snd -/
@[simp]
theorem before_dist_snd_snd {ram₁ ram₂ : α} {vs : List α}
    (h : before vs ram₁ ram₂) (hd : vs.Nodup) :
    (splitAt ram₂ (splitAt ram₁ vs).2).2 = (splitAt ram₁ (splitAt ram₂ vs).2).1 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨-, h2, -, h4, -, -⟩ := splitAt_dist_ram_all hd hvs
  rw [congrArg Prod.snd h4.symm, congrArg Prod.fst h2.symm]

/-- FaceDivisionProps.thy: before_dist_snd -/
@[simp]
theorem before_dist_snd {ram₁ ram₂ : α} {vs : List α}
    (h : before vs ram₁ ram₂) (hd : vs.Nodup) :
    (splitAt ram₁ (splitAt ram₂ vs).2).1 = (splitAt ram₂ vs).2 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨-, h2, -, -, h5, -⟩ := splitAt_dist_ram_all hd hvs
  rw [congrArg Prod.fst h2.symm]
  exact h5

/-- FaceDivisionProps.thy: before_dist_fst -/
@[simp]
theorem before_dist_fst {ram₁ ram₂ : α} {vs : List α}
    (h : before vs ram₁ ram₂) (hd : vs.Nodup) :
    (splitAt ram₁ (splitAt ram₂ vs).1).1 = (splitAt ram₁ vs).1 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨h1, -, -, -, -, h6⟩ := splitAt_dist_ram_all hd hvs
  rw [congrArg Prod.fst h1.symm]
  exact h6

/-- FaceDivisionProps.thy: before_or -/
theorem before_or {ram₁ ram₂ : α} {vs : List α}
    (h1 : ram₁ ∈ vs) (h2 : ram₂ ∈ vs) (h12 : ram₁ ≠ ram₂) :
    before vs ram₁ ram₂ ∨ before vs ram₂ ram₁ := by
  by_cases hc : ram₂ ∈ (splitAt ram₁ vs).2
  · have e1 : vs = (splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₁ vs).2 := splitAt_ram h1
    have e2 := splitAt_ram hc
    rw [e2] at e1
    refine Or.inl ⟨(splitAt ram₁ vs).1, (splitAt ram₂ (splitAt ram₁ vs).2).1,
      (splitAt ram₂ (splitAt ram₁ vs).2).2, e1.trans (by simp [List.append_assoc])⟩
  · have h2' : ram₂ ∈ (splitAt ram₁ vs).1 := splitAt_mem_fst_of_not_mem_snd hc h1 h2 h12
    have e1 : vs = (splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₁ vs).2 := splitAt_ram h1
    have e2 := splitAt_ram h2'
    rw [e2] at e1
    exact Or.inr ⟨_, _, _, e1⟩

/-- FaceDivisionProps.thy: before_r1 -/
theorem before_r1 {r₁ r₂ : α} {vs : List α} (h : before vs r₁ r₂) : r₁ ∈ vs := by
  obtain ⟨a, b, c, rfl⟩ := h
  simp

/-- FaceDivisionProps.thy: before_r2 -/
theorem before_r2 {r₁ r₂ : α} {vs : List α} (h : before vs r₁ r₂) : r₂ ∈ vs := by
  obtain ⟨a, b, c, rfl⟩ := h
  simp

/-- FaceDivisionProps.thy: before_dist_r2 -/
theorem before_dist_r2 {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h : before vs r₁ r₂) : r₂ ∈ (splitAt r₁ vs).2 := by
  obtain ⟨a, b, c, hvs⟩ := h
  have h1 : vs = a ++ r₁ :: (b ++ r₂ :: c) := by rw [hvs]; simp [List.append_assoc]
  have hsp : (a, b ++ r₂ :: c) = splitAt r₁ vs := splitAt_dist_ram hd h1
  rw [← hsp]
  exact List.mem_append_right _ List.mem_cons_self

/-- FaceDivisionProps.thy: before_dist_not_r2 -/
theorem before_dist_not_r2 {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h : before vs r₁ r₂) : r₂ ∉ (splitAt r₁ vs).1 :=
  fun hm => splitAt_distinct_fst_snd hd _ hm (before_dist_r2 hd h)

/-- FaceDivisionProps.thy: before_dist_r1 -/
theorem before_dist_r1 {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h : before vs r₁ r₂) : r₁ ∈ (splitAt r₂ vs).1 := by
  obtain ⟨a, b, c, hvs⟩ := h
  have hsp : (a ++ r₁ :: b, c) = splitAt r₂ vs := splitAt_dist_ram hd hvs
  rw [← hsp]
  exact List.mem_append_right _ List.mem_cons_self

/-- FaceDivisionProps.thy: before_dist_not_r1 -/
theorem before_dist_not_r1 {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h : before vs r₁ r₂) : r₁ ∉ (splitAt r₂ vs).2 :=
  fun hm => splitAt_distinct_fst_snd hd _ (before_dist_r1 hd h) hm

/-- FaceDivisionProps.thy: before_snd -/
theorem before_snd {r₁ r₂ : α} {vs : List α}
    (h : r₂ ∈ (splitAt r₁ vs).2) : before vs r₁ r₂ := by
  have h1 : r₁ ∈ vs := by
    by_contra hc
    rw [splitAt_no_ram hc] at h
    exact absurd h List.not_mem_nil
  have e1 : vs = (splitAt r₁ vs).1 ++ r₁ :: (splitAt r₁ vs).2 := splitAt_ram h1
  have e2 := splitAt_ram h
  rw [e2] at e1
  exact ⟨(splitAt r₁ vs).1, (splitAt r₂ (splitAt r₁ vs).2).1,
    (splitAt r₂ (splitAt r₁ vs).2).2, e1.trans (by simp [List.append_assoc])⟩

/-- FaceDivisionProps.thy: before_fst -/
theorem before_fst {r₁ r₂ : α} {vs : List α}
    (h2 : r₂ ∈ vs) (h1 : r₁ ∈ (splitAt r₂ vs).1) : before vs r₁ r₂ := by
  have e1 : vs = (splitAt r₂ vs).1 ++ r₂ :: (splitAt r₂ vs).2 := splitAt_ram h2
  have e2 := splitAt_ram h1
  rw [e2] at e1
  exact ⟨_, _, _, e1⟩

/-- FaceDivisionProps.thy: before_dist_eq_fst -/
theorem before_dist_eq_fst {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h2 : r₂ ∈ vs) :
    (r₁ ∈ (splitAt r₂ vs).1) ↔ before vs r₁ r₂ :=
  ⟨before_fst h2, before_dist_r1 hd⟩

/-- FaceDivisionProps.thy: before_dist_eq_snd -/
theorem before_dist_eq_snd {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) :
    (r₂ ∈ (splitAt r₁ vs).2) ↔ before vs r₁ r₂ :=
  ⟨before_snd, before_dist_r2 hd⟩

/-- FaceDivisionProps.thy: before_dist_not1 -/
theorem before_dist_not1 {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h : before vs r₁ r₂) : ¬ before vs r₂ r₁ := by
  intro h'
  have h2 : r₂ ∈ (splitAt r₁ vs).1 := before_dist_r1 hd h'
  have h3 : r₂ ∈ (splitAt r₁ vs).2 := before_dist_r2 hd h
  exact splitAt_distinct_fst_snd hd _ h2 h3

/-- FaceDivisionProps.thy: before_dist_not2 -/
theorem before_dist_not2 {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h1 : r₁ ∈ vs) (h2 : r₂ ∈ vs) (h12 : r₁ ≠ r₂)
    (h : ¬ before vs r₁ r₂) : before vs r₂ r₁ := by
  rcases before_or h1 h2 h12 with h' | h'
  · exact absurd h' h
  · exact h'

/-- FaceDivisionProps.thy: before_dist_eq -/
theorem before_dist_eq {r₁ r₂ : α} {vs : List α}
    (hd : vs.Nodup) (h1 : r₁ ∈ vs) (h2 : r₂ ∈ vs) (h12 : r₁ ≠ r₂) :
    (¬ before vs r₁ r₂) ↔ before vs r₂ r₁ :=
  ⟨before_dist_not2 hd h1 h2 h12, before_dist_not1 hd⟩

/-- FaceDivisionProps.thy: before_vs -/
theorem before_vs {ram₁ ram₂ : α} {vs : List α}
    (hd : vs.Nodup) (h : before vs ram₁ ram₂) :
    vs = (splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₂ (splitAt ram₁ vs).2).1 ++ ram₂ ::
      (splitAt ram₂ vs).2 := by
  obtain ⟨a, b, c, hvs⟩ := h
  obtain ⟨-, -, -, h4, h5, h6⟩ := splitAt_dist_ram_all hd hvs
  rw [h6.symm, congrArg Prod.fst h4.symm, h5.symm]
  exact hvs

end Before


/-! ### between -/

section Between

/-- FaceDivisionProps.thy: pre_between -/
def pre_between (vs : List α) (ram₁ ram₂ : α) : Prop :=
  vs.Nodup ∧ ram₁ ∈ vs ∧ ram₂ ∈ vs ∧ ram₁ ≠ ram₂

variable [BEq α] [LawfulBEq α]

/-- FaceDivisionProps.thy: pre_between_dist -/
theorem pre_between_dist {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : vs.Nodup := h.1

/-- FaceDivisionProps.thy: pre_between_r1 -/
theorem pre_between_r1 {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : ram₁ ∈ vs := h.2.1

/-- FaceDivisionProps.thy: pre_between_r2 -/
theorem pre_between_r2 {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : ram₂ ∈ vs := h.2.2.1

/-- FaceDivisionProps.thy: pre_between_r12 -/
theorem pre_between_r12 {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : ram₁ ≠ ram₂ := h.2.2.2

/-- FaceDivisionProps.thy: pre_between_symI -/
theorem pre_between_symI {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : pre_between vs ram₂ ram₁ :=
  ⟨h.1, h.2.2.1, h.2.1, fun e => h.2.2.2 e.symm⟩

/-- FaceDivisionProps.thy: pre_between_before -/
theorem pre_between_before {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : before vs ram₁ ram₂ ∨ before vs ram₂ ram₁ :=
  before_or h.2.1 h.2.2.1 h.2.2.2

/-- FaceDivisionProps.thy: pre_between_rotate1 -/
theorem pre_between_rotate1 {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : pre_between (vs.rotate 1) ram₁ ram₂ :=
  ⟨List.nodup_rotate.mpr h.1, List.mem_rotate.mpr h.2.1, List.mem_rotate.mpr h.2.2.1,
    h.2.2.2⟩

/-- FaceDivisionProps.thy: pre_between_rotate -/
theorem pre_between_rotate {ram₁ ram₂ : α} {vs : List α} {n : Nat}
    (h : pre_between vs ram₁ ram₂) : pre_between (vs.rotate n) ram₁ ram₂ :=
  ⟨List.nodup_rotate.mpr h.1, List.mem_rotate.mpr h.2.1, List.mem_rotate.mpr h.2.2.1,
    h.2.2.2⟩

/-- FaceDivisionProps.thy: before_xor -/
theorem before_xor {ram₁ ram₂ : α} {vs : List α}
    (h : pre_between vs ram₁ ram₂) : (¬ before vs ram₁ ram₂) ↔ before vs ram₂ ram₁ :=
  before_dist_eq h.1 h.2.1 h.2.2.1 h.2.2.2

/-- FaceDivisionProps.thy: between_simp1 -/
@[simp]
theorem between_simp1 {ram₁ ram₂ : α} {vs : List α}
    (hb : before vs ram₁ ram₂) (hp : pre_between vs ram₁ ram₂) :
    between vs ram₁ ram₂ = (splitAt ram₂ (splitAt ram₁ vs).2).1 := by
  rw [between_def]
  have hmem : ram₂ ∈ (splitAt ram₁ vs).2 := (before_dist_eq_snd hp.1).mpr hb
  rw [if_pos (List.contains_iff_mem.mpr hmem)]

/-- FaceDivisionProps.thy: between_simp2 -/
@[simp]
theorem between_simp2 {ram₁ ram₂ : α} {vs : List α}
    (hb : before vs ram₁ ram₂) (hp : pre_between vs ram₁ ram₂) :
    between vs ram₂ ram₁ = (splitAt ram₂ vs).2 ++ (splitAt ram₁ vs).1 := by
  have hb2 : ¬ before vs ram₂ ram₁ := before_dist_not1 hp.1 hb
  rw [between_def]
  have hmem : ram₁ ∉ (splitAt ram₂ vs).2 := by
    rw [before_dist_eq_snd hp.1]
    exact hb2
  rw [if_neg (fun hc => hmem (List.contains_iff_mem.mp hc)),
    before_dist_fst hb hp.1]

/-- FaceDivisionProps.thy: between_not_r1 -/
theorem between_not_r1 {ram₁ ram₂ : α} {vs : List α}
    (hd : vs.Nodup) : ram₁ ∉ between vs ram₁ ram₂ := by
  by_cases hp : pre_between vs ram₁ ram₂
  · by_cases hb : before vs ram₁ ram₂
    · rw [between_simp1 hb hp]
      exact fun hm => splitAt_distinct_ram_snd hp.1 (splitAt_in_fst hm)
    · have hb' : before vs ram₂ ram₁ := (before_xor hp).mp hb
      have hp' : pre_between vs ram₂ ram₁ := pre_between_symI hp
      rw [between_simp2 hb' hp']
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact splitAt_distinct_ram_snd hp.1 hm
      · exact hb ((before_dist_eq_fst hp.1 hp'.2.1).mp hm)
  · by_cases h12 : ram₁ = ram₂
    · subst h12
      rw [between_def]
      by_cases hc : ((splitAt ram₁ vs).2.contains ram₁) = true
      · rw [if_pos hc]
        exact fun hm => splitAt_distinct_ram_snd hd (splitAt_in_fst hm)
      · rw [if_neg hc]
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact splitAt_distinct_ram_snd hd hm
        · exact splitAt_distinct_ram_fst hd (splitAt_in_fst hm)
    · by_cases h1 : ram₁ ∉ vs
      · rw [between_of_splitAt (splitAt_no_ram h1)]
        have hc : ¬ (([] : List α).contains ram₂ = true) := fun h => by simp at h
        rw [if_neg hc, List.nil_append]
        exact splitAt_not1 h1
      · push Not at h1
        by_cases h2 : ram₂ ∉ vs
        · rw [between_def]
          have hc : ¬ ((splitAt ram₁ vs).2.contains ram₂ = true) :=
            fun hc => h2 (splitAt_in_snd (List.contains_iff_mem.mp hc))
          rw [if_neg hc, splitAt_no_ram (splitAt_not1 h2)]
          intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact splitAt_distinct_ram_snd hd hm
          · exact splitAt_distinct_ram_fst hd hm
        · push Not at h2
          exact absurd ⟨hd, h1, h2, h12⟩ hp

/-- FaceDivisionProps.thy: between_not_r2 -/
theorem between_not_r2 {ram₁ ram₂ : α} {vs : List α}
    (hd : vs.Nodup) : ram₂ ∉ between vs ram₁ ram₂ := by
  by_cases hp : pre_between vs ram₁ ram₂
  · by_cases hb : before vs ram₁ ram₂
    · rw [between_simp1 hb hp]
      exact fun hm => splitAt_distinct_ram_fst (splitAt_distinct_snd hp.1) hm
    · have hb' : before vs ram₂ ram₁ := (before_xor hp).mp hb
      have hp' : pre_between vs ram₂ ram₁ := pre_between_symI hp
      rw [between_simp2 hb' hp']
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hb ((before_dist_eq_snd hd).mp hm)
      · exact splitAt_distinct_ram_fst hd hm
  · by_cases h12 : ram₁ = ram₂
    · subst h12
      rw [between_def]
      by_cases hc : ((splitAt ram₁ vs).2.contains ram₁) = true
      · rw [if_pos hc]
        exact fun hm => splitAt_distinct_ram_fst (splitAt_distinct_snd hd) hm
      · rw [if_neg hc]
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact splitAt_distinct_ram_snd hd hm
        · exact splitAt_distinct_ram_fst hd (splitAt_in_fst hm)
    · by_cases h2 : ram₂ ∉ vs
      · rw [between_def]
        have hc : ¬ ((splitAt ram₁ vs).2.contains ram₂ = true) :=
          fun hc => h2 (splitAt_in_snd (List.contains_iff_mem.mp hc))
        rw [if_neg hc, splitAt_no_ram (splitAt_not1 h2)]
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact h2 (splitAt_in_snd hm)
        · exact h2 (splitAt_in_fst hm)
      · push Not at h2
        by_cases h1 : ram₁ ∉ vs
        · rw [between_of_splitAt (splitAt_no_ram h1)]
          have hc : ¬ (([] : List α).contains ram₂ = true) := fun h => by simp at h
          rw [if_neg hc, List.nil_append]
          exact splitAt_distinct_ram_fst hd
        · push Not at h1
          exact absurd ⟨hd, h1, h2, h12⟩ hp

/-- FaceDivisionProps.thy: between_distinct -/
theorem between_distinct {ram₁ ram₂ : α} {vs : List α}
    (hd : vs.Nodup) : (between vs ram₁ ram₂).Nodup := by
  rw [between_def]
  by_cases hc : ((splitAt ram₁ vs).2.contains ram₂) = true
  · rw [if_pos hc]
    exact splitAt_distinct_fst (splitAt_distinct_snd hd)
  · rw [if_neg hc]
    apply List.nodup_append.mpr
    refine ⟨splitAt_distinct_snd hd, splitAt_distinct_fst (splitAt_distinct_fst hd), ?_⟩
    intro x hx y hy hxy
    have hy' : y ∈ (splitAt ram₁ vs).1 := splitAt_in_fst hy
    exact splitAt_distinct_fst_snd hd _ hy' (hxy ▸ hx)

/-- FaceDivisionProps.thy: between_distinct_r12 -/
theorem between_distinct_r12 {ram₁ ram₂ : α} {vs : List α}
    (hd : vs.Nodup) (h12 : ram₁ ≠ ram₂) :
    (ram₁ :: between vs ram₁ ram₂ ++ [ram₂]).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact between_not_r1 hd hm
    · rw [List.mem_singleton] at hm
      exact h12 hm
  · apply List.nodup_append.mpr
    refine ⟨between_distinct hd, List.nodup_singleton _, ?_⟩
    intro x hx y hy hxy
    rw [List.mem_singleton] at hy
    subst hy
    exact between_not_r2 hd (hxy ▸ hx)

/-- FaceDivisionProps.thy: between_vs -/
theorem between_vs {ram₁ ram₂ : α} {vs : List α}
    (hb : before vs ram₁ ram₂) (hp : pre_between vs ram₁ ram₂) :
    vs = (splitAt ram₁ vs).1 ++ ram₁ :: between vs ram₁ ram₂ ++ ram₂ :: (splitAt ram₂ vs).2 := by
  rw [between_simp1 hb hp]
  exact before_vs hp.1 hb

/-- FaceDivisionProps.thy: between_in -/
theorem between_in {x ram₁ ram₂ : α} {vs : List α}
    (hb : before vs ram₁ ram₂) (hp : pre_between vs ram₁ ram₂) (hx : x ∈ vs) :
    x = ram₁ ∨ x ∈ between vs ram₁ ram₂ ∨ x = ram₂ ∨ x ∈ between vs ram₂ ram₁ := by
  have hvs := between_vs hb hp
  rw [hvs] at hx
  have hb2 := between_simp2 hb hp
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (Or.inr (Or.inr (by rw [hb2]; exact List.mem_append_right _ hx)))
    · rcases List.mem_cons.mp hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
  · rcases List.mem_cons.mp hx with hx | hx
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr (by rw [hb2]; exact List.mem_append_left _ hx)))

/-- FaceDivisionProps.thy: (unnamed lemma immediately before `between_congs`) -/
theorem between_splitAt_head [Inhabited α] {a b : List α} {ram₁ ram₂ : α} {vs : List α}
    (hb : before vs ram₁ ram₂) (hp : pre_between vs ram₁ ram₂)
    (hhd : vs.head! ≠ ram₁)
    (hab : (a, b) = splitAt vs.head! (between vs ram₂ ram₁)) :
    vs = [vs.head!] ++ b ++ [ram₁] ++ between vs ram₁ ram₂ ++ [ram₂] ++ a := by
  have hd : vs.Nodup := hp.1
  have hvs1 : vs = (splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₁ vs).2 := splitAt_ram hp.2.1
  have hne_fst : (splitAt ram₁ vs).1 ≠ [] := by
    intro hn
    apply hhd
    rw [hn] at hvs1
    simp only [List.nil_append] at hvs1
    have e := congrArg List.head! hvs1
    rwa [List.head!_cons] at e
  have hvs_fst : vs.head! = (splitAt ram₁ vs).1.head! := by
    conv_lhs => rw [hvs1]
    exact List.head!_append _ hne_fst
  have hhd_in : vs.head! ∈ (splitAt ram₁ vs).1 := by
    rw [hvs_fst]
    exact head!_mem hne_fst
  have hbtw : between vs ram₂ ram₁ = (splitAt ram₂ vs).2 ++ (splitAt ram₁ vs).1 :=
    between_simp2 hb hp
  have hhd_btw : vs.head! ∈ between vs ram₂ ram₁ := by
    rw [hbtw]
    exact List.mem_append_right _ hhd_in
  have help1 : between vs ram₂ ram₁ =
      (splitAt vs.head! (between vs ram₂ ram₁)).1 ++ vs.head! ::
        (splitAt vs.head! (between vs ram₂ ram₁)).2 := splitAt_ram hhd_btw
  have hfst_cons : (splitAt ram₁ vs).1 =
      (splitAt ram₁ vs).1.head! :: (splitAt ram₁ vs).1.tail := (List.cons_head!_tail hne_fst).symm
  have hbtw2 : between vs ram₂ ram₁ =
      (splitAt ram₂ vs).2 ++ vs.head! :: (splitAt ram₁ vs).1.tail := by
    rw [hbtw]
    nth_rewrite 1 [hfst_cons]
    rw [← hvs_fst]
  have hdist : (between vs ram₂ ram₁).Nodup := between_distinct hd
  obtain ⟨e1, e2⟩ := dist_at hdist hbtw2 help1
  have ha : a = (splitAt ram₂ vs).2 := (congrArg Prod.fst hab).trans e1.symm
  have hb2 : b = (splitAt ram₁ vs).1.tail := (congrArg Prod.snd hab).trans e2.symm
  have hfst : (splitAt ram₁ vs).1 = vs.head! :: b := by
    rw [hb2, hvs_fst]
    exact hfst_cons
  have hvs2 := before_vs hd hb
  rw [← between_simp1 hb hp, hfst, ← ha] at hvs2
  exact hvs2.trans (by simp [List.append_assoc])

/-- FaceDivisionProps.thy: between_congs -/
theorem between_congs {ram₁ ram₂ : α} {vs vs' : List α}
    (hp : pre_between vs ram₁ ram₂) (h : cong vs vs') :
    between vs ram₁ ram₂ = between vs' ram₁ ram₂ := by
  -- one rotation preserves `between`
  have key : ∀ us : List α, pre_between us ram₁ ram₂ →
      between us ram₁ ram₂ = between (us.rotate 1) ram₁ ram₂ := by
    intro us hpus
    rcases pre_between_before hpus with hb | hb
    · -- `before us ram₁ ram₂`
      obtain ⟨A, B, C, hus⟩ := hb
      have hus3 : us = A ++ ram₁ :: (B ++ ram₂ :: C) := by rw [hus]; simp [List.append_assoc]
      have hdus : (A ++ ram₁ :: (B ++ ram₂ :: C)).Nodup := hus3 ▸ hpus.1
      have hsp1 : (A, B ++ ram₂ :: C) = splitAt ram₁ us := splitAt_dist_ram hpus.1 hus3
      have hdM : (B ++ ram₂ :: C).Nodup :=
        (List.nodup_cons.mp (List.nodup_append.mp hdus).2.1).2
      have hsp2 : (B, C) = splitAt ram₂ (B ++ ram₂ :: C) := splitAt_dist_ram hdM rfl
      have e2 : (splitAt ram₁ us).2 = B ++ ram₂ :: C := congrArg Prod.snd hsp1.symm
      have e3 : (splitAt ram₂ (B ++ ram₂ :: C)).1 = B := congrArg Prod.fst hsp2.symm
      have hbetween : between us ram₁ ram₂ = B := by
        rw [between_simp1 ⟨A, B, C, hus⟩ hpus, e2, e3]
      cases A with
      | nil =>
        simp only [List.nil_append] at hus3
        have hrot : us.rotate 1 = (B ++ ram₂ :: C) ++ [ram₁] := by
          rw [hus3]
          show (ram₁ :: (B ++ ram₂ :: C)).rotate 1 = _
          rw [show (1 : Nat) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
        have hpb : pre_between (us.rotate 1) ram₁ ram₂ := pre_between_rotate1 hpus
        have hpb' : pre_between (us.rotate 1) ram₂ ram₁ := pre_between_symI hpb
        have hn1 : ram₁ ∉ B ++ ram₂ :: C := by
          have hnd := hpus.1
          rw [hus3] at hnd
          exact (List.nodup_cons.mp hnd).1
        have hsp1r : splitAt ram₁ (us.rotate 1) = (B ++ ram₂ :: C, []) := by
          rw [hrot, splitAt_append_of_not_mem hn1, splitAt_self_cons]
          simp
        have e1r : (splitAt ram₁ (us.rotate 1)).2 = [] := congrArg Prod.snd hsp1r
        have hrot' : us.rotate 1 = B ++ ram₂ :: (C ++ [ram₁]) := by
          rw [hrot]; simp [List.append_assoc]
        have hsp2r : (B, C ++ [ram₁]) = splitAt ram₂ (us.rotate 1) :=
          splitAt_dist_ram hpb.1 hrot'
        have e2r : (splitAt ram₂ (us.rotate 1)).1 = B := congrArg Prod.fst hsp2r.symm
        have hbr : before (us.rotate 1) ram₂ ram₁ :=
          ⟨B, C, [], hrot.trans (by simp [List.append_assoc])⟩
        rw [between_simp2 hbr hpb', e1r, e2r]
        exact hbetween.trans (by simp)
      | cons a₁ A' =>
        have hus4 : us = a₁ :: (A' ++ ram₁ :: (B ++ ram₂ :: C)) := hus3
        have hrot : us.rotate 1 = (A' ++ ram₁ :: (B ++ ram₂ :: C)) ++ [a₁] := by
          rw [hus4]
          show (a₁ :: (A' ++ ram₁ :: (B ++ ram₂ :: C))).rotate 1 = _
          rw [show (1 : Nat) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
        have hpb : pre_between (us.rotate 1) ram₁ ram₂ := pre_between_rotate1 hpus
        have hrot2 : us.rotate 1 = A' ++ ram₁ :: (B ++ ram₂ :: (C ++ [a₁])) := by
          rw [hrot]; simp [List.append_assoc]
        have hbr : before (us.rotate 1) ram₁ ram₂ :=
          ⟨A', B, C ++ [a₁], hrot2.trans (by simp [List.append_assoc])⟩
        have hsp1r : (A', B ++ ram₂ :: (C ++ [a₁])) = splitAt ram₁ (us.rotate 1) :=
          splitAt_dist_ram hpb.1 hrot2
        have hdrot : (A' ++ ram₁ :: (B ++ ram₂ :: (C ++ [a₁]))).Nodup := hrot2 ▸ hpb.1
        have hdM2 : (B ++ ram₂ :: (C ++ [a₁])).Nodup :=
          (List.nodup_cons.mp (List.nodup_append.mp hdrot).2.1).2
        have hsp2r : (B, C ++ [a₁]) = splitAt ram₂ (B ++ ram₂ :: (C ++ [a₁])) :=
          splitAt_dist_ram hdM2 rfl
        have e1r : (splitAt ram₁ (us.rotate 1)).2 = B ++ ram₂ :: (C ++ [a₁]) :=
          congrArg Prod.snd hsp1r.symm
        have e2r : (splitAt ram₂ (B ++ ram₂ :: (C ++ [a₁]))).1 = B :=
          congrArg Prod.fst hsp2r.symm
        rw [between_simp1 hbr hpb, e1r, e2r]
        exact hbetween
    · -- `before us ram₂ ram₁`
      obtain ⟨A, B, C, hus⟩ := hb
      have hsp0 : (A ++ ram₂ :: B, C) = splitAt ram₁ us := splitAt_dist_ram hpus.1 hus
      have hus3 : us = A ++ ram₂ :: (B ++ ram₁ :: C) := by rw [hus]; simp [List.append_assoc]
      have hdus : (A ++ ram₂ :: (B ++ ram₁ :: C)).Nodup := hus3 ▸ hpus.1
      have hsp1 : (A, B ++ ram₁ :: C) = splitAt ram₂ us := splitAt_dist_ram hpus.1 hus3
      have hdM : (B ++ ram₁ :: C).Nodup :=
        (List.nodup_cons.mp (List.nodup_append.mp hdus).2.1).2
      have hsp2 : (B, C) = splitAt ram₁ (B ++ ram₁ :: C) := splitAt_dist_ram hdM rfl
      have hpus' : pre_between us ram₂ ram₁ := pre_between_symI hpus
      have e1 : (splitAt ram₁ us).2 = C := congrArg Prod.snd hsp0.symm
      have e2 : (splitAt ram₂ us).1 = A := congrArg Prod.fst hsp1.symm
      have hbetween : between us ram₁ ram₂ = C ++ A := by
        rw [between_simp2 ⟨A, B, C, hus⟩ hpus', e1, e2]
      cases A with
      | nil =>
        simp only [List.nil_append] at hus3
        have hrot : us.rotate 1 = (B ++ ram₁ :: C) ++ [ram₂] := by
          rw [hus3]
          show (ram₂ :: (B ++ ram₁ :: C)).rotate 1 = _
          rw [show (1 : Nat) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
        have hpb : pre_between (us.rotate 1) ram₁ ram₂ := pre_between_rotate1 hpus
        have hrot2 : us.rotate 1 = B ++ ram₁ :: (C ++ [ram₂]) := by
          rw [hrot]; simp [List.append_assoc]
        have hbr : before (us.rotate 1) ram₁ ram₂ :=
          ⟨B, C, [], hrot2.trans (by simp [List.append_assoc])⟩
        have hsp1r : (B, C ++ [ram₂]) = splitAt ram₁ (us.rotate 1) :=
          splitAt_dist_ram hpb.1 hrot2
        have hdrot : (B ++ ram₁ :: (C ++ [ram₂])).Nodup := hrot2 ▸ hpb.1
        have hdC : (C ++ [ram₂]).Nodup :=
          (List.nodup_cons.mp (List.nodup_append.mp hdrot).2.1).2
        have hsp2r : (C, []) = splitAt ram₂ (C ++ [ram₂]) := splitAt_dist_ram hdC rfl
        have e1r : (splitAt ram₁ (us.rotate 1)).2 = C ++ [ram₂] := congrArg Prod.snd hsp1r.symm
        have e2r : (splitAt ram₂ (C ++ [ram₂])).1 = C := congrArg Prod.fst hsp2r.symm
        rw [between_simp1 hbr hpb, e1r, e2r]
        exact hbetween.trans (by simp)
      | cons a₁ A' =>
        have hus4 : us = a₁ :: (A' ++ ram₂ :: (B ++ ram₁ :: C)) := hus3
        have hrot : us.rotate 1 = (A' ++ ram₂ :: (B ++ ram₁ :: C)) ++ [a₁] := by
          rw [hus4]
          show (a₁ :: (A' ++ ram₂ :: (B ++ ram₁ :: C))).rotate 1 = _
          rw [show (1 : Nat) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
        have hpb : pre_between (us.rotate 1) ram₁ ram₂ := pre_between_rotate1 hpus
        have hpb' : pre_between (us.rotate 1) ram₂ ram₁ := pre_between_rotate1 hpus'
        have hrot2 : us.rotate 1 = A' ++ ram₂ :: (B ++ ram₁ :: (C ++ [a₁])) := by
          rw [hrot]; simp [List.append_assoc]
        have hrot3 : us.rotate 1 = (A' ++ ram₂ :: B) ++ ram₁ :: (C ++ [a₁]) := by
          rw [hrot2]; simp [List.append_assoc]
        have hbr : before (us.rotate 1) ram₂ ram₁ :=
          ⟨A', B, C ++ [a₁], hrot2.trans (by simp [List.append_assoc])⟩
        have hdrot : (A' ++ ram₂ :: (B ++ ram₁ :: (C ++ [a₁]))).Nodup := hrot2 ▸ hpb.1
        have hsp0r : (A' ++ ram₂ :: B, C ++ [a₁]) = splitAt ram₁ (us.rotate 1) :=
          splitAt_dist_ram hpb.1 hrot3
        have hsp1r : (A', B ++ ram₁ :: (C ++ [a₁])) = splitAt ram₂ (us.rotate 1) :=
          splitAt_dist_ram hpb.1 hrot2
        have hdM2 : (B ++ ram₁ :: (C ++ [a₁])).Nodup :=
          (List.nodup_cons.mp (List.nodup_append.mp hdrot).2.1).2
        have hsp2r : (B, C ++ [a₁]) = splitAt ram₁ (B ++ ram₁ :: (C ++ [a₁])) :=
          splitAt_dist_ram hdM2 rfl
        have e0r : (splitAt ram₁ (us.rotate 1)).2 = C ++ [a₁] := congrArg Prod.snd hsp0r.symm
        have e2r : (splitAt ram₂ (us.rotate 1)).1 = A' := congrArg Prod.fst hsp1r.symm
        rw [between_simp2 hbr hpb', e0r, e2r]
        exact hbetween.trans (by simp [List.append_assoc])
  have hstep : ∀ n : Nat, between vs ram₁ ram₂ = between (vs.rotate n) ram₁ ram₂ := by
    intro n
    induction n with
    | zero => rw [List.rotate_zero]
    | succ m ih =>
      rw [← List.rotate_rotate, ← key (vs.rotate m) (pre_between_rotate hp)]
      exact ih
  obtain ⟨n, rfl⟩ := h
  exact hstep n

/-- FaceDivisionProps.thy: between_inter_empty (membership form) -/
theorem between_inter_empty {x ram₁ ram₂ : α} {vs : List α}
    (hp : pre_between vs ram₁ ram₂) (hx : x ∈ between vs ram₁ ram₂) :
    x ∉ between vs ram₂ ram₁ := by
  rcases pre_between_before hp with hb | hb
  · rw [between_simp1 hb hp] at hx
    rw [between_simp2 hb hp]
    have hvs := before_vs hp.1 hb
    have hdv : ((splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₂ (splitAt ram₁ vs).2).1 ++ ram₂ ::
      (splitAt ram₂ vs).2).Nodup := hvs ▸ hp.1
    have hd1 : ((splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₂ (splitAt ram₁ vs).2).1).Nodup :=
      (List.nodup_append.mp hdv).1
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · have hxl : x ∈ (splitAt ram₁ vs).1 ++ ram₁ :: (splitAt ram₂ (splitAt ram₁ vs).2).1 :=
        List.mem_append_right _ (List.mem_cons_of_mem _ hx)
      exact (List.nodup_append.mp hdv).2.2 x hxl x (List.mem_cons_of_mem _ hm) rfl
    · have hxm : x ∈ ram₁ :: (splitAt ram₂ (splitAt ram₁ vs).2).1 :=
        List.mem_cons_of_mem _ hx
      exact (List.nodup_append.mp hd1).2.2 x hm x hxm rfl
  · have hp' := pre_between_symI hp
    rw [between_simp2 hb hp'] at hx
    rw [between_simp1 hb hp']
    have hvs := before_vs hp'.1 hb
    have hdv : ((splitAt ram₂ vs).1 ++ ram₂ :: (splitAt ram₁ (splitAt ram₂ vs).2).1 ++ ram₁ ::
      (splitAt ram₁ vs).2).Nodup := hvs ▸ hp'.1
    have hd1 : ((splitAt ram₂ vs).1 ++ ram₂ :: (splitAt ram₁ (splitAt ram₂ vs).2).1).Nodup :=
      (List.nodup_append.mp hdv).1
    intro hm
    rcases List.mem_append.mp hx with hx | hx
    · have hxl : x ∈ (splitAt ram₂ vs).1 ++ ram₂ :: (splitAt ram₁ (splitAt ram₂ vs).2).1 :=
        List.mem_append_right _ (List.mem_cons_of_mem _ hm)
      exact (List.nodup_append.mp hdv).2.2 x hxl x (List.mem_cons_of_mem _ hx) rfl
    · have hxm : x ∈ ram₂ :: (splitAt ram₁ (splitAt ram₂ vs).2).1 :=
        List.mem_cons_of_mem _ hm
      exact (List.nodup_append.mp hd1).2.2 x hx x hxm rfl

end Between

end Kepler.Graphs
