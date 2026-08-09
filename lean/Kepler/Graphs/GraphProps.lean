/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `GraphProps.thy`
(properties of graph utilities).

Source: `reference/afp-flyspeck-tame/GraphProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Correspondence notes:
- `𝒱 f = set (vertices f)` is rendered as list membership `x ∈ f.vertices`,
  or as `{x | x ∈ f.vertices}` where the original statement is a set equality.
- `hd`/`last` map to `List.head!`/`List.getLast!`, `butlast` to `List.dropLast`
  (as in `Graph.lean`).
- The `ℰ` subsection uses `Face.edges`, the port of `Graph.thy`'s
  `edges_face` overloading, which was added to `Graph.lean` for this file.
- `nextVertex_eq_lemma` is proved via rotation-invariance of the cyclic
  successor (`nextElem_head_rotate`) instead of Isabelle's case bash.
-/
import Kepler.Graphs.Graph
import Kepler.Graphs.ListAuxLemmas
import Kepler.Graphs.RotationLemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Set.Lattice

namespace Kepler.Graphs

variable {α : Type _}

/-! ### setFinal and graph vertices -/

/-- GraphProps.thy: final_setFinal -/
@[simp]
theorem final_setFinal (f : Face) : (setFinal f).final = true := rfl

/-- GraphProps.thy: eq_setFinal_iff -/
@[simp]
theorem eq_setFinal_iff (f : Face) : f = setFinal f ↔ f.final = true := by
  obtain ⟨vs, fin⟩ := f
  rw [show setFinal ⟨vs, fin⟩ = (⟨vs, true⟩ : Face) from rfl]
  cases fin <;> simp [Face.final]

/-- GraphProps.thy: setFinal_eq_iff -/
@[simp]
theorem setFinal_eq_iff (f : Face) : setFinal f = f ↔ f.final = true :=
  eq_comm.trans (eq_setFinal_iff f)

/-- GraphProps.thy: distinct_vertices -/
@[simp]
theorem distinct_vertices (g : Graph) : g.vertices.Nodup := List.nodup_range

/-- Auxiliary: `getLast!` of a reversed list. -/
theorem getLast!_reverse [Inhabited α] (l : List α) : l.reverse.getLast! = l.head! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_reverse]
  cases h : l.head? with
  | none =>
    rw [List.head?_eq_none_iff] at h
    subst h
    rfl
  | some a =>
    rw [List.head!_of_head? h]
    rfl

/-- Auxiliary: `head!` of a reversed list. -/
theorem head!_reverse [Inhabited α] (l : List α) : l.reverse.head! = l.getLast! := by
  have h := getLast!_reverse l.reverse
  simp only [List.reverse_reverse] at h
  exact h.symm

/-- Auxiliary: `head!` as a `getElem`. -/
theorem head!_eq_getElem [Inhabited α] {l : List α} (h : l ≠ []) :
    l.head! = l[0]'(List.length_pos_iff.mpr h) := by
  rw [List.head!_eq_getElem!]
  exact getElem!_pos l 0 (List.length_pos_iff.mpr h)

/-! ### nextElem -/

section NextElem

variable [BEq α]

/-- Unfolding equation for `nextElem` on `cons` (auxiliary). -/
theorem nextElem_cons (a : α) (as : List α) (b x : α) :
    nextElem (a :: as) b x =
      if x == a then (match as with | [] => b | a' :: _ => a') else nextElem as b x :=
  rfl

/-- Unfolding equation for `nextElem` on a singleton tail (auxiliary). -/
theorem nextElem_cons_nil (a b x : α) : nextElem [a] b x = if x == a then b else b := rfl

/-- Unfolding equation for `nextElem` on a `cons`-`cons` tail (auxiliary). -/
theorem nextElem_cons_cons (a a' : α) (as : List α) (b x : α) :
    nextElem (a :: a' :: as) b x = if x == a then a' else nextElem (a' :: as) b x := rfl

/-- GraphProps.thy: nextElem_in -/
theorem nextElem_in {x y : α} : ∀ {xs : List α}, nextElem xs x y ∈ x :: xs := by
  intro xs
  induction xs with
  | nil => exact List.mem_cons_self
  | cons a as ih =>
    rw [nextElem_cons]
    split
    · cases as with
      | nil => exact List.mem_cons_self
      | cons b bs => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · rcases List.mem_cons.mp ih with hmem | hmem
      · rw [hmem]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem)

variable [LawfulBEq α]

/-- Auxiliary: negated `BEq` test as a proposition. -/
theorem beq_ne_true_of_ne {a b : α} (h : a ≠ b) : ¬ ((a == b) = true) :=
  fun hc => h (beq_iff_eq.mp hc)

/-- Auxiliary: `splitAt` at the head of a list. -/
theorem splitAt_self_cons (a : α) (l : List α) : splitAt a (a :: l) = ([], l) := by
  simp [splitAt, splitAtRec]

/-- GraphProps.thy: nextElem_append -/
@[simp]
theorem nextElem_append {y : α} {xs : List α} (h : y ∉ xs) (ys : List α) (d : α) :
    nextElem (xs ++ ys) d y = nextElem ys d y := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    have hya : (y == a) = false :=
      beq_eq_false_iff_ne.mpr (fun e => h (List.mem_cons.mpr (Or.inl e)))
    have has : y ∉ as := fun hm => h (List.mem_cons_of_mem _ hm)
    show nextElem (a :: (as ++ ys)) d y = nextElem ys d y
    rw [nextElem_cons, if_neg (beq_ne_true_of_ne (beq_eq_false_iff_ne.mp hya))]
    exact ih has

/-- GraphProps.thy: nextElem_cases -/
theorem nextElem_cases [Inhabited α] {xs : List α} {d x y : α}
    (h : nextElem xs d x = y) :
    (x ∉ xs ∧ y = d) ∨
    (xs ≠ [] ∧ x = xs.getLast! ∧ y = d ∧ x ∉ xs.dropLast) ∨
    (∃ us vs, xs = us ++ [x, y] ++ vs ∧ x ∉ us) := by
  induction xs with
  | nil =>
    exact Or.inl ⟨List.not_mem_nil, h.symm⟩
  | cons a as ih =>
    by_cases hxa : x = a
    · subst hxa
      cases as with
      | nil =>
        right; left
        refine ⟨List.cons_ne_nil _ _, rfl, ?_, List.not_mem_nil⟩
        simpa [nextElem_cons] using h.symm
      | cons b bs =>
        right; right
        have hy : y = b := by simpa [nextElem_cons] using h.symm
        exact ⟨[], bs, by subst hy; rfl, List.not_mem_nil⟩
    · have h' : nextElem as d x = y := by
        rw [nextElem_cons, if_neg (beq_ne_true_of_ne hxa)] at h
        exact h
      rcases ih h' with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨us, vs, h5, h6⟩
      · exact Or.inl ⟨fun hm => (List.mem_cons.mp hm).elim hxa h1, h2⟩
      · right; left
        obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil h1
        refine ⟨List.cons_ne_nil _ _, ?_, h3, ?_⟩
        · rw [h2]; simp
        · simp only [List.dropLast_cons_cons, List.mem_cons, not_or]
          exact ⟨hxa, h4⟩
      · right; right
        exact ⟨a :: us, vs, by rw [h5]; rfl, fun hm => (List.mem_cons.mp hm).elim hxa h6⟩

/-- GraphProps.thy: nextElem_notin_butlast -/
@[simp]
theorem nextElem_notin_dropLast {x y : α} :
    ∀ {xs : List α}, y ∉ xs.dropLast → nextElem xs x y = x := by
  intro xs
  induction xs with
  | nil => intro; rfl
  | cons a as ih =>
    intro h
    cases as with
    | nil =>
      rw [nextElem_cons]
      split <;> rfl
    | cons b bs =>
      have h' : y ≠ a ∧ y ∉ (b :: bs).dropLast := by
        simp only [List.dropLast_cons_cons, List.mem_cons, not_or] at h
        exact h
      rw [nextElem_cons, if_neg (beq_ne_true_of_ne h'.1)]
      exact ih h'.2

/-- GraphProps.thy: nextElem_notin -/
@[simp]
theorem nextElem_notin {a c : α} {as : List α} (h : a ∉ as) : nextElem as c a = c := by
  have h' := nextElem_append h ([] : List α) c
  rwa [List.append_nil] at h'

/-- GraphProps.thy: nextElem_last -/
@[simp]
theorem nextElem_last [Inhabited α] {c : α} {xs : List α} (hd : xs.Nodup) :
    nextElem xs c xs.getLast! = c := by
  by_cases hx : xs = []
  · subst hx
    rfl
  · have hgl : xs.getLast! = xs.getLast hx :=
      List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hx)
    have h1 : xs = xs.dropLast ++ [xs.getLast!] := by
      rw [hgl]
      exact (List.dropLast_concat_getLast hx).symm
    have hnotin : xs.getLast! ∉ xs.dropLast := by
      rw [h1] at hd
      exact fun h => (List.nodup_append.mp hd).2.2 _ h _ List.mem_cons_self rfl
    have h2 : nextElem xs c xs.getLast! = nextElem [xs.getLast!] c xs.getLast! := by
      have e := nextElem_append hnotin [xs.getLast!] c
      rwa [← h1] at e
    rw [h2, nextElem_cons_nil, if_pos (beq_self_eq_true _)]

/-- GraphProps.thy: prevElem_nextElem -/
theorem prevElem_nextElem [Inhabited α] {x : α} {xs : List α} (hd : xs.Nodup)
    (hx : x ∈ xs) : nextElem xs.reverse xs.getLast! (nextElem xs xs.head! x) = x := by
  generalize hy : nextElem xs xs.head! x = y
  rcases nextElem_cases hy with ⟨h1, -⟩ | ⟨-, h2, h3, -⟩ | ⟨us, ws, h4, -⟩
  · exact absurd hx h1
  · subst h2; subst h3
    rw [← getLast!_reverse xs]
    exact nextElem_last (List.nodup_reverse.mpr hd)
  · subst h4
    have hyw : y ∉ ws := by
      intro hm
      have hy : y ∈ us ++ [x, y] := by simp
      exact (List.nodup_append.mp hd).2.2 y hy y hm rfl
    have hrev : (us ++ [x, y] ++ ws).reverse = ws.reverse ++ (y :: x :: us.reverse) := by
      simp [List.reverse_append]
    have hyw' : y ∉ ws.reverse := fun hm => hyw (List.mem_reverse.mp hm)
    rw [hrev, nextElem_append hyw', nextElem_cons_cons, if_pos (beq_self_eq_true y)]

/-- GraphProps.thy: nextElem_prevElem -/
theorem nextElem_prevElem [Inhabited α] {x : α} {xs : List α} (hd : xs.Nodup)
    (hx : x ∈ xs) : nextElem xs xs.head! (nextElem xs.reverse xs.getLast! x) = x := by
  have h := prevElem_nextElem (xs := xs.reverse) (List.nodup_reverse.mpr hd)
    (List.mem_reverse.mpr hx)
  simp only [List.reverse_reverse, getLast!_reverse, head!_reverse] at h
  exact h

/-- GraphProps.thy: nextElem_nth -/
theorem nextElem_nth [Inhabited α] (z : α) :
    ∀ {xs : List α}, xs.Nodup → ∀ {i : Nat} (h : i < xs.length),
      nextElem xs z (xs[i]'h) = if xs.length = i + 1 then z else xs[i + 1]! := by
  intro xs hd
  induction xs with
  | nil => intro i h; exact absurd h (Nat.not_lt_zero _)
  | cons a as ih =>
    intro i h
    obtain ⟨ha, hdas⟩ := List.nodup_cons.mp hd
    cases i with
    | zero =>
      rw [List.getElem_cons_zero]
      cases as with
      | nil => simp
      | cons b bs =>
        have hlen : ¬ ((a :: b :: bs).length = 0 + 1) := by
          have e : (a :: b :: bs).length = bs.length + 2 := rfl
          omega
        have hlt : 0 + 1 < (a :: b :: bs).length := by
          have e : (a :: b :: bs).length = bs.length + 2 := rfl
          omega
        rw [nextElem_cons, if_pos (beq_self_eq_true a), if_neg hlen,
          getElem!_pos (a :: b :: bs) (0 + 1) hlt]
        rfl
    | succ j =>
      have hj : j < as.length := by
        have e : (a :: as).length = as.length + 1 := rfl
        omega
      have hne : (as[j]'hj) ≠ a := fun he => ha (he ▸ List.getElem_mem hj)
      have e1 : nextElem (a :: as) z ((a :: as)[j + 1]'h) = nextElem as z (as[j]'hj) := by
        rw [List.getElem_cons_succ, nextElem_cons, if_neg (beq_ne_true_of_ne hne)]
      rw [e1, ih hdas hj]
      by_cases hlast : as.length = j + 1
      · rw [if_pos hlast,
          if_pos (show (a :: as).length = j + 1 + 1 from by
            have e : (a :: as).length = as.length + 1 := rfl
            omega)]
      · rw [if_neg hlast,
          if_neg (show ¬ ((a :: as).length = j + 1 + 1) from by
            have e : (a :: as).length = as.length + 1 := rfl
            omega)]
        have hlt : j + 1 + 1 < (a :: as).length := by
          have e : (a :: as).length = as.length + 1 := rfl
          omega
        rw [getElem!_pos (a :: as) (j + 1 + 1) hlt, List.getElem_cons_succ]
        exact getElem!_pos as (j + 1) (by omega)

/-- Auxiliary: `nextElem` over a singleton-appended list (one rotation step). -/
theorem nextElem_concat {v a d : α} {l : List α} (hv : v ∈ l) :
    nextElem (l ++ [a]) d v = nextElem l a v := by
  induction l with
  | nil => exact absurd hv List.not_mem_nil
  | cons b bs ih =>
    show nextElem (b :: (bs ++ [a])) d v = nextElem (b :: bs) a v
    rw [nextElem_cons, nextElem_cons]
    by_cases hb : v = b
    · subst hb
      rw [if_pos (beq_self_eq_true _), if_pos (beq_self_eq_true _)]
      cases bs with
      | nil => rfl
      | cons c cs => rfl
    · rw [if_neg (beq_ne_true_of_ne hb), if_neg (beq_ne_true_of_ne hb)]
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact absurd rfl hb
      · exact ih hv'

/-- Auxiliary: the cyclic successor is rotation-invariant. Used for
`nextVertex_eq_lemma` (Isabelle instead case-bashes on `split_list`). -/
theorem nextElem_head_rotate [Inhabited α] {v : α} (n : Nat) :
    ∀ {xs : List α}, xs.Nodup → v ∈ xs →
      nextElem xs xs.head! v = nextElem (xs.rotate n) (xs.rotate n).head! v := by
  induction n with
  | zero => intro xs _ _; rw [List.rotate_zero]
  | succ m ih =>
    intro xs hd hv
    cases xs with
    | nil => exact absurd hv List.not_mem_nil
    | cons a as =>
      rw [List.rotate_cons_succ]
      obtain ⟨ha, hdas⟩ := List.nodup_cons.mp hd
      have hd' : (as ++ [a]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hdas, List.nodup_singleton a,
          fun x hx y hy he => ha ((he.trans (List.mem_singleton.mp hy)) ▸ hx)⟩
      have hv' : v ∈ as ++ [a] := by
        rcases List.mem_cons.mp hv with rfl | hv''
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ hv''
      rw [← ih hd' hv']
      show nextElem (a :: as) a v = nextElem (as ++ [a]) (as ++ [a]).head! v
      by_cases hva : v = a
      · subst hva
        rw [nextElem_cons, if_pos (beq_self_eq_true v)]
        rw [nextElem_append ha, nextElem_cons_nil, if_pos (beq_self_eq_true v)]
        cases as with
        | nil => rfl
        | cons b bs => rfl
      · have hvas : v ∈ as := (List.mem_cons.mp hv).resolve_left hva
        rw [nextElem_cons, if_neg (beq_ne_true_of_ne hva)]
        rw [nextElem_concat hvas]

/-- Auxiliary: inside a non-final segment, `nextElem` does not see the base
value. -/
theorem nextElem_append_preserve {v d z : α} {l₁ l₂ rest : List α}
    (hv : v ∉ l₁) (h₂ : l₂ ≠ []) :
    nextElem ((l₁ ++ v :: l₂) ++ rest) d v = nextElem (l₁ ++ v :: l₂) z v := by
  obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil h₂
  rw [List.append_assoc]
  show nextElem (l₁ ++ v :: w :: (ws ++ rest)) d v = nextElem (l₁ ++ v :: w :: ws) z v
  rw [nextElem_append hv, nextElem_append hv,
    nextElem_cons_cons, nextElem_cons_cons, if_pos (beq_self_eq_true v),
    if_pos (beq_self_eq_true v)]

end NextElem

/-! ### nextVertex / prevVertex -/

/-- GraphProps.thy: nextVertex_in_face' -/
@[simp]
theorem nextVertex_in_face' {f : Face} {v : Vertex} (h : f.vertices ≠ []) :
    f.nextVertex v ∈ f.vertices := by
  have hhead : f.vertices.head! ∈ f.vertices := by
    obtain ⟨a, as, hcons⟩ := List.exists_cons_of_ne_nil h
    rw [hcons]
    exact List.mem_cons_self
  show nextElem f.vertices f.vertices.head! v ∈ f.vertices
  set e := nextElem f.vertices f.vertices.head! v with he
  rcases nextElem_cases (xs := f.vertices) (d := f.vertices.head!) (x := v) (y := e) rfl with
    ⟨-, hy⟩ | ⟨-, -, hy, -⟩ | ⟨us, ws, hvs, -⟩
  · rw [hy]; exact hhead
  · rw [hy]; exact hhead
  · rw [hvs]
    exact List.mem_append_left _
      (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- GraphProps.thy: nextVertex_in_face -/
@[simp]
theorem nextVertex_in_face {f : Face} {v : Vertex} (hv : v ∈ f.vertices) :
    f.nextVertex v ∈ f.vertices :=
  nextVertex_in_face' (List.ne_nil_of_mem hv)

/-- GraphProps.thy: nextVertex_prevVertex -/
@[simp]
theorem nextVertex_prevVertex {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) : f.nextVertex (f.prevVertex v) = v :=
  nextElem_prevElem hd hv

/-- GraphProps.thy: prevVertex_nextVertex -/
@[simp]
theorem prevVertex_nextVertex {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) : f.prevVertex (f.nextVertex v) = v :=
  prevElem_nextElem hd hv

/-- GraphProps.thy: prevVertex_in_face -/
@[simp]
theorem prevVertex_in_face {f : Face} {v : Vertex} (hv : v ∈ f.vertices) :
    f.prevVertex v ∈ f.vertices := by
  have hne : f.vertices ≠ [] := List.ne_nil_of_mem hv
  have h := nextElem_in (xs := f.vertices.reverse) (x := f.vertices.getLast!) (y := v)
  show nextElem f.vertices.reverse f.vertices.getLast! v ∈ f.vertices
  rcases List.mem_cons.mp h with heq | hmem
  · rw [heq]
    have hgl : f.vertices.getLast! = f.vertices.getLast hne :=
      List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hne)
    rw [hgl]
    exact List.getLast_mem hne
  · exact List.mem_reverse.mp hmem

/-- GraphProps.thy: nextVertex_nth -/
theorem nextVertex_nth {f : Face} (hd : f.vertices.Nodup) {i : Nat}
    (h : i < f.vertices.length) :
    f.nextVertex (f.vertices[i]'h) =
      f.vertices[(i + 1) % f.vertices.length]'(Nat.mod_lt _ (by omega)) := by
  have hne : f.vertices ≠ [] := List.ne_nil_of_mem (List.getElem_mem h)
  show nextElem f.vertices f.vertices.head! (f.vertices[i]'h) = _
  rw [head!_eq_getElem hne, nextElem_nth _ hd h]
  by_cases hlast : f.vertices.length = i + 1
  · rw [if_pos hlast]
    have e : (i + 1) % f.vertices.length = 0 := by
      rw [← hlast]
      exact Nat.mod_self _
    simp only [e]
  · have hlt : i + 1 < f.vertices.length := by omega
    rw [if_neg hlast]
    simp only [Nat.mod_eq_of_lt hlt]
    exact getElem!_pos f.vertices (i + 1) hlt

/-! ### ℰ (edges of a face) -/

/-- GraphProps.thy: edges_face_eq -/
theorem edges_face_eq {f : Face} {a b : Vertex} :
    (a, b) ∈ f.edges ↔ f.nextVertex a = b ∧ a ∈ f.vertices :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- GraphProps.thy: edges_setFinal -/
@[simp]
theorem edges_setFinal (f : Face) : (setFinal f).edges = f.edges := rfl

/-- GraphProps.thy: in_edges_in_vertices -/
theorem in_edges_in_vertices {f : Face} {x y : Vertex} (h : (x, y) ∈ f.edges) :
    x ∈ f.vertices ∧ y ∈ f.vertices := by
  have h' : x ∈ f.vertices ∧ f.nextVertex x = y := h
  obtain ⟨hx, hxy⟩ := h'
  rw [← hxy]
  exact ⟨hx, nextVertex_in_face hx⟩

/-- GraphProps.thy: vertices_conv_Union_edges -/
theorem vertices_conv_Union_edges (f : Face) :
    {x | x ∈ f.vertices} = ⋃ p ∈ f.edges, ({p.1} : Set Vertex) := by
  ext x
  constructor
  · intro hx
    exact Set.mem_biUnion (x := (x, f.nextVertex x)) ⟨hx, rfl⟩ rfl
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hx
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hx
    exact hp.1

/-- GraphProps.thy: nextVertex_in_edges -/
theorem nextVertex_in_edges {f : Face} {v : Vertex} (hv : v ∈ f.vertices) :
    (v, f.nextVertex v) ∈ f.edges :=
  ⟨hv, rfl⟩

/-- GraphProps.thy: prevVertex_in_edges -/
theorem prevVertex_in_edges {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) : (f.prevVertex v, v) ∈ f.edges :=
  ⟨prevVertex_in_face hv, nextVertex_prevVertex hd hv⟩

/-! ### Triangles -/

/-- GraphProps.thy: vertices_triangle -/
theorem vertices_triangle {f : Face} {a : Vertex} (h3 : f.vertices.length = 3)
    (ha : a ∈ f.vertices) (hd : f.vertices.Nodup) :
    {x | x ∈ f.vertices} = {a, f.nextVertex a, f.nextVertex (f.nextVertex a)} := by
  obtain ⟨vs, fin⟩ := f
  obtain ⟨a1, a2, a3, rfl⟩ := length3D h3
  have h12 : a1 ≠ a2 := fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h))
  have h13 : a1 ≠ a3 := fun h =>
    (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h23 : a2 ≠ a3 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (List.mem_cons.mpr (Or.inl h))
  have e1 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a1 = a2 := by
    show nextElem [a1, a2, a3] a1 a1 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a1)]
  have e2 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a2 = a3 := by
    show nextElem [a1, a2, a3] a1 a2 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h12)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have e3 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a3 = a1 := by
    show nextElem [a1, a2, a3] a1 a3 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h13)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h23)),
      nextElem_cons_nil, if_pos (beq_self_eq_true a3)]
  show ({x | x ∈ [a1, a2, a3]} : Set Vertex) = _
  rcases List.mem_cons.mp ha with rfl | ha'
  · rw [e1, e2]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    try tauto
  · rcases List.mem_cons.mp ha' with rfl | ha''
    · rw [e2, e3]
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      try tauto
    · rw [List.mem_singleton] at ha''
      subst ha''
      rw [e3, e1]
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      try tauto

/-- GraphProps.thy: tri_next3_id. Isabelle proves this via `nextVertex_nth` and
modular arithmetic; here we decompose the 3-element list and compute. -/
theorem tri_next3_id {f : Face} {v : Vertex} (h3 : f.vertices.length = 3)
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices) :
    f.nextVertex (f.nextVertex (f.nextVertex v)) = v := by
  obtain ⟨vs, fin⟩ := f
  obtain ⟨a1, a2, a3, rfl⟩ := length3D h3
  have h12 : a1 ≠ a2 := fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h))
  have h13 : a1 ≠ a3 := fun h =>
    (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h23 : a2 ≠ a3 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (List.mem_cons.mpr (Or.inl h))
  have e1 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a1 = a2 := by
    show nextElem [a1, a2, a3] a1 a1 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a1)]
  have e2 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a2 = a3 := by
    show nextElem [a1, a2, a3] a1 a2 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h12)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have e3 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a3 = a1 := by
    show nextElem [a1, a2, a3] a1 a3 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h13)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h23)),
      nextElem_cons_nil, if_pos (beq_self_eq_true a3)]
  rcases List.mem_cons.mp hv with rfl | hv'
  · rw [e1, e2, e3]
  · rcases List.mem_cons.mp hv' with rfl | hv''
    · rw [e2, e3, e1]
    · rw [List.mem_singleton] at hv''
      subst hv''
      rw [e3, e1, e2]

/-- GraphProps.thy: triangle_nextVertex_prevVertex -/
theorem triangle_nextVertex_prevVertex {f : Face} {a : Vertex} (h3 : f.vertices.length = 3)
    (ha : a ∈ f.vertices) (hd : f.vertices.Nodup) :
    f.nextVertex (f.nextVertex a) = f.prevVertex a := by
  obtain ⟨vs, fin⟩ := f
  obtain ⟨a1, a2, a3, rfl⟩ := length3D h3
  have h12 : a1 ≠ a2 := fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h))
  have h13 : a1 ≠ a3 := fun h =>
    (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h23 : a2 ≠ a3 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (List.mem_cons.mpr (Or.inl h))
  have e1 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a1 = a2 := by
    show nextElem [a1, a2, a3] a1 a1 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a1)]
  have e2 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a2 = a3 := by
    show nextElem [a1, a2, a3] a1 a2 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h12)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have e3 : Face.nextVertex ⟨[a1, a2, a3], fin⟩ a3 = a1 := by
    show nextElem [a1, a2, a3] a1 a3 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h13)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h23)),
      nextElem_cons_nil, if_pos (beq_self_eq_true a3)]
  have p1 : Face.prevVertex ⟨[a1, a2, a3], fin⟩ a1 = a3 := by
    show nextElem [a3, a2, a1] a3 a1 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne h13),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne h12),
      nextElem_cons_nil, if_pos (beq_self_eq_true a1)]
  have p2 : Face.prevVertex ⟨[a1, a2, a3], fin⟩ a2 = a1 := by
    show nextElem [a3, a2, a1] a3 a2 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne h23),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have p3 : Face.prevVertex ⟨[a1, a2, a3], fin⟩ a3 = a2 := by
    show nextElem [a3, a2, a1] a3 a3 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a3)]
  rcases List.mem_cons.mp ha with rfl | ha'
  · rw [e1, e2, p1]
  · rcases List.mem_cons.mp ha' with rfl | ha''
    · rw [e2, e3, p2]
    · rw [List.mem_singleton] at ha''
      subst ha''
      rw [e3, e1, p3]

/-! ### Quadrilaterals -/

/-- GraphProps.thy: vertices_quad -/
theorem vertices_quad {f : Face} {a : Vertex} (h4 : f.vertices.length = 4)
    (ha : a ∈ f.vertices) (hd : f.vertices.Nodup) :
    {x | x ∈ f.vertices} =
      {a, f.nextVertex a, f.nextVertex (f.nextVertex a),
        f.nextVertex (f.nextVertex (f.nextVertex a))} := by
  obtain ⟨vs, fin⟩ := f
  obtain ⟨a1, a2, a3, a4, rfl⟩ := length4D h4
  have h12 : a1 ≠ a2 := fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h))
  have h13 : a1 ≠ a3 := fun h =>
    (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h14 : a1 ≠ a4 := fun h =>
    (List.nodup_cons.mp hd).1
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))))
  have h23 : a2 ≠ a3 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (List.mem_cons.mpr (Or.inl h))
  have h24 : a2 ≠ a4 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h34 : a3 ≠ a4 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
      (List.mem_cons.mpr (Or.inl h))
  have e1 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a1 = a2 := by
    show nextElem [a1, a2, a3, a4] a1 a1 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a1)]
  have e2 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a2 = a3 := by
    show nextElem [a1, a2, a3, a4] a1 a2 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h12)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have e3 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a3 = a4 := by
    show nextElem [a1, a2, a3, a4] a1 a3 = a4
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h13)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h23)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a3)]
  have e4 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a4 = a1 := by
    show nextElem [a1, a2, a3, a4] a1 a4 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h14)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h24)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h34)),
      nextElem_cons_nil, if_pos (beq_self_eq_true a4)]
  show ({x | x ∈ [a1, a2, a3, a4]} : Set Vertex) = _
  rcases List.mem_cons.mp ha with rfl | ha'
  · rw [e1, e2, e3]
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    try tauto
  · rcases List.mem_cons.mp ha' with rfl | ha''
    · rw [e2, e3, e4]
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      try tauto
    · rcases List.mem_cons.mp ha'' with rfl | ha'''
      · rw [e3, e4, e1]
        ext x
        simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        try tauto
      · rw [List.mem_singleton] at ha'''
        subst ha'''
        rw [e4, e1, e2]
        ext x
        simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        try tauto

/-- GraphProps.thy: quad_next4_id. Isabelle proves this via `nextVertex_nth`
and modular arithmetic; here we decompose the 4-element list and compute. -/
theorem quad_next4_id {f : Face} {v : Vertex} (h4 : f.vertices.length = 4)
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices) :
    f.nextVertex (f.nextVertex (f.nextVertex (f.nextVertex v))) = v := by
  obtain ⟨vs, fin⟩ := f
  obtain ⟨a1, a2, a3, a4, rfl⟩ := length4D h4
  have h12 : a1 ≠ a2 := fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h))
  have h13 : a1 ≠ a3 := fun h =>
    (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h14 : a1 ≠ a4 := fun h =>
    (List.nodup_cons.mp hd).1
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))))
  have h23 : a2 ≠ a3 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (List.mem_cons.mpr (Or.inl h))
  have h24 : a2 ≠ a4 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h34 : a3 ≠ a4 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
      (List.mem_cons.mpr (Or.inl h))
  have e1 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a1 = a2 := by
    show nextElem [a1, a2, a3, a4] a1 a1 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a1)]
  have e2 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a2 = a3 := by
    show nextElem [a1, a2, a3, a4] a1 a2 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h12)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have e3 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a3 = a4 := by
    show nextElem [a1, a2, a3, a4] a1 a3 = a4
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h13)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h23)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a3)]
  have e4 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a4 = a1 := by
    show nextElem [a1, a2, a3, a4] a1 a4 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h14)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h24)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h34)),
      nextElem_cons_nil, if_pos (beq_self_eq_true a4)]
  rcases List.mem_cons.mp hv with rfl | hv'
  · rw [e1, e2, e3, e4]
  · rcases List.mem_cons.mp hv' with rfl | hv''
    · rw [e2, e3, e4, e1]
    · rcases List.mem_cons.mp hv'' with rfl | hv'''
      · rw [e3, e4, e1, e2]
      · rw [List.mem_singleton] at hv'''
        subst hv'''
        rw [e4, e1, e2, e3]

/-- GraphProps.thy: quad_nextVertex_prevVertex -/
theorem quad_nextVertex_prevVertex {f : Face} {a : Vertex} (h4 : f.vertices.length = 4)
    (ha : a ∈ f.vertices) (hd : f.vertices.Nodup) :
    f.nextVertex (f.nextVertex (f.nextVertex a)) = f.prevVertex a := by
  obtain ⟨vs, fin⟩ := f
  obtain ⟨a1, a2, a3, a4, rfl⟩ := length4D h4
  have h12 : a1 ≠ a2 := fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h))
  have h13 : a1 ≠ a3 := fun h =>
    (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h14 : a1 ≠ a4 := fun h =>
    (List.nodup_cons.mp hd).1
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))))
  have h23 : a2 ≠ a3 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1 (List.mem_cons.mpr (Or.inl h))
  have h24 : a2 ≠ a4 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hd).2).1
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h))))
  have h34 : a3 ≠ a4 := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hd).2).2).1
      (List.mem_cons.mpr (Or.inl h))
  have e1 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a1 = a2 := by
    show nextElem [a1, a2, a3, a4] a1 a1 = a2
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a1)]
  have e2 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a2 = a3 := by
    show nextElem [a1, a2, a3, a4] a1 a2 = a3
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h12)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have e3 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a3 = a4 := by
    show nextElem [a1, a2, a3, a4] a1 a3 = a4
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h13)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h23)),
      nextElem_cons_cons, if_pos (beq_self_eq_true a3)]
  have e4 : Face.nextVertex ⟨[a1, a2, a3, a4], fin⟩ a4 = a1 := by
    show nextElem [a1, a2, a3, a4] a1 a4 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h14)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h24)),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne (Ne.symm h34)),
      nextElem_cons_nil, if_pos (beq_self_eq_true a4)]
  have p1 : Face.prevVertex ⟨[a1, a2, a3, a4], fin⟩ a1 = a4 := by
    show nextElem [a4, a3, a2, a1] a4 a1 = a4
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne h14),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne h13),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne h12),
      nextElem_cons_nil, if_pos (beq_self_eq_true a1)]
  have p2 : Face.prevVertex ⟨[a1, a2, a3, a4], fin⟩ a2 = a1 := by
    show nextElem [a4, a3, a2, a1] a4 a2 = a1
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne h24),
      nextElem_cons_cons, if_neg (beq_ne_true_of_ne h23),
      nextElem_cons_cons, if_pos (beq_self_eq_true a2)]
  have p3 : Face.prevVertex ⟨[a1, a2, a3, a4], fin⟩ a3 = a2 := by
    show nextElem [a4, a3, a2, a1] a4 a3 = a2
    rw [nextElem_cons_cons, if_neg (beq_ne_true_of_ne h34),
      nextElem_cons_cons, if_pos (beq_self_eq_true a3)]
  have p4 : Face.prevVertex ⟨[a1, a2, a3, a4], fin⟩ a4 = a3 := by
    show nextElem [a4, a3, a2, a1] a4 a4 = a3
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true a4)]
  rcases List.mem_cons.mp ha with rfl | ha'
  · rw [e1, e2, e3, p1]
  · rcases List.mem_cons.mp ha' with rfl | ha''
    · rw [e2, e3, e4, p2]
    · rcases List.mem_cons.mp ha'' with rfl | ha'''
      · rw [e3, e4, e1, p3]
      · rw [List.mem_singleton] at ha'''
        subst ha'''
        rw [e4, e1, e2, p4]

/-! ### Graph lemmas -/

/-- GraphProps.thy: len_faces_sum -/
theorem len_faces_sum (g : Graph) :
    g.faces.length = (finals g).length + (nonFinals g).length :=
  List.length_eq_length_filter_add Face.final

/-- GraphProps.thy: graph_max_final_ex -/
theorem graph_max_final_ex (n : Nat) :
    ∃ f ∈ finals (graph n), f.vertices.length = n := by
  exact ⟨⟨List.range n, true⟩, by simp [graph, finals, Face.final], List.length_range⟩

/-! ### No loops -/

/-- GraphProps.thy: distinct_no_loop2 -/
theorem distinct_no_loop2 {f : Face} {u v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) (hu : u ∈ f.vertices) (huv : u ≠ v) :
    f.nextVertex v ≠ v := by
  obtain ⟨us, ws, hvs⟩ := List.append_of_mem hv
  have hd' : (us ++ v :: ws).Nodup := hvs ▸ hd
  have hvu : v ∉ us := fun hm => (List.nodup_append.mp hd').2.2 v hm v List.mem_cons_self rfl
  have hvw : v ∉ ws := (List.nodup_cons.mp (List.nodup_append.mp hd').2.1).1
  show nextElem f.vertices f.vertices.head! v ≠ v
  rw [hvs, nextElem_append hvu]
  cases ws with
  | nil =>
    rw [nextElem_cons_nil, if_pos (beq_self_eq_true v)]
    cases us with
    | nil =>
      exfalso
      rw [hvs] at hu
      exact huv (List.mem_singleton.mp hu)
    | cons a as =>
      show a ≠ v
      exact fun h => hvu (List.mem_cons.mpr (Or.inl h.symm))
  | cons w ws' =>
    rw [nextElem_cons_cons, if_pos (beq_self_eq_true v)]
    exact fun h => hvw (List.mem_cons.mpr (Or.inl h.symm))

/-- GraphProps.thy: distinct_no_loop1 -/
theorem distinct_no_loop1 {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) (hlen : 1 < f.vertices.length) : f.nextVertex v ≠ v := by
  obtain ⟨u, hu, huv⟩ : ∃ u ∈ f.vertices, u ≠ v := by
    obtain ⟨vs, fin⟩ := f
    cases vs with
    | nil => exact absurd hv List.not_mem_nil
    | cons a as =>
      cases as with
      | nil => simp at hlen
      | cons b bs =>
        by_cases hva : v = a
        · subst hva
          exact ⟨b, List.mem_cons_of_mem _ List.mem_cons_self,
            fun h => (List.nodup_cons.mp hd).1 (List.mem_cons.mpr (Or.inl h.symm))⟩
        · exact ⟨a, List.mem_cons_self, fun h => hva h.symm⟩
  exact distinct_no_loop2 hd hv hu huv

/-! ### between -/

section BetweenProps

variable [BEq α] [LawfulBEq α]

/-- GraphProps.thy: between_front -/
@[simp]
theorem between_front {u v : α} {us vs : List α} (h : v ∉ us) :
    between (u :: (us ++ v :: vs)) u v = us := by
  rw [between_of_splitAt (splitAt_self_cons u (us ++ v :: vs))]
  rw [if_pos (by simp),
    splitAt_append_of_not_mem h (v :: vs), splitAt_self_cons]
  exact List.append_nil _

/-- GraphProps.thy: between_back -/
theorem between_back {u v : α} {us vs : List α} (hv : v ∉ us) (hu : u ∉ vs)
    (hvu : v ≠ u) : between (v :: vs ++ u :: us) u v = us := by
  have hu' : u ∉ v :: vs := fun hm => (List.mem_cons.mp hm).elim (fun e => hvu e.symm) hu
  have hsp : splitAt u (v :: vs ++ u :: us) = (v :: vs, us) := by
    rw [show v :: vs ++ u :: us = (v :: vs) ++ u :: us from rfl,
      splitAt_append_of_not_mem hu' (u :: us), splitAt_self_cons]
    exact Prod.ext_iff.mpr ⟨List.append_nil _, rfl⟩
  rw [between_of_splitAt hsp, if_neg (fun hc => hv (List.contains_iff_mem.mp hc)),
    splitAt_self_cons]
  exact List.append_nil _

end BetweenProps

/-- GraphProps.thy: next_between -/
theorem next_between {f : Face} {u v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) (hu : u ∈ f.vertices) (h : f.nextVertex v ≠ u) :
    f.nextVertex v ∈ between f.vertices v u := by
  obtain ⟨us, ws, hvs⟩ := List.append_of_mem hv
  have hd' : (us ++ v :: ws).Nodup := hvs ▸ hd
  have hdus : us.Nodup := (List.nodup_append.mp hd').1
  have hdvws : (v :: ws).Nodup := (List.nodup_append.mp hd').2.1
  have hvu : v ∉ us := fun hm => (List.nodup_append.mp hd').2.2 v hm v List.mem_cons_self rfl
  have hsp : (us, ws) = splitAt v f.vertices := splitAt_dist_ram hd hvs
  have hopen : between f.vertices v u =
      if ws.contains u then (splitAt u ws).1 else ws ++ (splitAt u us).1 :=
    between_of_splitAt hsp.symm
  have hnv : f.nextVertex v = nextElem (v :: ws) f.vertices.head! v := by
    show nextElem f.vertices f.vertices.head! v = _
    rw [hvs]
    exact nextElem_append hvu _ _
  cases ws with
  | nil =>
    have e : nextElem [v] f.vertices.head! v = f.vertices.head! := by
      rw [nextElem_cons_nil, if_pos (beq_self_eq_true v)]
    rw [hnv, e] at h ⊢
    rw [hopen, if_neg (by simp), List.nil_append]
    rw [hvs] at hu
    rcases List.mem_append.mp hu with huA | huV
    · obtain ⟨p, q, hpq⟩ := List.append_of_mem huA
      have hspu : (p, q) = splitAt u us := splitAt_dist_ram hdus hpq
      rw [← hspu]
      cases p with
      | nil =>
        exfalso
        apply h
        rw [hvs, hpq]
        rfl
      | cons p0 ps =>
        rw [hvs, hpq]
        exact List.mem_cons_self
    · rw [List.mem_singleton] at huV
      subst huV
      rw [splitAt_no_ram hvu]
      cases us with
      | nil =>
        exfalso
        apply h
        rw [hvs]
        rfl
      | cons a as =>
        rw [hvs]
        exact List.mem_cons_self
  | cons w ws' =>
    have hnvw : f.nextVertex v = w := by
      rw [hnv, nextElem_cons_cons, if_pos (beq_self_eq_true v)]
    rw [hnvw] at h ⊢
    rw [hopen]
    by_cases huws : u ∈ w :: ws'
    · rw [if_pos (List.contains_iff_mem.mpr huws)]
      have huw : u ≠ w := Ne.symm h
      have huws' : u ∈ ws' := (List.mem_cons.mp huws).resolve_left huw
      obtain ⟨p, q, hpq⟩ := List.append_of_mem huws'
      have hspu : (w :: p, q) = splitAt u (w :: ws') := by
        apply splitAt_dist_ram (List.nodup_cons.mp hdvws).2
        rw [hpq]
        rfl
      rw [← hspu]
      exact List.mem_cons_self
    · rw [if_neg (mt List.contains_iff_mem.mp huws)]
      exact List.mem_append_left _ List.mem_cons_self

/-- GraphProps.thy: next_between2 -/
theorem next_between2 {f : Face} {u v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) (hu : u ∈ f.vertices) (huv : u ≠ v) :
    v ∈ between f.vertices u (f.nextVertex v) := by
  obtain ⟨p, q, hvs⟩ := List.append_of_mem hu
  have hd' : (p ++ u :: q).Nodup := hvs ▸ hd
  have hdp : p.Nodup := (List.nodup_append.mp hd').1
  have hduq : (u :: q).Nodup := (List.nodup_append.mp hd').2.1
  have hup : u ∉ p := fun hm => (List.nodup_append.mp hd').2.2 u hm u List.mem_cons_self rfl
  have huq : u ∉ q := (List.nodup_cons.mp hduq).1
  have hdq : q.Nodup := (List.nodup_cons.mp hduq).2
  have hdisjpq : ∀ x ∈ p, x ∉ q := by
    intro x hxp hxq
    exact (List.nodup_append.mp hd').2.2 x hxp x (List.mem_cons_of_mem _ hxq) rfl
  have hsp : (p, q) = splitAt u f.vertices := splitAt_dist_ram hd hvs
  have hopen : between f.vertices u (f.nextVertex v) =
      if q.contains (f.nextVertex v) then (splitAt (f.nextVertex v) q).1
      else q ++ (splitAt (f.nextVertex v) p).1 :=
    between_of_splitAt hsp.symm
  rw [hopen]
  have hv2 : v ∈ p ∨ v ∈ q := by
    have h1 : v ∈ p ++ u :: q := hvs ▸ hv
    rcases List.mem_append.mp h1 with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with e | h
      · exact absurd e.symm huv
      · exact Or.inr h
  rcases hv2 with hvp | hvq
  · -- `v` occurs before `u`
    obtain ⟨p₁, p₂, hp⟩ := List.append_of_mem hvp
    have hdp' : (p₁ ++ v :: p₂).Nodup := hp ▸ hdp
    have hvp₁ : v ∉ p₁ := fun hm => (List.nodup_append.mp hdp').2.2 v hm v List.mem_cons_self rfl
    have hvs2 : f.vertices = p₁ ++ v :: (p₂ ++ u :: q) := by
      rw [hvs, hp]
      simp [List.append_assoc]
    have hnv : f.nextVertex v = nextElem (v :: (p₂ ++ u :: q)) f.vertices.head! v := by
      show nextElem f.vertices f.vertices.head! v = _
      rw [hvs2]
      exact nextElem_append hvp₁ _ _
    cases p₂ with
    | nil =>
      have hnvu : f.nextVertex v = u := by
        rw [hnv]
        show nextElem (v :: u :: q) f.vertices.head! v = u
        rw [nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [hnvu]
      rw [if_neg (mt List.contains_iff_mem.mp huq), splitAt_no_ram hup]
      have hvp' : v ∈ p := by
        rw [hp]
        exact List.mem_append_right _ List.mem_cons_self
      exact List.mem_append_right _ hvp'
    | cons w p₂' =>
      have hnvw : f.nextVertex v = w := by
        rw [hnv]
        show nextElem (v :: w :: (p₂' ++ u :: q)) f.vertices.head! v = w
        rw [nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [hnvw]
      have hwp : w ∈ p := by
        rw [hp]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have hwq : w ∉ q := hdisjpq w hwp
      rw [if_neg (mt List.contains_iff_mem.mp hwq)]
      have hspw : (p₁ ++ [v], p₂') = splitAt w p := by
        apply splitAt_dist_ram hdp
        rw [hp]
        simp [List.append_assoc]
      rw [← hspw]
      exact List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self)
  · -- `v` occurs after `u`
    obtain ⟨q₁, q₂, hq⟩ := List.append_of_mem hvq
    have hdq' : (q₁ ++ v :: q₂).Nodup := hq ▸ hdq
    have hvq₁ : v ∉ q₁ := fun hm => (List.nodup_append.mp hdq').2.2 v hm v List.mem_cons_self rfl
    have hvp' : v ∉ p := fun h => hdisjpq v h hvq
    have hvs2 : f.vertices = (p ++ u :: q₁) ++ v :: q₂ := by
      rw [hvs, hq]
      simp [List.append_assoc]
    have hvnot : v ∉ p ++ u :: q₁ := by
      intro hm
      rcases List.mem_append.mp hm with h | h
      · exact hvp' h
      · rcases List.mem_cons.mp h with e | h
        · exact huv e.symm
        · exact hvq₁ h
    have hnv : f.nextVertex v = nextElem (v :: q₂) f.vertices.head! v := by
      show nextElem f.vertices f.vertices.head! v = _
      rw [hvs2]
      exact nextElem_append hvnot _ _
    cases q₂ with
    | nil =>
      have hnvh : f.nextVertex v = f.vertices.head! := by
        rw [hnv, nextElem_cons_nil, if_pos (beq_self_eq_true v)]
      have hhead_mem : f.vertices.head! ∈ p ++ [u] := by
        cases p with
        | nil =>
          rw [hvs]
          exact List.mem_cons_self
        | cons a p' =>
          rw [hvs]
          exact List.mem_append_left _ List.mem_cons_self
      have hhead_notin : f.vertices.head! ∉ q := by
        intro hm
        rcases List.mem_append.mp hhead_mem with h | h
        · exact hdisjpq _ h hm
        · rw [List.mem_singleton] at h
          exact huq (h ▸ hm)
      rw [hnvh, if_neg (mt List.contains_iff_mem.mp hhead_notin)]
      exact List.mem_append_left _ hvq
    | cons x q₂' =>
      have hnvx : f.nextVertex v = x := by
        rw [hnv, nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [hnvx]
      have hxq : x ∈ q := by
        rw [hq]
        exact List.mem_append_right _
          (List.mem_cons_of_mem _ List.mem_cons_self)
      rw [if_pos (List.contains_iff_mem.mpr hxq)]
      have hspx : (q₁ ++ [v], q₂') = splitAt x q := by
        apply splitAt_dist_ram hdq
        rw [hq]
        simp [List.append_assoc]
      rw [← hspx]
      exact List.mem_append_right _ List.mem_cons_self

/-- GraphProps.thy: between_next_empty -/
theorem between_next_empty {f : Face} {v : Vertex} (hd : f.vertices.Nodup) :
    between f.vertices v (f.nextVertex v) = [] := by
  by_cases hv : v ∈ f.vertices
  · obtain ⟨us, ws, hvs⟩ := List.append_of_mem hv
    have hd' : (us ++ v :: ws).Nodup := hvs ▸ hd
    have hvu : v ∉ us := fun hm => (List.nodup_append.mp hd').2.2 v hm v List.mem_cons_self rfl
    have hsp : (us, ws) = splitAt v f.vertices := splitAt_dist_ram hd hvs
    have hnv : f.nextVertex v = nextElem (v :: ws) f.vertices.head! v := by
      show nextElem f.vertices f.vertices.head! v = _
      rw [hvs]
      exact nextElem_append hvu _ _
    cases ws with
    | nil =>
      have e : f.nextVertex v = f.vertices.head! := by
        rw [hnv, nextElem_cons_nil, if_pos (beq_self_eq_true v)]
      rw [e, between_of_splitAt hsp.symm, if_neg (by simp)]
      cases us with
      | nil => rfl
      | cons a as =>
        have e2 : f.vertices.head! = a := by
          rw [hvs]
          rfl
        rw [e2, splitAt_self_cons]
        rfl
    | cons w ws' =>
      have e : f.nextVertex v = w := by
        rw [hnv, nextElem_cons_cons, if_pos (beq_self_eq_true v)]
      rw [e, between_of_splitAt hsp.symm, if_pos (by simp), splitAt_self_cons]
  · have hnv : f.nextVertex v = f.vertices.head! := nextElem_notin hv
    rw [hnv]
    cases hvs : f.vertices with
    | nil => rfl
    | cons a as =>
      rw [hvs] at hv
      rw [between_of_splitAt (splitAt_no_ram hv), if_neg (by simp)]
      have e : (a :: as).head! = a := rfl
      rw [e, splitAt_self_cons]
      rfl

/-- GraphProps.thy: unroll_between_next2 -/
theorem unroll_between_next2 {f : Face} {u v : Vertex} (hd : f.vertices.Nodup)
    (hu : u ∈ f.vertices) (hv : v ∈ f.vertices) (huv : u ≠ v) :
    between f.vertices u (f.nextVertex v) = between f.vertices u v ++ [v] := by
  have hmem : f.nextVertex v ∈ f.vertices := nextVertex_in_face hv
  have hb := split_between hd hu hmem (next_between2 hd hv hu huv)
  rw [if_neg huv, between_next_empty hd, List.append_nil] at hb
  exact hb

/-- GraphProps.thy: nextVertex_eq_lemma. The Isabelle proof is a long case
bash; here we rotate the vertex list to start at `x`, so that
`x :: between .. x y ++ [y]` becomes a prefix, and use that the cyclic
successor is rotation-invariant (`nextElem_head_rotate`). -/
theorem nextVertex_eq_lemma {f : Face} {x y v : Vertex} (z : Vertex)
    (hd : f.vertices.Nodup) (hx : x ∈ f.vertices) (hy : y ∈ f.vertices)
    (hxy : x ≠ y) (hv : v ∈ x :: between f.vertices x y) :
    f.nextVertex v = nextElem (x :: between f.vertices x y ++ [y]) z v := by
  obtain ⟨pre, post, hsp⟩ : ∃ pre post, (pre, post) = splitAt x f.vertices := ⟨_, _, rfl⟩
  have h1 : (splitAt x f.vertices).1 = pre := congrArg Prod.fst hsp.symm
  have hvs : f.vertices = pre ++ x :: post := splitAt_split hx hsp
  have hopen : between f.vertices x y =
      if post.contains y then (splitAt y post).1 else post ++ (splitAt y pre).1 :=
    between_of_splitAt hsp.symm
  have hvvs : v ∈ f.vertices := by
    rcases List.mem_cons.mp hv with rfl | hvb
    · exact hx
    · exact inbetween_inset hvb
  have hrot : rotate_to f.vertices x = f.vertices.rotate pre.length := by
    rw [rotate_to_eq_rotate hx, h1]
  have hndR : (rotate_to f.vertices x).Nodup := by
    rw [hrot]
    exact List.nodup_rotate.mpr hd
  have hnv : f.nextVertex v = nextElem (rotate_to f.vertices x)
      (rotate_to f.vertices x).head! v := by
    show nextElem f.vertices f.vertices.head! v = _
    exact (nextElem_head_rotate pre.length hd hvvs).trans (by rw [hrot])
  have hR : rotate_to f.vertices x = x :: post ++ pre := by
    show x :: (splitAt x f.vertices).2 ++ (splitAt x f.vertices).1 = _
    rw [h1]
    have h2 : (splitAt x f.vertices).2 = post := congrArg Prod.snd hsp.symm
    rw [h2]
  set L := x :: between f.vertices x y ++ [y] with hL
  by_cases hcase : y ∈ post
  · -- `y` occurs after `x`: the segment is a prefix of the rotated list
    have hpost_y : post = (splitAt y post).1 ++ y :: (splitAt y post).2 := splitAt_ram hcase
    rw [hpost_y] at hR
    have hbet : between f.vertices x y = (splitAt y post).1 := by
      rw [hopen, if_pos (List.contains_iff_mem.mpr hcase)]
    have hRL : rotate_to f.vertices x = L ++ ((splitAt y post).2 ++ pre) := by
      rw [hR, hL, hbet]
      simp [List.append_assoc]
    obtain ⟨l₁, m, hlm⟩ := List.append_of_mem hv
    have hLsplit : L = l₁ ++ v :: (m ++ [y]) := by
      rw [hL, hlm]
      simp [List.append_assoc]
    have hRsplit : rotate_to f.vertices x =
        (l₁ ++ v :: (m ++ [y])) ++ ((splitAt y post).2 ++ pre) := by
      rw [hRL, hLsplit]
    have hvl₁ : v ∉ l₁ := by
      have hnd := hRsplit ▸ hndR
      exact fun hm =>
        (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 v hm v List.mem_cons_self rfl
    rw [hnv, hRsplit, hLsplit]
    exact nextElem_append_preserve hvl₁ (by simp)
  · -- `y` occurs before `x`: the segment wraps around
    have hcont : ¬ (post.contains y = true) := mt List.contains_iff_mem.mp hcase
    have hypre : y ∈ pre := by
      have h1' : y ∈ pre ++ x :: post := hvs ▸ hy
      rcases List.mem_append.mp h1' with h | h
      · exact h
      · rcases List.mem_cons.mp h with e | h
        · exact absurd e (Ne.symm hxy)
        · exact absurd h hcase
    have hpre_y : pre = (splitAt y pre).1 ++ y :: (splitAt y pre).2 := splitAt_ram hypre
    rw [hpre_y] at hR
    have hbet : between f.vertices x y = post ++ (splitAt y pre).1 := by
      rw [hopen, if_neg hcont]
    have hRL : rotate_to f.vertices x = L ++ (splitAt y pre).2 := by
      rw [hR, hL, hbet]
      simp [List.append_assoc]
    obtain ⟨l₁, m, hlm⟩ := List.append_of_mem hv
    have hLsplit : L = l₁ ++ v :: (m ++ [y]) := by
      rw [hL, hlm]
      simp [List.append_assoc]
    have hRsplit : rotate_to f.vertices x =
        (l₁ ++ v :: (m ++ [y])) ++ (splitAt y pre).2 := by
      rw [hRL, hLsplit]
    have hvl₁ : v ∉ l₁ := by
      have hnd := hRsplit ▸ hndR
      exact fun hm =>
        (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 v hm v List.mem_cons_self rfl
    rw [hnv, hRsplit, hLsplit]
    exact nextElem_append_preserve hvl₁ (by simp)

end Kepler.Graphs
