/-
Port of the fourth (last) block (lines 3455–4958) of the Isabelle AFP
"Flyspeck-Tame" theory `FaceDivisionProps.thy`: the `removeNones`,
`natToVertexList`, `indexToVertexList` and `pre_subdivFace(')` sections.

Source: `reference/afp-flyspeck-tame/FaceDivisionProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Correspondence notes: as in `FaceDivisionProps2.lean`
(`hd`/`last`/`butlast` ↦ `List.head!`/`List.getLast!`/`List.dropLast`,
`distinct` ↦ `List.Nodup`, `xs ! i` ↦ `xs[i]!`).  `the (hd vs)` is rendered
as `vs.head!.get!`.  List comprehensions `[x ← xs. P x]` are rendered as
`xs.filter (fun x => decide (P x))`; set hypotheses such as
`set zs ∩ set us ⊆ {u} ∪ set as` are rendered as membership implications.

Everything in the block is ported, including Isabelle's `List.nths`
(selection by an index set, defined here classically as `nths`) and the
HOL `List.thy` lemmas used in the sequel (`nths_append`, `filter_in_nths`).
The ~500-line `pre_subdivFace'_Some1'` proof is split into the private
auxiliary lemmas `splitFace_new_edge_in_f21` (the shared edge case split of
its `rule5''`/`rule6` steps), `invalidVertexList_splitFace_transfer` (rule5)
and `not_is_duplicateEdge_splitFace` (rule6).  Isabelle's intermediate
facts `rule5'`, `rule5''`, `rule5'''`, `face_set_eq`, `dists`, `edges_or`,
`dist_f`, `edges_g'`, `edges_g'_or` are dead code (never used by the final
assembly) and are not ported.  The two `declare ... [simp del]` lines
(`incrIndexList_help4`, `verticesFrom_between`) are not applicable: dropping
the global `@[simp]` would require editing `EnumeratorProps.lean` (out of
scope), and no proof below depends on it.
-/
import Kepler.Graphs.FaceDivisionProps3
import Kepler.Graphs.EnumeratorProps

namespace Kepler.Graphs

/-! ### removeNones -/

/-- FaceDivisionProps.thy: removeNones. `[the x. x ← vOptionList, x ≠ None]`
rendered as a recursive definition. -/
def removeNones : List (Option α) → List α
  | [] => []
  | none :: xs => removeNones xs
  | some a :: xs => a :: removeNones xs

/-- FaceDivisionProps.thy: removeNones_inI -/
theorem removeNones_inI {a : α} {ls : List (Option α)} (h : some a ∈ ls) :
    a ∈ removeNones ls := by
  induction ls with
  | nil => exact absurd h (List.not_mem_nil)
  | cons x xs ih =>
    rcases List.mem_cons.mp h with hx | htl
    · subst hx
      exact List.mem_cons_self
    · cases x with
      | none => exact ih htl
      | some b => exact List.mem_cons_of_mem _ (ih htl)

/-- FaceDivisionProps.thy: removeNones_hd -/
@[simp] theorem removeNones_hd {a : α} {ls : List (Option α)} :
    removeNones (some a :: ls) = a :: removeNones ls := rfl

/-- FaceDivisionProps.thy: removeNones_last -/
@[simp] theorem removeNones_last {a : α} {ls : List (Option α)} :
    removeNones (ls ++ [some a]) = removeNones ls ++ [a] := by
  induction ls with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [removeNones]

/-- FaceDivisionProps.thy: removeNones_in -/
@[simp] theorem removeNones_in {a : α} {as bs : List (Option α)} :
    removeNones (as ++ some a :: bs) = removeNones as ++ a :: removeNones bs := by
  induction as with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [removeNones]

/-- FaceDivisionProps.thy: removeNones_none_hd -/
@[simp] theorem removeNones_none_hd {ls : List (Option α)} :
    removeNones (none :: ls) = removeNones ls := rfl

/-- FaceDivisionProps.thy: removeNones_none_last -/
@[simp] theorem removeNones_none_last {ls : List (Option α)} :
    removeNones (ls ++ [none]) = removeNones ls := by
  induction ls with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [removeNones]

/-- FaceDivisionProps.thy: removeNones_none_in -/
@[simp] theorem removeNones_none_in {as bs : List (Option α)} :
    removeNones (as ++ none :: bs) = removeNones (as ++ bs) := by
  induction as with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all

/-- FaceDivisionProps.thy: removeNones_empty -/
@[simp] theorem removeNones_empty : removeNones ([] : List (Option α)) = [] := rfl

/-! ### natToVertexList -/

/-- FaceDivisionProps.thy: natToVertexListRec -/
def natToVertexListRec (old : Nat) (v : Vertex) (f : Face) :
    List Nat → List (Option Vertex)
  | [] => []
  | i :: is =>
    if i = old then none :: natToVertexListRec i v f is
    else some (f.nextVertices i v) :: natToVertexListRec i v f is

/-- FaceDivisionProps.thy: natToVertexList -/
def natToVertexList (v : Vertex) (f : Face) : List Nat → List (Option Vertex)
  | [] => []
  | i :: is =>
    if i = 0 then some v :: natToVertexListRec i v f is else []

/-! ### indexToVertexList -/

/-- FaceDivisionProps.thy: nextVertex_inj -/
theorem nextVertex_inj {f : Face} {v : Vertex} (hd : f.vertices.Nodup)
    (hv : v ∈ f.vertices) {i a : Nat} (hi : i < f.vertices.length)
    (ha : a < f.vertices.length)
    (h : f.nextVertices a v = f.nextVertices i v) : i = a := by
  have hvf : (verticesFrom f v).Nodup := verticesFrom_distinct hd hv
  have hlen := verticesFrom_length hd hv
  have eq : (verticesFrom f v)[a]! = (verticesFrom f v)[i]! := by
    rw [verticesFrom_nth hd ha hv, verticesFrom_nth hd hi hv]
    exact h
  exact ((List.getElem!_inj (by rw [hlen]; exact ha) (by rw [hlen]; exact hi) hvf).mp eq).symm

/-- FaceDivisionProps.thy: a -/
theorem hideDupsRec_eq_natToVertexListRec {f : Face} {v : Vertex}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices) {a : Nat}
    (ha : a < f.vertices.length) {is : List Nat}
    (his : ∀ i ∈ is, i < f.vertices.length) :
    hideDupsRec (f.nextVertices a v) (is.map (fun k => f.nextVertices k v)) =
      natToVertexListRec a v f is := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih =>
    have hi : i < f.vertices.length := his i List.mem_cons_self
    have his' : ∀ j ∈ is, j < f.vertices.length :=
      fun j hj => his j (List.mem_cons_of_mem _ hj)
    by_cases hia : i = a
    · subst hia
      simp only [List.map_cons, hideDupsRec, beq_self_eq_true, ↓reduceIte,
        natToVertexListRec]
      exact congrArg (none :: ·) (ih hi his')
    · have hne : f.nextVertices a v ≠ f.nextVertices i v :=
        fun h => hia (nextVertex_inj hd hv hi ha h)
      simp only [List.map_cons, hideDupsRec, beq_iff_eq, hne, ↓reduceIte,
        natToVertexListRec, if_neg hia]
      exact congrArg (some (f.nextVertices i v) :: ·) (ih hi his')

/-- FaceDivisionProps.thy: indexToVertexList_natToVertexList_eq -/
theorem indexToVertexList_natToVertexList_eq {f : Face} {v : Vertex}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices) {is : List Nat}
    (his : ∀ i ∈ is, i < f.vertices.length) (hne : is ≠ []) (hhd : is.head! = 0) :
    indexToVertexList f v is = natToVertexList v f is := by
  cases is with
  | nil => exact absurd rfl hne
  | cons i is' =>
    have hi0 : i = 0 := by simpa using hhd
    subst hi0
    have hpos : 0 < f.vertices.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hv)
    have his' : ∀ j ∈ is', j < f.vertices.length :=
      fun j hj => his j (List.mem_cons_of_mem _ hj)
    show hideDups ((0 :: is').map (fun k => f.nextVertices k v)) =
      natToVertexList v f (0 :: is')
    rw [List.map_cons, hideDups, natToVertexList, if_pos rfl]
    exact congrArg (some v :: ·)
      (hideDupsRec_eq_natToVertexListRec hd hv hpos his')

/-! ### natToVertexListRec / natToVertexList length lemmas -/

/-- FaceDivisionProps.thy: nvlr_length -/
theorem nvlr_length {v : Vertex} {f : Face} {ls : List Nat} :
    ∀ {old : Nat}, (natToVertexListRec old v f ls).length = ls.length := by
  induction ls with
  | nil => intro old; rfl
  | cons i is ih =>
    intro old
    simp only [natToVertexListRec]
    split <;> simp [List.length_cons, ih]

/-- FaceDivisionProps.thy: nvl_length -/
@[simp] theorem nvl_length {v : Vertex} {f : Face} {e : List Nat} (h : e.head! = 0) :
    (natToVertexList v f e).length = e.length := by
  cases e with
  | nil => rfl
  | cons i is =>
    have hi : i = 0 := by simpa using h
    subst hi
    simp [natToVertexList, nvlr_length]

/-- FaceDivisionProps.thy: natToVertexListRec_length -/
@[simp] theorem natToVertexListRec_length {v : Vertex} {e : Nat} {f : Face}
    {es : List Nat} : (natToVertexListRec e v f es).length = es.length :=
  nvlr_length

/-- FaceDivisionProps.thy: natToVertexList_length -/
@[simp] theorem natToVertexList_length {v : Vertex} {f : Face} {es : List Nat}
    (h : incrIndexList es es.length f.vertices.length) :
    (natToVertexList v f es).length = es.length := by
  cases es with
  | nil => rfl
  | cons i is =>
    have hi : i = 0 := h.2.2.1
    subst hi
    simp [natToVertexList]

/-- FaceDivisionProps.thy: natToVertexList_nth_Suc (inner `natToVertexListRec`
recurrence) -/
theorem natToVertexListRec_nth_Suc {v : Vertex} {f : Face} {es : List Nat} :
    ∀ {old n : Nat}, n + 1 < es.length →
      (natToVertexListRec old v f es)[n + 1]! =
        (if es[n]! = es[n + 1]! then none
         else some (f.nextVertices es[n + 1]! v)) := by
  induction es with
  | nil => intro old n h; simp at h
  | cons e es ih =>
    intro old n h
    cases es with
    | nil => simp only [List.length_cons, List.length_nil] at h; omega
    | cons e' es' =>
      cases n with
      | zero =>
        by_cases h1 : e = old
        · by_cases h2 : e' = e
          · simp [natToVertexListRec, if_pos h1, h2]
          · simp [natToVertexListRec, if_pos h1, if_neg h2,
              if_neg (show e ≠ e' from fun he => h2 he.symm)]
        · by_cases h2 : e' = e
          · simp [natToVertexListRec, if_neg h1, h2]
          · simp [natToVertexListRec, if_neg h1, if_neg h2,
              if_neg (show e ≠ e' from fun he => h2 he.symm)]
      | succ m =>
        have hlen : m + 1 < (e' :: es').length := by
          simp only [List.length_cons] at h ⊢; omega
        have ih' := ih (old := e) hlen
        by_cases h1 : e = old
        · simp only [natToVertexListRec, if_pos h1, List.getElem!_cons_succ]
          exact ih'
        · simp only [natToVertexListRec, if_neg h1, List.getElem!_cons_succ]
          exact ih'

/-- FaceDivisionProps.thy: natToVertexList_nth_Suc -/
theorem natToVertexList_nth_Suc {v : Vertex} {f : Face} {es : List Nat} {n : Nat}
    (hincr : incrIndexList es es.length f.vertices.length) (hn : n + 1 < es.length) :
    (natToVertexList v f es)[n + 1]! =
      (if es[n]! = es[n + 1]! then none
       else some (f.nextVertices es[n + 1]! v)) := by
  cases es with
  | nil => simp at hn
  | cons e es' =>
    have he : e = 0 := hincr.2.2.1
    subst he
    have hrec0 := natToVertexListRec_nth_Suc (v := v) (f := f) (old := 0) hn
    have hrec : natToVertexListRec 0 v f (0 :: es') =
        none :: natToVertexListRec 0 v f es' := rfl
    rw [hrec, List.getElem!_cons_succ] at hrec0
    rw [natToVertexList, if_pos rfl, List.getElem!_cons_succ]
    exact hrec0

/-- FaceDivisionProps.thy: natToVertexList_nth_0 -/
theorem natToVertexList_nth_0 {v : Vertex} {f : Face} {es : List Nat}
    (hincr : incrIndexList es es.length f.vertices.length) (hpos : 0 < es.length) :
    (natToVertexList v f es)[0]! = some (f.nextVertices es[0]! v) := by
  cases es with
  | nil => simp at hpos
  | cons e es' =>
    have he : e = 0 := hincr.2.2.1
    subst he
    rw [natToVertexList, if_pos rfl, List.getElem!_cons_zero, List.getElem!_cons_zero]
    rfl

/-- FaceDivisionProps.thy: natToVertexList_hd -/
@[simp] theorem natToVertexList_hd {v : Vertex} {f : Face} {es : List Nat}
    (hincr : incrIndexList es es.length f.vertices.length) :
    (natToVertexList v f es).head! = some v := by
  cases es with
  | nil => simp [incrIndexList] at hincr
  | cons e es' =>
    have he : e = 0 := hincr.2.2.1
    subst he
    rw [natToVertexList, if_pos rfl]
    rfl

/-- FaceDivisionProps.thy: nth_last -/
theorem nth_last [Inhabited α] {xs : List α} {i : Nat} (h : i + 1 = xs.length) :
    xs[i]! = xs.getLast! := by
  rw [List.getLast!_eq_getElem!]
  congr 1
  omega

/-- Auxiliary (no direct Isabelle counterpart; `incrIndexList` there is
unfolded by `auto`): every entry of an `increasing` list is bounded by its
last element. -/
theorem le_getLast_of_mem_increasing {ls : List Nat} (h : increasing ls) :
    ∀ {i : Nat}, i ∈ ls → i ≤ ls.getLast! := by
  induction ls with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    intro i hi
    rcases List.mem_cons.mp hi with hix | hi
    · subst i
      cases xs with
      | nil => exact le_refl _
      | cons y ys =>
        have hxy : x ≤ y := h x y [] ys rfl
        have hinc : increasing (y :: ys) :=
          fun a b as bs e => h a b (x :: as) bs (by rw [e]; simp)
        exact le_trans hxy (ih hinc List.mem_cons_self)
    · cases xs with
      | nil => simp at hi
      | cons y ys =>
        have hinc : increasing (y :: ys) :=
          fun a b as bs e => h a b (x :: as) bs (by rw [e]; simp)
        have hg : (x :: y :: ys).getLast! = (y :: ys).getLast! := by
          simp only [List.getLast!_eq_getElem!, List.length_cons, Nat.add_sub_cancel,
            List.getElem!_cons_succ]
        rw [hg]
        exact ih hinc hi

/-- FaceDivisionProps.thy: natToVertexList_last -/
@[simp] theorem natToVertexList_last {v : Vertex} {f : Face} {es : List Nat}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices)
    (hincr : incrIndexList es es.length f.vertices.length) :
    (natToVertexList v f es).getLast! = some (verticesFrom f v).getLast! := by
  have h1 : 1 < es.length := hincr.1
  have hlenf : 1 < f.vertices.length := hincr.2.1
  have hnmax : es.getLast! = f.vertices.length - 1 := hincr.2.2.2.1
  have hdlt : es.dropLast.getLast! < es.getLast! := hincr.2.2.2.2.2.1
  set n' := es.length - 2 with hn'
  have hn'l : n' + 1 + 1 = es.length := by omega
  have hn'lt : n' + 1 < es.length := by omega
  have last_ntvl : (natToVertexList v f es)[n' + 1]! =
      (natToVertexList v f es).getLast! :=
    nth_last (by rw [natToVertexList_length hincr]; omega)
  have last_es : es[n' + 1]! = es.getLast! := nth_last hn'l
  have hdrop : es[n']! = es.dropLast.getLast! := by
    have hlen : es.dropLast.length = n' + 1 := by
      rw [List.length_dropLast]; omega
    rw [← nth_last (xs := es.dropLast) (i := n') (by omega), List.dropLast_eq_take,
      List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
      List.getElem?_take_of_lt (show n' < es.length - 1 by omega)]
  have hless : es[n']! < es[n' + 1]! := by rw [hdrop, last_es]; exact hdlt
  have hnth := natToVertexList_nth_Suc (v := v) (f := f) hincr hn'lt
  rw [if_neg (ne_of_lt hless)] at hnth
  rw [last_ntvl, last_es, hnmax] at hnth
  rw [hnth]
  have hvf : (verticesFrom f v)[f.vertices.length - 1]! =
      f.nextVertices (f.vertices.length - 1) v :=
    verticesFrom_nth hd (by omega) hv
  rw [← hvf]
  congr 1
  exact nth_last (by rw [verticesFrom_length hd hv]; omega)

/-- FaceDivisionProps.thy: indexToVertexList_last -/
@[simp] theorem indexToVertexList_last {v : Vertex} {f : Face} {es : List Nat}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices)
    (hincr : incrIndexList es es.length f.vertices.length) :
    (indexToVertexList f v es).getLast! = some (verticesFrom f v).getLast! := by
  have hne : es ≠ [] := by
    intro e; rw [e] at hincr; simp [incrIndexList] at hincr
  have h1 : 1 < f.vertices.length := hincr.2.1
  have his : ∀ i ∈ es, i < f.vertices.length := by
    intro i hi
    have hle := le_getLast_of_mem_increasing hincr.2.2.2.2.2.2 hi
    rw [hincr.2.2.2.1] at hle
    omega
  rw [indexToVertexList_natToVertexList_eq hd hv his hne hincr.2.2.1]
  exact natToVertexList_last hd hv hincr

/-- Auxiliary: `take (i+1)` as snoc, with `getElem!` (cf. Isabelle
`take_Suc_conv_app_nth`). -/
theorem take_succ_eq_append_getElem! [Inhabited α] {l : List α} {i : Nat}
    (h : i < l.length) : l.take (i + 1) = l.take i ++ [l[i]!] := by
  rw [List.take_succ_eq_append_getElem h, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

/-- Auxiliary (Isabelle `id_take_nth_drop`, with `getElem!`). -/
theorem id_take_nth_drop [Inhabited α] {l : List α} {i : Nat} (h : i < l.length) :
    l = l.take i ++ l[i]! :: l.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop (l := l) (i := i)]
  rw [List.drop_eq_getElem_cons h, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

/-- Auxiliary: snoc-decomposition of a nonempty list, with `getLast!`. -/
theorem dropLast_append_getLast! [Inhabited α] {l : List α} (h : l ≠ []) :
    l.dropLast ++ [l.getLast!] = l := by
  have h2 := List.dropLast_concat_getLast h
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  exact h2


open Classical

/-- Isabelle HOL `List.nths` (`nths xs A` keeps the elements of `xs` whose
index lies in the index set `A`).  Classical, since `A : Set Nat`. -/
noncomputable def nths : List α → Set Nat → List α
  | [], _ => []
  | x :: xs, A => (if 0 ∈ A then [x] else []) ++ nths xs {j | j + 1 ∈ A}

/-- HOL List.thy: nths_Nil -/
@[simp] theorem nths_nil (A : Set Nat) : nths ([] : List α) A = [] := rfl

/-- HOL List.thy: nths_Cons -/
theorem nths_cons (x : α) (xs : List α) (A : Set Nat) :
    nths (x :: xs) A = (if 0 ∈ A then [x] else []) ++ nths xs {j | j + 1 ∈ A} :=
  rfl

/-- Auxiliary: `nths` over the empty index set. -/
@[simp] theorem nths_empty (xs : List α) : nths xs ∅ = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have e : {j | j + 1 ∈ (∅ : Set Nat)} = ∅ := by ext j; simp
    rw [nths_cons, if_neg (by simp), e, ih]
    rfl

/-- FaceDivisionProps.thy: nths_take -/
theorem nths_take {xs : List α} :
    ∀ {n : Nat} {A : Set Nat}, (∀ i ∈ A, i < n) →
      nths (xs.take n) A = nths xs A := by
  induction xs with
  | nil => intro n A _; rw [List.take_nil]
  | cons x xs ih =>
    intro n A h
    cases n with
    | zero =>
      have e : A = ∅ := by
        ext i
        simp only [Set.mem_empty_iff_false, iff_false]
        exact fun hi => Nat.not_lt_zero i (h i hi)
      rw [List.take_zero, e, nths_empty, nths_empty]
    | succ m =>
      rw [List.take_succ_cons, nths_cons, nths_cons,
        ih (fun i hi => by
          have h2 : i + 1 ∈ A := hi
          have := h (i + 1) h2
          omega)]

/-- FaceDivisionProps.thy: nths_reduceIndices -/
theorem nths_reduceIndices {xs : List α} :
    ∀ {A : Set Nat}, nths xs A = nths xs {i | i < xs.length ∧ i ∈ A} := by
  induction xs with
  | nil => intro A; rw [nths_nil, nths_nil]
  | cons x xs ih =>
    intro A
    rw [nths_cons, nths_cons]
    have e1 : (0 ∈ ({i | i < (x :: xs).length ∧ i ∈ A} : Set Nat)) ↔ 0 ∈ A := by
      simp [List.length_cons]
    have e2 : {j | j + 1 ∈ ({i | i < (x :: xs).length ∧ i ∈ A} : Set Nat)} =
        {i | i < xs.length ∧ i ∈ {j | j + 1 ∈ A}} := by
      ext j
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by simp only [List.length_cons] at h1; omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by simp only [List.length_cons]; omega, h2⟩
    rw [e2, ← ih, propext e1]

/-- HOL List.thy: nths_append -/
theorem nths_append (l l' : List α) (A : Set Nat) :
    nths (l ++ l') A = nths l A ++ nths l' {j | j + l.length ∈ A} := by
  induction l generalizing A with
  | nil => rw [List.nil_append, nths_nil]; simp
  | cons x xs ih =>
    rw [List.cons_append, nths_cons, nths_cons, ih]
    have e : {j | j + xs.length ∈ ({j | j + 1 ∈ A} : Set Nat)} =
        {j | j + (x :: xs).length ∈ A} := by
      ext j
      simp only [List.length_cons, Set.mem_setOf_eq]
      rw [show j + xs.length + 1 = j + (xs.length + 1) from by omega]
    rw [e, ← List.append_assoc]

/-- Auxiliary: every element of `nths xs A` is an element of `xs`. -/
theorem mem_nths_mem {x : α} {xs : List α} {A : Set Nat} (h : x ∈ nths xs A) :
    x ∈ xs := by
  induction xs generalizing A with
  | nil => rw [nths_nil] at h; exact absurd h List.not_mem_nil
  | cons y ys ih =>
    rw [nths_cons] at h
    by_cases h0 : 0 ∈ A
    · rw [if_pos h0] at h
      rcases List.mem_append.mp h with h | h
      · rw [List.mem_singleton.mp h]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    · rw [if_neg h0] at h
      exact List.mem_cons_of_mem _ (ih (List.mem_append.mp h |>.resolve_left (by simp)))

/-- HOL List.thy: filter_in_nths -/
theorem filter_in_nths {xs : List α} [DecidableEq α] (hd : xs.Nodup) (A : Set Nat) :
    xs.filter (fun x => decide (x ∈ nths xs A)) = nths xs A := by
  induction xs generalizing A with
  | nil => rw [nths_nil]; simp
  | cons x xs ih =>
    have hxs : xs.Nodup := (List.nodup_cons.mp hd).2
    have hx : x ∉ xs := (List.nodup_cons.mp hd).1
    have hnotin : x ∉ nths xs {j | j + 1 ∈ A} := fun hm => hx (mem_nths_mem hm)
    have hcongr : ∀ y ∈ xs, decide (y ∈ nths (x :: xs) A) =
        decide (y ∈ nths xs {j | j + 1 ∈ A}) := by
      intro y hy
      rw [nths_cons]
      by_cases h0 : 0 ∈ A
      · rw [if_pos h0]
        have hne : y ≠ x := fun e => hx (e ▸ hy)
        simp [hne]
      · rw [if_neg h0]
        simp
    by_cases h0 : 0 ∈ A
    · have hmem : (fun y => decide (y ∈ nths (x :: xs) A)) x = true := by
        rw [nths_cons, if_pos h0]
        simp
      simp only [List.filter_cons, hmem]
      rw [List.filter_congr hcongr, ih hxs, nths_cons, if_pos h0]
      rfl
    · have hmem : (fun y => decide (y ∈ nths (x :: xs) A)) x = false := by
        rw [nths_cons, if_neg h0]
        simp [hnotin]
      simp only [List.filter_cons, hmem]
      rw [List.filter_congr hcongr, ih hxs, nths_cons, if_neg h0]
      rfl

/-- FaceDivisionProps.thy: natToVertexList_nths1 -/
theorem natToVertexList_nths1 {f : Face} {v : Vertex} {vs : List Vertex}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices) (hvs : vs = verticesFrom f v)
    {es : List Nat} {n : Nat}
    (hincr : incrIndexList es es.length vs.length) (hn : n ≤ es.length) :
    nths (vs.take (es[n - 1]! + 1)) {i | i ∈ es.take n} =
      removeNones ((natToVertexList v f es).take n) := by
  subst hvs
  induction n with
  | zero =>
    rw [List.take_zero, List.take_zero]
    have e : {i | i ∈ ([] : List Nat)} = (∅ : Set Nat) := by ext i; simp
    rw [e, nths_empty]
    rfl
  | succ n ih =>
    have hSuc : n + 1 ≤ es.length := hn
    have hnl : n < es.length := by omega
    have ih' := ih (by omega)
    have lvs : (verticesFrom f v).length = f.vertices.length := verticesFrom_length hd hv
    have hincr' : incrIndexList es es.length f.vertices.length := by rwa [← lvs]
    have hlen_vs : 1 < (verticesFrom f v).length := hincr.2.1
    have hes0 : es[0]! = 0 := by
      have h1 : es.head! = 0 := hincr.2.2.1
      rwa [List.head!_eq_getElem!] at h1
    have hv0 : (verticesFrom f v)[0]! = v := by
      rw [← List.head!_eq_getElem!]; exact verticesFrom_hd f v
    cases n with
    | zero =>
      have ht1 : es.take (0 + 1) = [0] := by
        rw [take_succ_eq_append_getElem! (by omega : 0 < es.length),
          List.take_zero, List.nil_append, hes0]
      have ht2 : (natToVertexList v f es).take (0 + 1) = [some v] := by
        rw [take_succ_eq_append_getElem! (by
            rw [natToVertexList_length hincr']; omega : 0 < (natToVertexList v f es).length),
          List.take_zero, List.nil_append,
          natToVertexList_nth_0 hincr' (by omega : 0 < es.length), hes0]
        rfl
      have ht3 : (verticesFrom f v).take (es[0 + 1 - 1]! + 1) = [v] := by
        have e0 : es[0 + 1 - 1]! = 0 := hes0
        rw [e0, take_succ_eq_append_getElem! (by omega : 0 < (verticesFrom f v).length),
          List.take_zero, List.nil_append, hv0]
      have e : {i | i ∈ ([0] : List Nat)} = ({0} : Set Nat) := by ext i; simp
      have e2 : {j | j + 1 ∈ ({0} : Set Nat)} = ∅ := by
        ext j
        simp only [Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact Nat.succ_ne_zero j
      rw [ht1, ht2, ht3, e, nths_cons, if_pos (by simp), e2, nths_empty]
      rfl
    | succ n' =>
      have hn'lt : n' + 1 < es.length := by omega
      have hn'l : n' < es.length := by omega
      cases hcase : (natToVertexList v f es)[n' + 1]! with
      | none =>
        have hnth := natToVertexList_nth_Suc (v := v) (f := f) hincr' hn'lt
        rw [hcase] at hnth
        have esn : es[n' + 1]! = es[n']! := by
          by_cases hc : es[n']! = es[n' + 1]!
          · exact hc.symm
          · rw [if_neg hc] at hnth
            simp at hnth
        by_cases hT : n' + 1 + 1 = es.length
        · have hlast : es[n' + 1]! = es.getLast! := nth_last hT
          have hdrop : es[n']! = es.dropLast.getLast! := by
            rw [← nth_last (xs := es.dropLast) (i := n') (by
              rw [List.length_dropLast]; omega), List.dropLast_eq_take,
              List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
              List.getElem?_take_of_lt (show n' < es.length - 1 by omega)]
          have hdlt : es.dropLast.getLast! < es.getLast! := hincr.2.2.2.2.2.1
          omega
        · have hmem_last : es[n']! ∈ es.take (n' + 1) := by
            rw [take_succ_eq_append_getElem! hn'l]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          have hset_goal : {i | i ∈ es.take (n' + 1 + 1)} =
              {i | i ∈ es.take (n' + 1)} := by
            rw [take_succ_eq_append_getElem! hn'lt]
            ext i
            simp only [List.mem_append, List.mem_singleton, Set.mem_setOf_eq]
            constructor
            · rintro (hi | rfl)
              · exact hi
              · rw [esn]; exact hmem_last
            · intro hi
              exact Or.inl hi
          have hnTVLl : (natToVertexList v f es).length = es.length :=
            natToVertexList_length hincr'
          have htake_r : (natToVertexList v f es).take (n' + 1 + 1) =
              (natToVertexList v f es).take (n' + 1) ++ [none] := by
            rw [take_succ_eq_append_getElem! (by
              omega : n' + 1 < (natToVertexList v f es).length), hcase]
          have e0 : es[n' + 1 + 1 - 1]! = es[n']! := esn
          have ih'' : nths ((verticesFrom f v).take (es[n']! + 1))
              {i | i ∈ es.take (n' + 1)} =
              removeNones ((natToVertexList v f es).take (n' + 1)) := ih'
          rw [hset_goal, htake_r, removeNones_none_last, e0]
          exact ih''
      | some v' =>
        have hnth := natToVertexList_nth_Suc (v := v) (f := f) hincr' hn'lt
        rw [hcase] at hnth
        have esn : es[n' + 1]! ≠ es[n']! := by
          by_contra hc
          rw [if_pos hc.symm] at hnth
          simp at hnth
        rw [if_neg (fun h => esn h.symm)] at hnth
        have hv'eq : v' = f.nextVertices es[n' + 1]! v := Option.some.inj hnth
        have hinc : increasing es := hincr.2.2.2.2.2.2
        have hmem1 : es[n']! ∈ es.take (n' + 1) := by
          rw [take_succ_eq_append_getElem! hn'l]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hle : es[n']! ≤ es[n' + 1]! :=
          increasing2 (id_take_nth_drop hn'lt ▸ hinc) hmem1 List.mem_cons_self
        have smaller_n : es[n']! < es[n' + 1]! :=
          lt_of_le_of_ne hle (fun h => esn h.symm)
        have hmem_esn : es[n' + 1]! ∈ es :=
          List.take_subset (n' + 2) es (by
            rw [take_succ_eq_append_getElem! hn'lt]
            exact List.mem_append_right _ (List.mem_singleton_self _))
        have smaller : es[n' + 1]! < (verticesFrom f v).length := by
          have hle2 := le_getLast_of_mem_increasing hinc hmem_esn
          rw [hincr.2.2.2.1] at hle2
          omega
        have hvF : (verticesFrom f v)[es[n' + 1]!]! = f.nextVertices es[n' + 1]! v :=
          verticesFrom_nth hd (by rw [← lvs]; exact smaller) hv
        have hvF' : (verticesFrom f v)[es[n' + 1]!]! = v' := hvF.trans hv'eq.symm
        have helper : ∀ x ∈ es.take (n' + 1), x ≤ es[n']! := by
          intro x hx
          have hdec := id_take_nth_drop (l := es) hn'l
          have hle' : ∀ y ∈ es.take n', y ≤ es[n']! := by
            intro y hy
            exact increasing2 (hdec ▸ hinc) hy List.mem_cons_self
          rw [take_succ_eq_append_getElem! hn'l] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hle' x hx
          · exact (List.mem_singleton.mp hx).le
        have hlt : ∀ x ∈ es.take (n' + 1), x < es[n' + 1]! :=
          fun x hx => Nat.lt_of_le_of_lt (helper x hx) smaller_n
        have elim_insert : {i | i < es[n' + 1]! ∧
            i ∈ insert es[n' + 1]! {i' | i' ∈ es.take (n' + 1)}} =
            {i | i ∈ es.take (n' + 1)} := by
          ext i
          constructor
          · rintro ⟨h1, h2⟩
            rcases h2 with rfl | h2
            · exact absurd h1 (Nat.lt_irrefl _)
            · exact h2
          · intro hi
            exact ⟨hlt i hi, Set.mem_insert_of_mem _ hi⟩
        have len : ((verticesFrom f v).take (es[n' + 1]!)).length = es[n' + 1]! := by
          rw [List.length_take]
          omega
        have sub2 : nths ((verticesFrom f v).take (es[n' + 1]!))
            (insert es[n' + 1]! {i | i ∈ es.take (n' + 1)}) =
            nths ((verticesFrom f v).take (es[n' + 1]!)) {i | i ∈ es.take (n' + 1)} := by
          rw [nths_reduceIndices, len, elim_insert]
        have htake_len : ((verticesFrom f v).take (es[n']! + 1)).length =
            es[n']! + 1 := by
          rw [List.length_take]
          omega
        have empty : {j | j + ((verticesFrom f v).take (es[n']! + 1)).length ∈
            {i | i ∈ es.take (n' + 1)}} = ∅ := by
          rw [htake_len]
          ext j
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hj
          have h2 := helper _ hj
          omega
        have hm' : es[n' + 1]! = (es[n']! + 1) + (es[n' + 1]! - (es[n']! + 1)) := by
          omega
        have step : nths ((verticesFrom f v).take (es[n' + 1]!))
            {i | i ∈ es.take (n' + 1)} =
            nths ((verticesFrom f v).take (es[n']! + 1)) {i | i ∈ es.take (n' + 1)} := by
          rw [hm', List.take_add, nths_append, empty, nths_empty, List.append_nil]
        have sub3 : nths ((verticesFrom f v).take (es[n' + 1]!))
            (insert es[n' + 1]! {i | i ∈ es.take (n' + 1)}) =
            nths ((verticesFrom f v).take (es[n']! + 1)) {i | i ∈ es.take (n' + 1)} :=
          sub2.trans step
        have sub1 : nths [(verticesFrom f v)[es[n' + 1]!]!]
            {j | j + es[n' + 1]! ∈ insert es[n' + 1]! {i | i ∈ es.take (n' + 1)}} =
            [v'] := by
          rw [nths_cons, if_pos (by simp), nths_nil, hvF', List.append_nil]
        have hset_goal : {i | i ∈ es.take (n' + 1 + 1)} =
            insert es[n' + 1]! {i | i ∈ es.take (n' + 1)} := by
          rw [take_succ_eq_append_getElem! hn'lt]
          ext i
          simp only [List.mem_append, List.mem_singleton, Set.mem_setOf_eq,
            Set.mem_insert_iff, or_comm]
        have htake_l : (verticesFrom f v).take (es[n' + 1 + 1 - 1]! + 1) =
            (verticesFrom f v).take (es[n' + 1]!) ++
              [(verticesFrom f v)[es[n' + 1]!]!] := by
          have e0 : es[n' + 1 + 1 - 1]! = es[n' + 1]! := rfl
          rw [e0]
          exact take_succ_eq_append_getElem! smaller
        have hnTVLl : (natToVertexList v f es).length = es.length :=
          natToVertexList_length hincr'
        have htake_r : (natToVertexList v f es).take (n' + 1 + 1) =
            (natToVertexList v f es).take (n' + 1) ++ [some v'] := by
          rw [take_succ_eq_append_getElem! (by
            omega : n' + 1 < (natToVertexList v f es).length), hcase]
        have ih'' : nths ((verticesFrom f v).take (es[n']! + 1))
            {i | i ∈ es.take (n' + 1)} =
            removeNones ((natToVertexList v f es).take (n' + 1)) := ih'
        rw [hset_goal, htake_l, htake_r, nths_append, len, sub3, sub1,
          removeNones_last, ih'']

/-- FaceDivisionProps.thy: natToVertexList_nths -/
theorem natToVertexList_nths {f : Face} {v : Vertex} {es : List Nat}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices)
    (hincr : incrIndexList es es.length f.vertices.length) :
    nths (verticesFrom f v) {i | i ∈ es} = removeNones (natToVertexList v f es) := by
  have lvs : (verticesFrom f v).length = f.vertices.length := verticesFrom_length hd hv
  have hincr' : incrIndexList es es.length (verticesFrom f v).length := by rwa [lvs]
  have h1 : 1 < es.length := hincr.1
  have hlast : es[es.length - 1]! = es.getLast! := nth_last (by omega)
  have hgl : es.getLast! = (verticesFrom f v).length - 1 := hincr'.2.2.2.1
  have htake : (verticesFrom f v).take (es[es.length - 1]! + 1) =
      verticesFrom f v := by
    rw [hlast, hgl,
      show (verticesFrom f v).length - 1 + 1 = (verticesFrom f v).length from by
        have h2 : 1 < (verticesFrom f v).length := by rw [lvs]; exact hincr.2.1
        omega]
    exact List.take_of_length_le (by omega)
  have htake2 : (natToVertexList v f es).take es.length = natToVertexList v f es :=
    List.take_of_length_le (by rw [natToVertexList_length hincr])
  have htake3 : es.take es.length = es := List.take_of_length_le (by omega)
  have hres := natToVertexList_nths1 hd hv rfl hincr' (n := es.length) (by omega)
  rw [htake, htake2, htake3] at hres
  exact hres

/-- Auxiliary: `getLast!` of a cons with nonempty tail. -/
theorem getLast!_cons_of_ne_nil [Inhabited α] {x : α} {l : List α} (hl : l ≠ []) :
    (x :: l).getLast! = l.getLast! := by
  cases l with
  | nil => exact absurd rfl hl
  | cons y ys => rfl

/-! ### invalidVertexList -/

/-- FaceDivisionProps.thy: filter_Cons2 -/
theorem filter_Cons2 {x : α} {ys : List α} {P : α → Prop} [DecidableEq α]
    [DecidablePred P] (h : x ∉ ys) :
    ys.filter (fun y => decide (y = x ∨ P y)) = ys.filter (fun y => decide (P y)) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have hy : y ≠ x := fun e => h (e ▸ List.mem_cons_self)
    have hys : x ∉ ys := fun hm => h (List.mem_cons_of_mem _ hm)
    by_cases hp : P y
    · simp only [List.filter_cons,
        show (fun z => decide (z = x ∨ P z)) y = true from by simp [hp],
        show (fun z => decide (P z)) y = true from by simp [hp], ↓reduceIte, ih hys]
    · simp only [List.filter_cons,
        show (fun z => decide (z = x ∨ P z)) y = false from by simp [hp, hy],
        show (fun z => decide (P z)) y = false from by simp [hp], ih hys]

/-- FaceDivisionProps.thy: natToVertexList_removeNones -/
theorem natToVertexList_removeNones {f : Face} {v : Vertex} {es : List Nat}
    (hd : f.vertices.Nodup) (hv : v ∈ f.vertices)
    (hincr : incrIndexList es es.length f.vertices.length) :
    (verticesFrom f v).filter
        (fun x => decide (x ∈ removeNones (natToVertexList v f es))) =
      removeNones (natToVertexList v f es) := by
  have dist : (verticesFrom f v).Nodup := verticesFrom_distinct hd hv
  have sub_eq : nths (verticesFrom f v) {i | i ∈ es} =
      removeNones (natToVertexList v f es) := natToVertexList_nths hd hv hincr
  rw [← sub_eq]
  exact filter_in_nths dist {i | i ∈ es}

/-- FaceDivisionProps.thy: is_duplicateEdge -/
def is_duplicateEdge (g : Graph) (f : Face) (a b : Vertex) : Prop :=
  ((a, b) ∈ g.edges ∧ (a, b) ∉ f.edges ∧ (b, a) ∉ f.edges) ∨
    ((b, a) ∈ g.edges ∧ (b, a) ∉ f.edges ∧ (a, b) ∉ f.edges)

/-- FaceDivisionProps.thy: invalidVertexList -/
def invalidVertexList (g : Graph) (f : Face) (vs : List (Option Vertex)) : Prop :=
  ∃ i < vs.length - 1, match vs[i]! with
    | none => False
    | some a => match vs[i + 1]! with
      | none => False
      | some b => is_duplicateEdge g f a b

/-! ### pre_subdivFace(') -/

/-- FaceDivisionProps.thy: pre_subdivFace_face -/
def pre_subdivFace_face (f : Face) (v' : Vertex)
    (vOptionList : List (Option Vertex)) : Prop :=
  (verticesFrom f v').filter (fun v => decide (v ∈ removeNones vOptionList)) =
      removeNones vOptionList ∧
    f.final = false ∧ f.vertices.Nodup ∧
    vOptionList.head! = some v' ∧ v' ∈ f.vertices ∧
    vOptionList.getLast! = some (verticesFrom f v').getLast! ∧
    vOptionList.tail.head! ≠ vOptionList.getLast! ∧
    2 < vOptionList.length ∧ vOptionList ≠ [] ∧ vOptionList.tail ≠ []

/-- FaceDivisionProps.thy: pre_subdivFace -/
def pre_subdivFace (g : Graph) (f : Face) (v' : Vertex)
    (vOptionList : List (Option Vertex)) : Prop :=
  pre_subdivFace_face f v' vOptionList ∧ ¬ invalidVertexList g f vOptionList

/-- FaceDivisionProps.thy: pre_subdivFace' -/
def pre_subdivFace' (g : Graph) (f : Face) (v' ram1 : Vertex) (n : Nat)
    (vOptionList : List (Option Vertex)) : Prop :=
  f.final = false ∧ v' ∈ f.vertices ∧ ram1 ∈ f.vertices ∧
    v' ∉ removeNones vOptionList ∧ f.vertices.Nodup ∧
    (((verticesFrom f v').filter (fun v => decide (v ∈ removeNones vOptionList)) =
        removeNones vOptionList) ∧
      before (verticesFrom f v') ram1 (removeNones vOptionList).head! ∧
      vOptionList.getLast! = some (verticesFrom f v').getLast! ∧
      vOptionList ≠ [] ∧
      ((v' = ram1 ∧ 0 < n) ∨
        (v' = ram1 ∧ vOptionList.head! ≠ some (verticesFrom f v').getLast!) ∨
        v' ≠ ram1) ∧
      ¬ invalidVertexList g f vOptionList ∧
      (n = 0 ∧ vOptionList.head! ≠ none →
        ¬ is_duplicateEdge g f ram1 vOptionList.head!.get!) ∨
      (vOptionList = [] ∧ v' ≠ ram1))

/-- FaceDivisionProps.thy: pre_subdivFace_face_in_f -/
theorem pre_subdivFace_face_in_f {f : Face} {v a : Vertex} {ls : List (Option Vertex)}
    (h : pre_subdivFace_face f v ls) (ha : some a ∈ ls) : a ∈ verticesFrom f v := by
  have h1 : a ∈ removeNones ls := removeNones_inI ha
  rw [← h.1] at h1
  exact (List.mem_filter.mp h1).1

/-- FaceDivisionProps.thy: pre_subdivFace_in_f -/
theorem pre_subdivFace_in_f {g : Graph} {f : Face} {v a : Vertex}
    {ls : List (Option Vertex)}
    (h : pre_subdivFace g f v ls) (ha : some a ∈ ls) : a ∈ verticesFrom f v :=
  pre_subdivFace_face_in_f h.1 ha

/-- FaceDivisionProps.thy: pre_subdivFace_face_in_f' -/
theorem pre_subdivFace_face_in_f' {f : Face} {v a : Vertex} {ls : List (Option Vertex)}
    (h : pre_subdivFace_face f v ls) (ha : some a ∈ ls) : a ∈ f.vertices := by
  by_cases hav : a = v
  · subst hav; exact h.2.2.2.2.1
  · exact verticesFrom_in' (pre_subdivFace_face_in_f h ha) hav

/-- FaceDivisionProps.thy: filter_congs_shorten1 -/
theorem filter_congs_shorten1 {f : Face} {v a : Vertex} {vs : List Vertex}
    (hdist : (verticesFrom f v).Nodup)
    (h : (verticesFrom f v).filter (fun w => decide (w = a ∨ w ∈ vs)) = a :: vs) :
    (verticesFrom f v).filter (fun w => decide (w ∈ vs)) = vs := by
  have rule1 : ∀ {xs : List Vertex} {a : Vertex} {ys : List Vertex},
      xs.Nodup →
      xs.filter (fun w => decide (w = a ∨ w ∈ ys)) = a :: ys →
      xs.filter (fun w => decide (w ∈ ys)) = ys := by
    intro xs a ys
    induction xs with
    | nil => intro _ h; simp at h
    | cons x xs ih =>
      intro hdxs hays
      have hdist' : (a :: ys).Nodup := by
        have h1 := hdxs.filter (fun w => decide (w = a ∨ w ∈ ys))
        rw [hays] at h1
        exact h1
      have hdxs' : xs.Nodup := (List.nodup_cons.mp hdxs).2
      have hxs : x ∉ xs := (List.nodup_cons.mp hdxs).1
      by_cases hxa : x = a
      · subst hxa
        have ha_ys : x ∉ ys := (List.nodup_cons.mp hdist').1
        simp only [List.filter_cons] at hays
        obtain ⟨-, htl⟩ := List.cons.inj hays
        simp only [List.filter_cons, show (fun w => decide (w ∈ ys)) x = false
            from by simp [ha_ys]]
        rw [← filter_Cons2 hxs]
        exact htl
      · by_cases hmem : x ∈ ys
        · simp only [List.filter_cons, show (fun w => decide (w = a ∨ w ∈ ys)) x = true
            from by simp [hmem], ↓reduceIte] at hays
          obtain ⟨hxae, -⟩ := List.cons.inj hays
          exact absurd hxae hxa
        · simp only [List.filter_cons, show (fun w => decide (w = a ∨ w ∈ ys)) x = false
            from by simp [hxa, hmem]] at hays
          simp only [List.filter_cons, show (fun w => decide (w ∈ ys)) x = false
            from by simp [hmem]]
          exact ih hdxs' hays
  exact rule1 hdist h

/-- FaceDivisionProps.thy: ovl_shorten -/
theorem ovl_shorten {f : Face} {v : Vertex} {vol : List (Option Vertex)}
    {va : Option Vertex} (hdist : (verticesFrom f v).Nodup)
    (h : (verticesFrom f v).filter (fun w => decide (w ∈ removeNones (va :: vol))) =
        removeNones (va :: vol)) :
    (verticesFrom f v).filter (fun w => decide (w ∈ removeNones vol)) =
      removeNones vol := by
  cases va with
  | none => exact h
  | some a =>
    have e : (fun w => decide (w ∈ removeNones (some a :: vol))) =
        (fun w => decide (w = a ∨ w ∈ removeNones vol)) := by
      funext w
      simp only [show removeNones (some a :: vol) = a :: removeNones vol from rfl,
        List.mem_cons]
    rw [e] at h
    exact filter_congs_shorten1 hdist h

/-- FaceDivisionProps.thy: pre_subdivFace_face_distinct -/
theorem pre_subdivFace_face_distinct {f : Face} {v : Vertex} {vol : List (Option Vertex)}
    (h : pre_subdivFace_face f v vol) : (removeNones vol).Nodup := by
  rw [← h.1]
  exact (verticesFrom_distinct h.2.2.1 h.2.2.2.2.1).filter _

/-- FaceDivisionProps.thy: invalidVertexList_shorten -/
theorem invalidVertexList_shorten {g : Graph} {f : Face} {vol : List (Option Vertex)}
    {v : Option Vertex} (h : invalidVertexList g f vol) :
    invalidVertexList g f (v :: vol) := by
  obtain ⟨i, hi, hcase⟩ := h
  refine ⟨i + 1, by simp only [List.length_cons]; omega, ?_⟩
  rw [List.getElem!_cons_succ, List.getElem!_cons_succ]
  exact hcase

/-- FaceDivisionProps.thy: pre_subdivFace_pre_subdivFace' -/
theorem pre_subdivFace_pre_subdivFace' {g : Graph} {f : Face} {v : Vertex}
    {vo : Option Vertex} {vol : List (Option Vertex)}
    (hv : v ∈ f.vertices) (h : pre_subdivFace g f v (vo :: vol)) :
    pre_subdivFace' g f v v 0 vol := by
  obtain ⟨hf, hinv⟩ := h
  have hvoeq : vo = some v := by simpa using hf.2.2.2.1
  subst hvoeq
  have hvolne : vol ≠ [] := by
    intro e
    have hlen : 2 < (some v :: vol).length := hf.2.2.2.2.2.2.2.1
    rw [e, List.length_cons, List.length_nil] at hlen
    omega
  have hgl : (some v :: vol).getLast! = vol.getLast! := getLast!_cons_of_ne_nil hvolne
  have r : removeNones vol ≠ [] := by
    intro hr
    have hlast : (some v :: vol).getLast! = some (verticesFrom f v).getLast! :=
      hf.2.2.2.2.2.1
    have hall : ∀ x ∈ vol, x = none := by
      intro x hx
      cases x with
      | none => rfl
      | some a => exact absurd (hr ▸ removeNones_inI hx) List.not_mem_nil
    have hnone : vol.getLast! = none := hall _ (getLast!_mem hvolne)
    rw [hgl, hnone] at hlast
    simp at hlast
  have hhdmem : ∀ {vol : List (Option Vertex)}, removeNones vol ≠ [] →
      some (removeNones vol).head! ∈ vol := by
    intro vol
    induction vol with
    | nil => intro hr; exact absurd rfl hr
    | cons x xs ih =>
      intro hr
      cases x with
      | none =>
        rw [removeNones_none_hd] at hr ⊢
        exact List.mem_cons_of_mem _ (ih hr)
      | some a =>
        rw [removeNones_hd]
        simp
  have hd : (removeNones vol).head! ∈ f.vertices :=
    pre_subdivFace_face_in_f' hf (List.mem_cons_of_mem _ (hhdmem r))
  have hdist : (removeNones (some v :: vol)).Nodup := pre_subdivFace_face_distinct hf
  rw [removeNones_hd] at hdist
  have hvnin : v ∉ removeNones vol := (List.nodup_cons.mp hdist).1
  have hne : v ≠ (removeNones vol).head! := by
    intro hvw
    exact hvnin (hvw ▸ head!_mem r)
  have hfilter : (verticesFrom f v).filter (fun w => decide (w ∈ removeNones vol)) =
      removeNones vol :=
    ovl_shorten (verticesFrom_distinct hf.2.2.1 hv) hf.1
  have hbefore : before (verticesFrom f v) v (removeNones vol).head! :=
    before_verticesFrom hf.2.2.1 hv hd hne
  have hlast2 : vol.getLast! = some (verticesFrom f v).getLast! := by
    rw [← hgl]; exact hf.2.2.2.2.2.1
  have h6 : vol.getLast! = some (verticesFrom f v).getLast! := hgl ▸ hf.2.2.2.2.2.1
  have hdisj : (v = v ∧ 0 < 0) ∨
      (v = v ∧ vol.head! ≠ some (verticesFrom f v).getLast!) ∨ v ≠ v := by
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    have h7 := hf.2.2.2.2.2.2.1
    rw [List.tail_cons, hgl, h6] at h7
    exact h7
  have hinvalid : ¬ invalidVertexList g f vol :=
    fun hbad => hinv (invalidVertexList_shorten hbad)
  have h0 : 0 < (some v :: vol).length - 1 := by
    rw [List.length_cons]
    have := List.length_pos_iff.mpr hvolne
    omega
  refine ⟨hf.2.1, hv, hv, hvnin, hf.2.2.1,
    Or.inl ⟨hfilter, hbefore, hlast2, hvolne, hdisj, hinvalid, ?_⟩⟩
  intro hpre
  obtain ⟨-, hhd⟩ := hpre
  cases hcase : vol.head! with
  | none => exact absurd hcase hhd
  | some y =>
    have h2 : ¬ is_duplicateEdge g f v y := by
      intro hdup
      apply hinv
      refine ⟨0, h0, ?_⟩
      rw [show (some v :: vol)[0]! = some v from rfl,
        show (some v :: vol)[0 + 1]! = vol.head! from List.head!_eq_getElem!.symm, hcase]
      exact hdup
    exact h2

/-- FaceDivisionProps.thy: pre_subdivFace'_distinct -/
theorem pre_subdivFace'_distinct {g : Graph} {f : Face} {v' v : Vertex} {n : Nat}
    {vol : List (Option Vertex)} (h : pre_subdivFace' g f v' v n vol) :
    (removeNones vol).Nodup := by
  obtain ⟨-, hv', -, -, hdist, hbig⟩ := h
  rcases hbig with ⟨hfilter, -⟩ | ⟨rfl, -⟩
  · rw [← hfilter]
    exact (verticesFrom_distinct hdist hv').filter _
  · simp

/-- FaceDivisionProps.thy: natToVertexList_pre_subdivFace_face -/
theorem natToVertexList_pre_subdivFace_face {f : Face} {v : Vertex} {es : List Nat}
    (hfin : f.final = false) (hd : f.vertices.Nodup) (hv : v ∈ f.vertices)
    (hlen : 2 < es.length) (hincr : incrIndexList es es.length f.vertices.length) :
    pre_subdivFace_face f v (natToVertexList v f es) := by
  have lastOvl : (natToVertexList v f es).getLast! =
      some (verticesFrom f v).getLast! := natToVertexList_last hd hv hincr
  have nvl_l : 2 < (natToVertexList v f es).length := by
    rw [natToVertexList_length hincr]; exact hlen
  have hfilter := natToVertexList_removeNones hd hv hincr
  have hdist : (removeNones (natToVertexList v f es)).Nodup := by
    rw [← hfilter]
    exact (verticesFrom_distinct hd hv).filter _
  have hd_last : (natToVertexList v f es).tail.head! ≠
      (natToVertexList v f es).getLast! := by
    have hne1 : natToVertexList v f es ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨T, hT⟩ : ∃ T, natToVertexList v f es = some v :: T := ⟨_, by
      have h1 := (List.cons_head!_tail hne1).symm
      rwa [natToVertexList_hd hincr] at h1⟩
    have hTne : T ≠ [] := by
      rw [hT, List.length_cons] at nvl_l
      exact List.ne_nil_of_length_pos (by omega)
    have hgl : (some v :: T).getLast! = T.getLast! := getLast!_cons_of_ne_nil hTne
    intro hcontra
    rw [hT, List.tail_cons, hgl] at hcontra
    cases hTlast : T.getLast! with
    | none =>
      rw [hT, hgl, hTlast] at lastOvl
      simp at lastOvl
    | some w =>
      have hThead : T.head! = some w := by rw [hcontra, hTlast]
      have hT2 : T.tail ≠ [] := by
        rw [hT, List.length_cons] at nvl_l
        have h1 : 1 ≤ T.tail.length := by rw [List.length_tail]; omega
        exact List.ne_nil_of_length_pos (by omega)
      have hTcons : T = some w :: T.tail := by
        have h1 := (List.cons_head!_tail hTne).symm
        rwa [hThead] at h1
      have hmemDL : some w ∈ T.dropLast := by
        obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hT2
        rw [hTcons, hys, List.dropLast_cons_cons]
        exact List.mem_cons_self
      have hdecomp : T = T.dropLast ++ [some w] := by
        have h1 := dropLast_append_getLast! hTne
        rw [hTlast] at h1
        exact h1.symm
      have hrm : removeNones (some v :: T) = (v :: removeNones T.dropLast) ++ [w] := by
        rw [removeNones_hd,
          show v :: removeNones T = v :: removeNones (T.dropLast ++ [some w]) from
            congrArg (fun l => v :: removeNones l) hdecomp,
          removeNones_last, List.cons_append]
      rw [hT, hrm] at hdist
      have hdisj := (List.nodup_append.mp hdist).2.2
      have hmem : w ∈ v :: removeNones T.dropLast :=
        List.mem_cons_of_mem _ (removeNones_inI hmemDL)
      exact hdisj w hmem w (List.mem_singleton_self w) rfl
  refine ⟨hfilter, hfin, hd, natToVertexList_hd hincr, hv, lastOvl, hd_last, nvl_l,
    List.ne_nil_of_length_pos (by omega), ?_⟩
  have h1 : 0 < (natToVertexList v f es).tail.length := by
    rw [List.length_tail]
    omega
  exact List.ne_nil_of_length_pos h1

/-- FaceDivisionProps.thy: indexToVertexList_pre_subdivFace_face -/
theorem indexToVertexList_pre_subdivFace_face {f : Face} {v : Vertex} {es : List Nat}
    (hfin : f.final = false) (hd : f.vertices.Nodup) (hv : v ∈ f.vertices)
    (hlen : 2 < es.length) (hincr : incrIndexList es es.length f.vertices.length) :
    pre_subdivFace_face f v (indexToVertexList f v es) := by
  have hne : es ≠ [] := List.ne_nil_of_length_pos (by omega)
  have h1 : 1 < f.vertices.length := hincr.2.1
  have his : ∀ i ∈ es, i < f.vertices.length := by
    intro i hi
    have hle := le_getLast_of_mem_increasing hincr.2.2.2.2.2.2 hi
    rw [hincr.2.2.2.1] at hle
    omega
  rw [indexToVertexList_natToVertexList_eq hd hv his hne hincr.2.2.1]
  exact natToVertexList_pre_subdivFace_face hfin hd hv hlen hincr

/-- FaceDivisionProps.thy: subdivFace_subdivFace'_eq -/
theorem subdivFace_subdivFace'_eq {g : Graph} {f : Face} {v : Vertex}
    {vol : List (Option Vertex)} (h : pre_subdivFace g f v vol) :
    subdivFace g f vol = subdivFace' g f v 0 vol.tail := by
  have hhd : vol.head! = some v := h.1.2.2.2.1
  simp [subdivFace, hhd]

/-- FaceDivisionProps.thy: pre_subdivFace'_None -/
theorem pre_subdivFace'_None {g : Graph} {f : Face} {v' v : Vertex} {n : Nat}
    {vol : List (Option Vertex)} (h : pre_subdivFace' g f v' v n (none :: vol)) :
    pre_subdivFace' g f v' v (n + 1) vol := by
  obtain ⟨hfin, hv', hram, hvnin, hdist, hbig⟩ := h
  rcases hbig with ⟨hfilter, hbefore, hlast, -, hdisj, hinv, -⟩ | ⟨hcontra, -⟩
  · have hvolne : vol ≠ [] := by
      intro e
      rw [e] at hlast
      simp at hlast
    have hgl : (none :: vol).getLast! = vol.getLast! := getLast!_cons_of_ne_nil hvolne
    refine ⟨hfin, hv', hram, hvnin, hdist, Or.inl ⟨hfilter, hbefore, ?_, hvolne, ?_, ?_, ?_⟩⟩
    · rw [← hgl]; exact hlast
    · rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩ | hne'
      · exact Or.inl ⟨h1, Nat.succ_pos n⟩
      · exact Or.inl ⟨h1, Nat.succ_pos n⟩
      · exact Or.inr (Or.inr hne')
    · exact fun hbad => hinv (invalidVertexList_shorten hbad)
    · intro hpre
      exact absurd hpre.1 (Nat.succ_ne_zero n)
  · exact absurd hcontra (List.cons_ne_nil _ _)

/-- FaceDivisionProps.thy: verticesFrom_split -/
theorem verticesFrom_split {f : Face} {v : Vertex} :
    v :: (verticesFrom f v).tail = verticesFrom f v := rfl

/-- FaceDivisionProps.thy: splitAt_fst -/
@[simp] theorem splitAt_fst [BEq α] [LawfulBEq α] {v : α} {xs a b : List α}
    (hd : xs.Nodup) (h : xs = a ++ v :: b) : (splitAt v xs).1 = a := by
  have hv : v ∈ xs := h ▸ List.mem_append_right _ List.mem_cons_self
  exact dist_at1 hd (splitAt_ram hv) h

/-- FaceDivisionProps.thy: splitAt_snd -/
@[simp] theorem splitAt_snd [BEq α] [LawfulBEq α] {v : α} {xs a b : List α}
    (hd : xs.Nodup) (h : xs = a ++ v :: b) : (splitAt v xs).2 = b := by
  have hv : v ∈ xs := h ▸ List.mem_append_right _ List.mem_cons_self
  exact dist_at2 hd (splitAt_ram hv) h

/-- FaceDivisionProps.thy: verticesFrom_v -/
theorem verticesFrom_v {f : Face} {v : Vertex} {a b : List Vertex}
    (hd : f.vertices.Nodup) (h : f.vertices = a ++ v :: b) :
    verticesFrom f v = v :: b ++ a := by
  have hfst : (splitAt v f.vertices).1 = a := splitAt_fst hd h
  have hsnd : (splitAt v f.vertices).2 = b := splitAt_snd hd h
  show v :: (splitAt v f.vertices).2 ++ (splitAt v f.vertices).1 = v :: b ++ a
  rw [hfst, hsnd]

/-- FaceDivisionProps.thy: verticesFrom_splitAt_v_fst -/
@[simp] theorem verticesFrom_splitAt_v_fst {f : Face} {v : Vertex}
    (_hd : (verticesFrom f v).Nodup) : (splitAt v (verticesFrom f v)).1 = [] := by
  have e : verticesFrom f v =
      v :: (splitAt v f.vertices).2 ++ (splitAt v f.vertices).1 := rfl
  rw [e, List.cons_append, splitAt_self_cons]

/-- FaceDivisionProps.thy: verticesFrom_splitAt_v_snd -/
@[simp] theorem verticesFrom_splitAt_v_snd {f : Face} {v : Vertex}
    (_hd : (verticesFrom f v).Nodup) :
    (splitAt v (verticesFrom f v)).2 = (verticesFrom f v).tail := by
  have e : verticesFrom f v =
      v :: (splitAt v f.vertices).2 ++ (splitAt v f.vertices).1 := rfl
  rw [e, List.cons_append, splitAt_self_cons]
  rfl

/-- FaceDivisionProps.thy: filter_distinct_at -/
theorem filter_distinct_at {xs as bs us : List α} {u : α} {P : α → Prop}
    [DecidableEq α] [DecidablePred P]
    (hd : xs.Nodup) (hxs : xs = as ++ u :: bs)
    (h : xs.filter (fun v => decide (v = u ∨ P v)) = u :: us) :
    bs.filter (fun v => decide (P v)) = us ∧
      as.filter (fun v => decide (P v)) = [] := by
  have hd' : (as ++ u :: bs).Nodup := hxs ▸ hd
  rw [List.nodup_append] at hd'
  obtain ⟨-, hdubs, hdisj⟩ := hd'
  have hunbs : u ∉ bs := (List.nodup_cons.mp hdubs).1
  have huas : u ∉ as := fun hu => hdisj u hu u List.mem_cons_self rfl
  have h2 : xs.filter (fun v => decide (v = u ∨ P v)) =
      as.filter (fun v => decide (P v)) ++ u :: bs.filter (fun v => decide (P v)) := by
    rw [hxs, List.filter_append, filter_Cons2 huas, List.filter_cons,
      filter_Cons2 hunbs]
    simp
  have h3 := dist_at (hd.filter _) h2 (h.trans (List.nil_append _).symm)
  exact ⟨h3.2, h3.1⟩

/-- FaceDivisionProps.thy: filter_distinct_at3 -/
theorem filter_distinct_at3 {xs as bs us zs : List α} {u : α} {P : α → Prop}
    [DecidableEq α] [DecidablePred P]
    (hd : xs.Nodup) (hxs : xs = as ++ u :: bs)
    (h : xs.filter (fun v => decide (v = u ∨ P v)) = u :: us)
    (hzs : ∀ z ∈ zs, z ∈ as ∨ ¬ P z) :
    (zs ++ bs).filter (fun v => decide (P v)) = us := by
  obtain ⟨hbs, has⟩ := filter_distinct_at hd hxs h
  rw [List.filter_eq_nil_iff] at has
  have hzs' : zs.filter (fun v => decide (P v)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro z hz
    rcases hzs z hz with hzas | hz
    · exact has z hzas
    · exact fun hp => hz (of_decide_eq_true hp)
  rw [List.filter_append, hbs, hzs', List.nil_append]

/-- FaceDivisionProps.thy: filter_distinct_at4 -/
theorem filter_distinct_at4 {xs as bs us zs : List α} {u : α} [DecidableEq α]
    (hd : xs.Nodup) (hxs : xs = as ++ u :: bs)
    (h : xs.filter (fun v => decide (v = u ∨ v ∈ us)) = u :: us)
    (hzs : ∀ z ∈ zs, ∀ w ∈ us, z = w → z = u ∨ z ∈ as) :
    (zs ++ bs).filter (fun v => decide (v ∈ us)) = us := by
  have hdist : (u :: us).Nodup := by
    have h1 := hd.filter (fun v => decide (v = u ∨ v ∈ us))
    rw [h] at h1
    exact h1
  apply filter_distinct_at3 hd hxs h
  intro z hz
  by_cases hzu : z ∈ us
  · rcases hzs z hz z hzu rfl with h2 | h2
    · exact absurd (h2 ▸ hzu) (List.nodup_cons.mp hdist).1
    · exact Or.inl h2
  · exact Or.inr hzu

/-- FaceDivisionProps.thy: filter_distinct_at5 -/
theorem filter_distinct_at5 {xs as bs us zs : List α} {u : α} [DecidableEq α]
    (hd : xs.Nodup) (hxs : xs = as ++ u :: bs)
    (h : xs.filter (fun v => decide (v = u ∨ v ∈ us)) = u :: us)
    (hzs : ∀ z ∈ zs, z ∈ xs → z = u ∨ z ∈ as) :
    (zs ++ bs).filter (fun v => decide (v ∈ us)) = us := by
  apply filter_distinct_at4 hd hxs h
  intro z hz w hw hzw
  subst hzw
  apply hzs z hz
  have hw' : z ∈ xs.filter (fun v => decide (v = u ∨ v ∈ us)) := by
    rw [h]; exact List.mem_cons_of_mem _ hw
  exact List.mem_of_mem_filter hw'

/-- FaceDivisionProps.thy: filter_distinct_at6 -/
theorem filter_distinct_at6 {xs as bs us zs : List α} {u : α} [DecidableEq α]
    (hd : xs.Nodup) (hxs : xs = as ++ u :: bs)
    (h : xs.filter (fun v => decide (v = u ∨ v ∈ us)) = u :: us)
    (hzs : ∀ z ∈ zs, z ∈ xs → z = u ∨ z ∈ as) :
    (zs ++ bs).filter (fun v => decide (v ∈ us)) = us ∧
      bs.filter (fun v => decide (v ∈ us)) = us :=
  ⟨filter_distinct_at5 hd hxs h hzs, (filter_distinct_at hd hxs h).1⟩

/-- FaceDivisionProps.thy: filter_distinct_at_special -/
theorem filter_distinct_at_special {xs as bs us zs : List α} {u hd_us : α}
    {tl_us : List α} [DecidableEq α]
    (hd : xs.Nodup) (hxs : xs = as ++ u :: bs)
    (h : xs.filter (fun v => decide (v = u ∨ v ∈ us)) = u :: us)
    (hzs : ∀ z ∈ zs, z ∈ xs → z = u ∨ z ∈ as)
    (hus : us = hd_us :: tl_us) :
    (zs ++ bs).filter (fun v => decide (v ∈ us)) = us ∧ hd_us ∈ bs := by
  obtain ⟨h1, h2⟩ := filter_distinct_at6 hd hxs h hzs
  refine ⟨h1, ?_⟩
  have hmem : hd_us ∈ bs.filter (fun v => decide (v ∈ us)) := by
    rw [h2, hus]
    simp
  exact List.mem_of_mem_filter hmem

/-- FaceDivisionProps.thy: before_filter -/
theorem before_filter {xs ys : List α} {u v : α} {P : α → Prop}
    [BEq α] [LawfulBEq α] [DecidablePred P]
    (hfilter : xs.filter (fun x => decide (P x)) = ys) (hd : xs.Nodup)
    (hb : before ys u v) : before xs u v := by
  have hu : u ∈ ys := before_r1 hb
  have hv : v ∈ ys := before_r2 hb
  have huf : u ∈ xs.filter (fun x => decide (P x)) := by rw [hfilter]; exact hu
  have hvf : v ∈ xs.filter (fun x => decide (P x)) := by rw [hfilter]; exact hv
  have huxs : u ∈ xs := List.mem_of_mem_filter huf
  have hvxs : v ∈ xs := List.mem_of_mem_filter hvf
  have hdys : ys.Nodup := by rw [← hfilter]; exact hd.filter _
  have hne : u ≠ v := by
    intro e
    subst e
    exact before_dist_not1 hdys hb hb
  by_contra hnb
  have hb2 : before xs v u := (before_xor ⟨hd, huxs, hvxs, hne⟩).mp hnb
  obtain ⟨a, b, c, hdec⟩ := hb2
  have hPu : P u := of_decide_eq_true (List.mem_filter.mp huf).2
  have hPv : P v := of_decide_eq_true (List.mem_filter.mp hvf).2
  have key : xs.filter (fun x => decide (P x)) =
      (a.filter (fun x => decide (P x)) ++ v :: b.filter (fun x => decide (P x))) ++
        u :: c.filter (fun x => decide (P x)) := by
    rw [hdec, List.filter_append, List.filter_append]
    simp [hPu, hPv]
  have hb3 : before ys v u := ⟨a.filter _, b.filter _, c.filter _, hfilter ▸ key⟩
  exact (before_dist_not1 hdys hb) hb3

/-- FaceDivisionProps.thy: pre_subdivFace'_Some2 -/
theorem pre_subdivFace'_Some2 {g : Graph} {f : Face} {v' v u : Vertex}
    {vol : List (Option Vertex)} (h : pre_subdivFace' g f v' v 0 (some u :: vol)) :
    pre_subdivFace' g f v' u 0 vol := by
  obtain ⟨hfin, hv', hram, hvnin, hdist, hbig⟩ := h
  rcases hbig with ⟨hfilter, hbefore, hlast, -, -, hinv, -⟩ | ⟨hcontra, -⟩
  swap
  · exact absurd hcontra (List.cons_ne_nil _ _)
  by_cases hvolnil : vol = []
  · subst hvolnil
    have hne : v' ≠ u := by
      have hvnin' : v' ∉ [u] := by
        rw [removeNones_hd] at hvnin; exact hvnin
      intro e; subst e; exact hvnin' List.mem_cons_self
    have hu : u ∈ f.vertices := by
      by_cases huv : u = v'
      · subst huv; exact hv'
      · apply verticesFrom_in' _ huv
        have h1 : (some u :: ([] : List (Option Vertex))).getLast! = some u := rfl
        rw [h1] at hlast
        have h2 : u = (verticesFrom f v').getLast! := Option.some.inj hlast
        rw [h2]
        exact getLast!_mem (fun e =>
          (List.ne_nil_of_mem hv') ((verticesFrom_empty hv').mp e))
    exact ⟨hfin, hv', hu, by simp, hdist, Or.inr ⟨rfl, hne⟩⟩
  · have hgl : (some u :: vol).getLast! = vol.getLast! := getLast!_cons_of_ne_nil hvolnil
    have hne : v' ≠ u := by
      have hvnin' : v' ∉ u :: removeNones vol := by
        rw [removeNones_hd] at hvnin; exact hvnin
      intro e; subst e; exact hvnin' List.mem_cons_self
    have huv : u ≠ v' := fun e => hne e.symm
    have hu : u ∈ f.vertices := verticesFrom_in' (before_r2 hbefore) huv
    have hfilter' : (verticesFrom f v').filter (fun w => decide (w ∈ removeNones vol)) =
        removeNones vol :=
      ovl_shorten (verticesFrom_distinct hdist hv') hfilter
    have r2 : removeNones vol ≠ [] := by
      intro hr
      have hall : ∀ x ∈ vol, x = none := by
        intro x hx
        cases x with
        | none => rfl
        | some a => exact absurd (hr ▸ removeNones_inI hx) List.not_mem_nil
      have hnone : vol.getLast! = none := hall _ (getLast!_mem hvolnil)
      rw [hgl, hnone] at hlast
      simp at hlast
    have hb3 : before (u :: removeNones vol) u (removeNones vol).head! := by
      refine ⟨[], [], (removeNones vol).tail, ?_⟩
      show u :: removeNones vol =
        ([] ++ u :: []) ++ (removeNones vol).head! :: (removeNones vol).tail
      rw [show u :: removeNones vol =
        u :: ((removeNones vol).head! :: (removeNones vol).tail)
        from congrArg (u :: ·) (List.cons_head!_tail r2).symm]
      rfl
    have hbefore' : before (verticesFrom f v') u (removeNones vol).head! :=
      before_filter hfilter (verticesFrom_distinct hdist hv') hb3
    refine ⟨hfin, hv', hu, ?_, hdist, Or.inl ⟨hfilter', hbefore', ?_, hvolnil,
      Or.inr (Or.inr hne), fun hbad => hinv (invalidVertexList_shorten hbad), ?_⟩⟩
    · rw [removeNones_hd] at hvnin
      exact fun hm => hvnin (List.mem_cons_of_mem _ hm)
    · rw [← hgl]; exact hlast
    · intro hpre
      obtain ⟨-, hhd⟩ := hpre
      cases hcase : vol.head! with
      | none => exact absurd hcase hhd
      | some y =>
        have h0 : 0 < (some u :: vol).length - 1 := by
          rw [List.length_cons]
          have := List.length_pos_iff.mpr hvolnil
          omega
        have h2 : ¬ is_duplicateEdge g f u y := by
          intro hdup
          apply hinv
          refine ⟨0, h0, ?_⟩
          rw [show (some u :: vol)[0]! = some u from rfl,
            show (some u :: vol)[0 + 1]! = vol.head! from List.head!_eq_getElem!.symm,
            hcase]
          exact hdup
        exact h2

/-- FaceDivisionProps.thy: pre_subdivFace'_preFaceDiv -/
theorem pre_subdivFace'_preFaceDiv {g : Graph} {f : Face} {v' v u : Vertex} {n : Nat}
    {vol : List (Option Vertex)}
    (h : pre_subdivFace' g f v' v n (some u :: vol)) (hf : f ∈ g.faces)
    (hnext : f.nextVertex v = u → n ≠ 0) (hsubset : ∀ x ∈ f.vertices, x ∈ g.vertices) :
    pre_splitFace g v u f (List.range' g.countVertices n) := by
  obtain ⟨hfin, hv', hram, hvnin, hdist, hbig⟩ := h
  rcases hbig with ⟨hfilter, hbefore, hlast, -, hdisj, hinv, himp⟩ | ⟨hcontra, -⟩
  swap
  · exact absurd hcontra (List.cons_ne_nil _ _)
  have hvnin' : v' ∉ u :: removeNones vol := by
    rw [removeNones_hd] at hvnin; exact hvnin
  have huv : u ≠ v' := by
    intro e; subst e; exact hvnin' List.mem_cons_self
  have hu : u ∈ f.vertices := verticesFrom_in' (before_r2 hbefore) huv
  have hne : v ≠ u := by
    intro e; subst e
    exact before_dist_not1 (verticesFrom_distinct hdist hv') hbefore hbefore
  have hgnin : ∀ x ∈ g.vertices, x ∉ List.range' g.countVertices n := by
    intro x hx
    have hx2 : x ∈ List.range g.countVertices := hx
    have hx' : x < g.countVertices := List.mem_range.mp hx2
    intro hbad
    rw [List.mem_range'_1] at hbad
    exact (Nat.not_le.mpr hx') hbad.1
  have hfnin : ∀ x ∈ f.vertices, x ∉ List.range' g.countVertices n :=
    fun x hx => hgnin x (hsubset x hx)
  have help2 : before (verticesFrom f v') v u → v ≠ v' →
      ¬ is_nextElem (verticesFrom f v') u v := by
    intro hb hvv' hne2
    have hdv : (verticesFrom f v').Nodup := verticesFrom_distinct hdist hv'
    rcases hne2 with hsub | ⟨-, -, hv⟩
    · obtain ⟨as, bs, hsub2⟩ := hsub
      obtain ⟨a, b, c, hdec⟩ := hb
      have e1 : verticesFrom f v' = (as ++ [u]) ++ v :: bs := by
        rw [hsub2]; simp [List.append_assoc]
      have e2 : verticesFrom f v' = a ++ v :: (b ++ u :: c) := by
        rw [hdec]; simp [List.append_assoc]
      have hau : as ++ [u] = a := dist_at1 hdv e1 e2
      have humem1 : u ∈ a := by
        rw [← hau]
        exact List.mem_append_right _ (List.mem_singleton_self u)
      have humem2 : u ∈ v :: (b ++ u :: c) :=
        List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
      have hdis := (List.nodup_append.mp (e2 ▸ hdv)).2.2
      exact hdis u humem1 u humem2 rfl
    · exact hvv' (hv.trans (verticesFrom_hd f v'))
  refine ⟨hf, hfin, hdist, List.nodup_range', hgnin, hfnin, hram, hu, hne, ?_⟩
  by_cases hn : 0 < n
  · refine Or.inr (fun e => ?_)
    have h1 := congrArg List.length e
    rw [List.length_range', List.length_nil] at h1
    omega
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have h1 : (v, u) ∉ f.edges := by
      intro he
      rw [is_nextElem_edges_eq hdist] at he
      have hne1 : f.nextVertex v = u := (nextElem_is_nextElem hdist hram).mp he
      exact hnext hne1 hn0
    have h2 : (u, v) ∉ f.edges := by
      intro he
      rw [is_nextElem_edges_eq hdist] at he
      have he' : is_nextElem (verticesFrom f v') u v := (verticesFrom_is_nextElem hv').mp he
      by_cases hvv' : v = v'
      · subst v
        rcases hdisj with ⟨-, h0⟩ | ⟨-, hhd⟩ | hne'
        · omega
        · have hu2 : u = (verticesFrom f v').getLast! :=
            verticesFrom_is_nextElem_hd hv' hdist he'
          rw [show (some u :: vol).head! = some u from rfl, ← hu2] at hhd
          exact hhd rfl
        · exact absurd rfl hne'
      · exact help2 hbefore hvv' he'
    have hdup : ¬ is_duplicateEdge g f v u := himp ⟨hn0, by simp⟩
    exact Or.inl ⟨h1, h2, fun he => hdup (Or.inl ⟨he, h1, h2⟩),
      fun he => hdup (Or.inr ⟨he, h2, h1⟩)⟩

/-- Auxiliary: `getLast!` of an append with nonempty right part. -/
theorem getLast!_append_of_ne_nil [Inhabited α] {l₁ l₂ : List α} (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast! = l₂.getLast! := by
  induction l₁ with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, getLast!_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil xs h)]
    exact ih

/-- Shared leaf of the `rule5`/`rule6` steps of FaceDivisionProps.thy
`pre_subdivFace'_Some1'`: an edge of `g'` that is not an edge of `g` cannot
have both orientations missing from `f21`. -/
private theorem splitFace_new_edge_in_f21
    {g g' : Graph} {f f12 f21 : Face} {v u x y : Vertex} {ws : List Vertex}
    (pre_fdg : pre_splitFace g v u f ws)
    (hsplit : (f12, f21, g') = splitFace g v u f ws)
    (hg' : (x, y) ∈ g'.edges) (hgN : (x, y) ∉ g.edges)
    (hf21a : (x, y) ∉ f21.edges) (hf21b : (y, x) ∉ f21.edges) :
    False := by
  have pre_split : pre_split_face f v u ws := pre_splitFace_pre_split_face pre_fdg
  have e1 : (splitFace g v u f ws).1 = (split_face f v u ws).1 := rfl
  have e2 : (splitFace g v u f ws).2.1 = (split_face f v u ws).2 := rfl
  have split : (f12, f21) = split_face f v u ws :=
    Prod.ext ((congrArg Prod.fst hsplit).trans e1)
      ((congrArg (fun p => p.2.1) hsplit).trans e2)
  by_cases hws : ws = []
  · have edges_g'2 : g'.edges = g.edges ∪ {(v, u), (u, v)} :=
      splitFace_edges_g'_vs (hws ▸ pre_fdg) (hws ▸ hsplit)
    rw [edges_g'2] at hg'
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
    have hvf21 : (v, u) ∈ f21.edges := by
      by_cases hbet : between f.vertices u v = []
      · rw [split_face_edges_f21_bet_vs (hws ▸ pre_split) (hws ▸ split) hbet]
        simp
      · rw [split_face_edges_f21_vs (hws ▸ pre_split) (hws ▸ split) rfl hbet]
        simp
    rcases hg' with hg | hg | hg
    · exact absurd hg hgN
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
      exact hf21a hvf21
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
      exact hf21b hvf21
  · have edges_g'1 := splitFace_edges_g' pre_fdg hsplit hws
    rw [edges_g'1] at hg'
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
    by_cases hbet : between f.vertices u v = []
    · have hf21e : f21.edges = {(v, ws.head!), (ws.getLast!, u), (u, v)} ∪ Edges ws :=
        split_face_edges_f21_bet pre_split split hws hbet
      have m1 : (v, ws.head!) ∈ f21.edges := by
        rw [hf21e]; simp
      have m2 : (ws.getLast!, u) ∈ f21.edges := by
        rw [hf21e]; simp
      rcases hg' with ((hg | hg) | hg) | (hg | hg | hg)
      · exact absurd hg hgN
      · exact hf21a (by rw [hf21e]; simp only [Set.mem_union]; exact Or.inr hg)
      · rw [in_Edges_rev] at hg
        exact hf21b (by rw [hf21e]; simp only [Set.mem_union]; exact Or.inr hg)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
        exact hf21b m2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
        exact hf21b m1
      · rcases hg with hg | hg
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
          exact hf21a m1
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
          exact hf21a m2
    · have hf21e : f21.edges =
          {((between f.vertices u v).getLast!, v), (v, ws.head!), (ws.getLast!, u),
            (u, (between f.vertices u v).head!)} ∪ Edges ws ∪
            Edges (between f.vertices u v) :=
        split_face_edges_f21 pre_split split hws rfl hbet
      have m1 : (v, ws.head!) ∈ f21.edges := by
        rw [hf21e]; simp
      have m2 : (ws.getLast!, u) ∈ f21.edges := by
        rw [hf21e]; simp
      rcases hg' with ((hg | hg) | hg) | (hg | hg | hg)
      · exact absurd hg hgN
      · exact hf21a (by
          rw [hf21e]
          simp only [Set.mem_union]
          exact Or.inl (Or.inr hg))
      · rw [in_Edges_rev] at hg
        exact hf21b (by
          rw [hf21e]
          simp only [Set.mem_union]
          exact Or.inl (Or.inr hg))
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
        exact hf21b m2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
        exact hf21b m1
      · rcases hg with hg | hg
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
          exact hf21a m1
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
          exact hf21a m2

/-- The `rule5` step of FaceDivisionProps.thy `pre_subdivFace'_Some1'`:
`invalidVertexList` transfers to the subdivided graph. -/
private theorem invalidVertexList_splitFace_transfer
    {g g' : Graph} {f f12 f21 : Face} {v u : Vertex} {ws : List Vertex}
    {vol : List (Option Vertex)}
    (pre_fdg : pre_splitFace g v u f ws)
    (hsplit : (f12, f21, g') = splitFace g v u f ws)
    (hmem : ∀ x ∈ removeNones vol, x ∉ f12.vertices)
    (hinv : ¬ invalidVertexList g f vol) :
    ¬ invalidVertexList g' f21 vol := by
  have pre_split : pre_split_face f v u ws := pre_splitFace_pre_split_face pre_fdg
  have e1 : (splitFace g v u f ws).1 = (split_face f v u ws).1 := rfl
  have e2 : (splitFace g v u f ws).2.1 = (split_face f v u ws).2 := rfl
  have split : (f12, f21) = split_face f v u ws :=
    Prod.ext ((congrArg Prod.fst hsplit).trans e1)
      ((congrArg (fun p => p.2.1) hsplit).trans e2)
  have hmem1 : ∀ x y, x ∈ removeNones vol → (x, y) ∉ f12.edges :=
    fun x y hx he => hmem x hx he.1
  intro hbad
  obtain ⟨i, hi, hcase⟩ := hbad
  have hcasef : (match vol[i]! with | none => False | some a => match vol[i + 1]! with
      | none => False | some b => is_duplicateEdge g f a b) → False :=
    fun h => hinv ⟨i, hi, h⟩
  cases h0 : vol[i]! with
  | none => rw [h0] at hcase; exact hcase
  | some a =>
    cases h1 : vol[i + 1]! with
    | none => rw [h0, h1] at hcase; exact hcase
    | some aa =>
      rw [h0, h1] at hcase hcasef
      have hilt : i < vol.length := by omega
      have hi1lt : i + 1 < vol.length := by omega
      have h0mem : vol[i]! ∈ vol :=
        List.take_subset _ _ (by
          rw [take_succ_eq_append_getElem! hilt]
          exact List.mem_append_right _ (List.mem_singleton_self _))
      have h1mem : vol[i + 1]! ∈ vol :=
        List.take_subset _ _ (by
          rw [take_succ_eq_append_getElem! hi1lt]
          exact List.mem_append_right _ (List.mem_singleton_self _))
      have ha : a ∈ removeNones vol := removeNones_inI (h0 ▸ h0mem)
      have haa : aa ∈ removeNones vol := removeNones_inI (h1 ▸ h1mem)
      obtain ⟨hf21a, hf21b⟩ : (a, aa) ∉ f21.edges ∧ (aa, a) ∉ f21.edges := by
        rcases hcase with ⟨-, h1, h2⟩ | ⟨-, h2, h1⟩
        · exact ⟨h1, h2⟩
        · exact ⟨h1, h2⟩
      have hf1 : (a, aa) ∉ f.edges := fun hf =>
        (split_face_edges_or split pre_split hf).elim (hmem1 a aa ha) hf21a
      have hf2 : (aa, a) ∉ f.edges := fun hf =>
        (split_face_edges_or split pre_split hf).elim (hmem1 aa a haa) hf21b
      have hgN1 : (a, aa) ∉ g.edges := fun hg => hcasef (Or.inl ⟨hg, hf1, hf2⟩)
      have hgN2 : (aa, a) ∉ g.edges := fun hg => hcasef (Or.inr ⟨hg, hf2, hf1⟩)
      rcases hcase with ⟨hg', -, -⟩ | ⟨hg', -, -⟩
      · exact splitFace_new_edge_in_f21 pre_fdg hsplit hg' hgN1 hf21a hf21b
      · exact splitFace_new_edge_in_f21 pre_fdg hsplit hg' hgN2 hf21b hf21a

/-- The `rule6` step of FaceDivisionProps.thy `pre_subdivFace'_Some1'`. -/
private theorem not_is_duplicateEdge_splitFace
    {g g' : Graph} {f f12 f21 : Face} {v u : Vertex} {ws : List Vertex}
    {vol : List (Option Vertex)}
    (pre_fdg : pre_splitFace g v u f ws)
    (hsplit : (f12, f21, g') = splitFace g v u f ws)
    (hmem : ∀ x ∈ removeNones vol, x ∉ f12.vertices)
    (hvol : 0 < vol.length)
    (hinv : ¬ invalidVertexList g f (some u :: vol))
    (hy : vol.head! ≠ none) :
    ¬ is_duplicateEdge g' f21 u vol.head!.get! := by
  obtain ⟨y, hy'⟩ : ∃ y, vol.head! = some y := by
    cases h : vol.head! with
    | none => exact absurd h hy
    | some y => exact ⟨y, rfl⟩
  have hget : vol.head!.get! = y := by rw [hy']; rfl
  rw [hget]
  have pre_split : pre_split_face f v u ws := pre_splitFace_pre_split_face pre_fdg
  have e1 : (splitFace g v u f ws).1 = (split_face f v u ws).1 := rfl
  have e2 : (splitFace g v u f ws).2.1 = (split_face f v u ws).2 := rfl
  have split : (f12, f21) = split_face f v u ws :=
    Prod.ext ((congrArg Prod.fst hsplit).trans e1)
      ((congrArg (fun p => p.2.1) hsplit).trans e2)
  have hcasef : ¬ is_duplicateEdge g f u y := by
    intro hdup
    apply hinv
    refine ⟨0, by rw [List.length_cons]; omega, ?_⟩
    rw [show (some u :: vol)[0]! = some u from rfl,
      show (some u :: vol)[0 + 1]! = vol.head! from List.head!_eq_getElem!.symm, hy']
    exact hdup
  have hvne : vol ≠ [] := List.ne_nil_of_length_pos hvol
  have hymem : y ∈ removeNones vol := by
    apply removeNones_inI
    have h1 : vol = vol.head! :: vol.tail := (List.cons_head!_tail hvne).symm
    rw [hy'] at h1
    rw [h1]
    exact List.mem_cons_self
  intro hdup
  obtain ⟨hf21a, hf21b⟩ : (u, y) ∉ f21.edges ∧ (y, u) ∉ f21.edges := by
    rcases hdup with ⟨-, h1, h2⟩ | ⟨-, h2, h1⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1, h2⟩
  have hf1 : (u, y) ∉ f.edges := fun hf =>
    (split_face_edges_or split pre_split hf).elim
      (fun h12 => by
        have hx : u ∈ f12.vertices := h12.1
        have hy2 : f12.nextVertex u = y := h12.2
        exact hmem y hymem (hy2 ▸ nextVertex_in_face hx)) hf21a
  have hf2 : (y, u) ∉ f.edges := fun hf =>
    (split_face_edges_or split pre_split hf).elim
      (fun h12 => hmem y hymem h12.1) hf21b
  have hgN1 : (u, y) ∉ g.edges := fun hg => hcasef (Or.inl ⟨hg, hf1, hf2⟩)
  have hgN2 : (y, u) ∉ g.edges := fun hg => hcasef (Or.inr ⟨hg, hf2, hf1⟩)
  rcases hdup with ⟨hg', -, -⟩ | ⟨hg', -, -⟩
  · exact splitFace_new_edge_in_f21 pre_fdg hsplit hg' hgN1 hf21a hf21b
  · exact splitFace_new_edge_in_f21 pre_fdg hsplit hg' hgN2 hf21b hf21a


/-- FaceDivisionProps.thy: pre_subdivFace'_Some1' -/
theorem pre_subdivFace'_Some1' {g g' : Graph} {f f21 : Face} {v' v u : Vertex} {n : Nat}
    {vol : List (Option Vertex)} {ws : List Vertex}
    (pre_add : pre_subdivFace' g f v' v n (some u :: vol))
    (pre_fdg : pre_splitFace g v u f ws)
    (fdg : f21 = (splitFace g v u f ws).2.1)
    (hg' : g' = (splitFace g v u f ws).2.2) :
    pre_subdivFace' g' f21 v' u 0 vol := by
  obtain ⟨hfin, hv', hram, hvnin, hdist, hbig⟩ := pre_add
  rcases hbig with ⟨hfilter, hbefore, hlast, -, hdisj, hinv, himp⟩ | ⟨hcontra, -⟩
  swap
  · exact absurd hcontra (List.cons_ne_nil _ _)
  have hbefore' : before (verticesFrom f v') v u := by
    rw [removeNones_hd, List.head!_cons] at hbefore
    exact hbefore
  have hf21 : f21 = (split_face f v u ws).2 := fdg
  have hf21v : f21.vertices = ([u] ++ between f.vertices u v ++ [v]) ++ ws := by
    rw [hf21]
    rfl
  by_cases hvol : vol = []
  · subst hvol
    have hvnin' : v' ≠ u := by
      have h1 : v' ∉ u :: removeNones [] := hvnin
      intro e; subst e; exact h1 List.mem_cons_self
    refine ⟨?_, ?_, ?_, by simp, ?_, Or.inr ⟨rfl, hvnin'⟩⟩
    · rw [hf21]
      rfl
    · rw [hf21v]
      by_cases hvv' : v = v'
      · subst v'
        exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      · have hd2 : (verticesFrom f v').Nodup := verticesFrom_distinct hdist hv'
        have huf : u ∈ f.vertices :=
          (cong_mem (verticesFrom_congs hv')).mpr (before_r2 hbefore')
        have h1 : before (verticesFrom f u) v' v :=
          rotate_before_vFrom hdist hv' (Ne.symm hvv') hbefore'
        have h2 : v' ∈ between f.vertices u v :=
          before_between h1 hdist huf (fun e => hvnin' e.symm)
        exact List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ h2))
    · rw [hf21v]
      exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
    · rw [fdg]
      exact splitFace_distinct1 pre_fdg
  · have hgl : (some u :: vol).getLast! = vol.getLast! := getLast!_cons_of_ne_nil hvol
    have r : removeNones vol ≠ [] := by
      intro hr
      have hall : ∀ x ∈ vol, x = none := by
        intro x hx
        cases x with
        | none => rfl
        | some a => exact absurd (hr ▸ removeNones_inI hx) List.not_mem_nil
      have hnone : vol.getLast! = none := hall _ (getLast!_mem hvol)
      rw [hgl, hnone] at hlast
      simp at hlast
    have removeNones_split := (List.cons_head!_tail r).symm
    have hcong := verticesFrom_congs hv'
    have hd2 : (verticesFrom f v').Nodup := verticesFrom_distinct hdist hv'
    have pre_bet' : pre_between (verticesFrom f v') u v := by
      refine ⟨hd2, before_r2 hbefore', before_r1 hbefore', ?_⟩
      intro e
      subst e
      exact before_dist_not1 hd2 hbefore' hbefore'
    have huf : u ∈ f.vertices := (cong_mem hcong).mpr (before_r2 hbefore')
    have pre_bet : pre_between f.vertices u v := ⟨hdist, huf, hram, pre_bet'.2.2.2⟩
    have bet_eq : between f.vertices u v = between (verticesFrom f v') u v :=
      verticesFrom_between hv' pre_bet
    have bet_eq2 : between f.vertices v u = between (verticesFrom f v') v u :=
      verticesFrom_between hv' (pre_between_symI pre_bet)
    have vert_f21 : f21.vertices =
        (u :: (splitAt u (verticesFrom f v')).2 ++ (splitAt v (verticesFrom f v')).1 ++
          [v]) ++ ws := by
      rw [hf21v, bet_eq, between_simp2 hbefore' (pre_between_symI pre_bet')]
      rfl
    have m_split : v' :: (verticesFrom f v').tail =
        (splitAt v (verticesFrom f v')).1 ++ v :: (splitAt v (verticesFrom f v')).2 :=
      verticesFrom_split.trans (splitAt_ram (before_r1 hbefore'))
    have vv' : v ≠ v' → (splitAt v (verticesFrom f v')).1 =
        v' :: (splitAt v (verticesFrom f v')).1.tail := by
      intro hne
      cases hfs : (splitAt v (verticesFrom f v')).1 with
      | nil =>
        rw [hfs, List.nil_append] at m_split
        exact absurd (List.cons.inj m_split).1.symm hne
      | cons x xs =>
        rw [hfs, show (x :: xs) ++ v :: (splitAt v (verticesFrom f v')).2 =
            x :: (xs ++ v :: (splitAt v (verticesFrom f v')).2) from rfl] at m_split
        obtain ⟨hx, -⟩ := List.cons.inj m_split
        exact (congrArg (fun z => z :: xs) hx).symm
    have rule2 : v' ∈ f21.vertices := by
      by_cases hvv' : v = v'
      · subst v'
        rw [vert_f21, verticesFrom_splitAt_v_fst hd2]
        simp
      · rw [vert_f21, vv' hvv']
        simp
    have dist_f21 : f21.vertices.Nodup := by
      rw [fdg]
      exact splitFace_distinct1 pre_fdg
    have dist_f21_v' : (verticesFrom f21 v').Nodup := verticesFrom_distinct dist_f21 rule2
    have m1 : v ≠ v' → verticesFrom f21 v' =
        (v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws) ++
          u :: (splitAt u (verticesFrom f v')).2 := by
      intro hvv'
      apply verticesFrom_v dist_f21
      rw [vert_f21, vv' hvv']
      simp [List.append_assoc]
    have m2 : v = v' → verticesFrom f21 v' =
        (v' :: ws) ++ u :: (splitAt u (verticesFrom f v')).2 := by
      intro hvv'
      subst v'
      apply verticesFrom_v dist_f21
      rw [vert_f21, verticesFrom_splitAt_v_fst hd2]
      simp [List.append_assoc]
    have umem : u ∈ verticesFrom f v' := before_r2 hbefore'
    have split_u : verticesFrom f v' =
        (splitAt u (verticesFrom f v')).1 ++ u :: (splitAt u (verticesFrom f v')).2 :=
      splitAt_ram umem
    have hfilter' : (verticesFrom f v').filter
        (fun w => decide (w = u ∨ w ∈ removeNones vol)) = u :: removeNones vol := by
      have e : (fun w => decide (w ∈ removeNones (some u :: vol))) =
          (fun w => decide (w = u ∨ w ∈ removeNones vol)) := by
        funext w
        simp only [show removeNones (some u :: vol) = u :: removeNones vol from rfl,
          List.mem_cons]
      rw [e] at hfilter
      exact hfilter
    have rule1' : ((splitAt u (verticesFrom f v')).2).filter
        (fun w => decide (w ∈ removeNones vol)) = removeNones vol :=
      filter_distinct_at5 hd2 split_u hfilter' (fun z hz => absurd hz List.not_mem_nil)
    have inSnd_u : ∀ x ∈ removeNones vol, x ∈ (splitAt u (verticesFrom f v')).2 := by
      intro x hx
      have h1 : x ∈ ((splitAt u (verticesFrom f v')).2).filter
          (fun w => decide (w ∈ removeNones vol)) := by
        rw [rule1']; exact hx
      exact List.mem_of_mem_filter h1
    have notinFst_u : ∀ x ∈ removeNones vol,
        x ∉ (splitAt u (verticesFrom f v')).1 ++ [u] := by
      intro x hx hbad
      have hxs := inSnd_u x hx
      rcases List.mem_append.mp hbad with hbad | hbad
      · exact splitAt_distinct_fst_snd hd2 _ hbad hxs
      · rw [List.mem_singleton.mp hbad] at hxs
        have hdis : (verticesFrom f v').Nodup := hd2
        rw [split_u] at hdis
        exact (List.nodup_cons.mp (List.nodup_append.mp hdis).2.1).1 hxs
    have nextElem_transfer : ∀ a b, is_nextElem f.vertices a b →
        a ∈ removeNones vol → b ∈ removeNones vol → is_nextElem f21.vertices a b := by
      intro a b hab ha hb
      have hab' : is_nextElem (verticesFrom f v') a b := (verticesFrom_is_nextElem hv').mp hab
      have ha2 : a ∈ (splitAt u (verticesFrom f v')).2 := inSnd_u a ha
      have hb2 : b ∈ (splitAt u (verticesFrom f v')).2 := inSnd_u b hb
      have hvnin_vol : v' ∉ removeNones vol := fun hm => by
        have h1 : v' ∉ u :: removeNones vol := hvnin
        exact h1 (List.mem_cons_of_mem _ hm)
      have hsub : is_sublist [a, b] (splitAt u (verticesFrom f v')).2 := by
        rcases hab' with hsub | ⟨-, -, hb'⟩
        swap
        · exfalso
          have hbv' : b = v' := hb'.trans (verticesFrom_hd f v')
          exact hvnin_vol (hbv' ▸ hb)
        · rw [split_u] at hsub
          have e : ((splitAt u (verticesFrom f v')).1 ++ [u]) ++
              (splitAt u (verticesFrom f v')).2 =
              (splitAt u (verticesFrom f v')).1 ++ u :: (splitAt u (verticesFrom f v')).2 := by
            simp [List.append_assoc]
          have hsub2 : is_sublist [a, b]
              (((splitAt u (verticesFrom f v')).1 ++ [u]) ++
                (splitAt u (verticesFrom f v')).2) := by
            rwa [← e] at hsub
          have hd3 : (((splitAt u (verticesFrom f v')).1 ++ [u]) ++
              (splitAt u (verticesFrom f v')).2).Nodup := by
            rw [e]
            exact split_u ▸ hd2
          rcases is_sublist_at5 hd3 hsub2 with h1 | h1 | ⟨h1, -⟩
          · have hd4 : ((splitAt u (verticesFrom f v')).1 ++ [u]).Nodup :=
              (List.nodup_append.mp hd3).1
            rcases is_sublist_at5 hd4 h1 with h11 | h11 | ⟨-, h12⟩
            · exact (splitAt_distinct_fst_snd hd2 _ (is_sublist_in1 h11) hb2).elim
            · exfalso
              have hb5 : b = u := by
                have h2 := is_sublist_in1 h11
                rwa [List.mem_singleton] at h2
              rw [hb5] at hb2
              have hdis : (verticesFrom f v').Nodup := hd2
              rw [split_u] at hdis
              exact (List.nodup_cons.mp (List.nodup_append.mp hdis).2.1).1 hb2
            · exfalso
              have hbu : b = u := h12
              rw [hbu] at hb2
              have hdis : (verticesFrom f v').Nodup := hd2
              rw [split_u] at hdis
              exact (List.nodup_cons.mp (List.nodup_append.mp hdis).2.1).1 hb2
          · exact h1
          · exfalso
            have hau : a = u := by
              rwa [getLast!_concat] at h1
            rw [hau] at ha2
            have hdis : (verticesFrom f v').Nodup := hd2
            rw [split_u] at hdis
            exact (List.nodup_cons.mp (List.nodup_append.mp hdis).2.1).1 ha2
      have hsub21 : is_sublist [a, b] (verticesFrom f21 v') := by
        by_cases hvv' : v = v'
        · rw [m2 hvv']
          have e : ((v' :: ws) ++ u :: (splitAt u (verticesFrom f v')).2) =
              ((v' :: ws) ++ [u]) ++ (splitAt u (verticesFrom f v')).2 ++ [] := by
            simp [List.append_assoc]
          rw [e]
          exact is_sublist_add hsub
        · rw [m1 hvv']
          have e : ((v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws) ++
              u :: (splitAt u (verticesFrom f v')).2) =
              ((v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws) ++ [u]) ++
                (splitAt u (verticesFrom f v')).2 ++ [] := by
            simp [List.append_assoc]
          rw [e]
          exact is_sublist_add hsub
      exact (verticesFrom_is_nextElem rule2).mpr (Or.inl hsub21)
    have hv'fst_aux : u ≠ v' → v' ∈ (splitAt u (verticesFrom f v')).1 := by
      intro huv'
      have m' : v' :: (verticesFrom f v').tail =
          (splitAt u (verticesFrom f v')).1 ++ u :: (splitAt u (verticesFrom f v')).2 :=
        verticesFrom_split.trans split_u
      cases hfs : (splitAt u (verticesFrom f v')).1 with
      | nil =>
        rw [hfs, List.nil_append] at m'
        exact absurd (List.cons.inj m').1 (Ne.symm huv')
      | cons x xs =>
        rw [hfs, show (x :: xs) ++ u :: (splitAt u (verticesFrom f v')).2 =
            x :: (xs ++ u :: (splitAt u (verticesFrom f v')).2) from rfl] at m'
        obtain ⟨hx, -⟩ := List.cons.inj m'
        rw [hx]
        exact List.mem_cons_self
    have rule1 : (verticesFrom f21 v').filter (fun w => decide (w ∈ removeNones vol)) =
        removeNones vol ∧
        (removeNones vol).head! ∈ (splitAt u (verticesFrom f v')).2 := by
      by_cases hvv' : v = v'
      · have hv'fst : v' ∈ (splitAt u (verticesFrom f v')).1 :=
          hv'fst_aux (fun h => pre_bet'.2.2.2 (h.trans hvv'.symm))
        have help : ∀ z ∈ (v' :: ws ++ [u]), z ∈ verticesFrom f v' →
            z = u ∨ z ∈ (splitAt u (verticesFrom f v')).1 := by
          intro z hz hzvf
          rcases List.mem_cons.mp hz with rfl | hz
          · exact Or.inr hv'fst
          · rcases List.mem_append.mp hz with hz | hz
            · exact absurd hz (pre_fdg.2.2.2.2.2.1 z ((cong_mem hcong).mpr hzvf))
            · exact Or.inl (List.mem_singleton.mp hz)
        have hspec := filter_distinct_at_special hd2 split_u hfilter' help removeNones_split
        have e : ((v' :: ws) ++ u :: (splitAt u (verticesFrom f v')).2) =
            ((v' :: ws ++ [u]) ++ (splitAt u (verticesFrom f v')).2) := by
          simp [List.append_assoc]
        refine ⟨?_, hspec.2⟩
        rw [m2 hvv', e]
        exact hspec.1
      · have ne_uv' : u ≠ v' := by
          intro huv'
          have h1 := m1 hvv'
          rw [huv'] at h1
          have hdis : (verticesFrom f21 v').Nodup := dist_f21_v'
          rw [h1] at hdis
          exact (List.nodup_append.mp hdis).2.2 v' List.mem_cons_self v' List.mem_cons_self rfl
        have hv'fst : v' ∈ (splitAt u (verticesFrom f v')).1 := hv'fst_aux ne_uv'
        have hvfst : v ∈ (splitAt u (verticesFrom f v')).1 := before_dist_r1 hd2 hbefore'
        have hfst_ram := splitAt_ram hvfst
        have he_ram : (splitAt u (verticesFrom f v')).1 ++ u ::
            (splitAt u (verticesFrom f v')).2 =
            ((splitAt v (splitAt u (verticesFrom f v')).1).1 ++ v ::
              (splitAt v (splitAt u (verticesFrom f v')).1).2) ++ u ::
                (splitAt u (verticesFrom f v')).2 := by
          conv_lhs => rw [hfst_ram]
        have h2 : verticesFrom f v' =
            (splitAt v (splitAt u (verticesFrom f v')).1).1 ++ v ::
              ((splitAt v (splitAt u (verticesFrom f v')).1).2 ++ u ::
                (splitAt u (verticesFrom f v')).2) := by
          conv_lhs => rw [split_u, he_ram]
          simp [List.append_assoc]
        have hfst_v : (splitAt v (verticesFrom f v')).1 =
            (splitAt v (splitAt u (verticesFrom f v')).1).1 :=
          dist_at1 hd2 (splitAt_ram (before_r1 hbefore')) h2
        have hzA : ∀ z ∈ (splitAt v (verticesFrom f v')).1,
            z ∈ (splitAt u (verticesFrom f v')).1 := by
          intro z hz
          rw [hfst_v] at hz
          rw [hfst_ram]
          exact List.mem_append_left _ hz
        have help : ∀ z ∈ (v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws ++ [u]),
            z ∈ verticesFrom f v' → z = u ∨ z ∈ (splitAt u (verticesFrom f v')).1 := by
          intro z hz hzvf
          have hzs : (v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws ++ [u]) =
              (splitAt v (verticesFrom f v')).1 ++ v :: ws ++ [u] := by
            rw [← vv' hvv']
          rw [hzs] at hz
          rcases List.mem_append.mp hz with hz | hz
          · rcases List.mem_append.mp hz with hz | hz
            · exact Or.inr (hzA z hz)
            · rcases List.mem_cons.mp hz with rfl | hz
              · exact Or.inr hvfst
              · exact absurd hz (pre_fdg.2.2.2.2.2.1 z ((cong_mem hcong).mpr hzvf))
          · exact Or.inl (List.mem_singleton.mp hz)
        have hspec := filter_distinct_at_special hd2 split_u hfilter' help removeNones_split
        have e : ((v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws) ++
            u :: (splitAt u (verticesFrom f v')).2) =
            ((v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws ++ [u]) ++
              (splitAt u (verticesFrom f v')).2) := by
          simp [List.append_assoc]
        refine ⟨?_, hspec.2⟩
        rw [m1 hvv', e]
        exact hspec.1
    have rule3 : before (verticesFrom f21 v') u (removeNones vol).head! := by
      have hd_mem : (removeNones vol).head! ∈ (splitAt u (verticesFrom f v')).2 := rule1.2
      have hdecomp := splitAt_ram hd_mem
      by_cases hvv' : v = v'
      · rw [m2 hvv']
        refine ⟨v' :: ws,
          (splitAt (removeNones vol).head! (splitAt u (verticesFrom f v')).2).1,
          (splitAt (removeNones vol).head! (splitAt u (verticesFrom f v')).2).2, ?_⟩
        conv_lhs => rw [hdecomp]
        simp [List.append_assoc]
      · rw [m1 hvv']
        refine ⟨(v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws),
          (splitAt (removeNones vol).head! (splitAt u (verticesFrom f v')).2).1,
          (splitAt (removeNones vol).head! (splitAt u (verticesFrom f v')).2).2, ?_⟩
        conv_lhs => rw [hdecomp]
        simp [List.append_assoc]
    have rule4 : (verticesFrom f v').getLast! = (verticesFrom f21 v').getLast! := by
      have snd_ne : (splitAt u (verticesFrom f v')).2 ≠ [] :=
        List.ne_nil_of_mem rule1.2
      have e1 : (verticesFrom f v').getLast! =
          ((splitAt u (verticesFrom f v')).2).getLast! := by
        conv_lhs => rw [split_u]
        rw [getLast!_append_of_ne_nil (List.cons_ne_nil _ _)]
        exact getLast!_cons_of_ne_nil snd_ne
      have e2 : (verticesFrom f21 v').getLast! =
          ((splitAt u (verticesFrom f v')).2).getLast! := by
        by_cases hvv' : v = v'
        · rw [m2 hvv', getLast!_append_of_ne_nil (List.cons_ne_nil _ _)]
          exact getLast!_cons_of_ne_nil snd_ne
        · rw [m1 hvv', getLast!_append_of_ne_nil (List.cons_ne_nil _ _)]
          exact getLast!_cons_of_ne_nil snd_ne
      rw [e1, e2]
    -- the f12 side
    have hsplit : ( (splitFace g v u f ws).1, f21, g') = splitFace g v u f ws := by
      rw [fdg, hg']
    set f12 : Face := (splitFace g v u f ws).1 with hf12_def
    have hsplit' : (f12, f21, g') = splitFace g v u f ws := hsplit
    have hf12 : f12 = (split_face f v u ws).1 := rfl
    have hf12v : f12.vertices = ws.reverse ++ ([v] ++ between f.vertices v u ++ [u]) := by
      rw [hf12]
      rfl
    have hbefore2 := hbefore'
    obtain ⟨a, b, c, hdec⟩ := hbefore2
    have hall := splitAt_dist_ram_all hd2 hdec
    obtain ⟨hsp1, hsp2, hsp3, hsp4, hsp5, hsp6⟩ := hall
    have hbetween : between (verticesFrom f v') v u = b :=
      (between_simp1 hbefore' (pre_between_symI pre_bet')).trans (congrArg Prod.fst hsp4).symm
    have hfst_u_eq : a ++ v :: b = (splitAt u (verticesFrom f v')).1 :=
      dist_at1 hd2 hdec (splitAt_ram umem)
    have hsnd_v_fst_u : (splitAt v ((splitAt u (verticesFrom f v')).1)).2 = b :=
      splitAt_snd (splitAt_distinct_fst hd2) hfst_u_eq.symm
    have vert_f12 : f12.vertices =
        ws.reverse ++ ([v] ++ (splitAt v ((splitAt u (verticesFrom f v')).1)).2 ++ [u]) := by
      rw [hf12v, bet_eq2, hbetween, ← hsnd_v_fst_u]
    have removeNones_vol_not_f12 : ∀ x ∈ removeNones vol, x ∉ f12.vertices := by
      intro x hx hxf12
      have hxs := inSnd_u x hx
      have hxf := notinFst_u x hx
      rw [vert_f12] at hxf12
      rcases List.mem_append.mp hxf12 with hxf12 | hxf12
      swap
      · -- x ∈ ([v] ++ b') ++ [u]
        rcases List.mem_append.mp hxf12 with hxf12 | hxf12
        · -- x ∈ [v] ++ b'
          rcases List.mem_append.mp hxf12 with hxf12 | hxf12
          · obtain rfl := List.mem_singleton.mp hxf12
            exact hxf (List.mem_append_left _ (before_dist_r1 hd2 hbefore'))
          · exact hxf (List.mem_append_left _ (splitAt_in_snd hxf12))
        · obtain rfl := List.mem_singleton.mp hxf12
          exact hxf (List.mem_append_right _ List.mem_cons_self)
      · -- x ∈ ws.reverse
        rw [List.mem_reverse] at hxf12
        have hdisv : (verticesFrom f21 v').Nodup := dist_f21_v'
        by_cases hvv' : v = v'
        · rw [m2 hvv'] at hdisv
          obtain ⟨hd1, -, hdisj⟩ := List.nodup_append.mp hdisv
          exact hdisj x (List.mem_cons_of_mem _ hxf12) x
            (List.mem_cons_of_mem _ hxs) rfl
        · rw [m1 hvv'] at hdisv
          obtain ⟨hd1, -, hdisj⟩ := List.nodup_append.mp hdisv
          have hx1 : x ∈ v' :: (splitAt v (verticesFrom f v')).1.tail ++ v :: ws :=
            List.mem_cons_of_mem _
              (List.mem_append_right _ (List.mem_cons_of_mem _ hxf12))
          exact hdisj x hx1 x (List.mem_cons_of_mem _ hxs) rfl
    have hinv' : ¬ invalidVertexList g f vol :=
      fun hbad => hinv (invalidVertexList_shorten hbad)
    have rule5 : ¬ invalidVertexList g' f21 vol :=
      invalidVertexList_splitFace_transfer pre_fdg hsplit' removeNones_vol_not_f12 hinv'
    have rule6 : 0 = 0 ∧ vol.head! ≠ none →
        ¬ is_duplicateEdge g' f21 u vol.head!.get! :=
      fun hpre => not_is_duplicateEdge_splitFace pre_fdg hsplit'
        removeNones_vol_not_f12 (List.length_pos_iff.mpr hvol) hinv hpre.2
    have u21 : u ∈ f21.vertices := by
      rw [hf21v]
      exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
    have hvnin' : v' ∉ removeNones vol := fun hm => by
      have h1 : v' ∉ u :: removeNones vol := hvnin
      exact h1 (List.mem_cons_of_mem _ hm)
    have hne' : v' ≠ u := by
      have h1 : v' ∉ u :: removeNones vol := hvnin
      intro e; subst e; exact h1 List.mem_cons_self
    refine ⟨?_, rule2, u21, hvnin', dist_f21, Or.inl ⟨rule1.1, rule3, ?_, hvol,
      Or.inr (Or.inr hne'), rule5, ?_⟩⟩
    · rw [hf21]
      rfl
    · have hlast' : vol.getLast! = some (verticesFrom f v').getLast! := hgl ▸ hlast
      rw [rule4] at hlast'
      exact hlast'
    · intro hpre
      exact rule6 hpre

/-- FaceDivisionProps.thy: pre_subdivFace'_Some1 -/
theorem pre_subdivFace'_Some1 {g g' : Graph} {f f21 : Face} {v' v u : Vertex} {n : Nat}
    {vol : List (Option Vertex)}
    (pre_add : pre_subdivFace' g f v' v n (some u :: vol)) (hf : f ∈ g.faces)
    (hnext : f.nextVertex v = u → n ≠ 0) (hsubset : ∀ x ∈ f.vertices, x ∈ g.vertices)
    (fdg : f21 = (splitFace g v u f (List.range' g.countVertices n)).2.1)
    (hg' : g' = (splitFace g v u f (List.range' g.countVertices n)).2.2) :
    pre_subdivFace' g' f21 v' u 0 vol :=
  pre_subdivFace'_Some1' pre_add
    (pre_subdivFace'_preFaceDiv pre_add hf hnext hsubset) fdg hg'

end Kepler.Graphs
