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

Skipped items (with reasons):
- `nths_take`, `nths_reduceIndices`, `natToVertexList_nths1`,
  `natToVertexList_nths`, `natToVertexList_removeNones`
  (source lines 3654–3906): all depend on Isabelle's `List.nths`
  (selection by an index *set*), which has not been ported;
  `natToVertexList_nths1` additionally has a ~170-line proof.
- `natToVertexList_pre_subdivFace_face`,
  `indexToVertexList_pre_subdivFace_face` (source lines 4065–4099):
  depend on `natToVertexList_removeNones`.
- `pre_subdivFace'_Some1'` (source lines 4208–4714) and
  `pre_subdivFace'_Some1` (source lines 4945–4953, which is a one-line
  corollary of `pre_subdivFace'_Some1'`): the ~500-line
  `pre_subdivFace'_Some1'` proof was not completed within the time box.
- `declare incrIndexList_help4 [simp del]` and
  `declare verticesFrom_between [simp del]`: not applicable — dropping the
  global `@[simp]` on `incrIndexList_help4` would require editing
  `EnumeratorProps.lean` (out of scope), and no proof below depends on it.
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
        show (fun z => decide (P z)) y = false from by simp [hp], ↓reduceIte, ih hys]

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
        simp only [List.filter_cons, show (fun w => decide (w = x ∨ w ∈ ys)) x = true
            from by simp, ↓reduceIte] at hays
        obtain ⟨-, htl⟩ := List.cons.inj hays
        simp only [List.filter_cons, show (fun w => decide (w ∈ ys)) x = false
            from by simp [ha_ys], ↓reduceIte]
        rw [← filter_Cons2 hxs]
        exact htl
      · by_cases hmem : x ∈ ys
        · simp only [List.filter_cons, show (fun w => decide (w = a ∨ w ∈ ys)) x = true
            from by simp [hmem], ↓reduceIte] at hays
          obtain ⟨hxae, -⟩ := List.cons.inj hays
          exact absurd hxae hxa
        · simp only [List.filter_cons, show (fun w => decide (w = a ∨ w ∈ ys)) x = false
            from by simp [hxa, hmem], ↓reduceIte] at hays
          simp only [List.filter_cons, show (fun w => decide (w ∈ ys)) x = false
            from by simp [hmem], ↓reduceIte]
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

end Kepler.Graphs
