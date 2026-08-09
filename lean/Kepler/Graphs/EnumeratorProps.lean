/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `EnumeratorProps.thy`
(properties of patch enumeration).

Source: `reference/afp-flyspeck-tame/EnumeratorProps.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Correspondence notes:
- `hd`/`last` map to `List.head!`/`List.getLast!`, `butlast` to `List.dropLast`
  (as in `GraphProps.lean`).
- `enumTab` is not ported (see `Enumerator.lean`), so `enum_enumerator` is `rfl`.
- `list_all (λx. x < Suc nmax) ls` is rendered as `∀ x ∈ ls, x < nmax + 1`.
- Auxiliary lemmas without a direct Isabelle counterpart: `mem_range'_iff`
  (membership in step-1 `List.range'`), `getLast!_append_singleton`,
  `getLast!_mem`, `mem_enumAppend` and `mem_enumerator` (membership
  unfoldings of `enumAppend`/`enumerator`).
-/
import Kepler.Graphs.Enumerator
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Nat.Basic

namespace Kepler.Graphs

variable {α : Type _}

/-! ### Auxiliary helpers (no direct Isabelle counterpart) -/

private theorem mem_range'_iff {s n m : Nat} : m ∈ List.range' s n ↔ s ≤ m ∧ m < s + n := by
  simp only [List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Nat.le_add_right _ _, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨m - s, by omega, by omega⟩

private theorem getLast!_append_singleton [Inhabited α] (l : List α) (a : α) :
    (l ++ [a]).getLast! = a :=
  List.getLast!_of_getLast? List.getLast?_concat

private theorem getLast!_mem [Inhabited α] {l : List α} (h : l ≠ []) : l.getLast! ∈ l := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_some_getLast h]
  exact List.getLast_mem h

/-! ### `hideDups` / `indexToVertexList` -/

/-- EnumeratorProps.thy: length_hideDupsRec -/
@[simp] theorem length_hideDupsRec [BEq α] (x : α) (xs : List α) :
    (hideDupsRec x xs).length = xs.length := by
  induction xs generalizing x with
  | nil => rfl
  | cons b bs ih => simp [hideDupsRec, ih]

/-- EnumeratorProps.thy: length_hideDups -/
@[simp] theorem length_hideDups [BEq α] (xs : List α) : (hideDups xs).length = xs.length := by
  cases xs with
  | nil => rfl
  | cons b bs => simp [hideDups]

/-- EnumeratorProps.thy: length_indexToVertexList -/
@[simp] theorem length_indexToVertexList (f : Face) (v : Vertex) (is : List Nat) :
    (indexToVertexList f v is).length = is.length := by
  simp [indexToVertexList]

/-! ### List not decreasing -/

/-- EnumeratorProps.thy: increasing -/
def increasing [LinearOrder α] (ls : List α) : Prop :=
  ∀ x y as bs, ls = as ++ x :: y :: bs → x ≤ y

/-- EnumeratorProps.thy: increasing1. NB: the mixed `::`/`++` statement needs
explicit parentheses — in Lean `as ++ x :: cs ++ y :: bs` parses as
`(as ++ (x :: cs)) ++ (y :: bs)`, unlike Isabelle's right-associative
`as @ x # cs @ y # bs`. -/
theorem increasing1 [LinearOrder α] {ls : List α} (h : increasing ls) :
    ∀ {as : List α} {x : α} {cs : List α} {y : α} {bs : List α},
      ls = as ++ x :: (cs ++ y :: bs) → x ≤ y := by
  intro as x cs y bs e
  induction cs generalizing as x with
  | nil =>
    simpa using h x y as bs e
  | cons c cs ih =>
    have hcy : c ≤ y := ih (as := as ++ [x]) (x := c) (by rw [e]; simp)
    have hxc : x ≤ c := h x c as (cs ++ y :: bs) (by rw [e]; simp)
    exact le_trans hxc hcy

/-- EnumeratorProps.thy: increasing2 -/
theorem increasing2 [LinearOrder α] {as bs : List α} {x y : α} (h : increasing (as ++ bs))
    (hx : x ∈ as) (hy : y ∈ bs) : x ≤ y := by
  obtain ⟨as', as'', rfl, -⟩ := List.eq_append_cons_of_mem hx
  obtain ⟨bs', bs'', rfl, -⟩ := List.eq_append_cons_of_mem hy
  exact increasing1 h (as := as') (cs := as'' ++ bs') (bs := bs'') (by simp)

/-- EnumeratorProps.thy: increasing3 -/
theorem increasing3 [LinearOrder α] {ls : List α}
    (h : ∀ as bs, ls = as ++ bs → ∀ x ∈ as, ∀ y ∈ bs, x ≤ y) : increasing ls := by
  intro x y as bs e
  exact h (as ++ [x]) (y :: bs) (by rw [e]; simp) x (by simp) y (by simp)

/-- EnumeratorProps.thy: increasing4 -/
theorem increasing4 [LinearOrder α] {as bs : List α} (h : increasing (as ++ bs)) :
    increasing as := by
  intro x y as' bs' e
  exact h x y as' (bs' ++ bs) (by rw [e]; simp)

/-- EnumeratorProps.thy: increasing5 -/
theorem increasing5 [LinearOrder α] {as bs : List α} (h : increasing (as ++ bs)) :
    increasing bs := by
  intro x y as' bs' e
  exact h x y (as ++ as') bs' (by rw [e]; simp)

/-! ### enumBase -/

/-- EnumeratorProps.thy: enumBase_length -/
theorem enumBase_length {nmax : Nat} {ls : List Nat} (h : ls ∈ enumBase nmax) :
    ls.length = 1 := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
  rfl

/-- EnumeratorProps.thy: enumBase_bound -/
theorem enumBase_bound {nmax : Nat} : ∀ y ∈ enumBase nmax, ∀ z ∈ y, z ≤ nmax := by
  intro y hy z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
  rw [List.mem_singleton] at hz
  subst hz
  exact Nat.le_of_lt_succ (List.mem_range.1 hi)

/-! ### enumAppend -/

/-- Membership in `enumAppend nmax lss`, unfolding the
`flatMap`/`map`/`range'` definition (no direct Isabelle counterpart). -/
theorem mem_enumAppend {nmax : Nat} {lss : List (List Nat)} {ls : List Nat} :
    ls ∈ enumAppend nmax lss ↔
      ∃ is ∈ lss, ∃ n : Nat, is.getLast! ≤ n ∧ n ≤ nmax ∧ ls = is ++ [n] := by
  simp only [enumAppend, List.mem_flatMap, List.mem_map, mem_range'_iff]
  constructor
  · rintro ⟨is, his, n, ⟨h1, h2⟩, rfl⟩
    exact ⟨is, his, n, h1, by omega, rfl⟩
  · rintro ⟨is, his, n, h1, h2, rfl⟩
    exact ⟨is, his, n, ⟨h1, by omega⟩, rfl⟩

/-- EnumeratorProps.thy: enumAppend_bound -/
theorem enumAppend_bound {nmax x : Nat} {lss : List (List Nat)} {ls : List Nat}
    (hls : ls ∈ enumAppend nmax lss) (hb : ∀ y ∈ lss, ∀ z ∈ y, z ≤ nmax)
    (hx : x ∈ ls) : x ≤ nmax := by
  obtain ⟨is, his, n, -, hn, rfl⟩ := mem_enumAppend.1 hls
  rw [List.mem_append, List.mem_singleton] at hx
  rcases hx with h | rfl
  · exact hb is his x h
  · exact hn

/-- EnumeratorProps.thy: enumAppend_bound_rec -/
theorem enumAppend_bound_rec {nmax n x : Nat} {lss : List (List Nat)} {ls : List Nat}
    (hls : ls ∈ iterate (enumAppend nmax) n lss) (hb : ∀ y ∈ lss, ∀ z ∈ y, z ≤ nmax)
    (hx : x ∈ ls) : x ≤ nmax := by
  suffices h : ∀ (n : Nat) (lss : List (List Nat)), (∀ y ∈ lss, ∀ z ∈ y, z ≤ nmax) →
      ∀ y ∈ iterate (enumAppend nmax) n lss, ∀ z ∈ y, z ≤ nmax from h n lss hb ls hls x hx
  intro n
  induction n with
  | zero =>
    intro lss hb y hy z hz
    exact hb y hy z hz
  | succ n ih =>
    intro lss hb y hy z hz
    exact enumAppend_bound hy (fun w hw => ih _ hb w hw) hz

/-- EnumeratorProps.thy: enumAppend_increase_rec -/
theorem enumAppend_increase_rec {nmax : Nat} :
    ∀ {ls : List Nat} {m : Nat} {as bs : List Nat},
      ls ∈ iterate (enumAppend nmax) m (enumBase nmax) →
      as ++ bs = ls → ∀ x ∈ as, ∀ y ∈ bs, x ≤ y := by
  intro ls
  induction ls using List.reverseRecOn with
  | nil =>
    intro m as bs _ hab x hx y _
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hab
    simp at hx
  | append_singleton xs x ih =>
    intro m as bs hmem hab xa hxa xb hxb
    cases m with
    | zero =>
      have hlen := enumBase_length hmem
      simp only [List.length_append, List.length_singleton] at hlen
      have hxs : xs = [] := List.length_eq_zero_iff.mp (by omega)
      subst hxs
      have ha : 0 < as.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hxa)
      have hb : 0 < bs.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hxb)
      have e : (as ++ bs).length = 1 := by rw [hab]; rfl
      rw [List.length_append] at e
      omega
    | succ n =>
      obtain ⟨is, his, k, hk1, -, hks⟩ := mem_enumAppend.1 hmem
      obtain ⟨hxs, hxk⟩ := List.append_inj' hks (by simp)
      subst hxs
      have hxk' : x = k := (List.cons.inj hxk).1
      subst hxk'
      induction bs using List.reverseRecOn with
      | nil => simp at hxb
      | append_singleton bs' b _ =>
        have hab2 : (as ++ bs') ++ [b] = xs ++ [x] := by
          rw [List.append_assoc]
          exact hab
        obtain ⟨hisb, hbk⟩ := List.append_inj' hab2 (by simp)
        have hb : b = x := (List.cons.inj hbk).1
        have hxax : xa ≤ x := by
          induction xs using List.reverseRecOn with
          | nil =>
            obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hisb
            simp at hxa
          | append_singleton ys y _ =>
            have hy : (ys ++ [y]).getLast! = y := getLast!_append_singleton _ _
            rw [hy] at hk1
            by_cases hxy : xa = y
            · exact le_trans (le_of_eq hxy) hk1
            · have hxai : xa ∈ ys ++ [y] := hisb ▸ List.mem_append_left bs' hxa
              rw [List.mem_append, List.mem_singleton] at hxai
              rcases hxai with h | h
              · exact le_trans (ih his rfl xa h y (List.mem_singleton_self y)) hk1
              · exact absurd h hxy
        by_cases hxbb : xb = b
        · rw [hxbb, hb]
          exact hxax
        · have hxb' : xb ∈ bs' := by
            rw [List.mem_append, List.mem_singleton] at hxb
            rcases hxb with h | h
            · exact h
            · exact absurd h hxbb
          exact ih his hisb xa hxa xb hxb'

/-- EnumeratorProps.thy: enumAppend_length1 -/
theorem enumAppend_length1 {nmax : Nat} :
    ∀ {ls : List Nat} {n : Nat} {lss : List (List Nat)} {k : Nat},
      ls ∈ iterate (enumAppend nmax) n lss →
      (∀ l ∈ lss, l.length = k) → ls.length = k + n := by
  intro ls n
  induction n generalizing ls with
  | zero =>
    intro lss k hmem hl
    exact hl ls hmem
  | succ n ih =>
    intro lss k hmem hl
    obtain ⟨is, his, m, -, -, rfl⟩ := mem_enumAppend.1 hmem
    have := ih his hl
    simp only [List.length_append, List.length_singleton]
    omega

/-- EnumeratorProps.thy: enumAppend_length2 -/
theorem enumAppend_length2 {nmax n k K : Nat} {lss : List (List Nat)} {ls : List Nat}
    (hls : ls ∈ iterate (enumAppend nmax) n lss) (hl : ∀ l ∈ lss, l.length = k)
    (hK : K = k + n) : ls.length = K := by
  rw [hK]
  exact enumAppend_length1 hls hl

/-! ### enum -/

/-- EnumeratorProps.thy: enum_enumerator. In this port `enum` is *defined* as
`enumerator` (the `enumTab` cache is not ported), so this is `rfl`. -/
theorem enum_enumerator (i j : Nat) : enum i j = enumerator i j := rfl

/-! ### enumerator -/

/-- Membership in `enumerator m nmax`, unfolding the definition (no direct
Isabelle counterpart). -/
theorem mem_enumerator {m nmax : Nat} {ls : List Nat} :
    ls ∈ enumerator m nmax ↔
      ∃ is, is ∈ iterate (enumAppend (nmax - 2)) (m - 3) (enumBase (nmax - 2)) ∧
        [0] ++ is ++ [nmax - 1] = ls :=
  List.mem_map

/-- EnumeratorProps.thy: enumerator_hd -/
theorem enumerator_hd {m n : Nat} {ls : List Nat} (h : ls ∈ enumerator m n) :
    ls.head! = 0 := by
  obtain ⟨is, -, rfl⟩ := mem_enumerator.1 h
  simp

/-- EnumeratorProps.thy: enumerator_last -/
theorem enumerator_last {m n : Nat} {ls : List Nat} (h : ls ∈ enumerator m n) :
    ls.getLast! = n - 1 := by
  obtain ⟨is, -, rfl⟩ := mem_enumerator.1 h
  exact getLast!_append_singleton _ _

/-- EnumeratorProps.thy: enumerator_length -/
theorem enumerator_length {m n : Nat} {ls : List Nat} (h : ls ∈ enumerator m n) :
    2 ≤ ls.length := by
  obtain ⟨is, -, rfl⟩ := mem_enumerator.1 h
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- EnumeratorProps.thy: enumerator_not_empty -/
theorem enumerator_not_empty {m n : Nat} {ls : List Nat} (h : ls ∈ enumerator m n) :
    ls ≠ [] := by
  have hlen := enumerator_length h
  intro he
  subst he
  simp at hlen

/-- EnumeratorProps.thy: enumerator_length2 -/
theorem enumerator_length2 {m n : Nat} {ls : List Nat} (h : ls ∈ enumerator m n)
    (hm : 2 < m) : ls.length = m := by
  obtain ⟨is, his, rfl⟩ := mem_enumerator.1 h
  have hlen : is.length = 1 + (m - 3) :=
    enumAppend_length1 his (fun l hl => enumBase_length hl)
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- EnumeratorProps.thy: enumerator_bound -/
theorem enumerator_bound {m nmax x : Nat} {ls : List Nat} (h : ls ∈ enumerator m nmax)
    (hn : 0 < nmax) (hx : x ∈ ls) : x < nmax := by
  obtain ⟨is, his, rfl⟩ := mem_enumerator.1 h
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (h0 | hxi) | h1
  · omega
  · have hle := enumAppend_bound_rec his enumBase_bound hxi
    omega
  · omega

/-- EnumeratorProps.thy: enumerator_bound2 -/
theorem enumerator_bound2 {m nmax x : Nat} {ls : List Nat} (h : ls ∈ enumerator m nmax)
    (hn : 1 < nmax) (hx : x ∈ ls.dropLast) : x < nmax - 1 := by
  obtain ⟨is, his, rfl⟩ := mem_enumerator.1 h
  rw [List.dropLast_concat] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with h0 | hxi
  · omega
  · have hle := enumAppend_bound_rec his enumBase_bound hxi
    omega

/-- EnumeratorProps.thy: enumerator_bound3 -/
theorem enumerator_bound3 {m nmax : Nat} {ls : List Nat} (h : ls ∈ enumerator m nmax)
    (hn : 1 < nmax) : ls.dropLast.getLast! < nmax - 1 := by
  have hlen := enumerator_length h
  cases ls using List.reverseRecOn with
  | nil => simp at hlen
  | append_singleton ys y _ =>
    rw [List.dropLast_concat]
    by_cases hys : ys = []
    · subst hys
      simp at hlen
    · apply enumerator_bound2 h hn
      rw [List.dropLast_concat]
      exact getLast!_mem hys

/-- EnumeratorProps.thy: enumerator_increase -/
theorem enumerator_increase {m nmax : Nat} {ls as bs : List Nat} (h : ls ∈ enumerator m nmax)
    (heq : as ++ bs = ls) : ∀ x ∈ as, ∀ y ∈ bs, x ≤ y := by
  obtain ⟨is, his, rfl⟩ := mem_enumerator.1 h
  intro x hx y hy
  cases as with
  | nil => simp at hx
  | cons a as' =>
    have h1 : (a :: as') ++ bs = (0 :: is) ++ [nmax - 1] := heq
    rw [List.cons_append, List.cons_append] at h1
    obtain ⟨h0, habs⟩ := List.cons.inj h1
    subst h0
    cases bs using List.reverseRecOn with
    | nil => simp at hy
    | append_singleton bs' b _ =>
      have h2 : (as' ++ bs') ++ [b] = is ++ [nmax - 1] := by
        rw [List.append_assoc]
        exact habs
      obtain ⟨hisb, hb⟩ := List.append_inj' h2 (by simp)
      have hbv : b = nmax - 1 := (List.cons.inj hb).1
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact Nat.zero_le y
      · rw [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy' | rfl
        · exact enumAppend_increase_rec his hisb x hx' y hy'
        · have hxis : x ∈ is := hisb ▸ List.mem_append_left bs' hx'
          have hxle := enumAppend_bound_rec his enumBase_bound hxis
          omega

/-- EnumeratorProps.thy: enumerator_increasing -/
theorem enumerator_increasing {m nmax : Nat} {ls : List Nat} (h : ls ∈ enumerator m nmax) :
    increasing ls := by
  apply increasing3
  intro as bs heq x hx y hy
  exact enumerator_increase h heq.symm x hx y hy

/-! ### incrIndexList -/

/-- EnumeratorProps.thy: incrIndexList -/
def incrIndexList (ls : List Nat) (m nmax : Nat) : Prop :=
  1 < m ∧ 1 < nmax ∧ ls.head! = 0 ∧ ls.getLast! = nmax - 1 ∧ ls.length = m ∧
    ls.dropLast.getLast! < ls.getLast! ∧ increasing ls

/-- EnumeratorProps.thy: incrIndexList_1lem -/
@[simp] theorem incrIndexList_1lem {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : 1 < m := h.1

/-- EnumeratorProps.thy: incrIndexList_1len -/
@[simp] theorem incrIndexList_1len {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : 1 < nmax := h.2.1

/-- EnumeratorProps.thy: incrIndexList_help2 -/
@[simp] theorem incrIndexList_help2 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : ls.head! = 0 := h.2.2.1

/-- EnumeratorProps.thy: incrIndexList_help21 -/
@[simp] theorem incrIndexList_help21 {l : Nat} {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList (l :: ls) m nmax) : l = 0 := by
  have := h.2.2.1
  rwa [List.head!_cons] at this

/-- EnumeratorProps.thy: incrIndexList_help3 -/
@[simp] theorem incrIndexList_help3 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : ls.getLast! = nmax - 1 := h.2.2.2.1

/-- EnumeratorProps.thy: incrIndexList_help4 -/
@[simp] theorem incrIndexList_help4 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : ls.length = m := h.2.2.2.2.1

/-- EnumeratorProps.thy: incrIndexList_help5 -/
theorem incrIndexList_help5 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : ls.dropLast.getLast! < nmax - 1 := by
  obtain ⟨-, -, -, hlast, -, hbl, -⟩ := h
  rw [← hlast]
  exact hbl

/-- EnumeratorProps.thy: incrIndexList_help6 -/
@[simp] theorem incrIndexList_help6 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : increasing ls := h.2.2.2.2.2.2

/-- EnumeratorProps.thy: incrIndexList_help7 -/
@[simp] theorem incrIndexList_help7 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : ls ≠ [] := by
  intro he
  have hlen := h.2.2.2.2.1
  have hm := h.1
  subst he
  simp only [List.length_nil] at hlen
  omega

/-- EnumeratorProps.thy: incrIndexList_help71 -/
@[simp] theorem incrIndexList_help71 {m nmax : Nat} : ¬ incrIndexList [] m nmax :=
  fun h => incrIndexList_help7 h rfl

/-- EnumeratorProps.thy: incrIndexList_help8 -/
@[simp] theorem incrIndexList_help8 {ls : List Nat} {m nmax : Nat}
    (h : incrIndexList ls m nmax) : ls.dropLast ≠ [] := by
  intro hne
  have hne' := incrIndexList_help7 h
  have h2 := List.dropLast_concat_getLast hne'
  rw [hne] at h2
  have hlen := h.2.2.2.2.1
  have hm := h.1
  have e : ls.length = 1 := by rw [← h2]; rfl
  omega

/-- EnumeratorProps.thy: incrIndexList_help81 -/
@[simp] theorem incrIndexList_help81 {l m nmax : Nat} : ¬ incrIndexList [l] m nmax :=
  fun h => incrIndexList_help8 h (by simp)

/-- EnumeratorProps.thy: incrIndexList_help9 -/
theorem incrIndexList_help9 {ls : List Nat} {m nmax x : Nat}
    (h : incrIndexList ls m nmax) (hx : x ∈ ls.dropLast) : x ≤ nmax - 2 := by
  have hne := incrIndexList_help7 h
  have hbl := incrIndexList_help8 h
  have e1 : ls.dropLast = ls.dropLast.dropLast ++ [ls.dropLast.getLast hbl] :=
    (List.dropLast_concat_getLast hbl).symm
  have e2 : ls = (ls.dropLast.dropLast ++ [ls.dropLast.getLast hbl]) ++ [ls.getLast hne] :=
    (List.dropLast_concat_getLast hne).symm.trans (congrArg (· ++ [ls.getLast hne]) e1)
  -- `last (butlast ls) ≤ nmax - 2` from `last (butlast ls) < last ls = nmax - 1`
  have hd : ls.dropLast.getLast! = ls.dropLast.getLast hbl :=
    List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hbl)
  have hlt : ls.dropLast.getLast! < ls.getLast! := h.2.2.2.2.2.1
  have hl : ls.getLast! = nmax - 1 := h.2.2.2.1
  have hle2 : ls.dropLast.getLast hbl ≤ nmax - 2 := by omega
  -- any member of `butlast ls` is at most `last (butlast ls)`, by monotonicity
  have hinc : increasing ((ls.dropLast.dropLast ++ [ls.dropLast.getLast hbl]) ++ [ls.getLast hne]) := by
    rw [← e2]
    exact h.2.2.2.2.2.2
  rw [List.append_assoc] at hinc
  have hxle : x ≤ ls.dropLast.getLast hbl := by
    by_cases hx' : x ∈ ls.dropLast.dropLast
    · exact increasing2 hinc hx' (by simp)
    · rw [e1, List.mem_append, List.mem_singleton] at hx
      rcases hx with hmem | hmem
      · exact absurd hmem hx'
      · exact le_of_eq hmem
  omega

/-- EnumeratorProps.thy: incrIndexList_help10 -/
theorem incrIndexList_help10 {ls : List Nat} {m nmax x : Nat}
    (h : incrIndexList ls m nmax) (hx : x ∈ ls) : x < nmax := by
  have hne := incrIndexList_help7 h
  have e := List.dropLast_concat_getLast hne
  rw [← e, List.mem_append, List.mem_singleton] at hx
  have hn := h.2.1
  rcases hx with hx' | hx'
  · have hle := incrIndexList_help9 h hx'
    omega
  · have hl : ls.getLast! = nmax - 1 := h.2.2.2.1
    have hg : ls.getLast hne = ls.getLast! :=
      (List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hne)).symm
    omega

/-- EnumeratorProps.thy: enumerator_correctness -/
theorem enumerator_correctness {m nmax : Nat} {ls : List Nat} (hm : 2 < m) (hn : 1 < nmax)
    (h : ls ∈ enumerator m nmax) : incrIndexList ls m nmax := by
  refine ⟨by omega, hn, enumerator_hd h, enumerator_last h, enumerator_length2 h hm, ?_, ?_⟩
  · rw [enumerator_last h]
    exact enumerator_bound3 h hn
  · exact enumerator_increasing h

/-- EnumeratorProps.thy: enumerator_completeness_help -/
theorem enumerator_completeness_help {nmax : Nat} :
    ∀ {ks : Nat} {ls : List Nat}, increasing ls → ls ≠ [] → ls.length = ks + 1 →
      (∀ x ∈ ls, x < nmax + 1) →
      ls ∈ iterate (enumAppend nmax) ks (enumBase nmax) := by
  intro ks
  induction ks with
  | zero =>
    intro ls hinc hne hlen hall
    obtain ⟨x, rfl⟩ : ∃ x, ls = [x] := by
      cases ls with
      | nil => simp at hlen
      | cons x xs =>
        cases xs with
        | nil => exact ⟨x, rfl⟩
        | cons y ys =>
          simp only [List.length_cons] at hlen
          omega
    have hx : x < nmax + 1 := hall x (by simp)
    exact List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩
  | succ n ih =>
    intro ls hinc hne hlen hall
    obtain ⟨ls', l, hls⟩ : ∃ ls' l, ls = ls' ++ [l] :=
      ⟨ls.dropLast, ls.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    have hlen' : ls'.length = n + 1 := by
      have e := congrArg List.length hls
      simp only [List.length_append, List.length_singleton] at e
      omega
    have hne' : ls' ≠ [] := by
      intro c
      subst c
      simp at hlen'
    have h1 : increasing (ls' ++ [l]) := by rw [← hls]; exact hinc
    have hinc' : increasing ls' := increasing4 h1
    have hall' : ∀ z ∈ ls', z < nmax + 1 := by
      intro z hz
      exact hall z (by rw [hls]; exact List.mem_append_left [l] hz)
    have his' : ls' ∈ iterate (enumAppend nmax) n (enumBase nmax) := ih hinc' hne' hlen' hall'
    have hll : l < nmax + 1 := hall l (by rw [hls]; simp)
    have hgl : ls'.getLast! ≤ l := by
      have e1 : ls'.dropLast ++ [ls'.getLast hne'] = ls' := List.dropLast_concat_getLast hne'
      have e2 : ls = (ls'.dropLast ++ [ls'.getLast hne']) ++ [l] := by rw [hls, e1]
      have h2 : increasing ((ls'.dropLast ++ [ls'.getLast hne']) ++ [l]) := by
        rw [← e2]
        exact hinc
      have hle : ls'.getLast hne' ≤ l := increasing2 h2 (by simp) (by simp)
      have hg : ls'.getLast! = ls'.getLast hne' :=
        List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hne')
      omega
    have hfin : ls' ++ [l] ∈ enumAppend nmax (iterate (enumAppend nmax) n (enumBase nmax)) :=
      mem_enumAppend.2 ⟨ls', his', l, hgl, by omega, rfl⟩
    rw [hls]
    exact hfin

/-- EnumeratorProps.thy: enumerator_completeness -/
theorem enumerator_completeness {m nmax : Nat} {ls : List Nat} (hm : 2 < m)
    (h : incrIndexList ls m nmax) : ls ∈ enumerator m nmax := by
  have hhd : ls.head! = 0 := h.2.2.1
  have hlast : ls.getLast! = nmax - 1 := h.2.2.2.1
  have hlen : ls.length = m := h.2.2.2.2.1
  have hinc : increasing ls := h.2.2.2.2.2.2
  cases ls with
  | nil =>
    simp only [List.length_nil] at hlen
    omega
  | cons x zs =>
    rw [List.head!_cons] at hhd
    subst hhd
    cases zs using List.reverseRecOn with
    | nil =>
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    | append_singleton ks y _ =>
      have e : (0 :: (ks ++ [y])).getLast! = y := getLast!_append_singleton (0 :: ks) y
      rw [e] at hlast
      subst hlast
      have hkslen : ks.length = m - 2 := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hlen
        omega
      have hksne : ks ≠ [] := by
        intro c
        subst c
        simp only [List.length_nil] at hkslen
        omega
      have hincks : increasing ks := by
        have h1 : increasing (([0] ++ ks) ++ [nmax - 1]) := hinc
        exact increasing5 (increasing4 h1)
      have hbound : ∀ z ∈ ks, z < (nmax - 2) + 1 := by
        intro z hz
        have edl : (0 :: (ks ++ [nmax - 1])).dropLast = 0 :: ks :=
          List.dropLast_concat (l₁ := 0 :: ks) (b := nmax - 1)
        have hz' : z ∈ (0 :: (ks ++ [nmax - 1])).dropLast := by
          rw [edl]
          exact List.mem_cons_of_mem 0 hz
        have hle := incrIndexList_help9 h hz'
        omega
      have hlen1 : 0 < ks.length := List.length_pos_iff.mpr hksne
      have hksmem : ks ∈ iterate (enumAppend (nmax - 2)) (ks.length - 1) (enumBase (nmax - 2)) :=
        enumerator_completeness_help hincks hksne (by omega) hbound
      rw [show ks.length - 1 = m - 3 from by omega] at hksmem
      exact mem_enumerator.2 ⟨ks, hksmem, rfl⟩

/-- EnumeratorProps.thy: enumerator_equiv -/
@[simp] theorem enumerator_equiv {n m : Nat} {is : List Nat} (hn : 2 < n) (hm : 1 < m) :
    is ∈ enumerator n m ↔ incrIndexList is n m :=
  ⟨fun h => enumerator_correctness hn hm h, fun h => enumerator_completeness hn h⟩

end Kepler.Graphs
