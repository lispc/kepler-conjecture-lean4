/-
Port of the lemma layer of Isabelle AFP "Flyspeck-Tame" `Rotation.thy`, plus
the rotation-equivalence relation `congs` from `PlaneGraphIso.thy` (lines 30-121)
that `Rotation.thy` builds on.

Sources:
- `reference/afp-flyspeck-tame/Rotation.thy`
- `reference/afp-flyspeck-tame/PlaneGraphIso.thy` (only the `congs` definition
  and its basic properties; the graph-isomorphism machinery is out of scope)

Isabelle's `rotate n xs` is Lean's `List.rotate xs n`; its API comes from
`Mathlib.Data.List.Rotate`.

Note: Isabelle's proof of `norm_eq_if_face_cong` goes through ListAux.thy's
`splitAt_rotate_pair_conv`. This port instead proves the uniqueness lemma
`rotate_eq_rotate_to_of_cons` (a rotation of a `Nodup` list is determined by
its head), which gives a more direct route.
-/
import Kepler.Graphs.Rotation
import Kepler.Graphs.ListAuxLemmas
import Mathlib.Data.List.Rotate

namespace Kepler.Graphs

variable {α β : Type _}

/-- PlaneGraphIso.thy: congs (`F₁ ≅ F₂ ≡ ∃n. F₂ = rotate n F₁`). -/
def cong (xs ys : List α) : Prop := ∃ n, ys = xs.rotate n

/-- PlaneGraphIso.thy: congs_refl -/
theorem cong_refl (xs : List α) : cong xs xs :=
  ⟨0, (List.rotate_zero xs).symm⟩

/-- PlaneGraphIso.thy: congs_sym -/
theorem cong_sym {xs ys : List α} (h : cong xs ys) : cong ys xs := by
  obtain ⟨n, rfl⟩ := h
  by_cases hx : xs = []
  · subst hx
    exact ⟨0, by simp⟩
  · refine ⟨xs.length - n % xs.length, ?_⟩
    rw [List.rotate_rotate]
    have hl : 0 < xs.length := List.length_pos_iff.mpr hx
    have hlt : n % xs.length < xs.length := Nat.mod_lt _ hl
    have hsum : n + (xs.length - n % xs.length) = xs.length * (n / xs.length + 1) := by
      rw [Nat.mul_succ]
      have hdm := Nat.div_add_mod n xs.length
      omega
    rw [hsum, List.rotate_length_mul]

/-- PlaneGraphIso.thy: congs_trans -/
theorem cong_trans {xs ys zs : List α} (h1 : cong xs ys) (h2 : cong ys zs) : cong xs zs := by
  obtain ⟨n, rfl⟩ := h1
  obtain ⟨m, rfl⟩ := h2
  exact ⟨n + m, by rw [List.rotate_rotate]⟩

/-- PlaneGraphIso.thy: congs_length -/
theorem cong_length {xs ys : List α} (h : cong xs ys) : xs.length = ys.length := by
  obtain ⟨n, rfl⟩ := h
  rw [List.length_rotate]

/-- PlaneGraphIso.thy: congs_pres_nodes (membership form) -/
theorem cong_mem {xs ys : List α} (h : cong xs ys) {a : α} : a ∈ xs ↔ a ∈ ys := by
  obtain ⟨n, rfl⟩ := h
  exact List.mem_rotate.symm

/-- PlaneGraphIso.thy: congs_distinct -/
theorem cong_distinct {xs ys : List α} (h : cong xs ys) : xs.Nodup ↔ ys.Nodup := by
  obtain ⟨n, rfl⟩ := h
  exact List.nodup_rotate.symm

/-- PlaneGraphIso.thy: congs_map -/
theorem cong_map {xs ys : List α} (f : α → β) (h : cong xs ys) :
    cong (xs.map f) (ys.map f) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n, List.map_rotate f xs n⟩

section RotateTo

variable [BEq α] [LawfulBEq α]

/-- Computational content of `Rotation.thy: cong_rotate_to`: rotating a list by
the length of the `x`-prefix is exactly `rotate_to`. -/
theorem rotate_to_eq_rotate {x : α} {xs : List α} (h : x ∈ xs) :
    rotate_to xs x = xs.rotate (splitAt x xs).1.length := by
  obtain ⟨a, b, hab⟩ : ∃ a b, (a, b) = splitAt x xs := ⟨_, _, rfl⟩
  have h1 : (splitAt x xs).1 = a := congrArg Prod.fst hab.symm
  have h2 : (splitAt x xs).2 = b := congrArg Prod.snd hab.symm
  show x :: (splitAt x xs).2 ++ (splitAt x xs).1 = xs.rotate (splitAt x xs).1.length
  rw [h1, h2, splitAt_split h hab,
    List.rotate_eq_drop_append_take (by rw [List.length_append, List.length_cons]; omega),
    List.drop_left, List.take_left]

/-- Rotation.thy: cong_rotate_to -/
theorem cong_rotate_to {x : α} {xs : List α} (h : x ∈ xs) : cong xs (rotate_to xs x) :=
  ⟨_, rotate_to_eq_rotate h⟩

/-- Auxiliary uniqueness lemma: a rotation of a `Nodup` list whose head is `x`
is fully determined by `x`. Replaces ListAux.thy `splitAt_rotate_pair_conv`
in this port. -/
theorem rotate_eq_rotate_to_of_cons {x : α} {xs : List α} (hd : xs.Nodup) (hx : x ∈ xs)
    {t : Nat} {p : List α} (h : xs.rotate t = x :: p) : xs.rotate t = rotate_to xs x := by
  have hne : xs ≠ [] := List.ne_nil_of_mem hx
  have hl : 0 < xs.length := List.length_pos_iff.mpr hne
  have hram : xs = (splitAt x xs).1 ++ x :: (splitAt x xs).2 := splitAt_ram hx
  have hu : t % xs.length < xs.length := Nat.mod_lt _ hl
  have hrot : xs.rotate t = xs.drop (t % xs.length) ++ xs.take (t % xs.length) :=
    List.rotate_eq_drop_append_take_mod
  have hdropne : xs.drop (t % xs.length) ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    exact not_le_of_gt hu
  obtain ⟨y, q, hq⟩ := List.exists_cons_of_ne_nil hdropne
  rw [hrot, hq] at h
  obtain ⟨hyx, -⟩ := List.cons.inj h
  rw [hyx] at hq
  have h3 : xs = xs.take (t % xs.length) ++ x :: q := by
    rw [← hq]
    exact (List.take_append_drop _ _).symm
  obtain ⟨h1, h2⟩ := dist_at hd hram h3
  rw [hrot, hq]
  show (x :: q) ++ xs.take (t % xs.length) = x :: (splitAt x xs).2 ++ (splitAt x xs).1
  rw [← h2, ← h1]

end RotateTo

/-- `min_list` is invariant under rotation (the set of elements does not change). -/
theorem min_list_rotate (xs : List Nat) (n : Nat) : min_list (xs.rotate n) = min_list xs := by
  by_cases hx : xs = []
  · subst hx
    simp
  · apply le_antisymm
    · exact min_list_le (List.mem_rotate.mpr (min_list_mem hx))
    · have hne : xs.rotate n ≠ [] := fun e => hx (List.rotate_eq_nil_iff.mp e)
      exact min_list_le (List.mem_rotate.mp (min_list_mem hne))

/-- Rotation.thy: face_cong_if_norm_eq -/
theorem face_cong_if_norm_eq {xs ys : List Nat} (h : rotate_min xs = rotate_min ys)
    (hx : xs ≠ []) (hy : ys ≠ []) : cong xs ys := by
  have c1 : cong xs (rotate_min xs) := cong_rotate_to (min_list_mem hx)
  have c2 : cong ys (rotate_min ys) := cong_rotate_to (min_list_mem hy)
  rw [← h] at c2
  exact cong_trans c1 (cong_sym c2)

/-- Rotation.thy: norm_eq_if_face_cong -/
theorem norm_eq_if_face_cong {xs ys : List Nat} (h : cong xs ys) (hd : xs.Nodup)
    (hx : xs ≠ []) : rotate_min xs = rotate_min ys := by
  obtain ⟨n, rfl⟩ := h
  have hmA : min_list xs ∈ xs := min_list_mem hx
  have hmB : min_list xs ∈ xs.rotate n := List.mem_rotate.mpr hmA
  show rotate_to xs (min_list xs) = rotate_to (xs.rotate n) (min_list (xs.rotate n))
  rw [min_list_rotate xs n]
  rw [rotate_to_eq_rotate hmA, rotate_to_eq_rotate hmB, List.rotate_rotate]
  have hA : xs.rotate (splitAt (min_list xs) xs).1.length =
      min_list xs :: (splitAt (min_list xs) xs).2 ++ (splitAt (min_list xs) xs).1 :=
    (rotate_to_eq_rotate hmA).symm
  have hB : xs.rotate (n + (splitAt (min_list xs) (xs.rotate n)).1.length) =
      min_list xs :: (splitAt (min_list xs) (xs.rotate n)).2 ++
        (splitAt (min_list xs) (xs.rotate n)).1 := by
    rw [← List.rotate_rotate]
    exact (rotate_to_eq_rotate hmB).symm
  rw [hA]
  show rotate_to xs (min_list xs) = xs.rotate (n + _)
  rw [rotate_eq_rotate_to_of_cons hd hmA hB]

/-- Rotation.thy: norm_eq_iff_face_cong -/
theorem norm_eq_iff_face_cong {xs ys : List Nat} (hd : xs.Nodup) (hx : xs ≠ [])
    (hy : ys ≠ []) : rotate_min xs = rotate_min ys ↔ cong xs ys :=
  ⟨fun h => face_cong_if_norm_eq h hx hy, fun h => norm_eq_if_face_cong h hd hx⟩

end Kepler.Graphs
