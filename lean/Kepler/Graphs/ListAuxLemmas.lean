/-
Port of the lemma layer of Isabelle AFP "Flyspeck-Tame" `ListAux.thy`.

Source: `reference/afp-flyspeck-tame/ListAux.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

Scope: lemmas about the functions already ported in `Kepler/Graphs/ListAux.lean`
(`splitAtRec`/`splitAt`, `between`, `minimal`, `min_list`, `replace`, `mapAt`,
`removeKey`/`removeKeyList`), plus the `distinct` splitting lemmas (`dist_at*`)
they rely on. Since the ported functions are defined with `BEq`, the lemmas
assume `[LawfulBEq α]`.

Deliberately skipped:
- lemmas about functions we did not port (`listProd`, `enum`, `isTable`, ...);
- the `rotate`-section helper lemmas (`plus_length1`, `rotate_inv1`, ...):
  Lean's `List.rotate` API (Mathlib `Mathlib.Data.List.Rotate`) covers them,
  see `RotationLemmas.lean`;
- `splitAt_rotate_pair_conv`: superseded in this port by
  `RotationLemmas.rotate_eq_rotate_to_of_cons`;
- `splitAt_take`/`splitAt_drop`, `fst_splitAt_last`, `fst/snd_splitAt_rev`,
  `fst/snd_splitAt_upt` (not needed for the Rotation port);
- `split_between` (a 50-line case bash; can be ported later if needed).
-/
import Kepler.Graphs.ListAux

namespace Kepler.Graphs

variable {α β : Type _}

/-! ### splitAt -/

section SplitAt

variable [BEq α] [LawfulBEq α]

/-- ListAux.thy: splitAtRec_ram -/
theorem splitAtRec_ram {c : α} :
    ∀ {us vs : List α} {a b : List α},
      c ∈ vs → (a, b) = splitAtRec c us vs → us ++ vs = a ++ c :: b := by
  intro us vs
  induction vs generalizing us with
  | nil => intro a b h _; exact absurd h List.not_mem_nil
  | cons v vs ih =>
    intro a b hv hab
    rw [List.mem_cons] at hv
    by_cases hvc : v = c
    · subst hvc
      simp only [splitAtRec, beq_self_eq_true, ↓reduceIte] at hab
      obtain ⟨rfl, rfl⟩ := hab
      rfl
    · have hb : (v == c) = false := beq_eq_false_iff_ne.mpr hvc
      simp only [splitAtRec, hb] at hab
      have hvs : c ∈ vs := hv.resolve_left (Ne.symm hvc)
      have e := ih hvs hab
      simpa [List.append_assoc] using e

/-- ListAux.thy: splitAtRec_notRam -/
theorem splitAtRec_notRam {c : α} :
    ∀ {us vs : List α}, c ∉ vs → splitAtRec c us vs = (us ++ vs, []) := by
  intro us vs
  induction vs generalizing us with
  | nil => intro _; simp [splitAtRec]
  | cons v vs ih =>
    intro h
    rw [List.mem_cons, not_or] at h
    have hb : (v == c) = false := beq_eq_false_iff_ne.mpr (Ne.symm h.1)
    simp only [splitAtRec, hb]
    rw [ih h.2, List.append_assoc]
    rfl

/-- ListAux.thy: splitAt_no_ram -/
theorem splitAt_no_ram {c : α} {vs : List α} (h : c ∉ vs) :
    splitAt c vs = (vs, []) := by
  have e := splitAtRec_notRam (us := []) h
  simpa [splitAt] using e

/-- ListAux.thy: splitAt_ram -/
theorem splitAt_ram {c : α} {vs : List α} (h : c ∈ vs) :
    vs = (splitAt c vs).1 ++ c :: (splitAt c vs).2 :=
  splitAtRec_ram (us := []) (a := (splitAt c vs).1) (b := (splitAt c vs).2) h rfl

/-- ListAux.thy: splitAt_split -/
theorem splitAt_split {c : α} {vs : List α} (h : c ∈ vs) {a b : List α}
    (hab : (a, b) = splitAt c vs) : vs = a ++ c :: b := by
  have hram := splitAt_ram h
  rw [← hab] at hram
  exact hram

/-- ListAux.thy: splitAt_in_fst -/
theorem splitAt_in_fst {v c : α} {vs : List α} (h : v ∈ (splitAt c vs).1) : v ∈ vs := by
  by_cases hc : c ∈ vs
  · rw [splitAt_ram hc]
    exact List.mem_append_left _ h
  · rw [splitAt_no_ram hc] at h
    exact h

/-- ListAux.thy: splitAt_in_snd -/
theorem splitAt_in_snd {v c : α} {vs : List α} (h : v ∈ (splitAt c vs).2) : v ∈ vs := by
  by_cases hc : c ∈ vs
  · rw [splitAt_ram hc]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · rw [splitAt_no_ram hc] at h
    exact absurd h (List.not_mem_nil)

/-- ListAux.thy: splitAt_not1 -/
theorem splitAt_not1 {v c : α} {vs : List α} (h : v ∉ vs) : v ∉ (splitAt c vs).1 :=
  mt splitAt_in_fst h

/-- ListAux.thy: splitAt_subset_ab (also `splitAt_subset` there) -/
theorem splitAt_subset_ab {c : α} {vs : List α} {a b : List α}
    (hab : (a, b) = splitAt c vs) : a ⊆ vs ∧ b ⊆ vs := by
  have e1 : a = (splitAt c vs).1 := congrArg Prod.fst hab
  have e2 : b = (splitAt c vs).2 := congrArg Prod.snd hab
  exact ⟨fun _ h => splitAt_in_fst (e1 ▸ h), fun _ h => splitAt_in_snd (e2 ▸ h)⟩

/-- ListAux.thy: splitAt_2 -/
theorem splitAt_2 {v c : α} {vs : List α} (hv : v ∈ vs) {a b : List α}
    (hab : (a, b) = splitAt c vs) : v ∈ a ∨ v ∈ b ∨ v = c := by
  by_cases hc : c ∈ vs
  · have hsplit := splitAt_split hc hab
    rw [hsplit, List.mem_append, List.mem_cons] at hv
    rcases hv with h | rfl | h
    · exact Or.inl h
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl h)
  · rw [splitAt_no_ram hc] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact Or.inl hv

end SplitAt

/-! ### distinct splitting lemmas -/

/-- ListAux.thy: dist_at1 -/
theorem dist_at1 {r : α} :
    ∀ {vs a b c d : List α}, vs.Nodup → vs = a ++ r :: b → vs = c ++ r :: d → a = c := by
  intro vs a
  induction a generalizing vs with
  | nil =>
    intro b c d hd h1 h2
    cases c with
    | nil => rfl
    | cons c cs =>
      exfalso
      simp only [List.nil_append] at h1
      simp only [List.cons_append] at h2
      rw [h1] at h2 hd
      obtain ⟨_, hbd⟩ := List.cons.inj h2
      rw [List.nodup_cons] at hd
      apply hd.1
      rw [hbd]
      exact List.mem_append_right _ (List.mem_cons_self)
  | cons x xs ih =>
    intro b c d hd h1 h2
    cases c with
    | nil =>
      exfalso
      simp only [List.cons_append] at h1
      simp only [List.nil_append] at h2
      rw [h2] at h1 hd
      obtain ⟨_, hdb⟩ := List.cons.inj h1
      rw [List.nodup_cons] at hd
      apply hd.1
      rw [hdb]
      exact List.mem_append_right _ (List.mem_cons_self)
    | cons c cs =>
      simp only [List.cons_append] at h1 h2
      have heq : x :: (xs ++ r :: b) = c :: (cs ++ r :: d) := h1.symm.trans h2
      obtain ⟨hxc, htl⟩ := List.cons.inj heq
      rw [h1, List.nodup_cons] at hd
      have h := ih hd.2 rfl htl
      rw [hxc, h]

/-- ListAux.thy: dist_at -/
theorem dist_at {r : α} {vs a b c d : List α} (hd : vs.Nodup)
    (h1 : vs = a ++ r :: b) (h2 : vs = c ++ r :: d) : a = c ∧ b = d := by
  have hac : a = c := dist_at1 hd h1 h2
  subst hac
  have h : a ++ r :: b = a ++ r :: d := h1.symm.trans h2
  exact ⟨rfl, (List.cons.inj (List.append_cancel_left h)).2⟩

/-- ListAux.thy: dist_at2 -/
theorem dist_at2 {r : α} {vs a b c d : List α} (hd : vs.Nodup)
    (h1 : vs = a ++ r :: b) (h2 : vs = c ++ r :: d) : b = d :=
  (dist_at hd h1 h2).2

section SplitAtDistinct

variable [BEq α] [LawfulBEq α]

/-- ListAux.thy: splitAt_distinct_ab_aux -/
theorem splitAt_distinct_ab_aux {c : α} {vs : List α} (hd : vs.Nodup) {a b : List α}
    (hab : (a, b) = splitAt c vs) : a.Nodup ∧ b.Nodup := by
  by_cases hc : c ∈ vs
  · have hsplit := splitAt_split hc hab
    rw [hsplit, List.nodup_append] at hd
    exact ⟨hd.1, (List.nodup_cons.mp hd.2.1).2⟩
  · rw [splitAt_no_ram hc] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hd, List.nodup_nil⟩

/-- ListAux.thy: splitAt_distinct_fst -/
theorem splitAt_distinct_fst {c : α} {vs : List α} (hd : vs.Nodup) :
    (splitAt c vs).1.Nodup :=
  (splitAt_distinct_ab_aux hd rfl).1

/-- ListAux.thy: splitAt_distinct_snd -/
theorem splitAt_distinct_snd {c : α} {vs : List α} (hd : vs.Nodup) :
    (splitAt c vs).2.Nodup :=
  (splitAt_distinct_ab_aux hd rfl).2

/-- ListAux.thy: splitAt_distinct_ab -/
theorem splitAt_distinct_ab {c : α} {vs : List α} (hd : vs.Nodup) {a b : List α}
    (hab : (a, b) = splitAt c vs) : ∀ x ∈ a, x ∉ b := by
  by_cases hc : c ∈ vs
  · have hsplit := splitAt_split hc hab
    rw [hsplit, List.nodup_append] at hd
    intro x hxa hxb
    exact hd.2.2 x hxa x (List.mem_cons_of_mem c hxb) rfl
  · rw [splitAt_no_ram hc] at hab
    obtain ⟨rfl, rfl⟩ := hab
    intro x _ hxb
    exact absurd hxb (List.not_mem_nil)

/-- ListAux.thy: splitAt_distinct_fst_snd -/
theorem splitAt_distinct_fst_snd {c : α} {vs : List α} (hd : vs.Nodup) :
    ∀ x ∈ (splitAt c vs).1, x ∉ (splitAt c vs).2 :=
  splitAt_distinct_ab hd rfl

/-- ListAux.thy: splitAt_distinct_ram_fst -/
theorem splitAt_distinct_ram_fst {c : α} {vs : List α} (hd : vs.Nodup) :
    c ∉ (splitAt c vs).1 := by
  by_cases hc : c ∈ vs
  · have hram := splitAt_ram hc
    rw [hram, List.nodup_append] at hd
    intro hmem
    exact hd.2.2 c hmem c (List.mem_cons_self) rfl
  · rw [splitAt_no_ram hc]
    exact hc

/-- ListAux.thy: splitAt_distinct_ram_snd -/
theorem splitAt_distinct_ram_snd {c : α} {vs : List α} (hd : vs.Nodup) :
    c ∉ (splitAt c vs).2 := by
  by_cases hc : c ∈ vs
  · have hram := splitAt_ram hc
    rw [hram, List.nodup_append] at hd
    exact (List.nodup_cons.mp hd.2.1).1
  · rw [splitAt_no_ram hc]
    exact List.not_mem_nil

/-- ListAux.thy: splitAt_dist_ram -/
theorem splitAt_dist_ram {c : α} {vs : List α} (hd : vs.Nodup) {a b : List α}
    (h : vs = a ++ c :: b) : (a, b) = splitAt c vs := by
  have hc : c ∈ vs := by
    rw [h]
    exact List.mem_append_right _ (List.mem_cons_self)
  have hram := splitAt_ram hc
  obtain ⟨h1, h2⟩ := dist_at hd h hram
  rw [h1, h2]

end SplitAtDistinct

/-! ### between -/

section Between

variable [BEq α]

/-- Unfolded form of `ListAux.thy: between` (avoids the pattern-matching `let`). -/
theorem between_def (vs : List α) (r₁ r₂ : α) :
    between vs r₁ r₂ =
      if (splitAt r₁ vs).2.contains r₂ then (splitAt r₂ (splitAt r₁ vs).2).1
      else (splitAt r₁ vs).2 ++ (splitAt r₂ (splitAt r₁ vs).1).1 := by
  unfold between
  obtain ⟨pre, post⟩ := splitAt r₁ vs
  rfl

variable [LawfulBEq α]

/-- ListAux.thy: inbetween_inset -/
theorem inbetween_inset {x a b : α} {xs : List α} (h : x ∈ between xs a b) : x ∈ xs := by
  rw [between_def] at h
  by_cases hb : (splitAt a xs).2.contains b
  · rw [if_pos hb] at h
    exact splitAt_in_snd (splitAt_in_fst h)
  · rw [if_neg hb] at h
    rcases List.mem_append.mp h with h | h
    · exact splitAt_in_snd h
    · exact splitAt_in_fst (splitAt_in_fst h)

/-- ListAux.thy: notinset_notinbetween -/
theorem notinset_notinbetween {x a b : α} {xs : List α} (h : x ∉ xs) :
    x ∉ between xs a b :=
  mt inbetween_inset h

/-- ListAux.thy: set_between_id -/
theorem set_between_id {x y : α} {xs : List α} (hd : xs.Nodup) (hx : x ∈ xs) :
    y ∈ between xs x x ↔ y ∈ xs ∧ y ≠ x := by
  obtain ⟨a, b, hsplit⟩ := List.append_of_mem hx
  have hsp : (a, b) = splitAt x xs := splitAt_dist_ram hd hsplit
  have hdb : (a ++ x :: b).Nodup := hsplit ▸ hd
  have hxa : x ∉ a := fun h => (List.nodup_append.mp hdb).2.2 x h x
    (List.mem_cons_self) rfl
  have hxb : x ∉ b := (List.nodup_cons.mp (List.nodup_append.mp hdb).2.1).1
  have hb : between xs x x = b ++ a := by
    rw [between_def, ← hsp]
    show (if b.contains x then (splitAt x b).1 else b ++ (splitAt x a).1) = b ++ a
    have hcb : ¬ (b.contains x) := mt List.contains_iff_mem.mp hxb
    rw [if_neg hcb, splitAt_no_ram hxa]
  rw [hb, hsplit]
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact ⟨List.mem_append_right a (List.mem_cons_of_mem x h), fun hyx => hxb (hyx ▸ h)⟩
    · exact ⟨List.mem_append_left _ h, fun hyx => hxa (hyx ▸ h)⟩
  · rintro ⟨h, hyx⟩
    rw [List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact List.mem_append_right _ h
    · exact absurd h hyx
    · exact List.mem_append_left _ h

end Between

/-! ### minimal and min_list -/

/-- ListAux.thy: minimal_in_set -/
theorem minimal_in_set [Inhabited α] (f : α → Nat) :
    ∀ {xs : List α}, xs ≠ [] → minimal f xs ∈ xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
    intro _
    simp only [minimal]
    by_cases hx : xs.isEmpty
    · rw [if_pos hx]
      exact List.mem_cons_self
    · rw [if_neg hx]
      have hxs : xs ≠ [] := fun e => hx (List.isEmpty_iff.mpr e)
      show (if f x ≤ f (minimal f xs) then x else minimal f xs) ∈ x :: xs
      by_cases hle : f x ≤ f (minimal f xs)
      · rw [if_pos hle]
        exact List.mem_cons_self
      · rw [if_neg hle]
        exact List.mem_cons_of_mem _ (ih hxs)

/-- ListAux.thy: min_list (membership; cf. `min_list_conv_Min`) -/
theorem min_list_mem : ∀ {xs : List Nat}, xs ≠ [] → min_list xs ∈ xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons x xs ih =>
    intro _
    simp only [min_list]
    by_cases hx : xs.isEmpty
    · rw [if_pos hx]
      exact List.mem_cons_self
    · rw [if_neg hx]
      have hxs : xs ≠ [] := fun e => hx (List.isEmpty_iff.mpr e)
      rcases Nat.le_total x (min_list xs) with hle | hle
      · rw [Nat.min_eq_left hle]
        exact List.mem_cons_self
      · rw [Nat.min_eq_right hle]
        exact List.mem_cons_of_mem _ (ih hxs)

/-- ListAux.thy: min_list (minimum property; cf. `min_list_conv_Min`) -/
theorem min_list_le {xs : List Nat} {y : Nat} (h : y ∈ xs) : min_list xs ≤ y := by
  induction xs with
  | nil => exact absurd h (List.not_mem_nil)
  | cons x xs ih =>
    rw [List.mem_cons] at h
    simp only [min_list]
    by_cases hx : xs.isEmpty
    · rw [if_pos hx]
      have hxs : xs = [] := List.isEmpty_iff.mp hx
      subst hxs
      simp only [List.not_mem_nil, or_false] at h
      subst h
      exact Nat.le_refl _
    · rw [if_neg hx]
      rcases h with rfl | h
      · exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih h)

/-! ### replace -/

section Replace

variable [BEq α] [LawfulBEq α]

/-- ListAux.thy: replace_id -/
@[simp]
theorem replace_id {x : α} {xs : List α} : replace x [x] xs = xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases h : z = x
    · subst h
      simp [replace]
    · simp [replace, h, ih]

/-- ListAux.thy: length_replace1 -/
@[simp]
theorem length_replace1 {x y : α} {xs : List α} : (replace x [y] xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases h : z = x
    · subst h
      simp [replace]
    · simp [replace, h, ih]

/-- ListAux.thy: len_replace_ge_same -/
theorem len_replace_ge_same {x : α} {ys xs : List α} (h : 1 ≤ ys.length) :
    xs.length ≤ (replace x ys xs).length := by
  induction xs with
  | nil => simp [replace]
  | cons z zs ih =>
    by_cases hz : z = x
    · subst hz
      simp only [replace]
      rw [if_pos (beq_iff_eq.mpr rfl), List.length_cons, List.length_append]
      omega
    · have hb : (z == x) = false := beq_eq_false_iff_ne.mpr hz
      simp only [replace, hb, List.length_cons]
      exact Nat.succ_le_succ ih

/-- ListAux.thy: replace_append -/
theorem replace_append {x : α} {ys as bs : List α} :
    replace x ys (as ++ bs) =
      if x ∈ as then replace x ys as ++ bs else as ++ replace x ys bs := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.cons_append, replace]
    by_cases ha : a = x
    · subst ha
      simp [List.append_assoc]
    · have hxa : x ≠ a := fun e => ha e.symm
      by_cases hx : x ∈ as
      · simp [ha, hxa, hx, ih]
      · simp [ha, hxa, hx, ih]

/-- ListAux.thy: replace1 -/
theorem replace1 {f f' : α} {fs ls : List α} (h : f ∈ replace f' fs ls) (hn : f ∉ ls) :
    f ∈ fs := by
  induction ls with
  | nil => simp [replace] at h
  | cons l ls ih =>
    simp only [replace] at h
    by_cases hl : l = f'
    · subst hl
      rw [if_pos (beq_iff_eq.mpr rfl)] at h
      rcases List.mem_append.mp h with h | h
      · exact h
      · exact absurd (List.mem_cons_of_mem _ h) hn
    · rw [if_neg (mt beq_iff_eq.mp hl)] at h
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact absurd List.mem_cons_self hn
      · exact ih h fun hmem => hn (List.mem_cons_of_mem _ hmem)

/-- ListAux.thy: replace2 -/
theorem replace2 {f' : α} {fs ls : List α} (h : f' ∉ ls) : replace f' fs ls = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have hl : l ≠ f' := fun e => h (e ▸ List.mem_cons_self)
    have hls : f' ∉ ls := fun hmem => h (List.mem_cons_of_mem _ hmem)
    simp only [replace]
    rw [if_neg (mt beq_iff_eq.mp hl), ih hls]

/-- ListAux.thy: replace3 -/
theorem replace3 {f f' : α} {fs ls : List α} (hf' : f' ∈ ls) (hf : f ∈ fs) :
    f ∈ replace f' fs ls := by
  induction ls with
  | nil => exact absurd hf' (List.not_mem_nil)
  | cons l ls ih =>
    rw [List.mem_cons] at hf'
    simp only [replace]
    by_cases hl : l = f'
    · subst hl
      rw [if_pos (beq_iff_eq.mpr rfl)]
      exact List.mem_append_left _ hf
    · rw [if_neg (mt beq_iff_eq.mp hl)]
      exact List.mem_cons_of_mem _ (ih (hf'.resolve_left (Ne.symm hl)))

/-- ListAux.thy: replace4 -/
theorem replace4 {f oldF : α} {fs ls : List α} (hf : f ∈ ls) (hne : oldF ≠ f) :
    f ∈ replace oldF fs ls := by
  induction ls with
  | nil => exact absurd hf (List.not_mem_nil)
  | cons l ls ih =>
    rw [List.mem_cons] at hf
    simp only [replace]
    by_cases hl : l = oldF
    · subst hl
      rw [if_pos (beq_iff_eq.mpr rfl)]
      rcases hf with hf | hf
      · exact absurd hf (Ne.symm hne)
      · exact List.mem_append_right _ hf
    · rw [if_neg (mt beq_iff_eq.mp hl)]
      rcases hf with rfl | hf
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hf)

/-- ListAux.thy: replace5 -/
theorem replace5 {f oldF : α} {newfs fs : List α} (h : f ∈ replace oldF newfs fs) :
    f ∈ fs ∨ f ∈ newfs := by
  induction fs with
  | nil => simp [replace] at h
  | cons z zs ih =>
    simp only [replace] at h
    by_cases hz : z = oldF
    · subst hz
      rw [if_pos (beq_iff_eq.mpr rfl)] at h
      rcases List.mem_append.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [if_neg (mt beq_iff_eq.mp hz)] at h
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact Or.inl (List.mem_cons_self)
      · rcases ih h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

end Replace

/-! ### mapAt -/

/-- ListAux.thy: length_mapAt -/
@[simp]
theorem length_mapAt {ns : List Nat} {f : α → α} :
    ∀ {as : List α}, (mapAt ns f as).length = as.length := by
  induction ns with
  | nil => intro as; rfl
  | cons n ns ih =>
    intro as
    simp only [mapAt]
    by_cases hn : n < as.length
    · rw [dif_pos hn, ih, List.length_set]
    · rw [dif_neg hn, ih]

/-! ### removeKey / removeKeyList -/

/-- ListAux.thy: removeKey_subset -/
theorem removeKey_subset [BEq α] (a : α) (ps : List (α × β)) : removeKey a ps ⊆ ps :=
  List.filter_sublist.subset

/-- ListAux.thy: removeKeyList_subset -/
theorem removeKeyList_subset [BEq α] (ws : List α) (ps : List (α × β)) :
    removeKeyList ws ps ⊆ ps := by
  induction ws generalizing ps with
  | nil => exact List.Subset.refl _
  | cons w ws ih =>
    exact List.Subset.trans List.filter_sublist.subset (ih _)

/-- ListAux.thy: notin_removeKey1 -/
theorem notin_removeKey1 [BEq α] [LawfulBEq α] (a : α) (b : β) (ps : List (α × β)) :
    (a, b) ∉ removeKey a ps := by
  intro h
  have hmem := (List.mem_filter.mp h).2
  simp at hmem

end Kepler.Graphs
