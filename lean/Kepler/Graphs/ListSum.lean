/-
Port of the Isabelle AFP "Flyspeck-Tame" theory `ListSum.thy`.

Source: `reference/afp-flyspeck-tame/ListSum.thy`
(afp-Flyspeck-Tame-current, downloaded 2026-08-09 from isa-afp.org).

`ListSum xs f` sums `f` over the elements of `xs` (with multiplicities);
it is equal to `(xs.map f).sum` (`ListSum_eq_sum_map`). The Isabelle
notation `∑⇘x ∈ xs⇙ f x` is provided as `∑ₗ x ∈ xs, f x`.

Correspondence notes:
- Lemmas that Isabelle states at type `nat` (`ListSum_compl1/2`,
  `listsum_const`, `ListSum_add`, `ListSum_le`, `ListSum1_bound`,
  `ListSum_disj_union`, the unnamed `[simp]` zero lemma) are ported at
  `Nat`. The congruence lemmas and `ListSum_conv_sum` are generic over
  `AddCommMonoid`, as in Isabelle.
- `strong_listsum_cong` differs from `listsum_cong` only by Isabelle's
  `=simp=>` premise machinery; it is ported as an alias with the same
  (Lean) statement.
- `ListSum_disj_union`: Isabelle's premises `set C = set A ∪ set B` and
  `set A ∩ set B = {}` are rendered pointwise (the project's convention,
  cf. `Tame.lean`).

Bridges to the pre-existing definition layer (which wrote the sums
directly as `(xs.map f).sum`, without this theory):
`ListSum_eq_sum_map` (general) and `faceSquanderLowerBound_eq_ListSum`
(for `Generator.lean`).
-/
import Kepler.Graphs.Generator
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Kepler.Graphs

/-- `ListSum.thy: ListSum`. -/
def ListSum {β : Type*} {α : Type*} [AddCommMonoid α] : List β → (β → α) → α
  | [], _ => 0
  | l :: ls, f => f l + ListSum ls f

@[simp]
theorem ListSum_nil {α : Type*} [AddCommMonoid α] {β : Type*} {f : β → α} :
    ListSum [] f = 0 := rfl

@[simp]
theorem ListSum_cons {α : Type*} [AddCommMonoid α] {β : Type*} {x : β}
    {xs : List β} {f : β → α} :
    ListSum (x :: xs) f = f x + ListSum xs f := rfl

/-- `ListSum.thy`: the notation `∑⇘x ∈ xs⇙ f`. -/
syntax "∑ₗ " ident " ∈ " term ", " term:67 : term
macro_rules
  | `(∑ₗ $x:ident ∈ $xs, $f) => `(ListSum $xs fun $x:ident => $f)

/-- `ListSum.thy`: unnamed `[simp]` lemma `(∑⇘v ∈ V⇙ 0) = 0`. -/
@[simp]
theorem ListSum_zero {β : Type*} (xs : List β) : ListSum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `ListSum.thy: ListSum_compl1`. -/
theorem ListSum_compl1 {β : Type*} (P : β → Bool) (f : β → Nat) (xs : List β) :
    ListSum (xs.filter fun x => !P x) f + ListSum (xs.filter P) f = ListSum xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : P x <;> simp [h, ListSum_cons] <;> omega

/-- `ListSum.thy: ListSum_compl2`. -/
theorem ListSum_compl2 {β : Type*} (P : β → Bool) (f : β → Nat) (xs : List β) :
    ListSum (xs.filter P) f + ListSum (xs.filter fun x => !P x) f = ListSum xs f := by
  rw [Nat.add_comm, ListSum_compl1]

/-- `ListSum.thy: ListSum_conv_sum`. -/
theorem ListSum_conv_sum {α : Type*} [AddCommMonoid α] {β : Type*} [DecidableEq β]
    {xs : List β} (hxs : xs.Nodup) (f : β → α) :
    ListSum xs f = xs.toFinset.sum f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs'⟩ := List.nodup_cons.mp hxs
    rw [ListSum_cons, List.toFinset_cons,
      Finset.sum_insert (by rwa [List.mem_toFinset]), ih hxs']

/-- `ListSum.thy: ListSum_eq` (Isabelle `[trans]`). -/
theorem ListSum_eq {α : Type*} [AddCommMonoid α] {β : Type*} {xs : List β} {f g : β → α}
    (h : ∀ v ∈ xs, f v = g v) :
    ListSum xs f = ListSum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [ListSum_cons, ListSum_cons, h x (by simp),
      ih (fun z hz => h z (by simp [hz]))]

/-- `ListSum.thy: listsum_cong`. -/
theorem listsum_cong {α : Type*} [AddCommMonoid α] {β : Type*} {xs ys : List β}
    {f g : β → α} (h : xs = ys) (hfg : ∀ y ∈ ys, f y = g y) :
    ListSum xs f = ListSum ys g := by
  subst h
  exact ListSum_eq hfg

/-- `ListSum.thy: strong_listsum_cong` (Isabelle `[cong]`; the `=simp=>`
premise is Isabelle-specific, so the Lean statement is that of
`listsum_cong`). -/
theorem strong_listsum_cong {α : Type*} [AddCommMonoid α] {β : Type*} {xs ys : List β}
    {f g : β → α} (h : xs = ys) (hfg : ∀ y ∈ ys, f y = g y) :
    ListSum xs f = ListSum ys g :=
  listsum_cong h hfg

/-- `ListSum.thy: ListSum_disj_union`. -/
theorem ListSum_disj_union {β : Type*} [DecidableEq β] {A B C : List β}
    (hA : A.Nodup) (hB : B.Nodup) (hC : C.Nodup)
    (hun : ∀ x, x ∈ C ↔ x ∈ A ∨ x ∈ B)
    (hdisj : ∀ x, x ∈ A → x ∈ B → False)
    (f : β → Nat) :
    ListSum C f = ListSum A f + ListSum B f := by
  rw [ListSum_conv_sum hC, ListSum_conv_sum hA, ListSum_conv_sum hB]
  have hABC : C.toFinset = A.toFinset ∪ B.toFinset := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_union]
    exact hun x
  have hdj : Disjoint A.toFinset B.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hdisj x (List.mem_toFinset.mp hxA) (List.mem_toFinset.mp hxB)
  rw [hABC, Finset.sum_union hdj]

/-- `ListSum.thy: listsum_const`. -/
@[simp]
theorem listsum_const {β : Type*} (xs : List β) (k : Nat) :
    ListSum xs (fun _ => k) = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    show k + ListSum xs (fun _ => k) = (xs.length + 1) * k
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- `ListSum.thy: ListSum_add`. -/
theorem ListSum_add {β : Type*} (xs : List β) (f g : β → Nat) :
    ListSum xs f + ListSum xs g = ListSum xs fun x => f x + g x := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show f x + ListSum xs f + (g x + ListSum xs g) =
      f x + g x + ListSum xs (fun x => f x + g x)
    omega

/-- `ListSum.thy: ListSum_le`. -/
theorem ListSum_le {β : Type*} {xs : List β} {f g : β → Nat}
    (h : ∀ v ∈ xs, f v ≤ g v) :
    ListSum xs f ≤ ListSum xs g := by
  induction xs with
  | nil => exact Nat.le.refl
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun z hz => h z (by simp [hz])))

/-- `ListSum.thy: ListSum1_bound`. -/
theorem ListSum1_bound {β : Type*} {xs : List β} {d : β → Nat} {a : β} (h : a ∈ xs) :
    d a ≤ ListSum xs d := by
  induction xs with
  | nil => exact (List.not_mem_nil h).elim
  | cons x xs ih =>
    cases List.mem_cons.mp h with
    | inl hx => subst hx; exact Nat.le_add_right ..
    | inr hx => exact Nat.le_trans (ih hx) (Nat.le_add_left ..)

/-! ### Bridges to the pre-existing definition layer -/

/-- Bridge between `ListSum` and the direct `(xs.map f).sum` form used by the
pre-existing definition layer (`Generator.lean`, `Tame.lean`). -/
theorem ListSum_eq_sum_map {α : Type*} [AddCommMonoid α] {β : Type*}
    (xs : List β) (f : β → α) :
    ListSum xs f = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [ListSum_cons, List.map_cons, List.sum_cons, ih]

/-- Bridge for `Generator.lean`: `Generator.thy` defines
`faceSquanderLowerBound g ≡ ∑⇘f ∈ finals g⇙ d |vertices f|`; the existing Lean
definition writes it as `((finals g).map …).sum`. -/
theorem faceSquanderLowerBound_eq_ListSum (g : Graph) :
    faceSquanderLowerBound g = ∑ₗ f ∈ finals g, squanderFace f.vertices.length :=
  (ListSum_eq_sum_map _ _).symm

end Kepler.Graphs
