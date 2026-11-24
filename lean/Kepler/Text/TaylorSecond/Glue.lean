/-
Kepler.Text.TaylorSecond.Glue — lane `wt1-phaseb-glue-w1` (2026-11-24).

Core covering/glue kernel for the Route B leaf-covering emission layer
(`scripts/gen_glue.py`).

Geometry.  A parent box `Box lo hi` is bisected along one axis `j` at
`m = (lo j + hi j) / 2`:

* lower/left child  `Box lo (Function.update hi j m)`,  i.e. `[lo j, m]`;
* upper/right child `Box (Function.update lo j m) hi`,  i.e. `[m, hi j]`.

The split transfer lemmas (`mem_box_update_hi`, `mem_box_update_lo`) and the
covering combinator (`box_glue`) are stated with the raw `Function.update`
form so that a generated node theorem can apply a child theorem verbatim: the
emitter writes every child box as a `def` whose body is *syntactically* that
`Function.update` term, hence the child's statement matches by delta only — no
per-node arithmetic in the emitted proof term.

Statement orientation (ERRATA vs. the work order, item A): the work order
wrote `x ∈ Box lo hi → x j ≤ mid → x ∈ Box (update lo j mid) hi`; that is false
as written, because `Box (update lo j mid) hi` is the *upper* half `[mid, hi j]`.
The correct pair is `x j ≤ mid → x ∈ Box lo (update hi j mid)` (lower half) and
`mid ≤ x j → x ∈ Box (update lo j mid) hi` (upper half).  Implemented below in
the correct orientation; see GLUE_SPEC.md section 1.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Basic

set_option maxHeartbeats 1000000

namespace Kepler.Text.TaylorSecond

variable {n : ℕ}

/-! ## 0. Unfolding `Box` and `Function.update` -/

/-- Membership in a coordinate box, unfolded (definitional). -/
theorem mem_box_iff {lo hi : Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ Box lo hi ↔ ∀ i, x i ∈ Set.Icc (lo i) (hi i) :=
  Iff.rfl

/-- Pointwise `Function.update` at the updated index. -/
theorem update_self {hi : Fin n → ℝ} {j : Fin n} {m : ℝ} :
    Function.update hi j m j = m := by
  rw [Function.update_apply, if_pos rfl]

/-- Pointwise `Function.update` away from the updated index. -/
theorem update_of_ne {hi : Fin n → ℝ} {j i : Fin n} {m : ℝ} (h : i ≠ j) :
    Function.update hi j m i = hi i := by
  rw [Function.update_apply, if_neg h]

/-! ## 1. Split transfer: parent box + side condition ⇒ child box -/

/-- Lower half of the split transfer: a point of `Box lo hi` with `x j ≤ m`
lies in the lower child box `[lo j, m]`. -/
theorem mem_box_update_hi {lo hi : Fin n → ℝ} {j : Fin n} {m : ℝ} {x : Fin n → ℝ}
    (hx : x ∈ Box lo hi) (hj : x j ≤ m) :
    x ∈ Box lo (Function.update hi j m) := by
  intro i
  have h := hx i
  rw [Function.update_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    exact ⟨h.1, hij ▸ hj⟩
  · rw [if_neg hij]
    exact h

/-- Upper half of the split transfer: a point of `Box lo hi` with `m ≤ x j`
lies in the upper child box `[m, hi j]`. -/
theorem mem_box_update_lo {lo hi : Fin n → ℝ} {j : Fin n} {m : ℝ} {x : Fin n → ℝ}
    (hx : x ∈ Box lo hi) (hj : m ≤ x j) :
    x ∈ Box (Function.update lo j m) hi := by
  intro i
  have h := hx i
  rw [Function.update_apply]
  by_cases hij : i = j
  · rw [if_pos hij]
    exact ⟨hij ▸ hj, h.2⟩
  · rw [if_neg hij]
    exact h

/-! ## 2. Child boxes are contained in the parent box -/

/-- The lower child box (with `m` inside `[lo j, hi j]`) is contained in the
parent box.  This is the direction consumed by nested emission: a leaf box is
contained in every ancestor box. -/
theorem box_update_hi_subset {lo hi : Fin n → ℝ} {j : Fin n} {m : ℝ}
    (hlo : lo j ≤ m) (hhi : m ≤ hi j) :
    Box lo (Function.update hi j m) ⊆ Box lo hi := by
  intro x hx i
  have h := hx i
  rw [Function.update_apply] at h
  by_cases hij : i = j
  · rw [if_pos hij] at h
    exact ⟨h.1, le_trans h.2 (hij ▸ hhi)⟩
  · rw [if_neg hij] at h
    exact h

/-- The upper child box (with `m` inside `[lo j, hi j]`) is contained in the
parent box. -/
theorem box_update_lo_subset {lo hi : Fin n → ℝ} {j : Fin n} {m : ℝ}
    (hlo : lo j ≤ m) (hhi : m ≤ hi j) :
    Box (Function.update lo j m) hi ⊆ Box lo hi := by
  intro x hx i
  have h := hx i
  rw [Function.update_apply] at h
  by_cases hij : i = j
  · rw [if_pos hij] at h
    exact ⟨le_trans (hij ▸ hlo) h.1, h.2⟩
  · rw [if_neg hij] at h
    exact h

/-! ## 3. The covering combinator -/

/-- **Glue rule.**  If a predicate holds on both halves of a box bisected at
`m` (which may be any real, in particular the rational midpoint), then it holds
on the whole box.  This is the single kernel lemma the emitter's internal-node
theorems apply. -/
theorem box_glue {lo hi : Fin n → ℝ} {j : Fin n} {m : ℝ}
    {P : (Fin n → ℝ) → Prop}
    (hL : ∀ x ∈ Box lo (Function.update hi j m), P x)
    (hR : ∀ x ∈ Box (Function.update lo j m) hi, P x) :
    ∀ x ∈ Box lo hi, P x := by
  intro x hx
  by_cases h : x j ≤ m
  · exact hL x (mem_box_update_hi hx h)
  · exact hR x (mem_box_update_lo hx (le_of_lt (lt_of_not_ge h)))

/-! ## 4. Generic transports (for child boxes given by independent literals) -/

/-- Monotonicity: shrinking a box preserves membership.  Use this when a child
box is stated with its own rational literals instead of the `Function.update`
form (the "flat literal" leaf interface). -/
theorem mem_box_of_le {lo hi lo' hi' : Fin n → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ Box lo hi) (hlo : ∀ i, lo' i ≤ lo i) (hhi : ∀ i, hi i ≤ hi' i) :
    x ∈ Box lo' hi' := by
  intro i
  exact ⟨le_trans (hlo i) (hx i).1, le_trans (hx i).2 (hhi i)⟩

/-- Box inclusion from pointwise corner monotonicity. -/
theorem box_subset_of_le {lo hi lo' hi' : Fin n → ℝ}
    (hlo : ∀ i, lo' i ≤ lo i) (hhi : ∀ i, hi i ≤ hi' i) :
    Box lo hi ⊆ Box lo' hi' :=
  fun _ hx => mem_box_of_le hx hlo hhi

/-- Box equality from corner equality; the bridge a leaf theorem needs when it
is stated over flat rational literals rather than the emitted `Function.update`
defs. -/
theorem box_congr {lo hi lo' hi' : Fin n → ℝ}
    (hl : ∀ i, lo i = lo' i) (hh : ∀ i, hi i = hi' i) :
    Box lo hi = Box lo' hi' := by
  refine Set.Subset.antisymm ?_ ?_
  · exact box_subset_of_le (fun i => le_of_eq (hl i).symm) (fun i => le_of_eq (hh i))
  · exact box_subset_of_le (fun i => le_of_eq (hl i)) (fun i => le_of_eq (hh i).symm)

/-- Cornerwise membership extraction, named for readability in generated files. -/
theorem mem_box_apply {lo hi : Fin n → ℝ} {x : Fin n → ℝ}
    (hx : x ∈ Box lo hi) (i : Fin n) : x i ∈ Set.Icc (lo i) (hi i) :=
  hx i

/-! ## 5. Audit -/

#print axioms mem_box_iff
#print axioms update_self
#print axioms update_of_ne
#print axioms mem_box_update_hi
#print axioms mem_box_update_lo
#print axioms box_update_hi_subset
#print axioms box_update_lo_subset
#print axioms box_glue
#print axioms mem_box_of_le
#print axioms box_subset_of_le
#print axioms box_congr
#print axioms mem_box_apply

end Kepler.Text.TaylorSecond
