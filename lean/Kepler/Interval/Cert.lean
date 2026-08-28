/-
  Phase 4, step 6: **branch-and-bound certificate trees** — the box-splitting
  layer on top of the `IExpr` positivity checker
  (`Kepler.Interval.Expr.checkPos_sound`).

  Interval evaluation is conservative (e.g. `x²` on `[-1,1]` evaluates to
  `[-1,1]`, not `[0,1]`), so a whole-box `checkPos` can fail on a true
  inequality.  The branch-and-bound answer: bisect the box and re-check the
  leaves.  This file defines the *certificate format* and proves its
  **soundness**; actually running large bisections is a generator's job
  (off-kernel), exactly like the root mantissas of `Dyadic.sqrtI`.

  ## The format

  - `BBTree n e`: a leaf carries a box together with its kernel-checked
    certificate `checkPos e box = true` (a `Bool` equality — `decide`
    closes it); an internal node carries its box, the split dimension
    `d : Fin n`, and the two children.
  - `splitOK box d bl br`: the children are the *exact halves* of the parent
    along `d` — outside `d` they agree with the parent, and the `d`-th
    intervals are `[lo, mid]` / `[mid, hi]` with `mid` the exact dyadic
    midpoint `(lo + hi)/2` (`DInterval.mid`, an exponent decrement — no
    rounding).
  - `BBTree.covers`: recursively, every node splits correctly down to its
    leaves; all predicates are dyadic equalities, so `decide` can verify
    the covering structure of a concrete tree in the kernel.

  ## Soundness

  `bb_sound`: if the tree covers itself, the root box contains the target
  box (`boxSub target t.box`), and `ρ` is pointwise in the target, then
  `0 < e.evalReal ρ` — because some leaf of the tree contains `ρ` pointwise
  (`covers_point`) and that leaf's certificate is a `checkPos` success.

  No `sorry`, no `native_decide`, no new axioms; kernel checks only.
-/
import Kepler.Interval.Expr

namespace Kepler.Interval

/-! ## Boxes -/

/-- Real membership in a box (pointwise interval membership). -/
def boxMem {n : ℕ} (box : Fin n → DInterval) (ρ : Fin n → ℝ) : Prop :=
  ∀ i, (box i).mem (ρ i)

/-- Box containment `b ⊆ t` (pointwise endpoint comparisons, expressed via
the kernel-decidable `Dyadic.ble`). -/
def boxSub {n : ℕ} (b t : Fin n → DInterval) : Prop :=
  ∀ i, Dyadic.ble (t i).lo (b i).lo = true ∧ Dyadic.ble (b i).hi (t i).hi = true

/-- Containment transports real membership: `b ⊆ t` and `ρ ∈ b` give `ρ ∈ t`. -/
theorem boxSub_mem {n : ℕ} {b t : Fin n → DInterval} {ρ : Fin n → ℝ}
    (hsub : boxSub b t) (hρ : boxMem b ρ) : boxMem t ρ := by
  intro i
  obtain ⟨h1, h2⟩ := hρ i
  obtain ⟨ha, hb⟩ := hsub i
  exact ⟨le_trans (Dyadic.ble_toReal ha) h1, le_trans h2 (Dyadic.ble_toReal hb)⟩

/-! ## Exact dyadic bisection -/

namespace DInterval

/-- The exact dyadic midpoint `(lo + hi)/2` (the center of `midRadius`;
halving is an exponent decrement, so no rounding occurs). -/
def mid (I : DInterval) : Dyadic := I.midRadius.c

theorem toReal_mid (I : DInterval) : I.mid.toReal * 2 = I.lo.toReal + I.hi.toReal :=
  I.midRadius_center

end DInterval

/-- Split certificate: `bl`/`br` are exactly the two halves of `box` along
dimension `d` — outside `d` they agree with `box`, and the `d`-th intervals
are `[lo, mid]` resp. `[mid, hi]`.  All components are equalities of dyadic
structures (kernel-decidable). -/
def splitOK {n : ℕ} (box : Fin n → DInterval) (d : Fin n)
    (bl br : Fin n → DInterval) : Prop :=
  (∀ i, i ≠ d → bl i = box i ∧ br i = box i) ∧
    (bl d).lo = (box d).lo ∧ (bl d).hi = (box d).mid ∧
      (br d).lo = (box d).mid ∧ (br d).hi = (box d).hi

/-! ## The branch-and-bound tree -/

/-- Bisection tree for the positivity check of `e : IExpr n`.  A leaf carries
its box and the kernel-checked certificate `checkPos e box = true`; an
internal node carries its box, the split dimension and both children. -/
inductive BBTree (n : ℕ) (e : IExpr n) : Type where
  | leaf (box : Fin n → DInterval) (h : checkPos e box = true) : BBTree n e
  | node (box : Fin n → DInterval) (d : Fin n) (l r : BBTree n e) : BBTree n e

namespace BBTree

/-- The box of a node (root included). -/
def box {n : ℕ} {e : IExpr n} : BBTree n e → (Fin n → DInterval)
  | .leaf b _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop-level): every internal node's children are its
exact halves, recursively; leaves trivially cover themselves.  For concrete
trees this is kernel-`decide`able. -/
def covers {n : ℕ} {e : IExpr n} : BBTree n e → Prop
  | .leaf _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- **Point-coverage**: a covering tree places every real point of its own box
inside some leaf (with that leaf's certificate). -/
theorem covers_point {n : ℕ} {e : IExpr n} (t : BBTree n e)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ box : Fin n → DInterval, checkPos e box = true ∧ boxMem box ρ := by
  induction t with
  | leaf box hcert => exact ⟨box, hcert, hρ⟩
  | node box d l r ihl ihr =>
    obtain ⟨hsplit, hlcov, hrcov⟩ := hcov
    by_cases hcase : ρ d ≤ (box d).mid.toReal
    · have hρl : boxMem l.box ρ := by
        intro i
        by_cases hid : i = d
        · subst hid
          constructor
          · show (l.box i).lo.toReal ≤ ρ i
            rw [hsplit.2.1]
            exact (hρ i).1
          · show ρ i ≤ (l.box i).hi.toReal
            rw [hsplit.2.2.1]
            exact hcase
        · have hli : l.box i = box i := (hsplit.1 i hid).1
          rw [hli]
          exact hρ i
      exact ihl hlcov hρl
    · have hρr : boxMem r.box ρ := by
        intro i
        by_cases hid : i = d
        · subst hid
          constructor
          · show (r.box i).lo.toReal ≤ ρ i
            rw [hsplit.2.2.2.1]
            exact le_of_lt (lt_of_not_ge hcase)
          · show ρ i ≤ (r.box i).hi.toReal
            rw [hsplit.2.2.2.2]
            exact (hρ i).2
        · have hri : r.box i = box i := (hsplit.1 i hid).2
          rw [hri]
          exact hρ i
      exact ihr hrcov hρr

end BBTree

/-- **Soundness of branch-and-bound certificates**: if the tree covers
itself, its root box contains the target box, and `ρ` is pointwise inside
the target, then the expression is strictly positive at `ρ`. -/
theorem bb_sound {n : ℕ} {e : IExpr n} (t : BBTree n e) (target : Fin n → DInterval)
    (hcov : t.covers) (hsub : boxSub target t.box) (ρ : Fin n → ℝ)
    (hρ : boxMem target ρ) : 0 < e.evalReal ρ := by
  obtain ⟨box, hcert, hmem⟩ :=
    t.covers_point hcov (boxSub_mem hsub hρ)
  exact checkPos_sound e box hcert ρ hmem

/-! ## Pilot: a two-leaf bisection of `[0,2]` (kernel `decide` only) -/

/-- `f(x) = x² − x + 2`: on the whole box `[0,2]` the conservative interval
evaluation gives `[0−2+2, 4−0+2] = [0,6]` — the lower endpoint is `0`, so
the whole-box check *fails* and a split is required. -/
def exExprBB : IExpr 1 :=
  .add (.sub (.mul (.var 0) (.var 0)) (.var 0)) (.const ⟨2, 0⟩)

/-- The root box `[0,2]`. -/
def exBoxBB : Fin 1 → DInterval := fun _ => ⟨⟨0, 0⟩, ⟨2, 0⟩⟩

/-- The left leaf `[0,1]` — the exact midpoint of `[0,2]` is the dyadic
`⟨2,-1⟩ = 1`. -/
def exLeafL : Fin 1 → DInterval := fun _ => ⟨⟨0, 0⟩, ⟨2, -1⟩⟩

/-- The right leaf `[1,2]`. -/
def exLeafR : Fin 1 → DInterval := fun _ => ⟨⟨2, -1⟩, ⟨2, 0⟩⟩

/-- Whole-box reject (kernel `decide`): `f` on `[0,2]` evaluates to `[0,6]`,
lower endpoint not positive — the bisection motivation. -/
theorem exBB_whole_reject : checkPos exExprBB exBoxBB = false := by decide

/-- Left-leaf accept (kernel `decide`): `f` on `[0,1]` evaluates to `[1,3]`. -/
theorem exBB_leafL_accept : checkPos exExprBB exLeafL = true := by decide

/-- Right-leaf accept (kernel `decide`): `f` on `[1,2]` evaluates to `[1,5]`. -/
theorem exBB_leafR_accept : checkPos exExprBB exLeafR = true := by decide

/-- The two-leaf certificate (root `[0,2]`, split along the only dimension). -/
def exTree : BBTree 1 exExprBB :=
  .node exBoxBB 0 (.leaf exLeafL exBB_leafL_accept) (.leaf exLeafR exBB_leafR_accept)

/-- The covering structure itself is kernel-verified: both children are the
exact halves of the root (the midpoint `mid [0,2] = ⟨2,-1⟩` and all endpoint
equalities are computed and checked by kernel `decide`). -/
theorem exTree_covers : exTree.covers := by
  show splitOK exBoxBB 0 exLeafL exLeafR ∧ True ∧ True
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, trivial, trivial⟩
  · intro i hi
    fin_cases i
    exact absurd rfl hi
  · decide
  · decide
  · decide
  · decide

/-- End-to-end: `0 < x² − x + 2` for every real `x ∈ [0,2]` — the whole-box
check fails (`[0,6]`), the two-leaf certificate succeeds. -/
theorem exBB_end_to_end (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x ≤ 2) :
    0 < x * x - x + 2 := by
  have hsub : boxSub exBoxBB exTree.box := by
    intro i
    fin_cases i
    constructor <;> decide
  have hmem : boxMem exBoxBB (fun _ => x) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨0, 0⟩ ≤ x
      rw [Dyadic.toReal_int]
      exact_mod_cast hx1
    · show x ≤ Dyadic.toReal ⟨2, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  have h := bb_sound exTree exBoxBB exTree_covers hsub (fun _ => x) hmem
  have hsimp : exExprBB.evalReal (fun _ => x) = x * x - x + 2 := by
    simp only [exExprBB, IExpr.evalReal]
    norm_num
  rwa [hsimp] at h

end Kepler.Interval
