/-
  Generic cover tree whose leaves are **already-proven pointwise positivity
  theorems** `∀ σ, boxMem box σ → 0 < e.evalReal σ`.

  This is the leaf-theorem analogue of `HullTree`/`HullTreeC` (which carry a
  `checkPosTMHull`/`checkPosTMHullC` certificate — box, params and the kernel
  `decide` — inline in each leaf).  It exists so a large certificate can be
  assembled from *separate leaf modules* without re-inlining their `TMParams`
  in the tree: each leaf cites the leaf module's `_pos` theorem by name, and
  the tree adds only the split/coverage layer (`splitOK`/`splitOKB`, shared
  with `Cert`/`CertBool`).

  Nothing here changes an existing definition; `HullTree`, `BBTree` and the
  `splitOKB` layer are untouched.  No new axioms, no `sorry`, no
  `native_decide`: the only evaluation is the kernel `decide +kernel` in the
  generated instance modules.

  Prepared by lane tskasm-prep-w1 (2026-11-16); mechanical sibling of the
  landed `Kepler/Interval/HullTree.lean`.
-/
import Kepler.Interval.CertBool

namespace Kepler.Interval

/-- Bisection tree whose leaves are pointwise positivity theorems.
Same node shape as `HullTree`/`BBTree`: the node box, the split dimension,
the two children. -/
inductive PosTree (n : ℕ) (e : IExpr n) : Type where
  | leaf (box : Fin n → DInterval)
      (hpos : ∀ σ, boxMem box σ → 0 < e.evalReal σ) : PosTree n e
  | node (box : Fin n → DInterval) (d : Fin n) (l r : PosTree n e) :
      PosTree n e

namespace PosTree

/-- The box of a node (root included). -/
def box {n : ℕ} {e : IExpr n} : PosTree n e → (Fin n → DInterval)
  | .leaf b _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop level), same shape as `HullTree.covers`. -/
def covers {n : ℕ} {e : IExpr n} : PosTree n e → Prop
  | .leaf _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- Bool-valued cover checker (mirrors `covers`; the split layer is the
shared `splitOKB`, so a whole tree is checked by one kernel `decide`). -/
def coversB {n : ℕ} {e : IExpr n} : PosTree n e → Bool
  | .leaf _ _ => true
  | .node b d l r =>
      Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `coversB`**: a passing Bool check yields the `Prop`
cover certificate. -/
theorem coversB_sound {n : ℕ} {e : IExpr n} (t : PosTree n e)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b hpos => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box)
        (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

/-- **Point-coverage**: a covering tree places every real point of its own
box inside some leaf, together with that leaf's positivity evidence.
Verbatim the `HullTree.covers_point` argument with the theorem-leaf case. -/
theorem covers_point {n : ℕ} {e : IExpr n} (t : PosTree n e)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval),
      boxMem box ρ ∧ ∀ σ, boxMem box σ → 0 < e.evalReal σ := by
  induction t with
  | leaf box hpos =>
    exact ⟨box, hρ, hpos⟩
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
            exact le_of_lt (not_le.mp hcase)
          · show ρ i ≤ (r.box i).hi.toReal
            rw [hsplit.2.2.2.2]
            exact (hρ i).2
        · have hri : r.box i = box i := (hsplit.1 i hid).2
          rw [hri]
          exact hρ i
      exact ihr hrcov hρr

end PosTree

/-- **End-to-end soundness**: the case expression is strictly positive on any
box contained in the tree's root box (the `hull_sound` analogue, with the
theorem-leaf case discharged by `PosTree.covers_point`). -/
theorem posTree_sound {n : ℕ} {e : IExpr n} (t : PosTree n e)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) : 0 < e.evalReal ρ := by
  obtain ⟨box, hmem, hpos⟩ :=
    t.covers_point hcov (boxSub_mem hsub hρ)
  exact hpos ρ hmem

namespace PosTree

/-- Alias of `posTree_sound` under the tree's own namespace (generated
modules call `Tree.sound`). -/
theorem sound {n : ℕ} {e : IExpr n} (t : PosTree n e)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) : 0 < e.evalReal ρ :=
  posTree_sound t target hcov hsub ρ hρ

end PosTree

end Kepler.Interval
