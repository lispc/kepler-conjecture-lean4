/-
  Phase 4 prep P2: **mixed main/TM branch-and-bound certificates**.

  `Cert.BBTree` closes every leaf with the plain interval checker
  `checkPos`; `CertG.BBTreeG` additionally supports per-leaf specialised
  expressions and Taylor-model leaves, but its module also carries old
  sqrt/TM pilots that no longer re-bake after the SF-42 sqrtRel change and
  is outside the default build closure.

  This module is the minimal kernel piece needed by the prep re-solve lane:
  one tree with two leaf kinds, both on the *same* global expression `e`:

  * `.leaf box hcert`       with `hcert : checkPos e box = true`
  * `.taylorLeaf box ps hcert` with `hcert : checkPosTM e box ps = true`

  Exactly `CertG`'s `BBTreeG` without the per-leaf specialised-expression
  field (`hsame` is `rfl` there for our polynomial cases anyway).  Soundness
  is the same two-line case split over `checkPos_sound` / `checkPosTM_sound`.

  Kernel checks only: no `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.CertBool
import Kepler.Interval.CertTM

namespace Kepler.Interval

/-- Bisection tree with mixed plain-interval and Taylor-model leaves on a
single global expression. -/
inductive BBTreeM (n : ℕ) (e : IExpr n) : Type where
  | leaf (box : Fin n → DInterval) (hcert : checkPos e box = true) :
      BBTreeM n e
  /-- Taylor-model leaf: closed by `checkPosTM` (kernel-checked). -/
  | taylorLeaf (box : Fin n → DInterval) (ps : TMParams)
      (hcert : checkPosTM e box ps = true) : BBTreeM n e
  | node (box : Fin n → DInterval) (d : Fin n) (l r : BBTreeM n e) :
      BBTreeM n e

namespace BBTreeM

/-- The box of a node (root included). -/
def box {n : ℕ} {e : IExpr n} : BBTreeM n e → (Fin n → DInterval)
  | .leaf b _ => b
  | .taylorLeaf b _ _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop-level), same shape as `BBTree.covers`. -/
def covers {n : ℕ} {e : IExpr n} : BBTreeM n e → Prop
  | .leaf _ _ => True
  | .taylorLeaf _ _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- **Point-coverage**: a covering tree places every real point of its own
box inside some leaf carrying a positivity certificate for `e`. -/
theorem covers_point {n : ℕ} {e : IExpr n} (t : BBTreeM n e)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval),
      boxMem box ρ ∧ ∀ σ, boxMem box σ → 0 < e.evalReal σ := by
  induction t with
  | leaf box hcert =>
    exact ⟨box, hρ, fun σ hσ => checkPos_sound e box hcert σ hσ⟩
  | taylorLeaf box ps hcert =>
    exact ⟨box, hρ, fun σ hσ => checkPosTM_sound hcert σ hσ⟩
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

/-- Bool-valued cover checker (same shape as `BBTree.coversB`). -/
def coversB {n : ℕ} {e : IExpr n} : BBTreeM n e → Bool
  | .leaf _ _ => true
  | .taylorLeaf _ _ _ => true
  | .node b d l r =>
      Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `coversB`**. -/
theorem coversB_sound {n : ℕ} {e : IExpr n} (t : BBTreeM n e)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b hcert => trivial
  | taylorLeaf b ps hcert => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box)
        (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

end BBTreeM

/-- **Soundness of mixed branch-and-bound certificates**: a covering tree
whose root contains the target box proves positivity of the expression at
every point of the target. -/
theorem bb_soundM {n : ℕ} {e : IExpr n} (t : BBTreeM n e)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) : 0 < e.evalReal ρ := by
  obtain ⟨box, hmem, hpos⟩ := t.covers_point hcov (boxSub_mem hsub hρ)
  exact hpos ρ hmem

end Kepler.Interval
