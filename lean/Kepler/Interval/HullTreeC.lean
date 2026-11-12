/-
  Schema-v3 (`--hull`, CertTM `checkPosTMHullC`) **full-coverage** certificate
  trees: the hull-leaf analogue of `CertG`'s `BBTreeG` + `bb_soundG`.

  `BBTreeG` has two leaf constructors — interval (`checkPos`) and Taylor-model
  (`checkPosTM`, the strict `evalTM` evaluator, which returns `none` on a
  guard-straddling `ite`).  The `bb_arb --ite-hull2` driver closes such leaves
  through the *guard-decided hull* checker `checkPosTMHullC`
  (`evalTMHullD2`, CertTM M2b/schema-v3), so a certificate emitted from a
  `--tm --ite-hull2` certificate cannot use `BBTreeG.taylorLeaf`.

  This file is the missing piece: `HullTreeC` carries `checkPosTMHullC` leaves
  and reuses the *same* split-certificate layer (`splitOKB`, Bool-valued, one
  kernel `decide` over the whole tree) and the same `covers_point` argument as
  `BBTreeG`.  Nothing here changes an existing definition; `BBTreeG`,
  `BBTreeG.covers_point` and `bb_soundG` are untouched.

  No new axioms, no `sorry`, no `native_decide`: the only evaluation is the
  kernel `decide +kernel` in the generated instance modules.
-/
import Kepler.Interval.CertBool
import Kepler.Interval.CertTM

namespace Kepler.Interval

/-- Bisection tree whose leaves are `checkPosTMHullC` (df-hull Taylor model)
certificates.  Same node shape as `BBTreeG`: the node box, the split
dimension, the two children. -/
inductive HullTreeC (n : ℕ) (e : IExpr n) : Type where
  | leaf (box : Fin n → DInterval) (ps : TMParams)
      (hcert : checkPosTMHullC e box ps = true) : HullTreeC n e
  | node (box : Fin n → DInterval) (d : Fin n) (l r : HullTreeC n e) :
      HullTreeC n e

namespace HullTreeC

/-- The box of a node (root included). -/
def box {n : ℕ} {e : IExpr n} : HullTreeC n e → (Fin n → DInterval)
  | .leaf b _ _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop level), same shape as `BBTreeG.covers`. -/
def covers {n : ℕ} {e : IExpr n} : HullTreeC n e → Prop
  | .leaf _ _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- Bool-valued cover checker (mirrors `covers`; the split layer is the
shared `splitOKB`, so a whole tree is checked by one kernel `decide`). -/
def coversB {n : ℕ} {e : IExpr n} : HullTreeC n e → Bool
  | .leaf _ _ _ => true
  | .node b d l r =>
      Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `coversB`**: a passing Bool check yields the `Prop`
cover certificate. -/
theorem coversB_sound {n : ℕ} {e : IExpr n} (t : HullTreeC n e)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b _ hcert => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box)
        (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

/-- **Point-coverage**: a covering tree places every real point of its own box
inside some leaf, together with that leaf's positivity evidence (the hull
Taylor-model check, already applied).  Verbatim the `BBTreeG.covers_point`
argument with `checkPosTMHullC_sound` in the leaf case. -/
theorem covers_point {n : ℕ} {e : IExpr n} (t : HullTreeC n e)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval),
      boxMem box ρ ∧ ∀ σ, boxMem box σ → 0 < e.evalReal σ := by
  induction t with
  | leaf box _ hcert =>
    exact ⟨box, hρ, fun σ hσ => checkPosTMHullC_sound hcert σ hσ⟩
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

end HullTreeC

/-- **End-to-end soundness**: the case expression is strictly positive on any
box contained in the tree's root box (the `bb_soundG` analogue, with the
`checkPosTMHullC` leaf case discharged by `HullTreeC.covers_point`). -/
theorem hull_soundC {n : ℕ} {e : IExpr n} (t : HullTreeC n e)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) : 0 < e.evalReal ρ := by
  obtain ⟨box, hmem, hpos⟩ :=
    t.covers_point hcov (boxSub_mem hsub hρ)
  exact hpos ρ hmem

namespace HullTreeC

/-- Alias of `hull_soundC` under the tree's own namespace (generated modules
call `Tree.sound`). -/
theorem sound {n : ℕ} {e : IExpr n} (t : HullTreeC n e)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) : 0 < e.evalReal ρ :=
  hull_soundC t target hcov hsub ρ hρ

end HullTreeC

end Kepler.Interval
