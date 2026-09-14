/-
  Phase 4, G4: **generalized branch-and-bound certificates** with
  per-leaf specialized expressions (`BBTreeG`).

  `Cert.BBTree` pins ONE expression `e` for the whole tree.  That is too
  rigid for the certificate-parameterised `IExpr` nodes: `.sqrt e s₁ s₂`
  bakes the two root mantissas into the expression, but the radicand
  interval (whose endpoints they must match) varies from leaf to leaf —
  so no single global `(s₁, s₂)` can certify `√` on every leaf of a
  bisection.  The same applies, in principle, to the `.div` granularity
  and `.trans` Taylor order.

  The way out: `IExpr.evalReal` **ignores the certificate parameters**
  (`.sqrt e _ _ ↦ √(evalReal e)`, `.div e₁ e₂ _ ↦ e₁/e₂`,
  `.trans k e _ _ ↦ transReal k (evalReal e)`), so a per-leaf
  *specialised* expression `el` that differs from `e` only in those
  parameters has — definitionally — the same real semantics.  A
  `BBTreeG` leaf carries such an `el` together with

  - `hsame : el.evalReal = e.evalReal` (closed by `rfl` for
    parameter-only differences), and
  - `hcert : checkPos el box = true` (the kernel check, with `el`'s
    per-leaf parameters filled in by the generator).

  Soundness (`bb_soundG`) then yields `0 < e.evalReal ρ` for the global
  expression, exactly like `Cert.bb_sound`.

  Kernel checks only: no `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.CertBool

namespace Kepler.Interval

/-- Bisection tree with per-leaf specialised expressions.  Internal nodes
are exactly as in `Cert.BBTree` (box + split dimension). -/
inductive BBTreeG (n : ℕ) (e : IExpr n) : Type where
  | leaf (box : Fin n → DInterval) (el : IExpr n)
      (hsame : el.evalReal = e.evalReal) (hcert : checkPos el box = true) :
      BBTreeG n e
  | node (box : Fin n → DInterval) (d : Fin n) (l r : BBTreeG n e) :
      BBTreeG n e

namespace BBTreeG

/-- The box of a node (root included). -/
def box {n : ℕ} {e : IExpr n} : BBTreeG n e → (Fin n → DInterval)
  | .leaf b _ _ _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop-level), same shape as `BBTree.covers`. -/
def covers {n : ℕ} {e : IExpr n} : BBTreeG n e → Prop
  | .leaf _ _ _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- **Point-coverage**: a covering tree places every real point of its own
box inside some leaf (with that leaf's specialised expression and cert). -/
theorem covers_point {n : ℕ} {e : IExpr n} (t : BBTreeG n e)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval) (el : IExpr n),
      el.evalReal = e.evalReal ∧ checkPos el box = true ∧ boxMem box ρ := by
  induction t with
  | leaf box el hsame hcert => exact ⟨box, el, hsame, hcert, hρ⟩
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
def coversB {n : ℕ} {e : IExpr n} : BBTreeG n e → Bool
  | .leaf _ _ _ _ => true
  | .node b d l r => Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `coversB`**. -/
theorem coversB_sound {n : ℕ} {e : IExpr n} (t : BBTreeG n e)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b el hsame hcert => trivial
  | node b d l r ihl ihr =>
    have h' : Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hs, hl, hr⟩ := h'
    exact ⟨splitOKB_sound hs, ihl hl, ihr hr⟩

end BBTreeG

/-- **Soundness of generalised branch-and-bound certificates**: a covering
tree whose root contains the target box proves positivity of the global
expression at every point of the target. -/
theorem bb_soundG {n : ℕ} {e : IExpr n} (t : BBTreeG n e)
    (target : Fin n → DInterval) (hcov : t.covers) (hsub : boxSub target t.box)
    (ρ : Fin n → ℝ) (hρ : boxMem target ρ) : 0 < e.evalReal ρ := by
  obtain ⟨box, el, hsame, hcert, hmem⟩ :=
    t.covers_point hcov (boxSub_mem hsub hρ)
  rw [← hsame]
  exact checkPos_sound el box hcert ρ hmem

/-! ## Pilot: per-leaf sqrt mantissas on `√x − x/4 > 0` over `[1,2]`

Whole-box interval evaluation of `√x − x/4` needs the sqrt certificate
`⌊√1⌋ = 1` / `⌊√2⌋ = 1` (mantissas at the endpoints' scale).  We split
`[1,2]` at `3/2`; the two leaves use *different* mantissa pairs
(`(1,1)` on `[1,3/2]` vs `(1,1)`… the point is the mechanism: each leaf
carries its own `.sqrt` parameters). -/

/-- The global expression `√x − x/4` (parameters irrelevant to semantics). -/
def exGExpr : IExpr 1 := .sub (.sqrt (.var 0) 1 1) (.div (.var 0) (.const ⟨4, 0⟩) (-64))

/-- Left leaf `[1, 3/2]`: radicand box `[1, 3/2]` — mantissas `1 = ⌊√1⌋`, `2 = ⌊√6⌋`
(`3/2 = ⟨3,-1⟩` scales to `3·2 = 6`). -/
def exGLeafL : IExpr 1 := .sub (.sqrt (.var 0) 1 2) (.div (.var 0) (.const ⟨4, 0⟩) (-64))

/-- Right leaf `[3/2, 2]`: radicand box `[3/2, 2]` — mantissas `2 = ⌊√6⌋`, `1 = ⌊√2⌋`. -/
def exGLeafR : IExpr 1 := .sub (.sqrt (.var 0) 2 1) (.div (.var 0) (.const ⟨4, 0⟩) (-64))

/-- Box `[1,2]` and its halves. -/
def exGBox : Fin 1 → DInterval := fun _ => ⟨⟨1, 0⟩, ⟨2, 0⟩⟩
def exGBoxL : Fin 1 → DInterval := fun _ => ⟨⟨1, 0⟩, ⟨3, -1⟩⟩
def exGBoxR : Fin 1 → DInterval := fun _ => ⟨⟨3, -1⟩, ⟨2, 0⟩⟩

/-- The specialised expressions coincide with the global one over `ℝ`
(definitionally — only certificate parameters could differ). -/
theorem exGLeafL_same : exGLeafL.evalReal = exGExpr.evalReal := rfl
theorem exGLeafR_same : exGLeafR.evalReal = exGExpr.evalReal := rfl

/-- Left leaf certificate: on `[1, 3/2]`, `√x − x/4 ∈ [1 − 3/8, …]`, lo > 0. -/
theorem exGLeafL_cert : checkPos exGLeafL exGBoxL = true := by decide

/-- Right leaf certificate: on `[3/2, 2]`, `√x − x/4 ∈ [1 − 1/2, …]`, lo > 0. -/
theorem exGLeafR_cert : checkPos exGLeafR exGBoxR = true := by decide

/-- The two-leaf generalised tree. -/
def exGTree : BBTreeG 1 exGExpr :=
  .node exGBox 0 (.leaf exGBoxL exGLeafL exGLeafL_same exGLeafL_cert)
    (.leaf exGBoxR exGLeafR exGLeafR_same exGLeafR_cert)

/-- Covering via the Bool checker, one `decide`. -/
theorem exGTree_covers : exGTree.covers :=
  BBTreeG.coversB_sound _ (by decide)

/-- End-to-end: `0 < √x − x/4` for every real `x ∈ [1,2]`. -/
theorem exG_end_to_end (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    0 < Real.sqrt x - x / 4 := by
  have hsub : boxSub exGBox exGTree.box := by
    intro i
    fin_cases i
    exact ⟨by decide, by decide⟩
  have hmem : boxMem exGBox (fun _ => x) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨1, 0⟩ ≤ x
      rw [Dyadic.toReal_int]
      exact_mod_cast hx1
    · show x ≤ Dyadic.toReal ⟨2, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  have h := bb_soundG exGTree exGBox exGTree_covers hsub (fun _ => x) hmem
  have hsimp : exGExpr.evalReal (fun _ => x) = Real.sqrt x - x / 4 := by
    simp only [exGExpr, IExpr.evalReal]
    rw [Dyadic.toReal_int]
    norm_num
  rwa [hsimp] at h

#print axioms exG_end_to_end

end Kepler.Interval
