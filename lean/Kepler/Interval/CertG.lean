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

  TM0 (Phase 5): a third leaf form `taylorLeaf` closes a leaf by the
  **Taylor-model checker** `checkPosTM` (`CertTM.lean`) instead of plain
  interval evaluation — no specialised expression is needed (the TM
  parameters `ps` are separate from the expression, and `evalReal` already
  ignores the in-`IExpr` certificate parameters).
-/
import Kepler.Interval.CertBool
import Kepler.Interval.CertTM

namespace Kepler.Interval

/-- Bisection tree with per-leaf specialised expressions.  Internal nodes
are exactly as in `Cert.BBTree` (box + split dimension). -/
inductive BBTreeG (n : ℕ) (e : IExpr n) : Type where
  | leaf (box : Fin n → DInterval) (el : IExpr n)
      (hsame : el.evalReal = e.evalReal) (hcert : checkPos el box = true) :
      BBTreeG n e
  /-- Taylor-model leaf: closed by `checkPosTM` (kernel-checked Taylor-model
  evaluation of `e` itself — TM parameters live in `ps`, outside the
  expression). -/
  | taylorLeaf (box : Fin n → DInterval) (ps : List SqrtTMP)
      (hcert : checkPosTM e box ps = true) : BBTreeG n e
  | node (box : Fin n → DInterval) (d : Fin n) (l r : BBTreeG n e) :
      BBTreeG n e

namespace BBTreeG

/-- The box of a node (root included). -/
def box {n : ℕ} {e : IExpr n} : BBTreeG n e → (Fin n → DInterval)
  | .leaf b _ _ _ => b
  | .taylorLeaf b _ _ => b
  | .node b _ _ _ => b

/-- The covering checker (Prop-level), same shape as `BBTree.covers`. -/
def covers {n : ℕ} {e : IExpr n} : BBTreeG n e → Prop
  | .leaf _ _ _ _ => True
  | .taylorLeaf _ _ _ => True
  | .node b d l r => splitOK b d l.box r.box ∧ l.covers ∧ r.covers

/-- **Point-coverage**: a covering tree places every real point of its own
box inside some leaf, together with that leaf's positivity evidence (interval
check or Taylor-model check, already applied). -/
theorem covers_point {n : ℕ} {e : IExpr n} (t : BBTreeG n e)
    (hcov : t.covers) {ρ : Fin n → ℝ} (hρ : boxMem t.box ρ) :
    ∃ (box : Fin n → DInterval) (el : IExpr n),
      el.evalReal = e.evalReal ∧ boxMem box ρ ∧
        ∀ σ, boxMem box σ → 0 < el.evalReal σ := by
  induction t with
  | leaf box el hsame hcert =>
    exact ⟨box, el, hsame, hρ, fun σ hσ => checkPos_sound el box hcert σ hσ⟩
  | taylorLeaf box ps hcert =>
    exact ⟨box, e, rfl, hρ, fun σ hσ => checkPosTM_sound hcert σ hσ⟩
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
  | .taylorLeaf _ _ _ => true
  | .node b d l r => Bool.and (splitOKB b d l.box r.box) (Bool.and l.coversB r.coversB)

/-- **Soundness of `coversB`**. -/
theorem coversB_sound {n : ℕ} {e : IExpr n} (t : BBTreeG n e)
    (h : t.coversB = true) : t.covers := by
  induction t with
  | leaf b el hsame hcert => trivial
  | taylorLeaf b ps hcert => trivial
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
  obtain ⟨box, el, hsame, hmem, hpos⟩ :=
    t.covers_point hcov (boxSub_mem hsub hρ)
  rw [← hsame]
  exact hpos ρ hmem

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

/-! ## TM0 pilots: Taylor-model leaves (`CertTM.lean`)

Two acceptance cases of the TM0 milestone
(`pipeline/interval/taylor-model-design.md` §4 row 1): the sqrt pilot
re-closed by a single `taylorLeaf` at the root, and `x² − 2 > 0` adjacent to
`√2` closed by a depth-1 `taylorLeaf` tree. -/

/-- The sqrt pilot `√x − x/4` in TM-checkable form: `x/4` written as
`x · 2⁻²` (division by a dyadic constant is multiplication by its inverse —
TM0's `evalTM` does not support `.div`).  Same real semantics as `exGExpr`. -/
def exGExprTM : IExpr 1 := .sub (.sqrt (.var 0) 1 1) (.mul (.var 0) (.const ⟨1, -2⟩))

theorem exGExprTM_same : exGExprTM.evalReal = exGExpr.evalReal := by
  funext ρ
  simp only [exGExprTM, exGExpr, IExpr.evalReal]
  rw [Dyadic.toReal_int]
  have h1 : (⟨1, -2⟩ : Dyadic).toReal = 1 / 4 := by
    rw [Dyadic.toReal_def]
    norm_num
  rw [h1]
  ring

/-- TM certificate bundle for the sqrt node on `[1,2]` (center `3/2`, center
enclosure the point `⟨3,-1⟩`, envelope `1/2`, certified lower bound `c = 1`):
`√(3·2⁻¹)` mantissa `2 = ⌊√6⌋` (used twice — point enclosure), `√1` mantissa
`2 = ⌊√4⌋`, recip granularities `2⁻³` (slope `1/(2√(3/2))`) and `2⁻²`
(curvature `1/(8·1·1)`). -/
def exGTMP : List SqrtTMP := [⟨2, 2, 2, -3, -2⟩]

/-- The single-leaf TM tree closes the whole box `[1,2]` at the root — the
two-leaf bare-interval bisection of `exGTree` is unnecessary here (kernel
`decide`). -/
theorem exGTM_cert : checkPosTM exGExprTM exGBox exGTMP = true := by decide

/-- One-leaf Taylor-model tree for `√x − x/4` on `[1,2]`. -/
def exGTreeTM : BBTreeG 1 exGExprTM := .taylorLeaf exGBox exGTMP exGTM_cert

theorem exGTreeTM_covers : exGTreeTM.covers := BBTreeG.coversB_sound _ (by decide)

/-- End-to-end: `0 < √x − x/4` for every real `x ∈ [1,2]`, via the TM leaf. -/
theorem exGTM_end_to_end (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    0 < Real.sqrt x - x / 4 := by
  have hsub : boxSub exGBox exGTreeTM.box := by
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
  have h := bb_soundG exGTreeTM exGBox exGTreeTM_covers hsub (fun _ => x) hmem
  rw [exGExprTM_same] at h
  have hsimp : exGExpr.evalReal (fun _ => x) = Real.sqrt x - x / 4 := by
    simp only [exGExpr, IExpr.evalReal]
    rw [Dyadic.toReal_int]
    norm_num
  rwa [hsimp] at h

#print axioms exGTM_end_to_end

/-! ### `x² − 2 > 0` adjacent to `√2` -/

/-- `x·x − 2`. -/
def exTM2Expr : IExpr 1 := .sub (.mul (.var 0) (.var 0)) (.const ⟨2, 0⟩)

/-- Root box `[2897/2048, 3/2]` — `2897/2048 ≈ 1.41430664` is the dyadic just
above `√2 ≈ 1.41421356` at denominator `2¹¹` (and `2897² = 8392609 >
8388608 = 2·2048²`). -/
def exTM2Box : Fin 1 → DInterval := fun _ => ⟨⟨2897, -11⟩, ⟨3, -1⟩⟩

/-- The two halves, defined through `mid` so `splitOKB` closes by `decide`. -/
def exTM2BoxL : Fin 1 → DInterval := fun _ => ⟨(exTM2Box 0).lo, (exTM2Box 0).mid⟩
def exTM2BoxR : Fin 1 → DInterval := fun _ => ⟨(exTM2Box 0).mid, (exTM2Box 0).hi⟩

/-- The root box does NOT close under `checkPosTM`: the Taylor lower bound at
the root is `y² − 2 − 2yw − w² < 0` (the `O(w²)` remainder swamps the
`≈ 9.5·10⁻⁴` margin).  One bisection layer suffices: both halves close
(kernel `decide`). -/
theorem exTM2Root_fails : checkPosTM exTM2Expr exTM2Box [] = false := by decide
theorem exTM2L_cert : checkPosTM exTM2Expr exTM2BoxL [] = true := by decide
theorem exTM2R_cert : checkPosTM exTM2Expr exTM2BoxR [] = true := by decide

/-- Depth-1 Taylor-model tree for `x² − 2` on `[2897/2048, 3/2]`. -/
def exTM2Tree : BBTreeG 1 exTM2Expr :=
  .node exTM2Box 0 (.taylorLeaf exTM2BoxL [] exTM2L_cert)
    (.taylorLeaf exTM2BoxR [] exTM2R_cert)

theorem exTM2Tree_covers : exTM2Tree.covers := BBTreeG.coversB_sound _ (by decide)

/-- For the record: plain interval evaluation is *exact* for `x·x` on positive
boxes, so it closes even the root box here — the TM route's advantage is
quantitative (leaf counts on dependency-losing leaves), not qualitative for
this expression (see `pipeline/interval/tm0-progress.md`). -/
theorem exTM2Root_bare : checkPos exTM2Expr exTM2Box = true := by decide

/-- End-to-end: `0 < x² − 2` for every real `x ∈ [2897/2048, 3/2]`. -/
theorem exTM2_end_to_end (x : ℝ) (hx1 : 2897 / 2048 ≤ x) (hx2 : x ≤ 3 / 2) :
    0 < x * x - 2 := by
  have hsub : boxSub exTM2Box exTM2Tree.box := by
    intro i
    fin_cases i
    exact ⟨by decide, by decide⟩
  have hmem : boxMem exTM2Box (fun _ => x) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨2897, -11⟩ ≤ x
      rw [Dyadic.toReal_def]
      have h : (((2897 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-11 : ℤ)) = 2897 / 2048 := by norm_num
      rw [h]
      exact hx1
    · show x ≤ Dyadic.toReal ⟨3, -1⟩
      rw [Dyadic.toReal_def]
      have h : (((3 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-1 : ℤ)) = 3 / 2 := by norm_num
      rw [h]
      exact hx2
  have h := bb_soundG exTM2Tree exTM2Box exTM2Tree_covers hsub (fun _ => x) hmem
  simpa [exTM2Expr, IExpr.evalReal] using h

#print axioms exTM2_end_to_end

end Kepler.Interval
