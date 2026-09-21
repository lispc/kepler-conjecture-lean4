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
  | taylorLeaf (box : Fin n → DInterval) (ps : TMParams)
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
def exGTMP : TMParams := ⟨[⟨2, 2, 2, -3, -2⟩], []⟩

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
theorem exTM2Root_fails : checkPosTM exTM2Expr exTM2Box .empty = false := by decide
theorem exTM2L_cert : checkPosTM exTM2Expr exTM2BoxL .empty = true := by decide
theorem exTM2R_cert : checkPosTM exTM2Expr exTM2BoxR .empty = true := by decide

/-- Depth-1 Taylor-model tree for `x² − 2` on `[2897/2048, 3/2]`. -/
def exTM2Tree : BBTreeG 1 exTM2Expr :=
  .node exTM2Box 0 (.taylorLeaf exTM2BoxL .empty exTM2L_cert)
    (.taylorLeaf exTM2BoxR .empty exTM2R_cert)

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

/-! ## TM1 pilots: multivariate critical boxes (dependency loss, sqrt, div)

Three TM1 acceptance cases (`pipeline/interval/tm1-progress.md`): a 2-D box
where plain interval evaluation loses the `x`/`y` dependency and fails at the
root while the TM closes it outright; a 3-D box with a `sqrt` node whose
certificate granularity defeats bare interval evaluation at the root; and a
2-D box with a `div` node closed by a depth-2 `taylorLeaf` tree. -/

/-- A: `x·y − x − y + 1 + 1/64` — bare interval evaluation on
`[15/16, 17/16]²` gives `w² − 4w + 1/64 < 0` at the root (O(w) dependency
loss); the TM linear term vanishes at the center `(1,1)` and the remainder is
`w² = 1/256 < 1/64`, so the root closes. -/
def exTM1AExpr : IExpr 2 :=
  .add (.add (.sub (.sub (.mul (.var 0) (.var 1)) (.var 0)) (.var 1)) (.const ⟨1, 0⟩))
    (.const ⟨1, -6⟩)

/-- Box `[15/16, 17/16]²`. -/
def exTM1ABox : Fin 2 → DInterval := fun _ => ⟨⟨15, -4⟩, ⟨17, -4⟩⟩

theorem exTM1A_bare_root : checkPos exTM1AExpr exTM1ABox = false := by decide
theorem exTM1A_cert : checkPosTM exTM1AExpr exTM1ABox .empty = true := by decide

/-- One-leaf TM tree (the root itself). -/
def exTM1ATree : BBTreeG 2 exTM1AExpr := .taylorLeaf exTM1ABox .empty exTM1A_cert

theorem exTM1ATree_covers : exTM1ATree.covers := BBTreeG.coversB_sound _ (by decide)

/-- End-to-end: `0 < x·y − x − y + 1 + 1/64` on `[15/16, 17/16]²`. -/
theorem exTM1A_end_to_end (x y : ℝ) (hx0 : 15 / 16 ≤ x) (hx1 : x ≤ 17 / 16)
    (hy0 : 15 / 16 ≤ y) (hy1 : y ≤ 17 / 16) : 0 < x * y - x - y + 1 + 1 / 64 := by
  have hmem : boxMem exTM1ABox ![x, y] := by
    intro i
    fin_cases i
    · show DInterval.mem ⟨⟨15, -4⟩, ⟨17, -4⟩⟩ x
      constructor <;>
        · rw [Dyadic.toReal_def]
          first | (have h : (((15 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-4 : ℤ)) = 15 / 16 := by norm_num
                   rw [h]; exact hx0)
                | (have h : (((17 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-4 : ℤ)) = 17 / 16 := by norm_num
                   rw [h]; exact hx1)
    · show DInterval.mem ⟨⟨15, -4⟩, ⟨17, -4⟩⟩ y
      constructor <;>
        · rw [Dyadic.toReal_def]
          first | (have h : (((15 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-4 : ℤ)) = 15 / 16 := by norm_num
                   rw [h]; exact hy0)
                | (have h : (((17 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-4 : ℤ)) = 17 / 16 := by norm_num
                   rw [h]; exact hy1)
  have hsub : boxSub exTM1ABox exTM1ATree.box := by
    intro i
    fin_cases i <;> exact ⟨by decide, by decide⟩
  have h := bb_soundG exTM1ATree exTM1ABox exTM1ATree_covers hsub ![x, y] hmem
  have hsimp : exTM1AExpr.evalReal ![x, y] = x * y - x - y + 1 + (1 / 64 : ℝ) := by
    simp only [exTM1AExpr, IExpr.evalReal, Dyadic.toReal_int]
    rw [Dyadic.toReal_def]
    norm_num
  rwa [hsimp] at h

#print axioms exTM1A_end_to_end

/-- B: `√(x² + y² + 1) − z` on `[−1/8, 1/8]² × [7/8, 15/16]` — the bare
interval sqrt certificate at the root box's scale (`⌊√62⌋ = 7` at `2⁻³`) is
too coarse (lo = `7/8 − 15/16 < 0`); the TM's center evaluation is a point
(`√1 = 1`) and the remainder is `≈ 0.018 < 1/16`, so the root closes.  The
bundle: `√(256·2⁻⁸)` mantissa `16`, `√(248·2⁻⁸)` mantissa `15`, recip
granularities `2⁻⁴`/`2⁻¹²`. -/
def exTM1BExpr : IExpr 3 :=
  .sub (.sqrt (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (.const ⟨1, 0⟩)) 7 8)
    (.var 2)

/-- Box `[−1/8, 1/8]² × [7/8, 15/16]`. -/
def exTM1BBox : Fin 3 → DInterval := fun i =>
  if i = 2 then ⟨⟨7, -3⟩, ⟨15, -4⟩⟩ else ⟨⟨-1, -3⟩, ⟨1, -3⟩⟩

/-- TM certificates for B's sqrt node. -/
def exTM1BP : TMParams := ⟨[⟨16, 16, 31, -4, -12⟩], []⟩

theorem exTM1B_bare_root : checkPos exTM1BExpr exTM1BBox = false := by decide
theorem exTM1B_cert : checkPosTM exTM1BExpr exTM1BBox exTM1BP = true := by decide

/-- One-leaf TM tree (the root itself). -/
def exTM1BTree : BBTreeG 3 exTM1BExpr := .taylorLeaf exTM1BBox exTM1BP exTM1B_cert

theorem exTM1BTree_covers : exTM1BTree.covers := BBTreeG.coversB_sound _ (by decide)

/-- End-to-end: `0 < √(x² + y² + 1) − z` on the box. -/
theorem exTM1B_end_to_end (x y z : ℝ) (hx0 : -1 / 8 ≤ x) (hx1 : x ≤ 1 / 8)
    (hy0 : -1 / 8 ≤ y) (hy1 : y ≤ 1 / 8) (hz0 : 7 / 8 ≤ z) (hz1 : z ≤ 15 / 16) :
    0 < Real.sqrt (x * x + y * y + 1) - z := by
  have hmem : boxMem exTM1BBox ![x, y, z] := by
    intro i
    fin_cases i
    · show DInterval.mem ⟨⟨-1, -3⟩, ⟨1, -3⟩⟩ x
      constructor <;> rw [Dyadic.toReal_def]
      · have h : (((-1 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-3 : ℤ)) = -1 / 8 := by norm_num
        rw [h]; exact hx0
      · have h : (((1 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-3 : ℤ)) = 1 / 8 := by norm_num
        rw [h]; exact hx1
    · show DInterval.mem ⟨⟨-1, -3⟩, ⟨1, -3⟩⟩ y
      constructor <;> rw [Dyadic.toReal_def]
      · have h : (((-1 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-3 : ℤ)) = -1 / 8 := by norm_num
        rw [h]; exact hy0
      · have h : (((1 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-3 : ℤ)) = 1 / 8 := by norm_num
        rw [h]; exact hy1
    · show DInterval.mem ⟨⟨7, -3⟩, ⟨15, -4⟩⟩ z
      constructor <;> rw [Dyadic.toReal_def]
      · have h : (((7 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-3 : ℤ)) = 7 / 8 := by norm_num
        rw [h]; exact hz0
      · have h : (((15 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-4 : ℤ)) = 15 / 16 := by norm_num
        rw [h]; exact hz1
  have hsub : boxSub exTM1BBox exTM1BTree.box := by
    intro i
    fin_cases i <;> exact ⟨by decide, by decide⟩
  have h := bb_soundG exTM1BTree exTM1BBox exTM1BTree_covers hsub ![x, y, z] hmem
  have hsimp : exTM1BExpr.evalReal ![x, y, z] = Real.sqrt (x * x + y * y + 1) - z := by
    simp [exTM1BExpr, IExpr.evalReal, Dyadic.toReal_int]
  rwa [hsimp] at h

#print axioms exTM1B_end_to_end

/-- C: `x/(1 + y) − 7/16` on `[1, 3/2]×[1/2, 1]` — the TM root fails
(linear term swamps the `1/16`-scale margin) and the depth-2 tree
(x-split, then y-split) closes; exercises the `div` rule (`valid_div`). -/
def exTM1CExpr : IExpr 2 :=
  .sub (.div (.var 0) (.add (.const ⟨1, 0⟩) (.var 1)) (-64)) (.const ⟨7, -4⟩)

/-- Box `[1, 3/2]×[1/2, 1]` and its quadrants (via `mid`, so `splitOKB`
closes by `decide`). -/
def exTM1CBox : Fin 2 → DInterval := fun i =>
  if i = 0 then ⟨⟨1, 0⟩, ⟨3, -1⟩⟩ else ⟨⟨1, -1⟩, ⟨1, 0⟩⟩
def exTM1CBoxL : Fin 2 → DInterval := fun i =>
  if i = 0 then ⟨(exTM1CBox 0).lo, (exTM1CBox 0).mid⟩ else exTM1CBox i
def exTM1CBoxR : Fin 2 → DInterval := fun i =>
  if i = 0 then ⟨(exTM1CBox 0).mid, (exTM1CBox 0).hi⟩ else exTM1CBox i
def exTM1CBoxLL : Fin 2 → DInterval := fun i =>
  if i = 1 then ⟨(exTM1CBox 1).lo, (exTM1CBox 1).mid⟩ else exTM1CBoxL i
def exTM1CBoxLR : Fin 2 → DInterval := fun i =>
  if i = 1 then ⟨(exTM1CBox 1).mid, (exTM1CBox 1).hi⟩ else exTM1CBoxL i
def exTM1CBoxRL : Fin 2 → DInterval := fun i =>
  if i = 1 then ⟨(exTM1CBox 1).lo, (exTM1CBox 1).mid⟩ else exTM1CBoxR i
def exTM1CBoxRR : Fin 2 → DInterval := fun i =>
  if i = 1 then ⟨(exTM1CBox 1).mid, (exTM1CBox 1).hi⟩ else exTM1CBoxR i

/-- Reciprocal granularities (uniform: fine enough at every leaf). -/
def exTM1CP : TMParams := ⟨[], [⟨-12, -12, -12⟩]⟩

theorem exTM1C_root_fails : checkPosTM exTM1CExpr exTM1CBox exTM1CP = false := by decide
theorem exTM1C_LL : checkPosTM exTM1CExpr exTM1CBoxLL exTM1CP = true := by decide
theorem exTM1C_LR : checkPosTM exTM1CExpr exTM1CBoxLR exTM1CP = true := by decide
theorem exTM1C_RL : checkPosTM exTM1CExpr exTM1CBoxRL exTM1CP = true := by decide
theorem exTM1C_RR : checkPosTM exTM1CExpr exTM1CBoxRR exTM1CP = true := by decide

/-- Depth-2 TM tree for C. -/
def exTM1CTree : BBTreeG 2 exTM1CExpr :=
  .node exTM1CBox 0
    (.node exTM1CBoxL 1 (.taylorLeaf exTM1CBoxLL exTM1CP exTM1C_LL)
      (.taylorLeaf exTM1CBoxLR exTM1CP exTM1C_LR))
    (.node exTM1CBoxR 1 (.taylorLeaf exTM1CBoxRL exTM1CP exTM1C_RL)
      (.taylorLeaf exTM1CBoxRR exTM1CP exTM1C_RR))

theorem exTM1CTree_covers : exTM1CTree.covers := BBTreeG.coversB_sound _ (by decide)

/-- End-to-end: `0 < x/(1+y) − 7/16` on `[1, 3/2]×[1/2, 1]`. -/
theorem exTM1C_end_to_end (x y : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ 3 / 2)
    (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 1) : 0 < x / (1 + y) - 7 / 16 := by
  have hmem : boxMem exTM1CBox ![x, y] := by
    intro i
    fin_cases i
    · show DInterval.mem ⟨⟨1, 0⟩, ⟨3, -1⟩⟩ x
      constructor
      · rw [Dyadic.toReal_int]; exact_mod_cast hx0
      · rw [Dyadic.toReal_def]
        have h : (((3 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-1 : ℤ)) = 3 / 2 := by norm_num
        rw [h]; exact hx1
    · show DInterval.mem ⟨⟨1, -1⟩, ⟨1, 0⟩⟩ y
      constructor
      · rw [Dyadic.toReal_def]
        have h : (((1 : ℤ) : ℝ)) * (2 : ℝ) ^ ((-1 : ℤ)) = 1 / 2 := by norm_num
        rw [h]; exact hy0
      · rw [Dyadic.toReal_int]; exact_mod_cast hy1
  have hsub : boxSub exTM1CBox exTM1CTree.box := by
    intro i
    fin_cases i <;> exact ⟨by decide, by decide⟩
  have h := bb_soundG exTM1CTree exTM1CBox exTM1CTree_covers hsub ![x, y] hmem
  have hsimp : exTM1CExpr.evalReal ![x, y] = x / (1 + y) - (7 / 16 : ℝ) := by
    simp only [exTM1CExpr, IExpr.evalReal, Dyadic.toReal_int]
    rw [Dyadic.toReal_def]
    norm_num
  rwa [hsimp] at h

#print axioms exTM1C_end_to_end

end Kepler.Interval
