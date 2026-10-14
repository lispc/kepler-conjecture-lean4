/-
  W7: the `evalReal` chain rule and the mono-corner lemma — the Lean-kernel
  side of the W6a "route A" monotonicity reduction (see
  `docs/scouts/mono-corner-scout.md` §5 and the `--mono` block of
  `pipeline/interval/emit_lean.py`).

  Route A says: if the symbolic partial derivative `∂ⱼ f` of the leaf
  expression is sign-definite on a (guard-decided) sub-box, then `f` attains
  its minimum on the corresponding extreme face, so a positivity certificate
  at the corner point lifts to the whole box.  This file makes that a kernel
  theorem chain:

  - `IExpr.derivExpr e j` — the symbolic partial derivative of `e` along
    coordinate `j`, as an `IExpr` again (const/var/neg/add/sub/mul/div/
    sqrt/arctan/ite rules, mirroring the emitter's `_mono_diff`).  The
    kernel computes it itself — the Python-side derivative is search-only
    and is never trusted.
  - `IExpr.derivSafe` — the node whitelist (`derivExpr` is meaningful
    exactly there: no `.abs`, and arctan is the only trans kind).
  - `DomOK` — the pointwise domain premises (divisor `≠ 0`, radicand `> 0`,
    `ite` guard sign-definite on the box).
  - `hasDeriv_sliceEval` / `evalReal_deriv` — the per-op chain rule: the box
    slice `x ↦ e.evalReal (σ with j ↦ x)` has derivative
    `(derivExpr e j).evalReal σ` at every interior point.
  - `continuousOn_sliceEval` — the slice is `ContinuousOn` the closed
    interval (continuity side of the monotonicity transfer).
  - `slice_strict_incr` / `slice_strict_decr` — sign-definite derivative on
    the box ⇒ every slice is monotone
    (`monotoneOn_of_hasDerivWithinAt_nonneg`).
  - `monoCorner_le` — the n-dimensional telescope: moving each coordinate to
    its certified extreme face never increases `f`.
  - `checkMonoCorner` — the total assembly in checker form: per-dimension
    `checkPosTMHull` certificates on `derivExpr e j` (or its negation), a
    `checkPosTMHull` certificate at the corner point box, and a point in the
    box give `0 < e.evalReal ρ` — all premises kernel-`decide`-able
    statements of exactly the form the `--mono-lean` emitter produces.

  Checking layer: `Int` arithmetic + Mathlib real analysis.  No `sorry`,
  no native-decide shortcut, no new axioms.
-/
import Kepler.Interval.CertTM

-- `Set.Icc`/`Set.Ioo` and the `𝓝` / `=ᶠ[·]` notations
open Set Filter Topology

namespace Kepler.Interval

/-! ## The symbolic partial derivative -/

/-- Symbolic partial derivative of `e` along coordinate `j`, as an `IExpr`.
Product/quotient/chain rules; an `ite` differentiates both branches inside
the same guard (sound: on a guard-decided box the guard's own derivative is
irrelevant and the selected branch is fixed).  The `.abs` and the
`sinK`/`cosK`/`lnK` trans arms return the junk `0` — they are excluded from
the soundness theorem by `derivSafe` below (in the current 549 leaf progs
`abs` sits only in the constant-folded region and the only trans kind is
arctan; scout §5.4). -/
def IExpr.derivExpr {n : ℕ} : IExpr n → Fin n → IExpr n
  | .const _, _ => .const ⟨0, 0⟩
  | .var i, j => if i = j then .const ⟨1, 0⟩ else .const ⟨0, 0⟩
  | .neg e, j => .neg (e.derivExpr j)
  | .abs _, _ => .const ⟨0, 0⟩
  | .ite c t e, j => .ite c (t.derivExpr j) (e.derivExpr j)
  | .add e₁ e₂, j => .add (e₁.derivExpr j) (e₂.derivExpr j)
  | .sub e₁ e₂, j => .sub (e₁.derivExpr j) (e₂.derivExpr j)
  | .mul e₁ e₂, j =>
      .add (.mul (e₁.derivExpr j) e₂) (.mul e₁ (e₂.derivExpr j))
  | .div e₁ e₂ out, j =>
      .div (.sub (.mul (e₁.derivExpr j) e₂) (.mul e₁ (e₂.derivExpr j)))
        (.mul e₂ e₂) out
  | .sqrt e s₁ s₂, j =>
      .div (e.derivExpr j) (.mul (.const ⟨2, 0⟩) (.sqrt e s₁ s₂)) 0
  | .trans .arctanK e _ _, j =>
      .div (e.derivExpr j) (.add (.const ⟨1, 0⟩) (.mul e e)) 0
  | .trans _ _ _ _, _ => .const ⟨0, 0⟩

/-- The node whitelist of `derivExpr`: no `.abs`, and `arctanK` is the only
transcendental kind. -/
def IExpr.derivSafe {n : ℕ} : IExpr n → Bool
  | .const _ => true
  | .var _ => true
  | .neg e => e.derivSafe
  | .abs _ => false
  | .ite c t e => c.derivSafe && t.derivSafe && e.derivSafe
  | .add e₁ e₂ => e₁.derivSafe && e₂.derivSafe
  | .sub e₁ e₂ => e₁.derivSafe && e₂.derivSafe
  | .mul e₁ e₂ => e₁.derivSafe && e₂.derivSafe
  | .div e₁ e₂ _ => e₁.derivSafe && e₂.derivSafe
  | .sqrt e _ _ => e.derivSafe
  | .trans .arctanK e _ _ => e.derivSafe
  | .trans _ _ _ _ => false

/-! ## Domain premises -/

/-- Pointwise domain premises for differentiating (and evaluating) `e` over
the box: divisors stay away from `0`, square-root radicands stay positive,
and every `ite` guard is sign-definite on the whole box (uniformly, so the
selected branch is the same at every point of the box). -/
inductive DomOK {n : ℕ} (box : Fin n → DInterval) : IExpr n → Prop
  | const {d} : DomOK box (.const d)
  | var {i} : DomOK box (.var i)
  | neg {e : IExpr n} : DomOK box e → DomOK box (.neg e)
  | abs {e : IExpr n} : DomOK box e → DomOK box (.abs e)
  | ite {c t e : IExpr n} :
      (∀ σ, boxMem box σ → c.evalReal σ < 0) ∨
        (∀ σ, boxMem box σ → 0 ≤ c.evalReal σ) →
      DomOK box t → DomOK box e → DomOK box (.ite c t e)
  | add {e₁ e₂ : IExpr n} :
      DomOK box e₁ → DomOK box e₂ → DomOK box (.add e₁ e₂)
  | sub {e₁ e₂ : IExpr n} :
      DomOK box e₁ → DomOK box e₂ → DomOK box (.sub e₁ e₂)
  | mul {e₁ e₂ : IExpr n} :
      DomOK box e₁ → DomOK box e₂ → DomOK box (.mul e₁ e₂)
  | div {e₁ e₂ : IExpr n} {out} :
      (∀ σ, boxMem box σ → e₂.evalReal σ ≠ 0) →
      DomOK box e₁ → DomOK box e₂ → DomOK box (.div e₁ e₂ out)
  | sqrt {e : IExpr n} {s₁ s₂} :
      (∀ σ, boxMem box σ → 0 < e.evalReal σ) →
      DomOK box e → DomOK box (.sqrt e s₁ s₂)
  | trans {k : TKind} {e : IExpr n} {N out} :
      DomOK box e → DomOK box (.trans k e N out)

/-- Field inversions of `DomOK` (proved at top level with core `cases`;
the induction bodies below only use these term-level). -/
theorem DomOK.neg_inv {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    (h : DomOK box (.neg e)) : DomOK box e := by
  cases h with
  | neg h1 => exact h1

theorem DomOK.ite_inv_dec {n : ℕ} {box : Fin n → DInterval} {c t e : IExpr n}
    (h : DomOK box (.ite c t e)) :
      (∀ σ, boxMem box σ → c.evalReal σ < 0) ∨
        (∀ σ, boxMem box σ → 0 ≤ c.evalReal σ) := by
  cases h with
  | ite h0 _ _ => exact h0

theorem DomOK.ite_inv_then {n : ℕ} {box : Fin n → DInterval} {c t e : IExpr n}
    (h : DomOK box (.ite c t e)) : DomOK box t := by
  cases h with
  | ite _ h1 _ => exact h1

theorem DomOK.ite_inv_else {n : ℕ} {box : Fin n → DInterval} {c t e : IExpr n}
    (h : DomOK box (.ite c t e)) : DomOK box e := by
  cases h with
  | ite _ _ h2 => exact h2

theorem DomOK.add_inv_left {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    (h : DomOK box (.add e₁ e₂)) : DomOK box e₁ := by
  cases h with
  | add h1 _ => exact h1

theorem DomOK.add_inv_right {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    (h : DomOK box (.add e₁ e₂)) : DomOK box e₂ := by
  cases h with
  | add _ h2 => exact h2

theorem DomOK.sub_inv_left {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    (h : DomOK box (.sub e₁ e₂)) : DomOK box e₁ := by
  cases h with
  | sub h1 _ => exact h1

theorem DomOK.sub_inv_right {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    (h : DomOK box (.sub e₁ e₂)) : DomOK box e₂ := by
  cases h with
  | sub _ h2 => exact h2

theorem DomOK.mul_inv_left {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    (h : DomOK box (.mul e₁ e₂)) : DomOK box e₁ := by
  cases h with
  | mul h1 _ => exact h1

theorem DomOK.mul_inv_right {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    (h : DomOK box (.mul e₁ e₂)) : DomOK box e₂ := by
  cases h with
  | mul _ h2 => exact h2

theorem DomOK.div_inv_hz {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    {out} (h : DomOK box (.div e₁ e₂ out)) :
    ∀ σ, boxMem box σ → e₂.evalReal σ ≠ 0 := by
  cases h with
  | div h0 _ _ => exact h0

theorem DomOK.div_inv_left {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    {out} (h : DomOK box (.div e₁ e₂ out)) : DomOK box e₁ := by
  cases h with
  | div _ h1 _ => exact h1

theorem DomOK.div_inv_right {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    {out} (h : DomOK box (.div e₁ e₂ out)) : DomOK box e₂ := by
  cases h with
  | div _ _ h2 => exact h2

theorem DomOK.sqrt_inv_pos {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    {s₁ s₂} (h : DomOK box (.sqrt e s₁ s₂)) :
    ∀ σ, boxMem box σ → 0 < e.evalReal σ := by
  cases h with
  | sqrt h0 _ => exact h0

theorem DomOK.sqrt_inv {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    {s₁ s₂} (h : DomOK box (.sqrt e s₁ s₂)) : DomOK box e := by
  cases h with
  | sqrt _ h1 => exact h1

theorem DomOK.div_inv_all {n : ℕ} {box : Fin n → DInterval} {e₁ e₂ : IExpr n}
    {out} (h : DomOK box (.div e₁ e₂ out)) :
    (∀ σ, boxMem box σ → e₂.evalReal σ ≠ 0) ∧ DomOK box e₁ ∧ DomOK box e₂ := by
  cases h with
  | div h0 h1 h2 => exact ⟨h0, h1, h2⟩

theorem DomOK.sqrt_inv_all {n : ℕ} {box : Fin n → DInterval} {e : IExpr n}
    {s₁ s₂} (h : DomOK box (.sqrt e s₁ s₂)) :
    (∀ σ, boxMem box σ → 0 < e.evalReal σ) ∧ DomOK box e := by
  cases h with
  | sqrt h0 h1 => exact ⟨h0, h1⟩

theorem DomOK.trans_inv {n : ℕ} {box : Fin n → DInterval} {k : TKind}
    {e : IExpr n} {N out} (h : DomOK box (.trans k e N out)) : DomOK box e := by
  cases h with
  | trans h1 => exact h1

/-- Expressions without `div`/`sqrt`/`trans`/`ite` nodes satisfy `DomOK` on
every box (the discharge route the `--mono-lean` emitter uses). -/
def IExpr.domTrivial {n : ℕ} : IExpr n → Bool
  | .const _ => true
  | .var _ => true
  | .neg e => e.domTrivial
  | .abs e => e.domTrivial
  | .ite .. => false
  | .add e₁ e₂ => e₁.domTrivial && e₂.domTrivial
  | .sub e₁ e₂ => e₁.domTrivial && e₂.domTrivial
  | .mul e₁ e₂ => e₁.domTrivial && e₂.domTrivial
  | .div .. => false
  | .sqrt .. => false
  | .trans .. => false

theorem domOK_of_domTrivial {n : ℕ} (box : Fin n → DInterval) (e : IExpr n)
    (h : e.domTrivial = true) : DomOK box e := by
  induction e with
  | const d => exact .const
  | var i => exact .var
  | neg e ih => exact .neg (ih (by simpa [IExpr.domTrivial] using h))
  | abs e ih => exact .abs (ih (by simpa [IExpr.domTrivial] using h))
  | ite c t e _ _ _ => simp [IExpr.domTrivial] at h
  | add e₁ e₂ ih₁ ih₂ =>
      simp only [IExpr.domTrivial, Bool.and_eq_true] at h
      exact .add (ih₁ h.1) (ih₂ h.2)
  | sub e₁ e₂ ih₁ ih₂ =>
      simp only [IExpr.domTrivial, Bool.and_eq_true] at h
      exact .sub (ih₁ h.1) (ih₂ h.2)
  | mul e₁ e₂ ih₁ ih₂ =>
      simp only [IExpr.domTrivial, Bool.and_eq_true] at h
      exact .mul (ih₁ h.1) (ih₂ h.2)
  | div e₁ e₂ out _ _ => simp [IExpr.domTrivial] at h
  | sqrt e s₁ s₂ _ => simp [IExpr.domTrivial] at h
  | trans k e N out _ => simp [IExpr.domTrivial] at h

/-- The point box with both endpoints at the dyadic corner `c i`. -/
def pointBox {n : ℕ} (c : Fin n → Dyadic) : Fin n → DInterval :=
  fun i => ⟨c i, c i⟩

/-! ## Interval certificates for the domain premises -/

/-- An interval enclosure with a positive lower endpoint certifies pointwise
positivity over the box. -/
theorem evalReal_pos_of_lo_pos {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (ρ : Fin n → ℝ) (hρ : boxMem box ρ) (J : DInterval)
    (hJ : e.eval box = some J) (hpos : J.lo.isPos = true) :
    0 < e.evalReal ρ :=
  lt_of_lt_of_le (Dyadic.toReal_pos_of_isPos hpos)
    ((IExpr.eval_mem e box ρ hρ J hJ).1)

/-- Same, with only nonnegativity: `isNN` on the lower endpoint. -/
theorem evalReal_nonneg_of_lo_nn {n : ℕ} (e : IExpr n)
    (box : Fin n → DInterval) (ρ : Fin n → ℝ) (hρ : boxMem box ρ)
    (J : DInterval) (hJ : e.eval box = some J) (hnn : J.lo.isNN = true) :
    0 ≤ e.evalReal ρ :=
  le_trans ((Dyadic.isNN_iff J.lo).mp hnn) (IExpr.eval_mem e box ρ hρ J hJ).1

/-- An interval enclosure with a negative upper endpoint certifies pointwise
negativity over the box (the guard-decision certificate for `DomOK.ite`). -/
theorem evalReal_neg_of_hi_neg {n : ℕ} (e : IExpr n)
    (box : Fin n → DInterval) (ρ : Fin n → ℝ) (hρ : boxMem box ρ)
    (J : DInterval) (hJ : e.eval box = some J) (hneg : J.hi.isNeg = true) :
    e.evalReal ρ < 0 :=
  lt_of_le_of_lt (IExpr.eval_mem e box ρ hρ J hJ).2
    ((Dyadic.isNeg_iff J.hi).mp hneg)

/-- Positivity in particular excludes zero (divisor certificate). -/
theorem evalReal_ne_zero_of_lo_pos {n : ℕ} (e : IExpr n)
    (box : Fin n → DInterval) (ρ : Fin n → ℝ) (hρ : boxMem box ρ)
    (J : DInterval) (hJ : e.eval box = some J) (hpos : J.lo.isPos = true) :
    e.evalReal ρ ≠ 0 := ne_of_gt (evalReal_pos_of_lo_pos e box ρ hρ J hJ hpos)

/-- Box membership of an updated point: changing coordinate `j` of an in-box
point to `x` stays in the box exactly when `x` is in the `j`-side. -/
theorem boxMem_update {n : ℕ} {box : Fin n → DInterval} {σ : Fin n → ℝ}
    (hσ : boxMem box σ) (j : Fin n) (x : ℝ)
    (hx : (box j).lo.toReal ≤ x ∧ x ≤ (box j).hi.toReal) :
    boxMem box (Function.update σ j x) := by
  intro i
  by_cases h : i = j
  · subst h
    rw [Function.update_self]
    exact hx
  · rw [Function.update_of_ne h]
    exact hσ i

/-! ## The chain rule -/

/-- The one-dimensional slice of `e` along coordinate `j` through `σ`:
`x ↦ e.evalReal (σ with coordinate j replaced by x)`. -/
noncomputable def sliceEval {n : ℕ} (e : IExpr n) (j : Fin n) (σ : Fin n → ℝ) :
    ℝ → ℝ :=
  fun x => e.evalReal (Function.update σ j x)

/-- Updating coordinate `j` of `σ` to its own `j`-entry gives back `σ`
(pointwise; `Function.update_self` only sees the applied form). -/
theorem update_self_eq {n : ℕ} (σ : Fin n → ℝ) (j : Fin n) :
    Function.update σ j (σ j) = σ := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The slice at its base point is the evaluation at `σ`. -/
theorem sliceEval_self {n : ℕ} (e : IExpr n) (j : Fin n) (σ : Fin n → ℝ) :
    sliceEval e j σ (σ j) = e.evalReal σ := by
  unfold sliceEval
  rw [update_self_eq]

/-- **The `evalReal` chain rule** (`HasDerivAt` form).  At every interior
point of the `j`-side, the slice of `e` has derivative
`(derivExpr e j).evalReal σ`.  Per-op: `mul` = product rule, `div` =
`(f'·g − f·g')/g²` with `g ≠ 0`, `sqrt` = `u'/(2√u)` with `u > 0`,
`arctan` = `u'/(1 + u²)`, `ite` = the selected branch under a uniformly
sign-definite guard. -/
theorem hasDeriv_sliceEval {n : ℕ} (j : Fin n) (box : Fin n → DInterval) :
    ∀ (e : IExpr n) (σ : Fin n → ℝ), boxMem box σ →
      ((box j).lo.toReal < σ j ∧ σ j < (box j).hi.toReal) →
      e.derivSafe = true → DomOK box e →
      HasDerivAt (sliceEval e j σ) ((IExpr.derivExpr e j).evalReal σ) (σ j) := by
  intro e
  induction e with
  | const d =>
      intro σ _ _ _ _
      simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal, Dyadic.toReal_zero]
      exact hasDerivAt_const _ _
  | var i =>
      intro σ hσ _ _ _
      by_cases h : i = j
      · have hslice : sliceEval (.var i) j σ = fun x => x := by
          funext x
          show (Function.update σ j x) i = x
          rw [h, Function.update_self]
        rw [hslice]
        have hv : (IExpr.derivExpr (.var i) j).evalReal σ = 1 := by
          simp only [IExpr.derivExpr, IExpr.evalReal, if_pos h,
            Dyadic.toReal_one]
        rw [hv]
        exact (hasDerivAt_id' (x := σ j) :
          HasDerivAt (fun x : ℝ => x) 1 (σ j))
      · have hslice : sliceEval (.var i) j σ = fun _ => σ i := by
          funext x
          show (Function.update σ j x) i = σ i
          rw [Function.update_of_ne h]
        rw [hslice]
        have hv : (IExpr.derivExpr (.var i) j).evalReal σ = 0 := by
          simp only [IExpr.derivExpr, IExpr.evalReal, if_neg h,
            Dyadic.toReal_zero]
        rw [hv]
        exact (hasDerivAt_const (σ j) (σ i) :
          HasDerivAt (fun _ : ℝ => σ i) 0 (σ j))
  | neg e ih =>
      intro σ hσ hint hSafe hDom
      simp only [IExpr.derivSafe] at hSafe
      simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal]
      exact (ih σ hσ hint hSafe (DomOK.neg_inv hDom)).neg
  | abs e _ =>
      intro σ _ _ hSafe _
      exact Bool.noConfusion hSafe
  | ite c t e ihc iht ihe =>
      intro σ hσ hint hSafe hDom
      obtain ⟨hSafeCT, hSafeE⟩ := (Bool.and_eq_true _ _).mp hSafe
      obtain ⟨hSafeC, hSafeT⟩ := (Bool.and_eq_true _ _).mp hSafeCT
      rcases DomOK.ite_inv_dec hDom with hdec | hdec
      · -- guard strictly negative on the box: then-branch everywhere
        have hcLt : ∀ z : ℝ, (box j).lo.toReal ≤ z → z ≤ (box j).hi.toReal →
            c.evalReal (Function.update σ j z) < 0 := fun z hz1 hz2 =>
          hdec _ (boxMem_update hσ j z ⟨hz1, hz2⟩)
        have hev : sliceEval (.ite c t e) j σ =ᶠ[𝓝 (σ j)] sliceEval t j σ := by
          have hIoo : Ioo (box j).lo.toReal (box j).hi.toReal ∈ 𝓝 (σ j) :=
            Ioo_mem_nhds hint.1 hint.2
          filter_upwards [hIoo] with z hz
          show (if c.evalReal (Function.update σ j z) < 0
                then t.evalReal (Function.update σ j z)
                else e.evalReal (Function.update σ j z))
              = t.evalReal (Function.update σ j z)
          rw [if_pos (hcLt z (le_of_lt hz.1) (le_of_lt hz.2))]
        have hv : (IExpr.derivExpr (.ite c t e) j).evalReal σ
            = (IExpr.derivExpr t j).evalReal σ := by
          have hc0 := hcLt (σ j) (hσ j).1 (hσ j).2
          rw [update_self_eq] at hc0
          simp only [IExpr.derivExpr, IExpr.evalReal]
          exact if_pos hc0
        rw [hv]
        exact HasDerivAt.congr_of_eventuallyEq
          (iht σ hσ hint hSafeT (DomOK.ite_inv_then hDom)) hev
      · -- guard nonnegative on the box: else-branch everywhere
        have hcGe : ∀ z : ℝ, (box j).lo.toReal ≤ z → z ≤ (box j).hi.toReal →
            0 ≤ c.evalReal (Function.update σ j z) := fun z hz1 hz2 =>
          hdec _ (boxMem_update hσ j z ⟨hz1, hz2⟩)
        have hev : sliceEval (.ite c t e) j σ =ᶠ[𝓝 (σ j)] sliceEval e j σ := by
          have hIoo : Ioo (box j).lo.toReal (box j).hi.toReal ∈ 𝓝 (σ j) :=
            Ioo_mem_nhds hint.1 hint.2
          filter_upwards [hIoo] with z hz
          show (if c.evalReal (Function.update σ j z) < 0
                then t.evalReal (Function.update σ j z)
                else e.evalReal (Function.update σ j z))
              = e.evalReal (Function.update σ j z)
          rw [if_neg (not_lt.mpr (hcGe z (le_of_lt hz.1) (le_of_lt hz.2)))]
        have hv : (IExpr.derivExpr (.ite c t e) j).evalReal σ
            = (IExpr.derivExpr e j).evalReal σ := by
          have hc0 := hcGe (σ j) (hσ j).1 (hσ j).2
          rw [update_self_eq] at hc0
          simp only [IExpr.derivExpr, IExpr.evalReal]
          exact if_neg (not_lt.mpr hc0)
        rw [hv]
        exact HasDerivAt.congr_of_eventuallyEq
          (ihe σ hσ hint hSafeE (DomOK.ite_inv_else hDom)) hev
  | add e₁ e₂ ih₁ ih₂ =>
      intro σ hσ hint hSafe hDom
      simp only [IExpr.derivSafe, Bool.and_eq_true] at hSafe
      simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal]
      exact (ih₁ σ hσ hint hSafe.1 (DomOK.add_inv_left hDom)).add
        (ih₂ σ hσ hint hSafe.2 (DomOK.add_inv_right hDom))
  | sub e₁ e₂ ih₁ ih₂ =>
      intro σ hσ hint hSafe hDom
      cases hDom with
      | sub hD1 hD2 =>
        simp only [IExpr.derivSafe, Bool.and_eq_true] at hSafe
        simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal]
        exact (ih₁ σ hσ hint hSafe.1 hD1).sub (ih₂ σ hσ hint hSafe.2 hD2)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro σ hσ hint hSafe hDom
      cases hDom with
      | mul hD1 hD2 =>
        simp only [IExpr.derivSafe, Bool.and_eq_true] at hSafe
        have hm := (ih₁ σ hσ hint hSafe.1 hD1).mul (ih₂ σ hσ hint hSafe.2 hD2)
        rw [sliceEval_self e₁ j σ, sliceEval_self e₂ j σ] at hm
        simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal]
        exact hm
  | div e₁ e₂ out ih₁ ih₂ =>
      intro σ hσ hint hSafe hDom
      simp only [IExpr.derivSafe, Bool.and_eq_true] at hSafe
      have hz : sliceEval e₂ j σ (σ j) ≠ 0 := by
        rw [sliceEval_self]
        exact DomOK.div_inv_hz hDom σ hσ
      have hd := HasDerivAt.div (ih₁ σ hσ hint hSafe.1 (DomOK.div_inv_left hDom))
        (ih₂ σ hσ hint hSafe.2 (DomOK.div_inv_right hDom)) hz
      rw [pow_two (sliceEval e₂ j σ (σ j)), sliceEval_self e₂ j σ,
        sliceEval_self e₁ j σ] at hd
      simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal]
      exact hd
  | sqrt e s₁ s₂ ih =>
      intro σ hσ hint hSafe hDom
      simp only [IExpr.derivSafe] at hSafe
      have hu := ih σ hσ hint hSafe (DomOK.sqrt_inv hDom)
      have hlt : 0 < sliceEval e j σ (σ j) := by
        rw [sliceEval_self]
        exact DomOK.sqrt_inv_pos hDom σ hσ
      have hs := hu.sqrt (ne_of_gt hlt)
      rw [sliceEval_self e j σ] at hs
      simp only [sliceEval, IExpr.derivExpr, IExpr.evalReal, Dyadic.toReal_two]
      exact hs
  | trans k e N out ih =>
      intro σ hσ hint hSafe hDom
      cases k with
      | sinK => exact Bool.noConfusion hSafe
      | cosK => exact Bool.noConfusion hSafe
      | lnK => exact Bool.noConfusion hSafe
      | arctanK =>
        simp only [IExpr.derivSafe] at hSafe
        have hu := ih σ hσ hint hSafe (DomOK.trans_inv hDom)
        have hc := HasDerivAt.comp (σ j)
          (Real.hasDerivAt_arctan (sliceEval e j σ (σ j))) hu
        rw [sliceEval_self e j σ, pow_two] at hc
        have hv : (IExpr.derivExpr (.trans .arctanK e N out) j).evalReal σ
            = (1 / (1 + e.evalReal σ * e.evalReal σ))
              * (IExpr.derivExpr e j).evalReal σ := by
          simp only [IExpr.derivExpr, IExpr.evalReal, transReal,
            Dyadic.toReal_one, one_div, inv_mul_eq_div]
        rw [hv]
        exact hc

/-- **The chain rule**, `deriv` form (the W6a-stated shape
`∂ⱼ(e.evalReal) = dfⱼ.evalReal`). -/
theorem evalReal_deriv {n : ℕ} (e : IExpr n) (j : Fin n)
    (box : Fin n → DInterval) (σ : Fin n → ℝ) (hσ : boxMem box σ)
    (hint : (box j).lo.toReal < σ j ∧ σ j < (box j).hi.toReal)
    (hSafe : e.derivSafe = true) (hDom : DomOK box e) :
    deriv (fun x => e.evalReal (Function.update σ j x)) (σ j)
      = (IExpr.derivExpr e j).evalReal σ :=
  (hasDeriv_sliceEval j box e σ hσ hint hSafe hDom).deriv

/-! ## Continuity of slices -/

/-- The slice of `e` is continuous on the closed `j`-side of the box —
the continuity side of the monotonicity transfer. -/
theorem continuousOn_sliceEval {n : ℕ} (j : Fin n) (box : Fin n → DInterval) :
    ∀ (e : IExpr n) (σ : Fin n → ℝ), boxMem box σ → e.derivSafe = true →
      DomOK box e →
      ContinuousOn (sliceEval e j σ)
        (Icc (box j).lo.toReal (box j).hi.toReal) := by
  intro e
  induction e with
  | const d =>
      intro σ _ _ _
      exact continuousOn_const
  | var i =>
      intro σ hσ _ _
      by_cases h : i = j
      · have hslice : sliceEval (.var i) j σ = fun x => x := by
          funext x
          show (Function.update σ j x) i = x
          rw [h, Function.update_self]
        rw [hslice]
        exact continuousOn_id
      · have hslice : sliceEval (.var i) j σ = fun _ => σ i := by
          funext x
          show (Function.update σ j x) i = σ i
          rw [Function.update_of_ne h]
        rw [hslice]
        exact continuousOn_const
  | neg e ih =>
      intro σ hσ hSafe hDom
      simp only [IExpr.derivSafe] at hSafe
      exact (ih σ hσ hSafe (DomOK.neg_inv hDom)).neg
  | abs e _ =>
      intro σ _ hSafe _
      exact Bool.noConfusion hSafe
  | ite c t e ihc iht ihe =>
      intro σ hσ hSafe hDom
      obtain ⟨hSafeCT, hSafeE⟩ := (Bool.and_eq_true _ _).mp hSafe
      obtain ⟨hSafeC, hSafeT⟩ := (Bool.and_eq_true _ _).mp hSafeCT
      rcases DomOK.ite_inv_dec hDom with hdec | hdec
      · have hEq : ∀ z ∈ Icc (box j).lo.toReal (box j).hi.toReal,
            sliceEval (.ite c t e) j σ z = sliceEval t j σ z := by
          intro z hz
          show (if c.evalReal (Function.update σ j z) < 0
                then t.evalReal (Function.update σ j z)
                else e.evalReal (Function.update σ j z))
              = t.evalReal (Function.update σ j z)
          rw [if_pos (hdec _ (boxMem_update hσ j z hz))]
        exact (iht σ hσ hSafeT (DomOK.ite_inv_then hDom)).congr hEq
      · have hEq : ∀ z ∈ Icc (box j).lo.toReal (box j).hi.toReal,
            sliceEval (.ite c t e) j σ z = sliceEval e j σ z := by
          intro z hz
          show (if c.evalReal (Function.update σ j z) < 0
                then t.evalReal (Function.update σ j z)
                else e.evalReal (Function.update σ j z))
              = e.evalReal (Function.update σ j z)
          rw [if_neg (not_lt.mpr (hdec _ (boxMem_update hσ j z hz)))]
        exact (ihe σ hσ hSafeE (DomOK.ite_inv_else hDom)).congr hEq
  | add e₁ e₂ ih₁ ih₂ =>
      intro σ hσ hSafe hDom
      obtain ⟨hSafeC, hSafeE⟩ := (Bool.and_eq_true _ _).mp hSafe
      exact (ih₁ σ hσ hSafeC (DomOK.add_inv_left hDom)).add
        (ih₂ σ hσ hSafeE (DomOK.add_inv_right hDom))
  | sub e₁ e₂ ih₁ ih₂ =>
      intro σ hσ hSafe hDom
      obtain ⟨hSafeC, hSafeE⟩ := (Bool.and_eq_true _ _).mp hSafe
      exact (ih₁ σ hσ hSafeC (DomOK.sub_inv_left hDom)).sub
        (ih₂ σ hσ hSafeE (DomOK.sub_inv_right hDom))
  | mul e₁ e₂ ih₁ ih₂ =>
      intro σ hσ hSafe hDom
      obtain ⟨hSafeC, hSafeE⟩ := (Bool.and_eq_true _ _).mp hSafe
      exact (ih₁ σ hσ hSafeC (DomOK.mul_inv_left hDom)).mul
        (ih₂ σ hσ hSafeE (DomOK.mul_inv_right hDom))
  | div e₁ e₂ out ih₁ ih₂ =>
      intro σ hσ hSafe hDom
      obtain ⟨hnez, hD1, hD2⟩ := DomOK.div_inv_all hDom
      obtain ⟨hSafeC, hSafeE⟩ := (Bool.and_eq_true _ _).mp hSafe
      exact ContinuousOn.div (ih₁ σ hσ hSafeC (DomOK.div_inv_left hDom))
        (ih₂ σ hσ hSafeE (DomOK.div_inv_right hDom))
        (fun z hz => hnez _ (boxMem_update hσ j z hz))
  | sqrt e s₁ s₂ ih =>
      intro σ hσ hSafe hDom
      obtain ⟨hpos, hD⟩ := DomOK.sqrt_inv_all hDom
      simp only [IExpr.derivSafe] at hSafe
      exact Real.continuous_sqrt.comp_continuousOn (ih σ hσ hSafe hD)
  | trans k e N out ih =>
      intro σ hσ hSafe hDom
      cases k with
      | sinK => exact Bool.noConfusion hSafe
      | cosK => exact Bool.noConfusion hSafe
      | lnK => exact Bool.noConfusion hSafe
      | arctanK =>
        simp only [IExpr.derivSafe] at hSafe
        exact Real.continuous_arctan.comp_continuousOn
          (ih σ hσ hSafe (DomOK.trans_inv hDom))

/-! ## Sign-definite derivative ⇒ monotone slices -/

/-- If the symbolic partial derivative is strictly positive on the whole
box, every slice of `e` along `j` is monotone on the closed `j`-side. -/
theorem slice_strict_incr {n : ℕ} (e : IExpr n) (j : Fin n)
    (box : Fin n → DInterval) (σ : Fin n → ℝ) (hσ : boxMem box σ)
    (hSafe : e.derivSafe = true) (hDom : DomOK box e)
    (hpos : ∀ ρ', boxMem box ρ' → 0 < (IExpr.derivExpr e j).evalReal ρ')
    (x y : ℝ) (hx : (box j).lo.toReal ≤ x) (hxy : x ≤ y)
    (hy : y ≤ (box j).hi.toReal) :
    sliceEval e j σ x ≤ sliceEval e j σ y := by
  have hcont := continuousOn_sliceEval j box e σ hσ hSafe hDom
  have hmono : MonotoneOn (sliceEval e j σ)
      (Icc (box j).lo.toReal (box j).hi.toReal) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Icc (box j).lo.toReal (box j).hi.toReal)
      (f := sliceEval e j σ)
      (f' := fun z => (IExpr.derivExpr e j).evalReal (Function.update σ j z))
      (convex_Icc (box j).lo.toReal (box j).hi.toReal) hcont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx ⊢
      obtain ⟨hx1, hx2⟩ := hx
      have hmem : boxMem box (Function.update σ j x) :=
        boxMem_update hσ j x ⟨le_of_lt hx1, le_of_lt hx2⟩
      have hint' : (box j).lo.toReal < (Function.update σ j x) j ∧
          (Function.update σ j x) j < (box j).hi.toReal := by
        rw [Function.update_self]
        exact ⟨hx1, hx2⟩
      have hd := hasDeriv_sliceEval j box e (Function.update σ j x) hmem
        hint' hSafe hDom
      rw [Function.update_self] at hd
      have hfun : sliceEval e j (Function.update σ j x) = sliceEval e j σ := by
        funext z
        unfold sliceEval
        rw [Function.update_idem]
      rw [hfun] at hd
      exact hd.hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hmem : boxMem box (Function.update σ j x) :=
        boxMem_update hσ j x ⟨le_of_lt hx1, le_of_lt hx2⟩
      exact le_of_lt (hpos (Function.update σ j x) hmem)
  exact hmono
    (⟨hx, le_trans hxy hy⟩ : (box j).lo.toReal ≤ x ∧ x ≤ (box j).hi.toReal)
    (⟨le_trans hx hxy, hy⟩ : (box j).lo.toReal ≤ y ∧ y ≤ (box j).hi.toReal)
    hxy

/-- If the symbolic partial derivative is strictly negative on the whole
box, every slice of `e` along `j` is antitone on the closed `j`-side. -/
theorem slice_strict_decr {n : ℕ} (e : IExpr n) (j : Fin n)
    (box : Fin n → DInterval) (σ : Fin n → ℝ) (hσ : boxMem box σ)
    (hSafe : e.derivSafe = true) (hDom : DomOK box e)
    (hneg : ∀ ρ', boxMem box ρ' → (IExpr.derivExpr e j).evalReal ρ' < 0)
    (x y : ℝ) (hx : (box j).lo.toReal ≤ x) (hxy : x ≤ y)
    (hy : y ≤ (box j).hi.toReal) :
    sliceEval e j σ y ≤ sliceEval e j σ x := by
  have hS : IExpr.derivSafe (.neg e) = true := by
    simp only [IExpr.derivSafe]; exact hSafe
  have hD : DomOK box (.neg e) := .neg hDom
  have hpos : ∀ ρ', boxMem box ρ' →
      0 < (IExpr.derivExpr (.neg e) j).evalReal ρ' := by
    intro ρ' hρ'
    have hv : (IExpr.derivExpr (.neg e) j).evalReal ρ'
        = -((IExpr.derivExpr e j).evalReal ρ') := by
      simp only [IExpr.derivExpr, IExpr.evalReal]
    rw [hv]
    linarith [hneg ρ' hρ']
  have hmono := slice_strict_incr (.neg e) j box σ hσ hS hD hpos x y hx hxy hy
  simpa only [sliceEval, IExpr.evalReal] using le_of_neg_le_neg hmono

/-! ## The n-dimensional corner telescope -/

/-- Moving one coordinate to its certified extreme face never increases `f`
(each slice is monotone between the face point and `x` by
`slice_strict_incr` / `slice_strict_decr`); the move is iterated
coordinate by coordinate until every coordinate sits at the corner. -/
theorem monoCorner_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (lo hi corner : Fin n → ℝ)
    (hcorner : ∀ i, lo i ≤ corner i ∧ corner i ≤ hi i)
    (hstep : ∀ j : Fin n, ∀ σ : Fin n → ℝ,
      (∀ i, lo i ≤ σ i ∧ σ i ≤ hi i) →
      ∀ x, lo j ≤ x → x ≤ hi j →
        f (Function.update σ j (corner j)) ≤ f (Function.update σ j x))
    (ρ : Fin n → ℝ) (hρ : ∀ i, lo i ≤ ρ i ∧ ρ i ≤ hi i) :
    f corner ≤ f ρ := by
  -- walk ρ to corner one coordinate at a time: at step k the first k
  -- coordinates already sit at the corner
  set pt : ℕ → (Fin n → ℝ) :=
    fun k i => if (i : ℕ) < k then corner i else ρ i with hptdef
  have hmem : ∀ (k : ℕ) (i : Fin n), lo i ≤ pt k i ∧ pt k i ≤ hi i := by
    intro k i
    by_cases h : (i : ℕ) < k
    · simp only [hptdef, if_pos h]
      exact hcorner i
    · simp only [hptdef, if_neg h]
      exact hρ i
  have h0 : pt 0 = ρ := by
    funext i
    simp only [hptdef, if_neg (Nat.not_lt_zero (i : ℕ))]
  have hn : pt n = corner := by
    funext i
    simp only [hptdef, if_pos (Fin.isLt i)]
  have hstepk : ∀ k : ℕ, k < n → f (pt (k + 1)) ≤ f (pt k) := by
    intro k hk
    have hupd : pt (k + 1)
        = Function.update (pt k) ⟨k, hk⟩ (corner ⟨k, hk⟩) := by
      funext i
      by_cases h : i = ⟨k, hk⟩
      · subst h
        simp only [hptdef, if_pos (Nat.lt_succ_self k), Function.update_self]
      · rcases Nat.lt_or_ge (i : ℕ) k with h1 | h1
        · simp only [hptdef, if_pos (Nat.lt_succ_of_lt h1),
            Function.update_of_ne h, if_pos h1]
        · have hik : (i : ℕ) ≠ k := fun hcon => h (Fin.val_injective hcon)
          simp only [hptdef, if_neg (by omega : ¬ ((i : ℕ) < k)),
            Function.update_of_ne h,
            if_neg (by omega : ¬ ((i : ℕ) < k + 1))]
    have hself : Function.update (pt k) ⟨k, hk⟩ (pt k ⟨k, hk⟩) = pt k := by
      funext i
      by_cases h : i = ⟨k, hk⟩
      · subst h
        simp only [Function.update_self]
      · simp only [Function.update_of_ne h]
    calc f (pt (k + 1))
        = f (Function.update (pt k) ⟨k, hk⟩ (corner ⟨k, hk⟩)) := by rw [hupd]
      _ ≤ f (Function.update (pt k) ⟨k, hk⟩ (pt k ⟨k, hk⟩)) :=
        hstep ⟨k, hk⟩ (pt k) (hmem k) (pt k ⟨k, hk⟩)
          (hmem k ⟨k, hk⟩).1 (hmem k ⟨k, hk⟩).2
      _ = f (pt k) := by rw [hself]
  have htel : ∀ k : ℕ, k ≤ n → f (pt k) ≤ f (pt 0) := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ m ih =>
        exact le_trans (hstepk m (Nat.lt_of_succ_le hk)) (ih (Nat.le_of_succ_le hk))
  calc f corner = f (pt n) := by rw [hn]
    _ ≤ f (pt 0) := htel n le_rfl
    _ = f ρ := by rw [h0]

/-! ## Assembly: the mono-corner checker -/

/-- **The mono-corner assembly** (W6a item 3).  Per dimension, the emitted
certificate is a kernel `checkPosTMHull` success on the symbolic derivative
`derivExpr e j` (`sgn j = true`: increasing, corner at the `lo` face) or on
its negation (`sgn j = false`: decreasing, corner at the `hi` face); the
corner point box carries a `checkPosTMHull` success of `e` itself.  Under
`derivSafe` and the domain premises `DomOK`, every point of the box gets
`0 < e.evalReal ρ`. -/
theorem checkMonoCorner {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (sgn : Fin n → Bool) (corner : Fin n → Dyadic)
    (psd : Fin n → TMParams) (psc : TMParams)
    (hSafe : e.derivSafe = true) (hDom : DomOK box e)
    (hincr : ∀ j, sgn j = true →
      checkPosTMHull (IExpr.derivExpr e j) box (psd j) = true ∧
        corner j = (box j).lo)
    (hdecr : ∀ j, sgn j = false →
      checkPosTMHull (IExpr.neg (IExpr.derivExpr e j)) box (psd j) = true ∧
        corner j = (box j).hi)
    (hcorner : checkPosTMHull e (pointBox corner) psc = true)
    (hcmem : ∀ i, (box i).mem (corner i).toReal)
    (ρ : Fin n → ℝ) (hρ : boxMem box ρ) :
    0 < e.evalReal ρ := by
  have hstep : ∀ j : Fin n, ∀ σ : Fin n → ℝ,
      (∀ i, (box i).lo.toReal ≤ σ i ∧ σ i ≤ (box i).hi.toReal) →
      ∀ x, (box j).lo.toReal ≤ x → x ≤ (box j).hi.toReal →
        e.evalReal (Function.update σ j (corner j).toReal)
          ≤ e.evalReal (Function.update σ j x) := by
    intro j σ hσm x hx1 hx2
    by_cases hsgn : sgn j = true
    · -- sgn j = true: increasing, corner at the lo face
      obtain ⟨hcert, hface⟩ := hincr j hsgn
      have hpos : ∀ ρ', boxMem box ρ' →
          0 < (IExpr.derivExpr e j).evalReal ρ' := fun ρ' hρ' =>
        checkPosTMHull_sound hcert ρ' hρ'
      have hface' : (corner j).toReal = (box j).lo.toReal := by rw [hface]
      exact slice_strict_incr e j box σ hσm hSafe hDom hpos
        (corner j).toReal x (by rw [hface'])
        (by rw [hface']; exact hx1) hx2
    · -- sgn j = false: decreasing, corner at the hi face
      simp only [Bool.not_eq_true] at hsgn
      obtain ⟨hcert, hface⟩ := hdecr j hsgn
      have hneg : ∀ ρ', boxMem box ρ' →
          (IExpr.derivExpr e j).evalReal ρ' < 0 := by
        intro ρ' hρ'
        have h1 := checkPosTMHull_sound
          (e := IExpr.neg (IExpr.derivExpr e j)) (box := box) hcert ρ' hρ'
        have h2 : IExpr.evalReal (IExpr.neg (IExpr.derivExpr e j)) ρ'
            = -((IExpr.derivExpr e j).evalReal ρ') := by
          simp only [IExpr.evalReal]
        rw [h2] at h1
        linarith
      have hface' : (corner j).toReal = (box j).hi.toReal := by rw [hface]
      exact slice_strict_decr e j box σ hσm hSafe hDom hneg x (corner j).toReal
        hx1 (by rw [hface']; exact hx2) (by rw [hface'])
  have htele : e.evalReal (fun i => (corner i).toReal) ≤ e.evalReal ρ :=
    monoCorner_le (e.evalReal) (fun i => (box i).lo.toReal)
      (fun i => (box i).hi.toReal) (fun i => (corner i).toReal) hcmem hstep
      ρ hρ
  have hposc : 0 < e.evalReal (fun i => (corner i).toReal) :=
    checkPosTMHull_sound (e := e) (box := pointBox corner) (ps := psc) hcorner
      (fun i => (corner i).toReal) (fun i => ⟨le_rfl, le_rfl⟩)
  exact lt_of_lt_of_le hposc htele

/-! ## Pilot: the whole pipeline on a small bilinear leaf

`f(x,y) = 13/8·(x−1) + 13/8·(y−1) − 5/4·(x−1)(y−1) + 1/4` on `[1,2]²`:
plain interval arithmetic fails (the bilinear term costs its full unit of
width: `lo = 1/4 − 5/4 < 0`), but both partial derivatives are
sign-definite (`∂x = 13/8 − 5/4(y−1) ∈ [3/8, 13/8]`, symmetric in `y`) and
the min-corner `(1,1)` evaluates to exactly `1/4 > 0` — the mono route
closes the box.  Every `decide` below is a kernel check. -/

/-- The pilot expression. -/
def exMono : IExpr 2 :=
  .add (.add (.mul (.const ⟨13, -3⟩) (.sub (.var 0) (.const ⟨1, 0⟩)))
        (.mul (.const ⟨13, -3⟩) (.sub (.var 1) (.const ⟨1, 0⟩))))
    (.add (.neg (.mul (.mul (.const ⟨5, -2⟩) (.sub (.var 0) (.const ⟨1, 0⟩)))
        (.sub (.var 1) (.const ⟨1, 0⟩)))) (.const ⟨1, -2⟩))

/-- The pilot box `[1,2]²`. -/
def exMonoBox : Fin 2 → DInterval := ![⟨⟨1, 0⟩, ⟨2, 0⟩⟩, ⟨⟨1, 0⟩, ⟨2, 0⟩⟩]

/-- Negative anchor: plain interval arithmetic **fails** on the whole box. -/
theorem exMono_interval_fails : checkPos exMono exMonoBox = false := by
  decide

/-- The kernel-computed `∂x` is `13/8 − 5/4·(y−1)`. -/
theorem exMono_df0_val (ρ : Fin 2 → ℝ) :
    (IExpr.derivExpr exMono 0).evalReal ρ
      = (13 : ℝ) / 8 - 5 / 4 * (ρ 1 - 1) := by
  simp [exMono, IExpr.derivExpr, IExpr.evalReal, Dyadic.toReal_def] <;> ring

/-- `∂x > 0` on the box: a kernel TM-hull certificate. -/
theorem exMono_df0_pos :
    checkPosTMHull (IExpr.derivExpr exMono 0) exMonoBox TMParams.empty
      = true := by decide

/-- `∂y > 0` on the box: a kernel TM-hull certificate. -/
theorem exMono_df1_pos :
    checkPosTMHull (IExpr.derivExpr exMono 1) exMonoBox TMParams.empty
      = true := by decide

/-- The pilot corner: the increasing directions pin both coordinates to
the `lo` face. -/
def exMonoCorner : Fin 2 → Dyadic := ![⟨1, 0⟩, ⟨1, 0⟩]

/-- The corner point box carries `f = 1/4 > 0` (kernel TM-hull). -/
theorem exMono_corner_pos :
    checkPosTMHull exMono (pointBox exMonoCorner) TMParams.empty = true := by
  decide

/-- **End to end**: derivative sign certificates + corner certificate ⇒
`0 < f` at every real point of the whole box. -/
theorem exMono_end_to_end (ρ : Fin 2 → ℝ) (hρ : boxMem exMonoBox ρ) :
    0 < exMono.evalReal ρ :=
  checkMonoCorner exMono exMonoBox ![true, true] exMonoCorner
    (fun _ => TMParams.empty) TMParams.empty
    (by decide) (domOK_of_domTrivial _ _ (by decide))
    (by
      intro j hj
      fin_cases j
      · exact ⟨exMono_df0_pos, rfl⟩
      · exact ⟨exMono_df1_pos, rfl⟩)
    (by
      intro j hj
      fin_cases j <;> simp at hj)
    exMono_corner_pos
    (by
      intro i
      fin_cases i
      · simp only [DInterval.mem, exMonoBox, exMonoCorner, Dyadic.toReal_one,
          Dyadic.toReal_two]
        exact ⟨le_rfl, by norm_num⟩
      · simp only [DInterval.mem, exMonoBox, exMonoCorner, Dyadic.toReal_one,
          Dyadic.toReal_two]
        exact ⟨le_rfl, by norm_num⟩)
    ρ hρ

end Kepler.Interval
