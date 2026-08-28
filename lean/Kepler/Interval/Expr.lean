/-
  Phase 4, step 5: the **extended interval expression AST** — the positivity
  checker layer of the planned "branch-and-bound over boxes" certificate
  scheme for Flyspeck nonlinear inequalities (`f(x) > 0` on a box).

  `IExpr` started life in `Kepler.Interval.Basic` with total `+ - × Neg`
  nodes only.  It has moved *here* (and been extended) because the new nodes
  must call the `Div`/`Sqrt`/`Trans` layers, which sit downstream of
  `Basic` — extending in place would be an import cycle.

  ## New node kinds (and how their certificates stay kernel-checkable)

  - `.div e₁ e₂ out`: interval division at output granularity `2^out`
    (`DInterval.div`, `Option`-valued: `none` when the divisor interval
    meets `0` or the granularity has no scaling room).  Soundness via
    `DInterval.div_sound` (division is `I · recip J`, reciprocal floors with
    an explicit one-ulp error).
  - `.sqrt e s₁ s₂`: **certificate-based** square root — the node carries
    the two root mantissas `s₁ s₂ : Int` for the endpoints of the input
    interval (`Nat.sqrt` does not kernel-reduce, so the *generator* computes
    the mantissas off-kernel and the kernel only verifies
    `s² ≤ n < (s+1)²` in `Int`, exactly as in `Kepler.Interval.Sqrt`).
    The result is `⟨(sqrtI I.lo s₁).lo, (sqrtI I.hi s₂).hi⟩`; monotonicity
    of `√` does the rest.  `none` on a negative radicand or bad certificate.
  - `.trans k e N out`: transcendental node tagged by `TKind`
    (`sinK`/`cosK`/`arctanK`), delegating to the interval-level wrappers of
    `Trans.lean` (`sinGen` = `[-1,1]` direct or π-shift reduction, `cosI`,
    `arctanI`), each with internal kernel-decidable range checks and
    `N` Taylor terms outward-rounded at granularity `2^out`.

  ## The `Option` evaluator

  All operations are total-but-failable: `eval : IExpr n → (Fin n →
  DInterval) → Option DInterval` returns `none` whenever a sub-check fails
  (division by an interval meeting `0`, `√` of a negative box, transcendental
  outside its range, …).  Failure is always the *safe* direction — the
  corresponding `checkPos` is `false` — and `eval_mem` keeps the exact
  statement of the old total version: *every* successful interval contains
  the real value.

  ## Core checker theorem

  `checkPos_sound`: if the kernel-decidable check `checkPos e box` passes
  (the interval evaluation of `e` over `box` succeeds and its lower endpoint
  has a positive mantissa), then for every real assignment `ρ` pointwise
  inside `box`, `0 < e.evalReal ρ`.  This is the per-leaf certificate of the
  branch-and-bound scheme; `Kepler.Interval.Cert` builds the trees.

  Checking layer: `Int` only. No `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.Trans
import Kepler.Interval.Sqrt

namespace Kepler.Interval

/-! ## Transcendental kinds and the extended AST -/

/-- Kind tag of the `.trans` AST node. -/
inductive TKind where
  | sinK : TKind
  | cosK : TKind
  | arctanK : TKind
  deriving Repr, DecidableEq

/-- The real function denoted by a `TKind`. -/
noncomputable def transReal (k : TKind) (x : ℝ) : ℝ :=
  match k with
  | .sinK => Real.sin x
  | .cosK => Real.cos x
  | .arctanK => Real.arctan x

/-- The interval-level enclosure denoted by a `TKind` (range checks are
internal to the wrappers; failure gives `none`). -/
def transOn (k : TKind) (I : DInterval) (N : ℕ) (out : Int) : Option DInterval :=
  match k with
  | .sinK => sinGen I N out
  | .cosK => cosI I N out
  | .arctanK => arctanI I N out

/-- Interval expression AST: constants, variables, `+ - × Neg`, division at
granularity `out`, certificate-based square root (two root mantissas), and
transcendentals (`TKind`, Taylor order `N`, granularity `out`). -/
inductive IExpr (n : ℕ) : Type where
  | const (d : Dyadic) : IExpr n
  | var (i : Fin n) : IExpr n
  | neg (e : IExpr n) : IExpr n
  | add (e₁ e₂ : IExpr n) : IExpr n
  | sub (e₁ e₂ : IExpr n) : IExpr n
  | mul (e₁ e₂ : IExpr n) : IExpr n
  | div (e₁ e₂ : IExpr n) (out : Int) : IExpr n
  | sqrt (e : IExpr n) (s₁ s₂ : Int) : IExpr n
  | trans (k : TKind) (e : IExpr n) (N : ℕ) (out : Int) : IExpr n
  deriving Repr

namespace IExpr

/-- Interval evaluation over a box (`Option`-valued: `none` when a
sub-check — divisor range, radicand sign, transcendental range, scaling
room — fails; failure is always sound). -/
def eval {n : ℕ} : IExpr n → (Fin n → DInterval) → Option DInterval
  | .const d, _ => some ⟨d, d⟩
  | .var i, box => some (box i)
  | .neg e, box => (e.eval box).map DInterval.neg
  | .add e₁ e₂, box =>
      match e₁.eval box, e₂.eval box with
      | some I, some J => some (I.add J)
      | _, _ => none
  | .sub e₁ e₂, box =>
      match e₁.eval box, e₂.eval box with
      | some I, some J => some (I.sub J)
      | _, _ => none
  | .mul e₁ e₂, box =>
      match e₁.eval box, e₂.eval box with
      | some I, some J => some (I.mul J)
      | _, _ => none
  | .div e₁ e₂ out, box =>
      match e₁.eval box, e₂.eval box with
      | some I, some J => DInterval.div I J out
      | _, _ => none
  | .sqrt e s₁ s₂, box =>
      match e.eval box with
      | some I =>
          match Dyadic.sqrtI I.lo s₁, Dyadic.sqrtI I.hi s₂ with
          | some Jl, some Jh => some ⟨Jl.lo, Jh.hi⟩
          | _, _ => none
      | none => none
  | .trans k e N out, box =>
      match e.eval box with
      | some I => transOn k I N out
      | none => none

/-- Real evaluation under a real assignment. -/
noncomputable def evalReal {n : ℕ} : IExpr n → (Fin n → ℝ) → ℝ
  | .const d, _ => d.toReal
  | .var i, ρ => ρ i
  | .neg e, ρ => -e.evalReal ρ
  | .add e₁ e₂, ρ => e₁.evalReal ρ + e₂.evalReal ρ
  | .sub e₁ e₂, ρ => e₁.evalReal ρ - e₂.evalReal ρ
  | .mul e₁ e₂, ρ => e₁.evalReal ρ * e₂.evalReal ρ
  | .div e₁ e₂ _, ρ => e₁.evalReal ρ / e₂.evalReal ρ
  | .sqrt e _ _, ρ => Real.sqrt (e.evalReal ρ)
  | .trans k e _ _, ρ => transReal k (e.evalReal ρ)

/-- Soundness of the transcendental dispatch. -/
theorem transOn_sound (k : TKind) {I : DInterval} {N : ℕ} {out : Int}
    {K : DInterval} {y : ℝ} (hy : I.mem y) (h : transOn k I N out = some K) :
    K.mem (transReal k y) := by
  rcases k with _ | _ | _
  · exact sinGen_sound hy h
  · exact cosI_sound hy h
  · exact arctanI_sound hy h

/-- **Soundness of interval evaluation**: every *successful* interval value
contains the real value for every assignment pointwise inside the box. -/
theorem eval_mem {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).mem (ρ i)) :
    ∀ I, e.eval box = some I → I.mem (e.evalReal ρ) := by
  induction e with
  | const d =>
    intro I h
    obtain rfl : I = ⟨d, d⟩ := (Option.some.inj h).symm
    constructor
    · show d.toReal ≤ d.toReal
      exact le_rfl
    · show d.toReal ≤ d.toReal
      exact le_rfl
  | var i =>
    intro I h
    obtain rfl : I = box i := (Option.some.inj h).symm
    exact hρ i
  | neg e ih =>
    intro I h
    simp only [eval] at h
    cases he : e.eval box with
    | none => rw [he] at h; simp at h
    | some J =>
      rw [he] at h
      simp only [Option.map_some] at h
      obtain rfl : I = DInterval.neg J := (Option.some.inj h).symm
      exact DInterval.mem_neg (ih J he)
  | add e₁ e₂ ih₁ ih₂ =>
    intro I h
    simp only [eval] at h
    cases h₁ : e₁.eval box with
    | none => rw [h₁] at h; simp at h
    | some I₁ =>
      rw [h₁] at h
      cases h₂ : e₂.eval box with
      | none => rw [h₂] at h; simp at h
      | some I₂ =>
        rw [h₂] at h
        dsimp only at h
        obtain rfl : I = I₁.add I₂ := (Option.some.inj h).symm
        exact DInterval.mem_add (ih₁ I₁ h₁) (ih₂ I₂ h₂)
  | sub e₁ e₂ ih₁ ih₂ =>
    intro I h
    simp only [eval] at h
    cases h₁ : e₁.eval box with
    | none => rw [h₁] at h; simp at h
    | some I₁ =>
      rw [h₁] at h
      cases h₂ : e₂.eval box with
      | none => rw [h₂] at h; simp at h
      | some I₂ =>
        rw [h₂] at h
        dsimp only at h
        obtain rfl : I = I₁.sub I₂ := (Option.some.inj h).symm
        exact DInterval.mem_sub (ih₁ I₁ h₁) (ih₂ I₂ h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
    intro I h
    simp only [eval] at h
    cases h₁ : e₁.eval box with
    | none => rw [h₁] at h; simp at h
    | some I₁ =>
      rw [h₁] at h
      cases h₂ : e₂.eval box with
      | none => rw [h₂] at h; simp at h
      | some I₂ =>
        rw [h₂] at h
        dsimp only at h
        obtain rfl : I = I₁.mul I₂ := (Option.some.inj h).symm
        exact DInterval.mem_mul (ih₁ I₁ h₁) (ih₂ I₂ h₂)
  | div e₁ e₂ out ih₁ ih₂ =>
    intro I h
    simp only [eval] at h
    cases h₁ : e₁.eval box with
    | none => rw [h₁] at h; simp at h
    | some I₁ =>
      rw [h₁] at h
      cases h₂ : e₂.eval box with
      | none => rw [h₂] at h; simp at h
      | some I₂ =>
        rw [h₂] at h
        dsimp only at h
        have hd : DInterval.div I₁ I₂ out = some I := h
        exact DInterval.div_sound hd (ih₁ I₁ h₁) (ih₂ I₂ h₂)
  | sqrt e s₁ s₂ ih =>
    intro I h
    simp only [eval] at h
    cases he : e.eval box with
    | none => rw [he] at h; simp at h
    | some J =>
      rw [he] at h
      dsimp only at h
      cases hl : Dyadic.sqrtI J.lo s₁ with
      | none => rw [hl] at h; simp at h
      | some Jl =>
        rw [hl] at h
        cases hh : Dyadic.sqrtI J.hi s₂ with
        | none => rw [hh] at h; simp at h
        | some Jh =>
          rw [hh] at h
          dsimp only at h
          obtain rfl : I = ⟨Jl.lo, Jh.hi⟩ := (Option.some.inj h).symm
          -- radicand is nonnegative (certificates only succeed then)
          have hy := ih J he
          obtain ⟨hy1, hy2⟩ := hy
          have hnn : 0 ≤ J.lo.toReal := Dyadic.sqrtI_nonneg hl
          have hy0 : 0 ≤ e.evalReal ρ := le_trans hnn hy1
          obtain ⟨hl1, _⟩ := Dyadic.sqrtI_sound hl
          obtain ⟨_, hh2⟩ := Dyadic.sqrtI_sound hh
          exact ⟨le_trans hl1 (Real.sqrt_le_sqrt hy1),
            le_trans (Real.sqrt_le_sqrt hy2) hh2⟩
  | trans k e N out ih =>
    intro I h
    simp only [eval] at h
    cases he : e.eval box with
    | none => rw [he] at h; simp at h
    | some J =>
      rw [he] at h
      dsimp only at h
      exact transOn_sound k (ih J he) h

end IExpr

/-- The positivity checker: kernel-decidable, all arithmetic in `Int`;
fails (`false`) when the interval evaluation fails. -/
def checkPos {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) : Bool :=
  match e.eval box with
  | some I => I.lo.isPos
  | none => false

/-- **Core checker theorem**: if `checkPos` passes, the expression is
strictly positive at every real assignment pointwise inside the box. -/
theorem checkPos_sound {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (h : checkPos e box = true) (ρ : Fin n → ℝ) (hρ : ∀ i, (box i).mem (ρ i)) :
    0 < e.evalReal ρ := by
  unfold checkPos at h
  cases hE : e.eval box with
  | none => rw [hE] at h; simp at h
  | some I =>
    rw [hE] at h
    exact lt_of_lt_of_le (Dyadic.toReal_pos_of_isPos h) ((IExpr.eval_mem e box ρ hρ) I hE).1

/-! ## Small pilot cases (kernel `decide` only, no `native_decide`) -/

/-- Box `[1,2]²`. -/
def exBoxPos : Fin 2 → DInterval := fun _ => ⟨⟨1, 0⟩, ⟨2, 0⟩⟩

/-- `x·y` on two variables. -/
def exExprMul : IExpr 2 := .mul (.var 0) (.var 1)

/-- Accept: `x·y > 0` on `[1,2]²` (interval evaluation gives `[1,4]`). -/
theorem exMul_accept : checkPos exExprMul exBoxPos = true := by decide

/-- Reject: `x·y` on `[-2,1]²` evaluates to `[-2,4]` — the min-of-four-corners
logic is exercised (corner `(-2)·1 = -2` wins). -/
theorem exMul_reject :
    checkPos exExprMul (fun _ : Fin 2 => ⟨⟨-2, 0⟩, ⟨1, 0⟩⟩) = false := by decide

/-- Conservative reject: `x·x` on `[-1,1]` evaluates to `[-1,1]` although the
true range is `[0,1]` — motivates box refinement (branch and bound). -/
theorem exSquare_conservative :
    checkPos (.mul (.var 0) (.var 0)) (fun _ : Fin 1 => ⟨⟨-1, 0⟩, ⟨1, 0⟩⟩) = false := by
  decide

/-- Accept: `3 - x` on `[0,2]` evaluates to `[1,3]` (sub/neg path). -/
theorem exSub_accept :
    checkPos (.sub (.const ⟨3, 0⟩) (.var 0)) (fun _ : Fin 1 => ⟨⟨0, 0⟩, ⟨2, 0⟩⟩) = true := by
  decide

/-- Box for the dyadic-alignment case: `[1/2, 3/4]`. -/
def exBoxDy : Fin 1 → DInterval := fun _ => ⟨⟨1, -1⟩, ⟨3, -2⟩⟩

/-- `x - 1/4`（二进制有理数，指数为负）。 -/
def exExprDy : IExpr 1 := .sub (.var 0) (.const ⟨1, -2⟩)

/-- Accept: `x - 1/4` on `[1/2, 3/4]` evaluates to `[1/4, 1/2]` —
exercises exponent alignment with negative exponents. -/
theorem exDy_accept : checkPos exExprDy exBoxDy = true := by decide

/-- Precision stress case: `x - 2⁻²⁰` on `[1/2, 1]` (mantissas ~2¹⁹; kernel
`decide` on `Int` handles this trivially). -/
theorem exPrecise_accept :
    checkPos (.sub (.var 0) (.const ⟨1, -20⟩))
      (fun _ : Fin 1 => ⟨⟨1, -1⟩, ⟨1, 0⟩⟩) = true := by decide

/-- The optional box well-formedness check, kernel-verified. -/
theorem exBox_wf : (exBoxPos 0).wf = true := by decide

/-- End-to-end: from the kernel-checked certificate to a real inequality
(`x·y > 0` on `[1,2]²`). -/
theorem exMul_end_to_end (x y : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ 2) (hy0 : 1 ≤ y)
    (hy1 : y ≤ 2) : 0 < x * y := by
  have hmem : ∀ i : Fin 2, (exBoxPos i).mem (![x, y] i) := by
    intro i
    fin_cases i
    · exact ⟨by simpa [exBoxPos] using hx0, by simpa [exBoxPos] using hx1⟩
    · exact ⟨by simpa [exBoxPos] using hy0, by simpa [exBoxPos] using hy1⟩
  have h := checkPos_sound exExprMul exBoxPos exMul_accept ![x, y] hmem
  simpa [exExprMul, IExpr.evalReal] using h

/-- End-to-end with genuine dyadic arithmetic: `x - 1/4 > 0` on `[1/2, 3/4]`. -/
theorem exDy_end_to_end (x : ℝ) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 3 / 4) : 0 < x - 1 / 4 := by
  have hlo : Dyadic.toReal ⟨1, -1⟩ = 1 / 2 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hhi : Dyadic.toReal ⟨3, -2⟩ = 3 / 4 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hconst : Dyadic.toReal ⟨1, -2⟩ = 1 / 4 := by
    rw [Dyadic.toReal_def]
    norm_num
  have hmem : ∀ i : Fin 1, (exBoxDy i).mem ((fun _ => x) i) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨1, -1⟩ ≤ x
      rw [hlo]
      exact hx0
    · show x ≤ Dyadic.toReal ⟨3, -2⟩
      rw [hhi]
      exact hx1
  have h := checkPos_sound exExprDy exBoxDy exDy_accept (fun _ => x) hmem
  simpa [exExprDy, IExpr.evalReal, hconst] using h

/-! ## Pilots for the new node kinds (kernel `decide` only) -/

/-- `1/√x` on `[4, 9]`: the `.sqrt` node's certificates are `⌊√4⌋ = 2` and
`⌊√9⌋ = 3` (mantissas verified in `Int`), giving `√` of the box as
`[2, 4]`; the `.div` node then computes `1/[2,4] = [1/4, 3/4]` at
granularity `2^-2`. -/
def exExprInvSqrt : IExpr 1 :=
  .div (.const ⟨1, 0⟩) (.sqrt (.var 0) 2 3) (-2)

/-- Box `[4, 9]`. -/
def exBoxSqrt : Fin 1 → DInterval := fun _ => ⟨⟨4, 0⟩, ⟨9, 0⟩⟩

/-- Accept: the interval evaluation of `1/√x` on `[4,9]` is `[1/4, 3/4]`
(kernel `decide` runs the whole `Option` pipeline). -/
theorem exInvSqrt_accept : checkPos exExprInvSqrt exBoxSqrt = true := by decide

/-- The full certificate, exposed: `1/√x` evaluates exactly to
`[1/4, 3/4]` on `[4,9]`. -/
theorem exInvSqrt_eval :
    exExprInvSqrt.eval exBoxSqrt = some ⟨⟨1, -2⟩, ⟨3, -2⟩⟩ := by
  decide

/-- End-to-end: `1/√x > 1/5` on `[4,9]` — exercises the `.sqrt` and `.div`
soundness layers over `ℝ`. -/
theorem exInvSqrt_end_to_end (x : ℝ) (hx1 : 4 ≤ x) (hx2 : x ≤ 9) :
    1 / 5 < 1 / Real.sqrt x := by
  have hmem : ∀ i : Fin 1, (exBoxSqrt i).mem ((fun _ => x) i) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨4, 0⟩ ≤ x
      rw [Dyadic.toReal_int]
      exact_mod_cast hx1
    · show x ≤ Dyadic.toReal ⟨9, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  have h := IExpr.eval_mem exExprInvSqrt exBoxSqrt (fun _ => x) hmem
    ⟨⟨1, -2⟩, ⟨3, -2⟩⟩ exInvSqrt_eval
  have hev : exExprInvSqrt.evalReal (fun _ => x) = 1 / Real.sqrt x := by
    simp [exExprInvSqrt, IExpr.evalReal]
  have h1 : Dyadic.toReal ⟨1, -2⟩ ≤ 1 / Real.sqrt x := by
    rw [← hev]
    exact h.1
  have hlo : Dyadic.toReal ⟨1, -2⟩ = 1 / 4 := by
    rw [Dyadic.toReal_def]
    norm_num
  rw [hlo] at h1
  linarith

/-- `sin x - 1/4` on `[1/2, 1]`: the `.trans sinK` node evaluates `sin` on
the whole box (endpoint monotonicity on `[-1,1]` over the point enclosures
at granularity `2^-20`, 5 Taylor terms), then subtracts `1/4`. -/
def exExprSin : IExpr 1 :=
  .sub (.trans .sinK (.var 0) 5 (-20)) (.const ⟨1, -2⟩)

/-- Box `[1/2, 1]`. -/
def exBoxSin : Fin 1 → DInterval := fun _ => ⟨⟨1, -1⟩, ⟨1, 0⟩⟩

/-- Accept: `sin x − 1/4` evaluates to `[502712·2⁻²⁰ − 1/4, …]` with lower
endpoint `> 0` (kernel `decide`). -/
theorem exSin_accept : checkPos exExprSin exBoxSin = true := by decide

/-- End-to-end: `1/4 < sin x` for every real `x ∈ [1/2, 1]`. -/
theorem exSin_end_to_end (x : ℝ) (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 1) :
    1 / 4 < Real.sin x := by
  have hmem : ∀ i : Fin 1, (exBoxSin i).mem ((fun _ => x) i) := by
    intro i
    fin_cases i
    constructor
    · show Dyadic.toReal ⟨1, -1⟩ ≤ x
      rw [Dyadic.toReal_def]
      have h : (((1:ℤ):ℝ)) * (2:ℝ)^((-1:ℤ)) = 1 / 2 := by norm_num
      rw [h]
      exact hx1
    · show x ≤ Dyadic.toReal ⟨1, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  have h := checkPos_sound exExprSin exBoxSin exSin_accept (fun _ => x) hmem
  have hsimp : exExprSin.evalReal (fun _ => x) = Real.sin x - 1 / 4 := by
    simp only [exExprSin, IExpr.evalReal, transReal, Dyadic.toReal_def]
    norm_num
  rw [hsimp] at h
  linarith

end Kepler.Interval
