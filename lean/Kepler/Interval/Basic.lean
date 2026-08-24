/-
  Phase 4 pilot: kernel-checkable interval arithmetic with dyadic endpoints —
  the core layer of the planned "branch-and-bound over boxes" certificate
  checker for Flyspeck nonlinear inequalities (`f(x) > 0` on a box; see
  PLAN.md §2 and docs/module-map.md "非线性不等式"). As in Phase 3
  (`Kepler.LP.Cert`), the kernel **cannot** reduce `Rat` arithmetic
  (`@[extern]`), so every checked datum is integer-shaped and all small
  certificate checks below are closed by kernel `decide` — no `sorry`,
  no `native_decide`, no extra axioms.

  ## Design decisions

  - *Dyadic endpoints (key decision).* A `Dyadic` is a pair `⟨m, e⟩ : Int × Int`
    denoting `m · 2^e`. Rationale:
    + closed under `+`, `-`, `·`, `Neg` *exactly*, with all arithmetic in
      `Int` (kernel/GMP-backed `Nat` literals — the same trick as `LP.Cert`);
    + comparison and sign are *exact* and kernel-decidable: align exponents
      and compare integer mantissas (`ble`), and `d > 0 ↔ 0 < d.m`
      (`isPos_iff`) since `2^e > 0`. Unlike `Rat`, no normalization or gcd
      is ever needed — representations are non-canonical and equality is
      semantic, never syntactic;
    + `m · 2^e` with `e : ℤ` (rather than `m / 2^k`, `k : ℕ`) keeps the
      alignment identity `m·2^e = (m·2^(e-e₀))·2^e₀` uniform (`toRat_align`)
      and matches the usual dyadic-lib/floating-point convention;
    + division and transcendental functions (√, sin, arctan, …) are *not*
      dyadic-exact and are deliberately excluded from this layer — see
      "Next steps" below. This file only does `+ - × Neg`, interval
      comparison/inclusion, and the box-evaluation soundness theorem.
  - *Two layers again (following `LP.Cert`).* Checking layer: `Dyadic` ops
    on `Int`, `Bool` predicates (`ble`, `isPos`, `DInterval.wf`, `checkPos`).
    Semantic layer: `toRat` (via `Int.cast` + `zpow`) and `toReal`, with
    soundness theorems quantified over *reals* (`DInterval.mem`,
    `checkPos_sound`).
  - *Interval multiplication is the min/max of the four corner products.*
    Soundness (`mul_mem_Icc`) is proved via two one-variable sign-split
    lemmas (`mul_bounds_right`/`mul_bounds_left`: for `y ∈ [c,d]`,
    `y·m ∈ [min (c·m) (d·m), max (c·m) (d·m)]`), chained as
    `min₄ ≤ min (a*c, b*c) ≤ x*c` etc.
  - *Total evaluator, no `Option`.* Since `+ - × Neg` are total and always
    sound, `IExpr.eval` returns a `DInterval` directly. The `Option` from
    the design guidance is deferred: it becomes necessary once
    division/reciprocal or transcendental extensions can fail on a box
    (wrapping later is a local change to `eval`/`eval_mem`).
  - *No well-formedness requirement.* `DInterval.mem` never assumes
    `lo ≤ hi` (an empty interval is vacuously sound); `DInterval.wf` is an
    optional checker for certificate hygiene.

  ## Checker core theorem (雏形)

  `checkPos_sound`: if the kernel-decidable check `checkPos e box` passes
  (the lower endpoint of the interval evaluation of `e` over `box` has a
  positive mantissa), then for every real assignment `ρ` pointwise inside
  `box`, `0 < e.evalReal ρ`. This is exactly the per-leaf certificate of
  the branch-and-bound scheme; a future `Kepler.Interval.Cert` will add box
  splitting trees whose leaves carry these checks (sharded `decide`s, the
  `Kepler.Graphs.CertShards` pattern).

  ## Next steps (interface notes for follow-up phases)

  - *Division/reciprocal*: only when `0 ∉` divisor interval; the result is a
    dyadic *approximation with explicit error* at a chosen precision `p`
    (floor/ceil of `m·2^p / m'` in `Int`), i.e. `Option`-valued ops on top
    of this layer. Same pattern for `√` (stretch goal: `Int.sqrt` gives
    `⌊√n⌋² ≤ n < (⌊√n⌋+1)²`; scale the mantissa by `2^(2k)` first).
  - *Transcendentals* (sin, arctan, …): verified Taylor/rational bounds
    packaged as "dyadic value + dyadic radius"; suggest a midpoint-radius
    wrapper instead of complicating this endpoint layer.
  - *Tightness*: interval evaluation is conservative (see
    `exSquare_conservative`: `x²` on `[-1,1]` evaluates to `[-1,1]`, not
    `[0,1]`); the branch-and-bound loop must refine boxes — by design the
    checker only needs the leaf checks.

  Downstream wiring: `Kepler.lean` (import), `docs/module-map.md`.
-/
import Mathlib

namespace Kepler.Interval

/-! ## Dyadic rationals: the checked data layer -/

/-- Dyadic rational `⟨m, e⟩ = m · 2^e`（`m e : Int`，不要求规范形；相等是语义上的）。
对 `+ - × Neg` 精确封闭，全部算术落在 `Int`（内核经 `Nat`/GMP 可算）。 -/
structure Dyadic where
  m : Int
  e : Int
deriving Repr

namespace Dyadic

/-- Semantics over `Rat`: `m · 2^e`. -/
def toRat (d : Dyadic) : Rat := d.m * 2 ^ d.e

/-- Semantics over `ℝ`: the cast of `toRat`. -/
def toReal (d : Dyadic) : ℝ := d.toRat

instance : Neg Dyadic := ⟨fun d => ⟨-d.m, d.e⟩⟩

/-- Addition: align exponents to their `min` and add integer mantissas. -/
def add (a b : Dyadic) : Dyadic :=
  ⟨a.m * 2 ^ (a.e - min a.e b.e).toNat + b.m * 2 ^ (b.e - min a.e b.e).toNat, min a.e b.e⟩

/-- Multiplication: multiply mantissas, add exponents. -/
def mul (a b : Dyadic) : Dyadic := ⟨a.m * b.m, a.e + b.e⟩

/-! ### Correctness of the arithmetic (`toRat` layer) -/

theorem toRat_neg (d : Dyadic) : toRat (-d) = -toRat d := by
  show toRat ⟨-d.m, d.e⟩ = _
  simp [toRat]

theorem toRat_mk_add (p q : Int) (e₀ : ℤ) :
    toRat ⟨p + q, e₀⟩ = toRat ⟨p, e₀⟩ + toRat ⟨q, e₀⟩ := by
  simp [toRat, Int.cast_add, add_mul]

/-- Alignment lemma: lowering the exponent to `e₀ ≤ d.e` (multiplying the
mantissa by `2^(d.e - e₀)`) does not change the semantics. -/
theorem toRat_align (d : Dyadic) (e₀ : ℤ) (h : e₀ ≤ d.e) :
    toRat ⟨d.m * 2 ^ (d.e - e₀).toNat, e₀⟩ = toRat d := by
  have h1 : ((d.e - e₀).toNat : ℤ) = d.e - e₀ := Int.toNat_of_nonneg (by omega)
  simp only [toRat, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_assoc]
  congr 1
  rw [← zpow_natCast, h1, ← zpow_add₀ (by norm_num : (2 : Rat) ≠ 0), sub_add_cancel]

theorem toRat_add (a b : Dyadic) : toRat (a.add b) = toRat a + toRat b := by
  unfold Dyadic.add
  rw [toRat_mk_add, toRat_align a (min a.e b.e) (min_le_left _ _),
    toRat_align b (min a.e b.e) (min_le_right _ _)]

theorem toRat_mul (a b : Dyadic) : toRat (a.mul b) = toRat a * toRat b := by
  show toRat ⟨a.m * b.m, a.e + b.e⟩ = _
  simp only [toRat, Int.cast_mul]
  rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  ring

/-! ### Comparison, sign, `min`/`max` -/

/-- Boolean `≤`: align exponents and compare integer mantissas (kernel-decidable). -/
def ble (a b : Dyadic) : Bool :=
  decide (a.m * 2 ^ (a.e - min a.e b.e).toNat ≤ b.m * 2 ^ (b.e - min a.e b.e).toNat)

theorem le_toRat_of_aligned {a b : Dyadic}
    (h : a.m * 2 ^ (a.e - min a.e b.e).toNat ≤ b.m * 2 ^ (b.e - min a.e b.e).toNat) :
    toRat a ≤ toRat b := by
  rw [← toRat_align a (min a.e b.e) (min_le_left _ _),
    ← toRat_align b (min a.e b.e) (min_le_right _ _)]
  simp only [toRat]
  exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr h)
    (le_of_lt (zpow_pos (by norm_num) (min a.e b.e)))

theorem aligned_of_le_toRat {a b : Dyadic} (h : toRat a ≤ toRat b) :
    a.m * 2 ^ (a.e - min a.e b.e).toNat ≤ b.m * 2 ^ (b.e - min a.e b.e).toNat := by
  rw [← toRat_align a (min a.e b.e) (min_le_left _ _),
    ← toRat_align b (min a.e b.e) (min_le_right _ _)] at h
  simp only [toRat] at h
  exact Int.cast_le.mp (le_of_mul_le_mul_right h (zpow_pos (by norm_num) _))

theorem ble_iff (a b : Dyadic) : ble a b = true ↔ toRat a ≤ toRat b := by
  rw [ble, decide_eq_true_eq]
  exact ⟨le_toRat_of_aligned, aligned_of_le_toRat⟩

theorem toRat_lt_of_ble_false {a b : Dyadic} (h : ble a b = false) : toRat b < toRat a := by
  have h' : ¬ toRat a ≤ toRat b := by
    intro hb
    have ht : ble a b = true := (ble_iff a b).mpr hb
    rw [h] at ht
    simp at ht
  exact not_le.mp h'

/-- Semantic `min` on representatives. -/
def dmin (a b : Dyadic) : Dyadic := if ble a b then a else b

/-- Semantic `max` on representatives. -/
def dmax (a b : Dyadic) : Dyadic := if ble a b then b else a

theorem toRat_dmin (a b : Dyadic) : toRat (dmin a b) = min (toRat a) (toRat b) := by
  unfold dmin
  split
  · next h => exact (min_eq_left ((ble_iff a b).mp h)).symm
  · next h =>
      have h' : ble a b = false := by
        cases hb : ble a b <;> simp_all
      exact (min_eq_right (le_of_lt (toRat_lt_of_ble_false h'))).symm

theorem toRat_dmax (a b : Dyadic) : toRat (dmax a b) = max (toRat a) (toRat b) := by
  unfold dmax
  split
  · next h => exact (max_eq_right ((ble_iff a b).mp h)).symm
  · next h =>
      have h' : ble a b = false := by
        cases hb : ble a b <;> simp_all
      exact (max_eq_left (le_of_lt (toRat_lt_of_ble_false h'))).symm

/-- Strict positivity (exact: the sign of a dyadic is the sign of its mantissa,
since `2^e > 0`). -/
def isPos (d : Dyadic) : Bool := decide (0 < d.m)

/-! ### `toReal` bridge -/

theorem toReal_neg (d : Dyadic) : toReal (-d) = -toReal d := by
  simp [toReal, toRat_neg]

theorem toReal_add (a b : Dyadic) : toReal (a.add b) = toReal a + toReal b := by
  simp [toReal, toRat_add]

theorem toReal_mul (a b : Dyadic) : toReal (a.mul b) = toReal a * toReal b := by
  simp [toReal, toRat_mul]

theorem toReal_dmin (a b : Dyadic) : toReal (dmin a b) = min (toReal a) (toReal b) := by
  simp [toReal, toRat_dmin]

theorem toReal_dmax (a b : Dyadic) : toReal (dmax a b) = max (toReal a) (toReal b) := by
  simp [toReal, toRat_dmax]

theorem toReal_def (d : Dyadic) : toReal d = (d.m : ℝ) * (2 : ℝ) ^ d.e := by
  simp [toReal, toRat]

/-- 指数为零时语义即尾数（小案例 `decide`/end-to-end 定理里常用）。 -/
@[simp] theorem toReal_int (m : Int) : toReal ⟨m, 0⟩ = (m : ℝ) := by
  simp [toReal, toRat]

theorem isPos_iff (d : Dyadic) : d.isPos = true ↔ 0 < d.toReal := by
  simp only [isPos, decide_eq_true_eq, toReal, toRat, Rat.cast_mul, Rat.cast_intCast,
    Rat.cast_zpow, Rat.cast_ofNat]
  rw [mul_comm]
  exact Int.cast_pos.symm.trans
    (mul_pos_iff_of_pos_left (zpow_pos (by norm_num : (0 : ℝ) < 2) d.e)).symm

theorem toReal_pos_of_isPos {d : Dyadic} (h : d.isPos = true) : 0 < d.toReal :=
  d.isPos_iff.mp h

end Dyadic

/-! ## Real helper lemmas for interval multiplication -/

/-- One-variable corner bound (multiplier on the right): for `y ∈ [c,d]`,
`y·m` lies between the corner products `c·m` and `d·m`. -/
theorem mul_bounds_right {c d y : ℝ} (hc : c ≤ y) (hd : y ≤ d) (m : ℝ) :
    min (c * m) (d * m) ≤ y * m ∧ y * m ≤ max (c * m) (d * m) := by
  rcases le_total 0 m with hm | hm
  · have h1 : c * m ≤ y * m := mul_le_mul_of_nonneg_right hc hm
    have h2 : y * m ≤ d * m := mul_le_mul_of_nonneg_right hd hm
    exact ⟨by rwa [min_eq_left (le_trans h1 h2)], by rwa [max_eq_right (le_trans h1 h2)]⟩
  · have h1 : d * m ≤ y * m := mul_le_mul_of_nonpos_right hd hm
    have h2 : y * m ≤ c * m := mul_le_mul_of_nonpos_right hc hm
    exact ⟨by rwa [min_eq_right (le_trans h1 h2)], by rwa [max_eq_left (le_trans h1 h2)]⟩

/-- One-variable corner bound (multiplier on the left). -/
theorem mul_bounds_left {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) (m : ℝ) :
    min (m * a) (m * b) ≤ m * x ∧ m * x ≤ max (m * a) (m * b) := by
  have h := mul_bounds_right ha hb m
  rwa [← mul_comm m a, ← mul_comm m b, ← mul_comm m x] at h

/-- Interval multiplication soundness over `ℝ`: for `x ∈ [a,b]`, `y ∈ [c,d]`,
`x·y` lies between the min and the max of the four corner products. -/
theorem mul_mem_Icc {a b c d x y : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y)
    (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨hxy1, hxy2⟩ := mul_bounds_left hcy hyd x
  obtain ⟨hxc1, hxc2⟩ := mul_bounds_right hax hxb c
  obtain ⟨hxd1, hxd2⟩ := mul_bounds_right hax hxb d
  refine ⟨le_trans ?_ hxy1, le_trans hxy2 ?_⟩
  · exact le_min
      (le_trans (le_min (le_trans (min_le_left _ _) (min_le_left _ _))
        (le_trans (min_le_right _ _) (min_le_left _ _))) hxc1)
      (le_trans (le_min (le_trans (min_le_left _ _) (min_le_right _ _))
        (le_trans (min_le_right _ _) (min_le_right _ _))) hxd1)
  · exact max_le
      (le_trans hxc2 (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _))))
      (le_trans hxd2 (max_le (le_trans (le_max_right _ _) (le_max_left _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _))))

/-! ## Intervals with dyadic endpoints -/

/-- Interval with dyadic endpoints. `lo ≤ hi` is *not* required
(`wf` is an optional check; an empty interval is vacuously sound). -/
structure DInterval where
  lo : Dyadic
  hi : Dyadic
deriving Repr

namespace DInterval

/-- Real membership: `lo ≤ x ≤ hi`. -/
def mem (I : DInterval) (x : ℝ) : Prop := I.lo.toReal ≤ x ∧ x ≤ I.hi.toReal

/-- Optional well-formedness check: `lo ≤ hi`. -/
def wf (I : DInterval) : Bool := Dyadic.ble I.lo I.hi

theorem le_toReal_of_wf {I : DInterval} (h : I.wf = true) : I.lo.toReal ≤ I.hi.toReal :=
  Rat.cast_le.mpr ((Dyadic.ble_iff I.lo I.hi).mp h)

/-- Interval addition. -/
def add (I J : DInterval) : DInterval := ⟨I.lo.add J.lo, I.hi.add J.hi⟩

/-- Interval negation. -/
def neg (I : DInterval) : DInterval := ⟨-I.hi, -I.lo⟩

/-- Interval subtraction. -/
def sub (I J : DInterval) : DInterval := I.add J.neg

/-- Interval multiplication: min/max of the four corner products. -/
def mul (I J : DInterval) : DInterval where
  lo := Dyadic.dmin (Dyadic.dmin (I.lo.mul J.lo) (I.lo.mul J.hi))
    (Dyadic.dmin (I.hi.mul J.lo) (I.hi.mul J.hi))
  hi := Dyadic.dmax (Dyadic.dmax (I.lo.mul J.lo) (I.lo.mul J.hi))
    (Dyadic.dmax (I.hi.mul J.lo) (I.hi.mul J.hi))

theorem mem_add {I J : DInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (I.add J).mem (x + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · show Dyadic.toReal (I.lo.add J.lo) ≤ x + y
    rw [Dyadic.toReal_add]
    exact add_le_add hx1 hy1
  · show x + y ≤ Dyadic.toReal (I.hi.add J.hi)
    rw [Dyadic.toReal_add]
    exact add_le_add hx2 hy2

theorem mem_neg {I : DInterval} {x : ℝ} (hx : I.mem x) : I.neg.mem (-x) := by
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · show Dyadic.toReal (-I.hi) ≤ -x
    rw [Dyadic.toReal_neg]
    exact neg_le_neg hx2
  · show -x ≤ Dyadic.toReal (-I.lo)
    rw [Dyadic.toReal_neg]
    exact neg_le_neg hx1

theorem mem_sub {I J : DInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (I.sub J).mem (x - y) := by
  rw [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

theorem mem_mul {I J : DInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (I.mul J).mem (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hlo, hhi⟩ := mul_mem_Icc hx1 hx2 hy1 hy2
  constructor
  · show Dyadic.toReal (Dyadic.dmin (Dyadic.dmin (I.lo.mul J.lo) (I.lo.mul J.hi))
        (Dyadic.dmin (I.hi.mul J.lo) (I.hi.mul J.hi))) ≤ x * y
    rw [Dyadic.toReal_dmin, Dyadic.toReal_dmin, Dyadic.toReal_dmin,
      Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul]
    exact hlo
  · show x * y ≤ Dyadic.toReal (Dyadic.dmax (Dyadic.dmax (I.lo.mul J.lo) (I.lo.mul J.hi))
        (Dyadic.dmax (I.hi.mul J.lo) (I.hi.mul J.hi)))
    rw [Dyadic.toReal_dmax, Dyadic.toReal_dmax, Dyadic.toReal_dmax,
      Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul, Dyadic.toReal_mul]
    exact hhi

end DInterval

/-! ## Interval expressions and the positivity checker -/

/-- Simple interval expression AST: constants, variables, `+ - × Neg`.
（暂不含除法/超越函数；它们将以"近似 + 显式误差界"在后续层加入。） -/
inductive IExpr (n : ℕ) : Type where
  | const (d : Dyadic) : IExpr n
  | var (i : Fin n) : IExpr n
  | neg (e : IExpr n) : IExpr n
  | add (e₁ e₂ : IExpr n) : IExpr n
  | sub (e₁ e₂ : IExpr n) : IExpr n
  | mul (e₁ e₂ : IExpr n) : IExpr n
deriving Repr

namespace IExpr

/-- Interval evaluation over a box (total: every op is sound). -/
def eval {n : ℕ} : IExpr n → (Fin n → DInterval) → DInterval
  | .const d, _ => ⟨d, d⟩
  | .var i, box => box i
  | .neg e, box => DInterval.neg (e.eval box)
  | .add e₁ e₂, box => DInterval.add (e₁.eval box) (e₂.eval box)
  | .sub e₁ e₂, box => DInterval.sub (e₁.eval box) (e₂.eval box)
  | .mul e₁ e₂, box => DInterval.mul (e₁.eval box) (e₂.eval box)

/-- Real evaluation under a real assignment. -/
def evalReal {n : ℕ} : IExpr n → (Fin n → ℝ) → ℝ
  | .const d, _ => d.toReal
  | .var i, ρ => ρ i
  | .neg e, ρ => -e.evalReal ρ
  | .add e₁ e₂, ρ => e₁.evalReal ρ + e₂.evalReal ρ
  | .sub e₁ e₂, ρ => e₁.evalReal ρ - e₂.evalReal ρ
  | .mul e₁ e₂, ρ => e₁.evalReal ρ * e₂.evalReal ρ

/-- **Soundness of interval evaluation**: the interval value contains the real
value for every assignment pointwise inside the box. -/
theorem eval_mem {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) (ρ : Fin n → ℝ)
    (hρ : ∀ i, (box i).mem (ρ i)) : (e.eval box).mem (e.evalReal ρ) := by
  induction e with
  | const d => exact ⟨le_rfl, le_rfl⟩
  | var i => exact hρ i
  | neg e ih => exact DInterval.mem_neg ih
  | add e₁ e₂ ih₁ ih₂ => exact DInterval.mem_add ih₁ ih₂
  | sub e₁ e₂ ih₁ ih₂ => exact DInterval.mem_sub ih₁ ih₂
  | mul e₁ e₂ ih₁ ih₂ => exact DInterval.mem_mul ih₁ ih₂

end IExpr

/-- The positivity checker: kernel-decidable, all arithmetic in `Int`. -/
def checkPos {n : ℕ} (e : IExpr n) (box : Fin n → DInterval) : Bool :=
  (e.eval box).lo.isPos

/-- **Core checker theorem (雏形)**: if `checkPos` passes, the expression is
strictly positive at every real assignment pointwise inside the box. -/
theorem checkPos_sound {n : ℕ} (e : IExpr n) (box : Fin n → DInterval)
    (h : checkPos e box = true) (ρ : Fin n → ℝ) (hρ : ∀ i, (box i).mem (ρ i)) :
    0 < e.evalReal ρ :=
  lt_of_lt_of_le (Dyadic.toReal_pos_of_isPos h) (e.eval_mem box ρ hρ).1

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

end Kepler.Interval
