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
    sound, the arithmetic-only `IExpr` of the first pilot returned a
    `DInterval` directly. Division, `√` and the transcendental nodes *can*
    fail on a box, so the extended AST `Kepler.Interval.Expr.IExpr` evaluates
    into `Option DInterval` (`none` = check failed, never unsound).
  - *No well-formedness requirement.* `DInterval.mem` never assumes
    `lo ≤ hi` (an empty interval is vacuously sound); `DInterval.wf` is an
    optional checker for certificate hygiene.

  ## Checker core theorem (雏形)

  `checkPos_sound`: if the kernel-decidable check `checkPos e box` passes
  (the lower endpoint of the interval evaluation of `e` over `box` has a
  positive mantissa), then for every real assignment `ρ` pointwise inside
  `box`, `0 < e.evalReal ρ`. This is exactly the per-leaf certificate of
  the branch-and-bound scheme; `Kepler.Interval.Cert` adds the box
  splitting trees whose leaves carry these checks (sharded `decide`s, the
  `Kepler.Graphs.CertShards` pattern).

  ## Next steps (interface notes for follow-up phases)

  - *Division/reciprocal* (**done**): `Kepler.Interval.Div` — `divFloorQ`
    with an explicit one-ulp error, `DInterval.recip`/`div` in `Option`.
  - *Square roots* (**done**): `Kepler.Interval.Sqrt` — certificate-based
    `Dyadic.sqrtI` (the caller supplies the root mantissa; the kernel only
    checks `s² ≤ n < (s+1)²` in `Int`).
  - *Transcendentals* (**done, base layer**): `Kepler.Interval.Trans` —
    verified alternating-Taylor enclosures for `sin`/`cos`/`arctan`
    packaged as dyadic intervals/balls, plus π-shift range reduction.
    They enter the AST through the `.trans` node of
    `Kepler.Interval.Expr.IExpr`.
  - *Expression AST* (**moved**): `IExpr`/`checkPos` and the pilot
    examples now live in `Kepler.Interval.Expr`, where the extended AST
    (`.div`/`.sqrt`/`.trans`, `Option`-valued evaluation) can see the
    `Div`/`Sqrt`/`Trans` layers without import cycles.
  - *Tightness*: interval evaluation is conservative (see
    `exSquare_conservative` in `Expr.lean`: `x²` on `[-1,1]` evaluates to
    `[-1,1]`, not `[0,1]`); the branch-and-bound loop must refine boxes —
    by design the checker only needs the leaf checks.

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
  deriving Repr, DecidableEq

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

/-- Strict boolean `<` (mirror of `ble`; kernel-decidable). -/
def blt (a b : Dyadic) : Bool := !ble b a

theorem blt_iff (a b : Dyadic) : blt a b = true ↔ toRat a < toRat b := by
  unfold blt
  constructor
  · intro h
    have h' : ble b a = false := by simp at h; exact h
    exact toRat_lt_of_ble_false h'
  · intro h
    have h' : ble b a = false := by
      cases hb : ble b a with
      | false => rfl
      | true =>
          have hle := (ble_iff b a).mp hb
          exact absurd h (by linarith)
    simp only [Bool.not_eq_true', h']

/-- Boolean `≤` lifted to `ℝ` (semantic bridge used by the interval-level
transcendental wrappers in `Trans.lean`). -/
theorem ble_toReal {a b : Dyadic} (h : ble a b = true) : a.toReal ≤ b.toReal :=
  Rat.cast_le.mpr ((ble_iff a b).mp h)

theorem blt_toReal {a b : Dyadic} (h : blt a b = true) : a.toReal < b.toReal :=
  Rat.cast_lt.mpr ((blt_iff a b).mp h)

/-- Nonnegativity (exact: the sign of a dyadic is the sign of its mantissa). -/
def isNN (d : Dyadic) : Bool := decide (0 ≤ d.m)

theorem isNN_iff (d : Dyadic) : d.isNN = true ↔ 0 ≤ d.toReal := by
  have hp : (0:ℝ) < (2:ℝ)^d.e := zpow_pos (by norm_num) d.e
  simp only [isNN, decide_eq_true_eq, toReal_def]
  constructor
  · intro h
    exact mul_nonneg (by exact_mod_cast h) (le_of_lt hp)
  · intro h
    rcases le_or_gt 0 d.m with hm | hm
    · exact hm
    · exact absurd (mul_neg_of_neg_of_pos (show ((d.m : ℤ):ℝ) < 0 by exact_mod_cast hm) hp)
        (by linarith)

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
  deriving Repr, DecidableEq

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

end Kepler.Interval
