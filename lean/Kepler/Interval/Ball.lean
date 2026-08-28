/-
  Phase 4, step 3: **midpoint-radius balls** over dyadic endpoints.

  The endpoint layer (`DInterval` in `Kepler.Interval.Basic`) is the right shape
  for `+ - ×` and for leaf checks, but transcendental *approximations* are
  naturally produced as "dyadic value + dyadic error bound" (a Taylor value and
  its remainder, a `divFloorQ` result and its ulp, …).  `Ball` packages exactly
  that (this follows the "Next steps" note in `Basic.lean`: *"suggest a
  midpoint-radius wrapper instead of complicating this endpoint layer"*):

  - `Ball = ⟨c, r⟩` with `Ball.mem b x : Prop := |x - c.toReal| ≤ r.toReal`
    (semantic layer, over `ℝ`);
  - exact bidirectional conversions with `DInterval`:
    `Ball.toInterval_mem_iff`, `DInterval.midRadius` (the midpoint `(lo+hi)/2`
    and halfwidth `(hi-lo)/2` are *exact* dyadics — halving is an exponent
    decrement), with `mem_midRadius` / `midRadius_mem` in both directions;
  - sound ball arithmetic `add`, `neg`, `sub`, `mul` (radius of a product:
    `|c₁|·r₂ + r₁·(|c₂| + r₂)`) — enough to compose a transcendental ball with
    polynomial tails without leaving the midpoint-radius representation.

  Checking layer: `Int` only. No `sorry`, no `native_decide`, no new axioms.
-/
import Kepler.Interval.Basic

namespace Kepler.Interval

/-! ## Dyadic helpers: alignment (ℝ), subtraction, absolute value -/

namespace Dyadic

/-- Lowering the exponent to `e₀ ≤ d.e` does not change the semantics (ℝ
version of `toRat_align`). -/
theorem toReal_align' (d : Dyadic) (e₀ : ℤ) (h : e₀ ≤ d.e) :
    Dyadic.toReal ⟨d.m * 2 ^ (d.e - e₀).toNat, e₀⟩ = d.toReal := by
  have hr := toRat_align d e₀ h
  simp only [Dyadic.toReal]
  rw [hr]

/-- Semantic subtraction on dyadics (via `add`/`Neg`). -/
def dsub (a b : Dyadic) : Dyadic := a.add (-b)

theorem toReal_dsub (a b : Dyadic) : (a.dsub b).toReal = a.toReal - b.toReal := by
  unfold dsub
  rw [toReal_add, toReal_neg]
  ring

/-- Absolute value on dyadics (mantissa sign flip; kernel-decidable). -/
def absD (d : Dyadic) : Dyadic := ⟨if 0 ≤ d.m then d.m else -d.m, d.e⟩

theorem toReal_absD (d : Dyadic) : (d.absD).toReal = |d.toReal| := by
  have hp : (0:ℝ) < (2:ℝ)^d.e := zpow_pos (by norm_num) d.e
  unfold absD
  split
  · next hm =>
    have h0 : (0:ℝ) ≤ d.toReal := by
      rw [toReal_def]
      exact mul_nonneg (by exact_mod_cast hm) (le_of_lt hp)
    rw [abs_of_nonneg h0]
  · next hm =>
    have hlt : d.m < 0 := Int.lt_of_not_ge hm
    have h0 : d.toReal < 0 := by
      rw [toReal_def]
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hlt) hp
    rw [abs_of_neg h0, toReal_def, toReal_def]
    push_cast
    ring

end Dyadic

/-! ## The midpoint-radius wrapper -/

/-- A dyadic midpoint-radius ball: `c` is the (dyadic) center, `r` the
(dyadic) radius; membership `|x - c.toReal| ≤ r.toReal` is a statement over
`ℝ`.  A negative `r` simply makes the ball (vacuously) empty. -/
structure Ball where
  c : Dyadic
  r : Dyadic
  deriving Repr, DecidableEq

namespace Ball

/-- Real membership: `|x − c| ≤ r`. -/
def mem (b : Ball) (x : ℝ) : Prop := |x - b.c.toReal| ≤ b.r.toReal

/-- The endpoint interval `[c − r, c + r]` of a ball. -/
def toInterval (b : Ball) : DInterval := ⟨b.c.dsub b.r, b.c.add b.r⟩

/-- A ball and its endpoint interval have the same real members. -/
theorem toInterval_mem_iff (b : Ball) (x : ℝ) :
    b.toInterval.mem x ↔ b.mem x := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [show b.toInterval.lo = b.c.dsub b.r from rfl] at h1
    rw [show b.toInterval.hi = b.c.add b.r from rfl] at h2
    rw [Dyadic.toReal_dsub] at h1
    rw [Dyadic.toReal_add] at h2
    show |x - b.c.toReal| ≤ b.r.toReal
    rw [abs_le]
    constructor <;> linarith
  · intro h
    have h2 := abs_le.mp h
    constructor
    · show Dyadic.toReal (b.c.dsub b.r) ≤ x
      rw [Dyadic.toReal_dsub]
      linarith
    · show x ≤ Dyadic.toReal (b.c.add b.r)
      rw [Dyadic.toReal_add]
      linarith

/-! ### Sound ball arithmetic -/

/-- Ball addition (centers and radii add exactly). -/
def add (a b : Ball) : Ball := ⟨a.c.add b.c, a.r.add b.r⟩

theorem mem_add {a b : Ball} {x y : ℝ} (hx : a.mem x) (hy : b.mem y) :
    (a.add b).mem (x + y) := by
  show |x + y - Dyadic.toReal (a.c.add b.c)| ≤ Dyadic.toReal (a.r.add b.r)
  rw [Dyadic.toReal_add, Dyadic.toReal_add]
  have key : x + y - (a.c.toReal + b.c.toReal)
      = (x - a.c.toReal) + (y - b.c.toReal) := by ring
  rw [key]
  calc |x - a.c.toReal + (y - b.c.toReal)|
      ≤ |x - a.c.toReal| + |y - b.c.toReal| := abs_add_le _ _
    _ ≤ a.r.toReal + b.r.toReal := add_le_add hx hy

/-- Ball negation. -/
def neg (a : Ball) : Ball := ⟨-a.c, a.r⟩

theorem mem_neg {a : Ball} {x : ℝ} (hx : a.mem x) : a.neg.mem (-x) := by
  show |-x - Dyadic.toReal (-a.c)| ≤ a.r.toReal
  rw [Dyadic.toReal_neg]
  have key : -x - -(a.c.toReal) = -(x - a.c.toReal) := by ring
  rw [key, abs_neg]
  exact hx

/-- Ball subtraction. -/
def sub (a b : Ball) : Ball := a.add b.neg

theorem mem_sub {a b : Ball} {x y : ℝ} (hx : a.mem x) (hy : b.mem y) :
    (a.sub b).mem (x - y) := by
  have h := mem_add hx (mem_neg hy)
  rwa [sub_eq_add_neg]

/-- Ball multiplication: radius `r₁·(|c₂| + r₂) + |c₁|·r₂`
(truncation of `|x y − c₁ c₂| ≤ |x−c₁|·|y| + |c₁|·|y−c₂|` with
`|y| ≤ |c₂| + r₂`). -/
def mul (a b : Ball) : Ball where
  c := a.c.mul b.c
  r := (a.r.mul (b.c.absD.add b.r)).add (b.r.mul a.c.absD)

theorem mem_mul {a b : Ball} {x y : ℝ} (hx : a.mem x) (hy : b.mem y) :
    (a.mul b).mem (x * y) := by
  have hx' : |x - a.c.toReal| ≤ a.r.toReal := hx
  have hy' : |y - b.c.toReal| ≤ b.r.toReal := hy
  have haR : (0:ℝ) ≤ a.r.toReal := le_trans (abs_nonneg _) hx'
  have hyb : |y| ≤ |b.c.toReal| + b.r.toReal := by
    have h1 : |y| ≤ |b.c.toReal| + |y - b.c.toReal| := by
      calc |y| = |b.c.toReal + (y - b.c.toReal)| := by ring_nf
        _ ≤ |b.c.toReal| + |y - b.c.toReal| := abs_add_le _ _
    linarith
  show |x * y - Dyadic.toReal (a.c.mul b.c)|
    ≤ Dyadic.toReal ((a.r.mul (b.c.absD.add b.r)).add (b.r.mul a.c.absD))
  simp only [Dyadic.toReal_mul, Dyadic.toReal_add, Dyadic.toReal_absD]
  have key : x * y - a.c.toReal * b.c.toReal
      = (x - a.c.toReal) * y + a.c.toReal * (y - b.c.toReal) := by ring
  rw [key]
  calc |(x - a.c.toReal) * y + a.c.toReal * (y - b.c.toReal)|
      ≤ |(x - a.c.toReal) * y| + |a.c.toReal * (y - b.c.toReal)| := abs_add_le _ _
    _ = |x - a.c.toReal| * |y| + |a.c.toReal| * |y - b.c.toReal| := by
        rw [abs_mul, abs_mul]
    _ ≤ a.r.toReal * (|b.c.toReal| + b.r.toReal) + b.r.toReal * |a.c.toReal| := by
        refine add_le_add ?_ ?_
        · calc |x - a.c.toReal| * |y|
              ≤ |x - a.c.toReal| * (|b.c.toReal| + b.r.toReal) :=
                mul_le_mul_of_nonneg_left hyb (abs_nonneg _)
            _ ≤ a.r.toReal * (|b.c.toReal| + b.r.toReal) :=
                mul_le_mul_of_nonneg_right hx' (by linarith [abs_nonneg y, hyb])
        · calc |a.c.toReal| * |y - b.c.toReal|
              ≤ |a.c.toReal| * b.r.toReal := mul_le_mul_of_nonneg_left hy' (abs_nonneg _)
            _ = b.r.toReal * |a.c.toReal| := by ring

end Ball

/-! ## Conversion from endpoint intervals: exact midpoint and halfwidth -/

namespace DInterval

/-- The midpoint-radius form of an interval: the midpoint `(lo + hi)/2` and
halfwidth `(hi − lo)/2` are exact dyadics (align exponents, then halve by
decrementing the exponent). -/
def midRadius (I : DInterval) : Ball where
  c := ⟨I.lo.m * 2 ^ (I.lo.e - min I.lo.e I.hi.e).toNat
      + I.hi.m * 2 ^ (I.hi.e - min I.lo.e I.hi.e).toNat,
    min I.lo.e I.hi.e - 1⟩
  r := ⟨I.hi.m * 2 ^ (I.hi.e - min I.lo.e I.hi.e).toNat
      - I.lo.m * 2 ^ (I.lo.e - min I.lo.e I.hi.e).toNat,
    min I.lo.e I.hi.e - 1⟩

theorem midRadius_center (I : DInterval) :
    I.midRadius.c.toReal * 2 = I.lo.toReal + I.hi.toReal := by
  have h1 := Dyadic.toReal_align' I.lo (min I.lo.e I.hi.e) (min_le_left _ _)
  have h2 := Dyadic.toReal_align' I.hi (min I.lo.e I.hi.e) (min_le_right _ _)
  show Dyadic.toReal ⟨I.lo.m * 2 ^ (I.lo.e - min I.lo.e I.hi.e).toNat
      + I.hi.m * 2 ^ (I.hi.e - min I.lo.e I.hi.e).toNat,
      min I.lo.e I.hi.e - 1⟩ * 2 = _
  rw [← h1, ← h2, Dyadic.toReal_def, Dyadic.toReal_def, Dyadic.toReal_def]
  dsimp only
  have hz : (2:ℝ)^((min I.lo.e I.hi.e : ℤ) - 1) * 2
      = (2:ℝ)^(min I.lo.e I.hi.e : ℤ) := by
    have h := zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) ((min I.lo.e I.hi.e : ℤ) - 1) 1
    rw [sub_add_cancel] at h
    simpa using h.symm
  rw [mul_assoc, hz]
  push_cast
  ring

theorem midRadius_half (I : DInterval) :
    I.midRadius.r.toReal * 2 = I.hi.toReal - I.lo.toReal := by
  have h1 := Dyadic.toReal_align' I.lo (min I.lo.e I.hi.e) (min_le_left _ _)
  have h2 := Dyadic.toReal_align' I.hi (min I.lo.e I.hi.e) (min_le_right _ _)
  show Dyadic.toReal ⟨I.hi.m * 2 ^ (I.hi.e - min I.lo.e I.hi.e).toNat
      - I.lo.m * 2 ^ (I.lo.e - min I.lo.e I.hi.e).toNat,
      min I.lo.e I.hi.e - 1⟩ * 2 = _
  rw [← h1, ← h2, Dyadic.toReal_def, Dyadic.toReal_def, Dyadic.toReal_def]
  dsimp only
  have hz : (2:ℝ)^((min I.lo.e I.hi.e : ℤ) - 1) * 2
      = (2:ℝ)^(min I.lo.e I.hi.e : ℤ) := by
    have h := zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) ((min I.lo.e I.hi.e : ℤ) - 1) 1
    rw [sub_add_cancel] at h
    simpa using h.symm
  rw [mul_assoc, hz]
  push_cast
  ring

/-- Soundness (endpoints → ball): every member of the interval is in its
midpoint-radius form. -/
theorem mem_midRadius {I : DInterval} {x : ℝ} (h : I.mem x) :
    I.midRadius.mem x := by
  obtain ⟨h1, h2⟩ := h
  have hc := I.midRadius_center
  have hr := I.midRadius_half
  show |x - I.midRadius.c.toReal| ≤ I.midRadius.r.toReal
  rw [abs_le]
  constructor <;> linarith

/-- Soundness (ball → endpoints): every member of the midpoint-radius form is
in the interval (holds unconditionally: for a non-well-formed interval the
ball is vacuous, since the identities force `c ± r = lo/hi`). -/
theorem midRadius_mem {I : DInterval} {x : ℝ} (h : I.midRadius.mem x) :
    I.mem x := by
  have hc := I.midRadius_center
  have hr := I.midRadius_half
  have h2 := abs_le.mp h
  constructor <;> linarith

end DInterval

/-! ## Small pilot cases (kernel `decide` only) -/

-- `[1,2]` has exact midpoint `3/2` and halfwidth `1/2` (dyadics `⟨3,-1⟩` and
-- `⟨1,-1⟩`), computed by kernel `decide`.
theorem exMidRadius :
    (⟨⟨1, 0⟩, ⟨2, 0⟩⟩ : DInterval).midRadius = ⟨⟨3, -1⟩, ⟨1, -1⟩⟩ := by
  decide

-- Ball multiplication demo (kernel `decide`): the product of the ball
-- `1 ± 1/8` with itself is `1 ± 17/64`, since the radius formula gives
-- `1/8·(1 + 1/8) + 1/8·1 = 9/64 + 8/64 = 17/64`.
theorem exBallMul :
    (Ball.mul ⟨⟨1, 0⟩, ⟨1, -3⟩⟩ ⟨⟨1, 0⟩, ⟨1, -3⟩⟩)
      = ⟨⟨1, 0⟩, ⟨17, -6⟩⟩ := by
  decide

end Kepler.Interval
