/-
Wt1Check.ZPlan — lane `wt1-checker-w1` (2026-11-25).

Reflective interval-arithmetic checker for the D11 leaf cone.

Design
------
* `ZInt` is an interval with *fixed-point integer* endpoints on the grid
  `k / 2^96`.  All operations are transparent `def`s on `ℤ`, so the kernel can
  evaluate them (`by decide`), unlike `Rat`, whose `mul`/`add`/`inv`/`sub` are
  `@[irreducible]` in core and therefore opaque to the kernel.
* `ZInt.memR I x` is the real-membership predicate; `memR_*` prove that every
  operation is sound.  `mul` and `inv` round outward (floor for `lo`, ceiling
  for `hi`), so the only loss is one grid unit per operation.
* `Op` is a stack-machine program: `sl i` pushes input `i`, `dup d` copies the
  entry `d` deep in the stack, and the arithmetic ops pop/push.  `run` computes
  over `ZInt` (kernel-evaluable), `runR` over `ℝ` (the *specification*
  semantics).  `run_sound` is the single reflective-soundness theorem: the
  integer program refines the real program whenever the inputs do.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.QInterval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option maxRecDepth 400000
set_option maxHeartbeats 2000000

namespace Wt1Check

/-- Grid denominator `2^96` (integers). -/
def GD : ℤ := 2 ^ 96

/-- Grid denominator `2^96` (reals). -/
def GR : ℝ := 2 ^ 96

theorem GD_cast : ((GD : ℤ) : ℝ) = GR := by norm_num [GD, GR]

theorem GR_pos : (0 : ℝ) < GR := by norm_num [GR]

theorem GR_ne : (GR : ℝ) ≠ 0 := ne_of_gt GR_pos

/-- A closed interval with integer endpoints, meaning `[lo/2^96, hi/2^96]`. -/
structure ZInt where
  lo : ℤ
  hi : ℤ
  deriving Repr, DecidableEq

namespace ZInt

/-- Real membership in the fixed-point interval. -/
def memR (I : ZInt) (x : ℝ) : Prop := (I.lo : ℝ) / GR ≤ x ∧ x ≤ (I.hi : ℝ) / GR

/-- Point interval at `z / 2^96`. -/
def const (z : ℤ) : ZInt := ⟨z, z⟩

/-- Exact interval addition. -/
def add (I J : ZInt) : ZInt := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Exact interval negation. -/
def neg (I : ZInt) : ZInt := ⟨-I.hi, -I.lo⟩

/-- Exact interval subtraction. -/
def sub (I J : ZInt) : ZInt := I.add J.neg

/-- `floor (a / 2^96)`: downward rounding of a product endpoint. -/
def fsc (a : ℤ) : ℤ := a.fdiv GD

/-- `ceil (a / 2^96)`: upward rounding of a product endpoint. -/
def csc (a : ℤ) : ℤ := -((-a).fdiv GD)

/-- Interval multiplication, all four corner products rounded outward. -/
def mul (I J : ZInt) : ZInt where
  lo := min (min (fsc (I.lo * J.lo)) (fsc (I.lo * J.hi)))
        (min (fsc (I.hi * J.lo)) (fsc (I.hi * J.hi)))
  hi := max (max (csc (I.lo * J.lo)) (csc (I.lo * J.hi)))
        (max (csc (I.hi * J.lo)) (csc (I.hi * J.hi)))

/-- Interval reciprocal, defined only away from zero: a straddling interval
makes the program fail (this is the `posZ` check, folded into the computation). -/
def inv? (I : ZInt) : Option ZInt :=
  if 0 < I.lo ∨ I.hi < 0 then some ⟨(GD * GD).fdiv I.hi, -((-(GD * GD)).fdiv I.lo)⟩
  else none

/-! ### Rounding lemmas -/

theorem fdiv_mul_le_of_pos {a b : ℤ} (hb : 0 < b) : a.fdiv b * b ≤ a := by
  rw [Int.fdiv_mul_self]
  have := Int.fmod_nonneg_of_pos a hb
  linarith

/-- `floor (a/b) ≤ a/b` in `ℝ`, positive divisor. -/
theorem fdiv_le_div_of_pos {a b : ℤ} (hb : 0 < b) : ((a.fdiv b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  have h := fdiv_mul_le_of_pos (a := a) hb
  have h2 := (Int.cast_le (R := ℝ)).mpr h
  rwa [Int.cast_mul] at h2

/-- `floor (a/b) ≤ a/b` in `ℝ`, any nonzero divisor. -/
theorem fdiv_le_div {a b : ℤ} (hb : b ≠ 0) : ((a.fdiv b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rcases lt_or_gt_of_ne (Ne.symm hb) with h | h
  · exact fdiv_le_div_of_pos h
  · have hpos : (0 : ℤ) < -b := by linarith
    have h1 : a.fdiv b = (-a).fdiv (-b) := (Int.neg_fdiv_neg a b).symm
    rw [h1]
    have h2 := fdiv_le_div_of_pos (a := -a) (b := -b) hpos
    rw [show ((-b : ℤ) : ℝ) = -(b : ℝ) by simp,
      show ((-a : ℤ) : ℝ) = -(a : ℝ) by simp] at h2
    have h3 : (-(a : ℝ)) / (-(b : ℝ)) = (a : ℝ) / b := by
      rw [neg_div, div_neg, neg_neg]
    rwa [h3] at h2

/-- `a/b ≤ ceil (a/b)` in `ℝ`, any nonzero divisor. -/
theorem le_cdiv_div {a b : ℤ} (hb : b ≠ 0) :
    (a : ℝ) / b ≤ ((-((-a).fdiv b) : ℤ) : ℝ) := by
  have h := fdiv_le_div (a := -a) (b := b) hb
  rw [show ((-a : ℤ) : ℝ) = -(a : ℝ) by simp, neg_div] at h
  rw [show ((-((-a).fdiv b) : ℤ) : ℝ) = -((((-a).fdiv b : ℤ)) : ℝ) by simp]
  linarith

theorem fsc_mul_le (a : ℤ) : (fsc a : ℝ) * GR ≤ (a : ℝ) := by
  have h : fsc a * GD ≤ a := fdiv_mul_le_of_pos (by decide : (0 : ℤ) < GD)
  have h2 := (Int.cast_le (R := ℝ)).mpr h
  rwa [Int.cast_mul, GD_cast] at h2

theorem fsc_le (a : ℤ) : (fsc a : ℝ) ≤ (a : ℝ) / GR := by
  rw [le_div_iff₀ GR_pos]
  exact fsc_mul_le a

/-- The four-corner bound, copied from `QInterval.mul_mem_Icc`. -/
private theorem mul_bounds_right {c d y : ℝ} (hc : c ≤ y) (hd : y ≤ d) (m : ℝ) :
    min (c * m) (d * m) ≤ y * m ∧ y * m ≤ max (c * m) (d * m) := by
  rcases le_total 0 m with hm | hm
  · have h1 : c * m ≤ y * m := mul_le_mul_of_nonneg_right hc hm
    have h2 : y * m ≤ d * m := mul_le_mul_of_nonneg_right hd hm
    exact ⟨by rwa [min_eq_left (le_trans h1 h2)], by rwa [max_eq_right (le_trans h1 h2)]⟩
  · have h1 : d * m ≤ y * m := mul_le_mul_of_nonpos_right hd hm
    have h2 : y * m ≤ c * m := mul_le_mul_of_nonpos_right hc hm
    exact ⟨by rwa [min_eq_right (le_trans h1 h2)], by rwa [max_eq_left (le_trans h1 h2)]⟩

private theorem mul_bounds_left {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) (m : ℝ) :
    min (m * a) (m * b) ≤ m * x ∧ m * x ≤ max (m * a) (m * b) := by
  have h := mul_bounds_right ha hb m
  rwa [← mul_comm m a, ← mul_comm m b, ← mul_comm m x] at h

private theorem mul_mem_Icc {a b c d x y : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y)
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

/-! ### Operation soundness -/

theorem memR_const (z : ℤ) : (const z).memR ((z : ℝ) / GR) := ⟨le_rfl, le_rfl⟩

theorem memR_add {I J : ZInt} {x y : ℝ} (hx : I.memR x) (hy : J.memR y) :
    (add I J).memR (x + y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · simp only [add, Int.cast_add, add_div]
    linarith
  · simp only [add, Int.cast_add, add_div]
    linarith

theorem memR_neg {I : ZInt} {x : ℝ} (hx : I.memR x) : (neg I).memR (-x) := by
  obtain ⟨hx1, hx2⟩ := hx
  constructor
  · simp only [neg, Int.cast_neg, neg_div]
    linarith
  · simp only [neg, Int.cast_neg, neg_div]
    linarith

theorem memR_sub {I J : ZInt} {x y : ℝ} (hx : I.memR x) (hy : J.memR y) :
    (sub I J).memR (x - y) := by
  rw [sub_eq_add_neg]
  exact memR_add hx (memR_neg hy)

/-- `min` of four reals, normalised against the grid division. -/
private theorem min4_scaleR (a b c d : ℝ) :
    min (min (a / GR) (b / GR)) (min (c / GR) (d / GR))
      = min (min a b) (min c d) / GR := by
  rw [min_div_div_right (le_of_lt GR_pos), min_div_div_right (le_of_lt GR_pos),
    min_div_div_right (le_of_lt GR_pos)]

/-- `max` of four reals, normalised against the grid division. -/
private theorem max4_scaleR (a b c d : ℝ) :
    max (max (a / GR) (b / GR)) (max (c / GR) (d / GR))
      = max (max a b) (max c d) / GR := by
  rw [max_div_div_right (le_of_lt GR_pos), max_div_div_right (le_of_lt GR_pos),
    max_div_div_right (le_of_lt GR_pos)]

theorem memR_mul {I J : ZInt} {x y : ℝ} (hx : I.memR x) (hy : J.memR y) :
    (mul I J).memR (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hXm : (I.lo : ℝ) ≤ x * GR := by
    have h := hx1; rw [div_le_iff₀ GR_pos] at h; linarith
  have hXM : x * GR ≤ (I.hi : ℝ) := by
    have h := hx2; rw [le_div_iff₀ GR_pos] at h; linarith
  have hYm : (J.lo : ℝ) ≤ y * GR := by
    have h := hy1; rw [div_le_iff₀ GR_pos] at h; linarith
  have hYM : y * GR ≤ (J.hi : ℝ) := by
    have h := hy2; rw [le_div_iff₀ GR_pos] at h; linarith
  obtain ⟨hlo, hhi⟩ := mul_mem_Icc hXm hXM hYm hYM
  have hlo' : min (min ((I.lo * J.lo : ℤ) : ℝ) ((I.lo * J.hi : ℤ) : ℝ))
      (min ((I.hi * J.lo : ℤ) : ℝ) ((I.hi * J.hi : ℤ) : ℝ)) ≤ x * y * (GR * GR) := by
    have h : min (min ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)))
        (min ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ))) ≤
        (x * GR) * (y * GR) := hlo
    rw [show (x * GR) * (y * GR) = x * y * (GR * GR) by ring] at h
    simpa only [Int.cast_mul] using h
  have hhi' : x * y * (GR * GR) ≤
      max (max ((I.lo * J.lo : ℤ) : ℝ) ((I.lo * J.hi : ℤ) : ℝ))
        (max ((I.hi * J.lo : ℤ) : ℝ) ((I.hi * J.hi : ℤ) : ℝ)) := by
    have h : (x * GR) * (y * GR) ≤
        max (max ((I.lo : ℝ) * (J.lo : ℝ)) ((I.lo : ℝ) * (J.hi : ℝ)))
          (max ((I.hi : ℝ) * (J.lo : ℝ)) ((I.hi : ℝ) * (J.hi : ℝ))) := hhi
    rw [show (x * GR) * (y * GR) = x * y * (GR * GR) by ring] at h
    simpa only [Int.cast_mul] using h
  constructor
  · have hf1 : ((fsc (I.lo * J.lo) : ℤ) : ℝ) ≤ ((I.lo * J.lo : ℤ) : ℝ) / GR := fsc_le _
    have hf2 : ((fsc (I.lo * J.hi) : ℤ) : ℝ) ≤ ((I.lo * J.hi : ℤ) : ℝ) / GR := fsc_le _
    have hf3 : ((fsc (I.hi * J.lo) : ℤ) : ℝ) ≤ ((I.hi * J.lo : ℤ) : ℝ) / GR := fsc_le _
    have hf4 : ((fsc (I.hi * J.hi) : ℤ) : ℝ) ≤ ((I.hi * J.hi : ℤ) : ℝ) / GR := fsc_le _
    have he : ((mul I J).lo : ℝ) / GR =
        min (min ((fsc (I.lo * J.lo) : ℤ) : ℝ) ((fsc (I.lo * J.hi) : ℤ) : ℝ))
          (min ((fsc (I.hi * J.lo) : ℤ) : ℝ) ((fsc (I.hi * J.hi) : ℤ) : ℝ)) / GR := by
      simp only [mul, Int.cast_min]
    rw [he]
    have h1 : min (min ((fsc (I.lo * J.lo) : ℤ) : ℝ) ((fsc (I.lo * J.hi) : ℤ) : ℝ))
        (min ((fsc (I.hi * J.lo) : ℤ) : ℝ) ((fsc (I.hi * J.hi) : ℤ) : ℝ)) / GR ≤
        min (min ((I.lo * J.lo : ℤ) : ℝ) ((I.lo * J.hi : ℤ) : ℝ))
          (min ((I.hi * J.lo : ℤ) : ℝ) ((I.hi * J.hi : ℤ) : ℝ)) / GR / GR := by
      rw [div_le_div_iff_of_pos_right GR_pos, ← min4_scaleR]
      exact min_le_min (min_le_min hf1 hf2) (min_le_min hf3 hf4)
    refine le_trans h1 ?_
    rw [div_div, div_le_iff₀ (mul_pos GR_pos GR_pos)]
    exact hlo'
  · have hf1 : ((I.lo * J.lo : ℤ) : ℝ) / GR ≤ ((csc (I.lo * J.lo) : ℤ) : ℝ) := by
      have h := le_cdiv_div (a := I.lo * J.lo) (b := GD) (by decide : (GD : ℤ) ≠ 0)
      simpa [csc, div_eq_mul_inv, GD_cast] using h
    have hf2 : ((I.lo * J.hi : ℤ) : ℝ) / GR ≤ ((csc (I.lo * J.hi) : ℤ) : ℝ) := by
      have h := le_cdiv_div (a := I.lo * J.hi) (b := GD) (by decide : (GD : ℤ) ≠ 0)
      simpa [csc, div_eq_mul_inv, GD_cast] using h
    have hf3 : ((I.hi * J.lo : ℤ) : ℝ) / GR ≤ ((csc (I.hi * J.lo) : ℤ) : ℝ) := by
      have h := le_cdiv_div (a := I.hi * J.lo) (b := GD) (by decide : (GD : ℤ) ≠ 0)
      simpa [csc, div_eq_mul_inv, GD_cast] using h
    have hf4 : ((I.hi * J.hi : ℤ) : ℝ) / GR ≤ ((csc (I.hi * J.hi) : ℤ) : ℝ) := by
      have h := le_cdiv_div (a := I.hi * J.hi) (b := GD) (by decide : (GD : ℤ) ≠ 0)
      simpa [csc, div_eq_mul_inv, GD_cast] using h
    have h1 : x * y ≤
        max (max ((I.lo * J.lo : ℤ) : ℝ) ((I.lo * J.hi : ℤ) : ℝ))
          (max ((I.hi * J.lo : ℤ) : ℝ) ((I.hi * J.hi : ℤ) : ℝ)) / GR / GR := by
      rw [div_div, le_div_iff₀ (mul_pos GR_pos GR_pos)]
      exact hhi'
    have h2 : max (max ((I.lo * J.lo : ℤ) : ℝ) ((I.lo * J.hi : ℤ) : ℝ))
          (max ((I.hi * J.lo : ℤ) : ℝ) ((I.hi * J.hi : ℤ) : ℝ)) / GR / GR ≤
        max (max ((csc (I.lo * J.lo) : ℤ) : ℝ) ((csc (I.lo * J.hi) : ℤ) : ℝ))
          (max ((csc (I.hi * J.lo) : ℤ) : ℝ) ((csc (I.hi * J.hi) : ℤ) : ℝ)) / GR := by
      rw [div_le_div_iff_of_pos_right GR_pos, ← max4_scaleR]
      exact max_le_max (max_le_max hf1 hf2) (max_le_max hf3 hf4)
    refine le_trans h1 ?_
    rw [show ((mul I J).hi : ℝ) / GR =
        max (max ((csc (I.lo * J.lo) : ℤ) : ℝ) ((csc (I.lo * J.hi) : ℤ) : ℝ))
          (max ((csc (I.hi * J.lo) : ℤ) : ℝ) ((csc (I.hi * J.hi) : ℤ) : ℝ)) / GR by
      simp only [mul, Int.cast_max]]
    exact h2

/-! ### Reciprocal soundness -/

theorem GD_sq_cast : ((GD * GD : ℤ) : ℝ) = GR * GR := by
  rw [← GD_cast]
  push_cast
  ring

theorem memR_inv {I : ZInt} {x : ℝ} (hx : I.memR x) (h : 0 < I.lo ∨ I.hi < 0) :
    ∀ J, inv? I = some J → J.memR x⁻¹ := by
  intro J hJ
  unfold inv? at hJ
  rw [if_pos h] at hJ
  obtain rfl := Option.some.inj hJ
  obtain ⟨hx1, hx2⟩ := hx
  have hIle : (I.lo : ℝ) ≤ (I.hi : ℝ) := by
    have h' : (I.lo : ℝ) / GR ≤ (I.hi : ℝ) / GR := le_trans hx1 hx2
    rwa [div_le_div_iff_of_pos_right GR_pos] at h'
  have hIleZ : I.lo ≤ I.hi := by exact_mod_cast hIle
  have hb : ((I.hi : ℝ) / GR)⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ ((I.lo : ℝ) / GR)⁻¹ := by
    rcases h with hp | hn
    · have hp' : (0 : ℝ) < (I.lo : ℝ) / GR := by
        have h0 : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hp
        exact div_pos h0 GR_pos
      exact Kepler.Text.TaylorSecond.QInterval.inv_bounds_of_pos hp' hx1 hx2
    · have h0 : (I.hi : ℝ) < 0 := by exact_mod_cast hn
      have hn' : (I.hi : ℝ) / GR < 0 := div_neg_of_neg_of_pos h0 GR_pos
      exact Kepler.Text.TaylorSecond.QInterval.inv_bounds_of_neg hn' hx1 hx2
  constructor
  · have h1 : (((GD * GD).fdiv I.hi : ℤ) : ℝ) ≤ ((GD * GD : ℤ) : ℝ) / (I.hi : ℝ) := by
      refine fdiv_le_div ?_
      rcases h with hp | hn
      · exact ne_of_gt (lt_of_lt_of_le hp hIleZ)
      · exact ne_of_lt hn
    have h2 : ((GD * GD : ℤ) : ℝ) / (I.hi : ℝ) / GR = ((I.hi : ℝ) / GR)⁻¹ := by
      rw [GD_sq_cast]
      field_simp
    have h3 : (((GD * GD).fdiv I.hi : ℤ) : ℝ) / GR ≤ ((I.hi : ℝ) / GR)⁻¹ := by
      rw [← h2]
      rw [div_le_div_iff_of_pos_right GR_pos]
      exact h1
    exact le_trans h3 hb.1
  · have h1 : ((GD * GD : ℤ) : ℝ) / (I.lo : ℝ) ≤ ((-((-(GD * GD)).fdiv I.lo) : ℤ) : ℝ) := by
      refine le_cdiv_div ?_
      rcases h with hp | hn
      · exact ne_of_gt hp
      · exact ne_of_lt (lt_of_le_of_lt hIleZ hn)
    have h2 : ((GD * GD : ℤ) : ℝ) / (I.lo : ℝ) / GR = ((I.lo : ℝ) / GR)⁻¹ := by
      rw [GD_sq_cast]
      field_simp
    have h3 : ((I.lo : ℝ) / GR)⁻¹ ≤ ((-((-(GD * GD)).fdiv I.lo) : ℤ) : ℝ) / GR := by
      rw [← h2]
      rw [div_le_div_iff_of_pos_right GR_pos]
      exact h1
    exact le_trans hb.2 h3

end ZInt

/-! ### The straight-line program (packed as one `Nat`)

A `List Op` literal costs ~1.3 KB per instruction in the `.olean` (measured),
which would dominate the per-box certificate.  Packing the program into a
single `Nat` (40 bits per instruction, instruction 0 in the low chunk) costs
~2 bytes per byte of the literal and is still kernel-reducible: `Nat` `%` and
`/` on literals are handled natively by the kernel. -/

/-- Instruction chunk width `2^40`. -/
def PW : Nat := 1099511627776

/-- `List` index lookup (this toolchain has no `List.get?`). -/
def lget? : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => lget? l n

/-- Stack-machine instruction: `sl i` pushes input `i`, `dup d` copies the entry
`d` positions deep in the stack, the arithmetic ops pop their operands. -/
inductive Op where
  | sl (i : Nat)
  | dup (d : Nat)
  | add
  | sub
  | mul
  | neg
  | inv

/-- Decode the low instruction chunk. -/
def decode (v : Nat) : Op :=
  match v % 8 with
  | 0 => Op.sl (v / 8)
  | 1 => Op.dup (v / 8)
  | 2 => Op.add
  | 3 => Op.sub
  | 4 => Op.mul
  | 5 => Op.neg
  | _ => Op.inv

/-- Encode one instruction (inverse of `decode` on the used range). -/
def packOp : Op → Nat
  | Op.sl i => 8 * i
  | Op.dup d => 8 * d + 1
  | Op.add => 2
  | Op.sub => 3
  | Op.mul => 4
  | Op.neg => 5
  | Op.inv => 6

/-- One integer step. -/
def step (slots : List ZInt) (v : Nat) (st : List ZInt) : Option (List ZInt) :=
  match decode v with
  | Op.sl i => (lget? slots i).map fun I => I :: st
  | Op.dup d => (lget? st d).map fun I => I :: st
  | Op.add => match st with
    | a :: b :: st' => some (b.add a :: st')
    | _ => none
  | Op.sub => match st with
    | a :: b :: st' => some (b.sub a :: st')
    | _ => none
  | Op.mul => match st with
    | a :: b :: st' => some (b.mul a :: st')
    | _ => none
  | Op.neg => match st with
    | a :: st' => some (a.neg :: st')
    | _ => none
  | Op.inv => match st with
    | a :: st' => (a.inv?).map fun I => I :: st'
    | _ => none

/-- One real step: the same instruction read over `ℝ`. -/
noncomputable def stepR (xs : List ℝ) (v : Nat) (st : List ℝ) : Option (List ℝ) :=
  match decode v with
  | Op.sl i => (lget? xs i).map fun x => x :: st
  | Op.dup d => (lget? st d).map fun x => x :: st
  | Op.add => match st with
    | a :: b :: st' => some ((b + a) :: st')
    | _ => none
  | Op.sub => match st with
    | a :: b :: st' => some ((b - a) :: st')
    | _ => none
  | Op.mul => match st with
    | a :: b :: st' => some ((b * a) :: st')
    | _ => none
  | Op.neg => match st with
    | a :: st' => some ((-a) :: st')
    | _ => none
  | Op.inv => match st with
    | a :: st' => some ((a⁻¹) :: st')
    | _ => none

/-- Integer execution of a packed program of `k` instructions. -/
def runP (slots : List ZInt) : Nat → Nat → List ZInt → Option (List ZInt)
  | 0, _, st => some st
  | k + 1, plan, st =>
      (step slots (plan % PW) st).bind fun st' => runP slots k (plan / PW) st'

/-- Real execution of the same packed program. -/
noncomputable def runPR (xs : List ℝ) : Nat → Nat → List ℝ → Option (List ℝ)
  | 0, _, st => some st
  | k + 1, plan, st =>
      (stepR xs (plan % PW) st).bind fun st' => runPR xs k (plan / PW) st'

/-- `runP` truncated to the top `n` stack entries (keeps per-box statements small). -/
def runPTop (slots : List ZInt) (plan n ops : Nat) : Option (List ZInt) :=
  (runP slots ops plan []).map (fun st => st.take n)

theorem forall₂_lget? : ∀ {α β : Type} {r : α → β → Prop} {l₁ : List α} {l₂ : List β},
    List.Forall₂ r l₁ l₂ → ∀ {n : Nat} {a : α}, lget? l₁ n = some a → ∃ b, lget? l₂ n = some b ∧ r a b
  | _, _, _, _, _, List.Forall₂.nil, n, a, h => by simp [lget?] at h
  | _, _, _, _, _, List.Forall₂.cons hab _, 0, a, h => by
      simp only [lget?] at h
      obtain rfl := Option.some.inj h
      exact ⟨_, rfl, hab⟩
  | _, _, _, _, _, List.Forall₂.cons _ htl, n + 1, a, h => by
      simp only [lget?] at h
      obtain ⟨b, hb, hr⟩ := forall₂_lget? htl h
      exact ⟨b, hb, hr⟩

/-- Single-step refinement. -/
theorem step_sound (slots : List ZInt) (xs : List ℝ) (hxs : List.Forall₂ ZInt.memR slots xs)
    (v : Nat) {stI : List ZInt} {stR : List ℝ} (hst : List.Forall₂ ZInt.memR stI stR)
    {outI : List ZInt} (hrun : step slots v stI = some outI) :
    ∃ outR, stepR xs v stR = some outR ∧ List.Forall₂ ZInt.memR outI outR := by
  cases hv : decode v with
  | sl i =>
      simp only [step, hv, Option.map_eq_some_iff] at hrun
      obtain ⟨I, hI, rfl⟩ := hrun
      obtain ⟨x, hxg, hmem⟩ := forall₂_lget? hxs hI
      exact ⟨_, by simp [stepR, hv, hxg], List.Forall₂.cons hmem hst⟩
  | dup d =>
      simp only [step, hv, Option.map_eq_some_iff] at hrun
      obtain ⟨I, hI, rfl⟩ := hrun
      obtain ⟨x, hxg, hmem⟩ := forall₂_lget? hst hI
      exact ⟨_, by simp [stepR, hv, hxg], List.Forall₂.cons hmem hst⟩
  | add =>
      cases hst with
      | nil => simp [step, hv] at hrun
      | cons ha hst1 =>
          cases hst1 with
          | nil => simp [step, hv] at hrun
          | cons hb hst2 =>
              simp only [step, hv] at hrun
              obtain rfl := Option.some.inj hrun
              exact ⟨_, by simp only [stepR, hv], List.Forall₂.cons (ZInt.memR_add hb ha) hst2⟩
  | sub =>
      cases hst with
      | nil => simp [step, hv] at hrun
      | cons ha hst1 =>
          cases hst1 with
          | nil => simp [step, hv] at hrun
          | cons hb hst2 =>
              simp only [step, hv] at hrun
              obtain rfl := Option.some.inj hrun
              exact ⟨_, by simp only [stepR, hv], List.Forall₂.cons (ZInt.memR_sub hb ha) hst2⟩
  | mul =>
      cases hst with
      | nil => simp [step, hv] at hrun
      | cons ha hst1 =>
          cases hst1 with
          | nil => simp [step, hv] at hrun
          | cons hb hst2 =>
              simp only [step, hv] at hrun
              obtain rfl := Option.some.inj hrun
              exact ⟨_, by simp only [stepR, hv], List.Forall₂.cons (ZInt.memR_mul hb ha) hst2⟩
  | neg =>
      cases hst with
      | nil => simp [step, hv] at hrun
      | cons ha hst1 =>
          simp only [step, hv] at hrun
          obtain rfl := Option.some.inj hrun
          exact ⟨_, by simp only [stepR, hv], List.Forall₂.cons (ZInt.memR_neg ha) hst1⟩
  | inv =>
      match stI, stR, hst with
      | a :: stI', x :: stR', hst =>
          cases hst with
          | cons ha hst1 =>
              cases hi : ZInt.inv? a with
              | none => simp [step, hv, hi] at hrun
              | some J =>
                  simp only [step, hv, hi, Option.map_eq_some_iff] at hrun
                  obtain ⟨I, hI, hout⟩ := hrun
                  subst hout
                  have hJI : J = I := Option.some.inj hI
                  subst hJI
                  have hs : 0 < a.lo ∨ a.hi < 0 := by
                    by_contra hcon
                    rw [show ZInt.inv? a = none from by unfold ZInt.inv?; rw [if_neg hcon]] at hi
                    simp at hi
                  exact ⟨_, by simp only [stepR, hv], List.Forall₂.cons (ZInt.memR_inv ha hs J hi) hst1⟩
      | [], _, _ => simp [step, hv] at hrun
      | _ :: _, [], hst => cases hst

/-- **Reflective soundness.**  If every input interval of the integer program
contains the corresponding real input, then every output does too. -/
theorem run_sound (slots : List ZInt) (xs : List ℝ) (hxs : List.Forall₂ ZInt.memR slots xs) :
    ∀ (k plan : Nat) (stI : List ZInt) (stR : List ℝ), List.Forall₂ ZInt.memR stI stR →
      ∀ outI, runP slots k plan stI = some outI →
        ∃ outR, runPR xs k plan stR = some outR ∧ List.Forall₂ ZInt.memR outI outR
  | 0, plan, stI, stR, hst, outI, hrun => by
      simp only [runP, Option.some.injEq] at hrun
      subst hrun
      exact ⟨stR, rfl, hst⟩
  | k + 1, plan, stI, stR, hst, outI, hrun => by
      simp only [runP] at hrun
      cases hs : step slots (plan % PW) stI with
      | none => simp [hs] at hrun
      | some mid =>
          simp only [hs, Option.bind_some] at hrun
          obtain ⟨midR, hmidR, hmid⟩ := step_sound slots xs hxs (plan % PW) hst hs
          simp only [runPR, hmidR, Option.bind_some]
          exact run_sound slots xs hxs k (plan / PW) mid midR hmid outI hrun

theorem forall₂_take : ∀ {l₁ : List ZInt} {l₂ : List ℝ}, List.Forall₂ ZInt.memR l₁ l₂ →
    ∀ n, List.Forall₂ ZInt.memR (l₁.take n) (l₂.take n)
  | _, _, h, 0 => by simp
  | _, _, h, n + 1 => by
      cases h with
      | nil => simp
      | cons hab htl => simp [forall₂_take htl n, hab]

/-- `runPTop` gives a full run plus a `take` equation. -/
theorem runPTop_spec {slots : List ZInt} {plan n ops : Nat} {out : List ZInt}
    (h : runPTop slots plan n ops = some out) :
    ∃ full, runP slots ops plan [] = some full ∧ full.take n = out := by
  unfold runPTop at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨full, hfull, htake⟩ := h
  exact ⟨full, hfull, htake⟩

end Wt1Check
