/-
Kepler.Text.ZTGDihKit — lane `ztgmain-w1`: the generic `dihY` lower-bound
kit for the ZTGIJCF4 residual (part 1; verified and frozen).

`dihXf x1 … x6 = π/2 + atn2 (√(4·x1·deltaX)) (−deltaX4)` with `A = √(4x1Δ)`,
and the exact pointwise identity `cot(dihXf) = deltaX4 / A` (all `atn2`
branches) give, for every `s > 0`:

  s·|deltaX4| ≤ A   ⟹   dihY ≥ arctan s        (`ztg_dihY_ge_arctan`),

i.e. an *angle* lower bound is one *polynomial* inequality in the squared
lengths — no trigonometric constants enter the box argument.

Numeric anchors: rational lower bounds for `arctan(8/5) ≥ 1.008` and
`arctan(6/5) ≥ 0.875` via the addition-formula split at 1 and the verified
alternating Taylor bracket `g4v_atan_pos_bounds` (order 32,
`Kepler.Text.Gamma4ValArctan`).

Also carries `ztgG q x1 … x6 = 4·x1·deltaX − q·delta4²` (the per-line
certificate polynomial, marked `irreducible` so per-corner discharges never
trigger the expensive definitional unfolding) — consumed by the per-debt
corner reductions in `Kepler.NliBanksZTGIJCF4Dih` (part 2, WIP).

No `sorry`/`axiom`/`native_decide`; every declaration axiom-audited.
-/
import Kepler.Text.Gamma4ValArctan
import Kepler.NliBanks8

set_option maxHeartbeats 40000000

namespace Kepler.Text

/-! ## 1. The generic `atn2` lower bound -/

private theorem ztg_arctan_inv {s : ℝ} (hs : 0 < s) :
    Real.arctan s - Real.pi / 2 = -(Real.arctan (1 / s)) := by
  have h := Real.arctan_inv_of_pos (x := s) hs
  rw [show (s⁻¹ : ℝ) = 1 / s from by rw [div_eq_mul_inv, one_mul]] at h
  linarith

/-- For `0 < x`, `0 < s` and `s·|y| ≤ x`: `atn2 x y ≥ arctan s − π/2`,
i.e. `π/2 + atn2 x y ≥ arctan s`.  Branch analysis of `atn2`: the `y > 0`
branch is nonnegative, the `y < 0` branch is `arctan(x/(−y)) − π/2` with
`x/(−y) ≥ s`, and the `|y| < x` branch uses `|y/x| ≤ 1/s` together with
`ztg_arctan_inv`. -/
theorem ztg_atn2_ge {x y s : ℝ} (hx : 0 < x) (hs : 0 < s) (h : s * |y| ≤ x) :
    Real.arctan s - Real.pi / 2 ≤ atn2 x y := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hlt := Real.arctan_lt_pi_div_two s
  have him := ztg_arctan_inv hs
  unfold atn2
  split_ifs with h1 h2 h3
  · -- |y| < x
    have habs1 : |y / x| ≤ 1 / s := by
      rw [abs_div, abs_of_pos hx]
      field_simp
      rw [mul_comm]
      exact h
    have hge : -(1 / s) ≤ y / x := (abs_le.mp habs1).1
    have key : Real.arctan (-(1 / s)) ≤ Real.arctan (y / x) :=
      Real.arctan_le_arctan_iff.mpr hge
    rw [Real.arctan_neg] at key
    rw [him]
    linarith
  · -- 0 < y : atn2 = π/2 − arctan (x/y) ≥ 0
    have h2' := Real.arctan_lt_pi_div_two (x / y)
    linarith
  · -- y < 0 : atn2 = −π/2 − arctan (x/y), x/y ≤ 0
    have hyn : y < 0 := h3
    have habsy : |y| = -y := abs_of_neg hyn
    have hxyn : (0:ℝ) < -y := by linarith
    have hge' : s ≤ x / (-y) := (le_div_iff₀ hxyn).mpr (by rw [← habsy]; linarith)
    have hmono := Real.arctan_le_arctan_iff.mpr hge'
    have hxy : x / y = -(x / (-y)) := by field_simp
    rw [hxy, Real.arctan_neg]
    linarith
  · -- y = 0 (and ¬(|y| < x)): contradicts 0 < x
    have hy0 : y = 0 := le_antisymm (by linarith) (by linarith)
    subst hy0
    rw [abs_zero] at h1
    linarith [hx]

/-- The `dihXf` form: `s·|deltaX4| ≤ √(4x1Δ)` (with `deltaX > 0`) implies
`dihXf ≥ arctan s`. -/
theorem ztg_dihXf_ge_arctan {x1 x2 x3 x4 x5 x6 s : ℝ} (hs : 0 < s)
    (hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
    (h : s * |deltaX4 x1 x2 x3 x4 x5 x6|
        ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) :
    Real.arctan s ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  have hh : s * |(-deltaX4 x1 x2 x3 x4 x5 x6)|
      ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    rw [abs_neg]; exact h
  have key := ztg_atn2_ge hA hs hh
  unfold dihXf
  linarith

/-- The `dihY` form (`x_i = y_i²` is definitional). -/
theorem ztg_dihY_ge_arctan {y1 y2 y3 y4 y5 y6 s : ℝ} (hs : 0 < s)
    (hA : 0 < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6))
    (h : s * |deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)|
        ≤ Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6)) :
    Real.arctan s ≤ dihY y1 y2 y3 y4 y5 y6 :=
  ztg_dihXf_ge_arctan hs hA h

/-! ## 2. Rational arctan lower bounds -/

/-- `arctan(3/13) ≥ 0.226` (alternating Taylor bracket, order 32). -/
theorem ztg_arctan_3_13_lb : (0.226 : ℝ) ≤ Real.arctan (3 / 13) :=
  (g4v_atan_pos_bounds (x := (3 / 13 : ℝ)) (lo := 0.226) (hi := 0.2272)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

/-- `arctan(8/5) ≥ 1.008`: split at 1 —
`arctan(8/5) = π/4 + arctan(3/13)` — and the Taylor bracket above. -/
theorem ztg_arctan_8_5_lb : (1.008 : ℝ) ≤ Real.arctan (8 / 5) := by
  have hadd : Real.arctan 1 + Real.arctan (3 / 13) = Real.arctan (8 / 5) := by
    have h : (1:ℝ) * (3 / 13) < 1 := by norm_num
    rw [Real.arctan_add h]
    norm_num
  have h1 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
  have hpi := g4v_pi_bounds_d8
  have h2 := ztg_arctan_3_13_lb
  rw [h1] at hadd
  linarith

/-- `arctan(1/11) ≥ 0.0906` (alternating Taylor bracket, order 32). -/
theorem ztg_arctan_1_11_lb : (0.0906 : ℝ) ≤ Real.arctan (1 / 11) :=
  (g4v_atan_pos_bounds (x := (1 / 11 : ℝ)) (lo := 0.0906) (hi := 0.0908)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

/-- `arctan(6/5) ≥ 0.875`: split at 1 —
`arctan(6/5) = π/4 + arctan(1/11)` — and the Taylor bracket above. -/
theorem ztg_arctan_6_5_lb : (0.875 : ℝ) ≤ Real.arctan (6 / 5) := by
  have hadd : Real.arctan 1 + Real.arctan (1 / 11) = Real.arctan (6 / 5) := by
    have h : (1:ℝ) * (1 / 11) < 1 := by norm_num
    rw [Real.arctan_add h]
    norm_num
  have h1 : Real.arctan 1 = Real.pi / 4 := Real.arctan_one
  have hpi := g4v_pi_bounds_d8
  have h2 := ztg_arctan_1_11_lb
  rw [h1] at hadd
  linarith

/-! ## 3. The per-line certificate polynomial -/

/-- `ztgG q x1 … x6 = 4·x1·deltaX − q·delta4²`.  Marked irreducible so that
per-corner discharges never trigger the (expensive) definitional unfolding
inside `exact`'s defeq checks. -/
noncomputable def ztgG (q x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  4 * x1 * deltaX x1 x2 x3 x4 x5 x6 - q * deltaX4 x1 x2 x3 x4 x5 x6 ^ 2

attribute [irreducible] ztgG

/-! ## Axiom audit (house style) -/

#print axioms ztg_arctan_inv
#print axioms ztg_atn2_ge
#print axioms ztg_dihXf_ge_arctan
#print axioms ztg_dihY_ge_arctan
#print axioms ztg_arctan_3_13_lb
#print axioms ztg_arctan_8_5_lb
#print axioms ztg_arctan_1_11_lb
#print axioms ztg_arctan_6_5_lb
#print axioms ztgG

end Kepler.Text
