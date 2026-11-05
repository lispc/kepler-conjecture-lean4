/-
Kepler.Text.Gamma4Deriv2 — part 2 of the `dihXf` derivative kit (lane
`gamma4-w2`): the `x2`–`x6` partial derivatives and the sign verdicts for
the partials on the x-box `[4, 4.004001]⁶` (the square of the RIBCYXU sharp
y-box `[2,2.001]⁶`).

Derivative values (with `A = √(4·x₁·Δ)`, `Δᵢ = ∂Δ/∂xᵢ`,
`u₁₂₆ = upsX x1 x2 x6`, `u₁₃₅ = upsX x1 x3 x5`):
    x2: −2·x₁·Δ₃ / (A·u₁₂₆)
    x3: −2·x₁·Δ₂ / (A·u₁₃₅)
    x4: 2·x₁/A = √x₁/√Δ
    x5: −2·x₁·Δ₆ / (A·u₁₃₅)
    x6: −2·x₁·Δ₅ / (A·u₁₂₆)
The `x2`/`x3` and `x5`/`x6` pairings cross over (the same twist as HOL
`OCBICBY.derived_form_dih_x_wrt_x5` using `delta_x6`); they are consequences
of the rationalisation identities in `Gamma4Deriv`.

Sign verdicts on `[4,4.004001]⁶` (numerically `dihXf` partials are
`(+,-,-,+,-,-)`; the x1 case is left as GAP, see `DELIVERY.md`):
`x2 < 0`, `x3 < 0`, `x4 > 0`, `x5 < 0`, `x6 < 0`.
-/
import Kepler.Text.Gamma4Deriv

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## The `x2`–`x6` partial derivatives -/

/-- `∂dihXf/∂x2 = −2·x₁·Δ₃/(A·u₁₂₆)` (the slot pairing is the same twist as
HOL's `derived_form_dih_x_wrt_x5` using `delta_x6`). -/
theorem dihXf_hasDerivAt_x2 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => dihXf x1 t x3 x4 x5 x6)
      (-2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) x2 := by
  have h := g4d_hasDerivAt_dihXf_aux (x1 := x1) (t := x2)
    (f := fun t => deltaX x1 t x3 x4 x5 x6)
    (g := fun t => deltaX4 x1 t x3 x4 x5 x6)
    (f' := g4dDX2 x1 x2 x3 x4 x5 x6) (g' := x1 - x3 + x5) hx1
    (g4d_hasDerivAt_deltaX_x2 x1 x2 x3 x4 x5 x6)
    (g4d_hasDerivAt_deltaX4_x2 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 t x3 x4 x5 x6)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX2 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (x1 - x3 + x5))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x2 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hEpos : 0 < upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [mul_comm, ← hE]; positivity
  have hu126 : upsX x1 x2 x6 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).1
  have hu135 : upsX x1 x3 x5 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).2
  have hE' : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g4d_ups_delta, mul_comm]
  have hI := g4d_delta_ident_x2 x1 x2 x3 x4 x5 x6
  rw [hE']
  field_simp [hA0, hu126, hu135]
  nlinarith [hI]

/-- `∂dihXf/∂x3 = −2·x₁·Δ₂/(A·u₁₃₅)`. -/
theorem dihXf_hasDerivAt_x3 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => dihXf x1 x2 t x4 x5 x6)
      (-2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) x3 := by
  have h := g4d_hasDerivAt_dihXf_aux (x1 := x1) (t := x3)
    (f := fun t => deltaX x1 x2 t x4 x5 x6)
    (g := fun t => deltaX4 x1 x2 t x4 x5 x6)
    (f' := g4dDX3 x1 x2 x3 x4 x5 x6) (g' := x1 - x2 + x6) hx1
    (g4d_hasDerivAt_deltaX_x3 x1 x2 x3 x4 x5 x6)
    (g4d_hasDerivAt_deltaX4_x3 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 x2 t x4 x5 x6)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX3 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (x1 - x2 + x6))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x3 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hEpos : 0 < upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [mul_comm, ← hE]; positivity
  have hu126 : upsX x1 x2 x6 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).1
  have hu135 : upsX x1 x3 x5 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).2
  have hE' : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g4d_ups_delta, mul_comm]
  have hI := g4d_delta_ident_x3 x1 x2 x3 x4 x5 x6
  rw [hE']
  field_simp [hA0, hu126, hu135]
  nlinarith [hI]

/-- `∂dihXf/∂x4 = 2·x₁/A` (`A = √(4·x₁·Δ)`). -/
theorem dihXf_hasDerivAt_x4 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => dihXf x1 x2 x3 t x5 x6)
      (2 * x1 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) x4 := by
  have h := g4d_hasDerivAt_dihXf_aux (x1 := x1) (t := x4)
    (f := fun t => deltaX x1 x2 x3 t x5 x6)
    (g := fun t => deltaX4 x1 x2 x3 t x5 x6)
    (f' := deltaX4 x1 x2 x3 x4 x5 x6) (g' := -2 * x1) hx1
    (g4d_hasDerivAt_deltaX_x4 x1 x2 x3 x4 x5 x6)
    (g4d_hasDerivAt_deltaX4_x4 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 x2 x3 t x5 x6)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * deltaX4 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x4 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hEpos : 0 < upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [mul_comm, ← hE]; positivity
  have hu126 : upsX x1 x2 x6 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).1
  have hu135 : upsX x1 x3 x5 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).2
  have hE' : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g4d_ups_delta, mul_comm]
  rw [hE']
  field_simp [hA0, hu126, hu135]
  linear_combination hE' 

/-- `∂dihXf/∂x5 = −2·x₁·Δ₆/(A·u₁₃₅)` (HOL `derived_form_dih_x_wrt_x5`). -/
theorem dihXf_hasDerivAt_x5 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => dihXf x1 x2 x3 x4 t x6)
      (-2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) x5 := by
  have h := g4d_hasDerivAt_dihXf_aux (x1 := x1) (t := x5)
    (f := fun t => deltaX x1 x2 x3 x4 t x6)
    (g := fun t => deltaX4 x1 x2 x3 x4 t x6)
    (f' := deltaX5 x1 x2 x3 x4 x5 x6) (g' := x1 + x2 - x6) hx1
    (g4d_hasDerivAt_deltaX_x5 x1 x2 x3 x4 x5 x6)
    (g4d_hasDerivAt_deltaX4_x5 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 x2 x3 x4 t x6)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * deltaX5 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (x1 + x2 - x6))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x5 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hEpos : 0 < upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [mul_comm, ← hE]; positivity
  have hu126 : upsX x1 x2 x6 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).1
  have hu135 : upsX x1 x3 x5 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).2
  have hE' : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g4d_ups_delta, mul_comm]
  have hI := g4d_delta_ident_x5 x1 x2 x3 x4 x5 x6
  rw [hE']
  field_simp [hA0, hu126, hu135]
  nlinarith [hI]

/-- `∂dihXf/∂x6 = −2·x₁·Δ₅/(A·u₁₂₆)` (HOL `derived_form_dih_x_wrt_x6`). -/
theorem dihXf_hasDerivAt_x6 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => dihXf x1 x2 x3 x4 x5 t)
      (-2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) x6 := by
  have h := g4d_hasDerivAt_dihXf_aux (x1 := x1) (t := x6)
    (f := fun t => deltaX x1 x2 x3 x4 x5 t)
    (g := fun t => deltaX4 x1 x2 x3 x4 x5 t)
    (f' := g4dDX6 x1 x2 x3 x4 x5 x6) (g' := x1 + x3 - x5) hx1
    (g4d_hasDerivAt_deltaX_x6 x1 x2 x3 x4 x5 x6)
    (g4d_hasDerivAt_deltaX4_x6 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 x2 x3 x4 x5 t)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX6 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (x1 + x3 - x5))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x6 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hEpos : 0 < upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [mul_comm, ← hE]; positivity
  have hu126 : upsX x1 x2 x6 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).1
  have hu135 : upsX x1 x3 x5 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hEpos)).2
  have hE' : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g4d_ups_delta, mul_comm]
  have hI := g4d_delta_ident_x6 x1 x2 x3 x4 x5 x6
  rw [hE']
  field_simp [hA0, hu126, hu135]
  nlinarith [hI]

/-! ## Sign verdicts of the `dihXf` partials on the RIBCYXU x-box

The sharp bank box is `[2,2.001]⁶` in the `y` (edge-length) coordinates,
i.e. `[4, 4.004001]⁶` in the squared-length `x` coordinates.  On that box
the `dihXf` partials have constant signs `(+,-,-,+,-,-)`: five are proved
here; the `x1` slot is numerically positive (`min ≈ 0.0588`) but its
degree-five numerator is left to the next wave (see `DELIVERY.md`). -/

/-- The squared-length box `[4, 4.004001]⁶` (square of `[2,2.001]⁶`). -/
def g4dInBox (x1 x2 x3 x4 x5 x6 : ℝ) : Prop :=
  4 ≤ x1 ∧ x1 ≤ 4.004001 ∧ 4 ≤ x2 ∧ x2 ≤ 4.004001 ∧
    4 ≤ x3 ∧ x3 ≤ 4.004001 ∧ 4 ≤ x4 ∧ x4 ≤ 4.004001 ∧
      4 ≤ x5 ∧ x5 ≤ 4.004001 ∧ 4 ≤ x6 ∧ x6 ≤ 4.004001

theorem g4d_dihXf_x2_neg {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4dInBox x1 x2 x3 x4 x5 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    -2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) < 0 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hDX : 0 < g4dDX3 x1 x2 x3 x4 x5 x6 := by
    unfold g4dDX3
    nlinarith [sq_nonneg (x3 - 4), sq_nonneg (x6 - 4), sq_nonneg (x1 - 4),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h6),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h5),
      mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr h6)]
  have hu : 0 < upsX x1 x2 x6 := by
    unfold upsX
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x6), sq_nonneg (x2 - x6)]
  have hx1 : 0 < x1 := by linarith
  have hden : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6 :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) hu
  have hnum : 0 < 2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos two_pos hx1) hDX
  have h : 0 < 2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) :=
    div_pos hnum hden
  have hneg : -(2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) < 0 :=
    neg_lt_zero.mpr h
  convert hneg using 1
  ring

theorem g4d_dihXf_x3_neg {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4dInBox x1 x2 x3 x4 x5 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    -2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) < 0 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hDX : 0 < g4dDX2 x1 x2 x3 x4 x5 x6 := by
    unfold g4dDX2
    nlinarith [sq_nonneg (x1 - 4), sq_nonneg (x2 - 4), sq_nonneg (x3 - 4),
      sq_nonneg (x4 - 4), sq_nonneg (x5 - 4), sq_nonneg (x6 - 4),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h5),
      mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h4),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h5),
      mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr h5),
      mul_nonneg (sub_nonneg.mpr h5) (sub_nonneg.mpr h6)]
  have hu : 0 < upsX x1 x3 x5 := by
    unfold upsX
    nlinarith [sq_nonneg (x1 - x3), sq_nonneg (x1 - x5), sq_nonneg (x3 - x5)]
  have hx1 : 0 < x1 := by linarith
  have hden : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5 :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) hu
  have hnum : 0 < 2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos two_pos hx1) hDX
  have h : 0 < 2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) :=
    div_pos hnum hden
  have hneg : -(2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) < 0 :=
    neg_lt_zero.mpr h
  convert hneg using 1
  ring

theorem g4d_dihXf_x4_pos {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4dInBox x1 x2 x3 x4 x5 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    0 < 2 * x1 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hx1 : 0 < x1 := by linarith
  exact div_pos (mul_pos two_pos hx1) (Real.sqrt_pos.mpr (by positivity))

theorem g4d_dihXf_x5_neg {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4dInBox x1 x2 x3 x4 x5 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    -2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) < 0 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hDX : 0 < g4dDX6 x1 x2 x3 x4 x5 x6 := by
    unfold g4dDX6
    nlinarith [sq_nonneg (x1 - 4), sq_nonneg (x2 - 4), sq_nonneg (x3 - 4),
      sq_nonneg (x4 - 4), sq_nonneg (x5 - 4), sq_nonneg (x6 - 4),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h5),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h6),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h3),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3),
      mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr h5)]
  have hu : 0 < upsX x1 x3 x5 := by
    unfold upsX
    nlinarith [sq_nonneg (x1 - x3), sq_nonneg (x1 - x5), sq_nonneg (x3 - x5)]
  have hx1 : 0 < x1 := by linarith
  have hden : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5 :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) hu
  have hnum : 0 < 2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos two_pos hx1) hDX
  have h : 0 < 2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) :=
    div_pos hnum hden
  have hneg : -(2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) < 0 :=
    neg_lt_zero.mpr h
  convert hneg using 1
  ring

theorem g4d_dihXf_x6_neg {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4dInBox x1 x2 x3 x4 x5 x6)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    -2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) < 0 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hDX : 0 < deltaX5 x1 x2 x3 x4 x5 x6 := by
    unfold deltaX5
    nlinarith [sq_nonneg (x1 - 4), sq_nonneg (x2 - 4), sq_nonneg (x3 - 4),
      sq_nonneg (x4 - 4), sq_nonneg (x5 - 4), sq_nonneg (x6 - 4),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h5),
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h3),
      mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h6),
      mul_nonneg (sub_nonneg.mpr h4) (sub_nonneg.mpr h6),
      mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h4)]
  have hu : 0 < upsX x1 x2 x6 := by
    unfold upsX
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x6), sq_nonneg (x2 - x6)]
  have hx1 : 0 < x1 := by linarith
  have hden : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6 :=
    mul_pos (Real.sqrt_pos.mpr (by positivity)) hu
  have hnum : 0 < 2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 :=
    mul_pos (mul_pos two_pos hx1) hDX
  have h : 0 < 2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) :=
    div_pos hnum hden
  have hneg : -(2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) < 0 :=
    neg_lt_zero.mpr h
  convert hneg using 1
  ring

/-! ## Axiom audit -/

#print axioms g4d_ups_delta
#print axioms dihXf_hasDerivAt_x1
#print axioms dihXf_hasDerivAt_x2
#print axioms dihXf_hasDerivAt_x3
#print axioms dihXf_hasDerivAt_x4
#print axioms dihXf_hasDerivAt_x5
#print axioms dihXf_hasDerivAt_x6
#print axioms g4d_dihXf_x2_neg
#print axioms g4d_dihXf_x3_neg
#print axioms g4d_dihXf_x4_pos
#print axioms g4d_dihXf_x5_neg
#print axioms g4d_dihXf_x6_neg

end Kepler.Text
