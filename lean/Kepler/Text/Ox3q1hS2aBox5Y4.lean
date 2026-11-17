/-
Ox3q1hS2aBox5Y4: S2a envelope pilot, box 5 (idx 41/46), y4 direction.
Template pieces: the second partials of `dihXf` w.r.t. `x1`, `x4`, `x5`, `x6`.

Key structural fact: the first partials carry NO atan (the atan derivative
collapsed at first order), hence the second partials are elementary
sqrt/affine/quadratic compositions, proved by a HasDerivAt chain whose values
are kept in the chain-native (un-normalised) form so that the final step is a
plain `exact` (no congr/ring endgame).

No numeric data; no `sorry`/`axiom`/`native_decide`.
-/
import Mathlib
import Kepler.Text.Gamma4Deriv4

open Set Filter Topology

namespace Kepler.Text

/-- Derivative of a quadratic in the `a*(q*q) + (b*q + c)` normal form
(local copy of the Gamma4Deriv private helper, which is not exported). -/
theorem hasDerivAt_quad_s2a (a b c x : ℝ) :
    HasDerivAt (fun q : ℝ => a * (q * q) + (b * q + c)) (a * (x + x) + b) x := by
  have h1 : HasDerivAt (fun q : ℝ => q * q) (x + x) x := by
    exact HasDerivAt.congr_deriv
      ((hasDerivAt_id x).mul (hasDerivAt_id x)) (by norm_num)
  have h2 : HasDerivAt (fun q : ℝ => b * q + c) (b * 1 + 0) x :=
    ((hasDerivAt_id x).const_mul b).add (hasDerivAt_const (x := x) (c := c))
  exact HasDerivAt.congr_deriv ((h1.const_mul a).add h2) (by norm_num)

/-- Second partial of `dihXf` w.r.t. `x4`: the first partial
`g4dDihX4 = 2*x1/sqrt(4*x1*deltaX)` (whose x4-dependence sits entirely in
the affine-in-x4 `deltaX`) is itself differentiable in `x4`, with value
`-4*x1^2*deltaX4 / (sqrt(4*x1*deltaX) * (4*x1*deltaX))`
(`= -4*x1^2*deltaX4 / (4*x1*deltaX)^(3/2)`). -/
theorem dihXf_second_deriv_x4 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX4 x1 x2 x3 t x5 x6)
      (-(4 * x1 * x1 * deltaX4 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x4 := by
  have hupos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hsqrtne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hupos)
  have hΔ : HasDerivAt (fun t => deltaX x1 x2 x3 t x5 x6)
      (deltaX4 x1 x2 x3 x4 x5 x6) x4 :=
    g4d_hasDerivAt_deltaX_x4 x1 x2 x3 x4 x5 x6
  have hu' : HasDerivAt (fun t => (4 * x1 * deltaX x1 x2 x3 t x5 x6 : ℝ))
      (4 * x1 * deltaX4 x1 x2 x3 x4 x5 x6) x4 := hΔ.const_mul (4 * x1)
  have hu : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 x3 t x5 x6))
      ((4 * x1 * deltaX4 x1 x2 x3 x4 x5 x6)
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x4 :=
    hu'.sqrt (by positivity)
  have hinv : HasDerivAt
      (fun t => (Real.sqrt (4 * x1 * deltaX x1 x2 x3 t x5 x6))⁻¹)
      (-(4 * x1 * deltaX4 x1 x2 x3 x4 x5 x6
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ^ 2) x4 := hu.inv hsqrtne
  have h2 := hinv.const_mul (2 * x1)
  have hsqrt2 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2
      = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by
    rw [pow_two]
    exact Real.mul_self_sqrt (le_of_lt hupos)
  have hv4 : 2 * x1 * (-(4 * x1 * deltaX4 x1 x2 x3 x4 x5 x6
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) ^ 2)
      = -(4 * x1 * x1 * deltaX4 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) := by
    rw [hsqrt2]; ring
  unfold g4dDihX4
  exact h2.congr_deriv hv4

/-- Second partial of `dihXf` w.r.t. `x5`: the first partial
`g4dDihX5 = -2*x1*g4dDX6/(sqrt(4*x1*deltaX) * upsX x1 x3 x5)` is
differentiable in `x5` (numerator affine in x5 with slope `x2+x3-x4`,
`deltaX` affine in x5 with slope `deltaX5`, `upsX x1 x3 x5` quadratic in x5
with slope `2*x1+2*x3-2*x5`), value = the quotient-rule form over
`(sqrt(4*x1*deltaX) * upsX x1 x3 x5)^2` in chain-native shape. -/
theorem dihXf_second_deriv_x5 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX5 x1 x2 x3 x4 t x6)
      (-2 * x1 * (((x2 + x3 - x4)
            * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
          - g4dDX6 x1 x2 x3 x4 x5 x6
            * ((4 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
                  / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
                * upsX x1 x3 x5
              + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
                * (2 * x1 + 2 * x3 - 2 * x5)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2))) x5 := by
  have hupos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hsqrtne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hupos)
  have hprodp : 0 < deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  rw [g4d_ups_delta] at hprodp
  have hup5nz : upsX x1 x3 x5 ≠ 0 := by
    intro hc; rw [hc] at hprodp; simp at hprodp
  have hΔ5 : HasDerivAt (fun t => deltaX x1 x2 x3 x4 t x6)
      (deltaX5 x1 x2 x3 x4 x5 x6) x5 :=
    g4d_hasDerivAt_deltaX_x5 x1 x2 x3 x4 x5 x6
  have hsq : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6))
      (4 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x5 :=
    (hΔ5.const_mul (4 * x1)).sqrt (by positivity)
  have hupsq : HasDerivAt (fun t => (-1) * (t * t)
      + ((2 * x1 + 2 * x3) * t + (2 * x1 * x3 - x1 * x1 - x3 * x3)))
      ((-1) * (x5 + x5) + (2 * x1 + 2 * x3)) x5 :=
    hasDerivAt_quad_s2a (-1) (2 * x1 + 2 * x3) (2 * x1 * x3 - x1 * x1 - x3 * x3) x5
  have hvu : (-1) * (x5 + x5) + (2 * x1 + 2 * x3) = 2 * x1 + 2 * x3 - 2 * x5 := by ring
  have hup : HasDerivAt (fun t => upsX x1 x3 t) (2 * x1 + 2 * x3 - 2 * x5) x5 := by
    rw [show (fun t => upsX x1 x3 t) = fun t => (-1) * (t * t)
        + ((2 * x1 + 2 * x3) * t + (2 * x1 * x3 - x1 * x1 - x3 * x3)) from by
          funext t; unfold upsX; ring]
    exact hupsq.congr_deriv hvu
  have hD : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6)
        * upsX x1 x3 t)
      (4 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (2 * x1 + 2 * x3 - 2 * x5)) x5 :=
    hsq.mul hup
  have hDne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5 ≠ 0 := by
    intro hc
    rw [mul_eq_zero] at hc
    rcases hc with hc | hc
    · exact hsqrtne hc
    · exact hup5nz hc
  have hdg : HasDerivAt (fun t => g4dDX6 x1 x2 x3 x4 t x6) (x2 + x3 - x4) x5 := by
    have he : (fun t => g4dDX6 x1 x2 x3 x4 t x6)
        = fun t => (x2 + x3 - x4) * t
          + (-x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 - x3 ^ 2 + x3 * x4
            - 2 * x3 * x6) := by
      funext t; unfold g4dDX6; ring
    rw [he]
    have hv : (x2 + x3 - x4) * 1 = x2 + x3 - x4 := by ring
    exact HasDerivAt.congr_deriv
      (HasDerivAt.add_const (-x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 - x3 ^ 2
        + x3 * x4 - 2 * x3 * x6)
        (HasDerivAt.const_mul (x2 + x3 - x4) (hasDerivAt_id x5))) hv
  have hdiv : HasDerivAt (fun t => g4dDX6 x1 x2 x3 x4 t x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6) * upsX x1 x3 t))
      (((x2 + x3 - x4) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x3 x5)
        - g4dDX6 x1 x2 x3 x4 x5 x6
          * ((4 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
                / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
              * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * x1 + 2 * x3 - 2 * x5)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2)) x5 :=
    hdg.div hD hDne
  have h2 := hdiv.const_mul (-2 * x1)
  rw [show (fun t => g4dDihX5 x1 x2 x3 x4 t x6)
      = fun t => -2 * x1 * (g4dDX6 x1 x2 x3 x4 t x6
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6) * upsX x1 x3 t)) from by
        funext t; unfold g4dDihX5; ring]
  exact h2

/-- Second partial of `dihXf` w.r.t. `x6`: the first partial
`g4dDihX6 = -2*x1*deltaX5/(sqrt(4*x1*deltaX) * upsX x1 x2 x6)` is
differentiable in `x6` (numerator affine in x6 with slope `x2+x3-x4`,
`deltaX` affine in x6 with slope `g4dDX6`, `upsX x1 x2 x6` quadratic in x6
with slope `2*x1+2*x2-2*x6`), value = the quotient-rule form over
`(sqrt(4*x1*deltaX) * upsX x1 x2 x6)^2` in chain-native shape. -/
theorem dihXf_second_deriv_x6 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX6 x1 x2 x3 x4 x5 t)
      (-2 * x1 * (((x2 + x3 - x4)
            * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
          - deltaX5 x1 x2 x3 x4 x5 x6
            * ((4 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
                  / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
                * upsX x1 x2 x6
              + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
                * (2 * x1 + 2 * x2 - 2 * x6)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2))) x6 := by
  have hupos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hsqrtne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hupos)
  have hprodp : 0 < deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  rw [g4d_ups_delta] at hprodp
  have hup6nz : upsX x1 x2 x6 ≠ 0 := by
    intro hc; rw [hc] at hprodp; simp at hprodp
  have hΔ6 : HasDerivAt (fun t => deltaX x1 x2 x3 x4 x5 t)
      (g4dDX6 x1 x2 x3 x4 x5 x6) x6 :=
    g4d_hasDerivAt_deltaX_x6 x1 x2 x3 x4 x5 x6
  have hsq : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t))
      (4 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x6 :=
    (hΔ6.const_mul (4 * x1)).sqrt (by positivity)
  have hupsq : HasDerivAt (fun t => (-1) * (t * t)
      + ((2 * x1 + 2 * x2) * t + (2 * x1 * x2 - x1 * x1 - x2 * x2)))
      ((-1) * (x6 + x6) + (2 * x1 + 2 * x2)) x6 :=
    hasDerivAt_quad_s2a (-1) (2 * x1 + 2 * x2) (2 * x1 * x2 - x1 * x1 - x2 * x2) x6
  have hvu : (-1) * (x6 + x6) + (2 * x1 + 2 * x2) = 2 * x1 + 2 * x2 - 2 * x6 := by ring
  have hup : HasDerivAt (fun t => upsX x1 x2 t) (2 * x1 + 2 * x2 - 2 * x6) x6 := by
    rw [show (fun t => upsX x1 x2 t) = fun t => (-1) * (t * t)
        + ((2 * x1 + 2 * x2) * t + (2 * x1 * x2 - x1 * x1 - x2 * x2)) from by
          funext t; unfold upsX; ring]
    exact hupsq.congr_deriv hvu
  have hD : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t)
        * upsX x1 x2 t)
      (4 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (2 * x1 + 2 * x2 - 2 * x6)) x6 :=
    hsq.mul hup
  have hDne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6 ≠ 0 := by
    intro hc
    rw [mul_eq_zero] at hc
    rcases hc with hc | hc
    · exact hsqrtne hc
    · exact hup6nz hc
  have hd5 : HasDerivAt (fun t => deltaX5 x1 x2 x3 x4 x5 t) (x2 + x3 - x4) x6 := by
    have he : (fun t => deltaX5 x1 x2 x3 x4 x5 t)
        = fun t => (x2 + x3 - x4) * t
          + (x1 * x4 - x1 * x3 + x2 * x1 - x2 ^ 2 + x2 * x3 + x2 * x4
            - x2 * x5 - x2 * x5) := by
      funext t; unfold deltaX5; ring
    rw [he]
    have hv : (x2 + x3 - x4) * 1 = x2 + x3 - x4 := by ring
    exact HasDerivAt.congr_deriv
      (HasDerivAt.add_const (x1 * x4 - x1 * x3 + x2 * x1 - x2 ^ 2 + x2 * x3
        + x2 * x4 - x2 * x5 - x2 * x5)
        (HasDerivAt.const_mul (x2 + x3 - x4) (hasDerivAt_id x6))) hv
  have hdiv : HasDerivAt (fun t => deltaX5 x1 x2 x3 x4 x5 t
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t) * upsX x1 x2 t))
      (((x2 + x3 - x4) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x2 x6)
        - deltaX5 x1 x2 x3 x4 x5 x6
          * ((4 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
                / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
              * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * x1 + 2 * x2 - 2 * x6)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2)) x6 :=
    hd5.div hD hDne
  have h2 := hdiv.const_mul (-2 * x1)
  rw [show (fun t => g4dDihX6 x1 x2 x3 x4 x5 t)
      = fun t => -2 * x1 * (deltaX5 x1 x2 x3 x4 x5 t
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t) * upsX x1 x2 t)) from by
        funext t; unfold g4dDihX6; ring]
  exact h2

/-- Second partial of `dihXf` w.r.t. `x1`: the first partial `g4dDihX1`
(the rationalised big form over `sqrt(4*x1*deltaX) * u126 * u135`) is
differentiable in `x1`: `deltaX` is quadratic in x1 (slope `g4dDX1`),
`deltaX4` is quadratic in x1 with slope `-2*x1+x2+x3-2*x4+x5+x6`, `g4dDX1`
has constant slope `-2*x4`, `sqrt(4*t*deltaX t ...)` differentiates via the
landed first-order chain idiom, and both `upsX` slots are quadratic with
slopes `2*x2+2*x6-2*x1` / `2*x3+2*x5-2*x1`. Value = the quotient-rule form
over `(sqrt(4*x1*deltaX) * (u126 * u135))^2` in chain-native shape. -/
theorem dihXf_second_deriv_x1 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX1 t x2 x3 x4 x5 x6)
      ((((2 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
          + (1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
            + x1 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
              * g4dDX1 x1 x2 x3 x4 x5 x6
              + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4)))
          - ((2 * deltaX x1 x2 x3 x4 x5 x6 + 2 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
              * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
            + 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2))))
        * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (upsX x1 x2 x6 * upsX x1 x3 x5))
      - 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
            + x1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
          - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
            * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
        * ((4 * deltaX x1 x2 x3 x4 x5 x6 + 4 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
            / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
          * (upsX x1 x2 x6 * upsX x1 x3 x5)
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * ((2 * x2 + 2 * x6 - 2 * x1) * upsX x1 x3 x5
            + upsX x1 x2 x6 * (2 * x3 + 2 * x5 - 2 * x1))))
      / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ^ 2))) x1 := by
  have hupos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hsqrtne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hupos)
  have hprodp : 0 < deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  rw [g4d_ups_delta] at hprodp
  have hup126nz : upsX x1 x2 x6 ≠ 0 := by
    intro hc; rw [hc] at hprodp; simp at hprodp
  have hup135nz : upsX x1 x3 x5 ≠ 0 := by
    intro hc; rw [hc] at hprodp; simp at hprodp
  have hDne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
      * (upsX x1 x2 x6 * upsX x1 x3 x5) ≠ 0 := by
    intro hc
    rw [mul_eq_zero] at hc
    rcases hc with hc | hc
    · exact hsqrtne hc
    · rw [mul_eq_zero] at hc
      rcases hc with hc | hc
      · exact hup126nz hc
      · exact hup135nz hc
  have hΔ1 : HasDerivAt (fun t => deltaX t x2 x3 x4 x5 x6)
      (g4dDX1 x1 x2 x3 x4 x5 x6) x1 := by
    rw [show (fun t => deltaX t x2 x3 x4 x5 x6) = fun t => (-x4) * (t * t)
        + ((g4dDX1 x1 x2 x3 x4 x5 x6 + 2 * x1 * x4) * t
          + (x2 * x5 * (-x2 + x3 + x4 - x5 + x6)
            + x3 * x6 * (x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4
            - x4 * x5 * x6)) from by
          funext t; unfold deltaX g4dDX1; ring]
    have hv1 : (-x4) * (x1 + x1)
        + (g4dDX1 x1 x2 x3 x4 x5 x6 + 2 * x1 * x4)
        = g4dDX1 x1 x2 x3 x4 x5 x6 := by ring
    exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a (-x4)
      (g4dDX1 x1 x2 x3 x4 x5 x6 + 2 * x1 * x4)
      (x2 * x5 * (-x2 + x3 + x4 - x5 + x6)
        + x3 * x6 * (x2 - x3 + x4 + x5 - x6) - x2 * x3 * x4
        - x4 * x5 * x6) x1) hv1
  have hΔ4 : HasDerivAt (fun t => deltaX4 t x2 x3 x4 x5 x6)
      (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) x1 := by
    rw [show (fun t => deltaX4 t x2 x3 x4 x5 x6) = fun t => (-1) * (t * t)
        + ((x2 + x3 - 2 * x4 + x5 + x6) * t
          + (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6)) from by
          funext t; unfold deltaX4; ring]
    have hv4 : (-1) * (x1 + x1) + (x2 + x3 - 2 * x4 + x5 + x6)
        = -2 * x1 + x2 + x3 - 2 * x4 + x5 + x6 := by ring
    exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a (-1)
      (x2 + x3 - 2 * x4 + x5 + x6) (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6) x1) hv4
  have hG1 : HasDerivAt (fun t => g4dDX1 t x2 x3 x4 x5 x6) (-2 * x4) x1 := by
    rw [show (fun t => g4dDX1 t x2 x3 x4 x5 x6) = fun t => (-2 * x4) * t
        + (x2 * x4 + x2 * x5 - x2 * x6 + x3 * x4 - x3 * x5 + x3 * x6 - x4 ^ 2
          + x4 * x5 + x4 * x6) from by
          funext t; unfold g4dDX1; ring]
    have hvG : (-2 * x4) * 1 = -2 * x4 := by ring
    exact HasDerivAt.congr_deriv
      (HasDerivAt.add_const (x2 * x4 + x2 * x5 - x2 * x6 + x3 * x4 - x3 * x5
        + x3 * x6 - x4 ^ 2 + x4 * x5 + x4 * x6)
        (HasDerivAt.const_mul (-2 * x4) (hasDerivAt_id x1))) hvG
  have hK : HasDerivAt (fun t => -2 * t + x2 + x3 - 2 * x4 + x5 + x6) (-2) x1 := by
    rw [show (fun t => -2 * t + x2 + x3 - 2 * x4 + x5 + x6)
        = fun t => 0 * (t * t) + ((-2) * t + (x2 + x3 - 2 * x4 + x5 + x6)) from by
          funext t; ring]
    have hvK : 0 * (x1 + x1) + (-2) = -2 := by ring
    exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a 0 (-2)
      (x2 + x3 - 2 * x4 + x5 + x6) x1) hvK
  have hu126 : HasDerivAt (fun t => upsX t x2 x6) (2 * x2 + 2 * x6 - 2 * x1) x1 := by
    rw [show (fun t => upsX t x2 x6) = fun t => (-1) * (t * t)
        + ((2 * x2 + 2 * x6) * t + (2 * x2 * x6 - x2 * x2 - x6 * x6)) from by
          funext t; unfold upsX; ring]
    have hvu : (-1) * (x1 + x1) + (2 * x2 + 2 * x6)
        = 2 * x2 + 2 * x6 - 2 * x1 := by ring
    exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a (-1) (2 * x2 + 2 * x6)
      (2 * x2 * x6 - x2 * x2 - x6 * x6) x1) hvu
  have hu135 : HasDerivAt (fun t => upsX t x3 x5) (2 * x3 + 2 * x5 - 2 * x1) x1 := by
    rw [show (fun t => upsX t x3 x5) = fun t => (-1) * (t * t)
        + ((2 * x3 + 2 * x5) * t + (2 * x3 * x5 - x3 * x3 - x5 * x5)) from by
          funext t; unfold upsX; ring]
    have hvu : (-1) * (x1 + x1) + (2 * x3 + 2 * x5)
        = 2 * x3 + 2 * x5 - 2 * x1 := by ring
    exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a (-1) (2 * x3 + 2 * x5)
      (2 * x3 * x5 - x3 * x3 - x5 * x5) x1) hvu
  have h4t : HasDerivAt (fun t => 4 * t) 4 x1 := by
    simpa using (hasDerivAt_id x1).const_mul 4
  have h4td : HasDerivAt (fun t => 4 * t * deltaX t x2 x3 x4 x5 x6)
      (4 * deltaX x1 x2 x3 x4 x5 x6 + 4 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6) x1 :=
    h4t.mul hΔ1
  have hsq : HasDerivAt (fun t => Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6))
      ((4 * deltaX x1 x2 x3 x4 x5 x6 + 4 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x1 :=
    h4td.sqrt (by positivity)
  have hA : HasDerivAt (fun t => deltaX4 t x2 x3 x4 x5 x6 * deltaX t x2 x3 x4 x5 x6)
      ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
        + deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6) x1 :=
    hΔ4.mul hΔ1
  have hDG : HasDerivAt (fun t => deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6)
      ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * g4dDX1 x1 x2 x3 x4 x5 x6
        + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4)) x1 :=
    hΔ4.mul hG1
  have hB : HasDerivAt (fun t => t * (deltaX4 t x2 x3 x4 x5 x6
          * g4dDX1 t x2 x3 x4 x5 x6))
      (1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
        + x1 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
          * g4dDX1 x1 x2 x3 x4 x5 x6
          + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4))) x1 :=
    (hasDerivAt_id x1).mul hDG
  have hAB : HasDerivAt (fun t => deltaX4 t x2 x3 x4 x5 x6 * deltaX t x2 x3 x4 x5 x6
        + t * (deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6))
      ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
          + deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        + (1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
          + x1 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
            * g4dDX1 x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4)))) x1 :=
    hA.add hB
  have h2t : HasDerivAt (fun t => 2 * t) 2 x1 := by
    simpa using (hasDerivAt_id x1).const_mul 2
  have h2td : HasDerivAt (fun t => 2 * t * deltaX t x2 x3 x4 x5 x6)
      (2 * deltaX x1 x2 x3 x4 x5 x6 + 2 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6) x1 :=
    h2t.mul hΔ1
  have hC : HasDerivAt (fun t => 2 * t * deltaX t x2 x3 x4 x5 x6
        * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6))
      ((2 * deltaX x1 x2 x3 x4 x5 x6 + 2 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
        * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
        + 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2)) x1 :=
    h2td.mul hK
  have hN0 : HasDerivAt (fun t => deltaX4 t x2 x3 x4 x5 x6 * deltaX t x2 x3 x4 x5 x6
        + t * (deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6)
        - 2 * t * deltaX t x2 x3 x4 x5 x6 * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6))
      (((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
          + deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        + (1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
          + x1 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
            * g4dDX1 x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4))))
      - ((2 * deltaX x1 x2 x3 x4 x5 x6 + 2 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
          * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
        + 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2))) x1 :=
    hAB.sub hC
  have hN : HasDerivAt (fun t => 2 * (deltaX4 t x2 x3 x4 x5 x6
          * deltaX t x2 x3 x4 x5 x6
        + t * (deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6)
        - 2 * t * deltaX t x2 x3 x4 x5 x6
          * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6)))
      (2 * (((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
          + deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        + (1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
          + x1 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
            * g4dDX1 x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4))))
      - ((2 * deltaX x1 x2 x3 x4 x5 x6 + 2 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
          * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
        + 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2)))) x1 :=
    hN0.const_mul 2
  have hU126U135 : HasDerivAt (fun t => upsX t x2 x6 * upsX t x3 x5)
      ((2 * x2 + 2 * x6 - 2 * x1) * upsX x1 x3 x5
        + upsX x1 x2 x6 * (2 * x3 + 2 * x5 - 2 * x1)) x1 :=
    hu126.mul hu135
  have hD3 : HasDerivAt (fun t => Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6)
        * (upsX t x2 x6 * upsX t x3 x5))
      ((4 * deltaX x1 x2 x3 x4 x5 x6 + 4 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        * (upsX x1 x2 x6 * upsX x1 x3 x5)
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * ((2 * x2 + 2 * x6 - 2 * x1) * upsX x1 x3 x5
            + upsX x1 x2 x6 * (2 * x3 + 2 * x5 - 2 * x1))) x1 :=
    hsq.mul hU126U135
  have hND : HasDerivAt (fun t => 2 * (deltaX4 t x2 x3 x4 x5 x6
          * deltaX t x2 x3 x4 x5 x6
        + t * (deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6)
        - 2 * t * deltaX t x2 x3 x4 x5 x6
          * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6))
        / (Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6)
          * (upsX t x2 x6 * upsX t x3 x5)))
      ((2 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
          + deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        + (1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
          + x1 * ((-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
            * g4dDX1 x1 x2 x3 x4 x5 x6
            + deltaX4 x1 x2 x3 x4 x5 x6 * (-2 * x4)))
      - ((2 * deltaX x1 x2 x3 x4 x5 x6 + 2 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
          * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
        + 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2)))
        * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (upsX x1 x2 x6 * upsX x1 x3 x5))
      - 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
            + x1 * (deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
          - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
            * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
        * ((4 * deltaX x1 x2 x3 x4 x5 x6 + 4 * x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
            / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
          * (upsX x1 x2 x6 * upsX x1 x3 x5)
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * ((2 * x2 + 2 * x6 - 2 * x1) * upsX x1 x3 x5
            + upsX x1 x2 x6 * (2 * x3 + 2 * x5 - 2 * x1))))
      / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ^ 2)) x1 :=
    hN.div hD3 hDne
  rw [show (fun t => g4dDihX1 t x2 x3 x4 x5 x6)
      = fun t => (2 * (deltaX4 t x2 x3 x4 x5 x6 * deltaX t x2 x3 x4 x5 x6
            + t * (deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6)
          - 2 * t * deltaX t x2 x3 x4 x5 x6
            * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6)))
        / (Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6)
          * (upsX t x2 x6 * upsX t x3 x5)) from by
        funext t; unfold g4dDihX1; ring]
  exact hND

/-! ### Axiom audit -/

#print axioms hasDerivAt_quad_s2a
#print axioms dihXf_second_deriv_x4
#print axioms dihXf_second_deriv_x5
#print axioms dihXf_second_deriv_x6
#print axioms dihXf_second_deriv_x1

end Kepler.Text
