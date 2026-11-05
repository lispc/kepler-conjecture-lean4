/-
Kepler.Text.Gamma4Deriv — derivative kit for `dihXf` at the TSKAJXY sharp
boxes (lane `gamma4-w2`, second wave after `Gamma4Sharp` / `Gamma4SharpRoute`).
Contents, all machine-checked with no extra axioms:
* the rationalisation invariant `Δ₄² + 4·x₁·Δ = upsX x1 x3 x5 · upsX x1 x2 x6`
  (`g4d_ups_delta`) and its slot companions `g4d_delta_ident_x2/x3/x5/x6`,
  which cancel the radicals/`upsX` factors in the arctan derivative;
* `HasDerivAt` for `dihXf` in each of its six slots, with the closed-form
  (rationalised) derivative value.  Writing `A = √(4·x₁·Δ)`,
  `Δᵢ = ∂Δ/∂xᵢ`, `u₁₂₆ = upsX x1 x2 x6`, `u₁₃₅ = upsX x1 x3 x5`:
    x1: 2·(Δ·Δ₄ + x₁·Δ₄·Δ₁ − 2·x₁·Δ·∂Δ₄/∂x₁) / (A·u₁₂₆·u₁₃₅)
    x2: −2·x₁·Δ₃ / (A·u₁₂₆)
    x3: −2·x₁·Δ₂ / (A·u₁₃₅)
    x4: √x₁/√Δ            (= 2·x₁/A)
    x5: −2·x₁·Δ₆ / (A·u₁₃₅)
    x6: −2·x₁·Δ₅ / (A·u₁₂₆)
  (the x4/x5/x6 forms are the HOL `OCBICBY` `derived_form_dih_x_wrt_x4/5/6`
  values; the x1/x2/x3 slots were not in HOL's consumer and are derived here);
* sign verdicts for the `dihXf` partials on the x-box `[4, 4.004001]⁶`
  (the square of the RIBCYXU sharp y-box `[2,2.001]⁶`).
This is part 1 of 2: the `deltaX` partials, the rationalisation identities,
the `atn2` derivative kit, the slot atoms and the `x1` partial.  Part 2
(`Gamma4Deriv2`) carries the `x2`–`x6` partials and the box sign verdicts.
The reduction of `gamma4fgcy` monotonicity to these partials (the `volY`,
`solY`, `dihY`, `lmfun` chain and its sign analysis) is NOT done here; see
`DELIVERY.md` for the exact next-wave starting point.
-/
import Kepler.Text.Gamma4SharpRoute
set_option maxHeartbeats 4000000
open Filter
open scoped Topology

namespace Kepler.Text

/-! ## Partial-derivative polynomials of `deltaX`

`deltaX4`/`deltaX5` are the canonical SphereKit names for the x4/x5 slots;
SphereKit defers `delta_x6` and there is no canonical x1/x2/x3 name, so the
missing four partials live here (kept local to this kit). -/

/-- `∂deltaX/∂x1`. -/
def g4dDX1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -2 * x1 * x4 + x2 * x4 + x2 * x5 - x2 * x6 + x3 * x4 - x3 * x5 + x3 * x6
    - x4 ^ 2 + x4 * x5 + x4 * x6

/-- `∂deltaX/∂x2`. -/
def g4dDX2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x1 * x5 - x1 * x6 - 2 * x2 * x5 - x3 * x4 + x3 * x5 + x3 * x6
    + x4 * x5 - x5 ^ 2 + x5 * x6

/-- `∂deltaX/∂x3`. -/
def g4dDX3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 - x1 * x5 + x1 * x6 - x2 * x4 + x2 * x5 + x2 * x6 - 2 * x3 * x6
    + x4 * x6 + x5 * x6 - x6 ^ 2

/-- `∂deltaX/∂x6` (SphereKit defers `delta_x6`). -/
def g4dDX6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x5 - x3 ^ 2 + x3 * x4
    + x3 * x5 - 2 * x3 * x6 - x4 * x5

/-! ## The rationalisation identities

The first is HOL `OCBICBY.ups_x_delta_x`; the four slot companions are the
polynomial identities that turn the raw arctan-derivative numerator into the
`−2·x₁·Δⱼ/(A·ups)` forms. -/

/-- HOL `ups_x_delta_x`: `Δ₄² + 4·x₁·Δ = upsX x1 x3 x5 · upsX x1 x2 x6`. -/
theorem g4d_ups_delta (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
      = upsX x1 x3 x5 * upsX x1 x2 x6 := by
  simp only [deltaX, deltaX4, upsX]
  ring

theorem g4d_delta_ident_x2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX2 x1 x2 x3 x4 x5 x6
      + upsX x1 x3 x5 * g4dDX3 x1 x2 x3 x4 x5 x6
      = 2 * deltaX x1 x2 x3 x4 x5 x6 * (x1 - x3 + x5) := by
  simp only [deltaX, deltaX4, g4dDX2, g4dDX3, upsX]
  ring

theorem g4d_delta_ident_x3 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX3 x1 x2 x3 x4 x5 x6
      + upsX x1 x2 x6 * g4dDX2 x1 x2 x3 x4 x5 x6
      = 2 * deltaX x1 x2 x3 x4 x5 x6 * (x1 - x2 + x6) := by
  simp only [deltaX, deltaX4, g4dDX2, g4dDX3, upsX]
  ring

theorem g4d_delta_ident_x5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 * deltaX5 x1 x2 x3 x4 x5 x6
      + upsX x1 x2 x6 * g4dDX6 x1 x2 x3 x4 x5 x6
      = 2 * deltaX x1 x2 x3 x4 x5 x6 * (x1 + x2 - x6) := by
  simp only [deltaX, deltaX4, deltaX5, g4dDX6, upsX]
  ring

theorem g4d_delta_ident_x6 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX6 x1 x2 x3 x4 x5 x6
      + upsX x1 x3 x5 * deltaX5 x1 x2 x3 x4 x5 x6
      = 2 * deltaX x1 x2 x3 x4 x5 x6 * (x1 + x3 - x5) := by
  simp only [deltaX, deltaX4, deltaX5, g4dDX6, upsX]
  ring

/-! ## Elementary `HasDerivAt` atoms -/

/-- Derivative of a quadratic, in the `a*(q*q) + (b*q+c)` normal form. -/
private theorem hasDerivAt_quad (a b c x : ℝ) :
    HasDerivAt (fun q : ℝ => a * (q * q) + (b * q + c)) (a * (x + x) + b) x := by
  have h1 : HasDerivAt (fun q : ℝ => q * q) (x + x) x := by
    exact HasDerivAt.congr_deriv
      ((hasDerivAt_id x).mul (hasDerivAt_id x)) (by norm_num)
  have h2 : HasDerivAt (fun q : ℝ => b * q + c) (b * 1 + 0) x :=
    ((hasDerivAt_id x).const_mul b).add (hasDerivAt_const (x := x) (c := c))
  exact HasDerivAt.congr_deriv ((h1.const_mul a).add h2) (by norm_num)

/-- Derivative of an affine function. -/
private theorem hasDerivAt_affine (a b x : ℝ) :
    HasDerivAt (fun q : ℝ => a * q + b) a x := by
  have h : HasDerivAt (fun q : ℝ => a * q + b) (a * 1 + 0) x :=
    ((hasDerivAt_id x).const_mul a).add (hasDerivAt_const (x := x) (c := b))
  exact HasDerivAt.congr_deriv h (by norm_num)

/-! ### `deltaX` in each slot -/

private theorem hasDerivAt_deltaX_x1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX t x2 x3 x4 x5 x6) (g4dDX1 x1 x2 x3 x4 x5 x6) x1 := by
  have h := hasDerivAt_quad (-x4)
    (x4 * (x2 + x3 - x4 + x5 + x6) + x2 * x5 + x3 * x6 - x3 * x5 - x2 * x6)
    (x2 * x5 * (-x2 + x3 + x4 - x5 + x6) + x3 * x6 * (x2 - x3 + x4 + x5 - x6)
      - x2 * x3 * x4 - x4 * x5 * x6) x1
  have he : (fun t => deltaX t x2 x3 x4 x5 x6) = fun q => (-x4) * (q * q)
      + ((x4 * (x2 + x3 - x4 + x5 + x6) + x2 * x5 + x3 * x6 - x3 * x5 - x2 * x6) * q
        + (x2 * x5 * (-x2 + x3 + x4 - x5 + x6) + x3 * x6 * (x2 - x3 + x4 + x5 - x6)
          - x2 * x3 * x4 - x4 * x5 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [g4dDX1]; ring)

theorem g4d_hasDerivAt_deltaX_x2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 t x3 x4 x5 x6) (g4dDX2 x1 x2 x3 x4 x5 x6) x2 := by
  have h := hasDerivAt_quad (-x5)
    (x1 * x4 + x1 * x5 + x3 * x5 + x4 * x5 - x5 ^ 2 + x5 * x6 + x3 * x6 - x3 * x4 - x1 * x6)
    (x1 * x4 * (-x1 + x3 - x4 + x5 + x6) + x3 * x6 * (x1 - x3 + x4 + x5 - x6)
      - x1 * x3 * x5 - x4 * x5 * x6) x2
  have he : (fun t => deltaX x1 t x3 x4 x5 x6) = fun q => (-x5) * (q * q)
      + ((x1 * x4 + x1 * x5 + x3 * x5 + x4 * x5 - x5 ^ 2 + x5 * x6 + x3 * x6 - x3 * x4 - x1 * x6) * q
        + (x1 * x4 * (-x1 + x3 - x4 + x5 + x6) + x3 * x6 * (x1 - x3 + x4 + x5 - x6)
          - x1 * x3 * x5 - x4 * x5 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [g4dDX2]; ring)

theorem g4d_hasDerivAt_deltaX_x3 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 x2 t x4 x5 x6) (g4dDX3 x1 x2 x3 x4 x5 x6) x3 := by
  have h := hasDerivAt_quad (-x6)
    (x1 * x4 - x1 * x5 - x2 * x4 + x2 * x5 + x1 * x6 + x2 * x6 + x4 * x6 + x5 * x6 - x6 ^ 2)
    (x1 * x4 * (-x1 + x2 - x4 + x5 + x6) + x2 * x5 * (x1 - x2 + x4 - x5 + x6)
      - x1 * x2 * x6 - x4 * x5 * x6) x3
  have he : (fun t => deltaX x1 x2 t x4 x5 x6) = fun q => (-x6) * (q * q)
      + ((x1 * x4 - x1 * x5 - x2 * x4 + x2 * x5 + x1 * x6 + x2 * x6 + x4 * x6 + x5 * x6 - x6 ^ 2) * q
        + (x1 * x4 * (-x1 + x2 - x4 + x5 + x6) + x2 * x5 * (x1 - x2 + x4 - x5 + x6)
          - x1 * x2 * x6 - x4 * x5 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [g4dDX3]; ring)

theorem g4d_hasDerivAt_deltaX_x4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 x2 x3 t x5 x6) (deltaX4 x1 x2 x3 x4 x5 x6) x4 := by
  have h := hasDerivAt_quad (-x1)
    (x1 * (-x1 + x2 + x3 + x5 + x6) + (x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6))
    (x2 * x5 * (x1 - x2 + x3 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x5 - x6)
      - x1 * x3 * x5 - x1 * x2 * x6) x4
  have he : (fun t => deltaX x1 x2 x3 t x5 x6) = fun q => (-x1) * (q * q)
      + ((x1 * (-x1 + x2 + x3 + x5 + x6) + (x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6)) * q
        + (x2 * x5 * (x1 - x2 + x3 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x5 - x6)
          - x1 * x3 * x5 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [deltaX4]; ring)

theorem g4d_hasDerivAt_deltaX_x5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 x2 x3 x4 t x6) (deltaX5 x1 x2 x3 x4 x5 x6) x5 := by
  have h := hasDerivAt_quad (-x2)
    (x1 * x4 + x1 * x2 - x2 ^ 2 + x2 * x3 + x2 * x4 + x2 * x6 + x3 * x6 - x1 * x3 - x4 * x6)
    (x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6)
      - x2 * x3 * x4 - x1 * x2 * x6) x5
  have he : (fun t => deltaX x1 x2 x3 x4 t x6) = fun q => (-x2) * (q * q)
      + ((x1 * x4 + x1 * x2 - x2 ^ 2 + x2 * x3 + x2 * x4 + x2 * x6 + x3 * x6 - x1 * x3 - x4 * x6) * q
        + (x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6)
          - x2 * x3 * x4 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [deltaX5]; ring)

theorem g4d_hasDerivAt_deltaX_x6 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 x2 x3 x4 x5 t) (g4dDX6 x1 x2 x3 x4 x5 x6) x6 := by
  have h := hasDerivAt_quad (-x3)
    (x1 * x4 + x2 * x5 + x1 * x3 + x2 * x3 - x3 ^ 2 + x3 * x4 + x3 * x5 - x1 * x2 - x4 * x5)
    (x1 * x4 * (-x1 + x2 + x3 - x4 + x5) + x2 * x5 * (x1 - x2 + x3 + x4 - x5)
      - x2 * x3 * x4 - x1 * x3 * x5) x6
  have he : (fun t => deltaX x1 x2 x3 x4 x5 t) = fun q => (-x3) * (q * q)
      + ((x1 * x4 + x2 * x5 + x1 * x3 + x2 * x3 - x3 ^ 2 + x3 * x4 + x3 * x5 - x1 * x2 - x4 * x5) * q
        + (x1 * x4 * (-x1 + x2 + x3 - x4 + x5) + x2 * x5 * (x1 - x2 + x3 + x4 - x5)
          - x2 * x3 * x4 - x1 * x3 * x5)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [g4dDX6]; ring)

/-! ### `deltaX4` in each slot -/

private theorem hasDerivAt_deltaX4_x1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 t x2 x3 x4 x5 x6)
      (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) x1 := by
  have h := hasDerivAt_quad (-1) (x2 + x3 - 2 * x4 + x5 + x6)
    (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6) x1
  have he : (fun t => deltaX4 t x2 x3 x4 x5 x6) = fun q => (-1) * (q * q)
      + ((x2 + x3 - 2 * x4 + x5 + x6) * q + (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by ring)

theorem g4d_hasDerivAt_deltaX4_x2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 t x3 x4 x5 x6) (x1 - x3 + x5) x2 := by
  have h := hasDerivAt_affine (x1 - x3 + x5)
    (-x1 * x4 + x3 * x6 - x5 * x6 + x1 * (-x1 + x3 - x4 + x5 + x6)) x2
  have he : (fun t => deltaX4 x1 t x3 x4 x5 x6) = fun q => (x1 - x3 + x5) * q
      + (-x1 * x4 + x3 * x6 - x5 * x6 + x1 * (-x1 + x3 - x4 + x5 + x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

theorem g4d_hasDerivAt_deltaX4_x3 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 x2 t x4 x5 x6) (x1 - x2 + x6) x3 := by
  have h := hasDerivAt_affine (x1 - x2 + x6)
    (-x1 * x4 + x2 * x5 - x5 * x6 + x1 * (-x1 + x2 - x4 + x5 + x6)) x3
  have he : (fun t => deltaX4 x1 x2 t x4 x5 x6) = fun q => (x1 - x2 + x6) * q
      + (-x1 * x4 + x2 * x5 - x5 * x6 + x1 * (-x1 + x2 - x4 + x5 + x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

theorem g4d_hasDerivAt_deltaX4_x4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 x2 x3 t x5 x6) (-2 * x1) x4 := by
  have h := hasDerivAt_affine (-2 * x1)
    (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6 + x1 * (-x1 + x2 + x3 + x5 + x6)) x4
  have he : (fun t => deltaX4 x1 x2 x3 t x5 x6) = fun q => (-2 * x1) * q
      + (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6 + x1 * (-x1 + x2 + x3 + x5 + x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

theorem g4d_hasDerivAt_deltaX4_x5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 x2 x3 x4 t x6) (x1 + x2 - x6) x5 := by
  have h := hasDerivAt_affine (x1 + x2 - x6)
    (-x2 * x3 - x1 * x4 + x3 * x6 + x1 * (-x1 + x2 + x3 - x4 + x6)) x5
  have he : (fun t => deltaX4 x1 x2 x3 x4 t x6) = fun q => (x1 + x2 - x6) * q
      + (-x2 * x3 - x1 * x4 + x3 * x6 + x1 * (-x1 + x2 + x3 - x4 + x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

theorem g4d_hasDerivAt_deltaX4_x6 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 x2 x3 x4 x5 t) (x1 + x3 - x5) x6 := by
  have h := hasDerivAt_affine (x1 + x3 - x5)
    (-x2 * x3 - x1 * x4 + x2 * x5 + x1 * (-x1 + x2 + x3 - x4 + x5)) x6
  have he : (fun t => deltaX4 x1 x2 x3 x4 x5 t) = fun q => (x1 + x3 - x5) * q
      + (-x2 * x3 - x1 * x4 + x2 * x5 + x1 * (-x1 + x2 + x3 - x4 + x5)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

/-! ## `atn2` derivative on the right half-plane -/

private theorem atn2_of_neg {A B : ℝ} (hA : 0 < A) (hB : B < 0) :
    atn2 A B = -(Real.pi / 2) - Real.arctan (A / B) := by
  unfold atn2
  by_cases h1 : |B| < A
  · rw [if_pos h1]
    have hBA : B / A < 0 := div_neg_of_neg_of_pos hB hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp [ne_of_lt hB]
    rw [hrec, Real.arctan_inv_of_neg hBA]
    ring
  · rw [if_neg h1]
    by_cases h2 : 0 < B
    · exact absurd h2 (not_lt.mpr hB.le)
    · rw [if_neg h2]
      by_cases h3 : B < 0
      · rw [if_pos h3]
      · exact absurd hB h3

private theorem atn2_of_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    atn2 A B = Real.pi / 2 - Real.arctan (A / B) := by
  unfold atn2
  by_cases h1 : |B| < A
  · rw [if_pos h1]
    have hBA : 0 < B / A := div_pos hB hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp [ne_of_gt hB]
    rw [hrec, Real.arctan_inv_of_pos hBA]
    ring
  · rw [if_neg h1]
    by_cases h2 : 0 < B
    · rw [if_pos h2]
    · exact absurd hB h2

/-- Derivative of `atn2 (A t) (B t)` for `A t > 0`, all `atn2` branches. -/
private theorem hasDerivAt_atn2 {A B : ℝ → ℝ} {A' B' t : ℝ}
    (hA : 0 < A t) (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) :
    HasDerivAt (fun s => atn2 (A s) (B s))
      ((A t * B' - B t * A') / (A t ^ 2 + B t ^ 2)) t := by
  have hA2 : A t ^ 2 + B t ^ 2 ≠ 0 := by positivity
  rcases lt_trichotomy (B t) 0 with hneg | hzero | hpos
  · have hevA : ∀ᶠ s in 𝓝 t, 0 < A s :=
      hA'.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)
    have hevB : ∀ᶠ s in 𝓝 t, B s < 0 :=
      hB'.continuousAt.eventually_lt continuousAt_const hneg
    have heq : (fun s => atn2 (A s) (B s)) =ᶠ[𝓝 t]
        (fun s => -(Real.pi / 2) - Real.arctan (A s / B s)) := by
      filter_upwards [hevA, hevB] with s hsA hsB
      exact atn2_of_neg hsA hsB
    have hdiv : HasDerivAt (fun s => A s / B s) ((A' * B t - A t * B') / (B t) ^ 2) t :=
      hA'.div hB' (ne_of_lt hneg)
    have hmain : HasDerivAt (fun s => -(Real.pi / 2) - Real.arctan (A s / B s))
        (0 - (1 / (1 + (A t / B t) ^ 2)) * ((A' * B t - A t * B') / (B t) ^ 2)) t :=
      (hasDerivAt_const (x := t) (c := -(Real.pi / 2))).sub hdiv.arctan
    refine (hmain.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp [ne_of_lt hneg, hA2]
    ring
  · have hlt : |B t| < A t := by rw [hzero, abs_zero]; exact hA
    have hev : ∀ᶠ s in 𝓝 t, |B s| < A s :=
      (hB'.continuousAt.abs).eventually_lt hA'.continuousAt hlt
    have heq : (fun s => atn2 (A s) (B s)) =ᶠ[𝓝 t]
        (fun s => Real.arctan (B s / A s)) := by
      filter_upwards [hev] with s hs
      unfold atn2
      exact if_pos hs
    have hdiv : HasDerivAt (fun s => B s / A s) ((B' * A t - B t * A') / (A t) ^ 2) t :=
      hB'.div hA' (ne_of_gt hA)
    have hmain : HasDerivAt (fun s => Real.arctan (B s / A s))
        ((1 / (1 + (B t / A t) ^ 2)) * ((B' * A t - B t * A') / (A t) ^ 2)) t :=
      hdiv.arctan
    refine (hmain.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp [ne_of_gt hA, hA2]
  · have hevA : ∀ᶠ s in 𝓝 t, 0 < A s :=
      hA'.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)
    have hevB : ∀ᶠ s in 𝓝 t, 0 < B s :=
      continuousAt_const.eventually_lt hB'.continuousAt hpos
    have heq : (fun s => atn2 (A s) (B s)) =ᶠ[𝓝 t]
        (fun s => Real.pi / 2 - Real.arctan (A s / B s)) := by
      filter_upwards [hevA, hevB] with s hsA hsB
      exact atn2_of_pos hsA hsB
    have hdiv : HasDerivAt (fun s => A s / B s) ((A' * B t - A t * B') / (B t) ^ 2) t :=
      hA'.div hB' (ne_of_gt hpos)
    have hmain : HasDerivAt (fun s => Real.pi / 2 - Real.arctan (A s / B s))
        (0 - (1 / (1 + (A t / B t) ^ 2)) * ((A' * B t - A t * B') / (B t) ^ 2)) t :=
      (hasDerivAt_const (x := t) (c := Real.pi / 2)).sub hdiv.arctan
    refine (hmain.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp [ne_of_gt hpos, hA2]
    ring

/-! ## Derivative of `dihXf` in the slots with `x1` fixed (x2–x6) -/

theorem g4d_hasDerivAt_dihXf_aux {f g : ℝ → ℝ} {f' g' t x1 : ℝ}
    (hx1 : 0 < x1) (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hfpos : 0 < f t) :
    HasDerivAt (fun s => Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * f s)) (-(g s)))
      ((2 * x1 * g t * f' - 4 * x1 * f t * g')
        / (Real.sqrt (4 * x1 * f t) * (4 * x1 * f t + g t ^ 2))) t := by
  have hpos : 0 < 4 * x1 * f t := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * f t) := Real.sqrt_pos.mpr hpos
  have hA' : HasDerivAt (fun s => Real.sqrt (4 * x1 * f s))
      (4 * x1 * f' / (2 * Real.sqrt (4 * x1 * f t))) t :=
    (hf.const_mul (4 * x1)).sqrt (ne_of_gt hpos)
  have hB' : HasDerivAt (fun s => -(g s)) (-g') t := hg.neg
  have h := (hasDerivAt_const (x := t) (c := Real.pi / 2)).add
    (hasDerivAt_atn2 hA hA' hB')
  refine h.congr_deriv ?_
  have hA2 : Real.sqrt (4 * x1 * f t) ^ 2 = 4 * x1 * f t := Real.sq_sqrt (le_of_lt hpos)
  have hA0 : Real.sqrt (4 * x1 * f t) ≠ 0 := ne_of_gt hA
  field_simp [hA0]
  rw [hA2]
  ring

/-! ## The `x1` partial derivative -/

/-- `∂dihXf/∂x1`, rationalised against `u₁₂₆·u₁₃₅`. -/
theorem dihXf_hasDerivAt_x1 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => dihXf t x2 x3 x4 x5 x6)
      (2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
          + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
          - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
            * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5))) x1 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hpos
  have hA' : HasDerivAt (fun t => Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6))
      (4 * (deltaX x1 x2 x3 x4 x5 x6 + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x1 := by
    have hu : HasDerivAt (fun t : ℝ => 4 * t * deltaX t x2 x3 x4 x5 x6)
        (4 * (deltaX x1 x2 x3 x4 x5 x6 + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)) x1 := by
      have h1 : HasDerivAt (fun t : ℝ => 4 * t) 4 x1 := by
        simpa using (hasDerivAt_id x1).const_mul 4
      have hm := h1.mul (hasDerivAt_deltaX_x1 x1 x2 x3 x4 x5 x6)
      have he : ((fun t : ℝ => 4 * t) * fun t => deltaX t x2 x3 x4 x5 x6)
          = fun t => 4 * t * deltaX t x2 x3 x4 x5 x6 := by
        funext t; simp only [Pi.mul_apply]
      rw [he] at hm
      exact hm.congr_deriv (by ring)
    exact hu.sqrt (ne_of_gt hpos)
  have hB' : HasDerivAt (fun t => -(deltaX4 t x2 x3 x4 x5 x6))
      (-(-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)) x1 :=
    (hasDerivAt_deltaX4_x1 x1 x2 x3 x4 x5 x6).neg
  have h := (hasDerivAt_const (x := x1) (c := Real.pi / 2)).add
    (hasDerivAt_atn2 hA hA' hB')
  have he : ((fun _ : ℝ => Real.pi / 2) + fun s =>
        atn2 (Real.sqrt (4 * s * deltaX s x2 x3 x4 x5 x6)) (-(deltaX4 s x2 x3 x4 x5 x6)))
      = fun t => Real.pi / 2 + atn2 (Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6))
          (-(deltaX4 t x2 x3 x4 x5 x6)) := by
    funext t; rfl
  rw [he] at h
  have h' : HasDerivAt (fun t => dihXf t x2 x3 x4 x5 x6)
      ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (-(-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
          - (-(deltaX4 x1 x2 x3 x4 x5 x6))
            * (4 * (deltaX x1 x2 x3 x4 x5 x6 + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
              / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2
            + (-(deltaX4 x1 x2 x3 x4 x5 x6)) ^ 2)) x1 := by
    simpa only [dihXf, zero_add] using h
  refine h'.congr_deriv ?_
  have hA2 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2
      = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := Real.sq_sqrt (le_of_lt hpos)
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have hE' : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
      + (-(deltaX4 x1 x2 x3 x4 x5 x6)) ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [show (-(deltaX4 x1 x2 x3 x4 x5 x6)) ^ 2 = deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 by ring,
      add_comm, g4d_ups_delta, mul_comm]
  have hA2' : Real.sqrt (x1 * deltaX x1 x2 x3 x4 x5 x6 * 4) ^ 2
      = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by
    rw [show x1 * deltaX x1 x2 x3 x4 x5 x6 * 4
      = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 by ring, hA2]
  rw [hA2, hE']
  field_simp [hA0]
  rw [hA2]
  ring

/-! ## Axiom audit (part 1) -/

#print axioms g4d_ups_delta
#print axioms g4d_delta_ident_x2
#print axioms g4d_delta_ident_x3
#print axioms g4d_delta_ident_x5
#print axioms g4d_delta_ident_x6
#print axioms dihXf_hasDerivAt_x1

end Kepler.Text
