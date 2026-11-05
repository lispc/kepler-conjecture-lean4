/-
Kepler.Text.Gamma4Deriv3 — lane `gamma4-w3`, part 1 of the y-space derivative
chain on top of the `dihXf` kit (`Gamma4Deriv` / `Gamma4Deriv2`).

Contents:
* the six `dihXf` slot partial values as named functions `g4dDihX1..6`
  (definitionally the values of `dihXf_hasDerivAt_x1..x6`);
* the `deltaX` permutation invariance lemmas for the fourteen edge
  permutations used by `solY` / `vol4f` (all are even permutations of the
  six edge slots, i.e. tetrahedral rotations; each closes by `ring`);
* the six `volY` y-partials: with `Δ = deltaY y1..y6` and
  `Δᵢ = ∂deltaX/∂xᵢ` at the squared arguments,
    `∂volY/∂yᵢ = yᵢ·Δᵢ / (12·√Δ)`   (`volY_hasDerivAt_y1..y6`).
-/
import Kepler.Text.Gamma4Deriv2

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## The `dihXf` partial values as named functions

These are verbatim the derivative values of `dihXf_hasDerivAt_x1..x6`, kept as
`def`s so that the downstream chain (`dihY`, `solY`, `vol4f`, `gamma4fgcy`)
can state its derivative in closed form. -/

/-- `∂dihXf/∂x1`, rationalised against `u₁₂₆·u₁₃₅`. -/
noncomputable def g4dDihX1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
      + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
      - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
        * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
    / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        * (upsX x1 x2 x6 * upsX x1 x3 x5))

/-- `∂dihXf/∂x2 = −2·x₁·Δ₃/(A·u₁₂₆)`. -/
noncomputable def g4dDihX2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
    / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)

/-- `∂dihXf/∂x3 = −2·x₁·Δ₂/(A·u₁₃₅)`. -/
noncomputable def g4dDihX3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
    / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)

/-- `∂dihXf/∂x4 = 2·x₁/A`. -/
noncomputable def g4dDihX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  2 * x1 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)

/-- `∂dihXf/∂x5 = −2·x₁·Δ₆/(A·u₁₃₅)`. -/
noncomputable def g4dDihX5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
    / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)

/-- `∂dihXf/∂x6 = −2·x₁·Δ₅/(A·u₁₂₆)`. -/
noncomputable def g4dDihX6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
    / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)

/-! ## `deltaX` invariance under the edge permutations of `solY`/`vol4f`

`solY` expands into twelve `dihY` argument tuples and `vol4f` carries six
more; together they use fourteen permutations of the six edge slots.  All are
even permutations (tetrahedral rotations) and leave `deltaX` invariant. -/

theorem g4d_deltaX_p231564 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x2 x3 x1 x5 x6 x4 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p312645 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x3 x1 x2 x6 x4 x5 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p156423 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x1 x5 x6 x4 x2 x3 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p561234 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x5 x6 x1 x2 x3 x4 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p615342 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x6 x1 x5 x3 x4 x2 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p453126 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x4 x5 x3 x1 x2 x6 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p534261 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x5 x3 x4 x2 x6 x1 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p345612 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x3 x4 x5 x6 x1 x2 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p426153 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x4 x2 x6 x1 x5 x3 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p264531 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x2 x6 x4 x5 x3 x1 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p642315 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x6 x4 x2 x3 x1 x5 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p435162 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x4 x3 x5 x1 x6 x2 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

theorem g4d_deltaX_p516243 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x5 x1 x6 x2 x4 x3 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]; ring

/-! The same invariance in `y` coordinates (each `yᵢ²` plays the role of `xᵢ`). -/

theorem g4d_deltaY_p231564 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y2 y3 y1 y5 y6 y4 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p231564 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p312645 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y3 y1 y2 y6 y4 y5 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p312645 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p156423 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y1 y5 y6 y4 y2 y3 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p156423 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p561234 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y5 y6 y1 y2 y3 y4 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p561234 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p615342 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y6 y1 y5 y3 y4 y2 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p615342 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p453126 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y4 y5 y3 y1 y2 y6 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p453126 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p534261 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y5 y3 y4 y2 y6 y1 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p534261 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p345612 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y3 y4 y5 y6 y1 y2 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p345612 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p426153 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y4 y2 y6 y1 y5 y3 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p426153 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p264531 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y2 y6 y4 y5 y3 y1 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p264531 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p642315 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y6 y4 y2 y3 y1 y5 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p642315 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p435162 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y4 y3 y5 y1 y6 y2 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p435162 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

theorem g4d_deltaY_p516243 (y1 y2 y3 y4 y5 y6 : ℝ) :
    deltaY y5 y1 y6 y2 y4 y3 = deltaY y1 y2 y3 y4 y5 y6 := by
  simpa only [deltaY] using
    g4d_deltaX_p516243 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-! ## Elementary composition helpers -/

/-- Derivative of a quadratic in the `a*(q*q) + (b*q+c)` normal form. -/
private theorem hasDerivAt_quad (a b c x : ℝ) :
    HasDerivAt (fun q : ℝ => a * (q * q) + (b * q + c)) (a * (x + x) + b) x := by
  have h1 : HasDerivAt (fun q : ℝ => q * q) (x + x) x := by
    exact HasDerivAt.congr_deriv
      ((hasDerivAt_id x).mul (hasDerivAt_id x)) (by norm_num)
  have h2 : HasDerivAt (fun q : ℝ => b * q + c) (b * 1 + 0) x :=
    ((hasDerivAt_id x).const_mul b).add (hasDerivAt_const (x := x) (c := c))
  exact HasDerivAt.congr_deriv ((h1.const_mul a).add h2) (by norm_num)

/-- `∂deltaX/∂x1` (the w2 kit keeps this one private). -/
theorem g4d3_hasDerivAt_deltaX_x1 (x1 x2 x3 x4 x5 x6 : ℝ) :
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

/-- `t ↦ t*t`. -/
theorem g4d_hasDerivAt_sq (x : ℝ) : HasDerivAt (fun t : ℝ => t * t) (2 * x) x := by
  have h := hasDerivAt_quad 1 0 0 x
  have he : (fun t : ℝ => t * t) = fun q : ℝ => 1 * (q * q) + (0 * q + 0) := by
    funext q; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by ring)

/-- Chain rule for the substitution `t ↦ t*t`. -/
theorem g4d_hasDerivAt_sq_comp {F : ℝ → ℝ} {F' x : ℝ} (hF : HasDerivAt F F' (x * x)) :
    HasDerivAt (fun t => F (t * t)) (F' * (2 * x)) x := by
  have h := HasDerivAt.comp (𝕜 := ℝ) (x := x) (h := fun t : ℝ => t * t) (h₂ := F)
    hF (g4d_hasDerivAt_sq x)
  convert h using 1 <;> rfl

/-- `t ↦ √(F t)/12`. -/
private theorem hasDerivAt_sqrt_div12 {F : ℝ → ℝ} {F' x : ℝ}
    (hF : HasDerivAt F F' x) (hpos : 0 < F x) :
    HasDerivAt (fun t => Real.sqrt (F t) / 12) (F' / (24 * Real.sqrt (F x))) x := by
  have hs : Real.sqrt (F x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have h := (hF.sqrt (ne_of_gt hpos)).div_const 12
  refine h.congr_deriv ?_
  field_simp
  ring

/-! ## The six `volY` y-partials

`volY y = √(Δ)/12` with `Δ = deltaY y`; hence `∂volY/∂yᵢ = yᵢ·Δᵢ/(12·√Δ)`,
where `Δᵢ` is the `xᵢ` partial of `deltaX` at the squared arguments. -/

theorem volY_hasDerivAt_y1 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => volY t y2 y3 y4 y5 y6)
      (y1 * g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))) y1 := by
  have hdx : HasDerivAt
      (fun t => deltaX (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      (g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        * (2 * y1)) y1 :=
    g4d_hasDerivAt_sq_comp
      (g4d3_hasDerivAt_deltaX_x1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
  have h := hasDerivAt_sqrt_div12 hdx (by simpa only [deltaY] using hd)
  convert h using 1
  · funext t
    simp only [volY, volXf]
  · simp only [deltaY]
    field_simp
    ring

theorem volY_hasDerivAt_y2 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => volY y1 t y3 y4 y5 y6)
      (y2 * g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))) y2 := by
  have hdx : HasDerivAt
      (fun t => deltaX (y1 * y1) (t * t) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      (g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        * (2 * y2)) y2 :=
    g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
  have h := hasDerivAt_sqrt_div12 hdx (by simpa only [deltaY] using hd)
  convert h using 1
  · funext t
    simp only [volY, volXf]
  · simp only [deltaY]
    field_simp
    ring

theorem volY_hasDerivAt_y3 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => volY y1 y2 t y4 y5 y6)
      (y3 * g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))) y3 := by
  have hdx : HasDerivAt
      (fun t => deltaX (y1 * y1) (y2 * y2) (t * t) (y4 * y4) (y5 * y5) (y6 * y6))
      (g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        * (2 * y3)) y3 :=
    g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
  have h := hasDerivAt_sqrt_div12 hdx (by simpa only [deltaY] using hd)
  convert h using 1
  · funext t
    simp only [volY, volXf]
  · simp only [deltaY]
    field_simp
    ring

theorem volY_hasDerivAt_y4 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => volY y1 y2 y3 t y5 y6)
      (y4 * deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))) y4 := by
  have hdx : HasDerivAt
      (fun t => deltaX (y1 * y1) (y2 * y2) (y3 * y3) (t * t) (y5 * y5) (y6 * y6))
      (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        * (2 * y4)) y4 :=
    g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
  have h := hasDerivAt_sqrt_div12 hdx (by simpa only [deltaY] using hd)
  convert h using 1
  · funext t
    simp only [volY, volXf]
  · simp only [deltaY]
    field_simp
    ring

theorem volY_hasDerivAt_y5 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => volY y1 y2 y3 y4 t y6)
      (y5 * deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))) y5 := by
  have hdx : HasDerivAt
      (fun t => deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (t * t) (y6 * y6))
      (deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        * (2 * y5)) y5 :=
    g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
  have h := hasDerivAt_sqrt_div12 hdx (by simpa only [deltaY] using hd)
  convert h using 1
  · funext t
    simp only [volY, volXf]
  · simp only [deltaY]
    field_simp
    ring

theorem volY_hasDerivAt_y6 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => volY y1 y2 y3 y4 y5 t)
      (y6 * g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))) y6 := by
  have hdx : HasDerivAt
      (fun t => deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (t * t))
      (g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        * (2 * y6)) y6 :=
    g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
  have h := hasDerivAt_sqrt_div12 hdx (by simpa only [deltaY] using hd)
  convert h using 1
  · funext t
    simp only [volY, volXf]
  · simp only [deltaY]
    field_simp
    ring

/-! ## Axiom audit -/

#print axioms g4d_deltaX_p231564
#print axioms g4d_deltaY_p435162
#print axioms volY_hasDerivAt_y1
#print axioms volY_hasDerivAt_y2
#print axioms volY_hasDerivAt_y3
#print axioms volY_hasDerivAt_y4
#print axioms volY_hasDerivAt_y5
#print axioms volY_hasDerivAt_y6

end Kepler.Text
