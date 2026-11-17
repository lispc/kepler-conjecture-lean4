/-
Ox3q1hS2aSupplyKit: S2 supply-batch kit for box5/y4 (batch 2 of the S2a
envelope roadmap, companion to the landed Ox3q1hS2aBox5Y4 pilot cec2264f).

Contents:
1. `comp2_y4sec` — generic chain-rule composition: the second derivative of
   `t ↦ 2*t*g (t*t)` from the slot partial `g`'s own second-partial chain
   (applies to all six `dihXf` slots AND to `volY` via `volY_hasDerivAt2_y4`).
2. `dihXf_second_deriv_x2/_x3` — the x2/x3 second partials (completing the
   six-slot second-derivative base; clones of the landed x5/x6 templates).
3. `dihYcomp_y4sec_slot1..6` — the six instantiated compositions with values
   `2*g4dDihXj(pts) + 4*z_j^2*V_j` (slice variable = the tuple entry `z_j`
   where y4 sits); these are the dihXf-side building blocks for every
   `dihY` instance of a `margin''_y4` assembly (16 live instances on box5:
   12 solY + 4 weighted vol4f + 1 top).
4. `volYcomp_y4sec` — the volY twin.
5. `bump_hasDerivAt/_2` and `lmfun_eq_zero_of_ge` — the mass constants used
   by the c41/c46 margin slices (bump'' = -0.01/0.0654^2 is a nonzero
   constant; lmfun vanishes identically above the h0-kink, which kills the
   y1/y4-slot vol4f dihY-terms on box5).

Numeric study (snapshot study/y4study.py, 2026-11-18): on box5^6 the true
6-D sup of margin''_y4 is about +0.55 (positive; the weak form
`margin'' <= 0` is FALSE), still below b2K41 3 = 949858192033/1099511627776,
so the concrete-K form has slack about +0.31.  The per-gate hslp slot as
landed quantifies `forall y` with no box constraint and is FALSE off box5
(counterexample y = (3,2,2,2.53,2,2): slice'' = 1.386 > K) — supply against
it is BLOCKED pending the statement upgrade `forall y in box5` (SF channel);
this file deliberately delivers only the shape-independent pieces.

No numeric data beyond definition constants; no `sorry`/`axiom`/`native_decide`.
-/
import Mathlib
import Kepler.Text.Ox3q1hS2aBox5Y4
import Kepler.Text.Gamma4Concave

open Set Filter Topology

namespace Kepler.Text

/-! ## 1. Generic y4-composition of a slot second-partial chain -/

/-- If the slot partial `g4` (as a function of its slot variable) has
second-partial chain value `V` at the squared point `w*w`, then the
composition variable `w` (the y4-coordinate sitting in that slot) has
`(2*t*g (t*t))'` = `2*g (w*w) + 4*w^2*V`.  Applies verbatim to the six
`dihXf` slot partials and to `g4dDVolY4` (volY). -/
theorem comp2_y4sec {g4 : ℝ → ℝ} {V w : ℝ}
    (hg : HasDerivAt (fun s : ℝ => g4 s) V (w * w)) :
    HasDerivAt (fun t => 2 * t * g4 (t * t))
      (2 * g4 (w * w) + 4 * (w * w) * V) w := by
  have hc : HasDerivAt (fun t : ℝ => g4 (t * t)) (V * (2 * w)) w :=
    g4d_hasDerivAt_sq_comp hg
  have h2t : HasDerivAt (fun t : ℝ => 2 * t) 2 w := by
    simpa using (hasDerivAt_id w).const_mul 2
  have hp : HasDerivAt (fun t : ℝ => 2 * t * g4 (t * t))
      (2 * g4 (w * w) + 2 * w * (V * (2 * w))) w :=
    h2t.mul hc
  have hv : 2 * g4 (w * w) + 2 * w * (V * (2 * w))
      = 2 * g4 (w * w) + 4 * (w * w) * V := by ring
  exact hp.congr_deriv hv

/-! ## 2. The x2/x3 second partials (six-slot base completion) -/

/-- Second partial of `dihXf` w.r.t. `x2`: the first partial
`g4dDihX2 = -2*x1*g4dDX3/(sqrt(4*x1*deltaX) * upsX x1 x2 x6)` is
differentiable in `x2` (numerator affine in x2 with slope `-x4+x5+x6`,
`deltaX` affine in x2 with slope `g4dDX2`, `upsX x1 x2 x6` quadratic in x2
with slope `2*x1+2*x6-2*x2`), value = the quotient-rule form over
`(sqrt(4*x1*deltaX) * upsX x1 x2 x6)^2` in chain-native shape. -/
theorem dihXf_second_deriv_x2 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX2 x1 t x3 x4 x5 x6)
      (-2 * x1 * (((-x4 + x5 + x6)
            * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
          - g4dDX3 x1 x2 x3 x4 x5 x6
            * ((4 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
                  / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
                * upsX x1 x2 x6
              + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
                * (2 * x1 + 2 * x6 - 2 * x2)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x2 x6) ^ 2))) x2 := by
  have hupos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hsqrtne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hupos)
  have hprodp : 0 < deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  rw [g4d_ups_delta] at hprodp
  have hup2nz : upsX x1 x2 x6 ≠ 0 := by
    intro hc; rw [hc] at hprodp; simp at hprodp
  have hΔ2 : HasDerivAt (fun t => deltaX x1 t x3 x4 x5 x6)
      (g4dDX2 x1 x2 x3 x4 x5 x6) x2 :=
    g4d_hasDerivAt_deltaX_x2 x1 x2 x3 x4 x5 x6
  have hsq : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6))
      (4 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x2 :=
    (hΔ2.const_mul (4 * x1)).sqrt (by positivity)
  have hupsq : HasDerivAt (fun t => (-1) * (t * t)
      + ((2 * x1 + 2 * x6) * t + (2 * x1 * x6 - x1 * x1 - x6 * x6)))
      ((-1) * (x2 + x2) + (2 * x1 + 2 * x6)) x2 :=
    hasDerivAt_quad_s2a (-1) (2 * x1 + 2 * x6)
      (2 * x1 * x6 - x1 * x1 - x6 * x6) x2
  have hvu : (-1) * (x2 + x2) + (2 * x1 + 2 * x6)
      = 2 * x1 + 2 * x6 - 2 * x2 := by ring
  have hup : HasDerivAt (fun t => upsX x1 t x6) (2 * x1 + 2 * x6 - 2 * x2) x2 := by
    rw [show (fun t => upsX x1 t x6) = fun t => (-1) * (t * t)
        + ((2 * x1 + 2 * x6) * t + (2 * x1 * x6 - x1 * x1 - x6 * x6)) from by
          funext t; unfold upsX; ring]
    exact hupsq.congr_deriv hvu
  have hD : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6)
        * upsX x1 t x6)
      (4 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (2 * x1 + 2 * x6 - 2 * x2)) x2 :=
    hsq.mul hup
  have hDne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6 ≠ 0 := by
    intro hc
    rw [mul_eq_zero] at hc
    rcases hc with hc | hc
    · exact hsqrtne hc
    · exact hup2nz hc
  have hdg : HasDerivAt (fun t => g4dDX3 x1 t x3 x4 x5 x6) (-x4 + x5 + x6) x2 := by
    have he : (fun t => g4dDX3 x1 t x3 x4 x5 x6)
        = fun t => (-x4 + x5 + x6) * t
          + (x1 * x4 - x1 * x5 + x1 * x6 - 2 * x3 * x6 + x4 * x6 + x5 * x6
            - x6 ^ 2) := by
      funext t; unfold g4dDX3; ring
    rw [he]
    have hv : (-x4 + x5 + x6) * 1 = -x4 + x5 + x6 := by ring
    exact HasDerivAt.congr_deriv
      (HasDerivAt.add_const (x1 * x4 - x1 * x5 + x1 * x6 - 2 * x3 * x6
        + x4 * x6 + x5 * x6 - x6 ^ 2)
        (HasDerivAt.const_mul (-x4 + x5 + x6) (hasDerivAt_id x2))) hv
  have hdiv : HasDerivAt (fun t => g4dDX3 x1 t x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6) * upsX x1 t x6))
      (((-x4 + x5 + x6) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x2 x6)
        - g4dDX3 x1 x2 x3 x4 x5 x6
          * ((4 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
                / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
              * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * x1 + 2 * x6 - 2 * x2)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x2 x6) ^ 2)) x2 :=
    hdg.div hD hDne
  have h2 := hdiv.const_mul (-2 * x1)
  rw [show (fun t => g4dDihX2 x1 t x3 x4 x5 x6)
      = fun t => -2 * x1 * (g4dDX3 x1 t x3 x4 x5 x6
          / (Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6) * upsX x1 t x6)) from by
        funext t; unfold g4dDihX2; ring]
  exact h2

/-- Second partial of `dihXf` w.r.t. `x3`: the first partial
`g4dDihX3 = -2*x1*g4dDX2/(sqrt(4*x1*deltaX) * upsX x1 x3 x5)` is
differentiable in `x3` (numerator affine in x3 with slope `-x4+x5+x6`,
`deltaX` affine in x3 with slope `g4dDX3`, `upsX x1 x3 x5` quadratic in x3
with slope `2*x1+2*x5-2*x3`), value = the quotient-rule form over
`(sqrt(4*x1*deltaX) * upsX x1 x3 x5)^2` in chain-native shape. -/
theorem dihXf_second_deriv_x3 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX3 x1 x2 t x4 x5 x6)
      (-2 * x1 * (((-x4 + x5 + x6)
            * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
          - g4dDX2 x1 x2 x3 x4 x5 x6
            * ((4 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
                  / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
                * upsX x1 x3 x5
              + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
                * (2 * x1 + 2 * x5 - 2 * x3)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x3 x5) ^ 2))) x3 := by
  have hupos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hsqrtne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hupos)
  have hprodp : 0 < deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  rw [g4d_ups_delta] at hprodp
  have hup3nz : upsX x1 x3 x5 ≠ 0 := by
    intro hc; rw [hc] at hprodp; simp at hprodp
  have hΔ3 : HasDerivAt (fun t => deltaX x1 x2 t x4 x5 x6)
      (g4dDX3 x1 x2 x3 x4 x5 x6) x3 :=
    g4d_hasDerivAt_deltaX_x3 x1 x2 x3 x4 x5 x6
  have hsq : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6))
      (4 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x3 :=
    (hΔ3.const_mul (4 * x1)).sqrt (by positivity)
  have hupsq : HasDerivAt (fun t => (-1) * (t * t)
      + ((2 * x1 + 2 * x5) * t + (2 * x1 * x5 - x1 * x1 - x5 * x5)))
      ((-1) * (x3 + x3) + (2 * x1 + 2 * x5)) x3 :=
    hasDerivAt_quad_s2a (-1) (2 * x1 + 2 * x5)
      (2 * x1 * x5 - x1 * x1 - x5 * x5) x3
  have hvu : (-1) * (x3 + x3) + (2 * x1 + 2 * x5)
      = 2 * x1 + 2 * x5 - 2 * x3 := by ring
  have hup : HasDerivAt (fun t => upsX x1 t x5) (2 * x1 + 2 * x5 - 2 * x3) x3 := by
    rw [show (fun t => upsX x1 t x5) = fun t => (-1) * (t * t)
        + ((2 * x1 + 2 * x5) * t + (2 * x1 * x5 - x1 * x1 - x5 * x5)) from by
          funext t; unfold upsX; ring]
    exact hupsq.congr_deriv hvu
  have hD : HasDerivAt (fun t => Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6)
        * upsX x1 t x5)
      (4 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
          / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
        + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (2 * x1 + 2 * x5 - 2 * x3)) x3 :=
    hsq.mul hup
  have hDne : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5 ≠ 0 := by
    intro hc
    rw [mul_eq_zero] at hc
    rcases hc with hc | hc
    · exact hsqrtne hc
    · exact hup3nz hc
  have hdg : HasDerivAt (fun t => g4dDX2 x1 x2 t x4 x5 x6) (-x4 + x5 + x6) x3 := by
    have he : (fun t => g4dDX2 x1 x2 t x4 x5 x6)
        = fun t => (-x4 + x5 + x6) * t
          + (x1 * x4 + x1 * x5 - x1 * x6 - 2 * x2 * x5 + x4 * x5 - x5 ^ 2
            + x5 * x6) := by
      funext t; unfold g4dDX2; ring
    rw [he]
    have hv : (-x4 + x5 + x6) * 1 = -x4 + x5 + x6 := by ring
    exact HasDerivAt.congr_deriv
      (HasDerivAt.add_const (x1 * x4 + x1 * x5 - x1 * x6 - 2 * x2 * x5
        + x4 * x5 - x5 ^ 2 + x5 * x6)
        (HasDerivAt.const_mul (-x4 + x5 + x6) (hasDerivAt_id x3))) hv
  have hdiv : HasDerivAt (fun t => g4dDX2 x1 x2 t x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6) * upsX x1 t x5))
      (((-x4 + x5 + x6) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x3 x5)
        - g4dDX2 x1 x2 x3 x4 x5 x6
          * ((4 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
                / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)))
              * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * x1 + 2 * x5 - 2 * x3)))
        / ((Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * upsX x1 x3 x5) ^ 2)) x3 :=
    hdg.div hD hDne
  have h2 := hdiv.const_mul (-2 * x1)
  rw [show (fun t => g4dDihX3 x1 x2 t x4 x5 x6)
      = fun t => -2 * x1 * (g4dDX2 x1 x2 t x4 x5 x6
          / (Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6) * upsX x1 t x5)) from by
        funext t; unfold g4dDihX3; ring]
  exact h2

/-! ## 3. The six instantiated y4-compositions

Slice variable = the tuple entry `z_j` where y4 sits; factor `4*z_j^2`. -/
/-- y4-composition, y4 in the x1 slot (tuple `(y4,·,·,·,·,·)`). -/
theorem dihYcomp_y4sec_slot1 (z1 z2 z3 z4 z5 z6 : ℝ) (hz1 : 0 < z1)
    (hd : 0 < deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
      (z6 * z6)) :
    HasDerivAt (fun t => 2 * t * g4dDihX1 (t * t) (z2 * z2) (z3 * z3)
          (z4 * z4) (z5 * z5) (z6 * z6))
      (2 * g4dDihX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
          (z6 * z6)
        + 4 * (z1 * z1) * (      ((((2 * ((-2 * (z1 * z1) + (z2 * z2) + (z3 * z3) - 2 * (z4 * z4) + (z5 * z5) + (z6 * z6)) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6)
            + deltaX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) * g4dDX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6)
          + (1 * (deltaX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) * g4dDX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
            + (z1 * z1) * ((-2 * (z1 * z1) + (z2 * z2) + (z3 * z3) - 2 * (z4 * z4) + (z5 * z5) + (z6 * z6))
              * g4dDX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6)
              + deltaX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) * (-2 * (z4 * z4))))
          - ((2 * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) + 2 * (z1 * z1) * g4dDX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
              * (-2 * (z1 * z1) + (z2 * z2) + (z3 * z3) - 2 * (z4 * z4) + (z5 * z5) + (z6 * z6))
            + 2 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) * (-2))))
        * (Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
          * (upsX (z1 * z1) (z2 * z2) (z6 * z6) * upsX (z1 * z1) (z3 * z3) (z5 * z5)))
      - 2 * (deltaX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6)
            + (z1 * z1) * (deltaX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) * g4dDX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
          - 2 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6)
            * (-2 * (z1 * z1) + (z2 * z2) + (z3 * z3) - 2 * (z4 * z4) + (z5 * z5) + (z6 * z6)))
        * ((4 * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6) + 4 * (z1 * z1) * g4dDX1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
            / (2 * Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6)))
          * (upsX (z1 * z1) (z2 * z2) (z6 * z6) * upsX (z1 * z1) (z3 * z3) (z5 * z5))
        + Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
          * ((2 * (z2 * z2) + 2 * (z6 * z6) - 2 * (z1 * z1)) * upsX (z1 * z1) (z3 * z3) (z5 * z5)
            + upsX (z1 * z1) (z2 * z2) (z6 * z6) * (2 * (z3 * z3) + 2 * (z5 * z5) - 2 * (z1 * z1)))))
      / ((Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
            * (upsX (z1 * z1) (z2 * z2) (z6 * z6) * upsX (z1 * z1) (z3 * z3) (z5 * z5))) ^ 2))))) z1 :=
  comp2_y4sec (dihXf_second_deriv_x1 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4)
    (z5 * z5) (z6 * z6) (mul_pos hz1 hz1) hd)

/-- y4-composition, y4 in the x2 slot (tuple `(·,y4,·,·,·,·)`). -/
theorem dihYcomp_y4sec_slot2 (z1 z2 z3 z4 z5 z6 : ℝ) (hz1 : 0 < z1)
    (hd : 0 < deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
      (z6 * z6)) :
    HasDerivAt (fun t => 2 * t * g4dDihX2 (z1 * z1) (t * t) (z3 * z3)
          (z4 * z4) (z5 * z5) (z6 * z6))
      (2 * g4dDihX2 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
          (z6 * z6)
        + 4 * (z2 * z2) * (-2 * (z1 * z1)
          * (((-(z4 * z4) + (z5 * z5) + (z6 * z6))
              * (Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z2 * z2) (z6 * z6))
            - g4dDX3 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
              (z6 * z6)
              * ((4 * (z1 * z1) * g4dDX2 (z1 * z1) (z2 * z2) (z3 * z3)
                    (z4 * z4) (z5 * z5) (z6 * z6)
                  / (2 * Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1)
                      (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))))
                * upsX (z1 * z1) (z2 * z2) (z6 * z6)
              + Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * (2 * (z1 * z1) + 2 * (z6 * z6) - 2 * (z2 * z2))))
            / ((Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z2 * z2) (z6 * z6)) ^ 2)))) z2 :=
  comp2_y4sec (dihXf_second_deriv_x2 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4)
    (z5 * z5) (z6 * z6) (mul_pos hz1 hz1) hd)

/-- y4-composition, y4 in the x3 slot (tuple `(·,·,y4,·,·,·)`). -/
theorem dihYcomp_y4sec_slot3 (z1 z2 z3 z4 z5 z6 : ℝ) (hz1 : 0 < z1)
    (hd : 0 < deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
      (z6 * z6)) :
    HasDerivAt (fun t => 2 * t * g4dDihX3 (z1 * z1) (z2 * z2) (t * t)
          (z4 * z4) (z5 * z5) (z6 * z6))
      (2 * g4dDihX3 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
          (z6 * z6)
        + 4 * (z3 * z3) * (-2 * (z1 * z1)
          * (((-(z4 * z4) + (z5 * z5) + (z6 * z6))
              * (Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z3 * z3) (z5 * z5))
            - g4dDX2 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
              (z6 * z6)
              * ((4 * (z1 * z1) * g4dDX3 (z1 * z1) (z2 * z2) (z3 * z3)
                    (z4 * z4) (z5 * z5) (z6 * z6)
                  / (2 * Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1)
                      (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))))
                * upsX (z1 * z1) (z3 * z3) (z5 * z5)
              + Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * (2 * (z1 * z1) + 2 * (z5 * z5) - 2 * (z3 * z3))))
            / ((Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z3 * z3) (z5 * z5)) ^ 2)))) z3 :=
  comp2_y4sec (dihXf_second_deriv_x3 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4)
    (z5 * z5) (z6 * z6) (mul_pos hz1 hz1) hd)

/-- y4-composition, y4 in the x4 slot (tuple `(·,·,·,y4,·,·)`; the top-level
`dihY y1..y6` and two solY tuples use this). -/
theorem dihYcomp_y4sec_slot4 (z1 z2 z3 z4 z5 z6 : ℝ) (hz1 : 0 < z1)
    (hd : 0 < deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
      (z6 * z6)) :
    HasDerivAt (fun t => 2 * t * g4dDihX4 (z1 * z1) (z2 * z2) (z3 * z3)
          (t * t) (z5 * z5) (z6 * z6))
      (2 * g4dDihX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
          (z6 * z6)
        + 4 * (z4 * z4) * (-(4 * (z1 * z1) * (z1 * z1)
              * deltaX4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
              (z6 * z6))
            / (Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
              * (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2) (z3 * z3)
                (z4 * z4) (z5 * z5) (z6 * z6))))) z4 :=
  comp2_y4sec (dihXf_second_deriv_x4 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4)
    (z5 * z5) (z6 * z6) (mul_pos hz1 hz1) hd)

/-- y4-composition, y4 in the x5 slot (tuple `(·,·,·,·,y4,·)`). -/
theorem dihYcomp_y4sec_slot5 (z1 z2 z3 z4 z5 z6 : ℝ) (hz1 : 0 < z1)
    (hd : 0 < deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
      (z6 * z6)) :
    HasDerivAt (fun t => 2 * t * g4dDihX5 (z1 * z1) (z2 * z2) (z3 * z3)
          (z4 * z4) (t * t) (z6 * z6))
      (2 * g4dDihX5 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
          (z6 * z6)
        + 4 * (z5 * z5) * (-2 * (z1 * z1)
          * (((z2 * z2 + z3 * z3 - z4 * z4)
              * (Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z3 * z3) (z5 * z5))
            - g4dDX6 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
              (z6 * z6)
              * ((4 * (z1 * z1) * deltaX5 (z1 * z1) (z2 * z2) (z3 * z3)
                    (z4 * z4) (z5 * z5) (z6 * z6)
                  / (2 * Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1)
                      (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))))
                * upsX (z1 * z1) (z3 * z3) (z5 * z5)
              + Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * (2 * (z1 * z1) + 2 * (z3 * z3) - 2 * (z5 * z5))))
            / ((Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z3 * z3) (z5 * z5)) ^ 2)))) z5 :=
  comp2_y4sec (dihXf_second_deriv_x5 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4)
    (z5 * z5) (z6 * z6) (mul_pos hz1 hz1) hd)

/-- y4-composition, y4 in the x6 slot (tuple `(·,·,·,·,·,y4)`). -/
theorem dihYcomp_y4sec_slot6 (z1 z2 z3 z4 z5 z6 : ℝ) (hz1 : 0 < z1)
    (hd : 0 < deltaX (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
      (z6 * z6)) :
    HasDerivAt (fun t => 2 * t * g4dDihX6 (z1 * z1) (z2 * z2) (z3 * z3)
          (z4 * z4) (z5 * z5) (t * t))
      (2 * g4dDihX6 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
          (z6 * z6)
        + 4 * (z6 * z6) * (-2 * (z1 * z1)
          * (((z2 * z2 + z3 * z3 - z4 * z4)
              * (Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z2 * z2) (z6 * z6))
            - deltaX5 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5)
              (z6 * z6)
              * ((4 * (z1 * z1) * g4dDX6 (z1 * z1) (z2 * z2) (z3 * z3)
                    (z4 * z4) (z5 * z5) (z6 * z6)
                  / (2 * Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1)
                      (z2 * z2) (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))))
                * upsX (z1 * z1) (z2 * z2) (z6 * z6)
              + Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * (2 * (z1 * z1) + 2 * (z2 * z2) - 2 * (z6 * z6))))
            / ((Real.sqrt (4 * (z1 * z1) * deltaX (z1 * z1) (z2 * z2)
                  (z3 * z3) (z4 * z4) (z5 * z5) (z6 * z6))
                * upsX (z1 * z1) (z2 * z2) (z6 * z6)) ^ 2)))) z6 :=
  comp2_y4sec (dihXf_second_deriv_x6 (z1 * z1) (z2 * z2) (z3 * z3) (z4 * z4)
    (z5 * z5) (z6 * z6) (mul_pos hz1 hz1) hd)

-- The volY twin is a one-line application of `comp2_y4sec` to
-- `volY_hasDerivAt2_y4`; omitted as a named corollary.


/-! ## 4. Mass constants: bump and lmfun -/

/-- `bump` is a quadratic; its first derivative. -/
theorem bump_hasDerivAt (h : ℝ) :
    HasDerivAt bump
      (-(0.01:ℝ) * (h - h0) / (hplus - h0) ^ 2) h := by
  rw [show bump = fun w : ℝ => (-0.005 / (hplus - h0) ^ 2) * (w * w)
        + ((0.01 * h0 / (hplus - h0) ^ 2) * w
          + (0.005 - 0.005 * h0 ^ 2 / (hplus - h0) ^ 2)) from by
        funext w; unfold bump; ring]
  have hv : (-0.005 / (hplus - h0) ^ 2) * (h + h)
      + (0.01 * h0 / (hplus - h0) ^ 2)
      = -(0.01:ℝ) * (h - h0) / (hplus - h0) ^ 2 := by
    field_simp
    ring
  exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a
    (-0.005 / (hplus - h0) ^ 2) (0.01 * h0 / (hplus - h0) ^ 2)
    (0.005 - 0.005 * h0 ^ 2 / (hplus - h0) ^ 2) h) hv

/-- `bump`'s second derivative is the constant `-0.01/(hplus-h0)^2`. -/
theorem bump_hasDerivAt2 (h : ℝ) :
    HasDerivAt (fun w : ℝ => -(0.01:ℝ) * (w - h0) / (hplus - h0) ^ 2)
      (-(0.01:ℝ) / (hplus - h0) ^ 2) h := by
  rw [show (fun w : ℝ => -(0.01:ℝ) * (w - h0) / (hplus - h0) ^ 2)
      = fun q : ℝ => (0:ℝ) * (q * q)
        + ((-(0.01:ℝ) / (hplus - h0) ^ 2) * q
          + (0.01 * h0 / (hplus - h0) ^ 2)) from by
        funext q; ring]
  have hv : 0 * (h + h) + (-(0.01:ℝ) / (hplus - h0) ^ 2)
      = -(0.01:ℝ) / (hplus - h0) ^ 2 := by ring
  exact HasDerivAt.congr_deriv (hasDerivAt_quad_s2a 0
    (-(0.01:ℝ) / (hplus - h0) ^ 2) (0.01 * h0 / (hplus - h0) ^ 2) h) hv

/-- `lmfun` vanishes identically on and above the kink `h0` (so on box5 the
y1/y4-slot vol4f `dihY`-terms are identically zero: `y1/2, y4/2 >= h0`). -/
theorem lmfun_eq_zero_of_ge {h : ℝ} (hh : h0 ≤ h) : lmfun h = 0 := by
  rcases lt_or_eq_of_le hh with hc | hc
  · unfold lmfun
    exact if_neg (not_le.mpr hc)
  · subst hc
    unfold lmfun
    rw [if_pos le_rfl]
    ring

/-! ### Axiom audit -/

#print axioms comp2_y4sec
#print axioms dihXf_second_deriv_x2
#print axioms dihXf_second_deriv_x3
#print axioms dihYcomp_y4sec_slot1
#print axioms dihYcomp_y4sec_slot2
#print axioms dihYcomp_y4sec_slot3
#print axioms dihYcomp_y4sec_slot4
#print axioms dihYcomp_y4sec_slot5
#print axioms dihYcomp_y4sec_slot6
#print axioms bump_hasDerivAt
#print axioms bump_hasDerivAt2
#print axioms lmfun_eq_zero_of_ge

end Kepler.Text
