/-
Kepler.Text.Gamma4DerivSecond — lane `g4-hessian-lean-w1` (2026-11-18):
the six diagonal second-order partials of `dihXf` in atan-free closed form
(Scout `g4-hessian-scout-w1` FORMULAS.md §1, with the lane's factor-2 ERRATA
on the Scout's lmfun weights — see the lane DELIVERY.md).

Each theorem has the raw quotient-rule shape
  `HasDerivAt (fun t => g4dDihX_i .. t ..) (RAW_i) x_i`
with `RAW_i` an explicit `√(4 x1 Δ)`-quotient (atan-free; no large
polynomial `def`s elaborated).  Consumed by the y1-slice chain (W2/W3)
and the B0 concavity certificate (lane W6, in flight).

Proof pattern: `g4s_quad_deriv` (every atom is affine/quadratic in the
slice variable) + the quotient rule + `change`-defeq + one closing `ring`.

No `sorry`/`axiom`/`admit`/`native_decide`; every declaration axiom-audited
below.
-/
import Kepler.Text.Gamma4Deriv3

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text

/-- Quadratic helper: `f t = a t^2 + b t + c` gives `f' x = 2 a x + b`.
Covers affine (a = 0) and constant cases. -/
theorem g4s_quad_deriv {f : ℝ → ℝ} {a b c x : ℝ}
    (h : ∀ t, f t = a * (t * t) + b * t + c) :
    HasDerivAt f (2 * a * x + b) x := by
  rw [show f = fun t : ℝ => a * (t * t) + b * t + c from funext h]
  have h2 : HasDerivAt (fun t : ℝ => a * (t * t) + (b * t + c)) (2 * a * x + b) x := by
    have hA : HasDerivAt (fun t : ℝ => a * (t * t)) (a * (1 * x + x * 1)) x := by
      simpa only [Pi.mul_apply, id_eq] using
        ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul a
    have hB : HasDerivAt (fun t : ℝ => b * t + c) (b * 1) x := by
      simpa using ((hasDerivAt_id x).const_mul b).add_const c
    have hC : HasDerivAt (fun t : ℝ => a * (t * t) + (b * t + c))
        (a * (1 * x + x * 1) + b * 1) x :=
      hA.add hB
    refine hC.congr_deriv ?_
    ring
  simpa only [add_assoc] using h2

noncomputable def g4sP44 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
    (2 : ℝ) * x1 * x4
      + x1 ^ 2
      + x2 * x3
      + x5 * x6
      + - x1 * x2
      + - x1 * x3
      + - x1 * x5
      + - x1 * x6
      + - x2 * x5
      + - x3 * x6

/-- `∂²dihXf/∂x4² = A * g4sP44 / (4 * Δ²)` with `A = √(4 x1 Δ)`. -/
theorem dihXf_hasDerivAt2_x4_x4 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) :
    HasDerivAt (fun t => g4dDihX4 x1 x2 x3 t x5 x6)
      (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * g4sP44 x1 x2 x3 x4 x5 x6
        / (4 * (deltaX x1 x2 x3 x4 x5 x6) ^ 2)) x4 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr hpos
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have hdA : HasDerivAt
      (fun t : ℝ => Real.sqrt (4 * x1 * deltaX x1 x2 x3 t x5 x6))
      (4 * x1 * deltaX4 x1 x2 x3 x4 x5 x6
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x4 := by
    have hu : HasDerivAt (fun t : ℝ => 4 * x1 * deltaX x1 x2 x3 t x5 x6)
        (4 * x1 * deltaX4 x1 x2 x3 x4 x5 x6) x4 := by
      have h1 : HasDerivAt (fun _ : ℝ => (4 * x1 : ℝ)) 0 x4 :=
        hasDerivAt_const x4 (4 * x1)
      have h2 := h1.mul (g4d_hasDerivAt_deltaX_x4 x1 x2 x3 x4 x5 x6)
      have he : ((fun _ : ℝ => (4 * x1 : ℝ)) * fun t => deltaX x1 x2 x3 t x5 x6)
          = fun t : ℝ => 4 * x1 * deltaX x1 x2 x3 t x5 x6 := by
        funext t; simp only [Pi.mul_apply]
      rw [he] at h2
      exact h2.congr_deriv (by ring)
    exact hu.sqrt (ne_of_gt hpos)
  have hnum : HasDerivAt (fun _ : ℝ => (2 * x1 : ℝ)) 0 x4 :=
    hasDerivAt_const x4 (2 * x1)
  have h := hnum.div hdA hA0
  refine h.congr_deriv ?_
  have hA2 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2
      = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := Real.sq_sqrt (le_of_lt hpos)
  have hA4 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 4
      = (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2 := by
    have e1 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 4
        = (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2) ^ 2 := by ring
    rw [e1, hA2]
  field_simp [hA0]
  rw [hA4]
  simp only [g4sP44, deltaX4]
  ring


theorem dihXf_hasDerivAt2_x1_x1 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hu126 : 0 < upsX x1 x2 x6) (hu135 : 0 < upsX x1 x3 x5) :
    HasDerivAt (fun t => g4dDihX1 t x2 x3 x4 x5 x6)
      ((2 * (-(-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
              + 2 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
              - x1 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * g4dDX1 x1 x2 x3 x4 x5 x6
              - 2 * x1 * x4 * deltaX4 x1 x2 x3 x4 x5 x6
              + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (upsX x1 x2 x6 * upsX x1 x3 x5))
        - 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
              + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
              - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
                * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
          * ((2 * (deltaX x1 x2 x3 x4 x5 x6
                + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
              * (upsX x1 x2 x6 * upsX x1 x3 x5)
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * (x2 + x6 - x1) * upsX x1 x3 x5
                + upsX x1 x2 x6 * 2 * (x3 + x5 - x1))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ^ 2) x1 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hpos
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have h1260 : upsX x1 x2 x6 ≠ 0 := ne_of_gt hu126
  have h1350 : upsX x1 x3 x5 ≠ 0 := ne_of_gt hu135
  have hU0 : upsX x1 x2 x6 * upsX x1 x3 x5 ≠ 0 := mul_ne_zero h1260 h1350
  have hD : HasDerivAt (fun t : ℝ => deltaX t x2 x3 x4 x5 x6)
      (g4dDX1 x1 x2 x3 x4 x5 x6) x1 := g4d3_hasDerivAt_deltaX_x1 x1 x2 x3 x4 x5 x6
  have hD1 : HasDerivAt (fun t : ℝ => g4dDX1 t x2 x3 x4 x5 x6) (-2 * x4) x1 := by
    refine (g4s_quad_deriv (a := 0) (b := -2 * x4)
      (c := x4 * (x2 + x3 - x4 + x5 + x6) + x2 * x5 + x3 * x6 - x3 * x5 - x2 * x6) ?_).congr_deriv ?_
    · intro t
      simp only [g4dDX1]
      ring
    · ring
  have hD4 : HasDerivAt (fun t : ℝ => deltaX4 t x2 x3 x4 x5 x6)
      (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) x1 := by
    refine (g4s_quad_deriv (a := -1) (b := x2 + x3 - 2 * x4 + x5 + x6)
      (c := -x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6) ?_).congr_deriv ?_
    · intro t
      simp only [deltaX4]
      ring
    · ring
  have hS : HasDerivAt (fun t : ℝ => -2 * t + x2 + x3 - 2 * x4 + x5 + x6) (-2) x1 := by
    refine (g4s_quad_deriv (a := 0) (b := -2) (c := x2 + x3 - 2 * x4 + x5 + x6) ?_).congr_deriv ?_
    · intro t
      ring
    · ring
  have h126 : HasDerivAt (fun t : ℝ => upsX t x2 x6) (2 * (x2 + x6 - x1)) x1 := by
    refine (g4s_quad_deriv (a := -1) (b := 2 * (x2 + x6)) (c := -x2 ^ 2 + 2 * x2 * x6 - x6 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [upsX]
      ring
    · ring
  have h135 : HasDerivAt (fun t : ℝ => upsX t x3 x5) (2 * (x3 + x5 - x1)) x1 := by
    refine (g4s_quad_deriv (a := -1) (b := 2 * (x3 + x5)) (c := -x3 ^ 2 + 2 * x3 * x5 - x5 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [upsX]
      ring
    · ring
  have hu : HasDerivAt (fun t : ℝ => 4 * t * deltaX t x2 x3 x4 x5 x6)
      (4 * (deltaX x1 x2 x3 x4 x5 x6 + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)) x1 := by
    have h1 : HasDerivAt (fun t : ℝ => 4 * t) 4 x1 := by
      simpa using (hasDerivAt_id x1).const_mul 4
    have hm := h1.mul hD
    have he : ((fun t : ℝ => 4 * t) * fun t => deltaX t x2 x3 x4 x5 x6)
        = fun t : ℝ => 4 * t * deltaX t x2 x3 x4 x5 x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hdA : HasDerivAt (fun t : ℝ => Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6))
      (4 * (deltaX x1 x2 x3 x4 x5 x6 + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
        / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x1 :=
    hu.sqrt (ne_of_gt hpos)
  have hA1 := hD4.mul hD
  have hid : HasDerivAt (fun t : ℝ => t) 1 x1 := hasDerivAt_id x1
  have hB1 := hid.mul hD1
  have hB2 := (hid.mul hD4).mul hD1
  have hC2 := ((hid.const_mul 2).mul hD).mul hS
  have hN := ((hA1.add hB2).sub hC2).const_mul 2
  have hden := hdA.mul (h126.mul h135)
  have h := hN.div hden (mul_ne_zero hA0 hU0)
  have h' := h
  change HasDerivAt (fun t : ℝ =>
      2 * (deltaX4 t x2 x3 x4 x5 x6 * deltaX t x2 x3 x4 x5 x6
            + t * deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6
            - 2 * t * deltaX t x2 x3 x4 x5 x6 * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6))
        / (Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6) * (upsX t x2 x6 * upsX t x3 x5))) _ x1 at h'
  change HasDerivAt (fun t : ℝ =>
      2 * (deltaX4 t x2 x3 x4 x5 x6 * deltaX t x2 x3 x4 x5 x6
            + t * deltaX4 t x2 x3 x4 x5 x6 * g4dDX1 t x2 x3 x4 x5 x6
            - 2 * t * deltaX t x2 x3 x4 x5 x6 * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6))
        / (Real.sqrt (4 * t * deltaX t x2 x3 x4 x5 x6) * (upsX t x2 x6 * upsX t x3 x5)))
    ((2 * (-(-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
              + 2 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
              - x1 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * g4dDX1 x1 x2 x3 x4 x5 x6
              - 2 * x1 * x4 * deltaX4 x1 x2 x3 x4 x5 x6
              + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (upsX x1 x2 x6 * upsX x1 x3 x5))
        - 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
              + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
              - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
                * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
          * ((2 * (deltaX x1 x2 x3 x4 x5 x6
                + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
              * (upsX x1 x2 x6 * upsX x1 x3 x5)
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * (x2 + x6 - x1) * upsX x1 x3 x5
                + upsX x1 x2 x6 * 2 * (x3 + x5 - x1))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ^ 2) x1
  refine h'.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring


theorem dihXf_hasDerivAt2_x2_x2 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu126 : 0 < upsX x1 x2 x6) :
    HasDerivAt (fun t => g4dDihX2 x1 t x3 x4 x5 x6)
      (((-2 * x1 * (-x4 + x5 + x6)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        - (-2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x6 - x2))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2) x2 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hpos
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have hu0 : upsX x1 x2 x6 ≠ 0 := ne_of_gt hu126
  have hD : HasDerivAt (fun t : ℝ => deltaX x1 t x3 x4 x5 x6) (g4dDX2 x1 x2 x3 x4 x5 x6) x2 :=
    g4d_hasDerivAt_deltaX_x2 x1 x2 x3 x4 x5 x6
  have hDn : HasDerivAt (fun t : ℝ => g4dDX3 x1 t x3 x4 x5 x6) (-x4 + x5 + x6) x2 := by
    refine (g4s_quad_deriv (a := 0) (b := -x4 + x5 + x6)
      (c := x1 * x4 - x1 * x5 + x1 * x6 - 2 * x3 * x6 + x4 * x6 + x5 * x6 - x6 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [g4dDX3]
      ring
    · ring
  have hu : HasDerivAt (fun t : ℝ => upsX x1 t x6) (2 * (x1 + x6 - x2)) x2 := by
    refine (g4s_quad_deriv (a := -1) (b := 2 * x1 + 2 * x6) (c := -x1 ^ 2 + 2 * x1 * x6 - x6 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [upsX]
      ring
    · ring
  have huA : HasDerivAt (fun t : ℝ => 4 * x1 * deltaX x1 t x3 x4 x5 x6)
      (4 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6) x2 := by
    have h1 : HasDerivAt (fun _ : ℝ => (4 * x1 : ℝ)) 0 x2 := hasDerivAt_const x2 (4 * x1)
    have hm := h1.mul hD
    have he : ((fun _ : ℝ => (4 * x1 : ℝ)) * fun t => deltaX x1 t x3 x4 x5 x6)
        = fun t : ℝ => 4 * x1 * deltaX x1 t x3 x4 x5 x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hdA : HasDerivAt (fun t : ℝ => Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6))
      (4 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x2 :=
    huA.sqrt (ne_of_gt hpos)
  have hnum : HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX3 x1 t x3 x4 x5 x6)
      (-2 * x1 * (-x4 + x5 + x6)) x2 := by
    have h1 : HasDerivAt (fun _ : ℝ => (-2 * x1 : ℝ)) 0 x2 := hasDerivAt_const x2 (-2 * x1)
    have hm := h1.mul hDn
    have he : ((fun _ : ℝ => (-2 * x1 : ℝ)) * fun t => g4dDX3 x1 t x3 x4 x5 x6)
        = fun t : ℝ => -2 * x1 * g4dDX3 x1 t x3 x4 x5 x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hden := hdA.mul hu
  have h := hnum.div hden (mul_ne_zero hA0 hu0)
  have h' := h
  change HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX3 x1 t x3 x4 x5 x6 / (Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6) * upsX x1 t x6)) _ x2 at h'
  change HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX3 x1 t x3 x4 x5 x6 / (Real.sqrt (4 * x1 * deltaX x1 t x3 x4 x5 x6) * upsX x1 t x6))
    (((-2 * x1 * (-x4 + x5 + x6)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        - (-2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x6 - x2))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2) x2
  refine h'.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring



theorem dihXf_hasDerivAt2_x3_x3 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu135 : 0 < upsX x1 x3 x5) :
    HasDerivAt (fun t => g4dDihX3 x1 x2 t x4 x5 x6)
      (((-2 * x1 * (-x4 + x5 + x6)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        - (-2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x5 - x3))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2) x3 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hpos
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have hu0 : upsX x1 x3 x5 ≠ 0 := ne_of_gt hu135
  have hD : HasDerivAt (fun t : ℝ => deltaX x1 x2 t x4 x5 x6) (g4dDX3 x1 x2 x3 x4 x5 x6) x3 :=
    g4d_hasDerivAt_deltaX_x3 x1 x2 x3 x4 x5 x6
  have hDn : HasDerivAt (fun t : ℝ => g4dDX2 x1 x2 t x4 x5 x6) (-x4 + x5 + x6) x3 := by
    refine (g4s_quad_deriv (a := 0) (b := -x4 + x5 + x6)
      (c := x1 * x4 + x1 * x5 - x1 * x6 - 2 * x2 * x5 + x4 * x5 - x5 ^ 2 + x5 * x6) ?_).congr_deriv ?_
    · intro t
      simp only [g4dDX2]
      ring
    · ring
  have hu : HasDerivAt (fun t : ℝ => upsX x1 t x5) (2 * (x1 + x5 - x3)) x3 := by
    refine (g4s_quad_deriv (a := -1) (b := 2 * x1 + 2 * x5) (c := -x1 ^ 2 + 2 * x1 * x5 - x5 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [upsX]
      ring
    · ring
  have huA : HasDerivAt (fun t : ℝ => 4 * x1 * deltaX x1 x2 t x4 x5 x6)
      (4 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6) x3 := by
    have h1 : HasDerivAt (fun _ : ℝ => (4 * x1 : ℝ)) 0 x3 := hasDerivAt_const x3 (4 * x1)
    have hm := h1.mul hD
    have he : ((fun _ : ℝ => (4 * x1 : ℝ)) * fun t => deltaX x1 x2 t x4 x5 x6)
        = fun t : ℝ => 4 * x1 * deltaX x1 x2 t x4 x5 x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hdA : HasDerivAt (fun t : ℝ => Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6))
      (4 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x3 :=
    huA.sqrt (ne_of_gt hpos)
  have hnum : HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX2 x1 x2 t x4 x5 x6)
      (-2 * x1 * (-x4 + x5 + x6)) x3 := by
    have h1 : HasDerivAt (fun _ : ℝ => (-2 * x1 : ℝ)) 0 x3 := hasDerivAt_const x3 (-2 * x1)
    have hm := h1.mul hDn
    have he : ((fun _ : ℝ => (-2 * x1 : ℝ)) * fun t => g4dDX2 x1 x2 t x4 x5 x6)
        = fun t : ℝ => -2 * x1 * g4dDX2 x1 x2 t x4 x5 x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hden := hdA.mul hu
  have h := hnum.div hden (mul_ne_zero hA0 hu0)
  have h' := h
  change HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX2 x1 x2 t x4 x5 x6 / (Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6) * upsX x1 t x5)) _ x3 at h'
  change HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX2 x1 x2 t x4 x5 x6 / (Real.sqrt (4 * x1 * deltaX x1 x2 t x4 x5 x6) * upsX x1 t x5))
    (((-2 * x1 * (-x4 + x5 + x6)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        - (-2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x5 - x3))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2) x3
  refine h'.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring



theorem dihXf_hasDerivAt2_x5_x5 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu135 : 0 < upsX x1 x3 x5) :
    HasDerivAt (fun t => g4dDihX5 x1 x2 x3 x4 t x6)
      (((-2 * x1 * (x2 + x3 - x4)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        - (-2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6) * ((2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x3 - x5))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2) x5 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hpos
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have hu0 : upsX x1 x3 x5 ≠ 0 := ne_of_gt hu135
  have hD : HasDerivAt (fun t : ℝ => deltaX x1 x2 x3 x4 t x6) (deltaX5 x1 x2 x3 x4 x5 x6) x5 :=
    g4d_hasDerivAt_deltaX_x5 x1 x2 x3 x4 x5 x6
  have hDn : HasDerivAt (fun t : ℝ => g4dDX6 x1 x2 x3 x4 t x6) (x2 + x3 - x4) x5 := by
    refine (g4s_quad_deriv (a := 0) (b := x2 + x3 - x4)
      (c := -x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 - x3 ^ 2 + x3 * x4 - 2 * x3 * x6) ?_).congr_deriv ?_
    · intro t
      simp only [g4dDX6]
      ring
    · ring
  have hu : HasDerivAt (fun t : ℝ => upsX x1 x3 t) (2 * (x1 + x3 - x5)) x5 := by
    refine (g4s_quad_deriv (a := -1) (b := 2 * x1 + 2 * x3) (c := -x1 ^ 2 + 2 * x1 * x3 - x3 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [upsX]
      ring
    · ring
  have huA : HasDerivAt (fun t : ℝ => 4 * x1 * deltaX x1 x2 x3 x4 t x6)
      (4 * x1 * deltaX5 x1 x2 x3 x4 x5 x6) x5 := by
    have h1 : HasDerivAt (fun _ : ℝ => (4 * x1 : ℝ)) 0 x5 := hasDerivAt_const x5 (4 * x1)
    have hm := h1.mul hD
    have he : ((fun _ : ℝ => (4 * x1 : ℝ)) * fun t => deltaX x1 x2 x3 x4 t x6)
        = fun t : ℝ => 4 * x1 * deltaX x1 x2 x3 x4 t x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hdA : HasDerivAt (fun t : ℝ => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6))
      (4 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x5 :=
    huA.sqrt (ne_of_gt hpos)
  have hnum : HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX6 x1 x2 x3 x4 t x6)
      (-2 * x1 * (x2 + x3 - x4)) x5 := by
    have h1 : HasDerivAt (fun _ : ℝ => (-2 * x1 : ℝ)) 0 x5 := hasDerivAt_const x5 (-2 * x1)
    have hm := h1.mul hDn
    have he : ((fun _ : ℝ => (-2 * x1 : ℝ)) * fun t => g4dDX6 x1 x2 x3 x4 t x6)
        = fun t : ℝ => -2 * x1 * g4dDX6 x1 x2 x3 x4 t x6 := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hden := hdA.mul hu
  have h := hnum.div hden (mul_ne_zero hA0 hu0)
  have h' := h
  change HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX6 x1 x2 x3 x4 t x6 / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6) * upsX x1 x3 t)) _ x5 at h'
  change HasDerivAt (fun t : ℝ => -2 * x1 * g4dDX6 x1 x2 x3 x4 t x6 / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 t x6) * upsX x1 x3 t))
    (((-2 * x1 * (x2 + x3 - x4)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        - (-2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6) * ((2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x3 - x5))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2) x5
  refine h'.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring



theorem dihXf_hasDerivAt2_x6_x6 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu126 : 0 < upsX x1 x2 x6) :
    HasDerivAt (fun t => g4dDihX6 x1 x2 x3 x4 x5 t)
      (((-2 * x1 * (x2 + x3 - x4)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        - (-2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x2 - x6))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2) x6 := by
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hpos
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 := ne_of_gt hA
  have hu0 : upsX x1 x2 x6 ≠ 0 := ne_of_gt hu126
  have hD : HasDerivAt (fun t : ℝ => deltaX x1 x2 x3 x4 x5 t) (g4dDX6 x1 x2 x3 x4 x5 x6) x6 :=
    g4d_hasDerivAt_deltaX_x6 x1 x2 x3 x4 x5 x6
  have hDn : HasDerivAt (fun t : ℝ => deltaX5 x1 x2 x3 x4 x5 t) (x2 + x3 - x4) x6 := by
    refine (g4s_quad_deriv (a := 0) (b := x2 + x3 - x4)
      (c := x1 * x2 - x1 * x3 + x1 * x4 - x2 ^ 2 + x2 * x3 + x2 * x4 - 2 * x2 * x5) ?_).congr_deriv ?_
    · intro t
      simp only [deltaX5]
      ring
    · ring
  have hu : HasDerivAt (fun t : ℝ => upsX x1 x2 t) (2 * (x1 + x2 - x6)) x6 := by
    refine (g4s_quad_deriv (a := -1) (b := 2 * x1 + 2 * x2) (c := -x1 ^ 2 + 2 * x1 * x2 - x2 ^ 2) ?_).congr_deriv ?_
    · intro t
      simp only [upsX]
      ring
    · ring
  have huA : HasDerivAt (fun t : ℝ => 4 * x1 * deltaX x1 x2 x3 x4 x5 t)
      (4 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6) x6 := by
    have h1 : HasDerivAt (fun _ : ℝ => (4 * x1 : ℝ)) 0 x6 := hasDerivAt_const x6 (4 * x1)
    have hm := h1.mul hD
    have he : ((fun _ : ℝ => (4 * x1 : ℝ)) * fun t => deltaX x1 x2 x3 x4 x5 t)
        = fun t : ℝ => 4 * x1 * deltaX x1 x2 x3 x4 x5 t := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hdA : HasDerivAt (fun t : ℝ => Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t))
      (4 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 / (2 * Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))) x6 :=
    huA.sqrt (ne_of_gt hpos)
  have hnum : HasDerivAt (fun t : ℝ => -2 * x1 * deltaX5 x1 x2 x3 x4 x5 t)
      (-2 * x1 * (x2 + x3 - x4)) x6 := by
    have h1 : HasDerivAt (fun _ : ℝ => (-2 * x1 : ℝ)) 0 x6 := hasDerivAt_const x6 (-2 * x1)
    have hm := h1.mul hDn
    have he : ((fun _ : ℝ => (-2 * x1 : ℝ)) * fun t => deltaX5 x1 x2 x3 x4 x5 t)
        = fun t : ℝ => -2 * x1 * deltaX5 x1 x2 x3 x4 x5 t := by
      funext t; simp only [Pi.mul_apply]
    rw [he] at hm
    exact hm.congr_deriv (by ring)
  have hden := hdA.mul hu
  have h := hnum.div hden (mul_ne_zero hA0 hu0)
  have h' := h
  change HasDerivAt (fun t : ℝ => -2 * x1 * deltaX5 x1 x2 x3 x4 x5 t / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t) * upsX x1 x2 t)) _ x6 at h'
  change HasDerivAt (fun t : ℝ => -2 * x1 * deltaX5 x1 x2 x3 x4 x5 t / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 t) * upsX x1 x2 t))
    (((-2 * x1 * (x2 + x3 - x4)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        - (-2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x2 - x6))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2) x6
  refine h'.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
  ring

/-! ## Axiom audit -/
#print axioms g4s_quad_deriv
#print axioms dihXf_hasDerivAt2_x1_x1
#print axioms dihXf_hasDerivAt2_x2_x2
#print axioms dihXf_hasDerivAt2_x3_x3
#print axioms dihXf_hasDerivAt2_x4_x4
#print axioms dihXf_hasDerivAt2_x5_x5
#print axioms dihXf_hasDerivAt2_x6_x6

end Kepler.Text
