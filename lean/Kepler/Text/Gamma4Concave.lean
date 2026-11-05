/-
Kepler.Text.Gamma4Concave — lane `gamma4-w6`: the provable core of the
second-derivative kit for `gamma4fgcy` on the wide box
`[2·hminus, 2·hplus] × [2, √8]⁵`.

**Scope (honest).**  The work order asks for `∂²gamma4fgcy/∂yᵢ² ≤ 0` on each
kink piece of all six axes.  This file does **not** prove that; `DELIVERY.md`
records the measured reason (the second derivative cancels two O(3) summands
down to O(0.03), so it is a branch-and-bound certificate target, not an
`nlinarith` target).  What is proved here is the part that is both provable
and on the critical path of any concavity route:

1. **`lmfun (y/2)` kink at derivative level** (`y = 2·h0 = 2.52`): the
   derivative is the constant `−1/0.52` on `y < 2.52` and `0` on `2.52 < y`,
   and the second derivative is `0` on each piece.  (`Kepler.NliBanks9` has
   the *value*-level twins `lmfun_div_two_kink_left/right`.)
2. **`volY` second derivative in all six slots.**  `volY y = √Δ/12` with
   `Δ = deltaX (yᵢ²)`, a quartic in each `yᵢ` with no odd powers.  Writing
   `xᵢ = yᵢ²`, `Δᵢ = ∂Δ/∂xᵢ`, `Δᵢᵢ = ∂²Δ/∂xᵢ² = −2x_{π(i)}`, the exact value is
   ```
   ∂²volY/∂yᵢ² = ((Δᵢ − 4·xᵢ·x_{π(i)})·Δ − xᵢ·Δᵢ²) / (12·(√Δ)³)
   ```
   with the partner map `π = (1 4)(2 5)(3 6)`.  This is the only summand of
   `∂²gamma4fgcy/∂yᵢ²` that is transcendental-free, so its sign is a
   **polynomial** question (the `dihXf` second-partial kit is *not* here).

No `sorry`/`axiom`/`admit`/`native_decide`; every theorem audited at the end.
-/
import Kepler.Text.Gamma4Deriv8
import Kepler.Text.Gamma4Env

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## 1. `lmfun (y/2)` at derivative level, split at `y = 2·h0 = 2.52` -/

theorem g4c_two_h0 : 2 * h0 = 2.52 := by
  rw [show h0 = 1.26 from rfl]; norm_num

theorem g4c_two_h0_sub_one : 2 * (h0 - 1) = 0.52 := by
  rw [show h0 = 1.26 from rfl]; norm_num

/-- Below the kink the derivative of `y ↦ lmfun (y/2)` is the constant
`−1/0.52`. -/
theorem lmfun_div_two_deriv_left {y : ℝ} (hy : y < 2.52) :
    deriv (fun z : ℝ => lmfun (z / 2)) y = -1 / 0.52 := by
  have hy2 : y / 2 < h0 := by
    rw [show h0 = 1.26 from rfl] at *; linarith
  have hd : HasDerivAt (fun z : ℝ => lmfun (z / 2)) ((-1 / (h0 - 1)) * (1 / 2)) y :=
    g4d_hasDerivAt_lmfun_div2 (g4d_lmfun_hasDerivAt_of_lt hy2)
  rw [hd.deriv, show h0 = 1.26 from rfl]
  norm_num

/-- Above the kink the derivative of `y ↦ lmfun (y/2)` is `0`. -/
theorem lmfun_div_two_deriv_right {y : ℝ} (hy : 2.52 < y) :
    deriv (fun z : ℝ => lmfun (z / 2)) y = 0 := by
  have hy2 : h0 < y / 2 := by
    rw [show h0 = 1.26 from rfl] at *; linarith
  have hd : HasDerivAt (fun z : ℝ => lmfun (z / 2)) (0 * (1 / 2)) y :=
    g4d_hasDerivAt_lmfun_div2 (g4d_lmfun_hasDerivAt_of_gt hy2)
  rw [hd.deriv]; ring

/-- On the left piece the first derivative is locally constant, so the second
derivative vanishes. -/
theorem lmfun_div_two_iteratedDeriv_two_left {y : ℝ} (hy : y < 2.52) :
    iteratedDeriv 2 (fun z : ℝ => lmfun (z / 2)) y = 0 := by
  have hev : deriv (fun z : ℝ => lmfun (z / 2)) =ᶠ[𝓝 y] (fun _ => -1 / 0.52) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with z hz
    exact lmfun_div_two_deriv_left hz
  have h2 : iteratedDeriv 2 (fun z : ℝ => lmfun (z / 2))
      = deriv (deriv (fun z : ℝ => lmfun (z / 2))) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, hev.deriv_eq, deriv_const]

/-- Right-piece twin of `lmfun_div_two_iteratedDeriv_two_left`. -/
theorem lmfun_div_two_iteratedDeriv_two_right {y : ℝ} (hy : 2.52 < y) :
    iteratedDeriv 2 (fun z : ℝ => lmfun (z / 2)) y = 0 := by
  have hev : deriv (fun z : ℝ => lmfun (z / 2)) =ᶠ[𝓝 y] (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact lmfun_div_two_deriv_right hz
  have h2 : iteratedDeriv 2 (fun z : ℝ => lmfun (z / 2))
      = deriv (deriv (fun z : ℝ => lmfun (z / 2))) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, hev.deriv_eq, deriv_const]

/-! ## 2. The generic `√(quartic)` second-derivative lemma -/

/-- If `Q` is the radicand (`Q = Δ` as a function of one `yᵢ`), `D = Q′/2t`
is the corresponding `Δᵢ`, and `Δᵢᵢ` is the second `xᵢ`-partial of `Δ`, then
`t ↦ t·D t / (12·√(Q t))` has the second derivative below. -/
theorem g4c_volY2_generic {D Q : ℝ → ℝ} {D' Q' t0 Δii : ℝ}
    (hD : HasDerivAt D D' t0) (hQ : HasDerivAt Q Q' t0) (hQpos : 0 < Q t0)
    (hD' : D' = 2 * t0 * Δii) (hQ' : Q' = 2 * t0 * D t0) :
    HasDerivAt (fun t => t * D t / (12 * Real.sqrt (Q t)))
      (((D t0 + 2 * t0 ^ 2 * Δii) * Q t0 - t0 ^ 2 * (D t0) ^ 2)
        / (12 * (Real.sqrt (Q t0)) ^ 3)) t0 := by
  have hsqne : Real.sqrt (Q t0) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQpos)
  have hsq2 : (Real.sqrt (Q t0)) ^ 2 = Q t0 := Real.sq_sqrt (le_of_lt hQpos)
  have hsq : HasDerivAt (fun t => Real.sqrt (Q t)) (Q' / (2 * Real.sqrt (Q t0))) t0 :=
    hQ.sqrt (ne_of_gt hQpos)
  have hden : HasDerivAt (fun t => 12 * Real.sqrt (Q t))
      (12 * (Q' / (2 * Real.sqrt (Q t0)))) t0 :=
    hsq.const_mul 12
  have hnum : HasDerivAt (fun t => t * D t) (D t0 + t0 * D') t0 := by
    have h := (hasDerivAt_id t0).mul hD
    have hfun2 : (id * D) = fun t => t * D t := by funext t; simp
    rw [← hfun2]
    simpa using h
  have hq := hnum.div hden (mul_ne_zero (by norm_num) hsqne)
  refine hq.congr_deriv ?_
  rw [hD', hQ']
  have h3 : (Real.sqrt (Q t0)) ^ 3 = Q t0 * Real.sqrt (Q t0) := by
    have h4 : (Real.sqrt (Q t0)) ^ 3 = (Real.sqrt (Q t0)) ^ 2 * Real.sqrt (Q t0) := by ring
    rw [h4, hsq2]
  rw [h3]
  field_simp
  rw [hsq2]
  ring

/-! ## 3. `volY` second derivative in the six slots

Partner map `π = (1 4)(2 5)(3 6)`; `Δᵢᵢ = −2·x_{π(i)}`, so
`Δᵢ + 2yᵢ²Δᵢᵢ = Δᵢ − 4·xᵢ·x_{π(i)}`. -/

/-- Slot 1 (`Δᵢ = g4dDX1`, partner `x₄`). -/
theorem volY_hasDerivAt2_y1 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDVolY1 t y2 y3 y4 y5 y6)
      (((g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y1 * y1) * (y4 * y4)) * deltaY y1 y2 y3 y4 y5 y6
        - (y1 * y1) * (g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) y1 := by
  have hD : HasDerivAt (fun t : ℝ => g4dDX1 (t * t) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)) ((-2 * (y4 * y4)) * (2 * y1)) y1 := by
    have hlin : HasDerivAt (fun s : ℝ => g4dDX1 s (y2 * y2) (y3 * y3) (y4 * y4)
        (y5 * y5) (y6 * y6)) (-2 * (y4 * y4)) (y1 * y1) := by
      have hfun : (fun s : ℝ => g4dDX1 s (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
          = fun s => (-2 * (y4 * y4)) * s + g4dDX1 0 (y2 * y2) (y3 * y3) (y4 * y4)
              (y5 * y5) (y6 * y6) := by
        funext s; simp only [g4dDX1]; ring
      rw [hfun]
      have h := ((hasDerivAt_id (y1 * y1)).const_mul (-2 * (y4 * y4))).add_const
        (g4dDX1 0 (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
      simpa using h
    exact g4d_hasDerivAt_sq_comp hlin
  have hQ : HasDerivAt (fun t : ℝ => deltaY t y2 y3 y4 y5 y6)
      (g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 * y1)) y1 := by
    have := g4d_hasDerivAt_sq_comp
      (g4d3_hasDerivAt_deltaX_x1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    simpa only [deltaY] using this
  have hgen := g4c_volY2_generic (D := fun t : ℝ => g4dDX1 (t * t) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6)) (Q := fun t : ℝ => deltaY t y2 y3 y4 y5 y6)
      (Δii := -2 * (y4 * y4)) hD hQ hd (by ring) (by ring)
  have hfun : (fun t : ℝ => t * g4dDX1 (t * t) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6) / (12 * Real.sqrt (deltaY t y2 y3 y4 y5 y6)))
      = fun t => g4dDVolY1 t y2 y3 y4 y5 y6 := by
    funext t; simp only [g4dDVolY1, deltaY]
  rw [hfun] at hgen
  have hval : (((g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        + 2 * y1 ^ 2 * (-2 * (y4 * y4))) * deltaY y1 y2 y3 y4 y5 y6
      - y1 ^ 2 * (g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2)
      / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))
      = (((g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y1 * y1) * (y4 * y4)) * deltaY y1 y2 y3 y4 y5 y6
        - (y1 * y1) * (g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) := by
    ring
  rw [hval] at hgen
  exact hgen

/-- Helper: a function affine in `xᵢ` composed with `t ↦ t²`. -/
theorem g4c_hasDerivAt_lin_sq (c K x : ℝ) :
    HasDerivAt (fun t : ℝ => c * (t * t) + K) (c * (2 * x)) x := by
  have hlin : HasDerivAt (fun s : ℝ => c * s + K) c (x * x) := by
    simpa using ((hasDerivAt_id (x * x)).const_mul c).add_const K
  exact g4d_hasDerivAt_sq_comp hlin

/-- Slot 2 (`Δᵢ = g4dDX2`, partner `x₅`). -/
theorem volY_hasDerivAt2_y2 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDVolY2 y1 t y3 y4 y5 y6)
      (((g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y2 * y2) * (y5 * y5)) * deltaY y1 y2 y3 y4 y5 y6
        - (y2 * y2) * (g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) y2 := by
  have hD : HasDerivAt (fun t : ℝ => g4dDX2 (y1 * y1) (t * t) (y3 * y3) (y4 * y4)
      (y5 * y5) (y6 * y6)) ((-2 * (y5 * y5)) * (2 * y2)) y2 := by
    have hfun : (fun t : ℝ => g4dDX2 (y1 * y1) (t * t) (y3 * y3) (y4 * y4) (y5 * y5)
        (y6 * y6))
        = fun t => (-2 * (y5 * y5)) * (t * t) + g4dDX2 (y1 * y1) 0 (y3 * y3) (y4 * y4)
            (y5 * y5) (y6 * y6) := by
      funext t; simp only [g4dDX2]; ring
    rw [hfun]
    exact g4c_hasDerivAt_lin_sq _ _ _
  have hQ : HasDerivAt (fun t : ℝ => deltaY y1 t y3 y4 y5 y6)
      (g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 * y2)) y2 := by
    have := g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    simpa only [deltaY] using this
  have hgen := g4c_volY2_generic (D := fun t : ℝ => g4dDX2 (y1 * y1) (t * t) (y3 * y3)
      (y4 * y4) (y5 * y5) (y6 * y6)) (Q := fun t : ℝ => deltaY y1 t y3 y4 y5 y6)
      (Δii := -2 * (y5 * y5)) hD hQ hd (by ring) (by ring)
  have hfun : (fun t : ℝ => t * g4dDX2 (y1 * y1) (t * t) (y3 * y3) (y4 * y4) (y5 * y5)
      (y6 * y6) / (12 * Real.sqrt (deltaY y1 t y3 y4 y5 y6)))
      = fun t => g4dDVolY2 y1 t y3 y4 y5 y6 := by
    funext t; simp only [g4dDVolY2, deltaY]
  rw [hfun] at hgen
  have hval : (((g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        + 2 * y2 ^ 2 * (-2 * (y5 * y5))) * deltaY y1 y2 y3 y4 y5 y6
      - y2 ^ 2 * (g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2)
      / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))
      = (((g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y2 * y2) * (y5 * y5)) * deltaY y1 y2 y3 y4 y5 y6
        - (y2 * y2) * (g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) := by
    ring
  rw [hval] at hgen
  exact hgen

/-- Slot 3 (`Δᵢ = g4dDX3`, partner `x₆`). -/
theorem volY_hasDerivAt2_y3 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDVolY3 y1 y2 t y4 y5 y6)
      (((g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y3 * y3) * (y6 * y6)) * deltaY y1 y2 y3 y4 y5 y6
        - (y3 * y3) * (g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) y3 := by
  have hD : HasDerivAt (fun t : ℝ => g4dDX3 (y1 * y1) (y2 * y2) (t * t) (y4 * y4)
      (y5 * y5) (y6 * y6)) ((-2 * (y6 * y6)) * (2 * y3)) y3 := by
    have hfun : (fun t : ℝ => g4dDX3 (y1 * y1) (y2 * y2) (t * t) (y4 * y4) (y5 * y5)
        (y6 * y6))
        = fun t => (-2 * (y6 * y6)) * (t * t) + g4dDX3 (y1 * y1) (y2 * y2) 0 (y4 * y4)
            (y5 * y5) (y6 * y6) := by
      funext t; simp only [g4dDX3]; ring
    rw [hfun]
    exact g4c_hasDerivAt_lin_sq _ _ _
  have hQ : HasDerivAt (fun t : ℝ => deltaY y1 y2 t y4 y5 y6)
      (g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 * y3)) y3 := by
    have := g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    simpa only [deltaY] using this
  have hgen := g4c_volY2_generic (D := fun t : ℝ => g4dDX3 (y1 * y1) (y2 * y2) (t * t)
      (y4 * y4) (y5 * y5) (y6 * y6)) (Q := fun t : ℝ => deltaY y1 y2 t y4 y5 y6)
      (Δii := -2 * (y6 * y6)) hD hQ hd (by ring) (by ring)
  have hfun : (fun t : ℝ => t * g4dDX3 (y1 * y1) (y2 * y2) (t * t) (y4 * y4) (y5 * y5)
      (y6 * y6) / (12 * Real.sqrt (deltaY y1 y2 t y4 y5 y6)))
      = fun t => g4dDVolY3 y1 y2 t y4 y5 y6 := by
    funext t; simp only [g4dDVolY3, deltaY]
  rw [hfun] at hgen
  have hval : (((g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        + 2 * y3 ^ 2 * (-2 * (y6 * y6))) * deltaY y1 y2 y3 y4 y5 y6
      - y3 ^ 2 * (g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2)
      / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))
      = (((g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y3 * y3) * (y6 * y6)) * deltaY y1 y2 y3 y4 y5 y6
        - (y3 * y3) * (g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) := by
    ring
  rw [hval] at hgen
  exact hgen

/-- Slot 4 (`Δᵢ = deltaX4`, partner `x₁`). -/
theorem volY_hasDerivAt2_y4 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDVolY4 y1 y2 y3 t y5 y6)
      (((deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y4 * y4) * (y1 * y1)) * deltaY y1 y2 y3 y4 y5 y6
        - (y4 * y4) * (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) y4 := by
  have hD : HasDerivAt (fun t : ℝ => deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (t * t)
      (y5 * y5) (y6 * y6)) ((-2 * (y1 * y1)) * (2 * y4)) y4 := by
    have hfun : (fun t : ℝ => deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (t * t) (y5 * y5)
        (y6 * y6))
        = fun t => (-2 * (y1 * y1)) * (t * t) + deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) 0
            (y5 * y5) (y6 * y6) := by
      funext t; simp only [deltaX4]; ring
    rw [hfun]
    exact g4c_hasDerivAt_lin_sq _ _ _
  have hQ : HasDerivAt (fun t : ℝ => deltaY y1 y2 y3 t y5 y6)
      (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 * y4)) y4 := by
    have := g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    simpa only [deltaY] using this
  have hgen := g4c_volY2_generic (D := fun t : ℝ => deltaX4 (y1 * y1) (y2 * y2) (y3 * y3)
      (t * t) (y5 * y5) (y6 * y6)) (Q := fun t : ℝ => deltaY y1 y2 y3 t y5 y6)
      (Δii := -2 * (y1 * y1)) hD hQ hd (by ring) (by ring)
  have hfun : (fun t : ℝ => t * deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (t * t) (y5 * y5)
      (y6 * y6) / (12 * Real.sqrt (deltaY y1 y2 y3 t y5 y6)))
      = fun t => g4dDVolY4 y1 y2 y3 t y5 y6 := by
    funext t; simp only [g4dDVolY4, deltaY]
  rw [hfun] at hgen
  have hval : (((deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        + 2 * y4 ^ 2 * (-2 * (y1 * y1))) * deltaY y1 y2 y3 y4 y5 y6
      - y4 ^ 2 * (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2)
      / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))
      = (((deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y4 * y4) * (y1 * y1)) * deltaY y1 y2 y3 y4 y5 y6
        - (y4 * y4) * (deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) := by
    ring
  rw [hval] at hgen
  exact hgen

/-- Slot 5 (`Δᵢ = deltaX5`, partner `x₂`). -/
theorem volY_hasDerivAt2_y5 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDVolY5 y1 y2 y3 y4 t y6)
      (((deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y5 * y5) * (y2 * y2)) * deltaY y1 y2 y3 y4 y5 y6
        - (y5 * y5) * (deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) y5 := by
  have hD : HasDerivAt (fun t : ℝ => deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (t * t) (y6 * y6)) ((-2 * (y2 * y2)) * (2 * y5)) y5 := by
    have hfun : (fun t : ℝ => deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (t * t)
        (y6 * y6))
        = fun t => (-2 * (y2 * y2)) * (t * t) + deltaX5 (y1 * y1) (y2 * y2) (y3 * y3)
            (y4 * y4) 0 (y6 * y6) := by
      funext t; simp only [deltaX5]; ring
    rw [hfun]
    exact g4c_hasDerivAt_lin_sq _ _ _
  have hQ : HasDerivAt (fun t : ℝ => deltaY y1 y2 y3 y4 t y6)
      (deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 * y5)) y5 := by
    have := g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    simpa only [deltaY] using this
  have hgen := g4c_volY2_generic (D := fun t : ℝ => deltaX5 (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (t * t) (y6 * y6)) (Q := fun t : ℝ => deltaY y1 y2 y3 y4 t y6)
      (Δii := -2 * (y2 * y2)) hD hQ hd (by ring) (by ring)
  have hfun : (fun t : ℝ => t * deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (t * t)
      (y6 * y6) / (12 * Real.sqrt (deltaY y1 y2 y3 y4 t y6)))
      = fun t => g4dDVolY5 y1 y2 y3 y4 t y6 := by
    funext t; simp only [g4dDVolY5, deltaY]
  rw [hfun] at hgen
  have hval : (((deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        + 2 * y5 ^ 2 * (-2 * (y2 * y2))) * deltaY y1 y2 y3 y4 y5 y6
      - y5 ^ 2 * (deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2)
      / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))
      = (((deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y5 * y5) * (y2 * y2)) * deltaY y1 y2 y3 y4 y5 y6
        - (y5 * y5) * (deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) := by
    ring
  rw [hval] at hgen
  exact hgen

/-- Slot 6 (`Δᵢ = g4dDX6`, partner `x₃`). -/
theorem volY_hasDerivAt2_y6 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => g4dDVolY6 y1 y2 y3 y4 y5 t)
      (((g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y6 * y6) * (y3 * y3)) * deltaY y1 y2 y3 y4 y5 y6
        - (y6 * y6) * (g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) y6 := by
  have hD : HasDerivAt (fun t : ℝ => g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4)
      (y5 * y5) (t * t)) ((-2 * (y3 * y3)) * (2 * y6)) y6 := by
    have hfun : (fun t : ℝ => g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
        (t * t))
        = fun t => (-2 * (y3 * y3)) * (t * t) + g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3)
            (y4 * y4) (y5 * y5) 0 := by
      funext t; simp only [g4dDX6]; ring
    rw [hfun]
    exact g4c_hasDerivAt_lin_sq _ _ _
  have hQ : HasDerivAt (fun t : ℝ => deltaY y1 y2 y3 y4 y5 t)
      (g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) * (2 * y6)) y6 := by
    have := g4d_hasDerivAt_sq_comp
      (g4d_hasDerivAt_deltaX_x6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6))
    simpa only [deltaY] using this
  have hgen := g4c_volY2_generic (D := fun t : ℝ => g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3)
      (y4 * y4) (y5 * y5) (t * t)) (Q := fun t : ℝ => deltaY y1 y2 y3 y4 y5 t)
      (Δii := -2 * (y3 * y3)) hD hQ hd (by ring) (by ring)
  have hfun : (fun t : ℝ => t * g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
      (t * t) / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 t)))
      = fun t => g4dDVolY6 y1 y2 y3 y4 y5 t := by
    funext t; simp only [g4dDVolY6, deltaY]
  rw [hfun] at hgen
  have hval : (((g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        + 2 * y6 ^ 2 * (-2 * (y3 * y3))) * deltaY y1 y2 y3 y4 y5 y6
      - y6 ^ 2 * (g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)) ^ 2)
      / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3))
      = (((g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
          - 4 * (y6 * y6) * (y3 * y3)) * deltaY y1 y2 y3 y4 y5 y6
        - (y6 * y6) * (g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5)
            (y6 * y6)) ^ 2)
        / (12 * (Real.sqrt (deltaY y1 y2 y3 y4 y5 y6)) ^ 3)) := by
    ring
  rw [hval] at hgen
  exact hgen

/-! ## Axiom audit -/

#print axioms g4c_two_h0
#print axioms lmfun_div_two_deriv_left
#print axioms lmfun_div_two_deriv_right
#print axioms lmfun_div_two_iteratedDeriv_two_left
#print axioms lmfun_div_two_iteratedDeriv_two_right
#print axioms g4c_volY2_generic
#print axioms volY_hasDerivAt2_y1
#print axioms volY_hasDerivAt2_y2
#print axioms volY_hasDerivAt2_y3
#print axioms volY_hasDerivAt2_y4
#print axioms volY_hasDerivAt2_y5
#print axioms volY_hasDerivAt2_y6

end Kepler.Text
