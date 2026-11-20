/-
Kepler.Text.IyouSharpV2 — the analytic half of the
`bank_TSKAJXYIYOUOBFsharpv2` closure (HOL ineq entry
`TSKAJXY-IYOUOBF sharp v2`, ineq.hl:242; Assembly slot
`nliTskIYOUOBFsharpv2`).

Lane `iyou-sharpv2-slots-w1`.  The bank box is
`[2hplus,√8] × [2,2.001]² × [2,2hminus] × [2,2.001]²`; the reduction
`bank_TSKAJXYIYOUOBFsharpv2_of_reduce` (Gamma4SharpRoute) leaves two
slots: four-axis monotonicity in `y2,y3,y5,y6` and the two-variable slice
inequality at `y2=y3=y5=y6=2`.  On this WIDE box the RIBCYXU-style crude
per-term derivative bounds fail (the `volY`/`vol4f` pieces swing in
correlated opposite corners), so the sign work is delegated to TM-hull
certificate leaves (`checkPosTMHullC`, Rule P — bounded opt-in per
AGENTS §4); this module supplies the full analytic reduction from eight
explicit certificate slots to the bank:

* `hS2/hS3/hS5/hS6`: `0 <` the four narrow-axis partials on the whole box
  (numerically `min ∂ = +0.1310985`, at the `y1=√8` corner);
* `hS1`: the `y1`-partial is negative on the corner zone
  `[2.80,√8]×[2,2.05]` of the slice (numerically `max = −0.0039`);
* `hS4`: the `y4`-partial is positive along the `y1=√8` edge for
  `y4 ∈ [2,2.05]` (numerically `min = +0.176`);
* `hL1`: `0 < γ4` on the left strip `[2hplus,2.80]×[2,2.05]`
  (min value `+2.4128e-6` at the `(2hplus,2)` corner);
* `hL23`: `0 < γ4` on `[2hplus,√8]×[2.05,2hminus]` (min `+8.3e-3`).

With those, `hmono` follows from `monotoneOn_of_deriv_nonneg` per axis
(the `Gamma4Feed` template lifted to this box), and `h2d` from a three-way
case split: the corner zone collapses monotonically to the PROVEN corner
`gamma4_at_sqrt8 : γ4(√8,2,2,2,2,2) = 0` (Gamma4Sharp), the other two
cases are `hL1`/`hL23`.  The certificate leaves themselves are separate
generated modules; nothing here is a `sorry`.

No new `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.Gamma4Deriv8
import Kepler.Text.Gamma4SharpRoute
import Kepler.Text.Gamma4Mono0
import Kepler.NliBanks17

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanks17

/-! ## 1. The sharpv2 box and its range facts -/

/-- The `TSKAJXY-IYOUOBF sharp v2` bank box. -/
def iysInBox (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 * hplus ≤ y1 ∧ y1 ≤ Real.sqrt 8 ∧
    2 ≤ y2 ∧ y2 ≤ 2.001 ∧ 2 ≤ y3 ∧ y3 ≤ 2.001 ∧
    2 ≤ y4 ∧ y4 ≤ 2 * hminus ∧
    2 ≤ y5 ∧ y5 ≤ 2.001 ∧ 2 ≤ y6 ∧ y6 ≤ 2.001

theorem iys_hplus_eq : hplus = (1.3254 : ℝ) := rfl

theorem iys_two_hplus : 2 * hplus = (2.6508 : ℝ) := by
  rw [iys_hplus_eq]; norm_num

/-- The numeric form of the box's `y1` lower range. -/
theorem iys_y1_ge (y1 : ℝ) (h : 2 * hplus ≤ y1) : (2.6508 : ℝ) ≤ y1 := by
  rw [← iys_two_hplus]; exact h

theorem iys_sqrt8_le : Real.sqrt 8 ≤ (2.8285 : ℝ) := by
  have hsq : (8 : ℝ) ≤ 2.8285 ^ 2 := by norm_num
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.8285)] at h

/-- On the box, `h0 < y1/2` (the `lmfun` zero branch). -/
theorem iys_y1_div2_gt_h0 {y1 : ℝ} (h : 2 * hplus ≤ y1) : h0 < y1 / 2 := by
  have h' : (2.6508 : ℝ) ≤ y1 := by rw [← iys_two_hplus]; exact h
  have hv : h0 = (1.26 : ℝ) := rfl
  rw [hv]; linarith

/-- On the box, `y4/2 ≤ hminus < h0` (the `lmfun` affine branch). -/
theorem iys_y4_div2_lt_h0 {y4 : ℝ} (h : y4 ≤ 2 * hminus) : y4 / 2 < h0 := by
  have h1 : y4 / 2 ≤ hminus := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [h]
  have h2 : hminus ≤ (1.23176 : ℝ) := nb17_hminus_le_123176
  have hv : h0 = (1.26 : ℝ) := rfl
  linarith

/-- `2.4635 ≤ 2*hminus ≤ 2.46352`, so a box `y4` satisfies `y4 ≤ 2.464`. -/
theorem iys_y4_le_2464 {y4 : ℝ} (h : y4 ≤ 2 * hminus) : y4 ≤ (2.464 : ℝ) := by
  have h2 := (nb17_two_hminus_bounds).2
  have h3 : (2.46352 : ℝ) ≤ 2.464 := by norm_num
  linarith [h, h2, h3]

/-! ## 2. `deltaY > 0` on the box

Route: the rationalisation identity `g4d_ups_delta` (`Δ₄² + 4·y₁²·Δ =
upsX (y₁²,y₃²,y₅²) · upsX (y₁²,y₂²,y₆²)`), the factorisation
`upsX a b c = a·(2(b+c) − a) − (b−c)²`, the crude enclosures
`u ≥ 56` and `|Δ₄| ≤ 35.3`, hence `4·y₁²·Δ ≥ 56² − 35.3² > 0`. -/

private theorem iys_ups_factor (a b c : ℝ) :
    upsX a b c = a * (2 * (b + c) - a) - (b - c) ^ 2 := by
  unfold upsX; ring

/-- The squared-slot ranges on the box. -/
private theorem iys_sq_ranges {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : (2.6508 : ℝ) ≤ y1) (h1' : y1 ≤ Real.sqrt 8)
    (h2 : (2 : ℝ) ≤ y2) (h2' : y2 ≤ (2.001 : ℝ))
    (h3 : (2 : ℝ) ≤ y3) (h3' : y3 ≤ (2.001 : ℝ))
    (h4 : (2 : ℝ) ≤ y4) (h4' : y4 ≤ (2.464 : ℝ))
    (h5 : (2 : ℝ) ≤ y5) (h5' : y5 ≤ (2.001 : ℝ))
    (h6 : (2 : ℝ) ≤ y6) (h6' : y6 ≤ (2.001 : ℝ)) :
    (7.02674064 : ℝ) ≤ y1 * y1 ∧ y1 * y1 ≤ 8 ∧
      (4 : ℝ) ≤ y2 * y2 ∧ y2 * y2 ≤ 4.004001 ∧
      (4 : ℝ) ≤ y3 * y3 ∧ y3 * y3 ≤ 4.004001 ∧
      (4 : ℝ) ≤ y4 * y4 ∧ y4 * y4 ≤ 6.071296 ∧
      (4 : ℝ) ≤ y5 * y5 ∧ y5 * y5 ≤ 4.004001 ∧
      (4 : ℝ) ≤ y6 * y6 ∧ y6 * y6 ≤ 4.004001 := by
  have hv8 : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hy1 : (0 : ℝ) ≤ y1 := le_trans (by norm_num : (0 : ℝ) ≤ 2.6508) h1
  have hy2 : (0 : ℝ) ≤ y2 := le_trans (by norm_num : (0 : ℝ) ≤ 2) h2
  have hy3 : (0 : ℝ) ≤ y3 := le_trans (by norm_num : (0 : ℝ) ≤ 2) h3
  have hy4 : (0 : ℝ) ≤ y4 := le_trans (by norm_num : (0 : ℝ) ≤ 2) h4
  have hy5 : (0 : ℝ) ≤ y5 := le_trans (by norm_num : (0 : ℝ) ≤ 2) h5
  have hy6 : (0 : ℝ) ≤ y6 := le_trans (by norm_num : (0 : ℝ) ≤ 2) h6
  have hs8 : (0 : ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := mul_le_mul h1 h1 (by norm_num : (0 : ℝ) ≤ 2.6508) hy1
    have hc : (2.6508 : ℝ) * 2.6508 = 7.02674064 := by norm_num
    linarith [h, hc]
  · have h := mul_le_mul h1' h1' hy1 hs8
    linarith [h, hv8]
  · have h := mul_le_mul h2 h2 (by norm_num : (0 : ℝ) ≤ 2) hy2
    linarith [h]
  · have h := mul_le_mul h2' h2' hy2 (by norm_num : (0 : ℝ) ≤ 2.001)
    have hc : (2.001 : ℝ) * 2.001 = 4.004001 := by norm_num
    linarith [h, hc]
  · have h := mul_le_mul h3 h3 (by norm_num : (0 : ℝ) ≤ 2) hy3
    linarith [h]
  · have h := mul_le_mul h3' h3' hy3 (by norm_num : (0 : ℝ) ≤ 2.001)
    have hc : (2.001 : ℝ) * 2.001 = 4.004001 := by norm_num
    linarith [h, hc]
  · have h := mul_le_mul h4 h4 (by norm_num : (0 : ℝ) ≤ 2) hy4
    linarith [h]
  · have h := mul_le_mul h4' h4' hy4 (by norm_num : (0 : ℝ) ≤ 2.464)
    have hc : (2.464 : ℝ) * 2.464 = 6.071296 := by norm_num
    linarith [h, hc]
  · have h := mul_le_mul h5 h5 (by norm_num : (0 : ℝ) ≤ 2) hy5
    linarith [h]
  · have h := mul_le_mul h5' h5' hy5 (by norm_num : (0 : ℝ) ≤ 2.001)
    have hc : (2.001 : ℝ) * 2.001 = 4.004001 := by norm_num
    linarith [h, hc]
  · have h := mul_le_mul h6 h6 (by norm_num : (0 : ℝ) ≤ 2) hy6
    linarith [h]
  · have h := mul_le_mul h6' h6' hy6 (by norm_num : (0 : ℝ) ≤ 2.001)
    have hc : (2.001 : ℝ) * 2.001 = 4.004001 := by norm_num
    linarith [h, hc]

/-- The absolute-value bound: with `-m ≤ x ≤ m`, `x² ≤ m²`. -/
private theorem iys_sq_abs_le {x m : ℝ} (hx : x ≤ m) (hx' : -m ≤ x)
    (hm : (0 : ℝ) ≤ m) : x ^ 2 ≤ m * m := by
  have h1 : x - m ≤ 0 := by linarith
  have h2 : 0 ≤ x + m := by linarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos h2 h1
  have hexp : (x + m) * (x - m) = x ^ 2 - m * m := by ring
  rw [hexp] at hprod
  linarith

/-- `upsX (y1²,y2²,y6²) ≥ 56` on the box. -/
private theorem iys_u126_ge {y1 y2 y6 : ℝ}
    (hx1 : (7.02674064 : ℝ) ≤ y1 * y1) (hx1' : y1 * y1 ≤ 8)
    (hx2 : (4 : ℝ) ≤ y2 * y2) (hx2' : y2 * y2 ≤ 4.004001)
    (hx6 : (4 : ℝ) ≤ y6 * y6) (hx6' : y6 * y6 ≤ 4.004001) :
    (56 : ℝ) ≤ upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
  rw [iys_ups_factor]
  have hinner : (8 : ℝ) ≤ 2 * (y2 * y2 + y6 * y6) - y1 * y1 := by
    linarith [hx1', hx2, hx6]
  have hx1p : (0 : ℝ) ≤ y1 * y1 := le_trans (by norm_num : (0 : ℝ) ≤ 7.02674064) hx1
  have h := mul_le_mul hx1 hinner (by norm_num : (0 : ℝ) ≤ (8 : ℝ)) hx1p
  have hc : (7.02674064 : ℝ) * 8 = 56.21392512 := by norm_num
  have hd : y2 * y2 - y6 * y6 ≤ (0.004001 : ℝ) := by linarith [hx2', hx6]
  have hd' : -(0.004001 : ℝ) ≤ y2 * y2 - y6 * y6 := by linarith [hx2, hx6']
  have hcross := iys_sq_abs_le hd hd' (by norm_num)
  have hcross' : (0.004001 : ℝ) * 0.004001 ≤ (0.0001 : ℝ) := by norm_num
  linarith [h, hc, hcross, hcross']

/-- `upsX (y1²,y3²,y5²) ≥ 56` on the box. -/
private theorem iys_u135_ge {y1 y3 y5 : ℝ}
    (hx1 : (7.02674064 : ℝ) ≤ y1 * y1) (hx1' : y1 * y1 ≤ 8)
    (hx3 : (4 : ℝ) ≤ y3 * y3) (hx3' : y3 * y3 ≤ 4.004001)
    (hx5 : (4 : ℝ) ≤ y5 * y5) (hx5' : y5 * y5 ≤ 4.004001) :
    (56 : ℝ) ≤ upsX (y1 * y1) (y3 * y3) (y5 * y5) := by
  rw [iys_ups_factor]
  have hinner : (8 : ℝ) ≤ 2 * (y3 * y3 + y5 * y5) - y1 * y1 := by
    linarith [hx1', hx3, hx5]
  have hx1p : (0 : ℝ) ≤ y1 * y1 := le_trans (by norm_num : (0 : ℝ) ≤ 7.02674064) hx1
  have h := mul_le_mul hx1 hinner (by norm_num : (0 : ℝ) ≤ (8 : ℝ)) hx1p
  have hc : (7.02674064 : ℝ) * 8 = 56.21392512 := by norm_num
  have hd : y3 * y3 - y5 * y5 ≤ (0.004001 : ℝ) := by linarith [hx3', hx5]
  have hd' : -(0.004001 : ℝ) ≤ y3 * y3 - y5 * y5 := by linarith [hx3, hx5']
  have hcross := iys_sq_abs_le hd hd' (by norm_num)
  have hcross' : (0.004001 : ℝ) * 0.004001 ≤ (0.0001 : ℝ) := by norm_num
  linarith [h, hc, hcross, hcross']

/-- `|Δ₄| ≤ 35.4` on the box: `−35.4 ≤ Δ₄ ≤ 12.0` over the squared
box, from the crude monomial chains. -/
private theorem iys_deltaX4_bounds {y1 y2 y3 y4 y5 y6 : ℝ}
    (hx1 : (7.02674064 : ℝ) ≤ y1 * y1) (hx1' : y1 * y1 ≤ 8)
    (hx2 : (4 : ℝ) ≤ y2 * y2) (hx2' : y2 * y2 ≤ 4.004001)
    (hx3 : (4 : ℝ) ≤ y3 * y3) (hx3' : y3 * y3 ≤ 4.004001)
    (hx4 : (4 : ℝ) ≤ y4 * y4) (hx4' : y4 * y4 ≤ 6.071296)
    (hx5 : (4 : ℝ) ≤ y5 * y5) (hx5' : y5 * y5 ≤ 4.004001)
    (hx6 : (4 : ℝ) ≤ y6 * y6) (hx6' : y6 * y6 ≤ 4.004001) :
    (-35.4 : ℝ) ≤ deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ∧
      deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≤ 12.0 := by
  set x1 := y1 * y1 with hx1def
  set x2 := y2 * y2 with hx2def
  set x3 := y3 * y3 with hx3def
  set x4 := y4 * y4 with hx4def
  set x5 := y5 * y5 with hx5def
  set x6 := y6 * y6 with hx6def
  have hx1p : (0 : ℝ) ≤ x1 := le_trans (by norm_num : (0 : ℝ) ≤ 7.02674064) hx1
  have hx2p : (0 : ℝ) ≤ x2 := le_trans (by norm_num : (0 : ℝ) ≤ 4) hx2
  have hx3p : (0 : ℝ) ≤ x3 := le_trans (by norm_num : (0 : ℝ) ≤ 4) hx3
  have hx4p : (0 : ℝ) ≤ x4 := le_trans (by norm_num : (0 : ℝ) ≤ 4) hx4
  have hx5p : (0 : ℝ) ≤ x5 := le_trans (by norm_num : (0 : ℝ) ≤ 4) hx5
  have hx6p : (0 : ℝ) ≤ x6 := le_trans (by norm_num : (0 : ℝ) ≤ 4) hx6
  have hx2x3 : (16 : ℝ) ≤ x2 * x3 := by
    have := mul_le_mul hx2 hx3 (by norm_num : (0 : ℝ) ≤ 4) hx2p
    linarith [this]
  have hx2x3' : x2 * x3 ≤ 16.033 := by
    have := mul_le_mul hx2' hx3' hx3p (by norm_num : (0 : ℝ) ≤ 4.004001)
    have hc : (4.004001 : ℝ) * 4.004001 ≤ 16.033 := by norm_num
    linarith [this, hc]
  have hx2x5 : (16 : ℝ) ≤ x2 * x5 := by
    have := mul_le_mul hx2 hx5 (by norm_num : (0 : ℝ) ≤ 4) hx2p
    linarith [this]
  have hx2x5' : x2 * x5 ≤ 16.033 := by
    have := mul_le_mul hx2' hx5' hx5p (by norm_num : (0 : ℝ) ≤ 4.004001)
    have hc : (4.004001 : ℝ) * 4.004001 ≤ 16.033 := by norm_num
    linarith [this, hc]
  have hx3x6 : (16 : ℝ) ≤ x3 * x6 := by
    have := mul_le_mul hx3 hx6 (by norm_num : (0 : ℝ) ≤ 4) hx3p
    linarith [this]
  have hx3x6' : x3 * x6 ≤ 16.033 := by
    have := mul_le_mul hx3' hx6' hx6p (by norm_num : (0 : ℝ) ≤ 4.004001)
    have hc : (4.004001 : ℝ) * 4.004001 ≤ 16.033 := by norm_num
    linarith [this, hc]
  have hx5x6 : (16 : ℝ) ≤ x5 * x6 := by
    have := mul_le_mul hx5 hx6 (by norm_num : (0 : ℝ) ≤ 4) hx5p
    linarith [this]
  have hx5x6' : x5 * x6 ≤ 16.033 := by
    have := mul_le_mul hx5' hx6' hx6p (by norm_num : (0 : ℝ) ≤ 4.004001)
    have hc : (4.004001 : ℝ) * 4.004001 ≤ 16.033 := by norm_num
    linarith [this, hc]
  have hx1x4 : (28.106 : ℝ) ≤ x1 * x4 := by
    have := mul_le_mul hx1 hx4 (by norm_num : (0 : ℝ) ≤ 4) hx1p
    have hc : (7.02674064 : ℝ) * 4 = 28.10696256 := by norm_num
    linarith [this, hc]
  have hx1x4' : x1 * x4 ≤ 48.58 := by
    have := mul_le_mul hx1' hx4' hx4p (by norm_num : (0 : ℝ) ≤ 8)
    have hc : (8 : ℝ) * 6.071296 = 48.570368 := by norm_num
    linarith [this, hc]
  have hLlo : (1.9 : ℝ) ≤ -x1 + x2 + x3 - x4 + x5 + x6 := by
    linarith [hx1', hx2, hx3, hx4', hx5, hx6]
  have hLhi : -x1 + x2 + x3 - x4 + x5 + x6 ≤ 5.0 := by
    linarith [hx1, hx2', hx3', hx4, hx5', hx6']
  have hxL : (13.3 : ℝ) ≤ x1 * (-x1 + x2 + x3 - x4 + x5 + x6) := by
    have := mul_le_mul hx1 hLlo (by norm_num : (0 : ℝ) ≤ 1.9) hx1p
    have hc : (7.02674064 : ℝ) * 1.9 = 13.350807216 := by norm_num
    linarith [this, hc]
  have hxL' : x1 * (-x1 + x2 + x3 - x4 + x5 + x6) ≤ (40 : ℝ) := by
    have := mul_le_mul hx1' hLhi (by linarith : (0 : ℝ) ≤ -x1 + x2 + x3 - x4 + x5 + x6)
      (by norm_num : (0 : ℝ) ≤ 8)
    have hc : (8 : ℝ) * 5.0 = 40 := by norm_num
    linarith [this, hc]
  unfold deltaX4
  constructor <;> linarith

/-- `deltaY > 0` on the sharpv2 box. -/
theorem iys_deltaY_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : iysInBox y1 y2 y3 y4 y5 y6) :
    0 < deltaY y1 y2 y3 y4 y5 y6 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h4'' : y4 ≤ (2.464 : ℝ) := iys_y4_le_2464 h4'
  have h1c : (2.6508 : ℝ) ≤ y1 := iys_y1_ge y1 h1
  obtain ⟨hx1, hx1', hx2, hx2', hx3, hx3', hx4, hx4', hx5, hx5', hx6, hx6'⟩ :=
    iys_sq_ranges h1c h1' h2 h2' h3 h3' h4 h4'' h5 h5' h6 h6'
  have hu126 := iys_u126_ge hx1 hx1' hx2 hx2' hx6 hx6'
  have hu135 := iys_u135_ge hx1 hx1' hx3 hx3' hx5 hx5'
  obtain ⟨hd4lo, hd4hi⟩ := iys_deltaX4_bounds hx1 hx1' hx2 hx2' hx3 hx3' hx4 hx4' hx5 hx5' hx6 hx6'
  have huu : (3136 : ℝ) ≤
      upsX (y1 * y1) (y3 * y3) (y5 * y5) * upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
    have := mul_le_mul hu135 hu126 (by norm_num : (0 : ℝ) ≤ 56) (by linarith [hu126])
    have hc : (56 : ℝ) * 56 = 3136 := by norm_num
    linarith [this, hc]
  have hd4sq : deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ^ 2
      ≤ (35.4 : ℝ) * 35.4 := by
    have hm : deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≤ (35.4 : ℝ) :=
      by linarith
    have hp : -(35.4 : ℝ) ≤ deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) :=
      by linarith
    exact iys_sq_abs_le hm hp (by norm_num)
  have hups := g4d_ups_delta (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
  have hkey : (1882.8 : ℝ) ≤ 4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
    have hcc : (35.4 : ℝ) * 35.4 = 1253.16 := by norm_num
    have hsub : 4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
        = upsX (y1 * y1) (y3 * y3) (y5 * y5) * upsX (y1 * y1) (y2 * y2) (y6 * y6)
          - deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ^ 2 := by
      linarith [hups]
    rw [hsub]
    have hc2 : (3136 : ℝ) - 1253.16 = 1882.84 := by norm_num
    linarith [huu, hd4sq, hcc, hc2]
  show 0 < deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
  by_contra hnn
  push_neg at hnn
  have h4pos : (0 : ℝ) ≤ 4 * (y1 * y1) := by positivity
  have hle : 4 * (y1 * y1) * deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h4pos hnn
  linarith [hkey]


/-! ## 3. `lmfun` branch facts on the box -/

/-- The affine-branch `lmfun` derivative value used for the narrow and `y4`
slots (`t/2 < h0` on the box). -/
theorem iys_lmfun_affine_deriv {t : ℝ} (ht : t ≤ (2.05 : ℝ)) :
    HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) :=
  g4d_lmfun_hasDerivAt_of_lt (by
    have hv : h0 = (1.26 : ℝ) := rfl
    rw [hv]
    linarith)

/-- The zero-branch `lmfun` derivative value used for the `y1` slot
(`h0 < y1/2` on the box). -/
theorem iys_lmfun_zero_deriv {y1 : ℝ} (h1 : 2 * hplus ≤ y1) :
    HasDerivAt lmfun 0 (y1 / 2) :=
  g4d_lmfun_hasDerivAt_of_gt (iys_y1_div2_gt_h0 h1)

/-- `2.6508 ≤ √8` and `2.80 ≤ √8` (rational lower bounds for the corner
zone). -/
theorem iys_sqrt8_ge : (2.6508 : ℝ) ≤ Real.sqrt 8 := by
  have hpos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hcmp : (2.6508 : ℝ) * 2.6508 ≤ 8 := by norm_num
  by_contra hcon
  push_neg at hcon
  have h1 := mul_lt_mul_of_pos_right hcon (by linarith [hpos] : (0 : ℝ) < (2.6508 : ℝ) + Real.sqrt 8)
  nlinarith [hsq, hcmp, h1]

theorem iys_sqrt8_ge_280 : (2.80 : ℝ) ≤ Real.sqrt 8 := by
  have hpos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 8 * Real.sqrt 8 = 8 := Real.mul_self_sqrt (by norm_num)
  have hcmp : (2.8 : ℝ) * 2.8 ≤ 8 := by norm_num
  by_contra hcon
  push_neg at hcon
  have h1 := mul_lt_mul_of_pos_right hcon (by linarith [hpos] : (0 : ℝ) < (2.8 : ℝ) + Real.sqrt 8)
  nlinarith [hsq, hcmp, h1]

/-! ## 4. The six monotonicity wirings -/

/-- Coordinatewise monotonicity in `y2`, from the `y2`-partial
certificate slot. -/
theorem iys_mono_y2 {a b y1 y3 y4 y5 y6 : ℝ}
    (hb : iysInBox y1 a y3 y4 y5 y6) (hb' : iysInBox y1 b y3 y4 y5 y6) (hab : a ≤ b)
    (hS : ∀ t : ℝ, iysInBox y1 t y3 y4 y5 y6 →
      0 < g4dDVolY2 y1 t y3 y4 y5 y6 - g4dDVol4f2 y1 t y3 y4 y5 y6 (-1 / (h0 - 1))) :
    gamma4fgcy y1 a y3 y4 y5 y6 lmfun ≤ gamma4fgcy y1 b y3 y4 y5 y6 lmfun := by
  obtain ⟨h1, h1', ha, ha', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h1c : (2.6508 : ℝ) ≤ y1 := by rw [← iys_two_hplus]; exact h1
  obtain ⟨_, _, hbl, hbh', _, _, _, _, _, _, _, _⟩ := hb'
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 t y3 y4 y5 y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 t y3 y4 y5 y6 :=
        ⟨h1, h1', le_trans ha hta, le_trans htb hbh', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y2 y1 t y3 y4 y5 y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [hta, ha]) (by linarith [h3]) (by linarith [h4]) (by linarith [h5]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 t y3 y4 y5 y6 :=
        ⟨h1, h1', le_trans ha hta.le, le_trans htb.le hbh', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y2 y1 t y3 y4 y5 y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [hta, ha]) (by linarith [h3]) (by linarith [h4]) (by linarith [h5]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 t y3 y4 y5 y6 :=
        ⟨h1, h1', le_trans ha hta.le, le_trans htb.le hbh', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y2 y1 t y3 y4 y5 y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [hta, ha]) (by linarith [h3]) (by linarith [h4]) (by linarith [h5]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      rw [hd.deriv]
      exact (hS t hbox).le
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y3`, from the `y3`-partial
certificate slot. -/
theorem iys_mono_y3 {a b y1 y2 y4 y5 y6 : ℝ}
    (hb : iysInBox y1 y2 a y4 y5 y6) (hb' : iysInBox y1 y2 b y4 y5 y6) (hab : a ≤ b)
    (hS : ∀ t : ℝ, iysInBox y1 y2 t y4 y5 y6 →
      0 < g4dDVolY3 y1 y2 t y4 y5 y6 - g4dDVol4f3 y1 y2 t y4 y5 y6 (-1 / (h0 - 1))) :
    gamma4fgcy y1 y2 a y4 y5 y6 lmfun ≤ gamma4fgcy y1 y2 b y4 y5 y6 lmfun := by
  obtain ⟨h1, h1', h2, h2', ha, ha', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h1c : (2.6508 : ℝ) ≤ y1 := by rw [← iys_two_hplus]; exact h1
  obtain ⟨_, _, _, _, hbl, hbh', _, _, _, _, _, _⟩ := hb'
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 t y4 y5 y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 t y4 y5 y6 :=
        ⟨h1, h1', h2, h2', le_trans ha hta, le_trans htb hbh', h4, h4', h5, h5', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y3 y1 y2 t y4 y5 y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [hta, ha]) (by linarith [h4]) (by linarith [h5]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 t y4 y5 y6 :=
        ⟨h1, h1', h2, h2', le_trans ha hta.le, le_trans htb.le hbh', h4, h4', h5, h5', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y3 y1 y2 t y4 y5 y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [hta, ha]) (by linarith [h4]) (by linarith [h5]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 t y4 y5 y6 :=
        ⟨h1, h1', h2, h2', le_trans ha hta.le, le_trans htb.le hbh', h4, h4', h5, h5', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y3 y1 y2 t y4 y5 y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [hta, ha]) (by linarith [h4]) (by linarith [h5]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      rw [hd.deriv]
      exact (hS t hbox).le
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y5`, from the `y5`-partial
certificate slot. -/
theorem iys_mono_y5 {a b y1 y2 y3 y4 y6 : ℝ}
    (hb : iysInBox y1 y2 y3 y4 a y6) (hb' : iysInBox y1 y2 y3 y4 b y6) (hab : a ≤ b)
    (hS : ∀ t : ℝ, iysInBox y1 y2 y3 y4 t y6 →
      0 < g4dDVolY5 y1 y2 y3 y4 t y6 - g4dDVol4f5 y1 y2 y3 y4 t y6 (-1 / (h0 - 1))) :
    gamma4fgcy y1 y2 y3 y4 a y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 b y6 lmfun := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', ha, ha', h6, h6'⟩ := hb
  have h1c : (2.6508 : ℝ) ≤ y1 := by rw [← iys_two_hplus]; exact h1
  obtain ⟨_, _, _, _, _, _, _, _, hbl, hbh', _, _⟩ := hb'
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 y3 y4 t y6 lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 y3 y4 t y6 :=
        ⟨h1, h1', h2, h2', h3, h3', h4, h4', le_trans ha hta, le_trans htb hbh', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 t y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [h3]) (by linarith [h4]) (by linarith [hta, ha]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 y3 y4 t y6 :=
        ⟨h1, h1', h2, h2', h3, h3', h4, h4', le_trans ha hta.le, le_trans htb.le hbh', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 t y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [h3]) (by linarith [h4]) (by linarith [hta, ha]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 y3 y4 t y6 :=
        ⟨h1, h1', h2, h2', h3, h3', h4, h4', le_trans ha hta.le, le_trans htb.le hbh', h6, h6'⟩
      have hd := gamma4fgcy_hasDerivAt_y5 y1 y2 y3 y4 t y6 (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [h3]) (by linarith [h4]) (by linarith [hta, ha]) (by linarith [h6])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      rw [hd.deriv]
      exact (hS t hbox).le
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Coordinatewise monotonicity in `y6`, from the `y6`-partial
certificate slot. -/
theorem iys_mono_y6 {a b y1 y2 y3 y4 y5 : ℝ}
    (hb : iysInBox y1 y2 y3 y4 y5 a) (hb' : iysInBox y1 y2 y3 y4 y5 b) (hab : a ≤ b)
    (hS : ∀ t : ℝ, iysInBox y1 y2 y3 y4 y5 t →
      0 < g4dDVolY6 y1 y2 y3 y4 y5 t - g4dDVol4f6 y1 y2 y3 y4 y5 t (-1 / (h0 - 1))) :
    gamma4fgcy y1 y2 y3 y4 y5 a lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 b lmfun := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', ha, ha'⟩ := hb
  have h1c : (2.6508 : ℝ) ≤ y1 := by rw [← iys_two_hplus]; exact h1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbl, hbh'⟩ := hb'
  have hmono : MonotoneOn (fun t => gamma4fgcy y1 y2 y3 y4 y5 t lmfun) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 y3 y4 y5 t :=
        ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', le_trans ha hta, le_trans htb hbh'⟩
      have hd := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 t (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [h3]) (by linarith [h4]) (by linarith [h5]) (by linarith [hta, ha])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 y3 y4 y5 t :=
        ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', le_trans ha hta.le, le_trans htb.le hbh'⟩
      have hd := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 t (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [h3]) (by linarith [h4]) (by linarith [h5]) (by linarith [hta, ha])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox y1 y2 y3 y4 y5 t :=
        ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', le_trans ha hta.le, le_trans htb.le hbh'⟩
      have hd := gamma4fgcy_hasDerivAt_y6 y1 y2 y3 y4 y5 t (-1 / (h0 - 1))
        (by linarith [h1c]) (by linarith [h2]) (by linarith [h3]) (by linarith [h4]) (by linarith [h5]) (by linarith [hta, ha])
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv (le_trans (le_trans htb.le hbh') (by norm_num : (2.001 : ℝ) ≤ 2.05)))
      rw [hd.deriv]
      exact (hS t hbox).le
  exact hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-! ## 5. The `hmono` assembly -/

/-- The full `hmono` slot of `bank_TSKAJXYIYOUOBFsharpv2_of_reduce`, from
the four narrow-axis certificate slots. -/
theorem iys_hmono
    (hS2 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY2 y1 y2 y3 y4 y5 y6 - g4dDVol4f2 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS3 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY3 y1 y2 y3 y4 y5 y6 - g4dDVol4f3 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS5 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY5 y1 y2 y3 y4 y5 y6 - g4dDVol4f5 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS6 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY6 y1 y2 y3 y4 y5 y6 - g4dDVol4f6 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1))) :
    ∀ y1 y2 y3 y4 y5 y6 y2' y3' y5' y6' : ℝ,
      2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 → 2 ≤ y4 → y4 ≤ 2 * hminus →
      (2 ≤ y2 ∧ y2 ≤ 2.001 ∧ 2 ≤ y3 ∧ y3 ≤ 2.001 ∧
        2 ≤ y5 ∧ y5 ≤ 2.001 ∧ 2 ≤ y6 ∧ y6 ≤ 2.001) →
      (2 ≤ y2' ∧ y2' ≤ 2.001 ∧ 2 ≤ y3' ∧ y3' ≤ 2.001 ∧
        2 ≤ y5' ∧ y5' ≤ 2.001 ∧ 2 ≤ y6' ∧ y6' ≤ 2.001) →
      y2 ≤ y2' → y3 ≤ y3' → y5 ≤ y5' → y6 ≤ y6' →
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ≤ gamma4fgcy y1 y2' y3' y4 y5' y6' lmfun := by
  intro y1 y2 y3 y4 y5 y6 y2' y3' y5' y6' h1 h1' h4 h4' hnb hnb' h2 h3 h5 h6
  obtain ⟨a2, a2', a3, a3', a5, a5', a6, a6'⟩ := hnb
  obtain ⟨b2, b2', b3, b3', b5, b5', b6, b6'⟩ := hnb'
  have hboxA : iysInBox y1 y2 y3 y4 y5 y6 :=
    ⟨h1, h1', a2, a2', a3, a3', h4, h4', a5, a5', a6, a6'⟩
  have hboxT2 : iysInBox y1 y2' y3 y4 y5 y6 :=
    ⟨h1, h1', b2, b2', a3, a3', h4, h4', a5, a5', a6, a6'⟩
  have hboxT3 : iysInBox y1 y2' y3' y4 y5 y6 :=
    ⟨h1, h1', b2, b2', b3, b3', h4, h4', a5, a5', a6, a6'⟩
  have hboxT5 : iysInBox y1 y2' y3' y4 y5' y6 :=
    ⟨h1, h1', b2, b2', b3, b3', h4, h4', b5, b5', a6, a6'⟩
  have hboxB : iysInBox y1 y2' y3' y4 y5' y6' :=
    ⟨h1, h1', b2, b2', b3, b3', h4, h4', b5, b5', b6, b6'⟩
  have s2 := iys_mono_y2 hboxA hboxT2 h2 (fun t ht => hS2 y1 t y3 y4 y5 y6 ht)
  have s3 := iys_mono_y3 hboxT2 hboxT3 h3 (fun t ht => hS3 y1 y2' t y4 y5 y6 ht)
  have s5 := iys_mono_y5 hboxT3 hboxT5 h5 (fun t ht => hS5 y1 y2' y3' y4 t y6 ht)
  have s6 := iys_mono_y6 hboxT5 hboxB h6 (fun t ht => hS6 y1 y2' y3' y4 y5' t ht)
  exact le_trans s2 (le_trans s3 (le_trans s5 s6))

/-! ## 6. The corner zone collapse -/

/-- On the corner zone `[2.80,√8]×[2,2.05]` the slice is antitone in `y1`
(the `y1`-partial certificate slot is negative). -/
theorem iys_zone_anti_y1 {y4 : ℝ}
    (h4 : (2 : ℝ) ≤ y4) (h4' : y4 ≤ (2.05 : ℝ))
    (hS1 : ∀ t : ℝ, (2.80 : ℝ) ≤ t → t ≤ Real.sqrt 8 →
      g4dDVolY1 t 2 2 y4 2 2 - g4dDVol4f1 t 2 2 y4 2 2 0 < 0) :
    ∀ y1 y1' : ℝ, (2.80 : ℝ) ≤ y1 → y1 ≤ Real.sqrt 8 →
      (2.80 : ℝ) ≤ y1' → y1' ≤ Real.sqrt 8 → y1 ≤ y1' →
      gamma4fgcy y1' 2 2 y4 2 2 lmfun ≤ gamma4fgcy y1 2 2 y4 2 2 lmfun := by
  have h4b : y4 ≤ 2 * hminus := by
    have hlo := (nb17_two_hminus_bounds).1
    have hv : (2.05 : ℝ) ≤ 2.4635 := by norm_num
    linarith
  have hmono : MonotoneOn (fun t => -gamma4fgcy t 2 2 y4 2 2 lmfun)
      (Set.Icc (2.80 : ℝ) (Real.sqrt 8)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox t 2 2 y4 2 2 :=
        ⟨by rw [iys_two_hplus]; linarith [hta], htb,
          by norm_num, by norm_num, by norm_num, by norm_num,
          h4, h4b, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hd := gamma4fgcy_hasDerivAt_y1 t 2 2 y4 2 2 0
        (by linarith [hta]) (by norm_num) (by norm_num) (by linarith [h4])
        (by norm_num) (by norm_num)
        (iys_deltaY_pos hbox) (iys_lmfun_zero_deriv (by
          rw [iys_two_hplus]; linarith [hta]))
      exact hd.neg.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox t 2 2 y4 2 2 :=
        ⟨by rw [iys_two_hplus]; linarith [hta.le], htb.le,
          by norm_num, by norm_num, by norm_num, by norm_num,
          h4, h4b, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hd := gamma4fgcy_hasDerivAt_y1 t 2 2 y4 2 2 0
        (by linarith [hta.le]) (by norm_num) (by norm_num) (by linarith [h4])
        (by norm_num) (by norm_num)
        (iys_deltaY_pos hbox) (iys_lmfun_zero_deriv (by
          rw [iys_two_hplus]; linarith [hta.le]))
      exact hd.neg.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox t 2 2 y4 2 2 :=
        ⟨by rw [iys_two_hplus]; linarith [hta.le], htb.le,
          by norm_num, by norm_num, by norm_num, by norm_num,
          h4, h4b, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hd := gamma4fgcy_hasDerivAt_y1 t 2 2 y4 2 2 0
        (by linarith [hta.le]) (by norm_num) (by norm_num) (by linarith [h4])
        (by norm_num) (by norm_num)
        (iys_deltaY_pos hbox) (iys_lmfun_zero_deriv (by
          rw [iys_two_hplus]; linarith [hta.le]))
      have hd2 : HasDerivAt (fun t => -gamma4fgcy t 2 2 y4 2 2 lmfun)
          (-(g4dDVolY1 t 2 2 y4 2 2 - g4dDVol4f1 t 2 2 y4 2 2 0)) t := hd.neg
      rw [hd2.deriv]
      have hp := hS1 t hta.le htb.le
      linarith
  intro y1 y1' ha ha' hb hb' ab
  have hm := hmono ⟨ha, ha'⟩ ⟨hb, hb'⟩ ab
  simpa using hm

/-- Along the `y1=√8` edge the slice is monotone in `y4` (the `y4`-partial
certificate slot is positive). -/
theorem iys_edge_mono_y4
    (hS4 : ∀ t : ℝ, (2 : ℝ) ≤ t → t ≤ (2.05 : ℝ) →
      0 < g4dDVolY4 (Real.sqrt 8) 2 2 t 2 2 - g4dDVol4f4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1))) :
    ∀ y4 y4' : ℝ, (2 : ℝ) ≤ y4 → y4 ≤ y4' → y4' ≤ (2.05 : ℝ) →
      gamma4fgcy (Real.sqrt 8) 2 2 y4 2 2 lmfun ≤ gamma4fgcy (Real.sqrt 8) 2 2 y4' 2 2 lmfun := by
  have h4b : (2.05 : ℝ) ≤ 2 * hminus := by
    have hlo := (nb17_two_hminus_bounds).1
    have hv : (2.05 : ℝ) ≤ 2.4635 := by norm_num
    linarith
  have hmono : MonotoneOn (fun t => gamma4fgcy (Real.sqrt 8) 2 2 t 2 2 lmfun)
      (Set.Icc (2 : ℝ) (2.05 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · intro t ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox (Real.sqrt 8) 2 2 t 2 2 :=
        ⟨by rw [iys_two_hplus]; exact iys_sqrt8_ge, le_rfl,
          by norm_num, by norm_num, by norm_num, by norm_num,
          hta, le_trans htb h4b, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hd := gamma4fgcy_hasDerivAt_y4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1))
        (by norm_num) (by norm_num) (by norm_num) (by linarith [hta])
        (by norm_num) (by norm_num)
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv htb)
      exact hd.continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox (Real.sqrt 8) 2 2 t 2 2 :=
        ⟨by rw [iys_two_hplus]; exact iys_sqrt8_ge, le_rfl,
          by norm_num, by norm_num, by norm_num, by norm_num,
          hta.le, le_trans htb.le h4b, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hd := gamma4fgcy_hasDerivAt_y4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1))
        (by norm_num) (by norm_num) (by norm_num) (by linarith [hta.le])
        (by norm_num) (by norm_num)
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv htb.le)
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨hta, htb⟩ := ht
      have hbox : iysInBox (Real.sqrt 8) 2 2 t 2 2 :=
        ⟨by rw [iys_two_hplus]; exact iys_sqrt8_ge, le_rfl,
          by norm_num, by norm_num, by norm_num, by norm_num,
          hta.le, le_trans htb.le h4b, by norm_num, by norm_num, by norm_num, by norm_num⟩
      have hd := gamma4fgcy_hasDerivAt_y4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1))
        (by norm_num) (by norm_num) (by norm_num) (by linarith [hta.le])
        (by norm_num) (by norm_num)
        (iys_deltaY_pos hbox) (iys_lmfun_affine_deriv htb.le)
      rw [hd.deriv]
      exact (hS4 t hta.le htb.le).le
  intro y4 y4' ha ab hb'
  exact hmono ⟨ha, le_trans ab hb'⟩ ⟨le_trans ha ab, hb'⟩ ab

/-- The corner-zone collapse: on `[2.80,√8]×[2,2.05]` the slice is
nonnegative (monotone down to the PROVEN corner value 0). -/
theorem iys_zone_nonneg {y4 : ℝ}
    (h4 : (2 : ℝ) ≤ y4) (h4' : y4 ≤ (2.05 : ℝ))
    (hS1 : ∀ t : ℝ, (2.80 : ℝ) ≤ t → t ≤ Real.sqrt 8 →
      g4dDVolY1 t 2 2 y4 2 2 - g4dDVol4f1 t 2 2 y4 2 2 0 < 0)
    (hS4 : ∀ t : ℝ, (2 : ℝ) ≤ t → t ≤ (2.05 : ℝ) →
      0 < g4dDVolY4 (Real.sqrt 8) 2 2 t 2 2 - g4dDVol4f4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1))) :
    ∀ y1 : ℝ, (2.80 : ℝ) ≤ y1 → y1 ≤ Real.sqrt 8 →
      0 ≤ gamma4fgcy y1 2 2 y4 2 2 lmfun := by
  intro y1 h1 h1'
  have s1 := iys_zone_anti_y1 h4 h4' hS1 y1 (Real.sqrt 8) h1 h1' iys_sqrt8_ge_280 le_rfl h1'
  have s2 := iys_edge_mono_y4 hS4 2 y4 (by norm_num) h4 h4'
  have hcorner : gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun = 0 := gamma4_at_sqrt8
  rw [← hcorner]
  exact le_trans s2 s1

/-! ## 7. The `h2d` assembly -/

/-- The full `h2d` slot of `bank_TSKAJXYIYOUOBFsharpv2_of_reduce`, from
the corner-zone certificates and the two value-region slots. -/
theorem iys_h2d
    (hS1 : ∀ t y4 : ℝ, (2.80 : ℝ) ≤ t → t ≤ Real.sqrt 8 → (2 : ℝ) ≤ y4 → y4 ≤ (2.05 : ℝ) →
      g4dDVolY1 t 2 2 y4 2 2 - g4dDVol4f1 t 2 2 y4 2 2 0 < 0)
    (hS4 : ∀ t : ℝ, (2 : ℝ) ≤ t → t ≤ (2.05 : ℝ) →
      0 < g4dDVolY4 (Real.sqrt 8) 2 2 t 2 2 - g4dDVol4f4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1)))
    (hL1 : ∀ y1 y4 : ℝ, 2 * hplus ≤ y1 → y1 ≤ (2.80 : ℝ) → (2 : ℝ) ≤ y4 → y4 ≤ (2.05 : ℝ) →
      0 < gamma4fgcy y1 2 2 y4 2 2 lmfun)
    (hL23 : ∀ y1 y4 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 → (2.05 : ℝ) ≤ y4 → y4 ≤ 2 * hminus →
      0 < gamma4fgcy y1 2 2 y4 2 2 lmfun) :
    ∀ y1 y4 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 → (2 : ℝ) ≤ y4 → y4 ≤ 2 * hminus →
      0 ≤ gamma4fgcy y1 2 2 y4 2 2 lmfun := by
  intro y1 y4 h1 h1' h4 h4'
  by_cases h05 : y4 ≤ (2.05 : ℝ)
  · by_cases h80 : y1 ≤ (2.80 : ℝ)
    · exact le_of_lt (hL1 y1 y4 h1 h80 h4 h05)
    · have h80' : (2.80 : ℝ) ≤ y1 := le_of_lt (lt_of_not_ge h80)
      exact iys_zone_nonneg h4 h05 (fun t ht1 ht2 => hS1 t y4 ht1 ht2 h4 h05) hS4 y1 h80' h1'
  · have h05' : (2.05 : ℝ) ≤ y4 := le_of_lt (lt_of_not_ge h05)
    exact le_of_lt (hL23 y1 y4 h1 h1' h05' h4')

/-! ## 8. The conditional bank closure -/

/-- **The bank follows from the eight certificate slots.**  This is the
fixed point of the analytic half; the slots are exactly what the
generated TM-hull leaf modules prove (`checkPosTMHullC` + `boxMem`
closers).  All eight statements are strictly decidable-sign claims over
dyadic-outer boxes of the ranges appearing here. -/
theorem bank_TSKAJXYIYOUOBFsharpv2_of_slots
    (hS2 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY2 y1 y2 y3 y4 y5 y6 - g4dDVol4f2 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS3 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY3 y1 y2 y3 y4 y5 y6 - g4dDVol4f3 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS5 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY5 y1 y2 y3 y4 y5 y6 - g4dDVol4f5 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS6 : ∀ y1 y2 y3 y4 y5 y6 : ℝ, iysInBox y1 y2 y3 y4 y5 y6 →
      0 < g4dDVolY6 y1 y2 y3 y4 y5 y6 - g4dDVol4f6 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)))
    (hS1 : ∀ t y4 : ℝ, (2.80 : ℝ) ≤ t → t ≤ Real.sqrt 8 → (2 : ℝ) ≤ y4 → y4 ≤ (2.05 : ℝ) →
      g4dDVolY1 t 2 2 y4 2 2 - g4dDVol4f1 t 2 2 y4 2 2 0 < 0)
    (hS4 : ∀ t : ℝ, (2 : ℝ) ≤ t → t ≤ (2.05 : ℝ) →
      0 < g4dDVolY4 (Real.sqrt 8) 2 2 t 2 2 - g4dDVol4f4 (Real.sqrt 8) 2 2 t 2 2 (-1 / (h0 - 1)))
    (hL1 : ∀ y1 y4 : ℝ, 2 * hplus ≤ y1 → y1 ≤ (2.80 : ℝ) → (2 : ℝ) ≤ y4 → y4 ≤ (2.05 : ℝ) →
      0 < gamma4fgcy y1 2 2 y4 2 2 lmfun)
    (hL23 : ∀ y1 y4 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 → (2.05 : ℝ) ≤ y4 → y4 ≤ 2 * hminus →
      0 < gamma4fgcy y1 2 2 y4 2 2 lmfun) :
    bank_TSKAJXYIYOUOBFsharpv2 :=
  bank_TSKAJXYIYOUOBFsharpv2_of_reduce (iys_hmono hS2 hS3 hS5 hS6) (iys_h2d hS1 hS4 hL1 hL23)

/-! ## Axiom audit (house style) -/

#print axioms iys_deltaY_pos
#print axioms iys_mono_y2
#print axioms iys_mono_y3
#print axioms iys_mono_y5
#print axioms iys_mono_y6
#print axioms iys_hmono
#print axioms iys_zone_anti_y1
#print axioms iys_edge_mono_y4
#print axioms iys_zone_nonneg
#print axioms iys_h2d
#print axioms bank_TSKAJXYIYOUOBFsharpv2_of_slots

end Kepler.Text
