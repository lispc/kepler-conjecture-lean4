import Kepler.Text.PackingAuto21
import Kepler.NliHminus

/-!
Kepler.NliBanks3 — W2 lane `nli-unknown-w2`, task W2-1.

Four `rad2` bank entries of the `TADIAMB` family are closed through the W1
template: with `H = rhoX − 8·deltaX`, `rad2X > 2` is `H > 0`, and `H` is
increasing along every axis on the rational super-box

`x1 ∈ [6.0650528, 7.02674064]`, `x2 … x6 ∈ [4, 8]`

(the `y1` edge uses the W2-0 envelope `hminus ≥ 1.2313664`, i.e.
`6.0650528 ≤ 4·hminus²`).  So `H(x) ≥ H(lower corner)` and the corner value
is a rational `norm_num` check.

Axes used (y-box → x super-box):

* `y ∈ [2·hminus, 2·hplus]` → `x ∈ [6.0650528, 7.02674064]`
* `y ∈ [2·hminus, √8]`       → `x ∈ [5.76, 8]`
* `y ∈ [2, 2·hminus]`        → `x ∈ [4, 8]`
* `y ∈ [2·hplus, √8]`        → `x ∈ [7.02674064, 8]`

Closed here: `QITNPEA1_2_2`, `MKFKQWU`, `ZTGIJCF4_1_1_1_1`, `ZTGIJCF4_1_0_1_1`.
No certificates, no `sorry`/`axiom`/`native_decide`.
-/

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks3
open Kepler.Text
open Kepler.NliHminus

/-! ## Scalar box helpers (`y ↦ x = y²`) -/

theorem sq_ge_sq (y lo : ℝ) (hl : 0 ≤ lo) (h : lo ≤ y) : lo ^ 2 ≤ y * y := by
  nlinarith

theorem sq_ge_4 (y : ℝ) (h : 2 ≤ y) : (4:ℝ) ≤ y * y := by nlinarith

theorem sq_ge_hminus (y : ℝ) (h : 2 * hminus ≤ y) : (6.0650528 : ℝ) ≤ y * y := by
  have h1 : (0:ℝ) < hminus := by linarith [mi_hminus_prop.1]
  have h4 := Kepler.NliHminus.four_hminus_sq_ge
  nlinarith [sq_nonneg (y - 2 * hminus), sq_nonneg (y + 2 * hminus)]

theorem sq_le_hplus (y : ℝ) (hy : 0 ≤ y) (h : y ≤ 2 * hplus) :
    y * y ≤ 7.02674064 := by
  have hp : hplus = 1.3254 := rfl
  rw [hp] at h
  nlinarith

theorem le_sqrt8 (y : ℝ) (h : y ≤ 2 * hminus) : y ≤ Real.sqrt 8 := by
  have h1 : hminus < 1.3 := mi_hminus_prop.2.1
  have h2 : (2.6:ℝ) < Real.sqrt 8 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

theorem sq_le_8 (y : ℝ) (hy : 0 ≤ y) (h : y ≤ Real.sqrt 8) : y * y ≤ 8 := by
  have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
  have h0 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
  nlinarith

theorem sq_ge_576 (y : ℝ) (h : 2 * hminus ≤ y) : (5.76 : ℝ) ≤ y * y := by
  have h1 : (1.2:ℝ) ≤ hminus := mi_hminus_prop.1
  have h0 : (0:ℝ) < hminus := by linarith
  nlinarith [sq_nonneg (y - 2 * hminus), sq_nonneg (y + 2 * hminus), sq_nonneg hminus]

theorem sq_ge_hplus (y : ℝ) (h : 2 * hplus ≤ y) : (7.02674064 : ℝ) ≤ y * y := by
  have hp : hplus = 1.3254 := rfl
  rw [hp] at h
  nlinarith

/-! ## Axis monotonicity of `H = rhoX − 8·deltaX`

Each lemma has the shape
`H(…, b, …) − H(…, a, …) = (b − a)·(G + x_pair(8 − x_pair)·(a + b − 2·lo))`
with `G = ∂H/∂x_i` at `x_i = lo` and `0 ≤ G` a sum of nonnegative products. -/

theorem H_mono_1 (a b x2 x3 x4 x5 x6 : ℝ)
    (ha : (6.0650528:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (7.02674064:ℝ))
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (5.76:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX a x2 x3 x4 x5 x6 - 8 * deltaX a x2 x3 x4 x5 x6 ≤
      rhoX b x2 x3 x4 x5 x6 - 8 * deltaX b x2 x3 x4 x5 x6 := by
  have hid : (rhoX b x2 x3 x4 x5 x6 - 8 * deltaX b x2 x3 x4 x5 x6) -
      (rhoX a x2 x3 x4 x5 x6 - 8 * deltaX a x2 x3 x4 x5 x6)
      = (b - a) * ((16.5204224 * (8 - x4) + 4.1301056 * (x4 - 4) * (8 - x4))
                  + 14.08 * (x5 - 4) + 3.52 * (x4 - 4) * (x6 - 4) + 8 * (x3 - 5.76) * (x5 - 4)
                  + 8 * (x2 - 4) * (x6 - 4) + 2 * (x3 - 5.76) * (x4 - 4) * (x6 - 4)
                  + 2 * (x2 - 4) * (x4 - 4) * (x5 - 4)
        + (x4 * (8 - x4)) * (a + b - 2 * 6.0650528)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (8 - x4) + 4.1301056 * (x4 - 4) * (8 - x4)
          + 14.08 * (x5 - 4) + 3.52 * (x4 - 4) * (x6 - 4) + 8 * (x3 - 5.76) * (x5 - 4)
          + 8 * (x2 - 4) * (x6 - 4) + 2 * (x3 - 5.76) * (x4 - 4) * (x6 - 4)
                + 2 * (x2 - 4) * (x4 - 4) * (x5 - 4) := by
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 5.76 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have gv : (0:ℝ) ≤ (8 - x4) := by linarith
    nlinarith [(mul_nonneg gx4 gv), (mul_nonneg gx3 gx5), (mul_nonneg gx2 gx6), (mul_nonneg gx4 gx6), (mul_nonneg (mul_nonneg gx3 gx4) gx6), (mul_nonneg (mul_nonneg gx2 gx4) gx5)]
  have hA : (0:ℝ) ≤ x4 * (8 - x4) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 6.0650528 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (8 - x4) + 4.1301056 * (x4 - 4) * (8 - x4) + 14.08 * (x5 - 4) + 3.52 * (x4 - 4) * (x6 - 4) + 8 * (x3 - 5.76) * (x5 - 4) + 8 * (x2 - 4) * (x6 - 4) + 2 * (x3 - 5.76) * (x4 - 4) * (x6 - 4) + 2 * (x2 - 4) * (x4 - 4) * (x5 - 4)) + (x4 * (8 - x4)) * (a + b - 2 * 6.0650528) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem H_mono_2 (a b x1 x3 x4 x5 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064) (h3 : (5.76:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 a x3 x4 x5 x6 - 8 * deltaX x1 a x3 x4 x5 x6 ≤
      rhoX x1 b x3 x4 x5 x6 - 8 * deltaX x1 b x3 x4 x5 x6 := by
  have hid : (rhoX x1 b x3 x4 x5 x6 - 8 * deltaX x1 b x3 x4 x5 x6) -
      (rhoX x1 a x3 x4 x5 x6 - 8 * deltaX x1 a x3 x4 x5 x6)
      = (b - a) * ((16.5204224 * (x6 - 4) + 14.08 * (x4 - 4) + 3.52 * (x5 - 4) * (x6 - 4))
                  + 4.1301056 * (x4 - 4) * (x5 - 4) + 8 * (x3 - 5.76) * (x4 - 4)
                  + 8 * (x1 - 6.0650528) * (x6 - 4) + 2 * (x3 - 5.76) * (x5 - 4) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x4 - 4) * (x5 - 4)
        + (x5 * (8 - x5)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (x6 - 4) + 14.08 * (x4 - 4) + 3.52 * (x5 - 4) * (x6 - 4)
          + 4.1301056 * (x4 - 4) * (x5 - 4) + 8 * (x3 - 5.76) * (x4 - 4)
          + 8 * (x1 - 6.0650528) * (x6 - 4) + 2 * (x3 - 5.76) * (x5 - 4) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x4 - 4) * (x5 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 5.76 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx5 gx6), (mul_nonneg gx4 gx5), (mul_nonneg gx3 gx4), (mul_nonneg gx1 gx6), (mul_nonneg (mul_nonneg gx3 gx5) gx6), (mul_nonneg (mul_nonneg gx1 gx4) gx5)]
  have hA : (0:ℝ) ≤ x5 * (8 - x5) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (x6 - 4) + 14.08 * (x4 - 4) + 3.52 * (x5 - 4) * (x6 - 4) + 4.1301056 * (x4 - 4) * (x5 - 4) + 8 * (x3 - 5.76) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x6 - 4) + 2 * (x3 - 5.76) * (x5 - 4) * (x6 - 4) + 2 * (x1 - 6.0650528) * (x4 - 4) * (x5 - 4)) + (x5 * (8 - x5)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem H_mono_3 (a b x1 x2 x4 x5 x6 : ℝ)
    (ha : (5.76:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064) (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 x2 a x4 x5 x6 - 8 * deltaX x1 x2 a x4 x5 x6 ≤
      rhoX x1 x2 b x4 x5 x6 - 8 * deltaX x1 x2 b x4 x5 x6 := by
  have hid : (rhoX x1 x2 b x4 x5 x6 - 8 * deltaX x1 x2 b x4 x5 x6) -
      (rhoX x1 x2 a x4 x5 x6 - 8 * deltaX x1 x2 a x4 x5 x6)
      = (b - a) * ((14.08 * (8 - x6) + 3.52 * (x6 - 4) * (8 - x6) + 16.5204224 * (x5 - 4))
                  + 4.1301056 * (x4 - 4) * (x6 - 4) + 8 * (x2 - 4) * (x4 - 4)
                  + 8 * (x1 - 6.0650528) * (x5 - 4) + 2 * (x2 - 4) * (x5 - 4) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x4 - 4) * (x6 - 4)
        + (x6 * (8 - x6)) * (a + b - 2 * 5.76)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 14.08 * (8 - x6) + 3.52 * (x6 - 4) * (8 - x6) + 16.5204224 * (x5 - 4)
          + 4.1301056 * (x4 - 4) * (x6 - 4) + 8 * (x2 - 4) * (x4 - 4)
          + 8 * (x1 - 6.0650528) * (x5 - 4) + 2 * (x2 - 4) * (x5 - 4) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x4 - 4) * (x6 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have gv : (0:ℝ) ≤ (8 - x6) := by linarith
    nlinarith [(mul_nonneg gx6 gv), (mul_nonneg gx4 gx6), (mul_nonneg gx2 gx4), (mul_nonneg gx1 gx5), (mul_nonneg (mul_nonneg gx2 gx5) gx6), (mul_nonneg (mul_nonneg gx1 gx4) gx6)]
  have hA : (0:ℝ) ≤ x6 * (8 - x6) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 5.76 := by linarith
  have hfac : (0:ℝ) ≤ (14.08 * (8 - x6) + 3.52 * (x6 - 4) * (8 - x6) + 16.5204224 * (x5 - 4) + 4.1301056 * (x4 - 4) * (x6 - 4) + 8 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x5 - 4) + 2 * (x2 - 4) * (x5 - 4) * (x6 - 4) + 2 * (x1 - 6.0650528) * (x4 - 4) * (x6 - 4)) + (x6 * (8 - x6)) * (a + b - 2 * 5.76) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem H_mono_4 (a b x1 x2 x3 x5 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064) (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (5.76:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 a x5 x6 - 8 * deltaX x1 x2 x3 a x5 x6 ≤
      rhoX x1 x2 x3 b x5 x6 - 8 * deltaX x1 x2 x3 b x5 x6 := by
  have hid : (rhoX x1 x2 x3 b x5 x6 - 8 * deltaX x1 x2 x3 b x5 x6) -
      (rhoX x1 x2 x3 a x5 x6 - 8 * deltaX x1 x2 x3 a x5 x6)
      = (b - a) * ((7.268985856 * (x6 - 4) + 14.08 * (x2 - 4) + 8 * (x5 - 4) * (x6 - 4))
                  + 4.1301056 * (x3 - 5.76) * (x6 - 4) + 4.1301056 * (x2 - 4) * (x5 - 4)
                  + 8 * (x2 - 4) * (x3 - 5.76) + 3.52 * (x1 - 6.0650528) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x3 - 5.76) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x2 - 4) * (x5 - 4)
        + (x1 * (8 - x1)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 7.268985856 * (x6 - 4) + 14.08 * (x2 - 4) + 8 * (x5 - 4) * (x6 - 4)
          + 4.1301056 * (x3 - 5.76) * (x6 - 4) + 4.1301056 * (x2 - 4) * (x5 - 4)
          + 8 * (x2 - 4) * (x3 - 5.76) + 3.52 * (x1 - 6.0650528) * (x6 - 4)
          + 2 * (x1 - 6.0650528) * (x3 - 5.76) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x2 - 4) * (x5 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 5.76 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx5 gx6), (mul_nonneg gx3 gx6), (mul_nonneg gx2 gx5), (mul_nonneg gx2 gx3), (mul_nonneg gx1 gx6), (mul_nonneg (mul_nonneg gx1 gx3) gx6), (mul_nonneg (mul_nonneg gx1 gx2) gx5)]
  have hA : (0:ℝ) ≤ x1 * (8 - x1) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (7.268985856 * (x6 - 4) + 14.08 * (x2 - 4) + 8 * (x5 - 4) * (x6 - 4) + 4.1301056 * (x3 - 5.76) * (x6 - 4) + 4.1301056 * (x2 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x3 - 5.76) + 3.52 * (x1 - 6.0650528) * (x6 - 4) + 2 * (x1 - 6.0650528) * (x3 - 5.76) * (x6 - 4) + 2 * (x1 - 6.0650528) * (x2 - 4) * (x5 - 4)) + (x1 * (8 - x1)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem H_mono_5 (a b x1 x2 x3 x4 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064) (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (5.76:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 x4 a x6 - 8 * deltaX x1 x2 x3 x4 a x6 ≤
      rhoX x1 x2 x3 x4 b x6 - 8 * deltaX x1 x2 x3 x4 b x6 := by
  have hid : (rhoX x1 x2 x3 x4 b x6 - 8 * deltaX x1 x2 x3 x4 b x6) -
      (rhoX x1 x2 x3 x4 a x6 - 8 * deltaX x1 x2 x3 x4 a x6)
      = (b - a) * ((29.075943424 + 16.5204224 * (x3 - 5.76) + 14.08 * (x1 - 6.0650528))
                  + 8 * (x4 - 4) * (x6 - 4) + 3.52 * (x2 - 4) * (x6 - 4)
                  + 4.1301056 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x3 - 5.76)
                  + 2 * (x2 - 4) * (x3 - 5.76) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x2 - 4) * (x4 - 4)
        + (x2 * (8 - x2)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 29.075943424 + 16.5204224 * (x3 - 5.76) + 14.08 * (x1 - 6.0650528)
          + 8 * (x4 - 4) * (x6 - 4) + 3.52 * (x2 - 4) * (x6 - 4)
          + 4.1301056 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x3 - 5.76)
          + 2 * (x2 - 4) * (x3 - 5.76) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x2 - 4) * (x4 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 5.76 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx4 gx6), (mul_nonneg gx2 gx6), (mul_nonneg gx2 gx4), (mul_nonneg gx1 gx3), (mul_nonneg (mul_nonneg gx2 gx3) gx6), (mul_nonneg (mul_nonneg gx1 gx2) gx4)]
  have hA : (0:ℝ) ≤ x2 * (8 - x2) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (29.075943424 + 16.5204224 * (x3 - 5.76) + 14.08 * (x1 - 6.0650528) + 8 * (x4 - 4) * (x6 - 4) + 3.52 * (x2 - 4) * (x6 - 4) + 4.1301056 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x3 - 5.76) + 2 * (x2 - 4) * (x3 - 5.76) * (x6 - 4) + 2 * (x1 - 6.0650528) * (x2 - 4) * (x4 - 4)) + (x2 * (8 - x2)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem H_mono_6 (a b x1 x2 x3 x4 x5 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064) (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (5.76:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) :
    rhoX x1 x2 x3 x4 x5 a - 8 * deltaX x1 x2 x3 x4 x5 a ≤
      rhoX x1 x2 x3 x4 x5 b - 8 * deltaX x1 x2 x3 x4 x5 b := by
  have hid : (rhoX x1 x2 x3 x4 x5 b - 8 * deltaX x1 x2 x3 x4 x5 b) -
      (rhoX x1 x2 x3 x4 x5 a - 8 * deltaX x1 x2 x3 x4 x5 a)
      = (b - a) * ((7.268985856 * (x4 - 4) + 16.5204224 * (x2 - 4) + 8 * (x4 - 4) * (x5 - 4))
                  + 4.1301056 * (x3 - 5.76) * (x4 - 4) + 3.52 * (x2 - 4) * (x5 - 4)
                  + 3.52 * (x1 - 6.0650528) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x2 - 4)
                  + 2 * (x2 - 4) * (x3 - 5.76) * (x5 - 4)
                  + 2 * (x1 - 6.0650528) * (x3 - 5.76) * (x4 - 4)
        + (x3 * (8 - x3)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 7.268985856 * (x4 - 4) + 16.5204224 * (x2 - 4) + 8 * (x4 - 4) * (x5 - 4)
          + 4.1301056 * (x3 - 5.76) * (x4 - 4) + 3.52 * (x2 - 4) * (x5 - 4)
          + 3.52 * (x1 - 6.0650528) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x2 - 4)
          + 2 * (x2 - 4) * (x3 - 5.76) * (x5 - 4)
                + 2 * (x1 - 6.0650528) * (x3 - 5.76) * (x4 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 5.76 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    nlinarith [(mul_nonneg gx4 gx5), (mul_nonneg gx3 gx4), (mul_nonneg gx2 gx5), (mul_nonneg gx1 gx4), (mul_nonneg gx1 gx2), (mul_nonneg (mul_nonneg gx2 gx3) gx5), (mul_nonneg (mul_nonneg gx1 gx3) gx4)]
  have hA : (0:ℝ) ≤ x3 * (8 - x3) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (7.268985856 * (x4 - 4) + 16.5204224 * (x2 - 4) + 8 * (x4 - 4) * (x5 - 4) + 4.1301056 * (x3 - 5.76) * (x4 - 4) + 3.52 * (x2 - 4) * (x5 - 4) + 3.52 * (x1 - 6.0650528) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x2 - 4) + 2 * (x2 - 4) * (x3 - 5.76) * (x5 - 4) + 2 * (x1 - 6.0650528) * (x3 - 5.76) * (x4 - 4)) + (x3 * (8 - x3)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]


/-- W2-1: `nliRestQITNPEA1_2_2` (rad2 branch; `QITNPEA1` i3=i4=2). -/
theorem nliRestQITNPEA1_2_2 : bank_QITNPEA1_2_2 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hplus ≤ y3 := by simpa [bank_QITNPEA1lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_QITNPEA1hi] using h3h
  have h4l' : 2 * hplus ≤ y4 := by simpa [bank_QITNPEA1lo] using h4l
  have h4h' : y4 ≤ Real.sqrt 8 := by simpa [bank_QITNPEA1hi] using h4h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (7.02674064:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hplus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (7.02674064:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hplus y4 h4l'
    linarith
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith [mi_hminus_prop.1]) h4h'
  have hx5l : (4:ℝ) ≤ y5*y5 := sq_ge_4 y5 h5l
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith) (le_sqrt8 y5 h5h)
  have hx6l : (4:ℝ) ≤ y6*y6 := sq_ge_4 y6 h6l
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith) (le_sqrt8 y6 h6h)
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 4 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 4 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 7.02674064 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 4 4 (by norm_num : (4:ℝ) ≤ (7.02674064:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 7.02674064 (y3*y3) (y1*y1) (y2*y2) 7.02674064 4 4 (by norm_num : (5.76:ℝ) ≤ (7.02674064:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 7.02674064 7.02674064 4 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 7.02674064 7.02674064 4 4 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have hcorner : (66:ℝ) ≤ rhoX 6.0650528 4 7.02674064 7.02674064 4 4 - 8 * deltaX 6.0650528 4 7.02674064 7.02674064 4 4 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W2-1: `nliRestQITNPEA1_2_1` (rad2 branch; W2-0 unlock, i3=2 i4=1). -/
theorem nliRestQITNPEA1_2_1 : bank_QITNPEA1_2_1 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hplus ≤ y3 := by simpa [bank_QITNPEA1lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_QITNPEA1hi] using h3h
  have h4l' : 2 * hminus ≤ y4 := by simpa [bank_QITNPEA1lo] using h4l
  have h4h' : y4 ≤ 2 * hplus := by simpa [bank_QITNPEA1hi] using h4h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (7.02674064:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hplus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (6.0650528:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hminus y4 h4l'
    linarith
  have hx4h : y4*y4 ≤ 7.02674064 := sq_le_hplus y4 (by linarith [mi_hminus_prop.1, h4l']) h4h'
  have hx5l : (4:ℝ) ≤ y5*y5 := sq_ge_4 y5 h5l
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith) (le_sqrt8 y5 h5h)
  have hx6l : (4:ℝ) ≤ y6*y6 := sq_ge_4 y6 h6l
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith) (le_sqrt8 y6 h6h)
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have hx4H : y4*y4 ≤ 8 := by linarith [hx4h]
  have s6 := H_mono_6 4 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4H hx5w hx5h
  have s5 := H_mono_5 4 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4H (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 6.0650528 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 4 4 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx4l hx4H
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 7.02674064 (y3*y3) (y1*y1) (y2*y2) 6.0650528 4 4 (by norm_num : (5.76:ℝ) ≤ (7.02674064:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 7.02674064 6.0650528 4 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 7.02674064 6.0650528 4 4 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (7.02674064:ℝ)) (by norm_num : (7.02674064:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have hcorner : (8:ℝ) ≤ rhoX 6.0650528 4 7.02674064 6.0650528 4 4 - 8 * deltaX 6.0650528 4 7.02674064 6.0650528 4 4 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4H (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W2-1: `nliRestMKFKQWU` (rad2 branch). -/
theorem nliRestMKFKQWU : bank_MKFKQWU := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (6.0650528:ℝ) ≤ y2*y2 := by
    have h := sq_ge_hminus y2 h2l
    linarith
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith [mi_hminus_prop.1]) h2h
  have hx3l : (6.0650528:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hminus y3 h3l
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h
  have hx4l : (4:ℝ) ≤ y4*y4 := sq_ge_4 y4 h4l
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith) h4h
  have hx5l : (6.0650528:ℝ) ≤ y5*y5 := by
    have h := sq_ge_hminus y5 h5l
    linarith
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith [mi_hminus_prop.1]) h5h
  have hx6l : (6.0650528:ℝ) ≤ y6*y6 := by
    have h := sq_ge_hminus y6 h6l
    linarith
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith [mi_hminus_prop.1]) h6h
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 6.0650528 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 6.0650528 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 6.0650528 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 4 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 6.0650528 6.0650528 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 6.0650528 (y3*y3) (y1*y1) (y2*y2) 4 6.0650528 6.0650528 (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 6.0650528 (y2*y2) (y1*y1) 6.0650528 4 6.0650528 6.0650528 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 6.0650528 6.0650528 4 6.0650528 6.0650528 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have hcorner : (226:ℝ) ≤ rhoX 6.0650528 6.0650528 6.0650528 4 6.0650528 6.0650528 - 8 * deltaX 6.0650528 6.0650528 6.0650528 4 6.0650528 6.0650528 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

#print axioms Kepler.NliBanks3.nliRestQITNPEA1_2_2
#print axioms Kepler.NliBanks3.nliRestQITNPEA1_2_1
#print axioms Kepler.NliBanks3.nliRestMKFKQWU

end Kepler.NliBanks3
