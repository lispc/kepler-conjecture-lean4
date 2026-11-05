import Kepler.NliBanks3

/-!
Kepler.NliBanks5 — W3 lane `nli-unknown-w3`, tasks 1–2.

Two `rad2` banks whose `y3`-slot is subcritical (`x3` down to `4`, not
`5.76`):

* `nliRestMKFKQWUhalfwt` (box `[2hmin,2hplus]×[2hplus,√8]×[2,√8]×[2hmin,√8]×[2,√8]²`)
* `nliRestZTGIJCF4_0_1_1_1` (`ZTGIJCF4 0 1 1 1`)

Same `H = rhoX − 8·deltaX` corner kit as `Kepler.NliBanks3/4`, but the
axis monotonicity lemmas are stated on the wider box `x3 ≥ 4`: the constants
`14.08 = 8·1.76` and `3.52 = 2·1.76` in the `H_mono` identities absorb the
`x3 − 5.76` terms exactly, leaving only `x3 − 4`.  Corner values are exact
rational `norm_num` checks (`t1 = 69.189…`, `t2 = 8.855…`).  No certificates,
no `sorry`/`axiom`/`native_decide`.
-/

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks5
open Kepler.Text
open Kepler.NliBanks3
open Kepler.NliHminus

/-! ## Wide axis monotonicity (`x3 ≥ 4` instead of `5.76`) -/

theorem HW_1 (a b x2 x3 x4 x5 x6 : ℝ)
    (ha : (6.0650528:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8)
    (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX a x2 x3 x4 x5 x6 - 8 * deltaX a x2 x3 x4 x5 x6 ≤
      rhoX b x2 x3 x4 x5 x6 - 8 * deltaX b x2 x3 x4 x5 x6 := by
  have hid : (rhoX b x2 x3 x4 x5 x6 - 8 * deltaX b x2 x3 x4 x5 x6) -
      (rhoX a x2 x3 x4 x5 x6 - 8 * deltaX a x2 x3 x4 x5 x6)
      = (b - a) * ((16.5204224 * (8 - x4) + 4.1301056 * (x4 - 4) * (8 - x4))
                  + 8 * (x3 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x6 - 4)
                  + 2 * (x3 - 4) * (x4 - 4) * (x6 - 4)
                  + 2 * (x2 - 4) * (x4 - 4) * (x5 - 4)
        + (x4 * (8 - x4)) * (a + b - 2 * 6.0650528)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (8 - x4) + 4.1301056 * (x4 - 4) * (8 - x4)
          + 8 * (x3 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x6 - 4)
          + 2 * (x3 - 4) * (x4 - 4) * (x6 - 4)
                + 2 * (x2 - 4) * (x4 - 4) * (x5 - 4) := by
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have gv : (0:ℝ) ≤ (8 - x4) := by linarith
    nlinarith [(mul_nonneg gx4 gv), (mul_nonneg gx3 gx5), (mul_nonneg gx2 gx6),
      (mul_nonneg gx4 gx6), (mul_nonneg (mul_nonneg gx3 gx4) gx6),
      (mul_nonneg (mul_nonneg gx2 gx4) gx5)]
  have hA : (0:ℝ) ≤ x4 * (8 - x4) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 6.0650528 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (8 - x4) + 4.1301056 * (x4 - 4) * (8 - x4)
          + 8 * (x3 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x6 - 4)
          + 2 * (x3 - 4) * (x4 - 4) * (x6 - 4)
          + 2 * (x2 - 4) * (x4 - 4) * (x5 - 4))
        + (x4 * (8 - x4)) * (a + b - 2 * 6.0650528) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem HW_2 (a b x1 x3 x4 x5 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8)
    (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 a x3 x4 x5 x6 - 8 * deltaX x1 a x3 x4 x5 x6 ≤
      rhoX x1 b x3 x4 x5 x6 - 8 * deltaX x1 b x3 x4 x5 x6 := by
  have hid : (rhoX x1 b x3 x4 x5 x6 - 8 * deltaX x1 b x3 x4 x5 x6) -
      (rhoX x1 a x3 x4 x5 x6 - 8 * deltaX x1 a x3 x4 x5 x6)
      = (b - a) * ((16.5204224 * (x6 - 4) + 4.1301056 * (x4 - 4) * (x5 - 4))
                  + 8 * (x3 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x6 - 4)
                  + 2 * (x3 - 4) * (x5 - 4) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x4 - 4) * (x5 - 4)
        + (x5 * (8 - x5)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (x6 - 4) + 4.1301056 * (x4 - 4) * (x5 - 4)
          + 8 * (x3 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x6 - 4)
          + 2 * (x3 - 4) * (x5 - 4) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x4 - 4) * (x5 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx4 gx5), (mul_nonneg gx3 gx4), (mul_nonneg gx1 gx6),
      (mul_nonneg (mul_nonneg gx3 gx5) gx6), (mul_nonneg (mul_nonneg gx1 gx4) gx5)]
  have hA : (0:ℝ) ≤ x5 * (8 - x5) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (x6 - 4) + 4.1301056 * (x4 - 4) * (x5 - 4)
          + 8 * (x3 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x6 - 4)
          + 2 * (x3 - 4) * (x5 - 4) * (x6 - 4)
          + 2 * (x1 - 6.0650528) * (x4 - 4) * (x5 - 4))
        + (x5 * (8 - x5)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem HW_3 (a b x1 x2 x4 x5 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8)
    (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 x2 a x4 x5 x6 - 8 * deltaX x1 x2 a x4 x5 x6 ≤
      rhoX x1 x2 b x4 x5 x6 - 8 * deltaX x1 x2 b x4 x5 x6 := by
  have hid : (rhoX x1 x2 b x4 x5 x6 - 8 * deltaX x1 x2 b x4 x5 x6) -
      (rhoX x1 x2 a x4 x5 x6 - 8 * deltaX x1 x2 a x4 x5 x6)
      = (b - a) * ((16.5204224 * (x5 - 4) + 4.1301056 * (x4 - 4) * (x6 - 4))
                  + 8 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x5 - 4)
                  + 2 * (x2 - 4) * (x5 - 4) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x4 - 4) * (x6 - 4)
        + (x6 * (8 - x6)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (x5 - 4) + 4.1301056 * (x4 - 4) * (x6 - 4)
          + 8 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x5 - 4)
          + 2 * (x2 - 4) * (x5 - 4) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x4 - 4) * (x6 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx4 gx6), (mul_nonneg gx2 gx4), (mul_nonneg gx1 gx5),
      (mul_nonneg (mul_nonneg gx2 gx5) gx6), (mul_nonneg (mul_nonneg gx1 gx4) gx6)]
  have hA : (0:ℝ) ≤ x6 * (8 - x6) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (x5 - 4) + 4.1301056 * (x4 - 4) * (x6 - 4)
          + 8 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x5 - 4)
          + 2 * (x2 - 4) * (x5 - 4) * (x6 - 4)
          + 2 * (x1 - 6.0650528) * (x4 - 4) * (x6 - 4))
        + (x6 * (8 - x6)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem HW_4 (a b x1 x2 x3 x5 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 a x5 x6 - 8 * deltaX x1 x2 x3 a x5 x6 ≤
      rhoX x1 x2 x3 b x5 x6 - 8 * deltaX x1 x2 x3 b x5 x6 := by
  have hid : (rhoX x1 x2 x3 b x5 x6 - 8 * deltaX x1 x2 x3 b x5 x6) -
      (rhoX x1 x2 x3 a x5 x6 - 8 * deltaX x1 x2 x3 a x5 x6)
      = (b - a) * (8 * (x5 - 4) * (x6 - 4) + 4.1301056 * (x3 - 4) * (x6 - 4)
                  + 4.1301056 * (x2 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x3 - 4)
                  + 2 * (x1 - 6.0650528) * (x3 - 4) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x2 - 4) * (x5 - 4)
        + (x1 * (8 - x1)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 8 * (x5 - 4) * (x6 - 4) + 4.1301056 * (x3 - 4) * (x6 - 4)
          + 4.1301056 * (x2 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x3 - 4)
          + 2 * (x1 - 6.0650528) * (x3 - 4) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x2 - 4) * (x5 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx5 gx6), (mul_nonneg gx3 gx6), (mul_nonneg gx2 gx5),
      (mul_nonneg gx2 gx3), (mul_nonneg (mul_nonneg gx1 gx3) gx6),
      (mul_nonneg (mul_nonneg gx1 gx2) gx5)]
  have hA : (0:ℝ) ≤ x1 * (8 - x1) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (8 * (x5 - 4) * (x6 - 4) + 4.1301056 * (x3 - 4) * (x6 - 4)
          + 4.1301056 * (x2 - 4) * (x5 - 4) + 8 * (x2 - 4) * (x3 - 4)
          + 2 * (x1 - 6.0650528) * (x3 - 4) * (x6 - 4)
          + 2 * (x1 - 6.0650528) * (x2 - 4) * (x5 - 4))
        + (x1 * (8 - x1)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem HW_5 (a b x1 x2 x3 x4 x6 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 x4 a x6 - 8 * deltaX x1 x2 x3 x4 a x6 ≤
      rhoX x1 x2 x3 x4 b x6 - 8 * deltaX x1 x2 x3 x4 b x6 := by
  have hid : (rhoX x1 x2 x3 x4 b x6 - 8 * deltaX x1 x2 x3 x4 b x6) -
      (rhoX x1 x2 x3 x4 a x6 - 8 * deltaX x1 x2 x3 x4 a x6)
      = (b - a) * (16.5204224 * (x3 - 4) + 8 * (x4 - 4) * (x6 - 4)
                  + 4.1301056 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x3 - 4)
                  + 2 * (x2 - 4) * (x3 - 4) * (x6 - 4)
                  + 2 * (x1 - 6.0650528) * (x2 - 4) * (x4 - 4)
        + (x2 * (8 - x2)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (x3 - 4) + 8 * (x4 - 4) * (x6 - 4)
          + 4.1301056 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x3 - 4)
          + 2 * (x2 - 4) * (x3 - 4) * (x6 - 4)
                + 2 * (x1 - 6.0650528) * (x2 - 4) * (x4 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx6 : (0:ℝ) ≤ x6 - 4 := by linarith
    nlinarith [(mul_nonneg gx4 gx6), (mul_nonneg gx2 gx4), (mul_nonneg gx1 gx3),
      (mul_nonneg (mul_nonneg gx2 gx3) gx6), (mul_nonneg (mul_nonneg gx1 gx2) gx4)]
  have hA : (0:ℝ) ≤ x2 * (8 - x2) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (x3 - 4) + 8 * (x4 - 4) * (x6 - 4)
          + 4.1301056 * (x2 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x3 - 4)
          + 2 * (x2 - 4) * (x3 - 4) * (x6 - 4)
          + 2 * (x1 - 6.0650528) * (x2 - 4) * (x4 - 4))
        + (x2 * (8 - x2)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem HW_6 (a b x1 x2 x3 x4 x5 : ℝ)
    (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ))
    (h1 : (6.0650528:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) :
    rhoX x1 x2 x3 x4 x5 a - 8 * deltaX x1 x2 x3 x4 x5 a ≤
      rhoX x1 x2 x3 x4 x5 b - 8 * deltaX x1 x2 x3 x4 x5 b := by
  have hid : (rhoX x1 x2 x3 x4 x5 b - 8 * deltaX x1 x2 x3 x4 x5 b) -
      (rhoX x1 x2 x3 x4 x5 a - 8 * deltaX x1 x2 x3 x4 x5 a)
      = (b - a) * (16.5204224 * (x2 - 4) + 8 * (x4 - 4) * (x5 - 4)
                  + 4.1301056 * (x3 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x2 - 4)
                  + 2 * (x2 - 4) * (x3 - 4) * (x5 - 4)
                  + 2 * (x1 - 6.0650528) * (x3 - 4) * (x4 - 4)
        + (x3 * (8 - x3)) * (a + b - 2 * 4)) := by
    unfold rhoX deltaX; ring
  have hG : (0:ℝ) ≤ 16.5204224 * (x2 - 4) + 8 * (x4 - 4) * (x5 - 4)
          + 4.1301056 * (x3 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x2 - 4)
          + 2 * (x2 - 4) * (x3 - 4) * (x5 - 4)
                + 2 * (x1 - 6.0650528) * (x3 - 4) * (x4 - 4) := by
    have gx1 : (0:ℝ) ≤ x1 - 6.0650528 := by linarith
    have gx2 : (0:ℝ) ≤ x2 - 4 := by linarith
    have gx3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have gx4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have gx5 : (0:ℝ) ≤ x5 - 4 := by linarith
    nlinarith [(mul_nonneg gx4 gx5), (mul_nonneg gx3 gx4), (mul_nonneg gx1 gx2),
      (mul_nonneg (mul_nonneg gx2 gx3) gx5), (mul_nonneg (mul_nonneg gx1 gx3) gx4)]
  have hA : (0:ℝ) ≤ x3 * (8 - x3) := by nlinarith
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hsum : (0:ℝ) ≤ a + b - 2 * 4 := by linarith
  have hfac : (0:ℝ) ≤ (16.5204224 * (x2 - 4) + 8 * (x4 - 4) * (x5 - 4)
          + 4.1301056 * (x3 - 4) * (x4 - 4) + 8 * (x1 - 6.0650528) * (x2 - 4)
          + 2 * (x2 - 4) * (x3 - 4) * (x5 - 4)
          + 2 * (x1 - 6.0650528) * (x3 - 4) * (x4 - 4))
        + (x3 * (8 - x3)) * (a + b - 2 * 4) := by
    linarith [hG, mul_nonneg hA hsum]
  nlinarith [mul_nonneg hba hfac]

theorem dX_box_ge_wide (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 6.0650528 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (50:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 6.0650528 x2 x3 x4 x5 x6) (deltaX 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 6.0650528 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

/-- W3-2: `nliRestMKFKQWUhalfwt` (rad2 branch; `y2` critical, `y3` subcritical). -/
theorem nliRestMKFKQWUhalfwt : bank_MKFKQWUhalfwt := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hp : hplus = 1.3254 := rfl
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (7.02674064:ℝ) ≤ y2*y2 := by
    have h := sq_ge_hplus y2 h2l
    linarith
  have hy2 : (0:ℝ) ≤ y2 := by rw [hp] at h2l; linarith
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 hy2 h2h
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3l : (4:ℝ) ≤ y3*y3 := sq_ge_4 y3 h3l
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith) h3h
  have hx4l : (6.0650528:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hminus y4 h4l
    linarith
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith [mi_hminus_prop.1]) h4h
  have hx5l : (4:ℝ) ≤ y5*y5 := sq_ge_4 y5 h5l
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith) h5h
  have hx6l : (4:ℝ) ≤ y6*y6 := sq_ge_4 y6 h6l
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith) h6h
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have s6 := HW_6 4 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5)
    (by norm_num : (4:ℝ) ≤ 4) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3l hx3h hx4w hx4h hx5l hx5h
  have s5 := HW_5 4 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 4
    (by norm_num : (4:ℝ) ≤ 4) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3l hx3h hx4w hx4h
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
  have s4 := HW_4 6.0650528 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 4 4
    (by norm_num : (4:ℝ) ≤ 6.0650528) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3l hx3h
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
  have s3 := HW_3 4 (y3*y3) (y1*y1) (y2*y2) 6.0650528 4 4
    (by norm_num : (4:ℝ) ≤ 4) hx3l hx3h
    hx1l hx1h hx2w hx2h
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
  have s2 := HW_2 7.02674064 (y2*y2) (y1*y1) 4 6.0650528 4 4
    (by norm_num : (4:ℝ) ≤ 7.02674064) hx2l hx2h
    hx1l hx1h (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
  have s1 := HW_1 6.0650528 (y1*y1) 7.02674064 4 6.0650528 4 4
    (by norm_num : (6.0650528:ℝ) ≤ 6.0650528) hx1l (by linarith [hx1h])
    (by norm_num : (4:ℝ) ≤ 7.02674064) (by norm_num : (7.02674064:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
  have hcorner : (8:ℝ) ≤ rhoX 6.0650528 7.02674064 4 6.0650528 4 4 -
      8 * deltaX 6.0650528 7.02674064 4 6.0650528 4 4 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge_wide _ _ _ _ _ _ hx1l hx1h hx2w hx2h hx3l hx3h hx4w hx4h hx5l hx5h hx6l hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W3-1: `nliRestZTGIJCF4_0_1_1_1` (rad2 branch; `y3` subcritical). -/
theorem nliRestZTGIJCF4_0_1_1_1 : bank_ZTGIJCF4_0_1_1_1 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : (2:ℝ) ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : 2 * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : 2 * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : 2 * hminus ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h6h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (4:ℝ) ≤ y3*y3 := sq_ge_4 y3 h3l'
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith) (le_sqrt8 y3 h3h')
  have hx4l : (6.0650528:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hminus y4 h4l'
    linarith
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith [mi_hminus_prop.1]) h4h'
  have hx5l : (6.0650528:ℝ) ≤ y5*y5 := by
    have h := sq_ge_hminus y5 h5l'
    linarith
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith [mi_hminus_prop.1]) h5h'
  have hx6l : (6.0650528:ℝ) ≤ y6*y6 := by
    have h := sq_ge_hminus y6 h6l'
    linarith
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith [mi_hminus_prop.1]) h6h'
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := HW_6 6.0650528 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5)
    (by norm_num : (4:ℝ) ≤ 6.0650528) hx6l hx6h
    hx1l hx1h hx2l hx2h hx3l hx3h hx4w hx4h hx5w hx5h
  have s5 := HW_5 6.0650528 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 6.0650528
    (by norm_num : (4:ℝ) ≤ 6.0650528) hx5l hx5h
    hx1l hx1h hx2l hx2h hx3l hx3h hx4w hx4h
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
  have s4 := HW_4 6.0650528 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 6.0650528 6.0650528
    (by norm_num : (4:ℝ) ≤ 6.0650528) hx4l hx4h
    hx1l hx1h hx2l hx2h hx3l hx3h
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
  have s3 := HW_3 4 (y3*y3) (y1*y1) (y2*y2) 6.0650528 6.0650528 6.0650528
    (by norm_num : (4:ℝ) ≤ 4) hx3l hx3h
    hx1l hx1h hx2l hx2h
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
  have s2 := HW_2 4 (y2*y2) (y1*y1) 4 6.0650528 6.0650528 6.0650528
    (by norm_num : (4:ℝ) ≤ 4) hx2l hx2h
    hx1l hx1h (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
  have s1 := HW_1 6.0650528 (y1*y1) 4 4 6.0650528 6.0650528 6.0650528
    (by norm_num : (6.0650528:ℝ) ≤ 6.0650528) hx1l (by linarith [hx1h])
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 4) (by norm_num : (4:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
    (by norm_num : (4:ℝ) ≤ 6.0650528) (by norm_num : (6.0650528:ℝ) ≤ 8)
  have hcorner : (69:ℝ) ≤ rhoX 6.0650528 4 4 6.0650528 6.0650528 6.0650528 -
      8 * deltaX 6.0650528 4 4 6.0650528 6.0650528 6.0650528 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge_wide _ _ _ _ _ _ hx1l hx1h hx2l hx2h hx3l hx3h hx4w hx4h hx5w hx5h hx6w hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

#print axioms Kepler.NliBanks5.nliRestMKFKQWUhalfwt
#print axioms Kepler.NliBanks5.nliRestZTGIJCF4_0_1_1_1

end Kepler.NliBanks5
