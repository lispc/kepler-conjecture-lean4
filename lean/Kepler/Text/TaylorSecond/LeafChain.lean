/-
Kepler.Text.TaylorSecond.LeafChain — lane `wt1-full-emission-w1` (2026-11-24).

Corner-pairing kit for the generated single-box `w1F2` D11 chains
(continuation of `LeafKit`, `fc1625d7`).

Measured design (this lane): among the corner-paired slots of the reference
evaluator, only `w1Dlt` *must* be corner-paired — with `Dlt` paired and all
other slots (`aA/aB/aC`, `d4A/d4C`, derivative slots) as pure `QInterval`
ops, the eight uniform sub-boxes of terminal `15874/LLLLRLRLR` all close
(`D11.hi ∈ [-0.0153, -0.0120]`; see `scripts/leaf_eval_pure.py`).  Hence this
file only carries the `w1Dlt` monotonicity lemmas.

`w1Dlt` is multi-affine in the three squared coordinates with a negative
cross term `x4 x5 x6`, and `∂w1Dlt/∂xi = -4 xi + 4 (xj + xk) - xj xk < 0`
on the wt1 domain (`y ≥ 2`, i.e. `x ≥ 4`): each coordinate is decreasing, so
the low corner is the max and the high corner is the min.  The sign facts are
discharged at the *low corner* literals (valid on the whole box by bilinearity
of the cross term), so the emitted per-box calls are `norm_num` only.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.LeafKit

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-! ## `w1Dlt` coordinate monotonicity (difference factorisation) -/

theorem lk_Dlt_anti_y4 {a b y5 y6 : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hs : 4 * (y5 * y5) + 4 * (y6 * y6) - 2 * (a * a + b * b) - (y5 * y5) * (y6 * y6) ≤ 0) :
    w1Dlt b y5 y6 ≤ w1Dlt a y5 y6 := by
  unfold w1Dlt
  have hprod : 0 ≤ (b * b - a * a) * (2 * (a * a + b * b) - 4 * (y5 * y5) - 4 * (y6 * y6) + (y5 * y5) * (y6 * y6)) :=
    mul_nonneg (by nlinarith) (by linarith)
  nlinarith [hprod]

theorem lk_Dlt_anti_y5 {a b y4 y6 : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hs : 4 * (y4 * y4) + 4 * (y6 * y6) - 2 * (a * a + b * b) - (y4 * y4) * (y6 * y6) ≤ 0) :
    w1Dlt y4 b y6 ≤ w1Dlt y4 a y6 := by
  unfold w1Dlt
  have hprod : 0 ≤ (b * b - a * a) * (2 * (a * a + b * b) - 4 * (y4 * y4) - 4 * (y6 * y6) + (y4 * y4) * (y6 * y6)) :=
    mul_nonneg (by nlinarith) (by linarith)
  nlinarith [hprod]

theorem lk_Dlt_anti_y6 {a b y4 y5 : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a)
    (hs : 4 * (y4 * y4) + 4 * (y5 * y5) - 2 * (a * a + b * b) - (y4 * y4) * (y5 * y5) ≤ 0) :
    w1Dlt y4 y5 b ≤ w1Dlt y4 y5 a := by
  unfold w1Dlt
  have hprod : 0 ≤ (b * b - a * a) * (2 * (a * a + b * b) - 4 * (y4 * y4) - 4 * (y5 * y5) + (y4 * y4) * (y5 * y5)) :=
    mul_nonneg (by nlinarith) (by linarith)
  nlinarith [hprod]

/-! ## The three derivative-sign transfers at the low corner

For `x5 = y5² ≥ 4` and `x6 = y6² ≥ 4`,
`4 x5 + 4 x6 - x5 x6 - (4 x5c + 4 x6c - x5c x6c)
   = (x5 - x5c)(4 - x6) + (x6 - x6c)(4 - x5c) ≤ 0`,
so the sign at the low corner bounds the sign on the whole box. -/

theorem lk_Dlt_step_y4 (y4 y5 y6 y4c y5c y6c : ℝ)
    (h4c : y4c ≤ y4) (h4c0 : 0 ≤ y4c) (h5c : y5c ≤ y5) (h6c : y6c ≤ y6)
    (h52 : 2 ≤ y5c) (h62 : 2 ≤ y6c)
    (hs4 : -4 * (y4c * y4c) + 4 * (y5c * y5c) + 4 * (y6c * y6c) - (y5c * y5c) * (y6c * y6c) < 0) :
    4 * (y5 * y5) + 4 * (y6 * y6) - 2 * (y4c * y4c + y4 * y4) - (y5 * y5) * (y6 * y6) ≤ 0 := by
  have hA : (y5 * y5 - y5c * y5c) * (4 - y6 * y6) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  have hB : (y6 * y6 - y6c * y6c) * (4 - y5c * y5c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  nlinarith [hA, hB]

theorem lk_Dlt_step_y5 (y4 y5 y6 y4c y5c y6c : ℝ)
    (h4c : y4c ≤ y4) (h5c : y5c ≤ y5) (h5c0 : 0 ≤ y5c) (h6c : y6c ≤ y6)
    (h42 : 2 ≤ y4c) (h62 : 2 ≤ y6c)
    (hs5 : -4 * (y5c * y5c) + 4 * (y4c * y4c) + 4 * (y6c * y6c) - (y4c * y4c) * (y6c * y6c) < 0) :
    4 * (y4 * y4) + 4 * (y6 * y6) - 2 * (y5c * y5c + y5 * y5) - (y4 * y4) * (y6 * y6) ≤ 0 := by
  have hA : (y4 * y4 - y4c * y4c) * (4 - y6 * y6) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  have hB : (y6 * y6 - y6c * y6c) * (4 - y4c * y4c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  nlinarith [hA, hB]

theorem lk_Dlt_step_y6 (y4 y5 y6 y4c y5c y6c : ℝ)
    (h4c : y4c ≤ y4) (h5c : y5c ≤ y5) (h6c : y6c ≤ y6) (h6c0 : 0 ≤ y6c)
    (h42 : 2 ≤ y4c) (h52 : 2 ≤ y5c)
    (hs6 : -4 * (y6c * y6c) + 4 * (y4c * y4c) + 4 * (y5c * y5c) - (y4c * y4c) * (y5c * y5c) < 0) :
    4 * (y4 * y4) + 4 * (y5 * y5) - 2 * (y6c * y6c + y6 * y6) - (y4 * y4) * (y5 * y5) ≤ 0 := by
  have hA : (y4 * y4 - y4c * y4c) * (4 - y5 * y5) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  have hB : (y5 * y5 - y5c * y5c) * (4 - y4c * y4c) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by nlinarith)
  nlinarith [hA, hB]

/-! ## Corner lemmas -/

/-- **`w1Dlt` box enclosure from the two y-corners.**  The low corner gives
the maximum, the high corner the minimum, on the whole box; the three
derivative-sign facts are discharged at the *low* corner literals. -/
theorem lk_Dlt_mem (y4 y5 y6 y4lo y4hi y5lo y5hi y6lo y6hi : ℝ)
    (h4lo : y4lo ≤ y4) (h4hi : y4 ≤ y4hi) (h5lo : y5lo ≤ y5) (h5hi : y5 ≤ y5hi)
    (h6lo : y6lo ≤ y6) (h6hi : y6 ≤ y6hi)
    (hy4lo : 2 ≤ y4lo) (hy5lo : 2 ≤ y5lo) (hy6lo : 2 ≤ y6lo) (hy4hi : 2 ≤ y4hi)
    (hs4 : -4 * (y4lo * y4lo) + 4 * (y5lo * y5lo) + 4 * (y6lo * y6lo)
      - (y5lo * y5lo) * (y6lo * y6lo) < 0)
    (hs5 : -4 * (y5lo * y5lo) + 4 * (y4lo * y4lo) + 4 * (y6lo * y6lo)
      - (y4lo * y4lo) * (y6lo * y6lo) < 0)
    (hs6 : -4 * (y6lo * y6lo) + 4 * (y4lo * y4lo) + 4 * (y5lo * y5lo)
      - (y4lo * y4lo) * (y5lo * y5lo) < 0) :
    w1Dlt y4hi y5hi y6hi ≤ w1Dlt y4 y5 y6 ∧ w1Dlt y4 y5 y6 ≤ w1Dlt y4lo y5lo y6lo := by
  constructor
  · -- lower bound: walk from the high corner down to the point
    have s4 : w1Dlt y4hi y5hi y6hi ≤ w1Dlt y4 y5hi y6hi := by
      refine lk_Dlt_anti_y4 h4hi (by linarith : (0:ℝ) ≤ y4) ?_
      have h := lk_Dlt_step_y4 y4 y5hi y6hi y4lo y5lo y6lo h4lo (by linarith : (0:ℝ) ≤ y4lo)
        (by linarith : y5lo ≤ y5hi) (by linarith : y6lo ≤ y6hi) hy5lo hy6lo hs4
      nlinarith [h]
    have s5 : w1Dlt y4 y5hi y6hi ≤ w1Dlt y4 y5 y6hi := by
      refine lk_Dlt_anti_y5 h5hi (by linarith : (0:ℝ) ≤ y5) ?_
      have h := lk_Dlt_step_y5 y4 y5 y6hi y4lo y5lo y6lo (by linarith : y4lo ≤ y4) h5lo
        (by linarith : (0:ℝ) ≤ y5lo) (by linarith : y6lo ≤ y6hi) (by linarith : (2:ℝ) ≤ y4lo) hy6lo hs5
      nlinarith [h]
    have s6 : w1Dlt y4 y5 y6hi ≤ w1Dlt y4 y5 y6 := by
      refine lk_Dlt_anti_y6 h6hi (by linarith : (0:ℝ) ≤ y6) ?_
      have h := lk_Dlt_step_y6 y4 y5 y6 y4lo y5lo y6lo (by linarith : y4lo ≤ y4)
        (by linarith : y5lo ≤ y5) h6lo (by linarith : (0:ℝ) ≤ y6lo) (by linarith : (2:ℝ) ≤ y4lo) hy5lo hs6
      nlinarith [h]
    exact le_trans s4 (le_trans s5 s6)
  · -- upper bound: walk from the point down to the low corner
    have s4 : w1Dlt y4 y5 y6 ≤ w1Dlt y4lo y5 y6 :=
      lk_Dlt_anti_y4 h4lo (by linarith : (0:ℝ) ≤ y4lo)
        (lk_Dlt_step_y4 y4 y5 y6 y4lo y5lo y6lo h4lo (by linarith : (0:ℝ) ≤ y4lo) h5lo h6lo hy5lo hy6lo hs4)
    have s5 : w1Dlt y4lo y5 y6 ≤ w1Dlt y4lo y5lo y6 := by
      refine lk_Dlt_anti_y5 h5lo (by linarith : (0:ℝ) ≤ y5lo) ?_
      have h := lk_Dlt_step_y5 y4lo y5 y6 y4lo y5lo y6lo (le_refl y4lo) h5lo
        (by linarith : (0:ℝ) ≤ y5lo) h6lo (by linarith : (2:ℝ) ≤ y4lo) hy6lo hs5
      nlinarith [h]
    have s6 : w1Dlt y4lo y5lo y6 ≤ w1Dlt y4lo y5lo y6lo := by
      refine lk_Dlt_anti_y6 h6lo (by linarith : (0:ℝ) ≤ y6lo) ?_
      have h := lk_Dlt_step_y6 y4lo y5lo y6 y4lo y5lo y6lo (le_refl y4lo) (le_refl y5lo) h6lo
        (by linarith : (0:ℝ) ≤ y6lo) (by linarith : (2:ℝ) ≤ y4lo) hy5lo hs6
      nlinarith [h]
    exact le_trans s4 (le_trans s5 s6)

#print axioms lk_Dlt_anti_y4
#print axioms lk_Dlt_anti_y5
#print axioms lk_Dlt_anti_y6
#print axioms lk_Dlt_step_y4
#print axioms lk_Dlt_step_y5
#print axioms lk_Dlt_step_y6
#print axioms lk_Dlt_mem

end Kepler.Text.TaylorSecond
