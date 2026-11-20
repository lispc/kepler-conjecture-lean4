/-
Kepler.Text.Wt1TowerDomain — lane `cell3-wt1-tower-build-w2` (2026-11-20),
phase 2 of the wt1 second-order tower (route A′), gate 1:
the differentiability-domain hypotheses of phase 1 are discharged from the
box bounds, giving the assumption-free D1/D2.

Phase 1 (`Wt1TowerDeriv`) states `w1aF_hasDerivAt_y5` and
`w1aF_hasDerivAt2_y5` with, besides the box, six `-1 < t` / `-1 < g`
differentiability hypotheses and six nonvanishing slot denominators.
This file:

* removes the six nonvanishing hypotheses via the box-positivity lemmas
  `w1aA_pos`/`w1aB_pos`/`w1aC_pos`/`w1d4A_pos`/`w1d4B_pos`/`w1d4C_pos`;
* proves the six domain facts from the rational box
  `y4 ∈ [2.4635, 2.6508]`, `y5, y6 ∈ [2, 2.46352]`:
  - `-1 < t_A/B/C`: `t = Δ/(4a²)`, so `-1 < t ↔ 0 < 4a² + Δ`; the crude
    bounds `a ≥ 14` (`a² ≥ 196`) and `Δ ≥ -600` give `4a² + Δ ≥ 184 > 0`;
  - `-1 < g_A/B/C`: `g = 4y²Δ/d4²`, so `-1 < g ↔ 0 < d4² + 4y²Δ`; the
    exact factorisation
    `d4_A² + 4y5²Δ = y5²·(y5²-8)·(y4-y5-y6)(y4-y5+y6)(y4+y5-y6)(y4+y5+y6)`
    (and its B/C analogues, `y5 ↦ y6` resp. `y4`) has sign
    `(+)(-)(-)(+)(+)(+) > 0` on the box;
* repackages the two phase-1 derivative facts as `*_box` (rational box) and
  `*_hminus` (the actual `2*hminus` box) versions with no domain or
  nonvanishing hypotheses.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.Wt1TowerDeriv

set_option maxHeartbeats 4000000

namespace Kepler.Text
open Kepler.NliBanks21

/-! ## 1. Basic box facts -/

theorem w1box_pos (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h5l : (2 : ℝ) ≤ y5) (h6l : (2 : ℝ) ≤ y6) :
    0 < y4 ∧ 0 < y5 ∧ 0 < y6 := by
  refine ⟨by linarith, by linarith, by linarith⟩

theorem w1box_y4sq (y4 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508) :
    (6.068 : ℝ) ≤ y4 * y4 ∧ y4 * y4 ≤ 7.03 := by
  constructor <;> nlinarith

theorem w1box_y5sq (y5 : ℝ) (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) :
    (4 : ℝ) ≤ y5 * y5 ∧ y5 * y5 ≤ 6.07 := by
  constructor <;> nlinarith

theorem w1box_y6sq (y6 : ℝ) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    (4 : ℝ) ≤ y6 * y6 ∧ y6 * y6 ≤ 6.07 := by
  constructor <;> nlinarith

/-- Three-factor monotone product bound. -/
theorem w1_mul3_ge {a b c x y z : ℝ} (ha : a ≤ x) (hb : b ≤ y) (hc : c ≤ z)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    a * b * c ≤ x * y * z := by
  have hx0 : (0 : ℝ) ≤ x := le_trans ha0 ha
  have hy0 : (0 : ℝ) ≤ y := le_trans hb0 hb
  have h1 : a * b ≤ x * y := mul_le_mul ha hb hb0 hx0
  exact mul_le_mul h1 hc hc0 (mul_nonneg hx0 hy0)

/-! ## 2. Euler-area lower bounds (a ≥ 14 on the box) -/

/-- `a_A ≥ 14` on the box (each of the four terms of `w1aA` is bounded
below). -/
theorem w1aA_ge (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    (14 : ℝ) ≤ w1aA y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx4l, hx4h⟩ := w1box_y4sq y4 h4l h4h
  obtain ⟨hx5l, hx5h⟩ := w1box_y5sq y5 h5l h5h
  obtain ⟨hx6l, hx6h⟩ := w1box_y6sq y6 h6l h6h
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1.4 : ℝ) ^ 2 ≤ 2 by norm_num)
    have h14 : Real.sqrt ((1.4 : ℝ) ^ 2) = 1.4 := Real.sqrt_sq (by norm_num)
    linarith
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  -- term 1: sqrt2 * y5 * y4 >= 1 * 2 * 2.4635
  have h1 : Real.sqrt 2 * y5 * y4 ≥ (4.9 : ℝ) := by
    have hm := w1_mul3_ge hs2 (by linarith : (2 : ℝ) ≤ y5)
      (by linarith : (2.4635 : ℝ) ≤ y4) (by norm_num) (by norm_num) (by norm_num)
    linarith
  -- term 2: y5 * y4^2 / 2 >= 2 * 6.068 / 2
  have h2 : y5 * (y4 * y4) / 2 ≥ (6.06 : ℝ) := by
    have hm : 2 * 6.068 ≤ y5 * (y4 * y4) :=
      mul_le_mul h5l hx4l (by norm_num : (0 : ℝ) ≤ 6.068) (by linarith)
    linarith
  -- term 3: sqrt2 * (y5^2 + y4^2 - y6^2) / 2 >= 0
  have h3 : 0 ≤ Real.sqrt 2 * ((y5 * y5) + (y4 * y4) - (y6 * y6)) / 2 := by
    have hd : (0 : ℝ) ≤ (y5 * y5) + (y4 * y4) - (y6 * y6) := by nlinarith
    exact div_nonneg (mul_nonneg hs2n hd) (by norm_num)
  -- term 4: y4 * y5^2 / 2 >= 2.4635 * 4 / 2
  have h4 : y4 * (y5 * y5) / 2 ≥ (4.9 : ℝ) := by
    have hm : 2.4635 * 4 ≤ y4 * (y5 * y5) :=
      mul_le_mul h4l hx5l (by norm_num : (0 : ℝ) ≤ 4) (by linarith)
    linarith
  unfold w1aA
  linarith

/-- `a_B ≥ 14` on the box. -/
theorem w1aB_ge (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    (12.5 : ℝ) ≤ w1aB y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx4l, hx4h⟩ := w1box_y4sq y4 h4l h4h
  obtain ⟨hx5l, hx5h⟩ := w1box_y5sq y5 h5l h5h
  obtain ⟨hx6l, hx6h⟩ := w1box_y6sq y6 h6l h6h
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1.4 : ℝ) ^ 2 ≤ 2 by norm_num)
    have h14 : Real.sqrt ((1.4 : ℝ) ^ 2) = 1.4 := Real.sqrt_sq (by norm_num)
    linarith
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : Real.sqrt 2 * y6 * y5 ≥ (4.9 : ℝ) := by
    have hm := w1_mul3_ge hs2 (by linarith : (2 : ℝ) ≤ y6)
      (by linarith : (2 : ℝ) ≤ y5) (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h2 : y6 * (y5 * y5) / 2 ≥ (4.0 : ℝ) := by
    have h5sq : (0 : ℝ) ≤ y5 * y5 := by nlinarith
    have hm : 2 * 4 ≤ y6 * (y5 * y5) :=
      mul_le_mul h6l hx5l (by norm_num : (0 : ℝ) ≤ 4) (by linarith)
    linarith
  have h3 : 0 ≤ Real.sqrt 2 * ((y6 * y6) + (y5 * y5) - (y4 * y4)) / 2 := by
    have hd : (0 : ℝ) ≤ (y6 * y6) + (y5 * y5) - (y4 * y4) := by nlinarith
    exact div_nonneg (mul_nonneg hs2n hd) (by norm_num)
  have h4 : y5 * (y6 * y6) / 2 ≥ (4.0 : ℝ) := by
    have h6sq : (0 : ℝ) ≤ y6 * y6 := by nlinarith
    have hm : 2 * 4 ≤ y5 * (y6 * y6) :=
      mul_le_mul h5l hx6l (by norm_num : (0 : ℝ) ≤ 4) (by linarith)
    linarith
  unfold w1aB
  linarith

/-- `a_C ≥ 14` on the box. -/
theorem w1aC_ge (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    (14 : ℝ) ≤ w1aC y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx4l, hx4h⟩ := w1box_y4sq y4 h4l h4h
  obtain ⟨hx5l, hx5h⟩ := w1box_y5sq y5 h5l h5h
  obtain ⟨hx6l, hx6h⟩ := w1box_y6sq y6 h6l h6h
  have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1.4 : ℝ) ^ 2 ≤ 2 by norm_num)
    have h14 : Real.sqrt ((1.4 : ℝ) ^ 2) = 1.4 := Real.sqrt_sq (by norm_num)
    linarith
  have hs2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h1 : Real.sqrt 2 * y4 * y6 ≥ (4.9 : ℝ) := by
    have hm := w1_mul3_ge hs2 (by linarith : (2.4635 : ℝ) ≤ y4)
      (by linarith : (2 : ℝ) ≤ y6) (by norm_num) (by norm_num) (by norm_num)
    linarith
  have h2 : y4 * (y6 * y6) / 2 ≥ (4.9 : ℝ) := by
    have hm : 2.4635 * 4 ≤ y4 * (y6 * y6) :=
      mul_le_mul h4l hx6l (by norm_num : (0 : ℝ) ≤ 4) (by linarith)
    linarith
  have h3 : 0 ≤ Real.sqrt 2 * ((y4 * y4) + (y6 * y6) - (y5 * y5)) / 2 := by
    have hd : (0 : ℝ) ≤ (y4 * y4) + (y6 * y6) - (y5 * y5) := by nlinarith
    exact div_nonneg (mul_nonneg hs2n hd) (by norm_num)
  have h4 : y6 * (y4 * y4) / 2 ≥ (6.06 : ℝ) := by
    have hm : 2 * 6.068 ≤ y6 * (y4 * y4) :=
      mul_le_mul h6l hx4l (by norm_num : (0 : ℝ) ≤ 6.068) (by linarith)
    linarith
  unfold w1aC
  linarith

/-! ## 3. Delta lower bound -/

/-- `Δ ≥ -600` on the box (crude: quadratic term `≥ -296.6`, cubic term
`≥ -259.2`, mixed term `≥ 0`). -/
theorem w1Dlt_ge (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -(600 : ℝ) ≤ w1Dlt y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx4l, hx4h⟩ := w1box_y4sq y4 h4l h4h
  obtain ⟨hx5l, hx5h⟩ := w1box_y5sq y5 h5l h5h
  obtain ⟨hx6l, hx6h⟩ := w1box_y6sq y6 h6l h6h
  have h4n : (0 : ℝ) ≤ y4 * y4 := by linarith
  have h5n : (0 : ℝ) ≤ y5 * y5 := by linarith
  have h6n : (0 : ℝ) ≤ y6 * y6 := by linarith
  have hxy4n : (0 : ℝ) ≤ (y4 * y4) * (y5 * y5) := mul_nonneg h4n h5n
  have hxy6n : (0 : ℝ) ≤ (y4 * y4) * (y6 * y6) := mul_nonneg h4n h6n
  have hxy56n : (0 : ℝ) ≤ (y5 * y5) * (y6 * y6) := mul_nonneg h5n h6n
  -- squares
  have hq : (y4 * y4) ^ 2 + (y5 * y5) ^ 2 + (y6 * y6) ^ 2 ≤ (148.3 : ℝ) := by
    nlinarith [sq_nonneg (y4 * y4), sq_nonneg (y5 * y5), sq_nonneg (y6 * y6)]
  -- cubic
  have hxy4 : (y4 * y4) * (y5 * y5) ≤ 7.03 * 6.07 := by nlinarith
  have hxy6 : (y4 * y4) * (y6 * y6) ≤ 7.03 * 6.07 := by nlinarith
  have hxy56 : (y5 * y5) * (y6 * y6) ≤ 6.07 * 6.07 := by nlinarith
  have hprod : (y4 * y4) * (y5 * y5) * (y6 * y6) ≤ 7.03 * 6.07 * 6.07 := by
    have h1 : 0 ≤ (y4 * y4) * (y5 * y5) := mul_nonneg h4n h5n
    have h2 : 0 ≤ y6 * y6 := h6n
    calc (y4 * y4) * (y5 * y5) * (y6 * y6)
        ≤ (7.03 * 6.07) * (6.07) := by
          exact mul_le_mul hxy4 hx6h h2 (by norm_num)
      _ = 7.03 * 6.07 * 6.07 := by ring
  unfold w1Dlt
  linarith

/-! ## 4. The six differentiability-domain facts -/

/-- `-1 < t_A` on the box. -/
theorem w1tA_domain (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -1 < w1tA y4 y5 y6 := by
  have ha := w1aA_ge y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have hdl := w1Dlt_ge y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have ha2 : (0 : ℝ) < w1aA y4 y5 y6 ^ 2 := by nlinarith
  have h4a : (0 : ℝ) < 4 * w1aA y4 y5 y6 ^ 2 := by nlinarith
  unfold w1tA w1tOf
  rw [lt_div_iff₀ h4a]
  nlinarith [sq_nonneg (w1aA y4 y5 y6)]

/-- `-1 < t_B` on the box. -/
theorem w1tB_domain (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -1 < w1tB y4 y5 y6 := by
  have ha := w1aB_ge y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have hdl := w1Dlt_ge y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have ha2 : (0 : ℝ) < w1aB y4 y5 y6 ^ 2 := by nlinarith
  have h4a : (0 : ℝ) < 4 * w1aB y4 y5 y6 ^ 2 := by nlinarith
  unfold w1tB w1tOf
  rw [lt_div_iff₀ h4a]
  nlinarith [sq_nonneg (w1aB y4 y5 y6)]

/-- `-1 < t_C` on the box. -/
theorem w1tC_domain (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -1 < w1tC y4 y5 y6 := by
  have ha := w1aC_ge y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have hdl := w1Dlt_ge y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have ha2 : (0 : ℝ) < w1aC y4 y5 y6 ^ 2 := by nlinarith
  have h4a : (0 : ℝ) < 4 * w1aC y4 y5 y6 ^ 2 := by nlinarith
  unfold w1tC w1tOf
  rw [lt_div_iff₀ h4a]
  nlinarith [sq_nonneg (w1aC y4 y5 y6)]

/-- The common quartic sign factor of the three `g` domain certificates
(negative on the box). -/
theorem w1_gfac_neg (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    (y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6))) < 0 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  have h1 : y4 - y5 - y6 < 0 := by linarith
  have h2 : 0 < y4 - y5 + y6 := by linarith
  have h3 : 0 < y4 + y5 - y6 := by linarith
  have h4 : 0 < y4 + y5 + y6 := by linarith
  have h34 : 0 < (y4 + y5 - y6) * (y4 + y5 + y6) := mul_pos h3 h4
  have h234 : 0 < (y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6)) :=
    mul_pos h2 h34
  exact mul_neg_of_neg_of_pos h1 h234

/-- `-1 < g_A` on the box, via the factorisation
`d4_A² + 4y5²Δ = y5²·(y5²-8)·(y4-y5-y6)(y4-y5+y6)(y4+y5-y6)(y4+y5+y6)`. -/
theorem w1gA_domain (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -1 < w1gA y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx5l, hx5h⟩ := w1box_y5sq y5 h5l h5h
  have hfac : w1d4A y4 y5 y6 ^ 2 + 4 * (y5 * y5) * w1Dlt y4 y5 y6
      = (y5 * y5) * ((y5 * y5 - 8) *
          ((y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6))))) := by
    unfold w1d4A w1Dlt
    ring
  have hg := w1_gfac_neg y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have h8 : y5 * y5 - 8 < 0 := by nlinarith
  have hbracket : 0 < (y5 * y5 - 8) *
      ((y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6)))) :=
    mul_pos_of_neg_of_neg h8 hg
  have hnum : 0 < w1d4A y4 y5 y6 ^ 2 + 4 * (y5 * y5) * w1Dlt y4 y5 y6 := by
    rw [hfac]
    exact mul_pos (by positivity) hbracket
  have hden : (0 : ℝ) < w1d4A y4 y5 y6 ^ 2 := by
    have := w1d4A_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h
    positivity
  unfold w1gA w1gOf
  rw [lt_div_iff₀ hden]
  nlinarith

/-- `-1 < g_B` on the box. -/
theorem w1gB_domain (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -1 < w1gB y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx6l, hx6h⟩ := w1box_y6sq y6 h6l h6h
  have hfac : w1d4B y4 y5 y6 ^ 2 + 4 * (y6 * y6) * w1Dlt y4 y5 y6
      = (y6 * y6) * ((y6 * y6 - 8) *
          ((y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6))))) := by
    unfold w1d4B w1Dlt
    ring
  have hg := w1_gfac_neg y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have h8 : y6 * y6 - 8 < 0 := by nlinarith
  have hbracket : 0 < (y6 * y6 - 8) *
      ((y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6)))) :=
    mul_pos_of_neg_of_neg h8 hg
  have hnum : 0 < w1d4B y4 y5 y6 ^ 2 + 4 * (y6 * y6) * w1Dlt y4 y5 y6 := by
    rw [hfac]
    exact mul_pos (by positivity) hbracket
  have hden : (0 : ℝ) < w1d4B y4 y5 y6 ^ 2 := by
    have := w1d4B_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h
    positivity
  unfold w1gB w1gOf
  rw [lt_div_iff₀ hden]
  nlinarith

/-- `-1 < g_C` on the box. -/
theorem w1gC_domain (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    -1 < w1gC y4 y5 y6 := by
  obtain ⟨hy4, hy5, hy6⟩ := w1box_pos y4 y5 y6 h4l h5l h6l
  obtain ⟨hx4l, hx4h⟩ := w1box_y4sq y4 h4l h4h
  have hfac : w1d4C y4 y5 y6 ^ 2 + 4 * (y4 * y4) * w1Dlt y4 y5 y6
      = (y4 * y4) * ((y4 * y4 - 8) *
          ((y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6))))) := by
    unfold w1d4C w1Dlt
    ring
  have hg := w1_gfac_neg y4 y5 y6 h4l h4h h5l h5h h6l h6h
  have h8 : y4 * y4 - 8 < 0 := by nlinarith
  have hbracket : 0 < (y4 * y4 - 8) *
      ((y4 - y5 - y6) * ((y4 - y5 + y6) * ((y4 + y5 - y6) * (y4 + y5 + y6)))) :=
    mul_pos_of_neg_of_neg h8 hg
  have hnum : 0 < w1d4C y4 y5 y6 ^ 2 + 4 * (y4 * y4) * w1Dlt y4 y5 y6 := by
    rw [hfac]
    exact mul_pos (by positivity) hbracket
  have hden : (0 : ℝ) < w1d4C y4 y5 y6 ^ 2 := by
    have := w1d4C_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h
    positivity
  unfold w1gC w1gOf
  rw [lt_div_iff₀ hden]
  nlinarith

/-! ## 5. Assumption-free D1/D2 -/

/-- **D1 without domain/nonvanishing hypotheses** (rational box). -/
theorem w1aF_hasDerivAt_y5_box (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    HasDerivAt (fun s => w1aF y4 s y6) (w1F1 y4 y5 y6) y5 :=
  w1aF_hasDerivAt_y5 y4 y5 y6
    (by linarith) (by linarith) (by linarith)
    (ne_of_gt (w1aA_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1aB_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1aC_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1d4A_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1d4B_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1d4C_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (w1tA_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1tB_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1tC_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1gA_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1gB_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1gC_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)

/-- **D2 without domain/nonvanishing hypotheses** (rational box). -/
theorem w1aF_hasDerivAt2_y5_box (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    HasDerivAt (fun s => w1F1 y4 s y6) (w1F2 y4 y5 y6) y5 :=
  w1aF_hasDerivAt2_y5 y4 y5 y6
    (by linarith) (by linarith) (by linarith)
    (ne_of_gt (w1aA_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1aB_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1aC_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1d4A_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1d4B_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (ne_of_gt (w1d4C_pos y4 y5 y6 h4l h4h h5l h5h h6l h6h))
    (w1tA_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1tB_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1tC_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1gA_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1gB_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)
    (w1gC_domain y4 y5 y6 h4l h4h h5l h5h h6l h6h)

/-- `2 * hplus = 2.6508`. -/
theorem w1_two_hplus : 2 * hplus = (2.6508 : ℝ) := by
  norm_num [hplus]

/-- **D1 on the actual `2*hminus` box** (no domain/nonvanishing hypotheses). -/
theorem w1aF_hasDerivAt_y5_hminus (y4 y5 y6 : ℝ)
    (h4 : 2 * hminus ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hminus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hminus) :
    HasDerivAt (fun s => w1aF y4 s y6) (w1F1 y4 y5 y6) y5 := by
  have hhm := Kepler.NliBanks17.nb17_two_hminus_bounds
  exact w1aF_hasDerivAt_y5_box y4 y5 y6
    (le_trans hhm.1 h4) (by rw [← w1_two_hplus]; exact h4')
    h5 (le_trans h5' hhm.2) h6 (le_trans h6' hhm.2)

/-- **D2 on the actual `2*hminus` box** (no domain/nonvanishing hypotheses). -/
theorem w1aF_hasDerivAt2_y5_hminus (y4 y5 y6 : ℝ)
    (h4 : 2 * hminus ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hminus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hminus) :
    HasDerivAt (fun s => w1F1 y4 s y6) (w1F2 y4 y5 y6) y5 := by
  have hhm := Kepler.NliBanks17.nb17_two_hminus_bounds
  exact w1aF_hasDerivAt2_y5_box y4 y5 y6
    (le_trans hhm.1 h4) (by rw [← w1_two_hplus]; exact h4')
    h5 (le_trans h5' hhm.2) h6 (le_trans h6' hhm.2)

/-! ## 6. Axiom audit -/

#print axioms w1box_pos
#print axioms w1aA_ge
#print axioms w1aB_ge
#print axioms w1aC_ge
#print axioms w1Dlt_ge
#print axioms w1tA_domain
#print axioms w1tB_domain
#print axioms w1tC_domain
#print axioms w1_gfac_neg
#print axioms w1gA_domain
#print axioms w1gB_domain
#print axioms w1gC_domain
#print axioms w1aF_hasDerivAt_y5_box
#print axioms w1aF_hasDerivAt2_y5_box
#print axioms w1aF_hasDerivAt_y5_hminus
#print axioms w1aF_hasDerivAt2_y5_hminus

end Kepler.Text
