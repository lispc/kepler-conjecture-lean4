import Kepler.Text.PackingAuto22

namespace Kepler.Text

/-- local T helper -/
noncomputable def T (h : ℝ) : ℝ := h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2

private theorem T1 : T 1 = sqrt3 / 2 := by
  unfold T sqrt3
  have h1 : Real.sqrt (1 - (1 / 2) ^ 2) = Real.sqrt 3 / 2 := by
    have h34 : 1 - (1 / 2) ^ 2 = 3 / 4 := by norm_num
    rw [h34, Real.sqrt_div (by norm_num : (4:ℝ) ≠ 0), Real.sqrt_div (by norm_num : (3:ℝ) ≠ 0)]
    norm_num [Real.sqrt_five, Real.sqrt_four]
  rw [h1]; ring

end Kepler.Text
