import Kepler.Text.PackingAuto22
namespace Kepler.Text
noncomputable def T (h : ℝ) : ℝ := h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2

private theorem T1 : T 1 = sqrt3 / 2 := by
  unfold T sqrt3
  have h34 : (1:ℝ) - (1/2)^2 = 3/4 := by norm_num
  rw [h34, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) ≤ 4)]
  norm_num [Real.sqrt_four]
