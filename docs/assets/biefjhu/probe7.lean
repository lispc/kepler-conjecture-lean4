import Kepler.Text.PackingAuto22
#check @pow_le_pow_right₀
#check @pow_le_pow_left₀
#check @IntervalIntegrable.congr_fun
example {w : ℝ} (hw : 0 ≤ w) (h : w ^ 2 ≤ (17:ℝ)/64) : w ^ 4 ≤ ((17:ℝ)/64) ^ 2 := by
  exact pow_le_pow_right₀ (by nlinarith) (by nlinarith) 2
