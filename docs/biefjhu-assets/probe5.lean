import Kepler.Text.PackingAuto22
example : Real.sqrt ((3:ℝ)/4) = Real.sqrt 3 / 2 := by
  rw [Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
  norm_num
