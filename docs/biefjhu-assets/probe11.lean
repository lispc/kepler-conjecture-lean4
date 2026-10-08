import Kepler.Text.PackingAuto22
open Real in
example : ∃ lem : ℝ → ℝ → Prop, True := by
  exact ⟨fun a b => a ≤ b, trivial⟩
#check @Real.cos_lt_cos_of_nonneg_of_le_pi
#check @Real.cos_le_cos_of_nonneg_of_le_pi
#check @Real.strictAntiOn_cos
