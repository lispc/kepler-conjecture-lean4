import Kepler.Text.ZTGJointKit
import Kepler.Text.Gamma4Wide

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

def ztg0000Wide (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 ≤ y1 ∧ y1 ≤ 2 * hplus ∧ 2 ≤ y2 ∧ y2 ≤ 2 * hplus ∧
    2 ≤ y3 ∧ y3 ≤ 2 * hplus ∧ 2 ≤ y4 ∧ y4 ≤ 2 * hplus ∧
      2 ≤ y5 ∧ y5 ≤ 2 * hplus ∧ 2 ≤ y6 ∧ y6 ≤ 2 * hplus

theorem ztg0000_wide {y1 y2 y3 y4 y5 y6 : ℝ}
    (hy : ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6) : ztg0000Wide y1 y2 y3 y4 y5 y6 := by
  rcases hy with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hhm : 2 * hminus ≤ 2 * hplus := ztg_two_hminus_le_kink.trans ztg_kink_le_two_hplus
  have h3l' : (2 : ℝ) ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : (2 : ℝ) ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : (2 : ℝ) ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : (2 : ℝ) ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h6h
  exact ⟨Kepler.NliBanksZTGIJCF4Route.two_le_two_hminus.trans h1l, h1h, h2l, h2h.trans hhm, h3l', h3h'.trans hhm,
    h4l', h4h'.trans hhm, h5l', h5h'.trans hhm, h6l', h6h'.trans hhm⟩

theorem ztg0000_g4wBox {y1 y2 y3 y4 y5 y6 : ℝ}
    (hy : ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6) :
    g4wBox (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
  rcases ztg0000_wide hy with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  rw [hplus] at *
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem ztg0000_deltaY_pos {y1 y2 y3 y4 y5 y6 : ℝ}
    (hy : ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6) : 0 < deltaY y1 y2 y3 y4 y5 y6 := by
  rw [deltaY]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 96) (g4w_deltaX_bounds (ztg0000_g4wBox hy))

theorem ztg_upsX_sq_pos {a b c : ℝ}
    (ha : 2 ≤ a) (ha' : a ≤ 2 * hplus)
    (hb : 2 ≤ b) (hb' : b ≤ 2 * hplus)
    (hc : 2 ≤ c) (hc' : c ≤ 2 * hplus) :
    0 < upsX (a * a) (b * b) (c * c) := by
  have hp : 2 * hplus < 3 := by rw [hplus]; norm_num
  have hsum : 0 < a + b + c := by linarith
  have hbc : 0 < -a + b + c := by linarith
  have hac : 0 < a - b + c := by linarith
  have hab : 0 < a + b - c := by linarith
  rw [show upsX (a * a) (b * b) (c * c) =
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) by
      unfold upsX; ring]
  positivity

theorem ztg0000_upsX_y126 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hy : ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6) :
    0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
  rcases ztg0000_wide hy with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ztg_upsX_sq_pos h1 h1' h2 h2' h6 h6'

theorem ztg0000_upsX_y135 {y1 y2 y3 y4 y5 y6 : ℝ}
    (hy : ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6) :
    0 < upsX (y1 * y1) (y3 * y3) (y5 * y5) := by
  rcases ztg0000_wide hy with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
  exact ztg_upsX_sq_pos h1 h1' h3 h3' h5 h5'

#print axioms ztg0000_wide
#print axioms ztg0000_g4wBox
#print axioms ztg0000_deltaY_pos
#print axioms ztg_upsX_sq_pos
#print axioms ztg0000_upsX_y126
#print axioms ztg0000_upsX_y135

end Kepler.Text
