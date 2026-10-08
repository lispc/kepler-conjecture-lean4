/-! ## BIEFJHU numeric kit (PA22f wave): algebraic h-reduction + polynomial `asn` majorants. -/

/-- auxiliary: `T h` = the spherical-cap cosine parameter of `BIEFJHU_explicit`. -/
private noncomputable def p22_bjf_T (h : ℝ) : ℝ :=
  h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2

private theorem p22_bjf_T1 : p22_bjf_T 1 = sqrt3 / 2 := by
  unfold p22_bjf_T sqrt3
  have h34 : (1:ℝ) - (1/2)^2 = 3/4 := by norm_num
  rw [h34, Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
  ring

private theorem p22_bjf_Tdiff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p22_bjf_T b - p22_bjf_T a
      = (b - a) * (sqrt3 / 4)
        - (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2 := by
  unfold p22_bjf_T sqrt3
  ring

/-- cos-representation: `T h = cos(π/3 - arcsin(h/2))`. -/
private theorem p22_bjf_Tcos (h : ℝ) (hh : 0 ≤ h) (h1 : h ≤ 2) :
    p22_bjf_T h = Real.cos (Real.pi / 3 - Real.arcsin (h / 2)) := by
  unfold p22_bjf_T sqrt3
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three,
    Real.cos_arcsin, Real.sin_arcsin (by linarith) (by linarith)]
  ring

/-- `T` is increasing on `[1, h0]`. -/
private theorem p22_bjf_Tmono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h0) :
    p22_bjf_T a ≤ p22_bjf_T b := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha
  have hb0 : (0:ℝ) ≤ b := le_trans ha0 hab
  have hab2 : a / 2 ≤ b / 2 := by linarith
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hble : (b:ℝ) ≤ 126 / 100 := by
    have h126b : (h0:ℝ) = 126 / 100 := h126
    have hb2 : (b:ℝ) ≤ h0 := hb
    rw [h126b] at hb2
    exact hb2
  have hsqrt3ge : (433:ℝ)/250 ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hrange : ∀ x : ℝ, 1 ≤ x → x ≤ h0 →
      0 ≤ Real.pi / 3 - Real.arcsin (x / 2)
      ∧ Real.pi / 3 - Real.arcsin (x / 2) ≤ Real.pi := by
    intro x hx1 hxh
    have hxi : (x:ℝ) ≤ 126 / 100 := by
      have h126x : (h0:ℝ) = 126 / 100 := h126
      have hx2 : (x:ℝ) ≤ h0 := hxh
      rw [h126x] at hx2
      exact hx2
    have hx2 : x / 2 ≤ Real.sqrt 3 / 2 := by
      have h1 : (x:ℝ)/2 ≤ 63 / 100 := by linarith
      have h2 : (433:ℝ)/500 ≤ Real.sqrt 3 / 2 := by linarith [hsqrt3ge]
      linarith
    have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
    have hpi32 : Real.pi / 3 ≤ Real.pi / 2 := by linarith
    have hasin : Real.arcsin (x / 2) ≤ Real.pi / 3 := by
      refine le_trans (Real.arcsin_le_arcsin hx2) ?_
      have h3 : Real.arcsin (Real.sin (Real.pi / 3)) = Real.pi / 3 :=
        Real.arcsin_sin (by linarith) (by linarith)
      rw [Real.sin_pi_div_three] at h3
      rw [h3]
    constructor
    · have h4 : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      linarith [hasin, h4]
    · have h4b : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      have h5 : Real.arcsin (x / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
      linarith [h5, h4b, Real.pi_pos]
  have hxeq : p22_bjf_T a = Real.cos (Real.pi / 3 - Real.arcsin (a / 2)) :=
    p22_bjf_Tcos a ha0 (by linarith [h126, hble])
  have hbeq : p22_bjf_T b = Real.cos (Real.pi / 3 - Real.arcsin (b / 2)) :=
    p22_bjf_Tcos b hb0 (by linarith [h126, hble])
  rw [hxeq, hbeq]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
  · exact (hrange b (le_trans ha hab) hb).1
  · exact (hrange a ha (le_trans hab hb)).2
  · have h1 : Real.arcsin (a / 2) ≤ Real.arcsin (b / 2) := Real.arcsin_le_arcsin hab2
    linarith

