/-- Taylor-5 upper bound for `sin(π/k)` with `π ∈ (3.1415, 3.1416)`. -/
private theorem p22_bjf_wtaylor {k : ℕ} (hk4 : 4 ≤ k) :
    Real.sin (Real.pi / k)
      ≤ (31416:ℝ)/10000/k - (31415:ℝ)/10000/k ^ 3 / 6 + (31416:ℝ)/10000/k ^ 5 / 120 := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by norm_num) hk4
  have hy0 : 0 ≤ Real.pi / k := div_nonneg Real.pi_pos.le hkpos.le
  have hyU : Real.pi / k ≤ (31416:ℝ)/10000/k :=
    p22_div_le_div_nat_right hkpos (le_of_lt Real.pi_lt_d4)
  have hyL : (31415:ℝ)/10000/k ≤ Real.pi / k :=
    p22_div_le_div_nat_right hkpos (le_of_lt Real.pi_gt_d4)
  have hy4 : Real.pi / k ≤ 4 := by
    have h1 : Real.pi / k ≤ (31416:ℝ)/10000/4 := by
      refine le_trans hyU ?_
      exact p22_div_le_div_nat_left (by norm_num) (by norm_num) hk4
    linarith
  have hsin := p22_sin_le_taylor5 hy0 hy4
  have h30 : (0:ℝ) ≤ (31415:ℝ)/10000/k := div_nonneg (by norm_num) hkpos.le
  have hy3L : ((31415:ℝ)/10000/k) ^ 3 ≤ (Real.pi / k) ^ 3 := pow_le_pow_left₀ h30 hyL 3
  have hy5U : (Real.pi / k) ^ 5 ≤ ((31416:ℝ)/10000/k) ^ 5 := pow_le_pow_left₀ hy0 hyU 5
  have h3n : (0:ℝ) ≤ (31415:ℝ)/10000/k := h30
  linarith

/-- monotonicity of the septic/P4 polynomial upper bound. -/
private theorem p22_bjf_Pmono {w v1 v3 v5 v7 : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v1)
    (hwv : w ≤ v1) (hc : 0 ≤ v3) (hc5 : 0 ≤ v5) (hc7 : 0 ≤ v7)
    (h3 : w ^ 3 ≤ v3) (h5 : w ^ 5 ≤ v5) (h7 : w ^ 7 ≤ v7) :
    w + w ^ 3 / 6 + w ^ 5 / 10 + (19/175) * w ^ 7
      ≤ v1 + v3 / 6 + v5 / 10 + (19/175) * v7 := by
  have h1 : w * 1 ≤ v1 * 1 := mul_le_mul hw hv (by linarith) (by linarith)
  have h3' : w ^ 3 / 6 ≤ v3 / 6 := p22_div_le_div_right (by norm_num) h3
  have h5' : w ^ 5 / 10 ≤ v5 / 10 := p22_div_le_div_right (by norm_num) h5
  have h7' : (19:ℝ)/175 * w ^ 7 ≤ (19:ℝ)/175 * v7 :=
    mul_le_mul_of_nonneg_left h7 (by norm_num)
  linarith

/-- k=3 window (v = 3/4 exactly). -/
private theorem p22_bjf_w3 :
    (2:ℝ)*3*asn ((sqrt3/2)*Real.sin (Real.pi/3)) ≤ 5.186 + 0.0331*3 := by
  have hsin : Real.sin (Real.pi/3) = Real.sqrt 3/2 := Real.sin_pi_div_three
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/3) = 3/4 := by
    unfold sqrt3
    rw [hsin]
    have h := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
    field_simp
    linarith [h]
  have hle : asn (3/4) ≤ 3/4 + (3/4)^3/6 + (3/4)^5/10 + (19/175)*(3/4)^7 :=
    p22_bjf_asn_sept (by norm_num) (by norm_num)
  rw [hv]
  exact le_trans hle (by norm_num)

/-- k=4 window (v = √6/4). -/
private theorem p22_bjf_w4 :
    (2:ℝ)*4*asn ((sqrt3/2)*Real.sin (Real.pi/4)) ≤ 5.186 + 0.0331*4 := by
  have hsin4 : Real.sin (Real.pi/4) = Real.sqrt 2/2 := Real.sin_pi_div_four
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/4) = Real.sqrt 6/4 := by
    unfold sqrt3
    rw [hsin4, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hvle : Real.sqrt 6/4 ≤ 6124/10000 := by
    refine (Real.le_sqrt (by norm_num) (by norm_num)).mpr ?_
    norm_num
  have hwu : Real.sqrt 6/4 ^ 2 ≤ 3/8 := by
    have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
    have : (Real.sqrt 6/4) ^ 2 = Real.sqrt 6 * Real.sqrt 6 / 16 := by
      rw [div_pow, mul_pow]
      congr 1
      ring
    rw [this, h6]
    norm_num
  have hle : asn (Real.sqrt 6/4)
      ≤ Real.sqrt 6/4 + (Real.sqrt 6/4)^3/6 + (3/40)*(Real.sqrt 6/4)^5
        + (17/140)*(Real.sqrt 6/4)^7 := p22_bjf_asn_p4 (by positivity) hwu
  have hmono : Real.sqrt 6/4 + (Real.sqrt 6/4)^3/6 + (3/40)*(Real.sqrt 6/4)^5
      + (17/140)*(Real.sqrt 6/4)^7
      ≤ 6124/10000 + (6124/10000)^3/6 + (3/40)*(6124/10000)^5
        + (17/140)*(6124/10000)^7 := by
    refine p22_bjf_Pmono (by positivity) (by norm_num) hvle (by norm_num) (by norm_num)
      (by norm_num) (by nlinarith) (by nlinarith) (by nlinarith)
  rw [hv]
  refine le_trans (le_trans hle hmono) ?_
  norm_num

/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w5 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/5)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/5)
      ≤ (31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6 + (31416:ℝ)/10000/5 ^ 5 / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/5)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/5)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/5))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/5)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/5))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/5))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/5)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/5)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/5))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/5))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/5) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/5 - (31415:ℝ)/10000/5 ^ 3 / 6
        + (31416:ℝ)/10000/5 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num

end Kepler.Text
