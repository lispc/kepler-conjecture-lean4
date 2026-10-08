/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w6 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/6)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/6) = 1/2 := Real.sin_pi_div_six
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/6)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/6)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/6))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/6)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/6))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/6))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/6)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/6)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/6))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/6))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/6) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/6 - (31415:ℝ)/10000/6 ^ 3 / 6
        + (31416:ℝ)/10000/6 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num


/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w7 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/7)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/7)
      ≤ (31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6 + (31416:ℝ)/10000/7 ^ 5 / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/7)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/7)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/7))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/7)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/7))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/7))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/7)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/7)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/7))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/7))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/7) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/7 - (31415:ℝ)/10000/7 ^ 3 / 6
        + (31416:ℝ)/10000/7 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num


/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w8 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/8)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/8)
      ≤ (31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6 + (31416:ℝ)/10000/8 ^ 5 / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/8)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/8)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/8))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/8)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/8))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/8))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/8)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/8)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/8))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/8))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/8) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/8 - (31415:ℝ)/10000/8 ^ 3 / 6
        + (31416:ℝ)/10000/8 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num


/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w9 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/9)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/9)
      ≤ (31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6 + (31416:ℝ)/10000/9 ^ 5 / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/9)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/9)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/9))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/9)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/9))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/9))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/9)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/9)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/9))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/9))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/9) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/9 - (31415:ℝ)/10000/9 ^ 3 / 6
        + (31416:ℝ)/10000/9 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num


/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w10 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/10)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/10)
      ≤ (31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6 + (31416:ℝ)/10000/10 ^ 5 / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/10)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/10)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/10))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/10)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/10))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/10))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/10)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/10)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/10))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/10))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/10) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/10 - (31415:ℝ)/10000/10 ^ 3 / 6
        + (31416:ℝ)/10000/10 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num


/-- k ∈ {5..11} windows (Taylor σ, quadratic majorant). -/
private theorem p22_bjf_w11 :
    (2:ℝ)*5*asn ((sqrt3/2)*Real.sin (Real.pi/11)) ≤ 5.186 + 0.0331*5 := by
  have hsig : Real.sin (Real.pi/11)
      ≤ (31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6 + (31416:ℝ)/10000/11 ^ 5 / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/11)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120) := by
    have h1 : (sqrt3:ℝ)/2 ≤ 8661/10000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    unfold sqrt3 at h1
    refine mul_le_mul_of_nonneg_left hsig ?_
    norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/11)) ^ 2 ≤ 17/64 := by nlinarith [hv]
  have hle : asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/11))
      ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/11)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/11))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/11))^5/10 :=
    p22_bjf_asn_quad (by
      unfold sqrt3
      positivity) hwu
  have hVt : (sqrt3:ℝ)/2*Real.sin (Real.pi/11)
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120) := hv
  have hmono : (sqrt3:ℝ)/2*Real.sin (Real.pi/11)
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/11))^3/6
        + ((sqrt3:ℝ)/2*Real.sin (Real.pi/11))^5/10
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120)
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120))^3/6
        + ((8661:ℝ)/10000*((31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120))^5/10 := by
    have hw : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/11) := by
      unfold sqrt3; positivity
    have hv0 : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120) := by
      have h1 : (0:ℝ) ≤ (31416:ℝ)/10000/11 - (31415:ℝ)/10000/11 ^ 3 / 6
        + (31416:ℝ)/10000/11 ^ 5 / 120 := by norm_num
      exact mul_nonneg (by norm_num) h1
      unfold sqrt3 at *
      positivity
    refine p22_bjf_Pmono hw (by linarith) hv (by linarith) (by linarith) (by linarith)
      (by nlinarith) (by nlinarith) (by nlinarith)
  refine le_trans (le_trans hle hmono) ?_
  norm_num

