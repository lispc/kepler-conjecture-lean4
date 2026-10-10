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
        - (Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)) / 2 := by
  unfold p22_bjf_T sqrt3
  ring

/-- sqrt-subtraction identity used by the chord bounds. -/
private theorem p22_bjf_sqrtAB (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpos : 0 < Real.sqrt x + Real.sqrt y) :
    Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.sq_sqrt hx
  have h2 : Real.sqrt y * Real.sqrt y = y := Real.sq_sqrt hy
  rw [eq_div_iff hpos]
  nlinarith [h1, h2]

private theorem p22_bjf_Wsub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : 0 < Real.sqrt (1 - (b / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2)) :
    Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)
      = ((b:ℝ) ^ 2 - a ^ 2) / 4
        / (Real.sqrt (1 - (b / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2)) := by
  rw [p22_bjf_sqrtAB (by nlinarith) ha hpos]
  have h4 : (1:ℝ) - (b / 2) ^ 2 - (1 - (a / 2) ^ 2) = ((b:ℝ) ^ 2 - a ^ 2) / 4 := by ring
  rw [h4]

/-- `T` is increasing on `[1, h0]`. -/
private theorem p22_bjf_Tmono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h0) :
    p22_bjf_T a ≤ p22_bjf_T b := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha
  have hb0 : (0:ℝ) ≤ b := le_trans ha0 hab
  have hab2 : a / 2 ≤ b / 2 := by linarith
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hble : (b:ℝ) ≤ 126 / 100 := by rw [h126]; exact_mod_cast hb
  have hsqrt3ge : (433:ℝ)/250 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hrange : ∀ x : ℝ, 1 ≤ x → x ≤ h0 →
      0 ≤ Real.pi / 3 - Real.arcsin (x / 2)
      ∧ Real.pi / 3 - Real.arcsin (x / 2) ≤ Real.pi := by
    intro x hx1 hxh
    have hxi : (x:ℝ) ≤ 126 / 100 := by rw [h126]; exact_mod_cast hxh
    have hx2 : x / 2 ≤ Real.sqrt 3 / 2 := by
      have h1 : (x:ℝ)/2 ≤ 63 / 100 := by linarith
      have h2 : (433:ℝ)/500 ≤ Real.sqrt 3 / 2 := by linarith [hsqrt3ge]
      linarith
    have hasin : Real.arcsin (x / 2) ≤ Real.pi / 3 := by
      refine le_trans (Real.arcsin_le_arcsin hx2) ?_
      have h3 : Real.arcsin (Real.sin (Real.pi / 3)) = Real.pi / 3 :=
        Real.arcsin_sin (by have := Real.pi_pos; have := Real.pi_lt_d4; linarith)
          (by have := Real.pi_lt_d4; linarith)
      rw [Real.sin_pi_div_three] at h3
      linarith [h3]
    constructor
    · have h4 : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      linarith
    · have h5 : Real.arcsin (x / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
      linarith
  have hxeq : p22_bjf_T a = Real.cos (Real.pi / 3 - Real.arcsin (a / 2)) :=
    p22_bjf_Tcos a ha0 (by linarith [h126, hble])
  have hbeq : p22_bjf_T b = Real.cos (Real.pi / 3 - Real.arcsin (b / 2)) :=
    p22_bjf_Tcos b hb0 (by linarith [h126, hble])
  rw [hxeq, hbeq]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
  · exact (hrange a ha1 hb).1
  · exact (hrange b ha1 hb).2
  · have h1 : Real.arcsin (a / 2) ≤ Real.arcsin (b / 2) := Real.arcsin_le_arcsin hab2
    linarith

/-- global chord from 1 (rational constant `2887/10000 ≥ 1/(2√3)`). -/
private theorem p22_bjf_chord_up {h : ℝ} (h1h : 1 ≤ h) (hh0 : h ≤ h0) :
    p22_bjf_T h - p22_bjf_T 1 ≤ (h - 1) * 2887 / 10000 := by
  have hTdiff := p22_bjf_Tdiff (a := 1) (by norm_num) (by linarith)
  rw [p22_bjf_T1] at hTdiff
  have hA0 : (0:ℝ) ≤ 1 - (h / 2) ^ 2 := by nlinarith
  have hA1 : (0:ℝ) ≤ 1 - (1 / 2) ^ 2 := by norm_num
  have hpos : (0:ℝ) < Real.sqrt (1 - (h / 2) ^ 2) + Real.sqrt (1 - (1 / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hA0) (Real.sqrt_pos.mpr hA1)
  have hWsub := p22_bjf_Wsub (a := 1) (b := h) hA1 hA0 hpos
  have hAle : Real.sqrt (1 - (h / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by
    refine Real.sqrt_le_sqrt ?_
    have h2 : (1:ℝ) ≤ h ^ 2 := by nlinarith
    have h3 : (1:ℝ) - (h / 2) ^ 2 ≤ 3 / 4 := by linarith
    exact h3
  have hB : Real.sqrt (1 - (1 / 2) ^ 2) = Real.sqrt 3 / 2 := by
    have h34 : (1:ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
    rw [h34, Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
    norm_num
  have hsum : Real.sqrt (1 - (h / 2) ^ 2) + Real.sqrt (1 - (1 / 2) ^ 2) ≤ Real.sqrt 3 := by
    have hB' : Real.sqrt (1 - (1 / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by rw [hB]
    linarith
  have hab0 : (0:ℝ) ≤ h - 1 := sub_nonneg.mpr h1h
  -- W := (A-B)/2 ≥ (h-1)/(4√3)
  have hWge : (Real.sqrt (1 - (h / 2) ^ 2) - Real.sqrt (1 - (1 / 2) ^ 2)) / 2
      ≥ (h - 1) / (4 * Real.sqrt 3) := by
    rw [hWsub, div_div_eq_mul_div, div_div_eq_mul_div]
    have hX : ((h:ℝ) ^ 2 - 1) / 4 = (h - 1) * (h + 1) / 4 := by ring
    rw [hX]
    have hd1 : (0:ℝ) < (2:ℝ) * Real.sqrt 3 := by positivity
    have hstep : ((h - 1) * (h + 1) / 4) / (2 * Real.sqrt 3)
        ≤ ((h - 1) * (h + 1) / 4)
          / (2 * (Real.sqrt (1 - (h / 2) ^ 2) + Real.sqrt (1 - (1 / 2) ^ 2))) := by
      refine p22_div_le_div_real_left (by nlinarith) hd1 ?_
      have h8 : (2:ℝ) * (Real.sqrt (1 - (h / 2) ^ 2) + Real.sqrt (1 - (1 / 2) ^ 2))
          ≤ 2 * Real.sqrt 3 := by linarith
      linarith
    have hx2 : ((h - 1) * (h + 1) / 4) / (2 * Real.sqrt 3)
        ≥ (h - 1) / (4 * Real.sqrt 3) := by
      have h4 : ((h - 1) * (h + 1)) * 2 ≥ (h - 1) * 4 := by
        refine mul_le_mul hab0 ?_ hab0 (by norm_num)
        linarith
      field_simp
      nlinarith [hd1]
    linarith [hstep, hx2]
  -- conclude: (h-1)·√3/4 - W ≤ (h-1)/(2√3) ≤ (h-1)·2887/10000
  have hsqrt3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.sq_sqrt (by norm_num)
  have hident : (h - 1) * (sqrt3 / 4) - (h - 1) / (4 * Real.sqrt 3)
      = (h - 1) / (2 * Real.sqrt 3) := by
    have hs : sqrt3 = Real.sqrt 3 := rfl
    rw [hs]
    field_simp
    nlinarith [hsqrt3sq]
  have hrec : (1:ℝ) / (2 * Real.sqrt 3) ≤ 125 / 433 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt 3)]
    nlinarith [hs3]
  rw [hTdiff]
  have h1 : (h - 1) * (sqrt3 / 4) - (h - 1) / (4 * Real.sqrt 3)
      = (h - 1) / (2 * Real.sqrt 3) := hident
  have h3 : (h - 1) / (2 * Real.sqrt 3) = (h - 1) * (1 / (2 * Real.sqrt 3)) := by field_simp
  rw [h1, h3]
  exact mul_le_mul hab0 hrec hab0 (by norm_num)

/-- chord between `a ≤ b` in `[1, h0]`: slope bound `√3/4 - a/(8r)`. -/
private theorem p22_bjf_chord_a {a b r : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b) (hb0 : b ≤ h0)
    (hr : Real.sqrt (1 - (a / 2) ^ 2) ≤ r)
    (hcle : √3 / 4 - a / (8 * r) ≤ 103 / 400) :
    p22_bjf_T b - p22_bjf_T a ≤ (b - a) * (103 / 400) := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha1
  have hab0 : (0:ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hTdiff := p22_bjf_Tdiff ha0 hb0
  have hA0 : (0:ℝ) ≤ 1 - (a / 2) ^ 2 := by nlinarith
  have hB0 : (0:ℝ) ≤ 1 - (b / 2) ^ 2 := by nlinarith
  have hpos : (0:ℝ) < Real.sqrt (1 - (b / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hB0) (Real.sqrt_pos.mpr hA0)
  have hWsub := p22_bjf_Wsub (a := a) (b := b) hA0 hB0 hpos
  -- W := (A_b - A_a)/2 ≥ (b-a)·a/(8r)
  have hWge : (Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)) / 2
      ≥ (b - a) * a / (8 * r) := by
    rw [hWsub, div_div_eq_mul_div, div_div_eq_mul_div]
    have hr0 : (0:ℝ) < r := lt_of_le_of_lt (Real.sqrt_nonneg _) (by nlinarith [hr] |>.elim)
    have hX : ((b:ℝ) ^ 2 - a ^ 2) / 4 = (b - a) * (a + b) / 4 := by ring
    rw [hX]
    have hsum : (a:ℝ) + b ≤ 2 * r := by
      have h1 : Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt (1 - (a / 2) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      have h2 : Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2) ≤ 2 * r := by
        have := mul_le_mul_of_nonneg_left hr (by norm_num)
        linarith
      linarith
    have hd : (0:ℝ) < (8:ℝ) * r := by positivity
    have hstep : ((b - a) * (a + b) / 4) / (2 * (Real.sqrt (1 - (b / 2) ^ 2)
        + Real.sqrt (1 - (a / 2) ^ 2)))
        ≥ ((b - a) * (a + b) / 4) / (8 * r) := by
      rw [div_le_div_iff hd (by positivity)]
      have h8 : ((b - a) * (a + b) / 4) * (8 * r)
          ≥ ((b - a) * (a + b) / 4) * (2 * (Real.sqrt (1 - (b / 2) ^ 2)
            + Real.sqrt (1 - (a / 2) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
      nlinarith
    linarith
  -- slope constant: √3/4 ≤ a/(8r) + 103/400 with a ≥ 1 ... (per-instance via norm_num on hc)
  rw [hTdiff]
  have h1 : (Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)) / 2
      ≥ (b - a) * a / (8 * r) := hWge
  have h2 : (b - a) * a / (8 * r) ≥ (b - a) * (√3 / 4 - 103 / 400) := by
    have h3 : (a:ℝ) * 1 ≥ a * 0 := by nlinarith
    have h4 : √3 / 4 - a / (8 * r) ≤ 103 / 400 := hcle
    have h5 : (0:ℝ) ≤ 103 / 400 := by norm_num
    have h6 : (a:ℝ)/(8*r) ≥ √3/4 - 103/400 := by linarith
    have h7 : (b - a) * ((a:ℝ)/(8*r)) ≥ (b - a) * (√3/4 - 103/400) :=
      mul_le_mul hab0 h6 (by nlinarith) (by norm_num)
    have h8 : (b - a) * a / (8 * r) = (b - a) * ((a:ℝ)/(8*r)) := by ring
    rw [h8]
    exact h7
  linarith

/-- `asn` increment bound (monotone-derivative/integral). -/
private theorem p22_bjf_asn_inc {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    asn y - asn x ≤ (y - x) / Real.sqrt (1 - y ^ 2) := by
  show Real.arcsin y - Real.arcsin x ≤ _
  have hle : ∀ t : ℝ, t ∈ Set.uIcc x y →
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - y ^ 2) := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    obtain ⟨ht0, hty⟩ := ht
    refine p22_div_le_div_right (Real.sqrt_pos.mpr (by nlinarith)) ?_
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc x y) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) (Set.uIcc x y) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    obtain ⟨ht0, hty⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hcon2 : ContinuousOn (fun _ : ℝ => 1 / Real.sqrt (1 - y ^ 2)) (Set.uIcc x y) := by
    fun_prop
  have hint : ∫ t in x..y, 1 / Real.sqrt (1 - t ^ 2) = asn y - asn x := by
    have hderiv : ∀ t ∈ Set.uIcc x y, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      obtain ⟨ht0, hty⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hcon2.intervalIntegrable hle
  have hconst : ∫ t in x..y, (1:ℝ) / Real.sqrt (1 - y ^ 2)
      = (y - x) / Real.sqrt (1 - y ^ 2) := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul]
  rw [hint, hconst] at hmono
  exact hmono

/-- Φ-window slide: with `phi²·(1-(tau·sig)²) ≥ 1` and the chord bound,
    the asn-growth over `[1, h]` is at most `2k·(h-1)·C·phi`. -/
private theorem p22_bjf_incle {k : ℕ} {h x y sig tau phi C : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y = p22_bjf_T h * Real.sin (Real.pi / k))
    (hT0 : 0 ≤ p22_bjf_T h) (hy1 : y < 1) (hTtau : p22_bjf_T h ≤ tau)
    (hsub : y - x ≤ (h - 1) * C * sig)
    (hh1 : 1 ≤ h) (hsig0 : 0 ≤ sig) (hC0 : 0 ≤ C) (hphi0 : 0 ≤ phi)
    (hphi : (1 - (tau * sig) ^ 2) * phi ^ 2 ≥ 1) :
    2 * (k:ℝ) * (asn y - asn x) ≤ 2 * (k:ℝ) * (h - 1) * C * phi := by
  have hy0 : (0:ℝ) ≤ y := by rw [hy]; exact mul_nonneg hT0 hsig0
  have hinc := p22_bjf_asn_inc hx0 hxy hy1
  have hy2 : y ^ 2 ≤ (tau * sig) ^ 2 := by
    rw [hy]
    exact pow_le_pow_left₀ (mul_nonneg hT0 hsig0)
      (mul_le_mul hTtau hsig0 (le_of_lt (by positivity)) hsig0) 2
  have hQ : (0:ℝ) < 1 - y ^ 2 := by nlinarith
  have hQ1 : (0:ℝ) ≤ 1 - (tau * sig) ^ 2 := by nlinarith
  have hsqrt1 : Real.sqrt (1 - y ^ 2) ≥ Real.sqrt (1 - (tau * sig) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hphiP : (0:ℝ) < phi := lt_of_le_of_lt hphi0 (by
    have h2 : (0:ℝ) < (1 - (tau * sig) ^ 2) * phi ^ 2 := hphi
    nlinarith)
  have hphige : Real.sqrt (1 - (tau * sig) ^ 2) ≥ 1 / phi := by
    refine Real.le_sqrt (by nlinarith) hQ1 |>.mpr ?_
    have h3 : (1:ℝ)/phi/phi = 1/(phi*phi) := by field_simp
    rw [h3, inv_le_iff_one_le_mul₀ (by positivity)]
    exact hphi
  have hdiv : (1:ℝ) / Real.sqrt (1 - y ^ 2) ≤ phi := by
    have h1 : (1:ℝ) ≤ phi * Real.sqrt (1 - y ^ 2) := by
      have h2 : phi * Real.sqrt (1 - y ^ 2) ≥ phi * Real.sqrt (1 - (tau * sig) ^ 2) :=
        mul_le_mul_of_nonneg_left hsqrt1 hphi0
      have h3 : phi * Real.sqrt (1 - (tau * sig) ^ 2) ≥ 1 := by
        have h4 := hphige
        have h5 : (0:ℝ) < Real.sqrt (1 - (tau * sig) ^ 2) :=
          lt_of_le_of_lt (by nlinarith) hQ1 |>.elim
        sorry
      linarith
    rw [div_le_iff₀ hQ]
    linarith
  have hstep : (y - x) / Real.sqrt (1 - y ^ 2) ≤ (h - 1) * C * phi := by
    have h1 : (y - x) * 1 / Real.sqrt (1 - y ^ 2)
        ≤ ((h - 1) * C * sig) * phi := by
      refine mul_le_mul (by linarith) (by
        exact mul_le_mul (by linarith) (le_of_lt hphiP) (by linarith) (by linarith))
        (by nlinarith) (by linarith)
      · linarith
    have h2 : (y - x) * 1 / Real.sqrt (1 - y ^ 2) = (y - x) / Real.sqrt (1 - y ^ 2) := by ring
    rw [h2] at h1
    exact h1
  calc 2 * (k:ℝ) * (asn y - asn x)
      ≤ 2 * (k:ℝ) * ((y - x) / Real.sqrt (1 - y ^ 2)) :=
        mul_le_mul_of_nonneg_left hinc (by positivity)
    _ ≤ 2 * (k:ℝ) * ((h - 1) * C * phi) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)

/-- quadratic majorant: `asn w ≤ w+w³/6+w⁵/10` for `w² ≤ 17/64`. -/
private theorem p22_bjf_asn_quad {w : ℝ} (hw : 0 ≤ w) (hwu : w ^ 2 ≤ 17 / 64) :
    asn w ≤ w + w ^ 3 / 6 + w ^ 5 / 10 := by
  show Real.arcsin w ≤ _
  have hdom : ∀ t ∈ Set.Icc (0:ℝ) w,
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have hu : t ^ 2 ≤ (17:ℝ) / 64 := by nlinarith
    have hu0 : (0:ℝ) ≤ t ^ 2 := by nlinarith
    have hQ : 0 < 1 - t ^ 2 := by nlinarith
    have hu2 : t ^ 4 ≤ ((17:ℝ)/64) ^ 2 := by nlinarith
    have hu3 : t ^ 6 ≤ ((17:ℝ)/64) ^ 3 := by nlinarith
    have hcert : 1 - 3 * t ^ 2 - t ^ 4 - t ^ 6 ≥ 0 := by linarith
    have hkey : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2) ≥ 1 := by
      have hex : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2)
          = 1 + t ^ 4 * (1 - 3 * t ^ 2 - t ^ 4 - t ^ 6) / 4 := by ring
      rw [hex]
      exact le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (by nlinarith) hcert) (by norm_num : (0:ℝ) ≤ 4))
    have hP : (0:ℝ) < 1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4 := by nlinarith
    have hge : (0:ℝ) ≤ 1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4 := le_of_lt hP
    have hsq : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2) ≥ 1 := by
      have h1 : ((1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2)) ^ 2
          = (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (by nlinarith)]
      have h2 : (0:ℝ) ≤ (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2) :=
        mul_nonneg hge (Real.sqrt_nonneg _)
      nlinarith [hkey, h2]
    exact (div_le_iff₀ hQ).mpr (by linarith [hsq])
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hw] at ht
    obtain ⟨ht0, htw⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hw] at ht
      obtain ⟨ht0, htw⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc (0:ℝ) w))
  have hbase4 : IntervalIntegrable (fun t : ℝ => t ^ 4) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 4) (Set.uIcc (0:ℝ) w))
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.uIcc (0:ℝ) w))
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)) MeasureTheory.volume (0:ℝ) w :=
    hc1.add ((hbase.const_mul (1/2)).add (hbase4.const_mul (1/2)))
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
      = w + w ^ 3 / 6 + w ^ 5 / 10 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
        MeasureTheory.volume (0:ℝ) w from (hbase.const_mul (1/2)).add (hbase4.const_mul (1/2))),
      intervalIntegral.integral_add (hbase.const_mul (1/2)) (hbase4.const_mul (1/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

/-- septic majorant: `asn w ≤ w+w³/6+w⁵/10+3w⁷/28` for `w² ≤ 19/50`. -/
private theorem p22_bjf_asn_sept {w : ℝ} (hw : 0 ≤ w) (hwu : w ^ 2 ≤ 19 / 50) :
    asn w ≤ w + w ^ 3 / 6 + w ^ 5 / 10 + 3 * w ^ 7 / 28 := by
  show Real.arcsin w ≤ _
  have hdom : ∀ t ∈ Set.Icc (0:ℝ) w,
      1 / Real.sqrt (1 - t ^ 2)
      ≤ 1 + ((1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have hu : t ^ 2 ≤ (19:ℝ) / 50 := by nlinarith
    have hu0 : (0:ℝ) ≤ t ^ 2 := by nlinarith
    have hQ : 0 < 1 - t ^ 2 := by nlinarith
    have hu2 : t ^ 4 ≤ ((19:ℝ)/50) ^ 2 := by nlinarith
    have hu3 : t ^ 6 ≤ ((19:ℝ)/50) ^ 3 := by nlinarith
    have hu4 : t ^ 8 ≤ ((19:ℝ)/50) ^ 4 := by nlinarith
    have hu5 : t ^ 10 ≤ ((19:ℝ)/50) ^ 5 := by nlinarith
    have hcert : 1 / 4 + 7 * t ^ 2 / 8 - 15 * t ^ 4 / 64 - t ^ 6 / 64 - 9 * t ^ 10 / 16 ≥ 0 := by
      linarith
    have hkey : (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2
        * (1 - t ^ 2) ≥ 1 := by
      have hex : (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2 * (1 - t ^ 2)
          = 1 + t ^ 2 * (1 / 4 + 7 * t ^ 2 / 8 - 15 * t ^ 4 / 64 - t ^ 6 / 64
            - 9 * t ^ 10 / 16) := by ring
      rw [hex]
      exact le_add_of_nonneg_right (mul_nonneg hu0 hcert)
    have hP : (0:ℝ) < 1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6) := by
      nlinarith
    have hge : (0:ℝ) ≤ 1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6) := le_of_lt hP
    have hsq : (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
        * Real.sqrt (1 - t ^ 2) ≥ 1 := by
      have h1 : ((1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
          * Real.sqrt (1 - t ^ 2)) ^ 2
          = (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2 * (1 - t ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (by nlinarith)]
      have h2 : (0:ℝ) ≤ (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
          * Real.sqrt (1 - t ^ 2) := mul_nonneg hge (Real.sqrt_nonneg _)
      nlinarith [hkey, h2]
    exact (div_le_iff₀ hQ).mpr (by linarith [hsq])
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hw] at ht
    obtain ⟨ht0, htw⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hw] at ht
      obtain ⟨ht0, htw⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc (0:ℝ) w))
  have hbase4 : IntervalIntegrable (fun t : ℝ => t ^ 4) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 4) (Set.uIcc (0:ℝ) w))
  have hbase6 : IntervalIntegrable (fun t : ℝ => t ^ 6) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 6) (Set.uIcc (0:ℝ) w))
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.uIcc (0:ℝ) w))
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)))
      MeasureTheory.volume (0:ℝ) w :=
    hc1.add ((hbase.const_mul (1/2)).add ((hbase4.const_mul (1/2)).add
      (hbase6.const_mul (3/4))))
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
      = w + w ^ 3 / 6 + w ^ 5 / 10 + 3 * w ^ 7 / 28 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2
        + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
        MeasureTheory.volume (0:ℝ) w
        from (hbase.const_mul (1/2)).add ((hbase4.const_mul (1/2)).add
          (hbase6.const_mul (3/4)))),
      intervalIntegral.integral_add (hbase.const_mul (1/2))
        ((hbase4.const_mul (1/2)).add (hbase6.const_mul (3/4))),
      intervalIntegral.integral_add (hbase4.const_mul (1/2)) (hbase6.const_mul (3/4)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow, integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

end Kepler.Text
