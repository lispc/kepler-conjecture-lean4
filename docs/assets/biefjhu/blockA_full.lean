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
    have hasin : Real.arcsin (x / 2) ≤ Real.pi / 3 := by
      refine le_trans (Real.arcsin_le_arcsin hx2) ?_
      have h3 : Real.arcsin (Real.sin (Real.pi / 3)) = Real.pi / 3 :=
        Real.arcsin_sin (by have := Real.pi_pos; have := Real.pi_lt_d4; linarith)
          (by have := Real.pi_lt_d4; linarith)
      rw [Real.sin_pi_div_three] at h3
      rw [h3]
      exact le_refl _
    constructor
    · have h4 : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      linarith [hasin, h4]
    · have h5 : Real.arcsin (x / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
      linarith [h5, Real.pi_pos]
  have hxeq : p22_bjf_T a = Real.cos (Real.pi / 3 - Real.arcsin (a / 2)) :=
    p22_bjf_Tcos a ha0 (by linarith [h126, hble])
  have hbeq : p22_bjf_T b = Real.cos (Real.pi / 3 - Real.arcsin (b / 2)) :=
    p22_bjf_Tcos b hb0 (by linarith [h126, hble])
  rw [hxeq, hbeq]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
  · exact (hrange b (le_trans ha hab) hb).1
  · exact (hrange a ha hb).2
  · have h1 : Real.arcsin (a / 2) ≤ Real.arcsin (b / 2) := Real.arcsin_le_arcsin hab2
    linarith

/-- sqrt-subtraction identity used by the chord bounds. -/
private theorem p22_bjf_sqrtAB (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpos : 0 < Real.sqrt x + Real.sqrt y) :
    Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have h2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
  rw [eq_div_iff (ne_of_gt hpos)]
  nlinarith [h1, h2]

/-- global chord from 1 (rational constant `2887/10000 ≥ 1/(2√3)`). -/
private theorem p22_bjf_chord_up {h : ℝ} (h1h : 1 ≤ h) (hh0 : h ≤ h0) :
    p22_bjf_T h - p22_bjf_T 1 ≤ (h - 1) * 2887 / 10000 := by
  have hs3 : (433:ℝ)/250 ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hTdiff := p22_bjf_Tdiff (a := 1) (by norm_num) (by linarith)
  rw [p22_bjf_T1] at hTdiff
  have hA0 : (0:ℝ) ≤ 1 - (h / 2) ^ 2 := by nlinarith
  have hA0s : (0:ℝ) < 1 - (h / 2) ^ 2 := by
    have h2 : (h0:ℝ) ≤ 2 := by norm_num [h0]
    nlinarith
  have hA1 : (0:ℝ) ≤ 1 - (1 / 2) ^ 2 := by norm_num
  have hpos : (0:ℝ) < Real.sqrt (1 - (1 / 2) ^ 2) + Real.sqrt (1 - (h / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hA1) (Real.sqrt_pos.mpr hA0s)
  have hWsub : Real.sqrt (1 - (1 / 2) ^ 2) - Real.sqrt (1 - (h / 2) ^ 2)
      = ((h:ℝ) ^ 2 - 1) / 4
        / (Real.sqrt (1 - (1 / 2) ^ 2) + Real.sqrt (1 - (h / 2) ^ 2)) := by
    rw [p22_bjf_sqrtAB (1 - (1 / 2) ^ 2) (1 - (h / 2) ^ 2) hA1 hA0 hpos]
    have h4 : (1:ℝ) - (1 / 2) ^ 2 - (1 - (h / 2) ^ 2) = ((h:ℝ) ^ 2 - 1) / 4 := by ring
    rw [h4]
  have hAle : Real.sqrt (1 - (h / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by
    refine Real.sqrt_le_sqrt ?_
    have h2 : (1:ℝ) ≤ h ^ 2 := by nlinarith
    have h3 : (1:ℝ) - (h / 2) ^ 2 ≤ 3 / 4 := by linarith
    exact h3
  have hB : Real.sqrt (1 - (1 / 2) ^ 2) = Real.sqrt 3 / 2 := by
    have h34 : (1:ℝ) - (1 / 2) ^ 2 = 3 / 4 := by norm_num
    rw [h34, Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
    norm_num
  have hsum : Real.sqrt (1 - (1 / 2) ^ 2) + Real.sqrt (1 - (h / 2) ^ 2) ≤ Real.sqrt 3 := by
    have hB' : Real.sqrt (1 - (1 / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by rw [hB]
    linarith
  have hab0 : (0:ℝ) ≤ h - 1 := sub_nonneg.mpr h1h
  have hd1 : (0:ℝ) < (2:ℝ) * Real.sqrt 3 := by positivity
  -- W := (√(3/4) - √(1-h²/4))/2 ≥ (h-1)/(4√3)
  have hWge : (Real.sqrt (1 - (1 / 2) ^ 2) - Real.sqrt (1 - (h / 2) ^ 2)) / 2
      ≥ (h - 1) / (4 * Real.sqrt 3) := by
    have hW2 : (Real.sqrt (1 - (1 / 2) ^ 2) - Real.sqrt (1 - (h / 2) ^ 2)) / 2
        = ((h:ℝ) ^ 2 - 1) / (8 * (Real.sqrt (1 - (1 / 2) ^ 2)
          + Real.sqrt (1 - (h / 2) ^ 2))) := by
      rw [hWsub]
      ring
    have h2le : (2:ℝ) ≤ (h:ℝ) + 1 := by linarith
    have h15 : (8:ℝ)*(Real.sqrt (1 - (1 / 2) ^ 2) + Real.sqrt (1 - (h / 2) ^ 2))
        ≤ (h:ℝ) * Real.sqrt 3 + Real.sqrt 3 := by linarith
    have h16 : (h:ℝ) * Real.sqrt 3 + Real.sqrt 3
        ≤ ((h:ℝ) + 1) * (4 * Real.sqrt 3) := by nlinarith [h2le]
    have hpos3 : (0:ℝ) < Real.sqrt 3 := lt_of_le_of_lt (by norm_num) hs3
    rw [hW2, ge_iff_le, div_le_div_iff (by positivity) (by positivity)]
    nlinarith [h15, h16, hab0, h2le, hpos3]
  -- conclude: (h-1)·√3/4 - W ≤ (h-1)/(2√3) ≤ (h-1)·2887/10000
  have hsqrt3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.sq_sqrt (by norm_num)
  have hident : (h - 1) * (sqrt3 / 4) - (h - 1) / (4 * Real.sqrt 3)
      = (h - 1) / (2 * Real.sqrt 3) := by
    have hs : sqrt3 = Real.sqrt 3 := rfl
    rw [hs]
    field_simp
    nlinarith [hsqrt3sq]
  have hrec : (1:ℝ) / (2 * Real.sqrt 3) ≤ 125 / 433 := by
    rw [div_le_iff₀ hd1]
    nlinarith [hsqrt3pos, hsqrt3sq]
  rw [hTdiff]
  have h1 : (h - 1) * (sqrt3 / 4) - (h - 1) / (4 * Real.sqrt 3)
      = (h - 1) / (2 * Real.sqrt 3) := hident
  have h3 : (h - 1) / (2 * Real.sqrt 3) = (h - 1) * (1 / (2 * Real.sqrt 3)) := by field_simp
  rw [h1, h3]
  exact mul_le_mul hab0 hrec hab0 (by norm_num)

/-- chord between `a ≤ b` in `[1, h0]` with slope bound `κ ≥ √3/4 - a/(8r)`,
    `r ≥ √(1-(a/2)²)`. -/
private theorem p22_bjf_chord_a {a b r κ : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b) (hb0 : b ≤ h0)
    (hr : Real.sqrt (1 - (a / 2) ^ 2) ≤ r) (hr0 : 0 < r)
    (hcle : √3 / 4 - a / (8 * r) ≤ κ) :
    p22_bjf_T b - p22_bjf_T a ≤ (b - a) * κ := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha1
  have hab0 : (0:ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hTdiff := p22_bjf_Tdiff ha0 (le_trans ha0 hab)
  have hA0 : (0:ℝ) ≤ 1 - (a / 2) ^ 2 := by nlinarith
  have hB0 : (0:ℝ) ≤ 1 - (b / 2) ^ 2 := by nlinarith
  have hA0s : (0:ℝ) < 1 - (a / 2) ^ 2 := by
    have h2 : (h0:ℝ) ≤ 2 := by norm_num [h0]
    nlinarith
  have hB0s : (0:ℝ) < 1 - (b / 2) ^ 2 := by
    have h2 : (h0:ℝ) ≤ 2 := by norm_num [h0]
    nlinarith
  have hpos : (0:ℝ) < Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hA0s) (Real.sqrt_pos.mpr hB0s)
  have hWsub : Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)
      = ((b:ℝ) ^ 2 - a ^ 2) / 4
        / (Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2)) := by
    rw [p22_bjf_sqrtAB (1 - (a / 2) ^ 2) (1 - (b / 2) ^ 2) hA0 hB0 hpos]
    have h4 : (1:ℝ) - (a / 2) ^ 2 - (1 - (b / 2) ^ 2) = ((b:ℝ) ^ 2 - a ^ 2) / 4 := by ring
    rw [h4]
  have hsum : (a:ℝ) + b ≤ 2 * r := by
    have h1 : Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt (1 - (a / 2) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h2 : (2:ℝ) * Real.sqrt (1 - (a / 2) ^ 2) ≤ 2 * r :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    linarith
  have hsum0 : (0:ℝ) < Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) := by
    have h1 : (0:ℝ) ≤ Real.sqrt (1 - (b / 2) ^ 2) := Real.sqrt_nonneg _
    linarith [hA0s]
  -- W := (√(1-a²/4) - √(1-b²/4))/2 ≥ (b-a)·a/(8r)
  have hWge : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
      ≥ (b - a) * a / (8 * r) := by
    have hW2 : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
        = ((b:ℝ) ^ 2 - a ^ 2) / (8 * (Real.sqrt (1 - (a / 2) ^ 2)
          + Real.sqrt (1 - (b / 2) ^ 2))) := by
      rw [hWsub]
      ring
    rw [hW2, ge_iff_le, div_le_div_iff (by positivity) (by positivity)]
    refine mul_le_mul hab0 ?_ (by nlinarith) (by positivity)
    -- goal: (b-a)*a*(8*S) ≤ (b²-a²)*(8*r)
    have h15 : (a:ℝ) * (Real.sqrt (1 - (a / 2) ^ 2)
        + Real.sqrt (1 - (b / 2) ^ 2)) ≤ ((a:ℝ) + b) * r := by
      have h16 : (a:ℝ) * (Real.sqrt (1 - (a / 2) ^ 2)
          + Real.sqrt (1 - (b / 2) ^ 2)) ≤ (a:ℝ) * (2 * r) :=
        mul_le_mul_of_nonneg_left hsum (by nlinarith)
      have h17 : ((a:ℝ) + b) * r ≥ (a:ℝ) * (2 * r) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith [h16, h17]
    nlinarith [h15, hab0, ha1, hsum0]
  rw [hTdiff]
  have h1 : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
      ≥ (b - a) * a / (8 * r) := hWge
  have h2 : (b - a) * a / (8 * r) ≥ (b - a) * (√3 / 4 - κ) := by
    have h3 : √3 / 4 - a / (8 * r) ≤ κ := hcle
    have h4 : (a:ℝ)/(8*r) ≥ √3 / 4 - κ := by linarith
    exact mul_le_mul hab0 h4 (by nlinarith) (by positivity)
  linarith

/-- `asn` increment bound. -/
private theorem p22_bjf_asn_inc {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    asn y - asn x ≤ (y - x) / Real.sqrt (1 - y ^ 2) := by
  show Real.arcsin y - Real.arcsin x ≤ _
  have hle : ∀ t ∈ Set.Icc x y →
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - y ^ 2) := by
    intro t ht
    obtain ⟨ht0, hty⟩ := ht
    exact inv_le_inv₀ (Real.sqrt_pos.mpr (by nlinarith : (0:ℝ) < 1 - y ^ 2))
      (Real.sqrt_pos.mpr (by nlinarith : (0:ℝ) < 1 - t ^ 2))
      (Real.sqrt_le_sqrt (by nlinarith))
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
    simp [asn, Real.arcsin_zero]
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hcon2.intervalIntegrable hle
  have hconst : ∫ t in x..y, (1:ℝ) / Real.sqrt (1 - y ^ 2)
      = (y - x) / Real.sqrt (1 - y ^ 2) := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul]
  rw [hint, hconst] at hmono
  exact hmono

/-- Φ-window slide: `2k·(asn y - asn x) ≤ 2k(h-1)·C·phi` given
    `phi²(1-(tau·sig)²) ≥ sig²`, `y = T h·sin(π/k) ≤ tau·sig < 1`, `y-x ≤ (h-1)·C·sig`. -/
private theorem p22_bjf_incle {k : ℕ} {h x y sig tau phi C : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y = p22_bjf_T h * Real.sin (Real.pi / k))
    (hT0 : 0 ≤ p22_bjf_T h) (hy1 : y < 1) (hTtau : p22_bjf_T h ≤ tau)
    (hsub : y - x ≤ (h - 1) * C * sig)
    (hh1 : 1 ≤ h) (hsin0 : 0 ≤ Real.sin (Real.pi / k))
    (hsig : Real.sin (Real.pi / k) ≤ sig) (hsigP : 0 < sig)
    (hsig0 : 0 ≤ sig) (hC0 : 0 ≤ C) (hphi0 : 0 ≤ phi)
    (hQ1 : tau * sig < 1)
    (hphi : (1 - (tau * sig) ^ 2) * phi ^ 2 ≥ sig ^ 2) :
    2 * (k:ℝ) * (asn y - asn x) ≤ 2 * (k:ℝ) * (h - 1) * C * phi := by
  have hy0 : (0:ℝ) ≤ y := by rw [hy]; exact mul_nonneg hT0 hsin0
  have hinc := p22_bjf_asn_inc hx0 hxy hy1
  have hy2 : y ^ 2 ≤ (tau * sig) ^ 2 := by
    rw [hy]
    refine pow_le_pow_left₀ (mul_nonneg hT0 hsin0) ?_ 2
    exact mul_le_mul hTtau hsig (le_of_lt (by positivity)) hsig0
  have hQ : (0:ℝ) < 1 - y ^ 2 := by nlinarith
  have hQ0 : (0:ℝ) ≤ 1 - (tau * sig) ^ 2 := by nlinarith
  have hsqrt1 : Real.sqrt (1 - y ^ 2) ≥ Real.sqrt (1 - (tau * sig) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hphiP : (0:ℝ) < phi := by
    have h2 : (0:ℝ) < (1 - (tau * sig) ^ 2) * phi ^ 2 := hphi
    have h3 : (0:ℝ) < sig ^ 2 := by nlinarith
    nlinarith
  have hsq1 : (sig / phi) ^ 2 ≤ 1 - (tau * sig) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by nlinarith : (0:ℝ) < phi ^ 2)]
    linarith
  have hsq2 : sig / phi ≤ Real.sqrt (1 - (tau * sig) ^ 2) :=
    (Real.le_sqrt (by positivity) hQ0).mpr hsq1
  have hsigle : (sig:ℝ) ≤ phi * Real.sqrt (1 - y ^ 2) := by
    have h3 : (sig:ℝ)/phi ≤ Real.sqrt (1 - y ^ 2) := le_trans hsq2 hsqrt1
    have h4 : (sig:ℝ) = phi * (sig / phi) := by field_simp
    rw [h4]
    exact mul_le_mul_of_nonneg_left h3 hphi0
  have hstep : (y - x) / Real.sqrt (1 - y ^ 2) ≤ (h - 1) * C * phi := by
    rw [div_le_iff₀ hQ]
    refine le_trans hsub (mul_le_mul_of_nonneg_left ?_ (by linarith))
    exact mul_le_mul_of_nonneg_left hsigle hC0
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
