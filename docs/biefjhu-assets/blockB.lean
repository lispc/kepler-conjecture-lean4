/-- sqrt-subtraction identity used by the chord bounds. -/
private theorem p22_bjf_sqrtAB (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpos : 0 < Real.sqrt x + Real.sqrt y) :
    Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have h2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
  rw [eq_div_iff (ne_of_gt hpos)]
  nlinarith [h1, h2]

/-- general chord: `|T b - T a| ≤ (b-a)/(2√3) ≤ (b-a)·2887/10000` on `[1, h0]`. -/
private theorem p22_bjf_chord {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h0) :
    p22_bjf_T b - p22_bjf_T a ≤ (b - a) * 2887 / 10000 := by
  have hab0 : (0:ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hTdiff := p22_bjf_Tdiff ha (le_trans ha hab)
  have hA0 : (0:ℝ) ≤ 1 - (a / 2) ^ 2 := by nlinarith
  have hB0 : (0:ℝ) ≤ 1 - (b / 2) ^ 2 := by nlinarith
  have hA0s : (0:ℝ) < 1 - (a / 2) ^ 2 := by
    have h2 : (h0:ℝ) < 2 := by norm_num [h0]
    have h3 : (a:ℝ) ≤ h0 := le_trans hab hb
    nlinarith
  have hB0s : (0:ℝ) < 1 - (b / 2) ^ 2 := by
    have h2 : (h0:ℝ) < 2 := by norm_num [h0]
    nlinarith
  have hpos : (0:ℝ) < Real.sqrt (1 - (b / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hB0s) (Real.sqrt_pos.mpr hA0s)
  have hWsub : Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)
      = ((b:ℝ) ^ 2 - a ^ 2) / 4
        / (Real.sqrt (1 - (b / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2)) := by
    rw [p22_bjf_sqrtAB hB0 hA0 hpos]
    have h4 : (1:ℝ) - (b / 2) ^ 2 - (1 - (a / 2) ^ 2) = ((b:ℝ) ^ 2 - a ^ 2) / 4 := by ring
    rw [h4]
  -- W := (√(1-b²/4) - √(1-a²/4))/2 ≥ (b-a)/(4√3)
  have hWge : (Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)) / 2
      ≥ (b - a) / (4 * Real.sqrt 3) := by
    have hW2 : (Real.sqrt (1 - (b / 2) ^ 2) - Real.sqrt (1 - (a / 2) ^ 2)) / 2
        = ((b:ℝ) ^ 2 - a ^ 2) / (8 * (Real.sqrt (1 - (b / 2) ^ 2)
          + Real.sqrt (1 - (a / 2) ^ 2))) := by
      rw [hWsub]
      ring
    have hsum : Real.sqrt (1 - (b / 2) ^ 2) + Real.sqrt (1 - (a / 2) ^ 2) ≤ Real.sqrt 3 := by
      have h1 : Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by
        refine Real.sqrt_le_sqrt ?_
        have h2 : (1:ℝ) ≤ b ^ 2 := by nlinarith
        have h3 : (1:ℝ) - (b / 2) ^ 2 ≤ 3 / 4 := by linarith
        exact h3
      have h2 : Real.sqrt (1 - (a / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by
        refine Real.sqrt_le_sqrt ?_
        have h3 : (1:ℝ) - (a / 2) ^ 2 ≤ 3 / 4 := by nlinarith
        exact h3
      have h4 : Real.sqrt 3 / 2 + Real.sqrt 3 / 2 = Real.sqrt 3 := by ring
      rw [h4]
      linarith
    have hsqrt3pos : (0:ℝ) < Real.sqrt 3 :=
      lt_of_le_of_lt (by norm_num) (by
        have h : (433:ℝ)/250 ≤ Real.sqrt 3 :=
          (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
        linarith)
    rw [hW2, ge_iff_le, div_le_div_iff (by positivity) (by positivity)]
    nlinarith [hsum, hab0, hsqrt3pos]
  -- conclude: (b-a)·√3/4 - W ≤ (b-a)/(2√3) ≤ (b-a)·2887/10000
  have hsqrt3sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.sq_sqrt (by norm_num)
  have hident : (b - a) * (sqrt3 / 4) - (b - a) / (4 * Real.sqrt 3)
      = (b - a) / (2 * Real.sqrt 3) := by
    have hs : sqrt3 = Real.sqrt 3 := rfl
    rw [hs]
    field_simp
    nlinarith [hsqrt3sq]
  have hrec : (1:ℝ) / (2 * Real.sqrt 3) ≤ 125 / 433 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt 3)]
    have h : (433:ℝ)/250 ≤ Real.sqrt 3 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    nlinarith
  rw [hTdiff]
  have h1 : (b - a) * (sqrt3 / 4) - (b - a) / (4 * Real.sqrt 3)
      = (b - a) / (2 * Real.sqrt 3) := by
    have hs : sqrt3 = Real.sqrt 3 := rfl
    have h2 : (b - a) * (sqrt3 / 4) - (b - a) / (4 * Real.sqrt 3)
        = (b - a) * ((sqrt3 / 4) - (1 / (4 * Real.sqrt 3))) := by ring
    rw [h2, hs]
    have h3 : (Real.sqrt 3 / 4) - (1 / (4 * Real.sqrt 3))
        = (Real.sqrt 3 - 1 / Real.sqrt 3) / 4 := by field_simp
    rw [h3]
    have h4 : Real.sqrt 3 - 1 / Real.sqrt 3 = 2 / Real.sqrt 3 := by
      field_simp
      nlinarith [hsqrt3sq]
    rw [h4]
    field_simp
    nlinarith [hsqrt3sq]
  rw [h1]
  have h5 : (b - a) / (2 * Real.sqrt 3) = (b - a) * (1 / (2 * Real.sqrt 3)) := by field_simp
  rw [h5]
  exact mul_le_mul hab0 hrec hab0 (by norm_num)

/-- asn-increment slide with Φ-window certificate (generic slack `S`): -/
private theorem p22_bjf_incle {k : ℕ} {h x y sig tau phi S : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y = p22_bjf_T h * Real.sin (Real.pi / k))
    (hT0 : 0 ≤ p22_bjf_T h) (hy1 : y < 1) (hTtau : p22_bjf_T h ≤ tau)
    (hS0 : 0 ≤ S)
    (hsin0 : 0 ≤ Real.sin (Real.pi / k)) (hsig : Real.sin (Real.pi / k) ≤ sig)
    (hphi : (1 - (tau * sig) ^ 2) * phi ^ 2 ≥ sig ^ 2) :
    2 * (k:ℝ) * (asn y - asn x) ≤ 2 * (k:ℝ) * S * phi := by
  have hy0 : (0:ℝ) ≤ y := by rw [hy]; exact mul_nonneg hT0 hsin0
  have hinc := p22_bjf_asn_inc hx0 hxy hy1
  have hy2 : y ^ 2 ≤ (tau * sig) ^ 2 := by
    rw [hy]
    refine pow_le_pow_left₀ (mul_nonneg hT0 hsin0) ?_ 2
    exact mul_le_mul hTtau hsig (le_of_lt (by positivity)) hsig
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
  rw [div_le_iff₀ hQ] at hinc
  have h1 : (y:ℝ) - x ≤ S * (phi * Real.sqrt (1 - y ^ 2)) := by
    refine le_trans hsub (mul_le_mul_of_nonneg_left ?_ hS0)
    exact mul_le_mul_of_nonneg_left hsigle hphi0
  have h2 : S * (phi * Real.sqrt (1 - y ^ 2)) = S * phi * Real.sqrt (1 - y ^ 2) := by ring
  rw [h2] at h1
  calc 2 * (k:ℝ) * (asn y - asn x)
      ≤ 2 * (k:ℝ) * ((y - x) / Real.sqrt (1 - y ^ 2)) :=
        mul_le_mul_of_nonneg_left hinc (by positivity)
    _ ≤ 2 * (k:ℝ) * (S * phi * Real.sqrt (1 - y ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 2 * (k:ℝ) * (S * phi) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (Real.sqrt_nonneg _) (by linarith)

/-- Φ-window certificate for the tail (`k ≥ 12`): the k-cancellation. -/
private theorem p22_bjf_tail_phi (k : ℕ) (hk : 12 ≤ k) :
    (1 - ((235273 / 250000) * (31416 / 10000 / k)) ^ 2)
      * (270126977 / 1000000000) ^ 2 ≥ (31416 / 10000 / k) ^ 2 := by
  have hk2 : ((k:ℝ)) ^ 2 ≥ 144 := by
    have h1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk
    nlinarith
  have hτc : (0:ℝ) ≤ (235273 / 250000) * (31416 / 10000) := by positivity
  have hmain : (270126977 / 1000000000) ^ 2 * (144
      - ((235273 / 250000) * (31416 / 10000)) ^ 2) ≥ (31416 / 10000) ^ 2 := by norm_num
  field_simp
  nlinarith [hk2, hτc, hmain]

/-- tail slide-budget (k-cancellation). -/
private theorem p22_bjf_tail_mono (k : ℕ) (hk : 12 ≤ k) :
    ((26:ℝ)/100) * (2 * k * (2887 / 10000) * (270126977 / 1000000000))
      ≤ 2 * Real.pi - 5777 / 1000 := by
  have hπ : (2:ℝ) * Real.pi ≥ 6283 / 1000 := by
    have := Real.pi_gt_d4
    linarith
  have hτc : (235273:ℝ) / 250000 * (31416 / 10000) ≤ 149 / 50 := by norm_num
  have hk1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk
  have hk2 : ((k:ℝ)) ^ 2 ≥ 144 := by nlinarith [hk1]
  have hφk : (270126977:ℝ) / 1000000000
      ≤ (31416:ℝ) / 10000 / k / Real.sqrt
          (1 - ((235273:ℝ) / 250000 * (31416 / 10000 / k)) ^ 2) := by
    refine (Real.le_sqrt (by positivity) (by
      positivity : (0:ℝ) ≤ 1 - ((235273:ℝ)/250000*(31416/10000/k))^2)).mpr ?_
    rw [div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^2 * (k:ℝ)^2)]
    nlinarith [hk2, hτc]
  have hcancel : ((2:ℝ) * k * (2887 / 10000) * (270126977 / 1000000000))
      ≤ (6283:ℝ) / 1000 - 5777 / 1000 := by
    have h1 : ((2:ℝ) * k * (2887 / 10000)) * ((270126977:ℝ)/1000000000)
        ≤ (2:ℝ) * k * (2887 / 10000) * ((31416:ℝ)/10000/k) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hφk]
    rw [h1]
    have h2 : ((2:ℝ) * k * (2887 / 10000)) * ((31416:ℝ)/10000/k)
        = (2:ℝ) * (2887 / 10000) * (31416 / 10000) := by field_simp
    rw [h2]
    norm_num
  linarith [hπ, hcancel]

/-- single-piece route. -/
private theorem p22_bjf_route1 {k : ℕ} {h sig φ : ℝ} (h1h : 1 ≤ h) (hh0 : h ≤ h0)
    (hwin : (2:ℝ)*k*asn ((sqrt3/2)*Real.sin (Real.pi/k)) ≤ 5.186 + 0.0331*k)
    (hsin0 : 0 ≤ Real.sin (Real.pi / k)) (hsig : Real.sin (Real.pi / k) ≤ sig)
    (hT0 : 0 ≤ p22_bjf_T h)
    (hTtau : p22_bjf_T h ≤ 235273 / 250000)
    (hQ1 : (235273:ℝ)/250000 * sig < 1)
    (hphi : (1 - (235273 / 250000 * sig) ^ 2) * φ ^ 2 ≥ sig ^ 2)
    (hφ0 : 0 ≤ φ)
    (hmono : ((126:ℝ)/100 - 1) * (2 * k * (2887 / 10000) * φ) ≤ 2 * Real.pi - 5777 / 1000) :
    (0.591 - 0.0331 * k + 0.506 * lfun h)
      ≤ 2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)) := by
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hlf : (0.506:ℝ) * lfun h = (253 / 130) * (126 / 100 - h) := by
    have h1 : lfun h = (h0 - h) / (h0 - 1) := rfl
    have h2 : (h0:ℝ) - 1 = 26 / 100 := by rw [h126]; norm_num
    rw [h1, h126] at h1
    rw [h2] at h1
    field_simp at h1 ⊢
    linarith
  have harea : regularSphericalPolygonAreaP22 (p22_bjf_T h) k
      = 2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)) := rfl
  have hchord := p22_bjf_chord h1h hh0 hh0
  have hTtau : p22_bjf_T h ≤ 235273 / 250000 := by
    have h3 : p22_bjf_T 1 = sqrt3 / 2 := p22_bjf_T1
    have h4 : p22_bjf_T h - p22_bjf_T 1 ≤ (h - 1) * 2887 / 10000 := hchord
    rw [h3] at h4
    have hs : (sqrt3:ℝ)/2 ≤ 86603 / 100000 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    have h26 : ((h0:ℝ) - 1) = 26 / 100 := by rw [h126]; norm_num
    linarith
  have hv1 : 0 ≤ (sqrt3:ℝ)/2 * Real.sin (Real.pi/k) := by
    have h1 : (0:ℝ) ≤ sqrt3 / 2 := by
      have hs : (433:ℝ)/250 ≤ Real.sqrt 3 :=
        (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      unfold sqrt3 at hs
      linarith
    exact mul_nonneg h1 hsin0
  have hy1 : p22_bjf_T h * Real.sin (Real.pi/k) < 1 := by
    have h1 : p22_bjf_T h * Real.sin (Real.pi/k) ≤ (235273:ℝ)/250000 * sig := by
      refine mul_le_mul hTtau hsig (le_of_lt (by positivity)) hsig
    have hQ1 : (235273:ℝ)/250000 * sig < 1 := hQ1
    linarith
  have hS0 : (0:ℝ) ≤ (h - 1) * 2887 / 10000 := by
    have h2 : (0:ℝ) ≤ h - 1 := sub_nonneg.mpr h1h
    exact mul_nonneg h2 (by norm_num)
  have hinc := p22_bjf_incle (k := k) (h := h) (x := (sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
    (y := p22_bjf_T h * Real.sin (Real.pi / k)) (sig := sig) (tau := 235273 / 250000)
    (phi := φ) (S := (h - 1) * 2887 / 10000)
    hv1 (le_of_eq rfl) rfl hT0 hy1 hTtau hS0 hsin0 hsig hphi
  have hπ : (2:ℝ) * Real.pi ≥ 6283 / 1000 := by
    have := Real.pi_gt_d4
    linarith
  rw [hlf, harea]
  rw [ge_iff_le]
  rcases le_or_lt (2 * k * (2887 / 10000) * φ) (253 / 130) with hc | hc
  · have h1 : (253:ℝ)/130*(126/100-h) ≤ 253/500 := by nlinarith [h1h]
    have h2 : (0.591:ℝ) - 0.0331*k + (253/130)*(126/100-h)
        + (5.186 + 0.0331*k) + (h-1)*(2*k*(2887/10000)*φ) ≤ 6283/1000 := by
      nlinarith [hπ, hc, h1, hwin]
    nlinarith [h2, hinc, hwin, hπ]
  · have h1 : (253:ℝ)/130*(126/100-h) ≤ (253:ℝ)/130*(126/100-h0) := by
      have h2 : (h:ℝ) ≤ h0 := hh0
      rw [h126] at h2
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h3 : (h:ℝ)-1 ≤ (h0:ℝ)-1 := by linarith
    have h5 : (h-1)*(2*k*(2887/10000)*φ) ≤ ((h0:ℝ)-1)*(2*k*(2887/10000)*φ) := by
      refine mul_le_mul_of_nonneg_right h3 (by positivity)
    have h6 : ((h0:ℝ)-1)*(2*k*(2887/10000)*φ) ≤ 2*Real.pi - 5777/1000 := hmono
    have h7 : (0.591:ℝ) - 0.0331*k + (253:ℝ)/130*(126/100-h0)
        + (h0:ℝ)-1*(2*k*(2887/10000)*φ) ≤ 2*Real.pi - 0.0331*k := by
      have hπ2 : (2:ℝ)*Real.pi - 5777/1000 + 5777/1000 - 0.0331*k ≤ (2:ℝ)*Real.pi := by
        linarith
      nlinarith [hπ, h6, hπ2]
    nlinarith [h7, hinc, hwin, h1, h5, h6]

/-- two-piece route. -/
private theorem p22_bjf_route2 {k : ℕ} {h b sig τ κ φT φF0 : ℝ}
    (h1h : 1 ≤ h) (hh0 : h ≤ h0) (h1b : 1 ≤ b) (hbb : b ≤ h0)
    (hwin : (2:ℝ)*k*asn ((sqrt3/2)*Real.sin (Real.pi/k)) ≤ 5.186 + 0.0331*k)
    (hsin0 : 0 ≤ Real.sin (Real.pi / k)) (hsig : Real.sin (Real.pi / k) ≤ sig)
    (hT0 : 0 ≤ p22_bjf_T h) (hT0b : 0 ≤ p22_bjf_T b)
    (hTtau : ∀ x : ℝ, 1 ≤ x → x ≤ b → p22_bjf_T x ≤ τ)
    (hTtau0 : ∀ x : ℝ, 1 ≤ x → x ≤ h0 → p22_bjf_T x ≤ τ0)
    (hQ1 : τ * sig < 1) (hQ10 : τ0 * sig < 1)
    (hphiT : (1 - (τ * sig) ^ 2) * φT ^ 2 ≥ sig ^ 2)
    (hphiF : (1 - (τ0 * sig) ^ 2) * φF0 ^ 2 ≥ sig ^ 2)
    (hφT0 : 0 ≤ φT) (hφF00 : 0 ≤ φF0) (hκ0 : 0 ≤ κ)
    (hchorda : ∀ x : ℝ, b ≤ x → x ≤ h0 → p22_bjf_T x - p22_bjf_T b ≤ (x-b)*κ)
    (hX1 : (253:ℝ)/130*(126/100-b) + (b-1)*(2*k*(2887/10000)*φT)
      ≤ 2*Real.pi - (5.186 + 0.0331*k))
    (hX2 : (b-1)*(2*k*(2887/10000)*φT)
      + ((h0:ℝ)-b)*(2*k*κ*φF0) ≤ 2*Real.pi - (5.186 + 0.0331*k)) :
    (0.591 - 0.0331 * k + 0.506 * lfun h)
      ≤ 2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)) := by
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hlf : (0.506:ℝ) * lfun h = (253 / 130) * (126 / 100 - h) := by
    have h1 : lfun h = (h0 - h) / (h0 - 1) := rfl
    have h2 : (h0:ℝ) - 1 = 26 / 100 := by rw [h126]; norm_num
    rw [h1, h126] at h1
    rw [h2] at h1
    field_simp at h1 ⊢
    linarith
  have harea : regularSphericalPolygonAreaP22 (p22_bjf_T h) k
      = 2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)) := rfl
  have hπ : (2:ℝ) * Real.pi ≥ 6283 / 1000 := by
    have := Real.pi_gt_d4
    linarith
  rw [harea, hlf]
  rw [ge_iff_le]
  have hbudget : (0.591:ℝ) - 0.0331*k + (253/130)*(126/100-h)
      + (5.186 + 0.0331*k) + 2*(k:ℝ)*(h-1)*(2887/10000)*φT ≤ 2*Real.pi := by
    rcases le_or_lt (2*k*(2887/10000)*φT) (253/130) with hc | hc
    · have h1 : (253:ℝ)/130*(126/100-h) ≤ 253/500 := by nlinarith [h1h]
      nlinarith [hπ, hc, h1, hwin]
    · have h1 : (253:ℝ)/130*(126/100-h) ≤ (253:ℝ)/130*(126/100-b) := by
        have h2 : (h:ℝ) ≤ b := le_trans hh0 hbb
        rw [h126] at h2
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      have h3 : (h:ℝ)-1 ≤ (b:ℝ)-1 := by linarith
      have h5 : (h-1)*(2*k*(2887/10000)*φT) ≤ (b-1)*(2*k*(2887/10000)*φT) := by
        refine mul_le_mul_of_nonneg_right h3 (by positivity)
      nlinarith [hπ, hc, h1, h5, hwin, hX1]
  rcases le_or_lt h b with hcase | hcase
  · -- piece 1
    have hTt : p22_bjf_T h ≤ τ := hTtau h h1h (le_of_lt hcase)
    have hv1 : 0 ≤ (sqrt3:ℝ)/2 * Real.sin (Real.pi/k) := by
      have h1 : (0:ℝ) ≤ sqrt3 / 2 := by
        have hs : (433:ℝ)/250 ≤ Real.sqrt 3 :=
          (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
        unfold sqrt3 at hs
        linarith
      exact mul_nonneg h1 hsin0
    have hy1 : p22_bjf_T h * Real.sin (Real.pi/k) < 1 := by
      have h1 : p22_bjf_T h * Real.sin (Real.pi/k) ≤ τ * sig := by
        refine mul_le_mul hTt hsig (le_of_lt (by positivity)) hsig
      linarith [hQ1]
    have hS0 : (0:ℝ) ≤ (h - 1) * 2887 / 10000 := by
      have h2 : (0:ℝ) ≤ h - 1 := sub_nonneg.mpr h1h
      exact mul_nonneg h2 (by norm_num)
    have hinc := p22_bjf_incle (k := k) (h := h) (x := (sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
      (y := p22_bjf_T h * Real.sin (Real.pi / k)) (sig := sig) (tau := τ)
      (phi := φT) (S := (h - 1) * 2887 / 10000)
      hv1 (le_of_eq rfl) rfl hT0 hy1 hTt hS0 hsin0 hsig hphiT
    have h2 : (h:ℝ)-1 ≤ (b:ℝ)-1 := by linarith
    have h3 : (h-1)*(2*k*(2887/10000)*φT) ≤ (b-1)*(2*k*(2887/10000)*φT) := by
      refine mul_le_mul_of_nonneg_right h2 (by positivity)
    have h5 : (0.591:ℝ) - 0.0331*k + (253/130)*(126/100-h)
        + (5.186 + 0.0331*k) + (b-1)*(2*k*(2887/10000)*φT) ≤ 2*Real.pi := by
      nlinarith [hπ, hX1, hwin, h3]
    linarith [h5, hinc, hbudget]
  · -- piece 2
    have hTb : p22_bjf_T b ≤ τ0 := hTtau0 b h1b hbb
    have hTt : p22_bjf_T h ≤ τ0 := hTtau0 h h1h hh0
    have hmono' : p22_bjf_T b ≤ p22_bjf_T h := p22_bjf_Tmono h1b (le_trans h1b hcase) hh0
    have hv1 : 0 ≤ (sqrt3:ℝ)/2 * Real.sin (Real.pi/k) := by
      have h1 : (0:ℝ) ≤ sqrt3 / 2 := by
        have hs : (433:ℝ)/250 ≤ Real.sqrt 3 :=
          (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
        unfold sqrt3 at hs
        linarith
      exact mul_nonneg h1 hsin0
    have hvb : 0 ≤ p22_bjf_T b * Real.sin (Real.pi/k) := mul_nonneg hT0b hsin0
    have hTb1 : p22_bjf_T b * Real.sin (Real.pi/k) < 1 := by
      have h1 : p22_bjf_T b * Real.sin (Real.pi/k) ≤ τ * sig := by
        refine mul_le_mul (hTtau b h1b hbb) hsig (le_of_lt (by positivity)) hsig
      linarith [hQ1]
    have hTh1 : p22_bjf_T h * Real.sin (Real.pi/k) < 1 := by
      have h1 : p22_bjf_T h * Real.sin (Real.pi/k) ≤ τ0 * sig := by
        refine mul_le_mul hTt hsig (le_of_lt (by positivity)) hsig
      linarith [hQ10]
    have hS0b : (0:ℝ) ≤ (b - 1) * 2887 / 10000 := by
      have h2 : (0:ℝ) ≤ b - 1 := sub_nonneg.mpr h1b
      exact mul_nonneg h2 (by norm_num)
    have hS0h : (0:ℝ) ≤ ((h0:ℝ) - h) * κ := by
      have h2 : (0:ℝ) ≤ (h0:ℝ) - h := sub_nonneg.mpr (le_trans (le_trans h1b hcase) hh0)
      exact mul_nonneg h2 hκ0
    have hinc1 := p22_bjf_incle (k := k) (h := b) (x := (sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
      (y := p22_bjf_T b * Real.sin (Real.pi / k)) (sig := sig) (tau := τ)
      (phi := φT) (S := (b - 1) * 2887 / 10000)
      hv1 (le_of_eq rfl) rfl hT0b hTb1 (hTtau b h1b hbb) hS0b hsin0 hsig hphiT
    have hinc2 := p22_bjf_incle (k := k) (h := h0) (x := p22_bjf_T b * Real.sin (Real.pi/k))
      (y := p22_bjf_T h0 * Real.sin (Real.pi / k)) (sig := sig) (tau := τ0)
      (phi := φF0) (S := ((h0:ℝ) - h) * κ)
      hvb (le_of_eq rfl) rfl
      (mul_nonneg (le_trans hT0b hmono') hsin0) hTh1 (hTtau0 h0 (by norm_num) hh0) hS0h
      hsin0 hsig hphiF
    have hTsplit : 2*(k:ℝ)*(asn (p22_bjf_T h * Real.sin (Real.pi/k)))
        ≤ 2*(k:ℝ)*(asn ((sqrt3:ℝ)/2*Real.sin (Real.pi/k)))
          + (b-1)*(2*k*(2887/10000)*φT) + ((h0:ℝ)-h)*(2*k*κ*φF0) := by
      have h1 := hinc1
      have h2 := hinc2
      have h3 : asn (p22_bjf_T h * Real.sin (Real.pi/k))
          ≤ asn (p22_bjf_T b * Real.sin (Real.pi/k))
          + 2*(k:ℝ)*(((h0:ℝ)-h)*κ*φF0) := by linarith [h2]
      linarith [h1, h3]
    have hLF : (253:ℝ)/130*(126/100-h) ≤ (253:ℝ)/130*(126/100-b) := by
      have h2 : (b:ℝ) ≤ h := le_trans (le_trans h1b hcase) hh0
      rw [h126] at h2
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h5 : (0.591:ℝ) - 0.0331*k + (253:ℝ)/130*(126/100-b)
        + (5.186 + 0.0331*k) + (b-1)*(2*k*(2887/10000)*φT) ≤ 2*Real.pi := by
      nlinarith [hπ, hX1, hwin]
    have h6 : ((h0:ℝ)-h)*(2*k*κ*φF0) ≤ ((h0:ℝ)-b)*(2*k*κ*φF0) := by
      refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [h5, h6, hTsplit, hLF]

end Kepler.Text
