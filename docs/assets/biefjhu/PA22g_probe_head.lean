import Kepler.Text.PackingAuto22

namespace Kepler.Text

private theorem p22_cos_le_taylor4 {t : ℝ} (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  rcases lt_or_eq_of_le ht with ht0 | rfl
  · have h2 := Real.cos_two_mul_eq_one_sub (t / 2)
    rw [show (2:ℝ) * (t / 2) = t from by ring] at h2
    have h16 : t ^ 2 ≤ 16 := by nlinarith
    have hage : 0 ≤ t / 2 - t ^ 3 / 48 := by
      have h316 : t ^ 3 ≤ 16 * t := by nlinarith [h16, ht]
      nlinarith
    have hsin : t / 2 - t ^ 3 / 48 ≤ Real.sin (t / 2) := by
      have h3 := Real.sin_gt_sub_cube (x := t / 2) (by linarith)
      have hrw : (t / 2) ^ 3 / 6 = t ^ 3 / 48 := by ring
      rw [hrw] at h3
      linarith
    have hspos : 0 ≤ Real.sin (t / 2) := by linarith
    have hss : 0 ≤ Real.sin (t / 2) + (t / 2 - t ^ 3 / 48) := by linarith
    have hsa : 0 ≤ Real.sin (t / 2) - (t / 2 - t ^ 3 / 48) := by linarith
    have hsq : (t / 2 - t ^ 3 / 48) ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
      nlinarith [hss, hsa]
    have hexpl : 2 * (t / 2 - t ^ 3 / 48) ^ 2
        = t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 1152 := by ring
    have ht6 : (0:ℝ) ≤ t ^ 6 := by positivity
    have h2a : t ^ 2 / 2 - t ^ 4 / 24 ≤ 2 * (t / 2 - t ^ 3 / 48) ^ 2 := by
      rw [hexpl]; linarith
    rw [h2]
    linarith [hsq, h2a]
  · norm_num [Real.cos_zero]


private theorem p22_sin_le_taylor5 {y : ℝ} (hy : 0 ≤ y) (hy4 : y ≤ 4) :
    Real.sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 := by
  set h : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t with hh
  have hf : (fun r : ℝ => r - r ^ 3 / 6 + r ^ 5 / 120 - Real.sin r)
      = fun r => (r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) - Real.sin r := by
    funext r; ring
  have hd : ∀ t : ℝ, deriv h t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    intro t
    rw [hh, hf]
    have dF : DifferentiableAt ℝ
        (fun r : ℝ => r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) t := by
      fun_prop
    have hrest : deriv
        (fun r : ℝ => (r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) - Real.sin r) t
        = deriv (fun r : ℝ => r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) t
          - deriv Real.sin t :=
      deriv_fun_sub dF (Real.differentiable_sin t)
    have hid1 : deriv (fun r : ℝ => r) t = 1 := by simp [deriv_id'']
    have d1 : DifferentiableAt ℝ (fun r : ℝ => r) t := by fun_prop
    have d23 : DifferentiableAt ℝ (fun r : ℝ => (-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5) t := by
      fun_prop
    have d3 : DifferentiableAt ℝ (fun r : ℝ => (-1 / 6) * r ^ 3) t := by fun_prop
    have d4 : DifferentiableAt ℝ (fun r : ℝ => (1 / 120) * r ^ 5) t := by fun_prop
    have hadd1 : deriv (fun r : ℝ => r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) t
        = deriv (fun r : ℝ => r) t
          + deriv (fun r : ℝ => (-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5) t :=
      deriv_fun_add d1 d23
    have hadd2 : deriv (fun r : ℝ => (-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5) t
        = deriv (fun r : ℝ => (-1 / 6) * r ^ 3) t
          + deriv (fun r : ℝ => (1 / 120) * r ^ 5) t :=
      deriv_fun_add d3 d4
    have hcm1 : deriv (fun r : ℝ => (-1 / 6) * r ^ 3) t
        = (-1 / 6) * deriv (fun r : ℝ => r ^ 3) t :=
      congrFun (deriv_const_mul_field' (-1 / 6)) t
    have hcm2 : deriv (fun r : ℝ => (1 / 120) * r ^ 5) t
        = (1 / 120) * deriv (fun r : ℝ => r ^ 5) t :=
      congrFun (deriv_const_mul_field' (1 / 120)) t
    have hp3 : deriv (fun r : ℝ => r ^ 3) t = 3 * t ^ 2 := deriv_pow_field (n := 3) (x := t)
    have hp5 : deriv (fun r : ℝ => r ^ 5) t = 5 * t ^ 4 := deriv_pow_field (n := 5) (x := t)
    have hsin1 : deriv Real.sin t = Real.cos t :=
      (Real.hasDerivAt_sin t).deriv
    rw [hrest, hadd1, hadd2, hid1, hcm1, hcm2, hp3, hp5, hsin1]
    ring
  have hdiff : Differentiable ℝ h := by fun_prop
  have key : ∀ s : ℝ, 0 ≤ s → 0 ≤ 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s := by
    intro s hs
    rcases le_or_gt s 4 with hle4 | hge4
    · have hc := p22_cos_le_taylor4 hs hle4
      linarith
    · have hs2pos : (0:ℝ) ≤ s ^ 2 := by nlinarith
      have hsub : 0 ≤ s ^ 2 - 12 := by nlinarith [hge4]
      have hs4 : (0:ℝ) ≤ s ^ 4 / 24 - s ^ 2 / 2 := by
        have he : s ^ 4 / 24 - s ^ 2 / 2 = s ^ 2 * (s ^ 2 - 12) / 24 := by ring
        rw [he]
        exact div_nonneg (mul_nonneg hs2pos hsub) (by norm_num)
      linarith [Real.cos_le_one s, hs4]
  have hge : ∀ t : ℝ, 0 ≤ deriv h t := by
    intro t
    rw [hd t]
    rcases le_or_gt t 0 with hneg | hnonneg
    · have h2 := hd (-t)
      rw [show (-t:ℝ) ^ 2 = t ^ 2 from by ring, show (-t:ℝ) ^ 4 = t ^ 4 from by ring,
        Real.cos_neg] at h2
      have hk := key (-t) (by linarith)
      rw [show (-t:ℝ) ^ 2 = t ^ 2 from by ring, show (-t:ℝ) ^ 4 = t ^ 4 from by ring,
        Real.cos_neg] at hk
      exact hk
    · exact key t (le_of_lt hnonneg)
  have hmono : Monotone h := monotone_of_deriv_nonneg hdiff hge
  have h0 : h 0 = 0 := by
    rw [hh]; norm_num [Real.sin_zero]
  have hle : h 0 ≤ h y := hmono (by nlinarith)
  rw [h0] at hle
  have hle2 : 0 ≤ y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y := hle
  linarith


/-- `a / c ≤ b / c` for `0 < c`. -/
private theorem p22_div_le_div_right {a b c : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    a / c ≤ b / c := by
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hc.le)

/-- `a / c ≤ b / c` for a natural divisor `c > 0`. -/
private theorem p22_div_le_div_nat_right {a b : ℝ} {c : ℕ} (hc : (0:ℝ) < c) (hab : a ≤ b) :
    a / c ≤ b / c := by
  have e1 : a / c = (c:ℝ)⁻¹ * a := by field_simp
  have e2 : b / c = (c:ℝ)⁻¹ * b := by field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hc.le)

/-- `a / d ≤ a / c` for naturals `0 < c ≤ d`. -/
private theorem p22_div_le_div_nat_left {a : ℝ} {c d : ℕ} (ha : 0 ≤ a) (hc : (0:ℝ) < (c:ℝ))
    (hcd : c ≤ d) : a / d ≤ a / c := by
  have hd : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hc (by exact_mod_cast hcd)
  have hinv : (d:ℝ)⁻¹ ≤ (c:ℝ)⁻¹ := (inv_le_inv₀ hd hc).mpr (by exact_mod_cast hcd)
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right hinv ha

/-- `a / d ≤ a / c` for reals `0 < c ≤ d`. -/
private theorem p22_div_le_div_real_left {a c d : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hcd : c ≤ d) : a / d ≤ a / c := by
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have hinv : d⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hd hc).mpr hcd
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right hinv ha

