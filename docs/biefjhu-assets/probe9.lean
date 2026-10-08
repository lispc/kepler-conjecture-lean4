import Kepler.Text.PackingAuto22
namespace Kepler.Text
noncomputable def T (h : ℝ) : ℝ := h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2

private theorem T1 : T 1 = sqrt3 / 2 := by
  unfold T sqrt3
  have h34 : (1:ℝ) - (1/2)^2 = 3/4 := by norm_num
  rw [h34, Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
  ring

/-- asn increment bound -/
private theorem p22_bjf_asn_inc {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    asn y - asn x ≤ (y - x) / Real.sqrt (1 - y ^ 2) := by
  show Real.arcsin y - Real.arcsin x ≤ _
  have hle : ∀ t : ℝ, t ∈ Set.uIcc x y → 1 / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - y ^ 2) := by
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    obtain ⟨ht0, hty⟩ := ht
    refine p22_div_le_div_right (Real.sqrt_pos.mpr (by nlinarith)) ?_
    exact Real.sqrt_le_sqrt (by nlinarith)
  -- integrate
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc x y) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) (Set.uIcc x y) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    obtain ⟨ht0, hty⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hcon2 : ContinuousOn (fun _ : ℝ => 1 / Real.sqrt (1 - y ^ 2)) (Set.uIcc x y) := by fun_prop
  have hint : ∫ t in x..y, 1 / Real.sqrt (1 - t ^ 2) = asn y - asn x := by
    have hderiv : ∀ t ∈ Set.uIcc x y, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      obtain ⟨ht0, hty⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable hcon2.intervalIntegrable hle
  have hconst : ∫ t in x..y, (1:ℝ) / Real.sqrt (1 - y ^ 2)
      = (y - x) / Real.sqrt (1 - y ^ 2) := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul]
  rw [hint, hconst] at hmono
  exact hmono

end Kepler.Text
