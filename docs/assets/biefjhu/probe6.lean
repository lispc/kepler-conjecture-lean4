import Kepler.Text.PackingAuto22
namespace Kepler.Text

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
        (div_nonneg (mul_nonneg (by nlinarith : (0:ℝ) ≤ t ^ 4) hcert) (by norm_num : (0:ℝ) ≤ 4))
    have hP : (0:ℝ) < 1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4 := by nlinarith
    have hge : (0:ℝ) ≤ 1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4 := le_of_lt hP
    have hsq : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2) ≥ 1 := by
      have h1 : ((1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2)) ^ 2
          = (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (by nlinarith)]
      have h2 : (0:ℝ) ≤ (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2) :=
        mul_nonneg hge (Real.sqrt_nonneg _)
      nlinarith [hkey, h2]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by linarith [hsq])
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
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
      = w + w ^ 3 / 6 + w ^ 5 / 10 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
        MeasureTheory.volume (0:ℝ) w from (hbase.const_mul (1/2)).add (hbase4.const_mul (1/2))),
      intervalIntegral.integral_add (hbase.const_mul (1/2)) (hbase4.const_mul (1/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow,
      integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

end Kepler.Text
