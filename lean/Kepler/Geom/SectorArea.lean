import Mathlib

open MeasureTheory Complex
open scoped Real ENNReal

noncomputable section

/-- The `ℝ≥0∞`-integral of `x ↦ x` over `(0, ρ)` is `ρ²/2` (for `ρ ≥ 0`). -/
theorem lintegral_Ioo_zero_ofReal_id {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ x in Set.Ioo (0 : ℝ) ρ, ENNReal.ofReal x = ENNReal.ofReal (ρ ^ 2 / 2) := by
  have h_int : IntegrableOn (fun x : ℝ => x) (Set.Ioo (0 : ℝ) ρ) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hρ).mp
      intervalIntegral.intervalIntegrable_id
  have h_nn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) ρ)] (fun x : ℝ => x) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact hx.1.le
  have hIoo : ∫ x in Set.Ioo (0 : ℝ) ρ, x = ρ ^ 2 / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ, integral_id]
    ring
  have key := ofReal_integral_eq_lintegral_ofReal
    (μ := volume.restrict (Set.Ioo (0 : ℝ) ρ)) h_int h_nn
  rw [hIoo] at key
  exact key.symm

/-- Area of the open circular sector of radius `ρ` and angle `θ`. -/
theorem sector_area {ρ θ : ℝ} (hρ : 0 ≤ ρ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    volume {z : ℂ | ‖z‖ < ρ ∧ 0 < z.arg ∧ z.arg < θ} = ENNReal.ofReal (ρ ^ 2 * θ / 2) := by
  set S : Set ℂ := {z : ℂ | ‖z‖ < ρ ∧ 0 < z.arg ∧ z.arg < θ} with hS
  set A : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (0 : ℝ) θ with hA
  have hS_meas : MeasurableSet S := by
    rw [hS]
    have h1 : MeasurableSet {z : ℂ | ‖z‖ < ρ} :=
      measurableSet_lt measurable_norm measurable_const
    have h2 : MeasurableSet {z : ℂ | 0 < z.arg} :=
      measurableSet_Ioi.preimage Complex.measurable_arg
    have h3 : MeasurableSet {z : ℂ | z.arg < θ} :=
      measurableSet_Iio.preimage Complex.measurable_arg
    exact h1.inter (h2.inter h3)
  have hA_meas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_Ioo.prod measurableSet_Ioo
  have hA_sub_T : A ⊆ Complex.polarCoord.target := by
    intro p hp
    rw [hA] at hp
    rw [Complex.polarCoord_target]
    refine ⟨hp.1.1, ?_, lt_of_lt_of_le hp.2.2 hθπ⟩
    linarith [hp.2.1, Real.pi_pos]
  -- Polar change of variables.
  have h_polar : volume S =
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator 1 (Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator_one hS_meas]
    exact (Complex.lintegral_comp_polarCoord_symm (S.indicator 1)).symm
  -- Pointwise identification of the pulled-back integrand on the target.
  have h_point : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • S.indicator 1 (Complex.polarCoord.symm p)
        = A.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) p := by
    intro p hp
    rw [Complex.polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have harg : (Complex.polarCoord.symm p).arg = p.2 := by
      rw [Complex.polarCoord_symm_apply]
      rw [show (↑p.1 * (↑(Real.cos p.2) + ↑(Real.sin p.2) * Complex.I))
          = (↑p.1 * (Complex.cos ↑p.2 + Complex.sin ↑p.2 * Complex.I)) by
        rw [Complex.ofReal_cos, Complex.ofReal_sin]]
      exact Complex.arg_mul_cos_add_sin_mul_I hp1 ⟨hp.2.1, hp.2.2.le⟩
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    have hmem : Complex.polarCoord.symm p ∈ S ↔ p ∈ A := by
      rw [hS, hA]
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo]
      rw [hnorm, harg]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨hp1, h1⟩, h2, h3⟩
      · rintro ⟨⟨_, h1⟩, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    by_cases hpA : p ∈ A
    · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem (hmem.mpr hpA)]
      simp
    · rw [Set.indicator_of_notMem hpA,
        Set.indicator_of_notMem (fun h => hpA (hmem.mp h))]
      simp
  have hT_to_A : ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator 1 (Complex.polarCoord.symm p) =
      ∫⁻ p in A, ENNReal.ofReal p.1 := by
    rw [setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet h_point]
    rw [setLIntegral_indicator hA_meas]
    rw [show A ∩ Complex.polarCoord.target = A from Set.inter_eq_left.mpr hA_sub_T]
  rw [h_polar, hT_to_A, hA]
  -- Evaluate the resulting product integral.
  have hprod := setLIntegral_prod (μ := volume) (ν := volume)
    (s := Set.Ioo (0 : ℝ) ρ) (t := Set.Ioo (0 : ℝ) θ)
    (fun p : ℝ × ℝ => ENNReal.ofReal p.1)
    (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable
  change (∫⁻ (p : ℝ × ℝ) in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (0 : ℝ) θ,
      ENNReal.ofReal p.1 ∂(volume.prod volume)) = ENNReal.ofReal (ρ ^ 2 * θ / 2)
  rw [hprod]
  have hinner : ∀ x : ℝ,
      ∫⁻ y in Set.Ioo (0 : ℝ) θ, ENNReal.ofReal x = ENNReal.ofReal x * ENNReal.ofReal θ := by
    intro x
    rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
  simp_rw [hinner]
  rw [lintegral_mul_const _ ENNReal.measurable_ofReal]
  rw [lintegral_Ioo_zero_ofReal_id hρ]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ 2 / 2)]
  congr 1
  ring

end
