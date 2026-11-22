import Kepler.Text.Ox3q1hConcaveKit

open Set Filter Topology

namespace Kepler.Text

/-- Concavity from explicit first and second derivatives on the open interval,
with only continuity required at the endpoints. -/
theorem concaveOn_of_hasDerivAt2_nonpos_on {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hf2 : ∀ t ∈ Set.Ioo a b, HasDerivAt f' (f'' t) t)
    (hneg : ∀ t ∈ Set.Ioo a b, f'' t ≤ 0) :
    ConcaveOn ℝ (Set.Icc a b) f := by
  by_cases hab : a ≤ b
  · refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Icc a b) (f := f)
      (f' := f') (f'' := f'') (convex_Icc a b) hcont ?_ ?_ ?_
    · intro t ht
      have ht' : t ∈ Set.Ioo a b := by rwa [interior_Icc] at ht
      exact (hf t ht').hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo a b := by rwa [interior_Icc] at ht
      exact (hf2 t ht').hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo a b := by rwa [interior_Icc] at ht
      exact hneg t ht'
  · have hempty : Set.Icc a b = ∅ := Set.Icc_eq_empty hab
    rw [hempty]
    exact ⟨convex_empty, by simp⟩

/-- Shifted-concavity supply form for an interval on which the explicit second
derivative is bounded above by `K`. -/
theorem concave_shifted_of_hasDerivAt2_le_on {f f' f'' : ℝ → ℝ} {a b K : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hf : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hf2 : ∀ t ∈ Set.Ioo a b, HasDerivAt f' (f'' t) t)
    (hbnd : ∀ t ∈ Set.Ioo a b, f'' t ≤ K) :
    ConcaveOn ℝ (Set.Icc a b) (fun t => f t - K / 2 * t * t) := by
  have hqcont : ContinuousOn (fun t : ℝ => K / 2 * t * t) (Set.Icc a b) := by fun_prop
  have hq : ∀ t : ℝ, HasDerivAt (fun q : ℝ => K / 2 * q * q) (K * t) t := by
    intro t
    have hc : HasDerivAt (fun x => K / 2 * x) ((K / 2) * 1) t :=
      HasDerivAt.const_mul (K / 2) (hasDerivAt_id t)
    have h := hc.mul (hasDerivAt_id t)
    rw [show (fun x => K / 2 * x) * id = fun x => K / 2 * x * x from rfl] at h
    rw [mul_one, mul_one] at h
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hq2 : ∀ t : ℝ, HasDerivAt (fun q : ℝ => K * q) K t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul K
  refine concaveOn_of_hasDerivAt2_nonpos_on
    (f' := fun t => f' t - K * t) (f'' := fun t => f'' t - K)
    (hcont.sub hqcont) ?_ ?_ ?_
  · intro t ht
    exact (hf t ht).sub (hq t)
  · intro t ht
    exact (hf2 t ht).sub (hq2 t)
  · intro t ht
    linarith [hbnd t ht]

#print axioms concaveOn_of_hasDerivAt2_nonpos_on
#print axioms concave_shifted_of_hasDerivAt2_le_on

end Kepler.Text
