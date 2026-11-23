import Kepler.Text.TaylorSecond.Basic
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

variable {n : ℕ}

/-- Coordinate Fréchet partials agree with ordinary derivatives along
`Function.update` coordinate lines. -/
theorem partial1_eq_deriv_update {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (i : Fin n) :
    partial1 i f x = deriv (fun t => f (Function.update x i t)) (x i) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using (hf.differentiableAt one_ne_zero).hasFDerivAt
  have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
  simpa only [partial1, coord, Function.comp_def] using h.deriv.symm

/-- The same bridge at second order, with HOL's `partial2 j i` order. -/
theorem partial2_eq_deriv_update {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j i : Fin n) :
    partial2 j i f x = deriv (fun t => partial1 i f (Function.update x j t)) (x j) := by
  exact partial1_eq_deriv_update (contDiffAt_partial1 hf i) j

#print axioms partial1_eq_deriv_update
#print axioms partial2_eq_deriv_update

end Kepler.Text.TaylorSecond
