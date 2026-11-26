import Kepler.NliBanks12
import Kepler.Interval.Trans

namespace Kepler.NliWt0LogKit

open Kepler.Text

/-- The negative `matan` branch is the ordinary `artanh` series divided by its argument. -/
theorem wt0_matan_neg_eq_artanh {t : ℝ} (ht : -1 < t) (ht0 : t < 0) :
    matan t = Real.artanh (Real.sqrt (-t)) / Real.sqrt (-t) := by
  have hs1 : Real.sqrt (-t) < 1 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by nlinarith)
  have hmem : Real.sqrt (-t) ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [Real.sqrt_nonneg (-t)], hs1.le⟩
  unfold matan
  rw [if_neg (ne_of_lt ht0), if_neg (not_lt.mpr ht0.le), Real.artanh_eq_half_log hmem]
  ring

/-- NB12's two-sided quadratic bracket on the negative branch. -/
theorem wt0_matan_neg_bracket {t : ℝ} (ht : t < 0) (ht4 : -(1 / 4) ≤ t) :
    1 - t / 3 ≤ matan t ∧ matan t ≤ 1 - t / 3 + 4 * t ^ 2 / 15 :=
  Kepler.NliBanks12.nb12_matan_neg_bracket ht ht4

/-- The same bracket with the removable zero point included. -/
theorem wt0_matan_nonpos_bracket {t : ℝ} (ht0 : t ≤ 0) (ht4 : -(1 / 4) ≤ t) :
    1 - t / 3 ≤ matan t ∧ matan t ≤ 1 - t / 3 + 4 * t ^ 2 / 15 := by
  rcases eq_or_lt_of_le ht0 with rfl | htneg
  · constructor <;> norm_num [matan]
  · exact wt0_matan_neg_bracket htneg ht4

/-- Re-export of the verified positive-term `artanh` series. -/
theorem wt0_real_hasSum_artanh {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) (Real.artanh y) :=
  Kepler.Interval.real_hasSum_artanh hy

/-- Partial sums under-estimate `artanh`; the positive tail has a geometric upper bound. -/
theorem wt0_real_artanh_partial_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤ Real.artanh y ∧
    Real.artanh y ≤ (∑ i ∈ Finset.range N, y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))
      + y ^ (2 * N + 1) / ((1 : ℝ) - y ^ 2) :=
  Kepler.Interval.real_artanh_partial_bounds hy0 hy1 N

example : 1 - (-(1 / 20) : ℝ) / 3 ≤ matan (-(1 / 20)) ∧
    matan (-(1 / 20)) ≤ 1 - (-(1 / 20) : ℝ) / 3 + 4 * (-(1 / 20) : ℝ) ^ 2 / 15 := by
  exact wt0_matan_nonpos_bracket (by norm_num) (by norm_num)

example : 1 - (0 : ℝ) / 3 ≤ matan 0 ∧ matan 0 ≤ 1 - (0 : ℝ) / 3 + 4 * (0 : ℝ) ^ 2 / 15 := by
  exact wt0_matan_nonpos_bracket (by norm_num) (by norm_num)

#print axioms wt0_matan_neg_eq_artanh
#print axioms wt0_matan_neg_bracket
#print axioms wt0_matan_nonpos_bracket
#print axioms wt0_real_hasSum_artanh
#print axioms wt0_real_artanh_partial_bounds

end Kepler.NliWt0LogKit
