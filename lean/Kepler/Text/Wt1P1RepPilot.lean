import Kepler.Text.Wt1TowerDomain
import Kepler.Text.Gamma4ValCornerKit

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-- The D5chain `matan''` atom is nonnegative on the representative box.
This is only the structural sign part of its external tight-range certificate. -/
theorem wt1_rep_d5chainA_nonneg (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.49175)
    (h5l : (2.23176 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352)
    (h6l : (2.23176 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 ≤ lfun (y5 * 0.5) * (w1WA y4 y5 y6 * (w1gAD y4 y5 y6) ^ 2) := by
  have hd : 0 < w1d4A y4 y5 y6 := w1d4A_pos y4 y5 y6 h4l (by linarith)
    (by linarith) h5h (by linarith) h6h
  have hW : 0 ≤ w1WA y4 y5 y6 := by
    unfold w1WA w1WOf
    exact div_nonneg (by linarith) hd.le
  have hnum : (0 : ℝ) ≤ 1.26 - y5 * 0.5 := by linarith
  have hlf : 0 ≤ lfun (y5 * 0.5) := by
    unfold lfun h0
    exact div_nonneg hnum (by norm_num)
  exact mul_nonneg hlf (mul_nonneg hW (sq_nonneg _))

/-- A rational corner value of the same D5chain atom, evaluated using the
pinned `Wt1TowerDeriv` definitions. -/
theorem wt1_rep_d5chainA_corner_lower :
    (0.010529 : ℝ) ≤ lfun (2.23176 * 0.5) *
      (w1WA 2.4635 2.23176 2.23176 * (w1gAD 2.4635 2.23176 2.23176) ^ 2) := by
  norm_num [w1WA, w1WOf, w1d4A, w1gAD, w1gDfun, w1Dlt, w1DltD, w1d4AD, lfun, h0]

/-- Real aggregation glue for the representative `p0_i0j1k1` box.  The six
slot bounds are hypotheses: this theorem does not internalize their external
Bernstein certificates. -/
theorem wt1_rep_aggregate_glue (y4 y5 y6 : ℝ)
    (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.49175)
    (_h5l : (2.23176 : ℝ) ≤ y5) (_h5h : y5 ≤ 2.46352)
    (_h6l : (2.23176 : ℝ) ≤ y6) (_h6h : y6 ≤ 2.46352)
    (hS1 : (0.01645 : ℝ) ≤ w1SEADD y4 y5 y6)
    (hS2 : (0.018146 : ℝ) ≤ w1SEBDD y4 y5 y6)
    (hS3 : (0.002887 : ℝ) ≤ w1SECDD y4 y5 y6)
    (hD5 : 2 * (-(25 / 13) : ℝ) * w1DIHAD y4 y5 y6 +
      lfun (y5 * 0.5) * w1DIHADD y4 y5 y6 ≤ -(0.01387 : ℝ))
    (hD6 : lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6 ≤ (0.10528 : ℝ))
    (hD4 : -(1.00883 : ℝ) ≤ w1DIHCDD y4 y5 y6) :
    w1F2 y4 y5 y6 ≤ -(0.013 : ℝ) := by
  obtain ⟨hk1lo, hk1hi, hk2lo, hk2hi⟩ := g4v_AB_bounds
  have hk1pos : (0 : ℝ) ≤ 2 * mm1 / Real.pi := le_trans (by norm_num) hk1lo
  have hk2pos : (0 : ℝ) ≤ 8 * mm2 / Real.pi := le_trans (by norm_num) hk2lo
  have hcut : h0cut y4 = 1 := Kepler.NliBanks19.nb19_h0cut_eq_one (by
    norm_num [h0]
    linarith)
  have hSE : (0.037483 : ℝ) ≤ w1SEADD y4 y5 y6 + w1SEBDD y4 y5 y6 +
      w1SECDD y4 y5 y6 := by linarith
  have hSEprod : (0.6443106485 : ℝ) * 0.037483 ≤
      (2 * mm1 / Real.pi) * (w1SEADD y4 y5 y6 + w1SEBDD y4 y5 y6 +
        w1SECDD y4 y5 y6) := mul_le_mul hk1lo hSE (by norm_num) hk1pos
  have hD5nonpos : 2 * (-(25 / 13) : ℝ) * w1DIHAD y4 y5 y6 +
      lfun (y5 * 0.5) * w1DIHADD y4 y5 y6 ≤ 0 := by linarith
  have hD5step : (8 * mm2 / Real.pi) *
      (2 * (-(25 / 13) : ℝ) * w1DIHAD y4 y5 y6 +
        lfun (y5 * 0.5) * w1DIHADD y4 y5 y6) ≤
      (0.0647174928 : ℝ) * (2 * (-(25 / 13) : ℝ) * w1DIHAD y4 y5 y6 +
        lfun (y5 * 0.5) * w1DIHADD y4 y5 y6) := by
    simpa [mul_comm] using mul_le_mul_of_nonpos_left hk2lo hD5nonpos
  have hD5prod : (8 * mm2 / Real.pi) *
      (2 * (-(25 / 13) : ℝ) * w1DIHAD y4 y5 y6 +
        lfun (y5 * 0.5) * w1DIHADD y4 y5 y6) ≤
      (0.0647174928 : ℝ) * (-(0.01387 : ℝ)) :=
    hD5step.trans (mul_le_mul_of_nonneg_left hD5 (by norm_num))
  have hD6prod : (8 * mm2 / Real.pi) * (lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6) ≤
      (0.0647175183 : ℝ) * 0.10528 :=
    (mul_le_mul_of_nonneg_left hD6 hk2pos).trans
      (mul_le_mul_of_nonneg_right hk2hi (by norm_num))
  have hlf4lo : (0.0543 : ℝ) ≤ lfun (y4 * 0.5) := by
    unfold lfun h0
    norm_num
    linarith
  have hlf4hi : lfun (y4 * 0.5) ≤ (0.10866 : ℝ) := by
    unfold lfun h0
    norm_num
    linarith
  have hlf4pos : (0 : ℝ) ≤ lfun (y4 * 0.5) := le_trans (by norm_num) hlf4lo
  have hk2lf4lo : (0.0647174928 : ℝ) * 0.0543 ≤
      (8 * mm2 / Real.pi) * lfun (y4 * 0.5) :=
    mul_le_mul hk2lo hlf4lo (by norm_num) hk2pos
  have hk2lf4hi : (8 * mm2 / Real.pi) * lfun (y4 * 0.5) ≤
      (0.0647175183 : ℝ) * 0.10866 :=
    mul_le_mul hk2hi hlf4hi hlf4pos (by linarith)
  have hwlo : -(0.00449 : ℝ) ≤
      (8 * mm2 / Real.pi) * lfun (y4 * 0.5) - 0.008 := by
    nlinarith [hk2lf4lo]
  have hwneg : (8 * mm2 / Real.pi) * lfun (y4 * 0.5) - 0.008 < 0 := by
    nlinarith [hk2lf4hi]
  have hD4prod : ((8 * mm2 / Real.pi) * lfun (y4 * 0.5) - 0.008) *
      w1DIHCDD y4 y5 y6 ≤ (-(0.00449 : ℝ)) * (-(1.00883 : ℝ)) := by
    by_cases hd4 : 0 ≤ w1DIHCDD y4 y5 y6
    · have hnonpos : ((8 * mm2 / Real.pi) * lfun (y4 * 0.5) - 0.008) *
          w1DIHCDD y4 y5 y6 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hwneg.le hd4
      nlinarith [hnonpos]
    · have hd4n : w1DIHCDD y4 y5 y6 ≤ 0 := le_of_not_ge hd4
      have hstep1 : ((8 * mm2 / Real.pi) * lfun (y4 * 0.5) - 0.008) *
          w1DIHCDD y4 y5 y6 ≤ (-(0.00449 : ℝ)) * w1DIHCDD y4 y5 y6 :=
        mul_le_mul_of_nonpos_right hwlo hd4n
      have hstep2 : (-(0.00449 : ℝ)) * w1DIHCDD y4 y5 y6 ≤
          (-(0.00449 : ℝ)) * (-(1.00883 : ℝ)) := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonpos_left hD4 (by norm_num : (-(0.00449 : ℝ)) ≤ 0))
      exact hstep1.trans hstep2
  unfold w1F2
  rw [hcut]
  nlinarith [hSEprod, hD5prod, hD6prod, hD4prod]

#print axioms wt1_rep_d5chainA_nonneg
#print axioms wt1_rep_d5chainA_corner_lower
#print axioms wt1_rep_aggregate_glue

end Kepler.Text
