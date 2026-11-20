import Kepler.Text.ZTGJoint0000MainSecond

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

noncomputable def ztgSignN2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  g4dDX3 x1 x2 x3 x4 x5 x6 *
      (deltaX x1 x2 x3 x4 x5 x6 *
          (2 * x2 * (2 * (x1 + x6 - x2)) - upsX x1 x2 x6)
        + x2 * g4dDX2 x1 x2 x3 x4 x5 x6 * upsX x1 x2 x6)
    - 2 * x2 * (-x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6 * upsX x1 x2 x6

theorem ztgDihY2_y2_compact (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6)) :
    ztgDihY2_y2 a1 a2 a3 a4 a5 a6 =
      2 * a1 * Real.sqrt (deltaY a1 a2 a3 a4 a5 a6) *
        ztgSignN2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) /
        ((deltaY a1 a2 a3 a4 a5 a6) ^ 2 * (upsX (a1 * a1) (a2 * a2) (a6 * a6)) ^ 2) := by
  have hD : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := hd
  have hApos : 0 < Real.sqrt (4 * (a1 * a1) *
      deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hspos : 0 < Real.sqrt (deltaY a1 a2 a3 a4 a5 a6) := Real.sqrt_pos.mpr hd
  have hA : Real.sqrt (4 * (a1 * a1) *
      deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)) =
      2 * a1 * Real.sqrt (deltaY a1 a2 a3 a4 a5 a6) := by
    rw [show 4 * (a1 * a1) *
        deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) =
        (2 * a1) ^ 2 * deltaY a1 a2 a3 a4 a5 a6 by rw [deltaY]; ring]
    rw [Real.sqrt_mul (sq_nonneg (2 * a1)), Real.sqrt_sq (by positivity)]
  have hs2 : (Real.sqrt (deltaY a1 a2 a3 a4 a5 a6)) ^ 2 = deltaY a1 a2 a3 a4 a5 a6 :=
    Real.sq_sqrt hd.le
  have hD' : 0 < deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2) := by
    simpa only [pow_two] using hD
  have hu' : 0 < upsX (a1 ^ 2) (a2 ^ 2) (a6 ^ 2) := by
    simpa only [pow_two] using hu
  have hspos' : 0 < Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) :=
    Real.sqrt_pos.mpr hD'
  have hs2' : (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 2 =
      deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2) :=
    Real.sq_sqrt hD'.le
  have hs3 : (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 3 =
      deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2) *
        Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) := by
    rw [show (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 3 =
      (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 2 *
        Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) by ring, hs2']
  have hs4 : (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 4 =
      (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) ^ 2 := by
    rw [show (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 4 =
      ((Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 2) ^ 2 by ring, hs2']
  simp only [deltaY] at hA hs2 hspos
  simp only [ztgDihY2_y2, ztgDihX2_x2, g4dDihX2, ztgSignN2, deltaY]
  rw [hA]
  field_simp [ne_of_gt hD', ne_of_gt hu', ne_of_gt hspos']
  simp only [hs2', hs3, hs4]
  field_simp [ne_of_gt hD', ne_of_gt hu', ne_of_gt hspos']
  ring

theorem ztgDihY2_y2_nonpos_of_signN2 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hN : ztgSignN2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) ≤ 0) :
    ztgDihY2_y2 a1 a2 a3 a4 a5 a6 ≤ 0 := by
  rw [ztgDihY2_y2_compact a1 a2 a3 a4 a5 a6 ha1 hd hu]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hN

noncomputable def ztgSignN1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let S := -2 * x1 + x2 + x3 - 2 * x4 + x5 + x6
  let P := g4dDX1 x1 x2 x3 x4 x5 x6
  let d4 := deltaX4 x1 x2 x3 x4 x5 x6
  let D := deltaX x1 x2 x3 x4 x5 x6
  let U := upsX x1 x2 x6
  let V := upsX x1 x3 x5
  let K := d4 * D + x1 * d4 * P - 2 * x1 * D * S
  let M := -S * D + 2 * d4 * P - x1 * S * P - 2 * x1 * x4 * d4 + 4 * x1 * D
  let E := D + x1 * P
  let R := 2 * (x2 + x6 - x1) * V + 2 * (x3 + x5 - x1) * U
  (4 * K + 8 * x1 * M) * D * U * V - 8 * x1 * K * R * D - 4 * E * K * U * V

theorem ztgDihY2_y1_compact (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    ztgDihY2_y1 a1 a2 a3 a4 a5 a6 =
      Real.sqrt (deltaY a1 a2 a3 a4 a5 a6) *
        ztgSignN1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) /
        (2 * a1 * (deltaY a1 a2 a3 a4 a5 a6) ^ 2 *
          (upsX (a1 * a1) (a2 * a2) (a6 * a6)) ^ 2 *
          (upsX (a1 * a1) (a3 * a3) (a5 * a5)) ^ 2) := by
  have hD : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := hd
  have hA : Real.sqrt (4 * (a1 * a1) *
      deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)) =
      2 * a1 * Real.sqrt (deltaY a1 a2 a3 a4 a5 a6) := by
    rw [show 4 * (a1 * a1) *
        deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) =
        (2 * a1) ^ 2 * deltaY a1 a2 a3 a4 a5 a6 by rw [deltaY]; ring]
    rw [Real.sqrt_mul (sq_nonneg (2 * a1)), Real.sqrt_sq (by positivity)]
  have hD' : 0 < deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2) := by
    simpa only [pow_two] using hD
  have hu126' : 0 < upsX (a1 ^ 2) (a2 ^ 2) (a6 ^ 2) := by
    simpa only [pow_two] using hu126
  have hu135' : 0 < upsX (a1 ^ 2) (a3 ^ 2) (a5 ^ 2) := by
    simpa only [pow_two] using hu135
  have hspos' : 0 < Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) :=
    Real.sqrt_pos.mpr hD'
  have hs2 : (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 2 =
      deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2) :=
    Real.sq_sqrt hD'.le
  have hs3 : (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 3 =
      deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2) *
        Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) := by
    rw [show (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 3 =
      (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 2 *
        Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) by ring, hs2]
  have hs4 : (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 4 =
      (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2)) ^ 2 := by
    rw [show (Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 4 =
      ((Real.sqrt (deltaX (a1 ^ 2) (a2 ^ 2) (a3 ^ 2) (a4 ^ 2) (a5 ^ 2) (a6 ^ 2))) ^ 2) ^ 2 by ring, hs2]
  simp only [deltaY] at hA
  simp only [ztgDihY2_y1, ztgDihX2_x1, g4dDihX1, ztgSignN1, deltaY]
  rw [hA]
  field_simp [ne_of_gt hD', ne_of_gt hu126', ne_of_gt hu135', ne_of_gt hspos']
  simp only [hs2, hs3, hs4]
  field_simp [ne_of_gt hD', ne_of_gt hu126', ne_of_gt hu135', ne_of_gt hspos']
  ring

theorem ztgDihY2_y1_nonpos_of_signN1 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5))
    (hN : ztgSignN1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) ≤ 0) :
    ztgDihY2_y1 a1 a2 a3 a4 a5 a6 ≤ 0 := by
  rw [ztgDihY2_y1_compact a1 a2 a3 a4 a5 a6 ha1 hd hu126 hu135]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hN

#print axioms ztgDihY2_y2_compact
#print axioms ztgDihY2_y2_nonpos_of_signN2
#print axioms ztgDihY2_y1_compact
#print axioms ztgDihY2_y1_nonpos_of_signN1

end Kepler.Text
