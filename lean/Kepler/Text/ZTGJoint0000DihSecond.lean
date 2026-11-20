import Kepler.Text.Gamma4DerivSecond
import Kepler.Text.Gamma4Deriv4

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text

theorem ztg_comp2 {g4 : ℝ → ℝ} {V w : ℝ}
    (hg : HasDerivAt (fun s : ℝ => g4 s) V (w * w)) :
    HasDerivAt (fun t => 2 * t * g4 (t * t))
      (2 * g4 (w * w) + 4 * (w * w) * V) w := by
  have hc : HasDerivAt (fun t : ℝ => g4 (t * t)) (V * (2 * w)) w :=
    g4d_hasDerivAt_sq_comp hg
  have h2t : HasDerivAt (fun t : ℝ => 2 * t) 2 w := by
    simpa using (hasDerivAt_id w).const_mul 2
  have hp : HasDerivAt (fun t => 2 * t * g4 (t * t))
      (2 * g4 (w * w) + 2 * w * (V * (2 * w))) w := h2t.mul hc
  exact hp.congr_deriv (by ring)

noncomputable def ztgDihX2_x1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  ((2 * (-(-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * deltaX x1 x2 x3 x4 x5 x6
              + 2 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
              - x1 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) * g4dDX1 x1 x2 x3 x4 x5 x6
              - 2 * x1 * x4 * deltaX4 x1 x2 x3 x4 x5 x6
              + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
          * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (upsX x1 x2 x6 * upsX x1 x3 x5))
        - 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
              + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
              - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6
                * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
          * ((2 * (deltaX x1 x2 x3 x4 x5 x6
                + x1 * g4dDX1 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
              * (upsX x1 x2 x6 * upsX x1 x3 x5)
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
              * (2 * (x2 + x6 - x1) * upsX x1 x3 x5
                + upsX x1 x2 x6 * 2 * (x3 + x5 - x1))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ^ 2)

noncomputable def ztgDihY2_y1 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * g4dDihX1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) +
    4 * (a1 * a1) * (ztgDihX2_x1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))

noncomputable def ztgDihX2_x2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (((-2 * x1 * (-x4 + x5 + x6)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        - (-2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x6 - x2))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2)

noncomputable def ztgDihY2_y2 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * g4dDihX2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) +
    4 * (a2 * a2) * (ztgDihX2_x2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))

noncomputable def ztgDihX2_x3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (((-2 * x1 * (-x4 + x5 + x6)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        - (-2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x5 - x3))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2)

noncomputable def ztgDihY2_y3 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * g4dDihX3 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) +
    4 * (a3 * a3) * (ztgDihX2_x3 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))

noncomputable def ztgDihX2_x4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * g4sP44 x1 x2 x3 x4 x5 x6
        / (4 * (deltaX x1 x2 x3 x4 x5 x6) ^ 2))

noncomputable def ztgDihY2_y4 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * g4dDihX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) +
    4 * (a4 * a4) * (ztgDihX2_x4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))

noncomputable def ztgDihX2_x5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (((-2 * x1 * (x2 + x3 - x4)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        - (-2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6) * ((2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x3 x5
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x3 - x5))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ^ 2)

noncomputable def ztgDihY2_y5 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * g4dDihX5 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) +
    4 * (a5 * a5) * (ztgDihX2_x5 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))

noncomputable def ztgDihX2_x6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  (((-2 * x1 * (x2 + x3 - x4)) * (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        - (-2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6) * ((2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) * upsX x1 x2 x6
            + Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (2 * (x1 + x2 - x6))))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ^ 2)

noncomputable def ztgDihY2_y6 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * g4dDihX6 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) +
    4 * (a6 * a6) * (ztgDihX2_x6 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))

theorem ztg_dihY_hasDerivAt2_y1 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    HasDerivAt (fun t => g4dDDihY1 t a2 a3 a4 a5 a6) (ztgDihY2_y1 a1 a2 a3 a4 a5 a6) a1 := by
  have h := ztg_comp2 (dihXf_hasDerivAt2_x1_x1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) (mul_pos ha1 ha1) (by simpa only [deltaY] using hd) hu126 hu135)
  exact h

theorem ztg_dihY_hasDerivAt2_y2 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    HasDerivAt (fun t => g4dDDihY2 a1 t a3 a4 a5 a6) (ztgDihY2_y2 a1 a2 a3 a4 a5 a6) a2 := by
  have h := ztg_comp2 (dihXf_hasDerivAt2_x2_x2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) (mul_pos ha1 ha1) (by simpa only [deltaY] using hd) hu126)
  exact h

theorem ztg_dihY_hasDerivAt2_y3 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    HasDerivAt (fun t => g4dDDihY3 a1 a2 t a4 a5 a6) (ztgDihY2_y3 a1 a2 a3 a4 a5 a6) a3 := by
  have h := ztg_comp2 (dihXf_hasDerivAt2_x3_x3 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) (mul_pos ha1 ha1) (by simpa only [deltaY] using hd) hu135)
  exact h

theorem ztg_dihY_hasDerivAt2_y4 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    HasDerivAt (fun t => g4dDDihY4 a1 a2 a3 t a5 a6) (ztgDihY2_y4 a1 a2 a3 a4 a5 a6) a4 := by
  have h := ztg_comp2 (dihXf_hasDerivAt2_x4_x4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) (mul_pos ha1 ha1) (by simpa only [deltaY] using hd))
  exact h

theorem ztg_dihY_hasDerivAt2_y5 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    HasDerivAt (fun t => g4dDDihY5 a1 a2 a3 a4 t a6) (ztgDihY2_y5 a1 a2 a3 a4 a5 a6) a5 := by
  have h := ztg_comp2 (dihXf_hasDerivAt2_x5_x5 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) (mul_pos ha1 ha1) (by simpa only [deltaY] using hd) hu135)
  exact h

theorem ztg_dihY_hasDerivAt2_y6 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6)
    (hu126 : 0 < upsX (a1 * a1) (a2 * a2) (a6 * a6))
    (hu135 : 0 < upsX (a1 * a1) (a3 * a3) (a5 * a5)) :
    HasDerivAt (fun t => g4dDDihY6 a1 a2 a3 a4 a5 t) (ztgDihY2_y6 a1 a2 a3 a4 a5 a6) a6 := by
  have h := ztg_comp2 (dihXf_hasDerivAt2_x6_x6 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) (mul_pos ha1 ha1) (by simpa only [deltaY] using hd) hu126)
  exact h


#print axioms ztg_comp2
#print axioms ztg_dihY_hasDerivAt2_y1
#print axioms ztg_dihY_hasDerivAt2_y2
#print axioms ztg_dihY_hasDerivAt2_y3
#print axioms ztg_dihY_hasDerivAt2_y4
#print axioms ztg_dihY_hasDerivAt2_y5
#print axioms ztg_dihY_hasDerivAt2_y6

end Kepler.Text
