/-
Kepler.Text.Gamma4VolY — the `volY` y-partial lower bounds and the six
`gamma4fgcy` y-partial positivity statements on the RIBCYXU box
(lane `gamma4-w4`, W4-c).
-/
import Kepler.Text.Gamma4Mono
import Kepler.Text.Gamma4Mono2

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- `deltaY > 0` on the RIBCYXU box (from the crude `Δ ≥ 127.67` bound). -/
theorem g4d_deltaY_pos {y1 y2 y3 y4 y5 y6 : ℝ} (h : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < deltaY y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq h
  have h1 := (g4d_deltaX_bounds hbox).1
  rw [deltaY]
  linarith


/-- `∂volY/∂y1 ≥ 0.2345` on the RIBCYXU box. -/
theorem g4dDVolY1_ge {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0.2345 ≤ g4dDVolY1 y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX1_bounds hbox
  obtain ⟨hDlo, hDhi⟩ := g4d_deltaX_bounds hbox
  have hsqrt : Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) ≤ 11.346 := by
    rw [deltaY]
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 11.346)]
    nlinarith [hDhi]
  unfold g4dDVolY1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hDXlo, h1, hsqrt]


/-- `∂volY/∂y2 ≥ 0.2345` on the RIBCYXU box. -/
theorem g4dDVolY2_ge {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0.2345 ≤ g4dDVolY2 y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX2_bounds hbox
  obtain ⟨hDlo, hDhi⟩ := g4d_deltaX_bounds hbox
  have hsqrt : Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) ≤ 11.346 := by
    rw [deltaY]
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 11.346)]
    nlinarith [hDhi]
  unfold g4dDVolY2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hDXlo, h2, hsqrt]


/-- `∂volY/∂y3 ≥ 0.2345` on the RIBCYXU box. -/
theorem g4dDVolY3_ge {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0.2345 ≤ g4dDVolY3 y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX3_bounds hbox
  obtain ⟨hDlo, hDhi⟩ := g4d_deltaX_bounds hbox
  have hsqrt : Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) ≤ 11.346 := by
    rw [deltaY]
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 11.346)]
    nlinarith [hDhi]
  unfold g4dDVolY3
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hDXlo, h3, hsqrt]


/-- `∂volY/∂y4 ≥ 0.2345` on the RIBCYXU box. -/
theorem g4dDVolY4_ge {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0.2345 ≤ g4dDVolY4 y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_deltaX4_bounds hbox
  obtain ⟨hDlo, hDhi⟩ := g4d_deltaX_bounds hbox
  have hsqrt : Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) ≤ 11.346 := by
    rw [deltaY]
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 11.346)]
    nlinarith [hDhi]
  unfold g4dDVolY4
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hDXlo, h4, hsqrt]


/-- `∂volY/∂y5 ≥ 0.2345` on the RIBCYXU box. -/
theorem g4dDVolY5_ge {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0.2345 ≤ g4dDVolY5 y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_deltaX5_bounds hbox
  obtain ⟨hDlo, hDhi⟩ := g4d_deltaX_bounds hbox
  have hsqrt : Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) ≤ 11.346 := by
    rw [deltaY]
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 11.346)]
    nlinarith [hDhi]
  unfold g4dDVolY5
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hDXlo, h5, hsqrt]


/-- `∂volY/∂y6 ≥ 0.2345` on the RIBCYXU box. -/
theorem g4dDVolY6_ge {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0.2345 ≤ g4dDVolY6 y1 y2 y3 y4 y5 y6 := by
  have hbox := g4dInBox_sq hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX6_bounds hbox
  obtain ⟨hDlo, hDhi⟩ := g4d_deltaX_bounds hbox
  have hsqrt : Real.sqrt (deltaY y1 y2 y3 y4 y5 y6) ≤ 11.346 := by
    rw [deltaY]
    rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 11.346)]
    nlinarith [hDhi]
  unfold g4dDVolY6
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hDXlo, h6, hsqrt]


/-- `∂gamma4fgcy/∂y1 ≥ 0.0207 > 0` on the RIBCYXU box. -/
theorem g4d_partial_y1_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < g4dDVolY1 y1 y2 y3 y4 y5 y6 - g4dDVol4f1 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) := by
  have h1 := g4dDVolY1_ge hb
  have h2 := g4dDVol4f1_le hb
  linarith


/-- `∂gamma4fgcy/∂y2 ≥ 0.0207 > 0` on the RIBCYXU box. -/
theorem g4d_partial_y2_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < g4dDVolY2 y1 y2 y3 y4 y5 y6 - g4dDVol4f2 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) := by
  have h1 := g4dDVolY2_ge hb
  have h2 := g4dDVol4f2_le hb
  linarith


/-- `∂gamma4fgcy/∂y3 ≥ 0.0207 > 0` on the RIBCYXU box. -/
theorem g4d_partial_y3_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < g4dDVolY3 y1 y2 y3 y4 y5 y6 - g4dDVol4f3 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) := by
  have h1 := g4dDVolY3_ge hb
  have h2 := g4dDVol4f3_le hb
  linarith


/-- `∂gamma4fgcy/∂y4 ≥ 0.0207 > 0` on the RIBCYXU box. -/
theorem g4d_partial_y4_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < g4dDVolY4 y1 y2 y3 y4 y5 y6 - g4dDVol4f4 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) := by
  have h1 := g4dDVolY4_ge hb
  have h2 := g4dDVol4f4_le hb
  linarith


/-- `∂gamma4fgcy/∂y5 ≥ 0.0207 > 0` on the RIBCYXU box. -/
theorem g4d_partial_y5_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < g4dDVolY5 y1 y2 y3 y4 y5 y6 - g4dDVol4f5 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) := by
  have h1 := g4dDVolY5_ge hb
  have h2 := g4dDVol4f5_le hb
  linarith


/-- `∂gamma4fgcy/∂y6 ≥ 0.0207 > 0` on the RIBCYXU box. -/
theorem g4d_partial_y6_pos {y1 y2 y3 y4 y5 y6 : ℝ} (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    0 < g4dDVolY6 y1 y2 y3 y4 y5 y6 - g4dDVol4f6 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) := by
  have h1 := g4dDVolY6_ge hb
  have h2 := g4dDVol4f6_le hb
  linarith



#print axioms g4dDVolY1_ge
#print axioms g4dDVolY2_ge
#print axioms g4dDVolY3_ge
#print axioms g4dDVolY4_ge
#print axioms g4dDVolY5_ge
#print axioms g4dDVolY6_ge
#print axioms g4d_partial_y1_pos
#print axioms g4d_partial_y2_pos
#print axioms g4d_partial_y3_pos
#print axioms g4d_partial_y4_pos
#print axioms g4d_partial_y5_pos
#print axioms g4d_partial_y6_pos

end Kepler.Text
