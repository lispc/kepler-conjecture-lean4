import Kepler.Text.Gamma4Mono0

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- `g4dDVol4f4 ≤ 0.2138` on the RIBCYXU box (route in `Gamma4Mono0`). -/
theorem g4dDVol4f4_le {y1 y2 y3 y4 y5 y6 : ℝ}
    (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    g4dDVol4f4 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) ≤ 0.2138 := by
  have hbk : g4dRInBox y1 y2 y3 y4 y5 y6 := hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hs1 : g4dDDihY4 y1 y2 y3 y4 y5 y6 ≤ 4.002 * 0.17709 :=
    (g4dDDihY4_of_rbox hbk).2
  have hs2 : g4dDDihY6 y2 y3 y1 y5 y6 y4 ≤ 4 * (-0.0585) :=
    (g4dDDihY6_of_rbox (g4dR_p231564 hbk)).2
  have hs3 : g4dDDihY5 y3 y1 y2 y6 y4 y5 ≤ 4 * (-0.0585) :=
    (g4dDDihY5_of_rbox (g4dR_p312645 hbk)).2
  have hs4 : g4dDDihY4 y1 y5 y6 y4 y2 y3 ≤ 4.002 * 0.17709 :=
    (g4dDDihY4_of_rbox (g4dR_p156423 hbk)).2
  have hs5 : g4dDDihY6 y5 y6 y1 y2 y3 y4 ≤ 4 * (-0.0585) :=
    (g4dDDihY6_of_rbox (g4dR_p561234 hbk)).2
  have hs6 : g4dDDihY5 y6 y1 y5 y3 y4 y2 ≤ 4 * (-0.0585) :=
    (g4dDDihY5_of_rbox (g4dR_p615342 hbk)).2
  have hs7 : g4dDDihY1 y4 y5 y3 y1 y2 y6 ≤ 4.002 * 0.0599 :=
    (g4dDDihY1_of_rbox (g4dR_p453126 hbk)).2
  have hs8 : g4dDDihY3 y5 y3 y4 y2 y6 y1 ≤ 4 * (-0.0585) :=
    (g4dDDihY3_of_rbox (g4dR_p534261 hbk)).2
  have hs9 : g4dDDihY2 y3 y4 y5 y6 y1 y2 ≤ 4 * (-0.0585) :=
    (g4dDDihY2_of_rbox (g4dR_p345612 hbk)).2
  have hs10 : g4dDDihY1 y4 y2 y6 y1 y5 y3 ≤ 4.002 * 0.0599 :=
    (g4dDDihY1_of_rbox (g4dR_p426153 hbk)).2
  have hs11 : g4dDDihY3 y2 y6 y4 y5 y3 y1 ≤ 4 * (-0.0585) :=
    (g4dDDihY3_of_rbox (g4dR_p264531 hbk)).2
  have hs12 : g4dDDihY2 y6 y4 y2 y3 y1 y5 ≤ 4 * (-0.0585) :=
    (g4dDDihY2_of_rbox (g4dR_p642315 hbk)).2
  have hS : g4dDSolY4 y1 y2 y3 y4 y5 y6 + g4dDSolY4 y1 y5 y6 y4 y2 y3 + g4dDSolY1 y4 y5 y3 y1 y2 y6 + g4dDSolY1 y4 y2 y6 y1 y5 y3 ≤ 0.024868 := by
    unfold g4dDSolY4 g4dDSolY1
    linarith [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12]
  have hd1 : 0.9979 * (4 * 0.17625) ≤ lmfun (y1/2) * g4dDDihY4 y1 y2 y3 y4 y5 y6 := by
    have hl := (g4d_lmfun_bounds (y := y1) h1 h1').1
    have hu := (g4d_lmfun_bounds (y := y1) h1 h1').2
    have ht := (g4dDDihY4_of_rbox hbk).1
    exact g4d_weighted_pos hl hu ht (by norm_num)
  have hd2 : 4.002 * (-0.0593) ≤ lmfun (y2/2) * g4dDDihY6 y2 y3 y1 y5 y6 y4 := by
    have hl := (g4d_lmfun_bounds (y := y2) h2 h2').1
    have hu := (g4d_lmfun_bounds (y := y2) h2 h2').2
    have ht := (g4dDDihY6_of_rbox (g4dR_p231564 hbk)).1
    have hX := (g4dDDihY6_of_rbox (g4dR_p231564 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd3 : 4.002 * (-0.0593) ≤ lmfun (y3/2) * g4dDDihY5 y3 y1 y2 y6 y4 y5 := by
    have hl := (g4d_lmfun_bounds (y := y3) h3 h3').1
    have hu := (g4d_lmfun_bounds (y := y3) h3 h3').2
    have ht := (g4dDDihY5_of_rbox (g4dR_p312645 hbk)).1
    have hX := (g4dDDihY5_of_rbox (g4dR_p312645 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd4 : 0.9979 * (4 * 0.0579) ≤ lmfun (y4/2) * g4dDDihY1 y4 y3 y5 y1 y6 y2 := by
    have hl := (g4d_lmfun_bounds (y := y4) h4 h4').1
    have hu := (g4d_lmfun_bounds (y := y4) h4 h4').2
    have ht := (g4dDDihY1_of_rbox (g4dR_p435162 hbk)).1
    exact g4d_weighted_pos hl hu ht (by norm_num)
  have hd5 : 4.002 * (-0.0593) ≤ lmfun (y5/2) * g4dDDihY5 y5 y1 y6 y2 y4 y3 := by
    have hl := (g4d_lmfun_bounds (y := y5) h5 h5').1
    have hu := (g4d_lmfun_bounds (y := y5) h5 h5').2
    have ht := (g4dDDihY5_of_rbox (g4dR_p516243 hbk)).1
    have hX := (g4dDDihY5_of_rbox (g4dR_p516243 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd6 : 4.002 * (-0.0593) ≤ lmfun (y6/2) * g4dDDihY5 y6 y1 y5 y3 y4 y2 := by
    have hl := (g4d_lmfun_bounds (y := y6) h6 h6').1
    have hu := (g4d_lmfun_bounds (y := y6) h6 h6').2
    have ht := (g4dDDihY5_of_rbox (g4dR_p615342 hbk)).1
    have hX := (g4dDDihY5_of_rbox (g4dR_p615342 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hD : -3.0355 ≤ lmfun (y1/2) * g4dDDihY4 y1 y2 y3 y4 y5 y6 + lmfun (y2/2) * g4dDDihY6 y2 y3 y1 y5 y6 y4 + lmfun (y3/2) * g4dDDihY5 y3 y1 y2 y6 y4 y5 + lmfun (y4/2) * g4dDDihY1 y4 y3 y5 y1 y6 y2 + lmfun (y5/2) * g4dDDihY5 y5 y1 y6 y2 y4 y3 + lmfun (y6/2) * g4dDDihY5 y6 y1 y5 y3 y4 y2 + ((-1/(h0-1))/2) * dihY y4 y3 y5 y1 y6 y2 := by
    have hn := (g4d_dihY_bounds_of_rbox (g4dR_p435162 hbk)).2
    have hL : ((-1/(h0-1))/2) * 1.5708 ≤ ((-1/(h0-1))/2) * dihY y4 y3 y5 y1 y6 y2 := by
      have hneg : ((-1/(h0-1))/2 : ℝ) ≤ 0 := by norm_num [h0]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have h1 : 0 ≤ ((-1/(h0-1))/2) * (dihY y4 y3 y5 y1 y6 y2 - Real.pi/2) :=
        mul_nonneg_of_nonpos_of_nonpos hneg (by linarith [hn])
      have h2 : 0 ≤ ((-1/(h0-1))/2) * (Real.pi/2 - 1.5708) :=
        mul_nonneg_of_nonpos_of_nonpos hneg (by linarith [hpi])
      nlinarith [h1, h2]
    have hcoeff : ((-1/(h0-1))/2) * 1.5708 = -(3927/1300) := by norm_num [h0]
    linarith [hd1, hd2, hd3, hd4, hd5, hd6, hL, hcoeff]
  have hc1 : (0:ℝ) ≤ 2 * mm1 / Real.pi := by
    have := g4d_mm1_bounds.1; positivity
  have hc1hi : 2 * mm1 / Real.pi ≤ 0.6456 := by
    have hp := g4d_pi_bounds.1; have hm := g4d_mm1_bounds.2
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]; nlinarith [hp, hm]
  have hc2 : (0:ℝ) ≤ 8 * mm2 / Real.pi := by
    have := g4d_mm2_bounds.1; positivity
  have hc2hi : 8 * mm2 / Real.pi ≤ 0.06512 := by
    have hp := g4d_pi_bounds.1; have hm := g4d_mm2_bounds.2
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]; nlinarith [hp, hm]
  have h1 := g4d_mul_le_upper hc1 hc1hi hS (by norm_num)
  have h2 := g4d_neg_mul_le hc2 hc2hi hD (by norm_num)
  unfold g4dDVol4f4
  nlinarith [h1, h2]

/-- `g4dDVol4f5 ≤ 0.2138` on the RIBCYXU box (route in `Gamma4Mono0`). -/
theorem g4dDVol4f5_le {y1 y2 y3 y4 y5 y6 : ℝ}
    (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    g4dDVol4f5 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) ≤ 0.2138 := by
  have hbk : g4dRInBox y1 y2 y3 y4 y5 y6 := hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hs1 : g4dDDihY5 y1 y2 y3 y4 y5 y6 ≤ 4 * (-0.0585) :=
    (g4dDDihY5_of_rbox hbk).2
  have hs2 : g4dDDihY4 y2 y3 y1 y5 y6 y4 ≤ 4.002 * 0.17709 :=
    (g4dDDihY4_of_rbox (g4dR_p231564 hbk)).2
  have hs3 : g4dDDihY6 y3 y1 y2 y6 y4 y5 ≤ 4 * (-0.0585) :=
    (g4dDDihY6_of_rbox (g4dR_p312645 hbk)).2
  have hs4 : g4dDDihY2 y1 y5 y6 y4 y2 y3 ≤ 4 * (-0.0585) :=
    (g4dDDihY2_of_rbox (g4dR_p156423 hbk)).2
  have hs5 : g4dDDihY1 y5 y6 y1 y2 y3 y4 ≤ 4.002 * 0.0599 :=
    (g4dDDihY1_of_rbox (g4dR_p561234 hbk)).2
  have hs6 : g4dDDihY3 y6 y1 y5 y3 y4 y2 ≤ 4 * (-0.0585) :=
    (g4dDDihY3_of_rbox (g4dR_p615342 hbk)).2
  have hs7 : g4dDDihY2 y4 y5 y3 y1 y2 y6 ≤ 4 * (-0.0585) :=
    (g4dDDihY2_of_rbox (g4dR_p453126 hbk)).2
  have hs8 : g4dDDihY1 y5 y3 y4 y2 y6 y1 ≤ 4.002 * 0.0599 :=
    (g4dDDihY1_of_rbox (g4dR_p534261 hbk)).2
  have hs9 : g4dDDihY3 y3 y4 y5 y6 y1 y2 ≤ 4 * (-0.0585) :=
    (g4dDDihY3_of_rbox (g4dR_p345612 hbk)).2
  have hs10 : g4dDDihY5 y4 y2 y6 y1 y5 y3 ≤ 4 * (-0.0585) :=
    (g4dDDihY5_of_rbox (g4dR_p426153 hbk)).2
  have hs11 : g4dDDihY4 y2 y6 y4 y5 y3 y1 ≤ 4.002 * 0.17709 :=
    (g4dDDihY4_of_rbox (g4dR_p264531 hbk)).2
  have hs12 : g4dDDihY6 y6 y4 y2 y3 y1 y5 ≤ 4 * (-0.0585) :=
    (g4dDDihY6_of_rbox (g4dR_p642315 hbk)).2
  have hS : g4dDSolY5 y1 y2 y3 y4 y5 y6 + g4dDSolY2 y1 y5 y6 y4 y2 y3 + g4dDSolY2 y4 y5 y3 y1 y2 y6 + g4dDSolY5 y4 y2 y6 y1 y5 y3 ≤ 0.024868 := by
    unfold g4dDSolY5 g4dDSolY2
    linarith [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12]
  have hd1 : 4.002 * (-0.0593) ≤ lmfun (y1/2) * g4dDDihY5 y1 y2 y3 y4 y5 y6 := by
    have hl := (g4d_lmfun_bounds (y := y1) h1 h1').1
    have hu := (g4d_lmfun_bounds (y := y1) h1 h1').2
    have ht := (g4dDDihY5_of_rbox hbk).1
    have hX := (g4dDDihY5_of_rbox hbk).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd2 : 0.9979 * (4 * 0.17625) ≤ lmfun (y2/2) * g4dDDihY4 y2 y3 y1 y5 y6 y4 := by
    have hl := (g4d_lmfun_bounds (y := y2) h2 h2').1
    have hu := (g4d_lmfun_bounds (y := y2) h2 h2').2
    have ht := (g4dDDihY4_of_rbox (g4dR_p231564 hbk)).1
    exact g4d_weighted_pos hl hu ht (by norm_num)
  have hd3 : 4.002 * (-0.0593) ≤ lmfun (y3/2) * g4dDDihY6 y3 y1 y2 y6 y4 y5 := by
    have hl := (g4d_lmfun_bounds (y := y3) h3 h3').1
    have hu := (g4d_lmfun_bounds (y := y3) h3 h3').2
    have ht := (g4dDDihY6_of_rbox (g4dR_p312645 hbk)).1
    have hX := (g4dDDihY6_of_rbox (g4dR_p312645 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd4 : 4.002 * (-0.0593) ≤ lmfun (y4/2) * g4dDDihY3 y4 y3 y5 y1 y6 y2 := by
    have hl := (g4d_lmfun_bounds (y := y4) h4 h4').1
    have hu := (g4d_lmfun_bounds (y := y4) h4 h4').2
    have ht := (g4dDDihY3_of_rbox (g4dR_p435162 hbk)).1
    have hX := (g4dDDihY3_of_rbox (g4dR_p435162 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd5 : 0.9979 * (4 * 0.0579) ≤ lmfun (y5/2) * g4dDDihY1 y5 y1 y6 y2 y4 y3 := by
    have hl := (g4d_lmfun_bounds (y := y5) h5 h5').1
    have hu := (g4d_lmfun_bounds (y := y5) h5 h5').2
    have ht := (g4dDDihY1_of_rbox (g4dR_p516243 hbk)).1
    exact g4d_weighted_pos hl hu ht (by norm_num)
  have hd6 : 4.002 * (-0.0593) ≤ lmfun (y6/2) * g4dDDihY3 y6 y1 y5 y3 y4 y2 := by
    have hl := (g4d_lmfun_bounds (y := y6) h6 h6').1
    have hu := (g4d_lmfun_bounds (y := y6) h6 h6').2
    have ht := (g4dDDihY3_of_rbox (g4dR_p615342 hbk)).1
    have hX := (g4dDDihY3_of_rbox (g4dR_p615342 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hD : -3.0355 ≤ lmfun (y1/2) * g4dDDihY5 y1 y2 y3 y4 y5 y6 + lmfun (y2/2) * g4dDDihY4 y2 y3 y1 y5 y6 y4 + lmfun (y3/2) * g4dDDihY6 y3 y1 y2 y6 y4 y5 + lmfun (y4/2) * g4dDDihY3 y4 y3 y5 y1 y6 y2 + lmfun (y5/2) * g4dDDihY1 y5 y1 y6 y2 y4 y3 + lmfun (y6/2) * g4dDDihY3 y6 y1 y5 y3 y4 y2 + ((-1/(h0-1))/2) * dihY y5 y1 y6 y2 y4 y3 := by
    have hn := (g4d_dihY_bounds_of_rbox (g4dR_p516243 hbk)).2
    have hL : ((-1/(h0-1))/2) * 1.5708 ≤ ((-1/(h0-1))/2) * dihY y5 y1 y6 y2 y4 y3 := by
      have hneg : ((-1/(h0-1))/2 : ℝ) ≤ 0 := by norm_num [h0]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have h1 : 0 ≤ ((-1/(h0-1))/2) * (dihY y5 y1 y6 y2 y4 y3 - Real.pi/2) :=
        mul_nonneg_of_nonpos_of_nonpos hneg (by linarith [hn])
      have h2 : 0 ≤ ((-1/(h0-1))/2) * (Real.pi/2 - 1.5708) :=
        mul_nonneg_of_nonpos_of_nonpos hneg (by linarith [hpi])
      nlinarith [h1, h2]
    have hcoeff : ((-1/(h0-1))/2) * 1.5708 = -(3927/1300) := by norm_num [h0]
    linarith [hd1, hd2, hd3, hd4, hd5, hd6, hL, hcoeff]
  have hc1 : (0:ℝ) ≤ 2 * mm1 / Real.pi := by
    have := g4d_mm1_bounds.1; positivity
  have hc1hi : 2 * mm1 / Real.pi ≤ 0.6456 := by
    have hp := g4d_pi_bounds.1; have hm := g4d_mm1_bounds.2
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]; nlinarith [hp, hm]
  have hc2 : (0:ℝ) ≤ 8 * mm2 / Real.pi := by
    have := g4d_mm2_bounds.1; positivity
  have hc2hi : 8 * mm2 / Real.pi ≤ 0.06512 := by
    have hp := g4d_pi_bounds.1; have hm := g4d_mm2_bounds.2
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]; nlinarith [hp, hm]
  have h1 := g4d_mul_le_upper hc1 hc1hi hS (by norm_num)
  have h2 := g4d_neg_mul_le hc2 hc2hi hD (by norm_num)
  unfold g4dDVol4f5
  nlinarith [h1, h2]

/-- `g4dDVol4f6 ≤ 0.2138` on the RIBCYXU box (route in `Gamma4Mono0`). -/
theorem g4dDVol4f6_le {y1 y2 y3 y4 y5 y6 : ℝ}
    (hb : g4dRInBox y1 y2 y3 y4 y5 y6) :
    g4dDVol4f6 y1 y2 y3 y4 y5 y6 (-1/(h0-1)) ≤ 0.2138 := by
  have hbk : g4dRInBox y1 y2 y3 y4 y5 y6 := hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hs1 : g4dDDihY6 y1 y2 y3 y4 y5 y6 ≤ 4 * (-0.0585) :=
    (g4dDDihY6_of_rbox hbk).2
  have hs2 : g4dDDihY5 y2 y3 y1 y5 y6 y4 ≤ 4 * (-0.0585) :=
    (g4dDDihY5_of_rbox (g4dR_p231564 hbk)).2
  have hs3 : g4dDDihY4 y3 y1 y2 y6 y4 y5 ≤ 4.002 * 0.17709 :=
    (g4dDDihY4_of_rbox (g4dR_p312645 hbk)).2
  have hs4 : g4dDDihY3 y1 y5 y6 y4 y2 y3 ≤ 4 * (-0.0585) :=
    (g4dDDihY3_of_rbox (g4dR_p156423 hbk)).2
  have hs5 : g4dDDihY2 y5 y6 y1 y2 y3 y4 ≤ 4 * (-0.0585) :=
    (g4dDDihY2_of_rbox (g4dR_p561234 hbk)).2
  have hs6 : g4dDDihY1 y6 y1 y5 y3 y4 y2 ≤ 4.002 * 0.0599 :=
    (g4dDDihY1_of_rbox (g4dR_p615342 hbk)).2
  have hs7 : g4dDDihY6 y4 y5 y3 y1 y2 y6 ≤ 4 * (-0.0585) :=
    (g4dDDihY6_of_rbox (g4dR_p453126 hbk)).2
  have hs8 : g4dDDihY5 y5 y3 y4 y2 y6 y1 ≤ 4 * (-0.0585) :=
    (g4dDDihY5_of_rbox (g4dR_p534261 hbk)).2
  have hs9 : g4dDDihY4 y3 y4 y5 y6 y1 y2 ≤ 4.002 * 0.17709 :=
    (g4dDDihY4_of_rbox (g4dR_p345612 hbk)).2
  have hs10 : g4dDDihY3 y4 y2 y6 y1 y5 y3 ≤ 4 * (-0.0585) :=
    (g4dDDihY3_of_rbox (g4dR_p426153 hbk)).2
  have hs11 : g4dDDihY2 y2 y6 y4 y5 y3 y1 ≤ 4 * (-0.0585) :=
    (g4dDDihY2_of_rbox (g4dR_p264531 hbk)).2
  have hs12 : g4dDDihY1 y6 y4 y2 y3 y1 y5 ≤ 4.002 * 0.0599 :=
    (g4dDDihY1_of_rbox (g4dR_p642315 hbk)).2
  have hS : g4dDSolY6 y1 y2 y3 y4 y5 y6 + g4dDSolY3 y1 y5 y6 y4 y2 y3 + g4dDSolY6 y4 y5 y3 y1 y2 y6 + g4dDSolY3 y4 y2 y6 y1 y5 y3 ≤ 0.024868 := by
    unfold g4dDSolY6 g4dDSolY3
    linarith [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12]
  have hd1 : 4.002 * (-0.0593) ≤ lmfun (y1/2) * g4dDDihY6 y1 y2 y3 y4 y5 y6 := by
    have hl := (g4d_lmfun_bounds (y := y1) h1 h1').1
    have hu := (g4d_lmfun_bounds (y := y1) h1 h1').2
    have ht := (g4dDDihY6_of_rbox hbk).1
    have hX := (g4dDDihY6_of_rbox hbk).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd2 : 4.002 * (-0.0593) ≤ lmfun (y2/2) * g4dDDihY5 y2 y3 y1 y5 y6 y4 := by
    have hl := (g4d_lmfun_bounds (y := y2) h2 h2').1
    have hu := (g4d_lmfun_bounds (y := y2) h2 h2').2
    have ht := (g4dDDihY5_of_rbox (g4dR_p231564 hbk)).1
    have hX := (g4dDDihY5_of_rbox (g4dR_p231564 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd3 : 0.9979 * (4 * 0.17625) ≤ lmfun (y3/2) * g4dDDihY4 y3 y1 y2 y6 y4 y5 := by
    have hl := (g4d_lmfun_bounds (y := y3) h3 h3').1
    have hu := (g4d_lmfun_bounds (y := y3) h3 h3').2
    have ht := (g4dDDihY4_of_rbox (g4dR_p312645 hbk)).1
    exact g4d_weighted_pos hl hu ht (by norm_num)
  have hd4 : 4.002 * (-0.0593) ≤ lmfun (y4/2) * g4dDDihY5 y4 y3 y5 y1 y6 y2 := by
    have hl := (g4d_lmfun_bounds (y := y4) h4 h4').1
    have hu := (g4d_lmfun_bounds (y := y4) h4 h4').2
    have ht := (g4dDDihY5_of_rbox (g4dR_p435162 hbk)).1
    have hX := (g4dDDihY5_of_rbox (g4dR_p435162 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd5 : 4.002 * (-0.0593) ≤ lmfun (y5/2) * g4dDDihY3 y5 y1 y6 y2 y4 y3 := by
    have hl := (g4d_lmfun_bounds (y := y5) h5 h5').1
    have hu := (g4d_lmfun_bounds (y := y5) h5 h5').2
    have ht := (g4dDDihY3_of_rbox (g4dR_p516243 hbk)).1
    have hX := (g4dDDihY3_of_rbox (g4dR_p516243 hbk)).2
    exact g4d_weighted_neg hl hu ht (by linarith)
  have hd6 : 0.9979 * (4 * 0.0579) ≤ lmfun (y6/2) * g4dDDihY1 y6 y1 y5 y3 y4 y2 := by
    have hl := (g4d_lmfun_bounds (y := y6) h6 h6').1
    have hu := (g4d_lmfun_bounds (y := y6) h6 h6').2
    have ht := (g4dDDihY1_of_rbox (g4dR_p615342 hbk)).1
    exact g4d_weighted_pos hl hu ht (by norm_num)
  have hD : -3.0355 ≤ lmfun (y1/2) * g4dDDihY6 y1 y2 y3 y4 y5 y6 + lmfun (y2/2) * g4dDDihY5 y2 y3 y1 y5 y6 y4 + lmfun (y3/2) * g4dDDihY4 y3 y1 y2 y6 y4 y5 + lmfun (y4/2) * g4dDDihY5 y4 y3 y5 y1 y6 y2 + lmfun (y5/2) * g4dDDihY3 y5 y1 y6 y2 y4 y3 + lmfun (y6/2) * g4dDDihY1 y6 y1 y5 y3 y4 y2 + ((-1/(h0-1))/2) * dihY y6 y1 y5 y3 y4 y2 := by
    have hn := (g4d_dihY_bounds_of_rbox (g4dR_p615342 hbk)).2
    have hL : ((-1/(h0-1))/2) * 1.5708 ≤ ((-1/(h0-1))/2) * dihY y6 y1 y5 y3 y4 y2 := by
      have hneg : ((-1/(h0-1))/2 : ℝ) ≤ 0 := by norm_num [h0]
      have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
      have h1 : 0 ≤ ((-1/(h0-1))/2) * (dihY y6 y1 y5 y3 y4 y2 - Real.pi/2) :=
        mul_nonneg_of_nonpos_of_nonpos hneg (by linarith [hn])
      have h2 : 0 ≤ ((-1/(h0-1))/2) * (Real.pi/2 - 1.5708) :=
        mul_nonneg_of_nonpos_of_nonpos hneg (by linarith [hpi])
      nlinarith [h1, h2]
    have hcoeff : ((-1/(h0-1))/2) * 1.5708 = -(3927/1300) := by norm_num [h0]
    linarith [hd1, hd2, hd3, hd4, hd5, hd6, hL, hcoeff]
  have hc1 : (0:ℝ) ≤ 2 * mm1 / Real.pi := by
    have := g4d_mm1_bounds.1; positivity
  have hc1hi : 2 * mm1 / Real.pi ≤ 0.6456 := by
    have hp := g4d_pi_bounds.1; have hm := g4d_mm1_bounds.2
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]; nlinarith [hp, hm]
  have hc2 : (0:ℝ) ≤ 8 * mm2 / Real.pi := by
    have := g4d_mm2_bounds.1; positivity
  have hc2hi : 8 * mm2 / Real.pi ≤ 0.06512 := by
    have hp := g4d_pi_bounds.1; have hm := g4d_mm2_bounds.2
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]; nlinarith [hp, hm]
  have h1 := g4d_mul_le_upper hc1 hc1hi hS (by norm_num)
  have h2 := g4d_neg_mul_le hc2 hc2hi hD (by norm_num)
  unfold g4dDVol4f6
  nlinarith [h1, h2]

#print axioms g4dDVol4f4_le
#print axioms g4dDVol4f5_le
#print axioms g4dDVol4f6_le

end Kepler.Text
