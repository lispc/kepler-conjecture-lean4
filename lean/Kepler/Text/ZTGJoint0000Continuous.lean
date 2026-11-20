import Kepler.Text.ZTGJoint0000MainSecond

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

theorem ztg_atn2_eq_arctan_div {x y : ℝ} (hx : 0 < x) :
    atn2 x y = Real.arctan (y / x) := by
  unfold atn2
  by_cases h : |y| < x
  · rw [if_pos h]
  · rw [if_neg h]
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      linarith
    by_cases hy : 0 < y
    · rw [if_pos hy]
      have hpos : 0 < y / x := div_pos hy hx
      have hinv : x / y = (y / x)⁻¹ := by field_simp
      rw [hinv, Real.arctan_inv_of_pos hpos]
      ring
    · rw [if_neg hy]
      have hyn : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hy0
      rw [if_pos hyn]
      have hneg : y / x < 0 := div_neg_of_neg_of_pos hyn hx
      have hinv : x / y = (y / x)⁻¹ := by field_simp
      rw [hinv, Real.arctan_inv_of_neg hneg]
      ring

theorem ztg_continuousAt_atn2 {f g : ℝ → ℝ} {q0 : ℝ}
    (hf : ContinuousAt f q0) (hg : ContinuousAt g q0) (hpos : 0 < f q0) :
    ContinuousAt (fun q => atn2 (f q) (g q)) q0 := by
  have hcont : ContinuousAt (fun q => Real.arctan (g q / f q)) q0 :=
    Real.continuous_arctan.continuousAt.comp' (hg.div hf hpos.ne')
  refine hcont.congr ?_
  filter_upwards [hf.eventually (isOpen_Ioi.mem_nhds hpos)] with q hq
  exact (ztg_atn2_eq_arctan_div hq).symm

theorem ztg_lmfun_eq_max (h : ℝ) : lmfun h = max ((h0 - h) / (h0 - 1)) 0 := by
  rw [lmfun]
  by_cases hh : h ≤ h0
  · rw [if_pos hh]
    exact (max_eq_left (show (0:ℝ) ≤ (h0 - h) / (h0 - 1) by
      exact div_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (by norm_num [h0])))).symm
  · rw [if_neg hh]
    exact (max_eq_right (show (h0 - h) / (h0 - 1) ≤ (0:ℝ) by
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (not_le.mp hh).le)
        (sub_nonneg.mpr (by norm_num [h0])))).symm

theorem ztg_lmfunContinuous : Continuous lmfun := by
  have hfun : lmfun = fun h : ℝ => max ((h0 - h) / (h0 - 1)) 0 := funext ztg_lmfun_eq_max
  rw [hfun]
  exact ((continuous_const.sub continuous_id).div
    (continuous_const.sub continuous_const)
    (fun _ => sub_ne_zero.mpr (by norm_num [h0]))).max continuous_const

theorem ztg_continuousAt_dihY_y1 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    ContinuousAt (fun q => dihY q a2 a3 a4 a5 a6) a1 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * (q * q) * deltaX (q * q) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))) a1 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 (q * q) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))) a1 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3)
      (a4 * a4) (a5 * a5) (a6 * a6)) := by
    apply Real.sqrt_pos.mpr
    have hd' : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := by
      simpa only [deltaY] using hd
    positivity
  have hmain := ztg_continuousAt_atn2 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * (q * q) * deltaX (q * q) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))) (-(deltaX4 (q * q) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)))) a1 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihY, dihXf] using hfin

theorem ztg_continuousAt_dihY_y2 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    ContinuousAt (fun q => dihY a1 q a3 a4 a5 a6) a2 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (q * q) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))) a2 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 (a1 * a1) (q * q) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))) a2 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3)
      (a4 * a4) (a5 * a5) (a6 * a6)) := by
    apply Real.sqrt_pos.mpr
    have hd' : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := by
      simpa only [deltaY] using hd
    positivity
  have hmain := ztg_continuousAt_atn2 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (q * q) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))) (-(deltaX4 (a1 * a1) (q * q) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)))) a2 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihY, dihXf] using hfin

theorem ztg_continuousAt_dihY_y3 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    ContinuousAt (fun q => dihY a1 a2 q a4 a5 a6) a3 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (q * q) (a4 * a4) (a5 * a5) (a6 * a6))) a3 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 (a1 * a1) (a2 * a2) (q * q) (a4 * a4) (a5 * a5) (a6 * a6))) a3 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3)
      (a4 * a4) (a5 * a5) (a6 * a6)) := by
    apply Real.sqrt_pos.mpr
    have hd' : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := by
      simpa only [deltaY] using hd
    positivity
  have hmain := ztg_continuousAt_atn2 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (q * q) (a4 * a4) (a5 * a5) (a6 * a6))) (-(deltaX4 (a1 * a1) (a2 * a2) (q * q) (a4 * a4) (a5 * a5) (a6 * a6)))) a3 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihY, dihXf] using hfin

theorem ztg_continuousAt_dihY_y4 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    ContinuousAt (fun q => dihY a1 a2 a3 q a5 a6) a4 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3) (q * q) (a5 * a5) (a6 * a6))) a4 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 (a1 * a1) (a2 * a2) (a3 * a3) (q * q) (a5 * a5) (a6 * a6))) a4 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3)
      (a4 * a4) (a5 * a5) (a6 * a6)) := by
    apply Real.sqrt_pos.mpr
    have hd' : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := by
      simpa only [deltaY] using hd
    positivity
  have hmain := ztg_continuousAt_atn2 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3) (q * q) (a5 * a5) (a6 * a6))) (-(deltaX4 (a1 * a1) (a2 * a2) (a3 * a3) (q * q) (a5 * a5) (a6 * a6)))) a4 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihY, dihXf] using hfin

theorem ztg_continuousAt_dihY_y5 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    ContinuousAt (fun q => dihY a1 a2 a3 a4 q a6) a5 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (q * q) (a6 * a6))) a5 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (q * q) (a6 * a6))) a5 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3)
      (a4 * a4) (a5 * a5) (a6 * a6)) := by
    apply Real.sqrt_pos.mpr
    have hd' : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := by
      simpa only [deltaY] using hd
    positivity
  have hmain := ztg_continuousAt_atn2 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (q * q) (a6 * a6))) (-(deltaX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (q * q) (a6 * a6)))) a5 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihY, dihXf] using hfin

theorem ztg_continuousAt_dihY_y6 (a1 a2 a3 a4 a5 a6 : ℝ)
    (ha1 : 0 < a1) (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    ContinuousAt (fun q => dihY a1 a2 a3 a4 a5 q) a6 := by
  have hF : ContinuousAt (fun q => Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (q * q))) a6 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaX; fun_prop)
  have hG : ContinuousAt (fun q => -(deltaX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (q * q))) a6 := by
    unfold deltaX4
    fun_prop
  have hpos : 0 < Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3)
      (a4 * a4) (a5 * a5) (a6 * a6)) := by
    apply Real.sqrt_pos.mpr
    have hd' : 0 < deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6) := by
      simpa only [deltaY] using hd
    positivity
  have hmain := ztg_continuousAt_atn2 hF hG hpos
  have hfin : ContinuousAt (fun q => Real.pi / 2 +
      atn2 (Real.sqrt (4 * (a1 * a1) * deltaX (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (q * q))) (-(deltaX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (q * q)))) a6 :=
    (continuousAt_const (y := Real.pi / 2)).add hmain
  simpa only [dihY, dihXf] using hfin

theorem ztg_main_continuousAt_y1 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun t => ztgMain 0 0 0 0 t y2 y3 y4 y5 y6) y1 := by
  have hv0 : ContinuousAt (fun t => Real.sqrt (deltaY t y2 y3 y4 y5 y6)) y1 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaY deltaX; fun_prop)
  have hv : ContinuousAt (fun t => volY t y2 y3 y4 y5 y6) y1 := by
    simpa only [volY, volXf, deltaY] using hv0.div_const 12
  have d10 := ztg_continuousAt_dihY_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have d11 := ztg_continuousAt_dihY_y3 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d12 := ztg_continuousAt_dihY_y2 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hface1 : ContinuousAt (fun t => solY t y2 y3 y4 y5 y6) y1 :=
    (d10.add d11).add d12 |>.sub_const Real.pi
  have d20 := ztg_continuousAt_dihY_y1 y1 y5 y6 y4 y2 y3 hy1 (by rw [g4d_deltaY_p156423]; exact hd)
  have d21 := ztg_continuousAt_dihY_y3 y5 y6 y1 y2 y3 y4 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p156423]; exact hd)
  have d22 := ztg_continuousAt_dihY_y2 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p156423]; exact hd)
  have hface2 : ContinuousAt (fun t => solY t y5 y6 y4 y2 y3) y1 :=
    (d20.add d21).add d22 |>.sub_const Real.pi
  have d30 := ztg_continuousAt_dihY_y4 y4 y5 y3 y1 y2 y6 hy4 (by rw [g4d_deltaY_p453126]; exact hd)
  have d31 := ztg_continuousAt_dihY_y6 y5 y3 y4 y2 y6 y1 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p453126]; exact hd)
  have d32 := ztg_continuousAt_dihY_y5 y3 y4 y5 y6 y1 y2 hy3 (by rw [g4d_deltaY_p312645, g4d_deltaY_p453126]; exact hd)
  have hface3 : ContinuousAt (fun t => solY y4 y5 y3 t y2 y6) y1 :=
    (d30.add d31).add d32 |>.sub_const Real.pi
  have d40 := ztg_continuousAt_dihY_y4 y4 y2 y6 y1 y5 y3 hy4 (by rw [g4d_deltaY_p426153]; exact hd)
  have d41 := ztg_continuousAt_dihY_y6 y2 y6 y4 y5 y3 y1 hy2 (by rw [g4d_deltaY_p231564, g4d_deltaY_p426153]; exact hd)
  have d42 := ztg_continuousAt_dihY_y5 y6 y4 y2 y3 y1 y5 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p426153]; exact hd)
  have hface4 : ContinuousAt (fun t => solY y4 y2 y6 t y5 y3) y1 :=
    (d40.add d41).add d42 |>.sub_const Real.pi
  have hS := ((hface1.add hface2).add hface3).add hface4
  have de1 := ztg_continuousAt_dihY_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have de2 := ztg_continuousAt_dihY_y3 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have de3 := ztg_continuousAt_dihY_y2 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have de4 := ztg_continuousAt_dihY_y4 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have de5 := ztg_continuousAt_dihY_y2 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have de6 := ztg_continuousAt_dihY_y2 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hlm : ContinuousAt (fun t => lmfun (t / 2)) y1 :=
    ztg_lmfunContinuous.continuousAt.comp' (by fun_prop)
  have we1 := hlm.mul de1
  have we2 := de2.const_mul (lmfun (y2 / 2))
  have we3 := de3.const_mul (lmfun (y3 / 2))
  have we4 := de4.const_mul (lmfun (y4 / 2))
  have we5 := de5.const_mul (lmfun (y5 / 2))
  have we6 := de6.const_mul (lmfun (y6 / 2))
  have hD := (((((we1.add we2).add we3).add we4).add we5).add we6)
  have hvol4 : ContinuousAt (fun t => vol4f t y2 y3 y4 y5 y6 lmfun) y1 :=
    (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  have hg : ContinuousAt (fun t => gamma4fgcy t y2 y3 y4 y5 y6 lmfun) y1 := hv.sub hvol4
  have hmain := ztg_continuousAt_dihY_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have hfun : (fun t => ztgMain 0 0 0 0 t y2 y3 y4 y5 y6) = fun t => gamma4fgcy t y2 y3 y4 y5 y6 lmfun - bSpine5 * dihY t y2 y3 y4 y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun]
  exact (hg.sub (hmain.const_mul bSpine5)).sub_const aSpine5

theorem ztg_main_continuousAt_y2 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun t => ztgMain 0 0 0 0 y1 t y3 y4 y5 y6) y2 := by
  have hv0 : ContinuousAt (fun t => Real.sqrt (deltaY y1 t y3 y4 y5 y6)) y2 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaY deltaX; fun_prop)
  have hv : ContinuousAt (fun t => volY y1 t y3 y4 y5 y6) y2 := by
    simpa only [volY, volXf, deltaY] using hv0.div_const 12
  have d10 := ztg_continuousAt_dihY_y2 y1 y2 y3 y4 y5 y6 hy1 hd
  have d11 := ztg_continuousAt_dihY_y1 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d12 := ztg_continuousAt_dihY_y3 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hface1 : ContinuousAt (fun t => solY y1 t y3 y4 y5 y6) y2 :=
    (d10.add d11).add d12 |>.sub_const Real.pi
  have d20 := ztg_continuousAt_dihY_y5 y1 y5 y6 y4 y2 y3 hy1 (by rw [g4d_deltaY_p156423]; exact hd)
  have d21 := ztg_continuousAt_dihY_y4 y5 y6 y1 y2 y3 y4 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p156423]; exact hd)
  have d22 := ztg_continuousAt_dihY_y6 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p156423]; exact hd)
  have hface2 : ContinuousAt (fun t => solY y1 y5 y6 y4 t y3) y2 :=
    (d20.add d21).add d22 |>.sub_const Real.pi
  have d30 := ztg_continuousAt_dihY_y5 y4 y5 y3 y1 y2 y6 hy4 (by rw [g4d_deltaY_p453126]; exact hd)
  have d31 := ztg_continuousAt_dihY_y4 y5 y3 y4 y2 y6 y1 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p453126]; exact hd)
  have d32 := ztg_continuousAt_dihY_y6 y3 y4 y5 y6 y1 y2 hy3 (by rw [g4d_deltaY_p312645, g4d_deltaY_p453126]; exact hd)
  have hface3 : ContinuousAt (fun t => solY y4 y5 y3 y1 t y6) y2 :=
    (d30.add d31).add d32 |>.sub_const Real.pi
  have d40 := ztg_continuousAt_dihY_y2 y4 y2 y6 y1 y5 y3 hy4 (by rw [g4d_deltaY_p426153]; exact hd)
  have d41 := ztg_continuousAt_dihY_y1 y2 y6 y4 y5 y3 y1 hy2 (by rw [g4d_deltaY_p231564, g4d_deltaY_p426153]; exact hd)
  have d42 := ztg_continuousAt_dihY_y3 y6 y4 y2 y3 y1 y5 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p426153]; exact hd)
  have hface4 : ContinuousAt (fun t => solY y4 t y6 y1 y5 y3) y2 :=
    (d40.add d41).add d42 |>.sub_const Real.pi
  have hS := ((hface1.add hface2).add hface3).add hface4
  have de1 := ztg_continuousAt_dihY_y2 y1 y2 y3 y4 y5 y6 hy1 hd
  have de2 := ztg_continuousAt_dihY_y1 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have de3 := ztg_continuousAt_dihY_y3 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have de4 := ztg_continuousAt_dihY_y6 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have de5 := ztg_continuousAt_dihY_y4 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have de6 := ztg_continuousAt_dihY_y6 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hlm : ContinuousAt (fun t => lmfun (t / 2)) y2 :=
    ztg_lmfunContinuous.continuousAt.comp' (by fun_prop)
  have we1 := de1.const_mul (lmfun (y1 / 2))
  have we2 := hlm.mul de2
  have we3 := de3.const_mul (lmfun (y3 / 2))
  have we4 := de4.const_mul (lmfun (y4 / 2))
  have we5 := de5.const_mul (lmfun (y5 / 2))
  have we6 := de6.const_mul (lmfun (y6 / 2))
  have hD := (((((we1.add we2).add we3).add we4).add we5).add we6)
  have hvol4 : ContinuousAt (fun t => vol4f y1 t y3 y4 y5 y6 lmfun) y2 :=
    (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  have hg : ContinuousAt (fun t => gamma4fgcy y1 t y3 y4 y5 y6 lmfun) y2 := hv.sub hvol4
  have hmain := ztg_continuousAt_dihY_y2 y1 y2 y3 y4 y5 y6 hy1 hd
  have hfun : (fun t => ztgMain 0 0 0 0 y1 t y3 y4 y5 y6) = fun t => gamma4fgcy y1 t y3 y4 y5 y6 lmfun - bSpine5 * dihY y1 t y3 y4 y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun]
  exact (hg.sub (hmain.const_mul bSpine5)).sub_const aSpine5

theorem ztg_main_continuousAt_y3 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun t => ztgMain 0 0 0 0 y1 y2 t y4 y5 y6) y3 := by
  have hv0 : ContinuousAt (fun t => Real.sqrt (deltaY y1 y2 t y4 y5 y6)) y3 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaY deltaX; fun_prop)
  have hv : ContinuousAt (fun t => volY y1 y2 t y4 y5 y6) y3 := by
    simpa only [volY, volXf, deltaY] using hv0.div_const 12
  have d10 := ztg_continuousAt_dihY_y3 y1 y2 y3 y4 y5 y6 hy1 hd
  have d11 := ztg_continuousAt_dihY_y2 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d12 := ztg_continuousAt_dihY_y1 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hface1 : ContinuousAt (fun t => solY y1 y2 t y4 y5 y6) y3 :=
    (d10.add d11).add d12 |>.sub_const Real.pi
  have d20 := ztg_continuousAt_dihY_y6 y1 y5 y6 y4 y2 y3 hy1 (by rw [g4d_deltaY_p156423]; exact hd)
  have d21 := ztg_continuousAt_dihY_y5 y5 y6 y1 y2 y3 y4 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p156423]; exact hd)
  have d22 := ztg_continuousAt_dihY_y4 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p156423]; exact hd)
  have hface2 : ContinuousAt (fun t => solY y1 y5 y6 y4 y2 t) y3 :=
    (d20.add d21).add d22 |>.sub_const Real.pi
  have d30 := ztg_continuousAt_dihY_y3 y4 y5 y3 y1 y2 y6 hy4 (by rw [g4d_deltaY_p453126]; exact hd)
  have d31 := ztg_continuousAt_dihY_y2 y5 y3 y4 y2 y6 y1 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p453126]; exact hd)
  have d32 := ztg_continuousAt_dihY_y1 y3 y4 y5 y6 y1 y2 hy3 (by rw [g4d_deltaY_p312645, g4d_deltaY_p453126]; exact hd)
  have hface3 : ContinuousAt (fun t => solY y4 y5 t y1 y2 y6) y3 :=
    (d30.add d31).add d32 |>.sub_const Real.pi
  have d40 := ztg_continuousAt_dihY_y6 y4 y2 y6 y1 y5 y3 hy4 (by rw [g4d_deltaY_p426153]; exact hd)
  have d41 := ztg_continuousAt_dihY_y5 y2 y6 y4 y5 y3 y1 hy2 (by rw [g4d_deltaY_p231564, g4d_deltaY_p426153]; exact hd)
  have d42 := ztg_continuousAt_dihY_y4 y6 y4 y2 y3 y1 y5 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p426153]; exact hd)
  have hface4 : ContinuousAt (fun t => solY y4 y2 y6 y1 y5 t) y3 :=
    (d40.add d41).add d42 |>.sub_const Real.pi
  have hS := ((hface1.add hface2).add hface3).add hface4
  have de1 := ztg_continuousAt_dihY_y3 y1 y2 y3 y4 y5 y6 hy1 hd
  have de2 := ztg_continuousAt_dihY_y2 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have de3 := ztg_continuousAt_dihY_y1 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have de4 := ztg_continuousAt_dihY_y2 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have de5 := ztg_continuousAt_dihY_y6 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have de6 := ztg_continuousAt_dihY_y4 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hlm : ContinuousAt (fun t => lmfun (t / 2)) y3 :=
    ztg_lmfunContinuous.continuousAt.comp' (by fun_prop)
  have we1 := de1.const_mul (lmfun (y1 / 2))
  have we2 := de2.const_mul (lmfun (y2 / 2))
  have we3 := hlm.mul de3
  have we4 := de4.const_mul (lmfun (y4 / 2))
  have we5 := de5.const_mul (lmfun (y5 / 2))
  have we6 := de6.const_mul (lmfun (y6 / 2))
  have hD := (((((we1.add we2).add we3).add we4).add we5).add we6)
  have hvol4 : ContinuousAt (fun t => vol4f y1 y2 t y4 y5 y6 lmfun) y3 :=
    (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  have hg : ContinuousAt (fun t => gamma4fgcy y1 y2 t y4 y5 y6 lmfun) y3 := hv.sub hvol4
  have hmain := ztg_continuousAt_dihY_y3 y1 y2 y3 y4 y5 y6 hy1 hd
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 t y4 y5 y6) = fun t => gamma4fgcy y1 y2 t y4 y5 y6 lmfun - bSpine5 * dihY y1 y2 t y4 y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun]
  exact (hg.sub (hmain.const_mul bSpine5)).sub_const aSpine5

theorem ztg_main_continuousAt_y4 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun t => ztgMain 0 0 0 0 y1 y2 y3 t y5 y6) y4 := by
  have hv0 : ContinuousAt (fun t => Real.sqrt (deltaY y1 y2 y3 t y5 y6)) y4 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaY deltaX; fun_prop)
  have hv : ContinuousAt (fun t => volY y1 y2 y3 t y5 y6) y4 := by
    simpa only [volY, volXf, deltaY] using hv0.div_const 12
  have d10 := ztg_continuousAt_dihY_y4 y1 y2 y3 y4 y5 y6 hy1 hd
  have d11 := ztg_continuousAt_dihY_y6 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d12 := ztg_continuousAt_dihY_y5 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hface1 : ContinuousAt (fun t => solY y1 y2 y3 t y5 y6) y4 :=
    (d10.add d11).add d12 |>.sub_const Real.pi
  have d20 := ztg_continuousAt_dihY_y4 y1 y5 y6 y4 y2 y3 hy1 (by rw [g4d_deltaY_p156423]; exact hd)
  have d21 := ztg_continuousAt_dihY_y6 y5 y6 y1 y2 y3 y4 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p156423]; exact hd)
  have d22 := ztg_continuousAt_dihY_y5 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p156423]; exact hd)
  have hface2 : ContinuousAt (fun t => solY y1 y5 y6 t y2 y3) y4 :=
    (d20.add d21).add d22 |>.sub_const Real.pi
  have d30 := ztg_continuousAt_dihY_y1 y4 y5 y3 y1 y2 y6 hy4 (by rw [g4d_deltaY_p453126]; exact hd)
  have d31 := ztg_continuousAt_dihY_y3 y5 y3 y4 y2 y6 y1 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p453126]; exact hd)
  have d32 := ztg_continuousAt_dihY_y2 y3 y4 y5 y6 y1 y2 hy3 (by rw [g4d_deltaY_p312645, g4d_deltaY_p453126]; exact hd)
  have hface3 : ContinuousAt (fun t => solY t y5 y3 y1 y2 y6) y4 :=
    (d30.add d31).add d32 |>.sub_const Real.pi
  have d40 := ztg_continuousAt_dihY_y1 y4 y2 y6 y1 y5 y3 hy4 (by rw [g4d_deltaY_p426153]; exact hd)
  have d41 := ztg_continuousAt_dihY_y3 y2 y6 y4 y5 y3 y1 hy2 (by rw [g4d_deltaY_p231564, g4d_deltaY_p426153]; exact hd)
  have d42 := ztg_continuousAt_dihY_y2 y6 y4 y2 y3 y1 y5 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p426153]; exact hd)
  have hface4 : ContinuousAt (fun t => solY t y2 y6 y1 y5 y3) y4 :=
    (d40.add d41).add d42 |>.sub_const Real.pi
  have hS := ((hface1.add hface2).add hface3).add hface4
  have de1 := ztg_continuousAt_dihY_y4 y1 y2 y3 y4 y5 y6 hy1 hd
  have de2 := ztg_continuousAt_dihY_y6 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have de3 := ztg_continuousAt_dihY_y5 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have de4 := ztg_continuousAt_dihY_y1 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have de5 := ztg_continuousAt_dihY_y5 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have de6 := ztg_continuousAt_dihY_y5 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hlm : ContinuousAt (fun t => lmfun (t / 2)) y4 :=
    ztg_lmfunContinuous.continuousAt.comp' (by fun_prop)
  have we1 := de1.const_mul (lmfun (y1 / 2))
  have we2 := de2.const_mul (lmfun (y2 / 2))
  have we3 := de3.const_mul (lmfun (y3 / 2))
  have we4 := hlm.mul de4
  have we5 := de5.const_mul (lmfun (y5 / 2))
  have we6 := de6.const_mul (lmfun (y6 / 2))
  have hD := (((((we1.add we2).add we3).add we4).add we5).add we6)
  have hvol4 : ContinuousAt (fun t => vol4f y1 y2 y3 t y5 y6 lmfun) y4 :=
    (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  have hg : ContinuousAt (fun t => gamma4fgcy y1 y2 y3 t y5 y6 lmfun) y4 := hv.sub hvol4
  have hmain := ztg_continuousAt_dihY_y4 y1 y2 y3 y4 y5 y6 hy1 hd
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 y3 t y5 y6) = fun t => gamma4fgcy y1 y2 y3 t y5 y6 lmfun - bSpine5 * dihY y1 y2 y3 t y5 y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun]
  exact (hg.sub (hmain.const_mul bSpine5)).sub_const aSpine5

theorem ztg_main_continuousAt_y5 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 t y6) y5 := by
  have hv0 : ContinuousAt (fun t => Real.sqrt (deltaY y1 y2 y3 y4 t y6)) y5 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaY deltaX; fun_prop)
  have hv : ContinuousAt (fun t => volY y1 y2 y3 y4 t y6) y5 := by
    simpa only [volY, volXf, deltaY] using hv0.div_const 12
  have d10 := ztg_continuousAt_dihY_y5 y1 y2 y3 y4 y5 y6 hy1 hd
  have d11 := ztg_continuousAt_dihY_y4 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d12 := ztg_continuousAt_dihY_y6 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hface1 : ContinuousAt (fun t => solY y1 y2 y3 y4 t y6) y5 :=
    (d10.add d11).add d12 |>.sub_const Real.pi
  have d20 := ztg_continuousAt_dihY_y2 y1 y5 y6 y4 y2 y3 hy1 (by rw [g4d_deltaY_p156423]; exact hd)
  have d21 := ztg_continuousAt_dihY_y1 y5 y6 y1 y2 y3 y4 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p156423]; exact hd)
  have d22 := ztg_continuousAt_dihY_y3 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p156423]; exact hd)
  have hface2 : ContinuousAt (fun t => solY y1 t y6 y4 y2 y3) y5 :=
    (d20.add d21).add d22 |>.sub_const Real.pi
  have d30 := ztg_continuousAt_dihY_y2 y4 y5 y3 y1 y2 y6 hy4 (by rw [g4d_deltaY_p453126]; exact hd)
  have d31 := ztg_continuousAt_dihY_y1 y5 y3 y4 y2 y6 y1 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p453126]; exact hd)
  have d32 := ztg_continuousAt_dihY_y3 y3 y4 y5 y6 y1 y2 hy3 (by rw [g4d_deltaY_p312645, g4d_deltaY_p453126]; exact hd)
  have hface3 : ContinuousAt (fun t => solY y4 t y3 y1 y2 y6) y5 :=
    (d30.add d31).add d32 |>.sub_const Real.pi
  have d40 := ztg_continuousAt_dihY_y5 y4 y2 y6 y1 y5 y3 hy4 (by rw [g4d_deltaY_p426153]; exact hd)
  have d41 := ztg_continuousAt_dihY_y4 y2 y6 y4 y5 y3 y1 hy2 (by rw [g4d_deltaY_p231564, g4d_deltaY_p426153]; exact hd)
  have d42 := ztg_continuousAt_dihY_y6 y6 y4 y2 y3 y1 y5 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p426153]; exact hd)
  have hface4 : ContinuousAt (fun t => solY y4 y2 y6 y1 t y3) y5 :=
    (d40.add d41).add d42 |>.sub_const Real.pi
  have hS := ((hface1.add hface2).add hface3).add hface4
  have de1 := ztg_continuousAt_dihY_y5 y1 y2 y3 y4 y5 y6 hy1 hd
  have de2 := ztg_continuousAt_dihY_y4 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have de3 := ztg_continuousAt_dihY_y6 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have de4 := ztg_continuousAt_dihY_y3 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have de5 := ztg_continuousAt_dihY_y1 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have de6 := ztg_continuousAt_dihY_y3 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hlm : ContinuousAt (fun t => lmfun (t / 2)) y5 :=
    ztg_lmfunContinuous.continuousAt.comp' (by fun_prop)
  have we1 := de1.const_mul (lmfun (y1 / 2))
  have we2 := de2.const_mul (lmfun (y2 / 2))
  have we3 := de3.const_mul (lmfun (y3 / 2))
  have we4 := de4.const_mul (lmfun (y4 / 2))
  have we5 := hlm.mul de5
  have we6 := de6.const_mul (lmfun (y6 / 2))
  have hD := (((((we1.add we2).add we3).add we4).add we5).add we6)
  have hvol4 : ContinuousAt (fun t => vol4f y1 y2 y3 y4 t y6 lmfun) y5 :=
    (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  have hg : ContinuousAt (fun t => gamma4fgcy y1 y2 y3 y4 t y6 lmfun) y5 := hv.sub hvol4
  have hmain := ztg_continuousAt_dihY_y5 y1 y2 y3 y4 y5 y6 hy1 hd
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 t y6) = fun t => gamma4fgcy y1 y2 y3 y4 t y6 lmfun - bSpine5 * dihY y1 y2 y3 y4 t y6 - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun]
  exact (hg.sub (hmain.const_mul bSpine5)).sub_const aSpine5

theorem ztg_main_continuousAt_y6 (y1 y2 y3 y4 y5 y6 : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3)
    (hy4 : 0 < y4) (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    ContinuousAt (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 y5 t) y6 := by
  have hv0 : ContinuousAt (fun t => Real.sqrt (deltaY y1 y2 y3 y4 y5 t)) y6 :=
    Real.continuous_sqrt.continuousAt.comp' (by unfold deltaY deltaX; fun_prop)
  have hv : ContinuousAt (fun t => volY y1 y2 y3 y4 y5 t) y6 := by
    simpa only [volY, volXf, deltaY] using hv0.div_const 12
  have d10 := ztg_continuousAt_dihY_y6 y1 y2 y3 y4 y5 y6 hy1 hd
  have d11 := ztg_continuousAt_dihY_y5 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d12 := ztg_continuousAt_dihY_y4 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hface1 : ContinuousAt (fun t => solY y1 y2 y3 y4 y5 t) y6 :=
    (d10.add d11).add d12 |>.sub_const Real.pi
  have d20 := ztg_continuousAt_dihY_y3 y1 y5 y6 y4 y2 y3 hy1 (by rw [g4d_deltaY_p156423]; exact hd)
  have d21 := ztg_continuousAt_dihY_y2 y5 y6 y1 y2 y3 y4 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p156423]; exact hd)
  have d22 := ztg_continuousAt_dihY_y1 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p156423]; exact hd)
  have hface2 : ContinuousAt (fun t => solY y1 y5 t y4 y2 y3) y6 :=
    (d20.add d21).add d22 |>.sub_const Real.pi
  have d30 := ztg_continuousAt_dihY_y6 y4 y5 y3 y1 y2 y6 hy4 (by rw [g4d_deltaY_p453126]; exact hd)
  have d31 := ztg_continuousAt_dihY_y5 y5 y3 y4 y2 y6 y1 hy5 (by rw [g4d_deltaY_p231564, g4d_deltaY_p453126]; exact hd)
  have d32 := ztg_continuousAt_dihY_y4 y3 y4 y5 y6 y1 y2 hy3 (by rw [g4d_deltaY_p312645, g4d_deltaY_p453126]; exact hd)
  have hface3 : ContinuousAt (fun t => solY y4 y5 y3 y1 y2 t) y6 :=
    (d30.add d31).add d32 |>.sub_const Real.pi
  have d40 := ztg_continuousAt_dihY_y3 y4 y2 y6 y1 y5 y3 hy4 (by rw [g4d_deltaY_p426153]; exact hd)
  have d41 := ztg_continuousAt_dihY_y2 y2 y6 y4 y5 y3 y1 hy2 (by rw [g4d_deltaY_p231564, g4d_deltaY_p426153]; exact hd)
  have d42 := ztg_continuousAt_dihY_y1 y6 y4 y2 y3 y1 y5 hy6 (by rw [g4d_deltaY_p312645, g4d_deltaY_p426153]; exact hd)
  have hface4 : ContinuousAt (fun t => solY y4 y2 t y1 y5 y3) y6 :=
    (d40.add d41).add d42 |>.sub_const Real.pi
  have hS := ((hface1.add hface2).add hface3).add hface4
  have de1 := ztg_continuousAt_dihY_y6 y1 y2 y3 y4 y5 y6 hy1 hd
  have de2 := ztg_continuousAt_dihY_y5 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have de3 := ztg_continuousAt_dihY_y4 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have de4 := ztg_continuousAt_dihY_y5 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have de5 := ztg_continuousAt_dihY_y3 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have de6 := ztg_continuousAt_dihY_y1 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hlm : ContinuousAt (fun t => lmfun (t / 2)) y6 :=
    ztg_lmfunContinuous.continuousAt.comp' (by fun_prop)
  have we1 := de1.const_mul (lmfun (y1 / 2))
  have we2 := de2.const_mul (lmfun (y2 / 2))
  have we3 := de3.const_mul (lmfun (y3 / 2))
  have we4 := de4.const_mul (lmfun (y4 / 2))
  have we5 := de5.const_mul (lmfun (y5 / 2))
  have we6 := hlm.mul de6
  have hD := (((((we1.add we2).add we3).add we4).add we5).add we6)
  have hvol4 : ContinuousAt (fun t => vol4f y1 y2 y3 y4 y5 t lmfun) y6 :=
    (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  have hg : ContinuousAt (fun t => gamma4fgcy y1 y2 y3 y4 y5 t lmfun) y6 := hv.sub hvol4
  have hmain := ztg_continuousAt_dihY_y6 y1 y2 y3 y4 y5 y6 hy1 hd
  have hfun : (fun t => ztgMain 0 0 0 0 y1 y2 y3 y4 y5 t) = fun t => gamma4fgcy y1 y2 y3 y4 y5 t lmfun - bSpine5 * dihY y1 y2 y3 y4 y5 t - aSpine5 := by
    funext t
    simp [ztgMain, ztgW, ztgM, bankGenMid]
    ring
  rw [hfun]
  exact (hg.sub (hmain.const_mul bSpine5)).sub_const aSpine5

#print axioms ztg_continuousAt_atn2
#print axioms ztg_lmfunContinuous
#print axioms ztg_continuousAt_dihY_y1
#print axioms ztg_main_continuousAt_y1
#print axioms ztg_continuousAt_dihY_y2
#print axioms ztg_main_continuousAt_y2
#print axioms ztg_continuousAt_dihY_y3
#print axioms ztg_main_continuousAt_y3
#print axioms ztg_continuousAt_dihY_y4
#print axioms ztg_main_continuousAt_y4
#print axioms ztg_continuousAt_dihY_y5
#print axioms ztg_main_continuousAt_y5
#print axioms ztg_continuousAt_dihY_y6
#print axioms ztg_main_continuousAt_y6

end Kepler.Text
