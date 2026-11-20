import Kepler.NliBanks25

set_option maxHeartbeats 16000000

namespace Kepler.NliBanks26
open Kepler.Text
open Kepler.NliBanks19
open Kepler.NliBanks20
open Kepler.NliBanks22

theorem cell52_core {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ 2.67421356)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.52:ℝ) * 2.52) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.174:ℝ) * 2.174) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.174) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.347:ℝ) * 2.347) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.174^2) - ((2.52^2) - (2.4635^2) - (2.174^2))^2) - (2.52^2) * (2.4635^2) * (2.174^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.174:ℝ) * 2.174) = 2.174 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.174)]
  have hea4min : (29.134988:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.779466:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.822105:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.4635 / 2 := by norm_num
    have hC2 : (7.646728:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.52 / 2 := by norm_num
    have hT3 : (4.886689:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) / 2 := by
      have hval : (4.886689:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hP5Lle
    have s2 : ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (22.568918:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.574031:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.174:ℝ) * 2.174)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.59682:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.174 / 2 := by norm_num
    have hC2 : (5.82159:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.4635 / 2 := by norm_num
    have hT3 : (2.576477:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.576477:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.174:ℝ) * 2.174) hP5Lle
    have s2 : ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (23.947712:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.74774:ℝ) ≤ Real.sqrt (2 * ((2.174:ℝ) * 2.174) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.174:ℝ) * 2.174) + ((2.52:ℝ) * 2.52) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.955107:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.52 / 2 := by norm_num
    have hC2 : (6.902884:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.174 / 2 := by norm_num
    have hT3 : (3.341981:ℝ) ≤ Real.sqrt 2 * (((2.174:ℝ) * 2.174) + ((2.52:ℝ) * 2.52) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.341981:ℝ) ≤ (1.41421356:ℝ) * (((2.174:ℝ) * 2.174) + ((2.52:ℝ) * 2.52) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.67421356:ℝ) * 2.67421356) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.67421356:ℝ) * 2.67421356) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.347:ℝ) * 2.347) * (((2.67421356:ℝ) * 2.67421356) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.67421356:ℝ) * 2.67421356) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.3326923:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.3326923:ℝ) ≤ lfun ((2.347:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.67421356:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.174:ℝ)) (q6h := (2.347:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.174^2) - ((2.52^2) - (2.4635^2) - (2.174^2))^2) - (2.52^2) * (2.4635^2) * (2.174^2))
    (ea4L := (29.134988:ℝ)) (ea5L := (22.568918:ℝ)) (ea6L := (23.947712:ℝ))
    (dx4L := ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.67421356:ℝ) * 2.67421356) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)))
    (dx6H := ((2.347:ℝ) * 2.347) * (((2.67421356:ℝ) * 2.67421356) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.3326923:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell53_core {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ 2.67421356)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.52:ℝ) * 2.52) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.174:ℝ) * 2.174) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.174) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.347:ℝ) * 2.347) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.174^2) - ((2.52^2) - (2.52^2) - (2.174^2))^2) - (2.52^2) * (2.52^2) * (2.174^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.174:ℝ) * 2.174) = 2.174 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.174)]
  have hea4min : (30.069617:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) := by
    unfold ea4X
    rw [hsq5]
    have hr : (8.980821:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.001504:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.52 / 2 := by norm_num
    have hC2 : (8.001504:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.52 / 2 := by norm_num
    have hT3 : (5.085788:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) / 2 := by
      have hval : (5.085788:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hP5Lle
    have s2 : ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (23.381307:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.74774:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.174:ℝ) * 2.174)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.902884:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.174 / 2 := by norm_num
    have hC2 : (5.955107:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.52 / 2 := by norm_num
    have hT3 : (2.775576:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.775576:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.174:ℝ) * 2.174) hP5Lle
    have s2 : ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (22.781269:ℝ) ≤ ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.74774:ℝ) ≤ Real.sqrt (2 * ((2.174:ℝ) * 2.174) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.174:ℝ) * 2.174) + ((2.52:ℝ) * 2.52) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.955107:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.52 / 2 := by norm_num
    have hC2 : (6.902884:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.174 / 2 := by norm_num
    have hT3 : (2.175538:ℝ) ≤ Real.sqrt 2 * (((2.174:ℝ) * 2.174) + ((2.52:ℝ) * 2.52) - ((8:ℝ))) / 2 := by
      have hval : (2.175538:ℝ) ≤ (1.41421356:ℝ) * (((2.174:ℝ) * 2.174) + ((2.52:ℝ) * 2.52) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.67421356:ℝ) * 2.67421356) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.67421356:ℝ) * 2.67421356) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.347:ℝ) * 2.347) * (((2.67421356:ℝ) * 2.67421356) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.67421356:ℝ) * 2.67421356) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.3326923:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.3326923:ℝ) ≤ lfun ((2.347:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.67421356:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.174:ℝ)) (q6h := (2.347:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.174^2) - ((2.52^2) - (2.52^2) - (2.174^2))^2) - (2.52^2) * (2.52^2) * (2.174^2))
    (ea4L := (30.069617:ℝ)) (ea5L := (23.381307:ℝ)) (ea6L := (22.781269:ℝ))
    (dx4L := ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.67421356:ℝ) * 2.67421356) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)))
    (dx6H := ((2.347:ℝ) * 2.347) * (((2.67421356:ℝ) * 2.67421356) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.3326923:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h.trans wt2a_sqrt8.2)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell54_core {y4 y5 y6 : ℝ}
    (hc4l : (2.4635:ℝ) ≤ y4) (hc4h : y4 ≤ 2.49175)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.49175:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.4635:ℝ) * 2.4635) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.174:ℝ) * 2.174) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.174) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.347:ℝ) * 2.347) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.174^2) - ((2.4635^2) - (2.4635^2) - (2.174^2))^2) - (2.4635^2) * (2.4635^2) * (2.174^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.174:ℝ) * 2.174) = 2.174 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.174)]
  have hea4min : (28.220783:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635) := by
    unfold ea4X
    rw [hsq5]
    have hr : (8.582624:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.475284:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.4635 / 2 := by norm_num
    have hC2 : (7.475284:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.4635 / 2 := by norm_num
    have hT3 : (4.687591:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) / 2 := by
      have hval : (4.687591:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hP5Lle
    have s2 : ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (23.235437:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.574031:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.174:ℝ) * 2.174)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.59682:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.174 / 2 := by norm_num
    have hC2 : (5.82159:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.4635 / 2 := by norm_num
    have hT3 : (3.242996:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (3.242996:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.174:ℝ) * 2.174) hP5Lle
    have s2 : ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (23.135324:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.574031:ℝ) ≤ Real.sqrt (2 * ((2.174:ℝ) * 2.174) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.174:ℝ) * 2.174) + ((2.4635:ℝ) * 2.4635) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.82159:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.4635 / 2 := by norm_num
    have hC2 : (6.59682:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.174 / 2 := by norm_num
    have hT3 : (3.142883:ℝ) ≤ Real.sqrt 2 * (((2.174:ℝ) * 2.174) + ((2.4635:ℝ) * 2.4635) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.142883:ℝ) ≤ (1.41421356:ℝ) * (((2.174:ℝ) * 2.174) + ((2.4635:ℝ) * 2.4635) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.174:ℝ) * 2.174) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.347:ℝ) * 2.347) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hm4bound : (0.05432692:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    have h1 : lfun ((2.49175:ℝ) * 0.5) ≤ h0cut y4 * lfun (y4 * 0.5) :=
      h0cut_lfun_ge hc4h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.05432692:ℝ) ≤ lfun ((2.49175:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.3326923:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.3326923:ℝ) ≤ lfun ((2.347:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.49175:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.174:ℝ)) (q6h := (2.347:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.174^2) - ((2.4635^2) - (2.4635^2) - (2.174^2))^2) - (2.4635^2) * (2.4635^2) * (2.174^2))
    (ea4L := (28.220783:ℝ)) (ea5L := (23.235437:ℝ)) (ea6L := (23.135324:ℝ))
    (dx4L := ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.174:ℝ) * 2.174) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)))
    (dx6H := ((2.347:ℝ) * 2.347) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (m4 := (0.05432692:ℝ)) (m5 := (0:ℝ)) (l6v := (0.3326923:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4bound) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell55_core {y4 y5 y6 : ℝ}
    (hc4l : (2.4635:ℝ) ≤ y4) (hc4h : y4 ≤ 2.49175)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.49175:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.4635:ℝ) * 2.4635) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.174:ℝ) * 2.174) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.174) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.347:ℝ) * 2.347) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.174^2) - ((2.4635^2) - (2.52^2) - (2.174^2))^2) - (2.4635^2) * (2.52^2) * (2.174^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.174:ℝ) * 2.174) = 2.174 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.174)]
  have hea4min : (29.134988:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.779466:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.646728:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.52 / 2 := by norm_num
    have hC2 : (7.822105:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.4635 / 2 := by norm_num
    have hT3 : (4.886689:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) / 2 := by
      have hval : (4.886689:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hP5Lle
    have s2 : ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (24.047826:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.74774:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.174:ℝ) * 2.174)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.902884:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.174 / 2 := by norm_num
    have hC2 : (5.955107:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.52 / 2 := by norm_num
    have hT3 : (3.442095:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (3.442095:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.174:ℝ) * 2.174) hP5Lle
    have s2 : ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.96888:ℝ) ≤ ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.574031:ℝ) ≤ Real.sqrt (2 * ((2.174:ℝ) * 2.174) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.174:ℝ) * 2.174) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.82159:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.4635 / 2 := by norm_num
    have hC2 : (6.59682:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.174 / 2 := by norm_num
    have hT3 : (1.976439:ℝ) ≤ Real.sqrt 2 * (((2.174:ℝ) * 2.174) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by
      have hval : (1.976439:ℝ) ≤ (1.41421356:ℝ) * (((2.174:ℝ) * 2.174) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.49175:ℝ) * 2.49175) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.49175:ℝ) * 2.49175) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.174:ℝ) * 2.174) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.347:ℝ) * 2.347) * (((2.49175:ℝ) * 2.49175) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.49175:ℝ) * 2.49175) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hm4bound : (0.05432692:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    have h1 : lfun ((2.49175:ℝ) * 0.5) ≤ h0cut y4 * lfun (y4 * 0.5) :=
      h0cut_lfun_ge hc4h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.05432692:ℝ) ≤ lfun ((2.49175:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.3326923:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.3326923:ℝ) ≤ lfun ((2.347:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.49175:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.174:ℝ)) (q6h := (2.347:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.174^2) - ((2.4635^2) - (2.52^2) - (2.174^2))^2) - (2.4635^2) * (2.52^2) * (2.174^2))
    (ea4L := (29.134988:ℝ)) (ea5L := (24.047826:ℝ)) (ea6L := (21.96888:ℝ))
    (dx4L := ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.49175:ℝ) * 2.49175) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.174:ℝ) * 2.174) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)))
    (dx6H := ((2.347:ℝ) * 2.347) * (((2.49175:ℝ) * 2.49175) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)))
    (m4 := (0.05432692:ℝ)) (m5 := (0:ℝ)) (l6v := (0.3326923:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h.trans wt2a_sqrt8.2)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4bound) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell56_core {y4 y5 y6 : ℝ}
    (hc4l : (2.49175:ℝ) ≤ y4) (hc4h : y4 ≤ 2.52)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.49175:ℝ) * 2.49175) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.49175) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.174:ℝ) * 2.174) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.174) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.347:ℝ) * 2.347) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.174^2) - ((2.49175^2) - (2.4635^2) - (2.174^2))^2) - (2.49175^2) * (2.4635^2) * (2.174^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.174:ℝ) * 2.174) = 2.174 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.174)]
  have hea4min : (28.676338:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.681045:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.49175:ℝ) * 2.49175) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.647711:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.4635 / 2 := by norm_num
    have hC2 : (7.561006:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.49175 / 2 := by norm_num
    have hT3 : (4.786576:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.49175:ℝ) * 2.49175) - ((2.347:ℝ) * 2.347)) / 2 := by
      have hval : (4.786576:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.49175:ℝ) * 2.49175) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hP5Lle
    have s2 : ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (23.135324:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.574031:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.174:ℝ) * 2.174)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.59682:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.174 / 2 := by norm_num
    have hC2 : (5.82159:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.4635 / 2 := by norm_num
    have hT3 : (3.142883:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.142883:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.174:ℝ) * 2.174) hP5Lle
    have s2 : ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (23.540088:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.660886:ℝ) ≤ Real.sqrt (2 * ((2.174:ℝ) * 2.174) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.174:ℝ) * 2.174) + ((2.49175:ℝ) * 2.49175) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.888349:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.49175 / 2 := by norm_num
    have hC2 : (6.748985:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.174 / 2 := by norm_num
    have hT3 : (3.241868:ℝ) ≤ Real.sqrt 2 * (((2.174:ℝ) * 2.174) + ((2.49175:ℝ) * 2.49175) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.241868:ℝ) ≤ (1.41421356:ℝ) * (((2.174:ℝ) * 2.174) + ((2.49175:ℝ) * 2.49175) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.49175:ℝ) * 2.49175) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.3326923:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.3326923:ℝ) ≤ lfun ((2.347:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.52:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.174:ℝ)) (q6h := (2.347:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.174^2) - ((2.49175^2) - (2.4635^2) - (2.174^2))^2) - (2.49175^2) * (2.4635^2) * (2.174^2))
    (ea4L := (28.676338:ℝ)) (ea5L := (23.135324:ℝ)) (ea6L := (23.540088:ℝ))
    (dx4L := ((2.49175:ℝ) * 2.49175) * (((2.4635:ℝ) * 2.4635) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.4635:ℝ) * 2.4635) - ((2.347:ℝ) * 2.347)))
    (dx6H := ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.3326923:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell57_core {y4 y5 y6 : ℝ}
    (hc4l : (2.49175:ℝ) ≤ y4) (hc4h : y4 ≤ 2.52)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.49175:ℝ) * 2.49175) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.49175) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.174:ℝ) * 2.174) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.174) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.347:ℝ) * 2.347) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.174^2) - ((2.49175^2) - (2.52^2) - (2.174^2))^2) - (2.49175^2) * (2.52^2) * (2.174^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.174:ℝ) * 2.174) = 2.174 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.174)]
  have hea4min : (29.600731:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.880143:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.82311:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.52 / 2 := by norm_num
    have hC2 : (7.911804:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.49175 / 2 := by norm_num
    have hT3 : (4.985674:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.347:ℝ) * 2.347)) / 2 := by
      have hval : (4.985674:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.347:ℝ) * 2.347)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hP5Lle
    have s2 : ea4X (y5*y5) ((2.347:ℝ) * 2.347) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (23.947712:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.74774:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.174:ℝ) * 2.174)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.902884:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.174 / 2 := by norm_num
    have hC2 : (5.955107:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.52 / 2 := by norm_num
    have hT3 : (3.341981:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.341981:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.174:ℝ) * 2.174) hP5Lle
    have s2 : ea5X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (22.373644:ℝ) ≤ ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.660886:ℝ) ≤ Real.sqrt (2 * ((2.174:ℝ) * 2.174) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.174:ℝ) * 2.174) + ((2.49175:ℝ) * 2.49175) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.888349:ℝ) ≤ ((2.174:ℝ) * 2.174) * 2.49175 / 2 := by norm_num
    have hC2 : (6.748985:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.174 / 2 := by norm_num
    have hT3 : (2.075424:ℝ) ≤ Real.sqrt 2 * (((2.174:ℝ) * 2.174) + ((2.49175:ℝ) * 2.49175) - ((8:ℝ))) / 2 := by
      have hval : (2.075424:ℝ) ≤ (1.41421356:ℝ) * (((2.174:ℝ) * 2.174) + ((2.49175:ℝ) * 2.49175) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.3326923:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.3326923:ℝ) ≤ lfun ((2.347:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.52:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.174:ℝ)) (q6h := (2.347:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.174^2) - ((2.49175^2) - (2.52^2) - (2.174^2))^2) - (2.49175^2) * (2.52^2) * (2.174^2))
    (ea4L := (29.600731:ℝ)) (ea5L := (23.947712:ℝ)) (ea6L := (22.373644:ℝ))
    (dx4L := ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.347:ℝ) * 2.347)))
    (dx6H := ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((8:ℝ)) - ((2.174:ℝ) * 2.174)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.3326923:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h.trans wt2a_sqrt8.2)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell58_vac {y4 y5 y6 : ℝ}
    (hc4l : (2.67421356:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  refine cell_vacuous (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
    (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  norm_num

theorem cell59_vac {y4 y5 y6 : ℝ}
    (hc4l : (2.67421356:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.174:ℝ) ≤ y6) (hc6h : y6 ≤ (2.347:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  refine cell_vacuous (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
    (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  norm_num

theorem cell60_core {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.347:ℝ) ≤ y6) (hc6h : y6 ≤ (2.46352:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.52:ℝ) * 2.52) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.347:ℝ) * 2.347) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.347) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.46352:ℝ) * 2.46352) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy4.le hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.347^2) - ((2.52^2) - (2.4635^2) - (2.347^2))^2) - (2.52^2) * (2.4635^2) * (2.347^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.347:ℝ) * 2.347) = 2.347 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.347)]
  have hea4min : (28.73864:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.46352:ℝ) * 2.46352) ((2.52:ℝ) * 2.52) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.779466:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.46352:ℝ) * 2.46352)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.822105:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.4635 / 2 := by norm_num
    have hC2 : (7.646728:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.52 / 2 := by norm_num
    have hT3 : (4.490341:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.46352:ℝ) * 2.46352)) / 2 := by
      have hval : (4.490341:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.46352:ℝ) * 2.46352)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.46352:ℝ) * 2.46352) ((2.52:ℝ) * 2.52)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.46352:ℝ) * 2.46352) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) ((2.46352:ℝ) * 2.46352) ((2.52:ℝ) * 2.52) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hP5Lle
    have s2 : ea4X (y5*y5) ((2.46352:ℝ) * 2.46352) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (24.612995:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((8:ℝ)) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (8.176748:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.347:ℝ) * 2.347)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.121774:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.347 / 2 := by norm_num
    have hC2 : (6.784982:ℝ) ≤ ((2.347:ℝ) * 2.347) * 2.4635 / 2 := by norm_num
    have hT3 : (2.529491:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))) / 2 := by
      have hval : (2.529491:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((8:ℝ))
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((8:ℝ))
        ≤ ea5X (y5*y5) ((2.347:ℝ) * 2.347) ((8:ℝ)) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.347:ℝ) * 2.347) hP5Lle
    have s2 : ea5X (y5*y5) ((2.347:ℝ) * 2.347) ((8:ℝ))
        ≤ ea5X (y5*y5) (y6*y6) ((8:ℝ)) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((8:ℝ))
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (25.48566:ℝ) ≤ ea6X ((8:ℝ)) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (8.364281:ℝ) ≤ Real.sqrt (2 * ((2.347:ℝ) * 2.347) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.347:ℝ) * 2.347) + ((2.52:ℝ) * 2.52) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.940595:ℝ) ≤ ((2.347:ℝ) * 2.347) * 2.52 / 2 := by norm_num
    have hC2 : (7.452194:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.347 / 2 := by norm_num
    have hT3 : (2.72859:ℝ) ≤ Real.sqrt 2 * (((2.347:ℝ) * 2.347) + ((2.52:ℝ) * 2.52) - ((8:ℝ))) / 2 := by
      have hval : (2.72859:ℝ) ≤ (1.41421356:ℝ) * (((2.347:ℝ) * 2.347) + ((2.52:ℝ) * 2.52) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ)))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((8:ℝ)) + ((2.46352:ℝ) * 2.46352) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((8:ℝ)) + ((2.46352:ℝ) * 2.46352) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.46352:ℝ) * 2.46352) * (((8:ℝ)) + ((8:ℝ)) - ((2.347:ℝ) * 2.347)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.46352:ℝ) * 2.46352) * (((8:ℝ)) + ((8:ℝ)) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.10861538:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.10861538:ℝ) ≤ lfun ((2.46352:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.82842713:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.347:ℝ)) (q6h := (2.46352:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.347^2) - ((2.52^2) - (2.4635^2) - (2.347^2))^2) - (2.52^2) * (2.4635^2) * (2.347^2))
    (ea4L := (28.73864:ℝ)) (ea5L := (24.612995:ℝ)) (ea6L := (25.48566:ℝ))
    (dx4L := ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.347:ℝ) * 2.347) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((8:ℝ)) + ((2.46352:ℝ) * 2.46352) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.347:ℝ) * 2.347) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)))
    (dx6H := ((2.46352:ℝ) * 2.46352) * (((8:ℝ)) + ((8:ℝ)) - ((2.347:ℝ) * 2.347)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.10861538:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h.trans wt2a_sqrt8.2) (hc5 := hc5l) (hc5' := hc5h.trans wt2a_sqrt8.2)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell61_core {y4 y5 y6 : ℝ}
    (hc4l : (2.4635:ℝ) ≤ y4) (hc4h : y4 ≤ 2.52)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.347:ℝ) ≤ y6) (hc6h : y6 ≤ (2.46352:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.4635:ℝ) * 2.4635) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.347:ℝ) * 2.347) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.347) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.46352:ℝ) * 2.46352) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.347^2) - ((2.4635^2) - (2.4635^2) - (2.347^2))^2) - (2.4635^2) * (2.4635^2) * (2.347^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.347:ℝ) * 2.347) = 2.347 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.347)]
  have hea4min : (27.824434:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.46352:ℝ) * 2.46352) ((2.4635:ℝ) * 2.4635) := by
    unfold ea4X
    rw [hsq5]
    have hr : (8.582624:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.475284:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.4635 / 2 := by norm_num
    have hC2 : (7.475284:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.4635 / 2 := by norm_num
    have hT3 : (4.291242:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)) / 2 := by
      have hval : (4.291242:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.46352:ℝ) * 2.46352) ((2.4635:ℝ) * 2.4635)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.46352:ℝ) * 2.46352) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) ((2.46352:ℝ) * 2.46352) ((2.4635:ℝ) * 2.4635) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hP5Lle
    have s2 : ea4X (y5*y5) ((2.46352:ℝ) * 2.46352) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (25.779438:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (8.176748:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.347:ℝ) * 2.347)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.121774:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.347 / 2 := by norm_num
    have hC2 : (6.784982:ℝ) ≤ ((2.347:ℝ) * 2.347) * 2.4635 / 2 := by norm_num
    have hT3 : (3.695934:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.695934:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.347:ℝ) * 2.347) hP5Lle
    have s2 : ea5X (y5*y5) ((2.347:ℝ) * 2.347) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (24.612995:ℝ) ≤ ea6X ((8:ℝ)) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (8.176748:ℝ) ≤ Real.sqrt (2 * ((2.347:ℝ) * 2.347) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.347:ℝ) * 2.347) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.784982:ℝ) ≤ ((2.347:ℝ) * 2.347) * 2.4635 / 2 := by norm_num
    have hC2 : (7.121774:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.347 / 2 := by norm_num
    have hT3 : (2.529491:ℝ) ≤ Real.sqrt 2 * (((2.347:ℝ) * 2.347) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by
      have hval : (2.529491:ℝ) ≤ (1.41421356:ℝ) * (((2.347:ℝ) * 2.347) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.347:ℝ) * 2.347) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.52:ℝ) * 2.52) + ((2.46352:ℝ) * 2.46352) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.52:ℝ) * 2.52) + ((2.46352:ℝ) * 2.46352) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.347:ℝ) * 2.347) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.347:ℝ) * 2.347) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.46352:ℝ) * 2.46352) * (((2.52:ℝ) * 2.52) + ((8:ℝ)) - ((2.347:ℝ) * 2.347)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.46352:ℝ) * 2.46352) * (((2.52:ℝ) * 2.52) + ((8:ℝ)) - ((2.347:ℝ) * 2.347)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.10861538:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.10861538:ℝ) ≤ lfun ((2.46352:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.52:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.347:ℝ)) (q6h := (2.46352:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.347^2) - ((2.4635^2) - (2.4635^2) - (2.347^2))^2) - (2.4635^2) * (2.4635^2) * (2.347^2))
    (ea4L := (27.824434:ℝ)) (ea5L := (25.779438:ℝ)) (ea6L := (24.612995:ℝ))
    (dx4L := ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((2.52:ℝ) * 2.52)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.347:ℝ) * 2.347) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.52:ℝ) * 2.52) + ((2.46352:ℝ) * 2.46352) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.347:ℝ) * 2.347) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.46352:ℝ) * 2.46352)))
    (dx6H := ((2.46352:ℝ) * 2.46352) * (((2.52:ℝ) * 2.52) + ((8:ℝ)) - ((2.347:ℝ) * 2.347)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.10861538:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h) (hc5 := hc5l) (hc5' := hc5h.trans wt2a_sqrt8.2)
    (hc6 := hc6l) (hc6' := hc6h) (hp5l := by norm_num)
    (hd0 := hd0) (hdh := hdh) (hdhp := by norm_num)
    (hea4 := hea4min.trans hea4pt) (hea4p := by norm_num)
    (hea5 := hea5min.trans hea5pt) (hea5p := by norm_num)
    (hea6 := hea6min.trans hea6pt) (hea6p := by norm_num)
    (hdx4 := hdx4) (hdx4p := hdx4p)
    (hdx5 := hdx5) (hdx5p := hdx5p)
    (hdx5' := hdx5') (hdx5p' := hdx5p')
    (hdx6 := hdx6) (hdx6p := hdx6p)
    (hdx6' := hdx6') (hdx6p' := hdx6p')
    (hm4 := hm4zero) (hm4p := by norm_num)
    (hm5 := hm5zero) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

end Kepler.NliBanks26
