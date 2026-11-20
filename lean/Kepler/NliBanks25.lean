import Kepler.NliBanks24

set_option maxHeartbeats 16000000

namespace Kepler.NliBanks25
open Kepler.Text
open Kepler.NliBanks19
open Kepler.NliBanks20
open Kepler.NliBanks22

theorem cell32_core {y4 y5 y6 : ℝ}
    (hc4l : (2.49175:ℝ) ≤ y4) (hc4h : y4 ≤ 2.52)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
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
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.058^2) - ((2.49175^2) - (2.4635^2) - (2.058^2))^2) - (2.49175^2) * (2.4635^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (29.229389:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.681045:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.647711:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.4635 / 2 := by norm_num
    have hC2 : (7.561006:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.49175 / 2 := by norm_num
    have hT3 : (5.339627:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.339627:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.42739:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hC2 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hT3 : (2.795756:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (2.795756:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.812465:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.252117:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.276734:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.49175 / 2 := by norm_num
    have hC2 : (6.388873:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.058 / 2 := by norm_num
    have hT3 : (2.894741:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (2.894741:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.49175:ℝ) * 2.49175) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.52:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.058^2) - ((2.49175^2) - (2.4635^2) - (2.058^2))^2) - (2.49175^2) * (2.4635^2) * (2.058^2))
    (ea4L := (29.229389:ℝ)) (ea5L := (21.42739:ℝ)) (ea6L := (21.812465:ℝ))
    (dx4L := ((2.49175:ℝ) * 2.49175) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell33_core {y4 y5 y6 : ℝ}
    (hc4l : (2.4635:ℝ) ≤ y4) (hc4h : y4 ≤ 2.49175)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
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
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.058^2) - ((2.4635^2) - (2.4635^2) - (2.058^2))^2) - (2.4635^2) * (2.4635^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (28.773835:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) := by
    unfold ea4X
    rw [hsq5]
    have hr : (8.582624:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.475284:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.4635 / 2 := by norm_num
    have hC2 : (7.475284:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.4635 / 2 := by norm_num
    have hT3 : (5.240643:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.240643:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.527503:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hC2 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hT3 : (2.895869:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (2.895869:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.42739:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hC2 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hT3 : (2.795756:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (2.795756:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) := by norm_num
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
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.49175:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.058^2) - ((2.4635^2) - (2.4635^2) - (2.058^2))^2) - (2.4635^2) * (2.4635^2) * (2.058^2))
    (ea4L := (28.773835:ℝ)) (ea5L := (21.527503:ℝ)) (ea6L := (21.42739:ℝ))
    (dx4L := ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.05432692:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell34_core {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ 2.59710678)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.49175)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.59710678:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.49175:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.52:ℝ) * 2.52) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.59710678:ℝ) * 2.59710678) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.058^2) - ((2.52^2) - (2.4635^2) - (2.058^2))^2) - (2.52^2) * (2.4635^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (29.68804:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.779466:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.822105:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.4635 / 2 := by norm_num
    have hC2 : (7.646728:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.52 / 2 := by norm_num
    have hT3 : (5.439741:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.439741:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.148391:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hC2 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hT3 : (2.516757:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by
      have hval : (2.516757:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (22.300424:ℝ) ≤ ea6X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hC2 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hT3 : (3.094968:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (3.094968:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.49175:ℝ) * 2.49175) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.49175:ℝ) * 2.49175) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.49175:ℝ) * 2.49175) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5bound : (0.05432692:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    have h1 : lfun ((2.49175:ℝ) * 0.5) ≤ h0cut y5 * lfun (y5 * 0.5) :=
      h0cut_lfun_ge hc5h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.05432692:ℝ) ≤ lfun ((2.49175:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.59710678:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.49175:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.058^2) - ((2.52^2) - (2.4635^2) - (2.058^2))^2) - (2.52^2) * (2.4635^2) * (2.058^2))
    (ea4L := (29.68804:ℝ)) (ea5L := (21.148391:ℝ)) (ea6L := (22.300424:ℝ))
    (dx4L := ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)))
    (dx5H := ((2.49175:ℝ) * 2.49175) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.49175:ℝ) * 2.49175) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0.05432692:ℝ)) (l6v := (0.66538461:ℝ))
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
    (hm5 := hm5bound) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell35_core {y4 y5 y6 : ℝ}
    (hc4l : (2.67421356:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.67421356:ℝ) * 2.67421356) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy4.le hc4h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.058^2) - ((2.67421356^2) - (2.4635^2) - (2.058^2))^2) - (2.67421356^2) * (2.4635^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.67421356:ℝ) * 2.67421356) = 2.67421356 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (32.246314:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.316733:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.67421356:ℝ) * 2.67421356)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.808759:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.4635 / 2 := by norm_num
    have hC2 : (8.114676:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.67421356 / 2 := by norm_num
    have hT3 : (6.006146:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (6.006146:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.67421356:ℝ) * 2.67421356) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea4X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (20.260946:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((8:ℝ)) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hC2 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hT3 : (1.629312:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) / 2 := by
      have hval : (1.629312:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((8:ℝ))
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((8:ℝ))
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((8:ℝ)) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((8:ℝ))
        ≤ ea5X (y5*y5) (y6*y6) ((8:ℝ)) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((8:ℝ))
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (24.366369:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.783168:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.67421356:ℝ) * 2.67421356)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.67421356:ℝ) * 2.67421356) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.663133:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.67421356 / 2 := by norm_num
    have hC2 : (7.358809:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.058 / 2 := by norm_num
    have hT3 : (3.561259:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.67421356:ℝ) * 2.67421356) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.561259:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.67421356:ℝ) * 2.67421356) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea6X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.67421356:ℝ) * 2.67421356) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.67421356:ℝ) * 2.67421356) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ)))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((8:ℝ)) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((8:ℝ)) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.67421356:ℝ) * 2.67421356) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.67421356:ℝ) * 2.67421356) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((8:ℝ)) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((8:ℝ)) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.82842713:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.058^2) - ((2.67421356^2) - (2.4635^2) - (2.058^2))^2) - (2.67421356^2) * (2.4635^2) * (2.058^2))
    (ea4L := (32.246314:ℝ)) (ea5L := (20.260946:ℝ)) (ea6L := (24.366369:ℝ))
    (dx4L := ((2.67421356:ℝ) * 2.67421356) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((8:ℝ)) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.67421356:ℝ) * 2.67421356) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((8:ℝ)) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
    (hb4 := by linarith [hc4l]) (hb4' := hc4box)
    (hb5 := by linarith [hc5l]) (hb5' := hc5box)
    (hq6l := by norm_num) (hq6h := by norm_num)
    (hc4' := hc4h.trans wt2a_sqrt8.2) (hc5 := hc5l) (hc5' := hc5h)
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

theorem cell36_core {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ 2.59710678)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ 2.67421356)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.59710678:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.52:ℝ) * 2.52) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.59710678:ℝ) * 2.59710678) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.058^2) - ((2.52^2) - (2.52^2) - (2.058^2))^2) - (2.52^2) * (2.52^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (30.622668:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea4X
    rw [hsq5]
    have hr : (8.980821:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.001504:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.52 / 2 := by norm_num
    have hC2 : (8.001504:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.52 / 2 := by norm_num
    have hT3 : (5.638839:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.638839:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.921311:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hC2 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hT3 : (2.715855:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by
      have hval : (2.715855:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.633905:ℝ) ≤ ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hC2 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hT3 : (2.428449:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.428449:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.67421356:ℝ) * 2.67421356) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.59710678:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.67421356:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.058^2) - ((2.52^2) - (2.52^2) - (2.058^2))^2) - (2.52^2) * (2.52^2) * (2.058^2))
    (ea4L := (30.622668:ℝ)) (ea5L := (21.921311:ℝ)) (ea6L := (21.633905:ℝ))
    (dx4L := ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5H := ((2.67421356:ℝ) * 2.67421356) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell37_core {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ 2.59710678)
    (hc5l : (2.49175:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.59710678:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.52:ℝ) * 2.52) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc4l
  have hP5Lle : ((2.49175:ℝ) * 2.49175) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.49175) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.59710678:ℝ) * 2.59710678) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.49175^2) * (2.058^2) - ((2.52^2) - (2.49175^2) - (2.058^2))^2) - (2.52^2) * (2.49175^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq5 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (30.153783:ℝ) ≤ ea4X ((2.49175:ℝ) * 2.49175) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.880143:ℝ) ≤ Real.sqrt (2 * ((2.49175:ℝ) * 2.49175) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.911804:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.49175 / 2 := by norm_num
    have hC2 : (7.82311:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.52 / 2 := by norm_num
    have hT3 : (5.538726:ℝ) ≤ Real.sqrt 2 * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.538726:ℝ) ≤ (1.41421356:ℝ) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.49175:ℝ) * 2.49175) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.49175:ℝ) * 2.49175) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.533466:ℝ) ≤ ea5X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.252117:ℝ) ≤ Real.sqrt (2 * ((2.49175:ℝ) * 2.49175) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.388873:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.058 / 2 := by norm_num
    have hC2 : (5.276734:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.49175 / 2 := by norm_num
    have hT3 : (2.615742:ℝ) ≤ Real.sqrt 2 * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by
      have hval : (2.615742:ℝ) ≤ (1.41421356:ℝ) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (22.20031:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.52:ℝ) * 2.52)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hC2 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hT3 : (2.994854:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (2.994854:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.52:ℝ) * 2.52) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.52:ℝ) * 2.52) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)) := by norm_num
  have hdx5 : ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.59710678:ℝ)) (p5l := (2.49175:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.49175^2) * (2.058^2) - ((2.52^2) - (2.49175^2) - (2.058^2))^2) - (2.52^2) * (2.49175^2) * (2.058^2))
    (ea4L := (30.153783:ℝ)) (ea5L := (21.533466:ℝ)) (ea6L := (22.20031:ℝ))
    (dx4L := ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.59710678:ℝ) * 2.59710678)))
    (dx5L := ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.59710678:ℝ) * 2.59710678) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.59710678:ℝ) * 2.59710678) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell38_core {y4 y5 y6 : ℝ}
    (hc4l : (2.4635:ℝ) ≤ y4) (hc4h : y4 ≤ 2.477625)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ 2.67421356)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.477625:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.4635:ℝ) * 2.4635) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.477625:ℝ) * 2.477625) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.058^2) - ((2.4635^2) - (2.52^2) - (2.058^2))^2) - (2.4635^2) * (2.52^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (29.68804:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.779466:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.646728:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.52 / 2 := by norm_num
    have hC2 : (7.822105:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.4635 / 2 := by norm_num
    have hT3 : (5.439741:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.439741:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (22.350057:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hC2 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hT3 : (3.144601:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) / 2 := by
      have hval : (3.144601:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea5X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (20.860984:ℝ) ≤ ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hC2 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hT3 : (2.22935:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.22935:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.67421356:ℝ) * 2.67421356) * (((2.477625:ℝ) * 2.477625) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.477625:ℝ) * 2.477625) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.477625:ℝ) * 2.477625) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.477625:ℝ) * 2.477625) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4bound : (0.08149038:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    have h1 : lfun ((2.477625:ℝ) * 0.5) ≤ h0cut y4 * lfun (y4 * 0.5) :=
      h0cut_lfun_ge hc4h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.08149038:ℝ) ≤ lfun ((2.477625:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.477625:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.67421356:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.058^2) - ((2.4635^2) - (2.52^2) - (2.058^2))^2) - (2.4635^2) * (2.52^2) * (2.058^2))
    (ea4L := (29.68804:ℝ)) (ea5L := (22.350057:ℝ)) (ea6L := (20.860984:ℝ))
    (dx4L := ((2.4635:ℝ) * 2.4635) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5H := ((2.67421356:ℝ) * 2.67421356) * (((2.477625:ℝ) * 2.477625) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.477625:ℝ) * 2.477625) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.08149038:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell39_core {y4 y5 y6 : ℝ}
    (hc4l : (2.477625:ℝ) ≤ y4) (hc4h : y4 ≤ 2.49175)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ 2.67421356)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.49175:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.477625:ℝ) * 2.477625) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.477625) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.058^2) - ((2.477625^2) - (2.52^2) - (2.058^2))^2) - (2.477625^2) * (2.52^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.477625:ℝ) * 2.477625) = 2.477625 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.477625)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (29.920519:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.829805:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.477625:ℝ) * 2.477625)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.477625:ℝ) * 2.477625) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.734668:ℝ) ≤ ((2.477625:ℝ) * 2.477625) * 2.52 / 2 := by norm_num
    have hC2 : (7.866954:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.477625 / 2 := by norm_num
    have hT3 : (5.489092:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.477625:ℝ) * 2.477625) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.489092:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.477625:ℝ) * 2.477625) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.477625:ℝ) * 2.477625) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625)
        ≤ ea4X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (22.300424:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hC2 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hT3 : (3.094968:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (3.094968:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.053175:ℝ) ≤ ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.211007:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.477625:ℝ) * 2.477625)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.477625:ℝ) * 2.477625) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.246821:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.477625 / 2 := by norm_num
    have hC2 : (6.316645:ℝ) ≤ ((2.477625:ℝ) * 2.477625) * 2.058 / 2 := by norm_num
    have hT3 : (2.278702:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.477625:ℝ) * 2.477625) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.278702:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.477625:ℝ) * 2.477625) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea6X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.477625:ℝ) * 2.477625) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.477625:ℝ) * 2.477625) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.477625:ℝ) * 2.477625) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.477625:ℝ) * 2.477625) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.477625:ℝ) * 2.477625) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.67421356:ℝ) * 2.67421356) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.477625:ℝ) * 2.477625) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.477625:ℝ) * 2.477625) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) := by norm_num
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
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.49175:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.67421356:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.058^2) - ((2.477625^2) - (2.52^2) - (2.058^2))^2) - (2.477625^2) * (2.52^2) * (2.058^2))
    (ea4L := (29.920519:ℝ)) (ea5L := (22.300424:ℝ)) (ea6L := (21.053175:ℝ))
    (dx4L := ((2.477625:ℝ) * 2.477625) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.477625:ℝ) * 2.477625) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5H := ((2.67421356:ℝ) * 2.67421356) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.477625:ℝ) * 2.477625) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.05432692:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell40_core {y4 y5 y6 : ℝ}
    (hc4l : (2.49175:ℝ) ≤ y4) (hc4h : y4 ≤ 2.505875)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ 2.67421356)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.505875:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.49175:ℝ) * 2.49175) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.49175) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.505875:ℝ) * 2.505875) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.058^2) - ((2.49175^2) - (2.52^2) - (2.058^2))^2) - (2.49175^2) * (2.52^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (30.153783:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.880143:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.82311:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.52 / 2 := by norm_num
    have hC2 : (7.911804:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.49175 / 2 := by norm_num
    have hT3 : (5.538726:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.538726:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (22.250508:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hC2 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hT3 : (3.045052:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) / 2 := by
      have hval : (3.045052:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
        ≤ ea5X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.246059:ℝ) ≤ ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.252117:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.276734:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.49175 / 2 := by norm_num
    have hC2 : (6.388873:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.058 / 2 := by norm_num
    have hT3 : (2.328335:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.328335:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.67421356:ℝ) * 2.67421356) * (((2.505875:ℝ) * 2.505875) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.505875:ℝ) * 2.505875) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.505875:ℝ) * 2.505875) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.505875:ℝ) * 2.505875) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4bound : (0.02716346:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    have h1 : lfun ((2.505875:ℝ) * 0.5) ≤ h0cut y4 * lfun (y4 * 0.5) :=
      h0cut_lfun_ge hc4h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.02716346:ℝ) ≤ lfun ((2.505875:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.505875:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.67421356:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.058^2) - ((2.49175^2) - (2.52^2) - (2.058^2))^2) - (2.49175^2) * (2.52^2) * (2.058^2))
    (ea4L := (30.153783:ℝ)) (ea5L := (22.250508:ℝ)) (ea6L := (21.246059:ℝ))
    (dx4L := ((2.49175:ℝ) * 2.49175) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5H := ((2.67421356:ℝ) * 2.67421356) * (((2.505875:ℝ) * 2.505875) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.505875:ℝ) * 2.505875) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.02716346:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell41_core {y4 y5 y6 : ℝ}
    (hc4l : (2.505875:ℝ) ≤ y4) (hc4h : y4 ≤ 2.52)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ 2.67421356)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.505875:ℝ) * 2.505875) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.505875) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.058^2) - ((2.505875^2) - (2.52^2) - (2.058^2))^2) - (2.505875^2) * (2.52^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.505875:ℝ) * 2.505875) = 2.505875 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.505875)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (30.387833:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.505875:ℝ) * 2.505875) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (8.930482:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.505875:ℝ) * 2.505875)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.505875:ℝ) * 2.505875) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.912055:ℝ) ≤ ((2.505875:ℝ) * 2.505875) * 2.52 / 2 := by norm_num
    have hC2 : (7.956654:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.505875 / 2 := by norm_num
    have hT3 : (5.588642:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.505875:ℝ) * 2.505875) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.588642:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.505875:ℝ) * 2.505875) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.505875:ℝ) * 2.505875)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.505875:ℝ) * 2.505875)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.505875:ℝ) * 2.505875) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.505875:ℝ) * 2.505875) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.505875:ℝ) * 2.505875)
        ≤ ea4X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (22.20031:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hC2 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hT3 : (2.994854:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (2.994854:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.52:ℝ) * 2.52)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (21.439636:ℝ) ≤ ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.293227:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.505875:ℝ) * 2.505875)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.505875:ℝ) * 2.505875) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.306646:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.505875 / 2 := by norm_num
    have hC2 : (6.461512:ℝ) ≤ ((2.505875:ℝ) * 2.505875) * 2.058 / 2 := by norm_num
    have hT3 : (2.378251:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.505875:ℝ) * 2.505875) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.378251:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.505875:ℝ) * 2.505875) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
        ≤ ea6X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.505875:ℝ) * 2.505875) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.505875:ℝ) * 2.505875) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.505875:ℝ) * 2.505875) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.505875:ℝ) * 2.505875) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.505875:ℝ) * 2.505875) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.67421356:ℝ) * 2.67421356) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.505875:ℝ) * 2.505875) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.505875:ℝ) * 2.505875) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.52:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.67421356:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.058^2) - ((2.505875^2) - (2.52^2) - (2.058^2))^2) - (2.505875^2) * (2.52^2) * (2.058^2))
    (ea4L := (30.387833:ℝ)) (ea5L := (22.20031:ℝ)) (ea6L := (21.439636:ℝ))
    (dx4L := ((2.505875:ℝ) * 2.505875) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.505875:ℝ) * 2.505875) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5H := ((2.67421356:ℝ) * 2.67421356) * (((2.52:ℝ) * 2.52) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.505875:ℝ) * 2.505875) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.52:ℝ) * 2.52) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell42_core {y4 y5 y6 : ℝ}
    (hc4l : (2.59710678:ℝ) ≤ y4) (hc4h : y4 ≤ 2.67421356)
    (hc5l : (2.4635:ℝ) ≤ y5) (hc5h : y5 ≤ 2.49175)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.49175:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.59710678:ℝ) * 2.59710678) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.59710678) hc4l
  have hP5Lle : ((2.4635:ℝ) * 2.4635) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.4635^2) * (2.058^2) - ((2.59710678^2) - (2.4635^2) - (2.058^2))^2) - (2.59710678^2) * (2.4635^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.59710678:ℝ) * 2.59710678) = 2.59710678 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.59710678)]
  have hsq5 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (30.955649:ℝ) ≤ ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.048099:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.59710678:ℝ) * 2.59710678)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.308108:ℝ) ≤ ((2.59710678:ℝ) * 2.59710678) * 2.4635 / 2 := by norm_num
    have hC2 : (7.880702:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.59710678 / 2 := by norm_num
    have hT3 : (5.71874:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.71874:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.4635:ℝ) * 2.4635) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.59710678:ℝ) * 2.59710678) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (20.860984:ℝ) ≤ ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.4635:ℝ) * 2.4635) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hC2 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hT3 : (2.22935:ℝ) ≤ Real.sqrt 2 * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.22935:ℝ) ≤ (1.41421356:ℝ) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.4635:ℝ) * 2.4635) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (23.373132:ℝ) ≤ ea6X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.558753:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.59710678:ℝ) * 2.59710678)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.499846:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.59710678 / 2 := by norm_num
    have hC2 : (6.940567:ℝ) ≤ ((2.59710678:ℝ) * 2.59710678) * 2.058 / 2 := by norm_num
    have hT3 : (3.373966:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (3.373966:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.59710678:ℝ) * 2.59710678) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.59710678:ℝ) * 2.59710678) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.59710678:ℝ) * 2.59710678) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5 : ((2.4635:ℝ) * 2.4635) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.49175:ℝ) * 2.49175) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.49175:ℝ) * 2.49175) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.49175:ℝ) * 2.49175) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5bound : (0.05432692:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    have h1 : lfun ((2.49175:ℝ) * 0.5) ≤ h0cut y5 * lfun (y5 * 0.5) :=
      h0cut_lfun_ge hc5h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.05432692:ℝ) ≤ lfun ((2.49175:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.67421356:ℝ)) (p5l := (2.4635:ℝ)) (p5h := (2.49175:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.4635^2) * (2.058^2) - ((2.59710678^2) - (2.4635^2) - (2.058^2))^2) - (2.59710678^2) * (2.4635^2) * (2.058^2))
    (ea4L := (30.955649:ℝ)) (ea5L := (20.860984:ℝ)) (ea6L := (23.373132:ℝ))
    (dx4L := ((2.59710678:ℝ) * 2.59710678) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5L := ((2.4635:ℝ) * 2.4635) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)))
    (dx5H := ((2.49175:ℝ) * 2.49175) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.4635:ℝ) * 2.4635)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.49175:ℝ) * 2.49175) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0.05432692:ℝ)) (l6v := (0.66538461:ℝ))
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
    (hm5 := hm5bound) (hm5p := by norm_num)
    (hl6 := hl6bound) (hl6p := by norm_num)
    (hv5 := by norm_num) (hv6 := by norm_num)
    (hcoef := by norm_num)
    (hmargin := by norm_num)

theorem cell43_core {y4 y5 y6 : ℝ}
    (hc4l : (2.59710678:ℝ) ≤ y4) (hc4h : y4 ≤ 2.67421356)
    (hc5l : (2.49175:ℝ) ≤ y5) (hc5h : y5 ≤ 2.52)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.59710678:ℝ) * 2.59710678) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.59710678) hc4l
  have hP5Lle : ((2.49175:ℝ) * 2.49175) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.49175) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.52:ℝ) * 2.52) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.49175^2) * (2.058^2) - ((2.59710678^2) - (2.49175^2) - (2.058^2))^2) - (2.59710678^2) * (2.49175^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.59710678:ℝ) * 2.59710678) = 2.59710678 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.59710678)]
  have hsq5 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (31.435444:ℝ) ≤ ea4X ((2.49175:ℝ) * 2.49175) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.151857:ℝ) ≤ Real.sqrt (2 * ((2.49175:ℝ) * 2.49175) * ((2.59710678:ℝ) * 2.59710678)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.49175:ℝ) * 2.49175) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.403381:ℝ) ≤ ((2.59710678:ℝ) * 2.59710678) * 2.49175 / 2 := by norm_num
    have hC2 : (8.062481:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.59710678 / 2 := by norm_num
    have hT3 : (5.817725:ℝ) ≤ Real.sqrt 2 * (((2.49175:ℝ) * 2.49175) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.817725:ℝ) ≤ (1.41421356:ℝ) * (((2.49175:ℝ) * 2.49175) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.49175:ℝ) * 2.49175) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.49175:ℝ) * 2.49175) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.59710678:ℝ) * 2.59710678) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.246059:ℝ) ≤ ea5X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.252117:ℝ) ≤ Real.sqrt (2 * ((2.49175:ℝ) * 2.49175) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.388873:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.058 / 2 := by norm_num
    have hC2 : (5.276734:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.49175 / 2 := by norm_num
    have hT3 : (2.328335:ℝ) ≤ Real.sqrt 2 * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.328335:ℝ) ≤ (1.41421356:ℝ) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.49175:ℝ) * 2.49175) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (23.273019:ℝ) ≤ ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.558753:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.59710678:ℝ) * 2.59710678)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.499846:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.59710678 / 2 := by norm_num
    have hC2 : (6.940567:ℝ) ≤ ((2.59710678:ℝ) * 2.59710678) * 2.058 / 2 := by norm_num
    have hT3 : (3.273853:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.52:ℝ) * 2.52)) / 2 := by
      have hval : (3.273853:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.52:ℝ) * 2.52)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.59710678:ℝ) * 2.59710678) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.59710678:ℝ) * 2.59710678) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.59710678:ℝ) * 2.59710678) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5 : ((2.49175:ℝ) * 2.49175) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.52:ℝ) * 2.52) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.67421356:ℝ)) (p5l := (2.49175:ℝ)) (p5h := (2.52:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.49175^2) * (2.058^2) - ((2.59710678^2) - (2.49175^2) - (2.058^2))^2) - (2.59710678^2) * (2.49175^2) * (2.058^2))
    (ea4L := (31.435444:ℝ)) (ea5L := (21.246059:ℝ)) (ea6L := (23.273019:ℝ))
    (dx4L := ((2.59710678:ℝ) * 2.59710678) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5L := ((2.49175:ℝ) * 2.49175) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.52:ℝ) * 2.52)))
    (dx5H := ((2.52:ℝ) * 2.52) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.49175:ℝ) * 2.49175)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.52:ℝ) * 2.52) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell44_core {y4 y5 y6 : ℝ}
    (hc4l : (2.59710678:ℝ) ≤ y4) (hc4h : y4 ≤ 2.67421356)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ 2.67421356)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hP4Lle : ((2.59710678:ℝ) * 2.59710678) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.59710678) hc4l
  have hP5Lle : ((2.52:ℝ) * 2.52) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.52) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((2.67421356:ℝ) * 2.67421356) := mul_self_le_mul_self hy5.le hc5h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.52^2) * (2.058^2) - ((2.59710678^2) - (2.52^2) - (2.058^2))^2) - (2.59710678^2) * (2.52^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.59710678:ℝ) * 2.59710678) = 2.59710678 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.59710678)]
  have hsq5 : Real.sqrt ((2.52:ℝ) * 2.52) = 2.52 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.52)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (31.918441:ℝ) ≤ ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.255616:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.59710678:ℝ) * 2.59710678)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.498654:ℝ) ≤ ((2.59710678:ℝ) * 2.59710678) * 2.52 / 2 := by norm_num
    have hC2 : (8.246333:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.59710678 / 2 := by norm_num
    have hT3 : (5.917838:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (5.917838:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.59710678:ℝ) * 2.59710678) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.52:ℝ) * 2.52) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.59710678:ℝ) * 2.59710678) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (21.633905:ℝ) ≤ ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.334337:ℝ) ≤ Real.sqrt (2 * ((2.52:ℝ) * 2.52) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (6.534561:ℝ) ≤ ((2.52:ℝ) * 2.52) * 2.058 / 2 := by norm_num
    have hC2 : (5.336558:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.52 / 2 := by norm_num
    have hT3 : (2.428449:ℝ) ≤ Real.sqrt 2 * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.428449:ℝ) ≤ (1.41421356:ℝ) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.52:ℝ) * 2.52) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.67421356:ℝ) * 2.67421356)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (22.706613:ℝ) ≤ ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.558753:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.59710678:ℝ) * 2.59710678)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.499846:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.59710678 / 2 := by norm_num
    have hC2 : (6.940567:ℝ) ≤ ((2.59710678:ℝ) * 2.59710678) * 2.058 / 2 := by norm_num
    have hT3 : (2.707447:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by
      have hval : (2.707447:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.59710678:ℝ) * 2.59710678) - ((2.67421356:ℝ) * 2.67421356)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.59710678:ℝ) * 2.59710678) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.59710678:ℝ) * 2.59710678)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.59710678:ℝ) * 2.59710678) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.59710678:ℝ) * 2.59710678) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5 : ((2.52:ℝ) * 2.52) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.52:ℝ) * 2.52) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((2.67421356:ℝ) * 2.67421356) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4zero : (0:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    exact nb19_h0cut_lfun_nonneg hy4.le
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.67421356:ℝ)) (p5l := (2.52:ℝ)) (p5h := (2.67421356:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.52^2) * (2.058^2) - ((2.59710678^2) - (2.52^2) - (2.058^2))^2) - (2.59710678^2) * (2.52^2) * (2.058^2))
    (ea4L := (31.918441:ℝ)) (ea5L := (21.633905:ℝ)) (ea6L := (22.706613:ℝ))
    (dx4L := ((2.59710678:ℝ) * 2.59710678) * (((2.52:ℝ) * 2.52) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5L := ((2.52:ℝ) * 2.52) * (((2.59710678:ℝ) * 2.59710678) + ((2.058:ℝ) * 2.058) - ((2.67421356:ℝ) * 2.67421356)))
    (dx5H := ((2.67421356:ℝ) * 2.67421356) * (((2.67421356:ℝ) * 2.67421356) + ((2.174:ℝ) * 2.174) - ((2.52:ℝ) * 2.52)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.59710678:ℝ) * 2.59710678) + ((2.52:ℝ) * 2.52) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.67421356:ℝ) * 2.67421356) + ((2.67421356:ℝ) * 2.67421356) - ((2.058:ℝ) * 2.058)))
    (m4 := (0:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell45_core {y4 y5 y6 : ℝ}
    (hc4l : (2.4635:ℝ) ≤ y4) (hc4h : y4 ≤ 2.477625)
    (hc5l : (2.67421356:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.477625:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.4635:ℝ) * 2.4635) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.4635) hc4l
  have hP5Lle : ((2.67421356:ℝ) * 2.67421356) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.477625:ℝ) * 2.477625) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.67421356^2) * (2.058^2) - ((2.4635^2) - (2.67421356^2) - (2.058^2))^2) - (2.4635^2) * (2.67421356^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.4635:ℝ) * 2.4635) = 2.4635 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.4635)]
  have hsq5 : Real.sqrt ((2.67421356:ℝ) * 2.67421356) = 2.67421356 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (32.246314:ℝ) ≤ ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.316733:ℝ) ≤ Real.sqrt (2 * ((2.67421356:ℝ) * 2.67421356) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.67421356:ℝ) * 2.67421356) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.114676:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.67421356 / 2 := by norm_num
    have hC2 : (8.808759:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.4635 / 2 := by norm_num
    have hT3 : (6.006146:ℝ) ≤ Real.sqrt 2 * (((2.67421356:ℝ) * 2.67421356) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (6.006146:ℝ) ≤ (1.41421356:ℝ) * (((2.67421356:ℝ) * 2.67421356) + ((2.4635:ℝ) * 2.4635) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (24.516117:ℝ) ≤ ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.783168:ℝ) ≤ Real.sqrt (2 * ((2.67421356:ℝ) * 2.67421356) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.358809:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.058 / 2 := by norm_num
    have hC2 : (5.663133:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.67421356 / 2 := by norm_num
    have hT3 : (3.711007:ℝ) ≤ Real.sqrt 2 * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) / 2 := by
      have hval : (3.711007:ℝ) ≤ (1.41421356:ℝ) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea5X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (20.260946:ℝ) ≤ ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.169897:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.4635:ℝ) * 2.4635)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.216909:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.4635 / 2 := by norm_num
    have hC2 : (6.244828:ℝ) ≤ ((2.4635:ℝ) * 2.4635) * 2.058 / 2 := by norm_num
    have hT3 : (1.629312:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by
      have hval : (1.629312:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.4635:ℝ) * 2.4635) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.4635:ℝ) * 2.4635) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.4635:ℝ) * 2.4635)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.4635:ℝ) * 2.4635) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.4635:ℝ) * 2.4635) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)) := by norm_num
  have hdx5 : ((2.67421356:ℝ) * 2.67421356) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.477625:ℝ) * 2.477625) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.477625:ℝ) * 2.477625) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.477625:ℝ) * 2.477625) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.477625:ℝ) * 2.477625) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4bound : (0.08149038:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    have h1 : lfun ((2.477625:ℝ) * 0.5) ≤ h0cut y4 * lfun (y4 * 0.5) :=
      h0cut_lfun_ge hc4h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.08149038:ℝ) ≤ lfun ((2.477625:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.477625:ℝ)) (p5l := (2.67421356:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.67421356^2) * (2.058^2) - ((2.4635^2) - (2.67421356^2) - (2.058^2))^2) - (2.4635^2) * (2.67421356^2) * (2.058^2))
    (ea4L := (32.246314:ℝ)) (ea5L := (24.516117:ℝ)) (ea6L := (20.260946:ℝ))
    (dx4L := ((2.4635:ℝ) * 2.4635) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.477625:ℝ) * 2.477625)))
    (dx5L := ((2.67421356:ℝ) * 2.67421356) * (((2.4635:ℝ) * 2.4635) + ((2.058:ℝ) * 2.058) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.477625:ℝ) * 2.477625) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.4635:ℝ) * 2.4635) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.477625:ℝ) * 2.477625) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.08149038:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell46_core {y4 y5 y6 : ℝ}
    (hc4l : (2.477625:ℝ) ≤ y4) (hc4h : y4 ≤ 2.49175)
    (hc5l : (2.67421356:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.49175:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.477625:ℝ) * 2.477625) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.477625) hc4l
  have hP5Lle : ((2.67421356:ℝ) * 2.67421356) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.49175:ℝ) * 2.49175) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.67421356^2) * (2.058^2) - ((2.477625^2) - (2.67421356^2) - (2.058^2))^2) - (2.477625^2) * (2.67421356^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.477625:ℝ) * 2.477625) = 2.477625 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.477625)]
  have hsq5 : Real.sqrt ((2.67421356:ℝ) * 2.67421356) = 2.67421356 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (32.492913:ℝ) ≤ ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.370152:ℝ) ≤ Real.sqrt (2 * ((2.67421356:ℝ) * 2.67421356) * ((2.477625:ℝ) * 2.477625)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.67421356:ℝ) * 2.67421356) + ((2.477625:ℝ) * 2.477625) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.207997:ℝ) ≤ ((2.477625:ℝ) * 2.477625) * 2.67421356 / 2 := by norm_num
    have hC2 : (8.859266:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.477625 / 2 := by norm_num
    have hT3 : (6.055498:ℝ) ≤ Real.sqrt 2 * (((2.67421356:ℝ) * 2.67421356) + ((2.477625:ℝ) * 2.477625) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (6.055498:ℝ) ≤ (1.41421356:ℝ) * (((2.67421356:ℝ) * 2.67421356) + ((2.477625:ℝ) * 2.477625) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.477625:ℝ) * 2.477625) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.477625:ℝ) * 2.477625)
        ≤ ea4X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (24.466483:ℝ) ≤ ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.783168:ℝ) ≤ Real.sqrt (2 * ((2.67421356:ℝ) * 2.67421356) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.358809:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.058 / 2 := by norm_num
    have hC2 : (5.663133:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.67421356 / 2 := by norm_num
    have hT3 : (3.661373:ℝ) ≤ Real.sqrt 2 * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by
      have hval : (3.661373:ℝ) ≤ (1.41421356:ℝ) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (20.453137:ℝ) ≤ ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.211007:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.477625:ℝ) * 2.477625)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.477625:ℝ) * 2.477625) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.246821:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.477625 / 2 := by norm_num
    have hC2 : (6.316645:ℝ) ≤ ((2.477625:ℝ) * 2.477625) * 2.058 / 2 := by norm_num
    have hT3 : (1.678664:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.477625:ℝ) * 2.477625) - ((8:ℝ))) / 2 := by
      have hval : (1.678664:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.477625:ℝ) * 2.477625) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.477625:ℝ) * 2.477625)
        ≤ ea6X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.477625:ℝ) * 2.477625) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.477625:ℝ) * 2.477625)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.477625:ℝ) * 2.477625) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.477625:ℝ) * 2.477625) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)) := by norm_num
  have hdx5 : ((2.67421356:ℝ) * 2.67421356) * (((2.477625:ℝ) * 2.477625) + ((2.058:ℝ) * 2.058) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.477625:ℝ) * 2.477625) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.477625:ℝ) * 2.477625) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.477625:ℝ) * 2.477625) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)) := by norm_num
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
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.49175:ℝ)) (p5l := (2.67421356:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.67421356^2) * (2.058^2) - ((2.477625^2) - (2.67421356^2) - (2.058^2))^2) - (2.477625^2) * (2.67421356^2) * (2.058^2))
    (ea4L := (32.492913:ℝ)) (ea5L := (24.466483:ℝ)) (ea6L := (20.453137:ℝ))
    (dx4L := ((2.477625:ℝ) * 2.477625) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.49175:ℝ) * 2.49175)))
    (dx5L := ((2.67421356:ℝ) * 2.67421356) * (((2.477625:ℝ) * 2.477625) + ((2.058:ℝ) * 2.058) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.49175:ℝ) * 2.49175) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.477625:ℝ) * 2.477625) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.49175:ℝ) * 2.49175) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.05432692:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell47_core {y4 y5 y6 : ℝ}
    (hc4l : (2.49175:ℝ) ≤ y4) (hc4h : y4 ≤ 2.505875)
    (hc5l : (2.67421356:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ))
    (hd0 : (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2) :
    0 < w2aF y4 y5 y6 := by
  have hy4 : (0:ℝ) < y4 := by linarith [hc4l]
  have hy5 : (0:ℝ) < y5 := by linarith [hc5l]
  have hy6 : (0:ℝ) < y6 := by linarith [hc6l]
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.505875:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  have hP4Lle : ((2.49175:ℝ) * 2.49175) ≤ y4 * y4 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.49175) hc4l
  have hP5Lle : ((2.67421356:ℝ) * 2.67421356) ≤ y5 * y5 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356) hc5l
  have hQ6Lle : ((2.058:ℝ) * 2.058) ≤ y6 * y6 :=
    mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 2.058) hc6l
  have hQ6Hge : y6 * y6 ≤ ((2.174:ℝ) * 2.174) :=
    mul_self_le_mul_self hy6.le hc6h
  have hP4Hge : y4 * y4 ≤ ((2.505875:ℝ) * 2.505875) := mul_self_le_mul_self hy4.le hc4h
  have hP5Hge : y5 * y5 ≤ ((8:ℝ)) := by
    have h := mul_self_le_mul_self hy5.le hc5h
    rwa [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)] at h
  have hdh : deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 ≤ 2 * (4 * (2.67421356^2) * (2.058^2) - ((2.49175^2) - (2.67421356^2) - (2.058^2))^2) - (2.49175^2) * (2.67421356^2) * (2.058^2) :=
    dlt_corner (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
      (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hsq4 : Real.sqrt ((2.49175:ℝ) * 2.49175) = 2.49175 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.49175)]
  have hsq5 : Real.sqrt ((2.67421356:ℝ) * 2.67421356) = 2.67421356 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.67421356)]
  have hsq6 : Real.sqrt ((2.058:ℝ) * 2.058) = 2.058 := by
    rw [Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2.058)]
  have hea4min : (32.740327:ℝ) ≤ ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) := by
    unfold ea4X
    rw [hsq5, hsq4]
    have hr : (9.423571:ℝ) ≤ Real.sqrt (2 * ((2.67421356:ℝ) * 2.67421356) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.67421356:ℝ) * 2.67421356) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (8.301852:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.67421356 / 2 := by norm_num
    have hC2 : (8.909773:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.49175 / 2 := by norm_num
    have hT3 : (6.105131:ℝ) ≤ Real.sqrt 2 * (((2.67421356:ℝ) * 2.67421356) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by
      have hval : (6.105131:ℝ) ≤ (1.41421356:ℝ) * (((2.67421356:ℝ) * 2.67421356) + ((2.49175:ℝ) * 2.49175) - ((2.174:ℝ) * 2.174)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea4pt : ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
      ≤ ea4X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea4X ((2.67421356:ℝ) * 2.67421356) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175) :=
      ea4X_mono_a (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hP5Lle
    have s2 : ea4X (y5*y5) ((2.174:ℝ) * 2.174) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea4X_anti_b hQ6Hge
    have s3 : ea4X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea4X (y5*y5) (y6*y6) (y4*y4) :=
      ea4X_mono_c (mul_nonneg hy5.le hy5.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hea5min : (24.416567:ℝ) ≤ ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875) := by
    unfold ea5X
    rw [hsq5, hsq6]
    have hr : (7.783168:ℝ) ≤ Real.sqrt (2 * ((2.67421356:ℝ) * 2.67421356) * ((2.058:ℝ) * 2.058)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (7.358809:ℝ) ≤ ((2.67421356:ℝ) * 2.67421356) * 2.058 / 2 := by norm_num
    have hC2 : (5.663133:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.67421356 / 2 := by norm_num
    have hT3 : (3.611457:ℝ) ≤ Real.sqrt 2 * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) / 2 := by
      have hval : (3.611457:ℝ) ≤ (1.41421356:ℝ) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea5pt : ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
      ≤ ea5X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea5X ((2.67421356:ℝ) * 2.67421356) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
        ≤ ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875) :=
      ea5X_mono_a (by norm_num : (0:ℝ) ≤ (2.058:ℝ) * 2.058) hP5Lle
    have s2 : ea5X (y5*y5) ((2.058:ℝ) * 2.058) ((2.505875:ℝ) * 2.505875)
        ≤ ea5X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875) :=
      ea5X_mono_b (mul_nonneg hy5.le hy5.le) hQ6Lle
    have s3 : ea5X (y5*y5) (y6*y6) ((2.505875:ℝ) * 2.505875)
        ≤ ea5X (y5*y5) (y6*y6) (y4*y4) :=
      ea5X_anti_c hP4Hge
    exact s1.trans (s2.trans s3)
  have hea6min : (20.646021:ℝ) ≤ ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) := by
    unfold ea6X
    rw [hsq4, hsq6]
    have hr : (7.252117:ℝ) ≤ Real.sqrt (2 * ((2.058:ℝ) * 2.058) * ((2.49175:ℝ) * 2.49175)) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    have hs2 := wt2a_sqrt2.1
    have hX : (0:ℝ) ≤ (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((8:ℝ))) / 2 := by norm_num
    have hs3 := mul_le_mul_of_nonneg_left hs2 hX
    have hC1 : (5.276734:ℝ) ≤ ((2.058:ℝ) * 2.058) * 2.49175 / 2 := by norm_num
    have hC2 : (6.388873:ℝ) ≤ ((2.49175:ℝ) * 2.49175) * 2.058 / 2 := by norm_num
    have hT3 : (1.728297:ℝ) ≤ Real.sqrt 2 * (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((8:ℝ))) / 2 := by
      have hval : (1.728297:ℝ) ≤ (1.41421356:ℝ) * (((2.058:ℝ) * 2.058) + ((2.49175:ℝ) * 2.49175) - ((8:ℝ))) / 2 := by norm_num
      linarith [hs3, hval]
    linarith [hr, hC1, hC2, hT3]
  have hea6pt : ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
      ≤ ea6X (y5*y5) (y6*y6) (y4*y4) := by
    have s1 : ea6X ((8:ℝ)) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175) :=
      ea6X_anti_a hP5Hge
    have s2 : ea6X (y5*y5) ((2.058:ℝ) * 2.058) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175) :=
      ea6X_mono_b (by norm_num : (0:ℝ) ≤ (2.49175:ℝ) * 2.49175) hQ6Lle
    have s3 : ea6X (y5*y5) (y6*y6) ((2.49175:ℝ) * 2.49175)
        ≤ ea6X (y5*y5) (y6*y6) (y4*y4) :=
      ea6X_mono_c (mul_nonneg hy6.le hy6.le) hP4Lle
    exact s1.trans (s2.trans s3)
  have hdx4 : ((2.49175:ℝ) * 2.49175) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875))
      ≤ y4*y4*(y5*y5 + y6*y6 - y4*y4) :=
    dx4_ge hP4Lle hP5Lle hQ6Lle hP4Hge (by norm_num) (by norm_num)
  have hdx4p : (0:ℝ) < ((2.49175:ℝ) * 2.49175) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)) := by norm_num
  have hdx5 : ((2.67421356:ℝ) * 2.67421356) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((8:ℝ)))
      ≤ y5*y5*(y4*y4 + y6*y6 - y5*y5) :=
    dx5_ge hP5Lle hP4Lle hQ6Lle hP5Hge (by norm_num) (by norm_num)
  have hdx5p : (0:ℝ) < ((2.67421356:ℝ) * 2.67421356) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((8:ℝ))) := by norm_num
  have hdx5' : y5*y5*(y4*y4 + y6*y6 - y5*y5)
      ≤ ((8:ℝ)) * (((2.505875:ℝ) * 2.505875) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) :=
    dx5_le hP5Hge hP4Hge hQ6Hge hP5Lle
      (by linarith [hP4Lle, hQ6Lle, hP5Hge]) (by norm_num)
  have hdx5p' : (0:ℝ) < ((8:ℝ)) * (((2.505875:ℝ) * 2.505875) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)) := by norm_num
  have hdx6 : ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174))
      ≤ y6*y6*(y4*y4 + y5*y5 - y6*y6) :=
    dx6_ge hQ6Lle hP4Lle hP5Lle hQ6Hge (by norm_num) (by norm_num)
  have hdx6p : (0:ℝ) < ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)) := by norm_num
  have hdx6' : y6*y6*(y4*y4 + y5*y5 - y6*y6)
      ≤ ((2.174:ℝ) * 2.174) * (((2.505875:ℝ) * 2.505875) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)) :=
    dx6_le hQ6Hge hP4Hge hP5Hge hQ6Lle
      (by linarith [hP4Lle, hP5Lle, hQ6Hge]) (by norm_num)
  have hdx6p' : (0:ℝ) < ((2.174:ℝ) * 2.174) * (((2.505875:ℝ) * 2.505875) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)) := by norm_num
  have hm4bound : (0.02716346:ℝ) ≤ lfun (y4 * 0.5) * h0cut y4 := by
    rw [mul_comm (lfun (y4 * 0.5)) (h0cut y4)]
    have h1 : lfun ((2.505875:ℝ) * 0.5) ≤ h0cut y4 * lfun (y4 * 0.5) :=
      h0cut_lfun_ge hc4h (by rw [nb19_two_h0]; norm_num)
    have h0v : h0 = (1.26:ℝ) := rfl
    have h2 : (0.02716346:ℝ) ≤ lfun ((2.505875:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  have hm5zero : (0:ℝ) ≤ lfun (y5 * 0.5) * h0cut y5 := by
    rw [mul_comm (lfun (y5 * 0.5)) (h0cut y5)]
    exact nb19_h0cut_lfun_nonneg hy5.le
  have hl6bound : (0.66538461:ℝ) ≤ lfun (y6 * 0.5) := by
    have h0v : h0 = (1.26:ℝ) := rfl
    have h1 := lfun_half_ge hc6h (by rw [h0v]; norm_num)
    have h2 : (0.66538461:ℝ) ≤ lfun ((2.174:ℝ) * 0.5) := by
      unfold lfun
      rw [h0v]
      norm_num
    exact h2.trans h1
  refine w2a_cell (p4h := (2.505875:ℝ)) (p5l := (2.67421356:ℝ)) (p5h := (2.82842713:ℝ))
    (q6l := (2.058:ℝ)) (q6h := (2.174:ℝ))
    (Dh := 2 * (4 * (2.67421356^2) * (2.058^2) - ((2.49175^2) - (2.67421356^2) - (2.058^2))^2) - (2.49175^2) * (2.67421356^2) * (2.058^2))
    (ea4L := (32.740327:ℝ)) (ea5L := (24.416567:ℝ)) (ea6L := (20.646021:ℝ))
    (dx4L := ((2.49175:ℝ) * 2.49175) * (((2.67421356:ℝ) * 2.67421356) + ((2.058:ℝ) * 2.058) - ((2.505875:ℝ) * 2.505875)))
    (dx5L := ((2.67421356:ℝ) * 2.67421356) * (((2.49175:ℝ) * 2.49175) + ((2.058:ℝ) * 2.058) - ((8:ℝ))))
    (dx5H := ((8:ℝ)) * (((2.505875:ℝ) * 2.505875) + ((2.174:ℝ) * 2.174) - ((2.67421356:ℝ) * 2.67421356)))
    (dx6L := ((2.058:ℝ) * 2.058) * (((2.49175:ℝ) * 2.49175) + ((2.67421356:ℝ) * 2.67421356) - ((2.174:ℝ) * 2.174)))
    (dx6H := ((2.174:ℝ) * 2.174) * (((2.505875:ℝ) * 2.505875) + ((8:ℝ)) - ((2.058:ℝ) * 2.058)))
    (m4 := (0.02716346:ℝ)) (m5 := (0:ℝ)) (l6v := (0.66538461:ℝ))
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

theorem cell48_vac {y4 y5 y6 : ℝ}
    (hc4l : (2.67421356:ℝ) ≤ y4) (hc4h : y4 ≤ Real.sqrt 8)
    (hc5l : (2.52:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  refine cell_vacuous (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
    (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  norm_num

theorem cell49_vac {y4 y5 y6 : ℝ}
    (hc4l : (2.52:ℝ) ≤ y4) (hc4h : y4 ≤ 2.59710678)
    (hc5l : (2.67421356:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.59710678:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  refine cell_vacuous (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
    (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  norm_num

theorem cell50_vac {y4 y5 y6 : ℝ}
    (hc4l : (2.59710678:ℝ) ≤ y4) (hc4h : y4 ≤ 2.67421356)
    (hc5l : (2.67421356:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.67421356:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  refine cell_vacuous (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
    (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  norm_num

theorem cell51_vac {y4 y5 y6 : ℝ}
    (hc4l : (2.505875:ℝ) ≤ y4) (hc4h : y4 ≤ 2.52)
    (hc5l : (2.67421356:ℝ) ≤ y5) (hc5h : y5 ≤ Real.sqrt 8)
    (hc6l : (2.058:ℝ) ≤ y6) (hc6h : y6 ≤ (2.174:ℝ)) :
    ¬ (0:ℝ) ≤ deltaX (y4*y4) 2 (y5*y5) 2 (y6*y6) 2 := by
  have hc4box : y4 ≤ Real.sqrt 8 := hc4h.trans ((by norm_num : (2.52:ℝ) ≤ 2.82842712).trans wt2a_sqrt8.1)
  have hc5box : y5 ≤ Real.sqrt 8 := hc5h
  refine cell_vacuous (by linarith [hc4l]) hc4box (by linarith [hc5l]) hc5box
    (by linarith [hc6l]) (by linarith [hc6h]) hc4l hc5l hc6l (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  norm_num

end Kepler.NliBanks25
