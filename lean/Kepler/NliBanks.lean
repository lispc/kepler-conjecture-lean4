import Kepler.Text.PackingAuto21

namespace Kepler.NliBanks
open Kepler.Text

/-! ## 服务件：`deltaX` 对每个变量单独凹（二次系数 = −配对变量） -/

private theorem dX_concave_1 (x2 x3 x4 x5 x6 : ℝ) (hx4 : 0 < x4)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6) ≤
      deltaX t x2 x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX t x2 x3 x4 x5 x6 -
      (lam * deltaX a x2 x3 x4 x5 x6 + (1 - lam) * deltaX b x2 x3 x4 x5 x6)
      = x4 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hnn : 0 ≤ x4 * (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6) ≤
      lam * deltaX a x2 x3 x4 x5 x6 + (1 - lam) * deltaX b x2 x3 x4 x5 x6 := by
    have hl := min_le_left (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6)
    have hr := min_le_right (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6)
    nlinarith
  linarith

private theorem dX_concave_2 (x1 x3 x4 x5 x6 : ℝ) (hx5 : 0 < x5)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6) ≤
      deltaX x1 t x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 t x3 x4 x5 x6 -
      (lam * deltaX x1 a x3 x4 x5 x6 + (1 - lam) * deltaX x1 b x3 x4 x5 x6)
      = x5 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hnn : 0 ≤ x5 * (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6) ≤
      lam * deltaX x1 a x3 x4 x5 x6 + (1 - lam) * deltaX x1 b x3 x4 x5 x6 := by
    have hl := min_le_left (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6)
    have hr := min_le_right (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6)
    nlinarith
  linarith

private theorem dX_concave_3 (x1 x2 x4 x5 x6 : ℝ) (hx6 : 0 < x6)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6) ≤
      deltaX x1 x2 t x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 t x4 x5 x6 -
      (lam * deltaX x1 x2 a x4 x5 x6 + (1 - lam) * deltaX x1 x2 b x4 x5 x6)
      = x6 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hnn : 0 ≤ x6 * (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6) ≤
      lam * deltaX x1 x2 a x4 x5 x6 + (1 - lam) * deltaX x1 x2 b x4 x5 x6 := by
    have hl := min_le_left (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6)
    have hr := min_le_right (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6)
    nlinarith
  linarith

private theorem dX_concave_4 (x1 x2 x3 x5 x6 : ℝ) (hx1 : 0 < x1)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6) ≤
      deltaX x1 x2 x3 t x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 x3 t x5 x6 -
      (lam * deltaX x1 x2 x3 a x5 x6 + (1 - lam) * deltaX x1 x2 x3 b x5 x6)
      = x1 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hnn : 0 ≤ x1 * (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6) ≤
      lam * deltaX x1 x2 x3 a x5 x6 + (1 - lam) * deltaX x1 x2 x3 b x5 x6 := by
    have hl := min_le_left (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6)
    have hr := min_le_right (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6)
    nlinarith
  linarith

private theorem dX_concave_5 (x1 x2 x3 x4 x6 : ℝ) (hx2 : 0 < x2)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6) ≤
      deltaX x1 x2 x3 x4 t x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 x3 x4 t x6 -
      (lam * deltaX x1 x2 x3 x4 a x6 + (1 - lam) * deltaX x1 x2 x3 x4 b x6)
      = x2 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hnn : 0 ≤ x2 * (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6) ≤
      lam * deltaX x1 x2 x3 x4 a x6 + (1 - lam) * deltaX x1 x2 x3 x4 b x6 := by
    have hl := min_le_left (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6)
    have hr := min_le_right (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6)
    nlinarith
  linarith

private theorem dX_concave_6 (x1 x2 x3 x4 x5 : ℝ) (hx3 : 0 < x3)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b) ≤
      deltaX x1 x2 x3 x4 x5 t := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 x3 x4 x5 t -
      (lam * deltaX x1 x2 x3 x4 x5 a + (1 - lam) * deltaX x1 x2 x3 x4 x5 b)
      = x3 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hnn : 0 ≤ x3 * (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b) ≤
      lam * deltaX x1 x2 x3 x4 x5 a + (1 - lam) * deltaX x1 x2 x3 x4 x5 b := by
    have hl := min_le_left (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b)
    have hr := min_le_right (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b)
    nlinarith
  linarith

set_option maxHeartbeats 4000000 in
/-- 有理放大盒上的角点判决：`[5.76,7.0756]×[4,8.0089]×[4,8.0089]×[4,7.0756]×[4,8.0089]×[4,8.0089]`
上 `deltaX ≥ 92`（64 角点全为有理数，`norm_num` 判决）。 -/
private theorem dX_box_ge (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.0756)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8.0089)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8.0089)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 7.0756)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8.0089)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8.0089) :
    (92:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 5.76 x2 x3 x4 x5 x6) (deltaX 7.0756 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 5.76 7.0756 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 4 8.0089 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 4 8.0089 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 7.0756 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8.0089 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8.0089 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

set_option maxHeartbeats 1000000 in
/-- rest 34：HOL ineq entry `BIXPCGW b`（ineq.hl:758）。**PURE-LEAN 探针**：
第三支 `deltaY > 60` 在盒上恒成立（真最小值 ≈ 96.1，角点判决 92 留 1.5 倍余量）。 -/
theorem nliRestBIXPCGWb : bank_BIXPCGWb := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hp : hplus = 1.3254 := rfl
  have hm12 : (1.2:ℝ) ≤ hminus := mi_hminus_prop.1
  have hs8 : Real.sqrt 8 ≤ 2.83 := by
    rw [show (2.83:ℝ) = Real.sqrt (2.83^2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- x = y^2 盒（有理放大）
  have x1l : (5.76:ℝ) ≤ y1 * y1 := by
    have h : (2.4:ℝ) ≤ y1 := by linarith
    nlinarith
  have x1h : y1 * y1 ≤ 7.0756 := by
    have h : y1 ≤ (2.66:ℝ) := by rw [hp] at h1h; linarith
    nlinarith
  have x2l : (4:ℝ) ≤ y2 * y2 := by nlinarith
  have x2h : y2 * y2 ≤ 8.0089 := by nlinarith
  have x3l : (4:ℝ) ≤ y3 * y3 := by nlinarith
  have x3h : y3 * y3 ≤ 8.0089 := by nlinarith
  have x4l : (4:ℝ) ≤ y4 * y4 := by nlinarith
  have x4h : y4 * y4 ≤ 7.0756 := by
    have h : y4 ≤ (2.66:ℝ) := by rw [hp] at h4h; linarith
    nlinarith
  have x5l : (4:ℝ) ≤ y5 * y5 := by nlinarith
  have x5h : y5 * y5 ≤ 8.0089 := by nlinarith
  have x6l : (4:ℝ) ≤ y6 * y6 := by nlinarith
  have x6h : y6 * y6 ≤ 8.0089 := by nlinarith
  right; left
  have h := dX_box_ge (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
    x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  unfold deltaY
  linarith

#print axioms Kepler.NliBanks.nliRestBIXPCGWb
end Kepler.NliBanks
