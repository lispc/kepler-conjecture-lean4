import Kepler.NliBanks6

/-!
Kepler.NliBanks7 — W3 lane `nli-unknown-w3`, task 3 (GCKBQEA), part 2.

* sharpened Marchal envelope `1.23175 ≤ hminus` (same certificate shape as
  `Kepler.NliHminus`, refined five-digit bound);
* `tan 0.606 < 0.6936` via `Real.sin_bound`/`Real.cos_bound` at `0.1515`
  and the quadruple-angle formula;
* `gckbP` is concave in each of `x2 … x6` on the box (the second derivative is
  `−Aₖ` with `Aₖ` an explicit nonnegative form).
-/

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks7
open Kepler.Text
open Kepler.NliBanks6

private theorem marchalQuartic_lt_lmfun_123175 {h : ℝ} (h1 : 1.2 ≤ h) (h2 : h ≤ 1.23175) :
    marchalQuartic h < lmfun h := by
  have hs_lo : (1.41421356 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs_hi : Real.sqrt 2 < 1.41421357 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hD : (0:ℝ) < (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have a : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hDlo : (0:ℝ) < (1.41421356 - 1) * 5 * (hplus - 1) := by
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hDge : (1.41421356 - 1) * 5 * (hplus - 1) ≤ (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have b : (0:ℝ) < 5 * (hplus - 1) := by rw [hplus]; norm_num
    nlinarith [hs_lo]
  have hA : (0:ℝ) < Real.sqrt 2 - h := by linarith
  have hB : (0:ℝ) < hplus - h := by rw [hplus]; linarith
  have hC : (0:ℝ) < 17 * h - 9 * h ^ 2 - 3 := by
    have hp1 : (0:ℝ) ≤ h - 1.2 := by linarith
    have hp2 : (0:ℝ) ≤ 1.23175 - h := by linarith
    have hprod : (0:ℝ) ≤ (h - 1.2) * (1.23175 - h) := mul_nonneg hp1 hp2
    nlinarith [hprod]
  have hE : (0:ℝ) < h0 - h := by rw [h0]; linarith
  have hE1 : (0:ℝ) < h0 - 1 := by rw [h0]; norm_num
  have hmq : marchalQuartic h =
      (Real.sqrt 2 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) /
        ((Real.sqrt 2 - 1) * 5 * (hplus - 1)) := by
    unfold marchalQuartic
    have e : (Real.sqrt 2 - h) * (h - hplus) * (9 * h ^ 2 - 17 * h + 3)
        = (Real.sqrt 2 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) := by ring
    rw [e]
  have hlm : lmfun h = (h0 - h) / (h0 - 1) := by
    unfold lmfun
    rw [if_pos (by rw [h0]; linarith)]
  have hkey : (0:ℝ) < (h0 - h) * ((1.41421356 - 1) * 5 * (hplus - 1)) -
      (1.41421357 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) := by
    rw [show h0 = (1.26:ℝ) from rfl, show hplus = (1.3254:ℝ) from rfl]
    have ht0 : (0:ℝ) ≤ 1.23175 - h := by linarith
    have htT : 1.23175 - h ≤ 0.03175 := by linarith
    have h2t : (1.23175 - h) ^ 2 ≤ 0.03175 * (1.23175 - h) := by nlinarith
    have h3t : (1.23175 - h) ^ 3 ≤ 0.03175 ^ 2 * (1.23175 - h) := by nlinarith
    have h4t : (0:ℝ) ≤ (1.23175 - h) ^ 4 := by positivity
    nlinarith [ht0, htT, h2t, h3t, h4t]
  rw [hmq, hlm, div_lt_div_iff₀ hD hE1]
  have hBCE : (0:ℝ) < (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) :=
    mul_pos (mul_pos hB hC) hE1
  have hltA : Real.sqrt 2 - h < 1.41421357 - h := by linarith
  have hp : (Real.sqrt 2 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1))
      < (1.41421357 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1)) :=
    mul_lt_mul_of_pos_right hltA hBCE
  have step1 : (Real.sqrt 2 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1)
      < (1.41421357 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) := by
    linarith [hp]
  have hDge' : (h0 - h) * ((1.41421356 - 1) * 5 * (hplus - 1))
      ≤ (h0 - h) * ((Real.sqrt 2 - 1) * 5 * (hplus - 1)) :=
    mul_le_mul_of_nonneg_left hDge hE.le
  linarith [step1, hDge', hkey]

theorem hminus_ge_123175 : (1.23175 : ℝ) ≤ hminus := by
  obtain ⟨h1, -, hspec⟩ := mi_hminus_prop
  by_contra hcon
  push_neg at hcon
  have hlt := marchalQuartic_lt_lmfun_123175 (h := hminus) h1 (le_of_lt hcon)
  rw [hspec] at hlt
  exact absurd hlt (lt_irrefl _)


theorem tan0606_lt : Real.tan (0.606:ℝ) < 0.6936 := by
  have hx : |(0.1515:ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by norm_num)]; norm_num
  have hs := Real.sin_bound (x := (0.1515:ℝ)) hx
  have hc := Real.cos_bound (x := (0.1515:ℝ)) hx
  have hsinle : Real.sin (0.1515:ℝ) ≤ (0.1515:ℝ) - 0.1515^3/6 + 0.1515^5/100 := by
    have h := (abs_le.mp hs).2
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 0.1515)] at h
    linarith
  have hcosge : (1:ℝ) - 0.1515^2/2 - 0.1515^4*(5/96) ≤ Real.cos (0.1515:ℝ) := by
    have h := (abs_le.mp hc).1
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 0.1515)] at h
    linarith
  have hcospos : (0:ℝ) < Real.cos (0.1515:ℝ) := Real.cos_pos_of_le_one hx
  have hsinpos : (0:ℝ) < Real.sin (0.1515:ℝ) :=
    Real.sin_pos_of_pos_of_le_one (by norm_num) (by norm_num)
  have ht0 : (0:ℝ) ≤ Real.tan (0.1515:ℝ) := by
    rw [Real.tan_eq_sin_div_cos]
    exact le_of_lt (div_pos hsinpos hcospos)
  have htle : Real.tan (0.1515:ℝ) ≤ 0.1527 := by
    rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcospos]
    have hSC : (0.1515:ℝ) - 0.1515^3/6 + 0.1515^5/100
        ≤ 0.1527 * (1 - 0.1515^2/2 - 0.1515^4*(5/96)) := by norm_num
    nlinarith [hsinle, hcosge, hSC]
  have h4 : Real.tan (4*(0.1515:ℝ)) =
      4 * Real.tan (0.1515:ℝ) * (1 - (Real.tan (0.1515:ℝ))^2) /
        (1 - 6*(Real.tan (0.1515:ℝ))^2 + (Real.tan (0.1515:ℝ))^4) := by
    have h2 := Real.tan_two_mul (x := (0.1515:ℝ))
    have h4b := Real.tan_two_mul (x := (2*(0.1515:ℝ)))
    rw [show (2:ℝ)*(2*0.1515) = 4*0.1515 by ring] at h4b
    rw [h2] at h4b
    have htne : (1:ℝ) - (Real.tan (0.1515:ℝ))^2 ≠ 0 := by nlinarith [ht0, htle]
    convert h4b using 1
    field_simp
    ring
  have hden : (0:ℝ) < 1 - 6*(Real.tan (0.1515:ℝ))^2 + (Real.tan (0.1515:ℝ))^4 := by
    nlinarith [ht0, htle]
  have hg : (0:ℝ) < 0.6936*(1 - 6*(Real.tan (0.1515:ℝ))^2 + (Real.tan (0.1515:ℝ))^4)
      - 4*Real.tan (0.1515:ℝ)*(1 - (Real.tan (0.1515:ℝ))^2) := by
    set t := Real.tan (0.1515:ℝ) with ht
    have key : 0.6936*(1 - 6*t^2 + t^4) - 4*t*(1 - t^2)
        = (0.6936*(1 - 6*0.1527^2 + 0.1527^4) - 4*0.1527*(1 - 0.1527^2))
          + (0.1527 - t)*(4 + 4.1616*(t + 0.1527) - 4*(t^2 + t*0.1527 + 0.1527^2)
              - 0.6936*(t + 0.1527)*(t^2 + 0.1527^2)) := by ring
    have hA : (0:ℝ) < 0.6936*(1 - 6*0.1527^2 + 0.1527^4) - 4*0.1527*(1 - 0.1527^2) := by
      norm_num
    have hB : (0:ℝ) ≤ 4 + 4.1616*(t + 0.1527) - 4*(t^2 + t*0.1527 + 0.1527^2)
        - 0.6936*(t + 0.1527)*(t^2 + 0.1527^2) := by
      nlinarith [ht0, htle]
    have hC : (0:ℝ) ≤ 0.1527 - t := by linarith
    nlinarith [key, hA, mul_nonneg hC hB]
  have hfin : 4 * Real.tan (0.1515:ℝ) * (1 - (Real.tan (0.1515:ℝ))^2) /
      (1 - 6*(Real.tan (0.1515:ℝ))^2 + (Real.tan (0.1515:ℝ))^4) < 0.6936 := by
    rw [div_lt_iff₀ hden]
    nlinarith [hg]
  rw [show (0.606:ℝ) = 4*0.1515 by norm_num, h4]
  exact hfin



/-- `gckbP` is concave in `x2` on the box. -/
theorem P_concave_2 (x1 x3 x4 x5 x6 : ℝ)
    (h1l : (6.06883225:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8)
    (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8)
    (a b t : ℝ) (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ)) (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) :
    min (gckbP x1 a x3 x4 x5 x6) (gckbP x1 b x3 x4 x5 x6) ≤ gckbP x1 t x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : gckbP x1 t x3 x4 x5 x6 -
      (lam * gckbP x1 a x3 x4 x5 x6 + (1 - lam) * gckbP x1 b x3 x4 x5 x6)
      = ((751689*x1^2 - 1503378*x1*x3 + 7753378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2)/1562500) * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold gckbP deltaX deltaX4; ring
  have hnn : (0:ℝ) ≤ ((751689*x1^2 - 1503378*x1*x3 + 7753378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2)/1562500) * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    have hA : (0:ℝ) ≤ (751689*x1^2 - 1503378*x1*x3 + 7753378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2)/1562500 := by
      have hsq : (0:ℝ) ≤ 751689*(x1 - x3)^2 := by positivity
      have hlin : (0:ℝ) ≤ 751689*x5 + 7753378*x1 - 1503378*x3 := by nlinarith [h1l, h3h, h5]
      have hmul : (0:ℝ) ≤ x5 * (751689*x5 + 7753378*x1 - 1503378*x3) := mul_nonneg (by linarith) hlin
      have hnum : (0:ℝ) ≤ 751689*(x1 - x3)^2 + x5*(751689*x5 + 7753378*x1 - 1503378*x3) := by linarith [hsq, hmul]
      have hexp : (751689*x1^2 - 1503378*x1*x3 + 7753378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2) = 751689*(x1 - x3)^2 + x5*(751689*x5 + 7753378*x1 - 1503378*x3) := by ring
      rw [hexp]
      exact div_nonneg hnum (by norm_num)
    exact mul_nonneg (mul_nonneg hA h1') h2'
  have hmin : min (gckbP x1 a x3 x4 x5 x6) (gckbP x1 b x3 x4 x5 x6) ≤
      lam * gckbP x1 a x3 x4 x5 x6 + (1 - lam) * gckbP x1 b x3 x4 x5 x6 := by
    have hl := min_le_left (gckbP x1 a x3 x4 x5 x6) (gckbP x1 b x3 x4 x5 x6)
    have hr := min_le_right (gckbP x1 a x3 x4 x5 x6) (gckbP x1 b x3 x4 x5 x6)
    nlinarith
  linarith

/-- `gckbP` is concave in `x3` on the box. -/
theorem P_concave_3 (x1 x2 x4 x5 x6 : ℝ)
    (h1l : (6.06883225:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8)
    (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8)
    (a b t : ℝ) (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ)) (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) :
    min (gckbP x1 x2 a x4 x5 x6) (gckbP x1 x2 b x4 x5 x6) ≤ gckbP x1 x2 t x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : gckbP x1 x2 t x4 x5 x6 -
      (lam * gckbP x1 x2 a x4 x5 x6 + (1 - lam) * gckbP x1 x2 b x4 x5 x6)
      = ((751689*x1^2 - 1503378*x1*x2 + 7753378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2)/1562500) * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold gckbP deltaX deltaX4; ring
  have hnn : (0:ℝ) ≤ ((751689*x1^2 - 1503378*x1*x2 + 7753378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2)/1562500) * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    have hA : (0:ℝ) ≤ (751689*x1^2 - 1503378*x1*x2 + 7753378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2)/1562500 := by
      have hsq : (0:ℝ) ≤ 751689*(x1 - x2)^2 := by positivity
      have hlin : (0:ℝ) ≤ 751689*x6 + 7753378*x1 - 1503378*x2 := by nlinarith [h1l, h2h, h6]
      have hmul : (0:ℝ) ≤ x6 * (751689*x6 + 7753378*x1 - 1503378*x2) := mul_nonneg (by linarith) hlin
      have hnum : (0:ℝ) ≤ 751689*(x1 - x2)^2 + x6*(751689*x6 + 7753378*x1 - 1503378*x2) := by linarith [hsq, hmul]
      have hexp : (751689*x1^2 - 1503378*x1*x2 + 7753378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2) = 751689*(x1 - x2)^2 + x6*(751689*x6 + 7753378*x1 - 1503378*x2) := by ring
      rw [hexp]
      exact div_nonneg hnum (by norm_num)
    exact mul_nonneg (mul_nonneg hA h1') h2'
  have hmin : min (gckbP x1 x2 a x4 x5 x6) (gckbP x1 x2 b x4 x5 x6) ≤
      lam * gckbP x1 x2 a x4 x5 x6 + (1 - lam) * gckbP x1 x2 b x4 x5 x6 := by
    have hl := min_le_left (gckbP x1 x2 a x4 x5 x6) (gckbP x1 x2 b x4 x5 x6)
    have hr := min_le_right (gckbP x1 x2 a x4 x5 x6) (gckbP x1 x2 b x4 x5 x6)
    nlinarith
  linarith

/-- `gckbP` is concave in `x4` on the box. -/
theorem P_concave_4 (x1 x2 x3 x5 x6 : ℝ)
    (h1l : (6.06883225:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8)
    (a b t : ℝ) (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ)) (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) :
    min (gckbP x1 x2 x3 a x5 x6) (gckbP x1 x2 x3 b x5 x6) ≤ gckbP x1 x2 x3 t x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : gckbP x1 x2 x3 t x5 x6 -
      (lam * gckbP x1 x2 x3 a x5 x6 + (1 - lam) * gckbP x1 x2 x3 b x5 x6)
      = (4628378*x1^2/781250) * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold gckbP deltaX deltaX4; ring
  have hnn : (0:ℝ) ≤ (4628378*x1^2/781250) * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    have hA : (0:ℝ) ≤ 4628378*x1^2/781250 := by
      positivity
    exact mul_nonneg (mul_nonneg hA h1') h2'
  have hmin : min (gckbP x1 x2 x3 a x5 x6) (gckbP x1 x2 x3 b x5 x6) ≤
      lam * gckbP x1 x2 x3 a x5 x6 + (1 - lam) * gckbP x1 x2 x3 b x5 x6 := by
    have hl := min_le_left (gckbP x1 x2 x3 a x5 x6) (gckbP x1 x2 x3 b x5 x6)
    have hr := min_le_right (gckbP x1 x2 x3 a x5 x6) (gckbP x1 x2 x3 b x5 x6)
    nlinarith
  linarith

/-- `gckbP` is concave in `x5` on the box. -/
theorem P_concave_5 (x1 x2 x3 x4 x6 : ℝ)
    (h1l : (6.06883225:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8)
    (a b t : ℝ) (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ)) (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) :
    min (gckbP x1 x2 x3 x4 a x6) (gckbP x1 x2 x3 x4 b x6) ≤ gckbP x1 x2 x3 x4 t x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : gckbP x1 x2 x3 x4 t x6 -
      (lam * gckbP x1 x2 x3 x4 a x6 + (1 - lam) * gckbP x1 x2 x3 x4 b x6)
      = ((751689*x1^2 + 7753378*x1*x2 - 1503378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2)/1562500) * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold gckbP deltaX deltaX4; ring
  have hnn : (0:ℝ) ≤ ((751689*x1^2 + 7753378*x1*x2 - 1503378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2)/1562500) * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    have hA : (0:ℝ) ≤ (751689*x1^2 + 7753378*x1*x2 - 1503378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2)/1562500 := by
      have hsq : (0:ℝ) ≤ 751689*(x1 - x6)^2 := by positivity
      have hlin : (0:ℝ) ≤ 751689*x2 + 7753378*x1 - 1503378*x6 := by nlinarith [h1l, h2, h6h]
      have hmul : (0:ℝ) ≤ x2 * (751689*x2 + 7753378*x1 - 1503378*x6) := mul_nonneg (by linarith) hlin
      have hnum : (0:ℝ) ≤ 751689*(x1 - x6)^2 + x2*(751689*x2 + 7753378*x1 - 1503378*x6) := by linarith [hsq, hmul]
      have hexp : (751689*x1^2 + 7753378*x1*x2 - 1503378*x1*x6 + 751689*x2^2 - 1503378*x2*x6 + 751689*x6^2) = 751689*(x1 - x6)^2 + x2*(751689*x2 + 7753378*x1 - 1503378*x6) := by ring
      rw [hexp]
      exact div_nonneg hnum (by norm_num)
    exact mul_nonneg (mul_nonneg hA h1') h2'
  have hmin : min (gckbP x1 x2 x3 x4 a x6) (gckbP x1 x2 x3 x4 b x6) ≤
      lam * gckbP x1 x2 x3 x4 a x6 + (1 - lam) * gckbP x1 x2 x3 x4 b x6 := by
    have hl := min_le_left (gckbP x1 x2 x3 x4 a x6) (gckbP x1 x2 x3 x4 b x6)
    have hr := min_le_right (gckbP x1 x2 x3 x4 a x6) (gckbP x1 x2 x3 x4 b x6)
    nlinarith
  linarith

/-- `gckbP` is concave in `x6` on the box. -/
theorem P_concave_6 (x1 x2 x3 x4 x5 : ℝ)
    (h1l : (6.06883225:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8)
    (a b t : ℝ) (ha : (4:ℝ) ≤ a) (hb : a ≤ b) (hbh : b ≤ (8:ℝ)) (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) :
    min (gckbP x1 x2 x3 x4 x5 a) (gckbP x1 x2 x3 x4 x5 b) ≤ gckbP x1 x2 x3 x4 x5 t := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : gckbP x1 x2 x3 x4 x5 t -
      (lam * gckbP x1 x2 x3 x4 x5 a + (1 - lam) * gckbP x1 x2 x3 x4 x5 b)
      = ((751689*x1^2 + 7753378*x1*x3 - 1503378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2)/1562500) * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold gckbP deltaX deltaX4; ring
  have hnn : (0:ℝ) ≤ ((751689*x1^2 + 7753378*x1*x3 - 1503378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2)/1562500) * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    have hA : (0:ℝ) ≤ (751689*x1^2 + 7753378*x1*x3 - 1503378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2)/1562500 := by
      have hsq : (0:ℝ) ≤ 751689*(x1 - x5)^2 := by positivity
      have hlin : (0:ℝ) ≤ 751689*x3 + 7753378*x1 - 1503378*x5 := by nlinarith [h1l, h3, h5h]
      have hmul : (0:ℝ) ≤ x3 * (751689*x3 + 7753378*x1 - 1503378*x5) := mul_nonneg (by linarith) hlin
      have hnum : (0:ℝ) ≤ 751689*(x1 - x5)^2 + x3*(751689*x3 + 7753378*x1 - 1503378*x5) := by linarith [hsq, hmul]
      have hexp : (751689*x1^2 + 7753378*x1*x3 - 1503378*x1*x5 + 751689*x3^2 - 1503378*x3*x5 + 751689*x5^2) = 751689*(x1 - x5)^2 + x3*(751689*x3 + 7753378*x1 - 1503378*x5) := by ring
      rw [hexp]
      exact div_nonneg hnum (by norm_num)
    exact mul_nonneg (mul_nonneg hA h1') h2'
  have hmin : min (gckbP x1 x2 x3 x4 x5 a) (gckbP x1 x2 x3 x4 x5 b) ≤
      lam * gckbP x1 x2 x3 x4 x5 a + (1 - lam) * gckbP x1 x2 x3 x4 x5 b := by
    have hl := min_le_left (gckbP x1 x2 x3 x4 x5 a) (gckbP x1 x2 x3 x4 x5 b)
    have hr := min_le_right (gckbP x1 x2 x3 x4 x5 a) (gckbP x1 x2 x3 x4 x5 b)
    nlinarith
  linarith

end Kepler.NliBanks7
