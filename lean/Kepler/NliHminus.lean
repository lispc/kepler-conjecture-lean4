import Kepler.Text.PackingAuto21

/-!
Kepler.NliHminus — W2 lane `nli-unknown-w2`, task W2-0.

`hminus` is the Marchal root (`pack_defs.hl:153`): the unique `x ∈ [1.2, 1.3)`
with `marchalQuartic x = lmfun x`.  The repository only exposed
`1.2 ≤ hminus` (`mi_hminus_prop.1`); several bank entries in the rad2 family
need the five-digit envelope `1.2313664 ≤ hminus` (equivalently
`6.0650528 ≤ 4·hminus²`, the `x1 = 4·hminus²` box edge).

Shape of the proof (no certificates, no `sorry`):

* `marchalQuartic h − lmfun h` is strictly negative on `[1.2, 1.2313664]`:
  after clearing the positive denominator `(√2−1)·5·(hplus−1)` the assertion
  is the quartic
  `0 < (h0−h)·(s_lo−1)·5·(hplus−1) − (s_hi−h)·(hplus−h)·(17h−9h²−3)·(h0−1)`
  with the rational enclosures `s_lo = 1.41421356 < √2 < 1.41421357 = s_hi`.
  Substituting `h = 1.2313664 − t`, `t ∈ [0, 0.0313664]`, all four `t`-powers
  are dominated by `t` (`t^k ≤ T^(k-1)·t`) and `nlinarith` closes.
* `hminus` satisfies `marchalQuartic hminus = lmfun hminus`, so it cannot lie
  in that interval; with `1.2 ≤ hminus` this gives `1.2313664 ≤ hminus`.

The real root is `1.231754422…`, so the bound has margin `3.9e-4`.
-/

namespace Kepler.NliHminus
open Kepler.Text

/-- On the left of the Marchal root the quartic stays strictly below the
linear cap: `marchalQuartic h < lmfun h` for `h ∈ [1.2, 1.2313664]`. -/
private theorem marchalQuartic_lt_lmfun {h : ℝ} (h1 : 1.2 ≤ h) (h2 : h ≤ 1.2313664) :
    marchalQuartic h < lmfun h := by
  -- rational enclosures of `√2`
  have hs_lo : (1.41421356 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs_hi : Real.sqrt 2 < 1.41421357 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  -- positivity of the pieces
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
    have hp2 : (0:ℝ) ≤ 1.2313664 - h := by linarith
    have hprod : (0:ℝ) ≤ (h - 1.2) * (1.2313664 - h) := mul_nonneg hp1 hp2
    nlinarith [hprod]
  have hE : (0:ℝ) < h0 - h := by rw [h0]; linarith
  have hE1 : (0:ℝ) < h0 - 1 := by rw [h0]; norm_num
  -- normal form of the quartic (the quadratic factor is negative on the interval)
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
  -- the quartic certificate: substitute `h = 1.2313664 - t`
  have hkey : (0:ℝ) < (h0 - h) * ((1.41421356 - 1) * 5 * (hplus - 1)) -
      (1.41421357 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) := by
    rw [show h0 = (1.26:ℝ) from rfl, show hplus = (1.3254:ℝ) from rfl]
    have ht0 : (0:ℝ) ≤ 1.2313664 - h := by linarith
    have htT : 1.2313664 - h ≤ 0.0313664 := by linarith
    have h2t : (1.2313664 - h) ^ 2 ≤ 0.0313664 * (1.2313664 - h) := by nlinarith
    have h3t : (1.2313664 - h) ^ 3 ≤ 0.0313664 ^ 2 * (1.2313664 - h) := by nlinarith
    have h4t : (0:ℝ) ≤ (1.2313664 - h) ^ 4 := by positivity
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

/-- W2-0: the five-digit Marchal envelope `1.2313664 ≤ hminus`. -/
theorem hminus_ge_12313664 : (1.2313664 : ℝ) ≤ hminus := by
  obtain ⟨h1, -, hspec⟩ := mi_hminus_prop
  by_contra hcon
  push_neg at hcon
  have hlt := marchalQuartic_lt_lmfun (h := hminus) h1 (le_of_lt hcon)
  rw [hspec] at hlt
  exact absurd hlt (lt_irrefl _)

/-- Consumed form of W2-0: `6.0650528 ≤ 4·hminus² = (2·hminus)²`
(the rational `x1 = y1²` lower edge of the critical `y1` slot). -/
theorem four_hminus_sq_ge : (6.0650528 : ℝ) ≤ 4 * hminus ^ 2 := by
  have h := hminus_ge_12313664
  have hpos : (0:ℝ) < hminus := by linarith
  nlinarith [sq_nonneg (hminus - 1.2313664)]

/-! ## `deltaX` positivity: the concavity kit

`deltaX` is concave in every variable (quadratic coefficient `−x_pair`), so its
box minimum sits at a rational corner; the 64 corners give `deltaX ≥ 100` on
the super-box.  Copied from `Kepler.NliBanks2` (`dX_concave_*`, same bodies). -/

theorem dX_concave_1 (x2 x3 x4 x5 x6 : ℝ) (hx4 : 0 < x4)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6) ≤
      deltaX t x2 x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX t x2 x3 x4 x5 x6 -
      (lam * deltaX a x2 x3 x4 x5 x6 + (1 - lam) * deltaX b x2 x3 x4 x5 x6)
      = x4 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hmin : min (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6) ≤
      lam * deltaX a x2 x3 x4 x5 x6 + (1 - lam) * deltaX b x2 x3 x4 x5 x6 := by
    have hl := min_le_left (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6)
    have hr := min_le_right (deltaX a x2 x3 x4 x5 x6) (deltaX b x2 x3 x4 x5 x6)
    nlinarith
  have hnn : (0:ℝ) ≤ x4 * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    positivity
  linarith

theorem dX_concave_2 (x1 x3 x4 x5 x6 : ℝ) (hx5 : 0 < x5)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6) ≤
      deltaX x1 t x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 t x3 x4 x5 x6 -
      (lam * deltaX x1 a x3 x4 x5 x6 + (1 - lam) * deltaX x1 b x3 x4 x5 x6)
      = x5 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hmin : min (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6) ≤
      lam * deltaX x1 a x3 x4 x5 x6 + (1 - lam) * deltaX x1 b x3 x4 x5 x6 := by
    have hl := min_le_left (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6)
    have hr := min_le_right (deltaX x1 a x3 x4 x5 x6) (deltaX x1 b x3 x4 x5 x6)
    nlinarith
  have hnn : (0:ℝ) ≤ x5 * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    positivity
  linarith

theorem dX_concave_3 (x1 x2 x4 x5 x6 : ℝ) (hx6 : 0 < x6)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6) ≤
      deltaX x1 x2 t x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 t x4 x5 x6 -
      (lam * deltaX x1 x2 a x4 x5 x6 + (1 - lam) * deltaX x1 x2 b x4 x5 x6)
      = x6 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hmin : min (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6) ≤
      lam * deltaX x1 x2 a x4 x5 x6 + (1 - lam) * deltaX x1 x2 b x4 x5 x6 := by
    have hl := min_le_left (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6)
    have hr := min_le_right (deltaX x1 x2 a x4 x5 x6) (deltaX x1 x2 b x4 x5 x6)
    nlinarith
  have hnn : (0:ℝ) ≤ x6 * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    positivity
  linarith

theorem dX_concave_4 (x1 x2 x3 x5 x6 : ℝ) (hx1 : 0 < x1)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6) ≤
      deltaX x1 x2 x3 t x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 x3 t x5 x6 -
      (lam * deltaX x1 x2 x3 a x5 x6 + (1 - lam) * deltaX x1 x2 x3 b x5 x6)
      = x1 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hmin : min (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6) ≤
      lam * deltaX x1 x2 x3 a x5 x6 + (1 - lam) * deltaX x1 x2 x3 b x5 x6 := by
    have hl := min_le_left (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6)
    have hr := min_le_right (deltaX x1 x2 x3 a x5 x6) (deltaX x1 x2 x3 b x5 x6)
    nlinarith
  have hnn : (0:ℝ) ≤ x1 * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    positivity
  linarith

theorem dX_concave_5 (x1 x2 x3 x4 x6 : ℝ) (hx2 : 0 < x2)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6) ≤
      deltaX x1 x2 x3 x4 t x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 x3 x4 t x6 -
      (lam * deltaX x1 x2 x3 x4 a x6 + (1 - lam) * deltaX x1 x2 x3 x4 b x6)
      = x2 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hmin : min (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6) ≤
      lam * deltaX x1 x2 x3 x4 a x6 + (1 - lam) * deltaX x1 x2 x3 x4 b x6 := by
    have hl := min_le_left (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6)
    have hr := min_le_right (deltaX x1 x2 x3 x4 a x6) (deltaX x1 x2 x3 x4 b x6)
    nlinarith
  have hnn : (0:ℝ) ≤ x2 * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    positivity
  linarith

theorem dX_concave_6 (x1 x2 x3 x4 x5 : ℝ) (hx3 : 0 < x3)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b) ≤
      deltaX x1 x2 x3 x4 x5 t := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : (0:ℝ) ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX x1 x2 x3 x4 x5 t -
      (lam * deltaX x1 x2 x3 x4 x5 a + (1 - lam) * deltaX x1 x2 x3 x4 x5 b)
      = x3 * (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX; ring
  have hmin : min (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b) ≤
      lam * deltaX x1 x2 x3 x4 x5 a + (1 - lam) * deltaX x1 x2 x3 x4 x5 b := by
    have hl := min_le_left (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b)
    have hr := min_le_right (deltaX x1 x2 x3 x4 x5 a) (deltaX x1 x2 x3 x4 x5 b)
    nlinarith
  have hnn : (0:ℝ) ≤ x3 * (t - a) * (b - t) := by
    have h1' : (0:ℝ) ≤ t - a := by linarith
    have h2' : (0:ℝ) ≤ b - t := by linarith
    positivity
  linarith

set_option maxHeartbeats 4000000 in
/-- `deltaX ≥ 100` on `[6.0650528, 7.02674064] × [4, 8] × [5.76, 8] × [4, 8]³`
(64 rational corners). -/
theorem dX_box_ge (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 6.0650528 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 5.76 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (100:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 6.0650528 x2 x3 x4 x5 x6) (deltaX 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 6.0650528 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 5.76 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])


#print axioms Kepler.NliHminus.hminus_ge_12313664
#print axioms Kepler.NliHminus.four_hminus_sq_ge

end Kepler.NliHminus
