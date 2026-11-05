import Kepler.Text.PackingAuto21

/-!
Kepler.NliBanks2 — W1 lane `nli-unknown-w1`: three `dih_y` bank bounds
(`BIXPCGW6652007036a2`: `dihY < 2.8`; `BIXPCGW7080972881a2` / `BIXPCGW1738910218a2`:
`dihY < 2.3`), all reduced to the same two boxes on `deltaX` / `deltaX4`.

Shape of the proof (no certificates, no `sorry`):
* `deltaX` is concave in every variable (quadratic coefficient `-x_pair`),
  so its box minimum is at a rational corner (`dX_box_ge_*`).
* `deltaX4` is linear in `x2 … x6` and concave in `x1`, so its box minimum
  is also at a corner (`d4_box_ge_*`).
* For `deltaY > 0` and the box bounds this pins `dihY`:
  `delta4Y ≥ 0` gives `dihY ≤ π/2`; `delta4Y < 0` goes through the
  `mi_lindihpi_lt_y` bridge with a rational `a`, whose polynomial side
  `a²·delta4Y² < 4·y1²·deltaY` follows from the two corner minima.
* The angle constants (`π − arctan(1/2) < 2.8`, `π − arctan(5/4) < 2.3`)
  are elementary rational/trig estimates; `π < 3.15` is Mathlib's
  `Real.pi_lt_d2`.
-/

namespace Kepler.NliBanks2
open Kepler.Text

/-! ## Serving kit 1: `deltaX` is concave in each variable
(copied verbatim from `Kepler.NliBanks`, the `nliRestBIXPCGWb` precedent). -/

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

/-! ## Serving kit 2: `deltaX4` has its box minimum at a corner
(`deltaX4` is concave in `x1` with leading coefficient `-1`, and linear in
`x2 … x6`; in both cases the minimum over an interval is at an endpoint). -/

private theorem d4_min_1 (x2 x3 x4 x5 x6 : ℝ)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX4 a x2 x3 x4 x5 x6) (deltaX4 b x2 x3 x4 x5 x6) ≤
      deltaX4 t x2 x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX4 t x2 x3 x4 x5 x6 -
      (lam * deltaX4 a x2 x3 x4 x5 x6 + (1 - lam) * deltaX4 b x2 x3 x4 x5 x6)
      = (t - a) * (b - t) := by
    rw [hlam]; field_simp; unfold deltaX4; ring
  have hnn : 0 ≤ (t - a) * (b - t) := by
    have h1' : 0 ≤ t - a := by linarith
    have h2' : 0 ≤ b - t := by linarith
    positivity
  have hmin : min (deltaX4 a x2 x3 x4 x5 x6) (deltaX4 b x2 x3 x4 x5 x6) ≤
      lam * deltaX4 a x2 x3 x4 x5 x6 + (1 - lam) * deltaX4 b x2 x3 x4 x5 x6 := by
    have hl := min_le_left (deltaX4 a x2 x3 x4 x5 x6) (deltaX4 b x2 x3 x4 x5 x6)
    have hr := min_le_right (deltaX4 a x2 x3 x4 x5 x6) (deltaX4 b x2 x3 x4 x5 x6)
    nlinarith
  linarith

private theorem d4_min_2 (x1 x3 x4 x5 x6 : ℝ)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX4 x1 a x3 x4 x5 x6) (deltaX4 x1 b x3 x4 x5 x6) ≤
      deltaX4 x1 t x3 x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX4 x1 t x3 x4 x5 x6 -
      (lam * deltaX4 x1 a x3 x4 x5 x6 + (1 - lam) * deltaX4 x1 b x3 x4 x5 x6) = 0 := by
    rw [hlam]; field_simp; unfold deltaX4; ring
  have hmin : min (deltaX4 x1 a x3 x4 x5 x6) (deltaX4 x1 b x3 x4 x5 x6) ≤
      lam * deltaX4 x1 a x3 x4 x5 x6 + (1 - lam) * deltaX4 x1 b x3 x4 x5 x6 := by
    have hl := min_le_left (deltaX4 x1 a x3 x4 x5 x6) (deltaX4 x1 b x3 x4 x5 x6)
    have hr := min_le_right (deltaX4 x1 a x3 x4 x5 x6) (deltaX4 x1 b x3 x4 x5 x6)
    nlinarith
  linarith

private theorem d4_min_3 (x1 x2 x4 x5 x6 : ℝ)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX4 x1 x2 a x4 x5 x6) (deltaX4 x1 x2 b x4 x5 x6) ≤
      deltaX4 x1 x2 t x4 x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX4 x1 x2 t x4 x5 x6 -
      (lam * deltaX4 x1 x2 a x4 x5 x6 + (1 - lam) * deltaX4 x1 x2 b x4 x5 x6) = 0 := by
    rw [hlam]; field_simp; unfold deltaX4; ring
  have hmin : min (deltaX4 x1 x2 a x4 x5 x6) (deltaX4 x1 x2 b x4 x5 x6) ≤
      lam * deltaX4 x1 x2 a x4 x5 x6 + (1 - lam) * deltaX4 x1 x2 b x4 x5 x6 := by
    have hl := min_le_left (deltaX4 x1 x2 a x4 x5 x6) (deltaX4 x1 x2 b x4 x5 x6)
    have hr := min_le_right (deltaX4 x1 x2 a x4 x5 x6) (deltaX4 x1 x2 b x4 x5 x6)
    nlinarith
  linarith

private theorem d4_min_4 (x1 x2 x3 x5 x6 : ℝ)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX4 x1 x2 x3 a x5 x6) (deltaX4 x1 x2 x3 b x5 x6) ≤
      deltaX4 x1 x2 x3 t x5 x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX4 x1 x2 x3 t x5 x6 -
      (lam * deltaX4 x1 x2 x3 a x5 x6 + (1 - lam) * deltaX4 x1 x2 x3 b x5 x6) = 0 := by
    rw [hlam]; field_simp; unfold deltaX4; ring
  have hmin : min (deltaX4 x1 x2 x3 a x5 x6) (deltaX4 x1 x2 x3 b x5 x6) ≤
      lam * deltaX4 x1 x2 x3 a x5 x6 + (1 - lam) * deltaX4 x1 x2 x3 b x5 x6 := by
    have hl := min_le_left (deltaX4 x1 x2 x3 a x5 x6) (deltaX4 x1 x2 x3 b x5 x6)
    have hr := min_le_right (deltaX4 x1 x2 x3 a x5 x6) (deltaX4 x1 x2 x3 b x5 x6)
    nlinarith
  linarith

private theorem d4_min_5 (x1 x2 x3 x4 x6 : ℝ)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX4 x1 x2 x3 x4 a x6) (deltaX4 x1 x2 x3 x4 b x6) ≤
      deltaX4 x1 x2 x3 x4 t x6 := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX4 x1 x2 x3 x4 t x6 -
      (lam * deltaX4 x1 x2 x3 x4 a x6 + (1 - lam) * deltaX4 x1 x2 x3 x4 b x6) = 0 := by
    rw [hlam]; field_simp; unfold deltaX4; ring
  have hmin : min (deltaX4 x1 x2 x3 x4 a x6) (deltaX4 x1 x2 x3 x4 b x6) ≤
      lam * deltaX4 x1 x2 x3 x4 a x6 + (1 - lam) * deltaX4 x1 x2 x3 x4 b x6 := by
    have hl := min_le_left (deltaX4 x1 x2 x3 x4 a x6) (deltaX4 x1 x2 x3 x4 b x6)
    have hr := min_le_right (deltaX4 x1 x2 x3 x4 a x6) (deltaX4 x1 x2 x3 x4 b x6)
    nlinarith
  linarith

private theorem d4_min_6 (x1 x2 x3 x4 x5 : ℝ)
    (a b t : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    min (deltaX4 x1 x2 x3 x4 x5 a) (deltaX4 x1 x2 x3 x4 x5 b) ≤
      deltaX4 x1 x2 x3 x4 x5 t := by
  set lam := (b - t) / (b - a) with hlam
  have hba : (0:ℝ) < b - a := by linarith
  have h0 : 0 ≤ lam := by rw [hlam]; positivity
  have h1 : lam ≤ 1 := by rw [hlam, div_le_one hba]; linarith
  have hkey : deltaX4 x1 x2 x3 x4 x5 t -
      (lam * deltaX4 x1 x2 x3 x4 x5 a + (1 - lam) * deltaX4 x1 x2 x3 x4 x5 b) = 0 := by
    rw [hlam]; field_simp; unfold deltaX4; ring
  have hmin : min (deltaX4 x1 x2 x3 x4 x5 a) (deltaX4 x1 x2 x3 x4 x5 b) ≤
      lam * deltaX4 x1 x2 x3 x4 x5 a + (1 - lam) * deltaX4 x1 x2 x3 x4 x5 b := by
    have hl := min_le_left (deltaX4 x1 x2 x3 x4 x5 a) (deltaX4 x1 x2 x3 x4 x5 b)
    have hr := min_le_right (deltaX4 x1 x2 x3 x4 x5 a) (deltaX4 x1 x2 x3 x4 x5 b)
    nlinarith
  linarith

/-! ## Box minima (64 rational corners each) -/

set_option maxHeartbeats 4000000 in
/-- `[5.76, 7.02674064]×[4,8]⁵` corner minimum of `deltaX`: `54`. -/
private theorem dX_box_ge_b1 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (54:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 5.76 x2 x3 x4 x5 x6) (deltaX 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 5.76 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

set_option maxHeartbeats 4000000 in
/-- `[5.76, 7.02674064]×[5.76,8]×[4,8]⁴` corner minimum of `deltaX`: `100`. -/
private theorem dX_box_ge_b3 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 5.76 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (100:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 5.76 x2 x3 x4 x5 x6) (deltaX 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 5.76 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 5.76 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

set_option maxHeartbeats 4000000 in
/-- `[5.76, 7.02674064]×[4,8]²×[4,7.02674064]×[4,8]²` corner minimum of
`deltaX`: `96`. -/
private theorem dX_box_ge_b5 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 7.02674064)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (96:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 5.76 x2 x3 x4 x5 x6) (deltaX 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 5.76 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 7.02674064 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

set_option maxHeartbeats 4000000 in
/-- `[5.76, 7.02674064]×[4,8]⁵` corner minimum of `deltaX4`: `-49.4`. -/
private theorem d4_box_ge_b1 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (-49.4:ℝ) ≤ deltaX4 x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX4 5.76 x2 x3 x4 x5 x6) (deltaX4 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX4 x1 x2 x3 x4 x5 x6 :=
    d4_min_1 x2 x3 x4 x5 x6 5.76 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (d4_min_2 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_3 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_4 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_5 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_6 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX4])

set_option maxHeartbeats 4000000 in
/-- `[5.76, 7.02674064]×[5.76,8]×[4,8]⁴` corner minimum of `deltaX4`: `-37.1`. -/
private theorem d4_box_ge_b3 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 5.76 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (-37.1:ℝ) ≤ deltaX4 x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX4 5.76 x2 x3 x4 x5 x6) (deltaX4 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX4 x1 x2 x3 x4 x5 x6 :=
    d4_min_1 x2 x3 x4 x5 x6 5.76 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (d4_min_2 _ _ _ _ _ 5.76 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_3 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_4 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_5 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_6 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX4])

set_option maxHeartbeats 4000000 in
/-- `[5.76, 7.02674064]×[4,8]²×[4,7.02674064]×[4,8]²` corner minimum of
`deltaX4`: `-35.7`. -/
private theorem d4_box_ge_b5 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 5.76 ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 7.02674064)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (-35.7:ℝ) ≤ deltaX4 x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX4 5.76 x2 x3 x4 x5 x6) (deltaX4 7.02674064 x2 x3 x4 x5 x6)
      ≤ deltaX4 x1 x2 x3 x4 x5 x6 :=
    d4_min_1 x2 x3 x4 x5 x6 5.76 7.02674064 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (d4_min_2 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_3 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_4 _ _ _ _ _ 4 7.02674064 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_5 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (d4_min_6 _ _ _ _ _ 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX4])

set_option maxHeartbeats 4000000 in
/-- `[7.02674064,8]²×[4,8]⁴` corner minimum of `deltaX`: `157`. -/
private theorem dX_box_ge_bT (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 7.02674064 ≤ x1) (h1h : x1 ≤ 8)
    (h2l : 7.02674064 ≤ x2) (h2h : x2 ≤ 8)
    (h3l : 4 ≤ x3) (h3h : x3 ≤ 8)
    (h4l : 4 ≤ x4) (h4h : x4 ≤ 8)
    (h5l : 4 ≤ x5) (h5h : x5 ≤ 8)
    (h6l : 4 ≤ x6) (h6h : x6 ≤ 8) :
    (157:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := by
  have e1 : min (deltaX 7.02674064 x2 x3 x4 x5 x6) (deltaX 8 x2 x3 x4 x5 x6)
      ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    dX_concave_1 x2 x3 x4 x5 x6 (by linarith) 7.02674064 8 x1 h1l h1h (by norm_num)
  refine le_trans ?_ e1
  refine le_min ?_ ?_
  all_goals (refine le_trans ?_ (dX_concave_2 _ _ _ _ _ (by linarith) 7.02674064 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_3 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_4 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_5 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (refine le_trans ?_ (dX_concave_6 _ _ _ _ _ (by linarith) 4 8 _ (by linarith) (by linarith) (by norm_num)))
  all_goals (refine le_min ?_ ?_)
  all_goals (norm_num [deltaX])

/-! ## `atn2` sign lemmas -/

private theorem atn2_le_zero (a b : ℝ) (ha : 0 < a) (hb : b ≤ 0) : atn2 a b ≤ 0 := by
  rw [atn2]
  split_ifs with h1 h2 h3
  · exact Real.arctan_le_zero.mpr (div_nonpos_of_nonpos_of_nonneg hb ha.le)
  · linarith
  · have := Real.neg_pi_div_two_lt_arctan (a / b)
    linarith
  · have hb0 : b = 0 := by linarith
    rw [hb0, abs_zero] at h1
    linarith

private theorem atn2_nonneg (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ atn2 a b := by
  rw [atn2]
  split_ifs with h1 h2 h3
  · exact Real.arctan_nonneg.mpr (div_nonneg hb ha.le)
  · have hlt := Real.arctan_lt_pi_div_two (a / b)
    linarith
  · linarith
  · have : |b| < a := by rw [show b = 0 by linarith, abs_zero]; exact ha
    linarith

/-- `deltaX4 ≥ 0` forces `dihXf ≤ π/2`. -/
private theorem dihXf_le_pi_div_two {x1 x2 x3 x4 x5 x6 : ℝ} (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hd4 : 0 ≤ deltaX4 x1 x2 x3 x4 x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 ≤ Real.pi / 2 := by
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  have hkey := atn2_le_zero _ _ hA (by linarith : -(deltaX4 x1 x2 x3 x4 x5 x6) ≤ 0)
  unfold dihXf
  linarith

/-- `deltaX4 ≤ 0` forces `π/2 ≤ dihXf`. -/
private theorem le_pi_div_two_dihXf {x1 x2 x3 x4 x5 x6 : ℝ} (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hd4 : deltaX4 x1 x2 x3 x4 x5 x6 ≤ 0) :
    Real.pi / 2 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  have hA : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  have hkey := atn2_nonneg _ _ hA (by linarith : -(deltaX4 x1 x2 x3 x4 x5 x6) ≥ 0)
  unfold dihXf
  linarith

/-! ## Angle constants -/

/-- `tan (0.35) < 1/2` (crude `sin x < x`, `cos x ≥ 1 − x²/2`). -/
private theorem tan_035_lt_half : Real.tan (0.35:ℝ) < 1/2 := by
  have hsin : Real.sin (0.35:ℝ) < 0.35 := Real.sin_lt (by norm_num)
  have hcos : (0.93875:ℝ) ≤ Real.cos 0.35 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (0.35:ℝ))
    norm_num at h
    linarith
  have hcospos : (0:ℝ) < Real.cos 0.35 := by linarith
  rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcospos]
  nlinarith

/-- `π − 2.8 < arctan (1/2)`. -/
private theorem pi_sub_2_8_lt_arctan_half : Real.pi - 2.8 < Real.arctan (1/2) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have h1 : Real.pi - 2.8 < 0.35 := by linarith
  have h2 : (0.35:ℝ) < Real.arctan (1/2) := by
    have hmem1 : (0.35:ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_gt_d2], by linarith [Real.pi_gt_d2]⟩
    have hmono := Real.strictMonoOn_tan.lt_iff_lt hmem1 (Real.arctan_mem_Ioo (1/2))
    rw [Real.tan_arctan] at hmono
    exact hmono.mp tan_035_lt_half
  linarith

/-- `tan (0.11) < 1/9` (crude `sin x < x`, `cos x ≥ 1 − x²/2`). -/
private theorem tan_011_lt_inv9 : Real.tan (0.11:ℝ) < 1/9 := by
  have hsin : Real.sin (0.11:ℝ) < 0.11 := Real.sin_lt (by norm_num)
  have hcos : (0.99395:ℝ) ≤ Real.cos 0.11 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (0.11:ℝ))
    norm_num at h
    linarith
  have hcospos : (0:ℝ) < Real.cos 0.11 := by linarith
  rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcospos]
  norm_num
  nlinarith

/-- `arctan (1/9) > 0.11`. -/
private theorem arctan_inv9_gt_011 : (0.11:ℝ) < Real.arctan (1/9) := by
  have hmem1 : (0.11:ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_gt_d2], by linarith [Real.pi_gt_d2]⟩
  have hmono := Real.strictMonoOn_tan.lt_iff_lt hmem1 (Real.arctan_mem_Ioo (1/9))
  rw [Real.tan_arctan] at hmono
  exact hmono.mp tan_011_lt_inv9

/-- `π − 2.3 < arctan (5/4)`, via `arctan (5/4) = π/4 + arctan (1/9)`. -/
private theorem pi_sub_2_3_lt_arctan_five_quarters :
    Real.pi - 2.3 < Real.arctan (5/4) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi4 : (0.785:ℝ) < Real.pi / 4 := by linarith [Real.pi_gt_d2]
  have hadd : Real.arctan (5/4) = Real.pi / 4 + Real.arctan (1/9) := by
    have h := Real.arctan_add (x := (1:ℝ)) (y := (1/9)) (by norm_num)
    have h5 : ((1:ℝ) + 1/9) / (1 - 1 * (1/9)) = 5/4 := by norm_num
    rw [h5, Real.arctan_one] at h
    exact h.symm
  have h9 := arctan_inv9_gt_011
  have h1 : Real.pi - 2.3 < 0.85 := by linarith
  have h2 : (0.85:ℝ) < Real.arctan (5/4) := by
    rw [hadd]
    linarith
  linarith

/-! ## The polynomial step shared by the three banks -/

/-- From `-K ≤ d4 < 0`, `x1m ≤ x1`, `dm ≤ d` and the rational constant
inequality `a²K² < 4·x1m·dm`, conclude `a²·d4² < 4·(x1·d)`. -/
private theorem poly_step {a K x1m dm x1 d d4 : ℝ}
    (hK : -K ≤ d4) (hd4 : d4 < 0) (hx1 : x1m ≤ x1) (hd : dm ≤ d)
    (hdmnn : 0 ≤ dm) (hx1nn : 0 ≤ x1) (hconst : a ^ 2 * K ^ 2 < 4 * (x1m * dm)) :
    a ^ 2 * d4 ^ 2 < 4 * (x1 * d) := by
  have hK2 : d4 ^ 2 ≤ K ^ 2 := by nlinarith
  have ha2 : (0:ℝ) ≤ a ^ 2 := sq_nonneg a
  have h1 : a ^ 2 * d4 ^ 2 ≤ a ^ 2 * K ^ 2 := by nlinarith
  have h2 : x1m * dm ≤ x1 * d := mul_le_mul hx1 hd hdmnn hx1nn
  linarith

/-! ## The three `dihY` banks -/

set_option maxHeartbeats 4000000 in
/-- rest 36: HOL ineq `BIXPCGW 6652007036 a2` (ineq.hl:701).  Box
`[2hmin,2hplus]×[2,√8]⁵`: `dihY < 2.8`. -/
theorem nliBIXPCGW6652007036a2 : bank_BIXPCGW6652007036a2 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hp : hplus = 1.3254 := rfl
  have hm : (1.2:ℝ) ≤ hminus := mi_hminus_prop.1
  have x1l : (5.76:ℝ) ≤ y1 * y1 := by nlinarith
  have x1h : y1 * y1 ≤ 7.02674064 := by rw [hp] at h1h; nlinarith
  have x2l : (4:ℝ) ≤ y2 * y2 := by nlinarith
  have x2h : y2 * y2 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x3l : (4:ℝ) ≤ y3 * y3 := by nlinarith
  have x3h : y3 * y3 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x4l : (4:ℝ) ≤ y4 * y4 := by nlinarith
  have x4h : y4 * y4 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x5l : (4:ℝ) ≤ y5 * y5 := by nlinarith
  have x5h : y5 * y5 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x6l : (4:ℝ) ≤ y6 * y6 := by nlinarith
  have x6h : y6 * y6 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have hd : (54:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge_b1 _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hd4 : (-49.4:ℝ) ≤ deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    d4_box_ge_b1 _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hdy : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by unfold deltaY; linarith
  by_cases hneg : delta4Y y1 y2 y3 y4 y5 y6 < 0
  · have hneg' : deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) < 0 := by
      unfold delta4Y yOfX at hneg
      exact hneg
    have hmain : (1/2:ℝ)^2 * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))^2
        < 4 * ((y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) :=
      poly_step (a := 1/2) (K := 49.4) (x1m := 5.76) (dm := 54)
        (x1 := y1*y1) (d := deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
        (d4 := deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
        hd4 hneg' x1l hd (by norm_num) (by nlinarith) (by norm_num)
    have hsq : (1/2:ℝ)^2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6
        < 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 := by
      unfold yOfX delta4SquaredX x1DeltaX
      exact hmain
    have hlt := (mi_lindihpi_lt_y (a := (1/2:ℝ)) (y1 := y1) (y2 := y2) (y3 := y3)
      (y4 := y4) (y5 := y5) (y6 := y6) (by linarith) (by norm_num) hdy hneg).mpr hsq
    have hpi := pi_sub_2_8_lt_arctan_half
    linarith
  · have hneg0 : (0:ℝ) ≤ delta4Y y1 y2 y3 y4 y5 y6 := le_of_not_gt hneg
    have hle : dihY y1 y2 y3 y4 y5 y6 ≤ Real.pi / 2 := by
      unfold dihY
      exact dihXf_le_pi_div_two (by nlinarith) (by unfold deltaY at hdy; exact hdy)
        (by unfold delta4Y yOfX at hneg0; exact hneg0)
    have hpi : Real.pi / 2 < 2.8 := by linarith [Real.pi_lt_d2]
    linarith

set_option maxHeartbeats 4000000 in
/-- rest 35: HOL ineq `BIXPCGW 7080972881 a2` (ineq.hl:721).  Box
`[2hmin,2hplus]×[2hmin,√8]×[2,√8]⁴`: `dihY < 2.3`. -/
theorem nliBIXPCGW7080972881a2 : bank_BIXPCGW7080972881a2 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hp : hplus = 1.3254 := rfl
  have hm : (1.2:ℝ) ≤ hminus := mi_hminus_prop.1
  have x1l : (5.76:ℝ) ≤ y1 * y1 := by nlinarith
  have x1h : y1 * y1 ≤ 7.02674064 := by rw [hp] at h1h; nlinarith
  have x2l : (5.76:ℝ) ≤ y2 * y2 := by nlinarith
  have x2h : y2 * y2 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x3l : (4:ℝ) ≤ y3 * y3 := by nlinarith
  have x3h : y3 * y3 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x4l : (4:ℝ) ≤ y4 * y4 := by nlinarith
  have x4h : y4 * y4 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x5l : (4:ℝ) ≤ y5 * y5 := by nlinarith
  have x5h : y5 * y5 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x6l : (4:ℝ) ≤ y6 * y6 := by nlinarith
  have x6h : y6 * y6 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have hd : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge_b3 _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hd4 : (-37.1:ℝ) ≤ deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    d4_box_ge_b3 _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hdy : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by unfold deltaY; linarith
  by_cases hneg : delta4Y y1 y2 y3 y4 y5 y6 < 0
  · have hneg' : deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) < 0 := by
      unfold delta4Y yOfX at hneg
      exact hneg
    have hmain : (5/4:ℝ)^2 * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))^2
        < 4 * ((y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) :=
      poly_step (a := 5/4) (K := 37.1) (x1m := 5.76) (dm := 100)
        (x1 := y1*y1) (d := deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
        (d4 := deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
        hd4 hneg' x1l hd (by norm_num) (by nlinarith) (by norm_num)
    have hsq : (5/4:ℝ)^2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6
        < 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 := by
      unfold yOfX delta4SquaredX x1DeltaX
      exact hmain
    have hlt := (mi_lindihpi_lt_y (a := (5/4:ℝ)) (y1 := y1) (y2 := y2) (y3 := y3)
      (y4 := y4) (y5 := y5) (y6 := y6) (by linarith) (by norm_num) hdy hneg).mpr hsq
    have hpi := pi_sub_2_3_lt_arctan_five_quarters
    linarith
  · have hneg0 : (0:ℝ) ≤ delta4Y y1 y2 y3 y4 y5 y6 := le_of_not_gt hneg
    have hle : dihY y1 y2 y3 y4 y5 y6 ≤ Real.pi / 2 := by
      unfold dihY
      exact dihXf_le_pi_div_two (by nlinarith) (by unfold deltaY at hdy; exact hdy)
        (by unfold delta4Y yOfX at hneg0; exact hneg0)
    have hpi : Real.pi / 2 < 2.3 := by linarith [Real.pi_lt_d2]
    linarith

set_option maxHeartbeats 4000000 in
/-- rest 34: HOL ineq `BIXPCGW 1738910218 a2` (ineq.hl:739).  Box
`[2hmin,2hplus]×[2,√8]²×[2,2hplus]×[2,√8]²`: `dihY < 2.3`. -/
theorem nliBIXPCGW1738910218a2 : bank_BIXPCGW1738910218a2 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hp : hplus = 1.3254 := rfl
  have hm : (1.2:ℝ) ≤ hminus := mi_hminus_prop.1
  have x1l : (5.76:ℝ) ≤ y1 * y1 := by nlinarith
  have x1h : y1 * y1 ≤ 7.02674064 := by rw [hp] at h1h; nlinarith
  have x2l : (4:ℝ) ≤ y2 * y2 := by nlinarith
  have x2h : y2 * y2 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x3l : (4:ℝ) ≤ y3 * y3 := by nlinarith
  have x3h : y3 * y3 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x4l : (4:ℝ) ≤ y4 * y4 := by nlinarith
  have x4h : y4 * y4 ≤ 7.02674064 := by rw [hp] at h4h; nlinarith
  have x5l : (4:ℝ) ≤ y5 * y5 := by nlinarith
  have x5h : y5 * y5 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x6l : (4:ℝ) ≤ y6 * y6 := by nlinarith
  have x6h : y6 * y6 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have hd : (96:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge_b5 _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hd4 : (-35.7:ℝ) ≤ deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    d4_box_ge_b5 _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hdy : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by unfold deltaY; linarith
  by_cases hneg : delta4Y y1 y2 y3 y4 y5 y6 < 0
  · have hneg' : deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) < 0 := by
      unfold delta4Y yOfX at hneg
      exact hneg
    have hmain : (5/4:ℝ)^2 * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))^2
        < 4 * ((y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) :=
      poly_step (a := 5/4) (K := 35.7) (x1m := 5.76) (dm := 96)
        (x1 := y1*y1) (d := deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
        (d4 := deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
        hd4 hneg' x1l hd (by norm_num) (by nlinarith) (by norm_num)
    have hsq : (5/4:ℝ)^2 * yOfX delta4SquaredX y1 y2 y3 y4 y5 y6
        < 4 * yOfX x1DeltaX y1 y2 y3 y4 y5 y6 := by
      unfold yOfX delta4SquaredX x1DeltaX
      exact hmain
    have hlt := (mi_lindihpi_lt_y (a := (5/4:ℝ)) (y1 := y1) (y2 := y2) (y3 := y3)
      (y4 := y4) (y5 := y5) (y6 := y6) (by linarith) (by norm_num) hdy hneg).mpr hsq
    have hpi := pi_sub_2_3_lt_arctan_five_quarters
    linarith
  · have hneg0 : (0:ℝ) ≤ delta4Y y1 y2 y3 y4 y5 y6 := le_of_not_gt hneg
    have hle : dihY y1 y2 y3 y4 y5 y6 ≤ Real.pi / 2 := by
      unfold dihY
      exact dihXf_le_pi_div_two (by nlinarith) (by unfold deltaY at hdy; exact hdy)
        (by unfold delta4Y yOfX at hneg0; exact hneg0)
    have hpi : Real.pi / 2 < 2.3 := by linarith [Real.pi_lt_d2]
    linarith


set_option maxHeartbeats 4000000

private theorem H_mono_1 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2) (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6) (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    rhoX 7.02674064 x2 x3 x4 x5 x6 - 8 * deltaX 7.02674064 x2 x3 x4 x5 x6 ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : (rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6) - (rhoX 7.02674064 x2 x3 x4 x5 x6 - 8 * deltaX 7.02674064 x2 x3 x4 x5 x6)
      = (x1 - 7.02674064) * ((2 * 7.02674064 - 8) * (16 - (x4 - 4) ^ 2) + 4 * (2 * 7.02674064 - 8) * (x6 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x5 - 4)) + 8 * ((x3 - 4) * (x5 - 4)) + 2 * ((x3 - 4) * (x4 - 4) * (x6 - 4)) + 8 * ((x2 - 7.02674064) * (x6 - 4)) + 2 * ((x2 - 7.02674064) * (x4 - 4) * (x5 - 4))) + (x4 * (8 - x4)) * (x1 - 7.02674064) ^ 2 := by
    unfold rhoX deltaX; ring
  have hA : (0:ℝ) ≤ x4 * (8 - x4) := by nlinarith
  have hG : (0:ℝ) ≤ (2 * 7.02674064 - 8) * (16 - (x4 - 4) ^ 2) + 4 * (2 * 7.02674064 - 8) * (x6 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x5 - 4)) + 8 * ((x3 - 4) * (x5 - 4)) + 2 * ((x3 - 4) * (x4 - 4) * (x6 - 4)) + 8 * ((x2 - 7.02674064) * (x6 - 4)) + 2 * ((x2 - 7.02674064) * (x4 - 4) * (x5 - 4)) := by
    have hCpos : (0:ℝ) < 2 * 7.02674064 - 8 := by norm_num
    have hDpos : (0:ℝ) < (7.02674064 - 4) * (2 * 7.02674064 - 8) := by norm_num
    have hu1 : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
    have hu2 : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
    have hu3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have hu4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have hu5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have hu6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have h16 : (0:ℝ) ≤ 16 - (x4 - 4) ^ 2 := by nlinarith
    have h16' : (0:ℝ) ≤ 16 - (x5 - 4) ^ 2 := by nlinarith
    nlinarith [      mul_nonneg hCpos.le h16, mul_nonneg hCpos.le h16',
      mul_nonneg (mul_nonneg hCpos.le hu6) (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (mul_nonneg hCpos.le hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu4) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu2) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu4) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu5) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu3) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu3,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu2,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu5) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu4) hu6,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu5,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu4,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu2) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu1) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu4) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu3) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu5) (by norm_num : (0:ℝ) ≤ 1)]
  have hstep : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
  have hprod : (0:ℝ) ≤ (x1 - 7.02674064) * ((2 * 7.02674064 - 8) * (16 - (x4 - 4) ^ 2) + 4 * (2 * 7.02674064 - 8) * (x6 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x5 - 4)) + 8 * ((x3 - 4) * (x5 - 4)) + 2 * ((x3 - 4) * (x4 - 4) * (x6 - 4)) + 8 * ((x2 - 7.02674064) * (x6 - 4)) + 2 * ((x2 - 7.02674064) * (x4 - 4) * (x5 - 4))) := mul_nonneg hstep hG
  have hsq : (0:ℝ) ≤ (x4 * (8 - x4)) * (x1 - 7.02674064) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  linarith

private theorem H_mono_2 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2) (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6) (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    rhoX x1 7.02674064 x3 x4 x5 x6 - 8 * deltaX x1 7.02674064 x3 x4 x5 x6 ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : (rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6) - (rhoX x1 7.02674064 x3 x4 x5 x6 - 8 * deltaX x1 7.02674064 x3 x4 x5 x6)
      = (x2 - 7.02674064) * ((2 * 7.02674064 - 8) * (16 - (x5 - 4) ^ 2) + 4 * (2 * 7.02674064 - 8) * (x6 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x5 - 4)) + 2 * ((x3 - 4) * (x5 - 4) * (x6 - 4)) + 8 * ((x3 - 4) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x6 - 4)) + 2 * ((x1 - 7.02674064) * (x4 - 4) * (x5 - 4))) + (x5 * (8 - x5)) * (x2 - 7.02674064) ^ 2 := by
    unfold rhoX deltaX; ring
  have hA : (0:ℝ) ≤ x5 * (8 - x5) := by nlinarith
  have hG : (0:ℝ) ≤ (2 * 7.02674064 - 8) * (16 - (x5 - 4) ^ 2) + 4 * (2 * 7.02674064 - 8) * (x6 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x5 - 4)) + 2 * ((x3 - 4) * (x5 - 4) * (x6 - 4)) + 8 * ((x3 - 4) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x6 - 4)) + 2 * ((x1 - 7.02674064) * (x4 - 4) * (x5 - 4)) := by
    have hCpos : (0:ℝ) < 2 * 7.02674064 - 8 := by norm_num
    have hDpos : (0:ℝ) < (7.02674064 - 4) * (2 * 7.02674064 - 8) := by norm_num
    have hu1 : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
    have hu2 : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
    have hu3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have hu4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have hu5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have hu6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have h16 : (0:ℝ) ≤ 16 - (x4 - 4) ^ 2 := by nlinarith
    have h16' : (0:ℝ) ≤ 16 - (x5 - 4) ^ 2 := by nlinarith
    nlinarith [      mul_nonneg hCpos.le h16, mul_nonneg hCpos.le h16',
      mul_nonneg (mul_nonneg hCpos.le hu6) (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (mul_nonneg hCpos.le hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu4) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu2) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu4) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu5) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu3) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu3,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu2,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu5) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu4) hu6,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu5,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu4,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu2) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu1) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu4) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu3) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu5) (by norm_num : (0:ℝ) ≤ 1)]
  have hstep : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
  have hprod : (0:ℝ) ≤ (x2 - 7.02674064) * ((2 * 7.02674064 - 8) * (16 - (x5 - 4) ^ 2) + 4 * (2 * 7.02674064 - 8) * (x6 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x5 - 4)) + 2 * ((x3 - 4) * (x5 - 4) * (x6 - 4)) + 8 * ((x3 - 4) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x6 - 4)) + 2 * ((x1 - 7.02674064) * (x4 - 4) * (x5 - 4))) := mul_nonneg hstep hG
  have hsq : (0:ℝ) ≤ (x5 * (8 - x5)) * (x2 - 7.02674064) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  linarith

private theorem H_mono_3 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2) (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6) (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    rhoX x1 x2 4 x4 x5 x6 - 8 * deltaX x1 x2 4 x4 x5 x6 ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : (rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6) - (rhoX x1 x2 4 x4 x5 x6 - 8 * deltaX x1 x2 4 x4 x5 x6)
      = (x3 - 4) * (4 * (2 * 7.02674064 - 8) * (x5 - 4) + (2 * 7.02674064 - 8) * ((x5 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x4 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x6 - 4)) + 2 * ((x2 - 7.02674064) * (x5 - 4) * (x6 - 4)) + 8 * ((x2 - 7.02674064) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x5 - 4)) + 2 * ((x1 - 7.02674064) * (x4 - 4) * (x6 - 4))) + (x6 * (8 - x6)) * (x3 - 4) ^ 2 := by
    unfold rhoX deltaX; ring
  have hA : (0:ℝ) ≤ x6 * (8 - x6) := by nlinarith
  have hG : (0:ℝ) ≤ 4 * (2 * 7.02674064 - 8) * (x5 - 4) + (2 * 7.02674064 - 8) * ((x5 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x4 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x6 - 4)) + 2 * ((x2 - 7.02674064) * (x5 - 4) * (x6 - 4)) + 8 * ((x2 - 7.02674064) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x5 - 4)) + 2 * ((x1 - 7.02674064) * (x4 - 4) * (x6 - 4)) := by
    have hCpos : (0:ℝ) < 2 * 7.02674064 - 8 := by norm_num
    have hDpos : (0:ℝ) < (7.02674064 - 4) * (2 * 7.02674064 - 8) := by norm_num
    have hu1 : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
    have hu2 : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
    have hu3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have hu4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have hu5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have hu6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have h16 : (0:ℝ) ≤ 16 - (x4 - 4) ^ 2 := by nlinarith
    have h16' : (0:ℝ) ≤ 16 - (x5 - 4) ^ 2 := by nlinarith
    nlinarith [      mul_nonneg hCpos.le h16, mul_nonneg hCpos.le h16',
      mul_nonneg (mul_nonneg hCpos.le hu6) (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (mul_nonneg hCpos.le hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu4) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu2) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu4) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu5) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu3) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu3,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu2,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu5) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu4) hu6,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu5,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu4,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu2) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu1) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu4) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu3) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu5) (by norm_num : (0:ℝ) ≤ 1)]
  have hstep : (0:ℝ) ≤ x3 - 4 := by linarith
  have hprod : (0:ℝ) ≤ (x3 - 4) * (4 * (2 * 7.02674064 - 8) * (x5 - 4) + (2 * 7.02674064 - 8) * ((x5 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x4 - 4) + (2 * 7.02674064 - 8) * ((x4 - 4) * (x6 - 4)) + 2 * ((x2 - 7.02674064) * (x5 - 4) * (x6 - 4)) + 8 * ((x2 - 7.02674064) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x5 - 4)) + 2 * ((x1 - 7.02674064) * (x4 - 4) * (x6 - 4))) := mul_nonneg hstep hG
  have hsq : (0:ℝ) ≤ (x6 * (8 - x6)) * (x3 - 4) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  linarith

private theorem H_mono_4 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2) (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6) (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 4 x5 x6 - 8 * deltaX x1 x2 x3 4 x5 x6 ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : (rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6) - (rhoX x1 x2 x3 4 x5 x6 - 8 * deltaX x1 x2 x3 4 x5 x6)
      = (x4 - 4) * (((7.02674064 - 4) * (2 * 7.02674064 - 8)) * (x5 - 4) + 8 * ((x5 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x3 - 4) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x2 - 7.02674064) * (x5 - 4)) + 8 * ((x2 - 7.02674064) * (x3 - 4)) + (2 * 7.02674064 - 8) * ((x1 - 7.02674064) * (x5 - 4)) + 2 * ((x1 - 7.02674064) * (x3 - 4) * (x6 - 4)) + 2 * ((x1 - 7.02674064) * (x2 - 7.02674064) * (x5 - 4))) + (x1 * (8 - x1)) * (x4 - 4) ^ 2 := by
    unfold rhoX deltaX; ring
  have hA : (0:ℝ) ≤ x1 * (8 - x1) := by nlinarith
  have hG : (0:ℝ) ≤ ((7.02674064 - 4) * (2 * 7.02674064 - 8)) * (x5 - 4) + 8 * ((x5 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x3 - 4) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x2 - 7.02674064) * (x5 - 4)) + 8 * ((x2 - 7.02674064) * (x3 - 4)) + (2 * 7.02674064 - 8) * ((x1 - 7.02674064) * (x5 - 4)) + 2 * ((x1 - 7.02674064) * (x3 - 4) * (x6 - 4)) + 2 * ((x1 - 7.02674064) * (x2 - 7.02674064) * (x5 - 4)) := by
    have hCpos : (0:ℝ) < 2 * 7.02674064 - 8 := by norm_num
    have hDpos : (0:ℝ) < (7.02674064 - 4) * (2 * 7.02674064 - 8) := by norm_num
    have hu1 : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
    have hu2 : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
    have hu3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have hu4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have hu5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have hu6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have h16 : (0:ℝ) ≤ 16 - (x4 - 4) ^ 2 := by nlinarith
    have h16' : (0:ℝ) ≤ 16 - (x5 - 4) ^ 2 := by nlinarith
    nlinarith [      mul_nonneg hCpos.le h16, mul_nonneg hCpos.le h16',
      mul_nonneg (mul_nonneg hCpos.le hu6) (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (mul_nonneg hCpos.le hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu4) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu2) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu4) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu5) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu3) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu3,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu2,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu5) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu4) hu6,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu5,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu4,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu2) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu1) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu4) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu3) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu5) (by norm_num : (0:ℝ) ≤ 1)]
  have hstep : (0:ℝ) ≤ x4 - 4 := by linarith
  have hprod : (0:ℝ) ≤ (x4 - 4) * (((7.02674064 - 4) * (2 * 7.02674064 - 8)) * (x5 - 4) + 8 * ((x5 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x3 - 4) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x2 - 7.02674064) * (x5 - 4)) + 8 * ((x2 - 7.02674064) * (x3 - 4)) + (2 * 7.02674064 - 8) * ((x1 - 7.02674064) * (x5 - 4)) + 2 * ((x1 - 7.02674064) * (x3 - 4) * (x6 - 4)) + 2 * ((x1 - 7.02674064) * (x2 - 7.02674064) * (x5 - 4))) := mul_nonneg hstep hG
  have hsq : (0:ℝ) ≤ (x1 * (8 - x1)) * (x4 - 4) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  linarith

private theorem H_mono_5 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2) (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6) (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 x4 4 x6 - 8 * deltaX x1 x2 x3 x4 4 x6 ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : (rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6) - (rhoX x1 x2 x3 x4 4 x6 - 8 * deltaX x1 x2 x3 x4 4 x6)
      = (x5 - 4) * (((7.02674064 - 4) * (2 * 7.02674064 - 8)) * (x4 - 4) + 8 * ((x4 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x3 - 4) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x2 - 7.02674064) * (x4 - 4)) + 2 * ((x2 - 7.02674064) * (x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x1 - 7.02674064) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x3 - 4)) + 2 * ((x1 - 7.02674064) * (x2 - 7.02674064) * (x4 - 4))) + (x2 * (8 - x2)) * (x5 - 4) ^ 2 := by
    unfold rhoX deltaX; ring
  have hA : (0:ℝ) ≤ x2 * (8 - x2) := by nlinarith
  have hG : (0:ℝ) ≤ ((7.02674064 - 4) * (2 * 7.02674064 - 8)) * (x4 - 4) + 8 * ((x4 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x3 - 4) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x2 - 7.02674064) * (x4 - 4)) + 2 * ((x2 - 7.02674064) * (x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x1 - 7.02674064) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x3 - 4)) + 2 * ((x1 - 7.02674064) * (x2 - 7.02674064) * (x4 - 4)) := by
    have hCpos : (0:ℝ) < 2 * 7.02674064 - 8 := by norm_num
    have hDpos : (0:ℝ) < (7.02674064 - 4) * (2 * 7.02674064 - 8) := by norm_num
    have hu1 : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
    have hu2 : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
    have hu3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have hu4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have hu5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have hu6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have h16 : (0:ℝ) ≤ 16 - (x4 - 4) ^ 2 := by nlinarith
    have h16' : (0:ℝ) ≤ 16 - (x5 - 4) ^ 2 := by nlinarith
    nlinarith [      mul_nonneg hCpos.le h16, mul_nonneg hCpos.le h16',
      mul_nonneg (mul_nonneg hCpos.le hu6) (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (mul_nonneg hCpos.le hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu4) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu2) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu4) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu5) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu3) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu3,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu2,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu5) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu4) hu6,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu5,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu4,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu2) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu1) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu4) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu3) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu5) (by norm_num : (0:ℝ) ≤ 1)]
  have hstep : (0:ℝ) ≤ x5 - 4 := by linarith
  have hprod : (0:ℝ) ≤ (x5 - 4) * (((7.02674064 - 4) * (2 * 7.02674064 - 8)) * (x4 - 4) + 8 * ((x4 - 4) * (x6 - 4)) + 4 * (2 * 7.02674064 - 8) * (x3 - 4) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x2 - 7.02674064) * (x4 - 4)) + 2 * ((x2 - 7.02674064) * (x3 - 4) * (x6 - 4)) + (2 * 7.02674064 - 8) * ((x1 - 7.02674064) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x3 - 4)) + 2 * ((x1 - 7.02674064) * (x2 - 7.02674064) * (x4 - 4))) := mul_nonneg hstep hG
  have hsq : (0:ℝ) ≤ (x2 * (8 - x2)) * (x5 - 4) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  linarith

private theorem H_mono_6 (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2) (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6) (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    rhoX x1 x2 x3 x4 x5 4 - 8 * deltaX x1 x2 x3 x4 x5 4 ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have hid : (rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6) - (rhoX x1 x2 x3 x4 x5 4 - 8 * deltaX x1 x2 x3 x4 x5 4)
      = (x6 - 4) * (4 * ((7.02674064 - 4) * (2 * 7.02674064 - 8)) * 1 + 8 * ((x4 - 4) * (x5 - 4)) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x5 - 4)) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x4 - 4)) + 4 * (2 * 7.02674064 - 8) * (x2 - 7.02674064) + 2 * ((x2 - 7.02674064) * (x3 - 4) * (x5 - 4)) + 4 * (2 * 7.02674064 - 8) * (x1 - 7.02674064) + 2 * ((x1 - 7.02674064) * (x3 - 4) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x2 - 7.02674064))) + (x3 * (8 - x3)) * (x6 - 4) ^ 2 := by
    unfold rhoX deltaX; ring
  have hA : (0:ℝ) ≤ x3 * (8 - x3) := by nlinarith
  have hG : (0:ℝ) ≤ 4 * ((7.02674064 - 4) * (2 * 7.02674064 - 8)) * 1 + 8 * ((x4 - 4) * (x5 - 4)) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x5 - 4)) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x4 - 4)) + 4 * (2 * 7.02674064 - 8) * (x2 - 7.02674064) + 2 * ((x2 - 7.02674064) * (x3 - 4) * (x5 - 4)) + 4 * (2 * 7.02674064 - 8) * (x1 - 7.02674064) + 2 * ((x1 - 7.02674064) * (x3 - 4) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x2 - 7.02674064)) := by
    have hCpos : (0:ℝ) < 2 * 7.02674064 - 8 := by norm_num
    have hDpos : (0:ℝ) < (7.02674064 - 4) * (2 * 7.02674064 - 8) := by norm_num
    have hu1 : (0:ℝ) ≤ x1 - 7.02674064 := by linarith
    have hu2 : (0:ℝ) ≤ x2 - 7.02674064 := by linarith
    have hu3 : (0:ℝ) ≤ x3 - 4 := by linarith
    have hu4 : (0:ℝ) ≤ x4 - 4 := by linarith
    have hu5 : (0:ℝ) ≤ x5 - 4 := by linarith
    have hu6 : (0:ℝ) ≤ x6 - 4 := by linarith
    have h16 : (0:ℝ) ≤ 16 - (x4 - 4) ^ 2 := by nlinarith
    have h16' : (0:ℝ) ≤ 16 - (x5 - 4) ^ 2 := by nlinarith
    nlinarith [      mul_nonneg hCpos.le h16, mul_nonneg hCpos.le h16',
      mul_nonneg (mul_nonneg hCpos.le hu6) (by norm_num : (0:ℝ) ≤ 4),
      mul_nonneg (mul_nonneg hCpos.le hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu4) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu2) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu4) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu3) hu5) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu3) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu6,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu4) hu5,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu3) hu6,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu3,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu1) hu2) hu4,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hu1) hu2,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu5,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hu2) hu3) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu5) hu6,
      mul_nonneg (mul_nonneg hDpos.le hu4) hu6,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu5,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) hu4,
      mul_nonneg (mul_nonneg hDpos.le (by norm_num : (0:ℝ) ≤ 1)) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu2) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu1) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu4) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu3) (by norm_num : (0:ℝ) ≤ 1),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hu5) (by norm_num : (0:ℝ) ≤ 1)]
  have hstep : (0:ℝ) ≤ x6 - 4 := by linarith
  have hprod : (0:ℝ) ≤ (x6 - 4) * (4 * ((7.02674064 - 4) * (2 * 7.02674064 - 8)) * 1 + 8 * ((x4 - 4) * (x5 - 4)) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x5 - 4)) + (2 * 7.02674064 - 8) * ((x3 - 4) * (x4 - 4)) + 4 * (2 * 7.02674064 - 8) * (x2 - 7.02674064) + 2 * ((x2 - 7.02674064) * (x3 - 4) * (x5 - 4)) + 4 * (2 * 7.02674064 - 8) * (x1 - 7.02674064) + 2 * ((x1 - 7.02674064) * (x3 - 4) * (x4 - 4)) + 8 * ((x1 - 7.02674064) * (x2 - 7.02674064))) := mul_nonneg hstep hG
  have hsq : (0:ℝ) ≤ (x3 * (8 - x3)) * (x6 - 4) ^ 2 :=
    mul_nonneg hA (sq_nonneg _)
  linarith
set_option maxHeartbeats 4000000 in
/-- The TADIAMB box bound: `rhoX − 8·deltaX ≥ 37` at the all-lower corner and
`H` increases along every axis (the six `H_mono_*` telescoping steps). -/
private theorem H_base (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 7.02674064 ≤ x1) (h2 : 7.02674064 ≤ x2)
    (h3 : 4 ≤ x3) (h4 : 4 ≤ x4) (h5 : 4 ≤ x5) (h6 : 4 ≤ x6)
    (h1h : x1 ≤ 8) (h2h : x2 ≤ 8) (h3h : x3 ≤ 8) (h4h : x4 ≤ 8) (h5h : x5 ≤ 8) (h6h : x6 ≤ 8) :
    (37:ℝ) ≤ rhoX x1 x2 x3 x4 x5 x6 - 8 * deltaX x1 x2 x3 x4 x5 x6 := by
  have s1 := H_mono_1 x1 7.02674064 4 4 4 4 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2 := H_mono_2 x1 x2 4 4 4 4 h1 h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1h h2h (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s3 := H_mono_3 x1 x2 x3 4 4 4 h1 h2 h3 (by norm_num) (by norm_num) (by norm_num) h1h h2h h3h (by norm_num) (by norm_num) (by norm_num)
  have s4 := H_mono_4 x1 x2 x3 x4 4 4 h1 h2 h3 h4 (by norm_num) (by norm_num) h1h h2h h3h h4h (by norm_num) (by norm_num)
  have s5 := H_mono_5 x1 x2 x3 x4 x5 4 h1 h2 h3 h4 h5 (by norm_num) h1h h2h h3h h4h h5h (by norm_num)
  have s6 := H_mono_6 x1 x2 x3 x4 x5 x6 h1 h2 h3 h4 h5 h6 h1h h2h h3h h4h h5h h6h
  have h0 : (37:ℝ) ≤ rhoX 7.02674064 7.02674064 4 4 4 4 - 8 * deltaX 7.02674064 7.02674064 4 4 4 4 := by
    norm_num [rhoX, deltaX]
  linarith

set_option maxHeartbeats 4000000 in
/-- rest 33: HOL ineq `TSKAJXY-TADIAMB` (ineq.hl:127).  Box
`[2hplus,√8]²×[2,√8]⁴`: `2 < yOfX rad2X`.  Pure algebra:
`rad2X = rhoX/(4·deltaX)` and `rhoX > 8·deltaX` on the box. -/
theorem nliTSKAJXYTADIAMB : bank_TSKAJXYTADIAMB := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hp : hplus = 1.3254 := rfl
  have x1l : (7.02674064:ℝ) ≤ y1 * y1 := by rw [hp] at h1l; nlinarith
  have x2l : (7.02674064:ℝ) ≤ y2 * y2 := by rw [hp] at h2l; nlinarith
  have x1h : y1 * y1 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x2h : y2 * y2 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x3l : (4:ℝ) ≤ y3 * y3 := by nlinarith
  have x3h : y3 * y3 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x4l : (4:ℝ) ≤ y4 * y4 := by nlinarith
  have x4h : y4 * y4 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x5l : (4:ℝ) ≤ y5 * y5 := by nlinarith
  have x5h : y5 * y5 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have x6l : (4:ℝ) ≤ y6 * y6 := by nlinarith
  have x6h : y6 * y6 ≤ 8 := by
    have h8 : Real.sqrt 8 * Real.sqrt 8 = (8:ℝ) := Real.mul_self_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (8:ℝ)]
  have hd : (157:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge_bT _ _ _ _ _ _ x1l x1h x2l x2h x3l x3h x4l x4h x5l x5h x6l x6h
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    have h37 := H_base (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      x1l x2l x3l x4l x5l x6l x1h x2h x3h x4h x5h x6h
    linarith
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by nlinarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

#print axioms Kepler.NliBanks2.nliBIXPCGW6652007036a2
#print axioms Kepler.NliBanks2.nliBIXPCGW7080972881a2
#print axioms Kepler.NliBanks2.nliBIXPCGW1738910218a2
#print axioms Kepler.NliBanks2.nliTSKAJXYTADIAMB

end Kepler.NliBanks2
