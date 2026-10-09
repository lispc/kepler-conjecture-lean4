#!/usr/bin/env python3
# Generator: BIEFJHU_explicit Lean block (PA22g wave) -> /tmp/bjf_block.lean
# Final version: all probe-3 fixes incorporated.

A_VAL = {3: "5.1501", 4: "5.2734", 5: "5.3452", 6: "5.3775", 7: "5.3955",
         8: "5.4067", 9: "5.4143", 10: "5.4196", 11: "5.4235"}

HEAD = r'''/-! ## BIEFJHU_explicit wave (PA22g): algebraic h-slide + polynomial asn
majorants.  Corrected route (supersedes the PA22e scout note below): the old
"reduce to h = 1" endpoint argument was WRONG (the gap is not worst at the
endpoint; for k = 5 the true worst point is interior, t ~ 1.05-1.10, true float
margin ~ 0.008).  Instead the h-range [1, h0] is covered by the chord/Phi-window
slide `p22_bjf_incle` (piecewise for k in {3,4,5,6} via `p22_bjf_route2` with
split b; single-piece k >= 7 via `p22_bjf_route1`), the k-windows
`2k*asn(sqrt3/2*sin(pi/k))` are polynomial majorants (`p22_bjf_w3..w11`,
`p22_bjf_wtail`), and every numeric certificate was re-verified in exact
rational arithmetic (min slide-budget slacks: k=3 0.024, k=4 0.015, k=5 0.003,
k=6 0.006, k in {7..11} >= 0.022, tail 0.047). -/

'''

KIT = r'''private theorem p22_bjf_sqrt3_le : (433:ℝ)/250 ≤ Real.sqrt 3 :=
  (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

private theorem p22_bjf_sqrt3_ub : Real.sqrt 3 ≤ 433015 / 250000 := by
  have h : (3:ℝ) ≤ (433015 / 250000) ^ 2 := by norm_num
  have h2 : Real.sqrt 3 ≤ Real.sqrt ((433015 / 250000) ^ 2) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 433015 / 250000)] at h2
  exact h2

private theorem p22_bjf_sqrt3_half : (sqrt3:ℝ)/2 ≤ 86603 / 100000 := by
  unfold sqrt3
  linarith [p22_bjf_sqrt3_ub]

private theorem p22_bjf_sqrt3_half2 : (sqrt3:ℝ)/2 ≤ 8661 / 10000 := by
  unfold sqrt3
  linarith [p22_bjf_sqrt3_ub]

private theorem p22_bjf_sqrt3_quarter : (sqrt3:ℝ)/4 ≤ 4331 / 10000 := by
  unfold sqrt3
  linarith [p22_bjf_sqrt3_ub]

/-- shared: `0 < 1 - x²` for `0 ≤ x < 1` (used by the BIEFJHU kit). -/
private theorem p22_bjf_sq_sub_pos {x : ℝ} (hx : x < 1) (hx0 : 0 ≤ x) :
    0 < 1 - x ^ 2 := by
  rcases lt_or_eq_of_le hx0 with hpos | h0eq
  · have hsq : x ^ 2 < x := by
      have e : x ^ 2 = x * x := by ring
      rw [e]; exact mul_lt_mul_of_pos_right hx hpos
    linarith
  · subst h0eq; norm_num

/-- auxiliary: `T h` = the spherical-cap cosine parameter of `BIEFJHU_explicit`. -/
private noncomputable def p22_bjf_T (h : ℝ) : ℝ :=
  h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2

private theorem p22_bjf_T1 : p22_bjf_T 1 = sqrt3 / 2 := by
  unfold p22_bjf_T sqrt3
  have h34 : (1:ℝ) - (1/2)^2 = 3/4 := by norm_num
  rw [h34, Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
  ring

private theorem p22_bjf_Tdiff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p22_bjf_T b - p22_bjf_T a
      = (b - a) * (sqrt3 / 4)
        - (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2 := by
  unfold p22_bjf_T sqrt3
  ring

/-- cos-representation: `T h = cos(pi/3 - arcsin(h/2))`. -/
private theorem p22_bjf_Tcos (h : ℝ) (hh : 0 ≤ h) (h1 : h ≤ 2) :
    p22_bjf_T h = Real.cos (Real.pi / 3 - Real.arcsin (h / 2)) := by
  unfold p22_bjf_T sqrt3
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three,
    Real.cos_arcsin, Real.sin_arcsin (by linarith) (by linarith)]
  ring

/-- `T` is increasing on `[1, h0]`. -/
private theorem p22_bjf_Tmono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h0) :
    p22_bjf_T a ≤ p22_bjf_T b := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha
  have hb0 : (0:ℝ) ≤ b := le_trans ha0 hab
  have hab2 : a / 2 ≤ b / 2 := by linarith
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hble : (b:ℝ) ≤ 126 / 100 := by rw [← h126]; exact hb
  have hsqrt3ge := p22_bjf_sqrt3_le
  have hrange : ∀ x : ℝ, 1 ≤ x → x ≤ h0 →
      0 ≤ Real.pi / 3 - Real.arcsin (x / 2)
      ∧ Real.pi / 3 - Real.arcsin (x / 2) ≤ Real.pi := by
    intro x hx1 hxh
    have hxi : (x:ℝ) ≤ 126 / 100 := by rw [← h126]; exact hxh
    have hx2 : x / 2 ≤ Real.sqrt 3 / 2 := by
      have h1 : (x:ℝ)/2 ≤ 63 / 100 := by linarith
      have h2 : (433:ℝ)/500 ≤ Real.sqrt 3 / 2 := by linarith [hsqrt3ge]
      linarith
    have hppi : (0:ℝ) < Real.pi := Real.pi_pos
    have hpi4 : (0:ℝ) < Real.pi / 2 := by linarith
    have hasin : Real.arcsin (x / 2) ≤ Real.pi / 3 := by
      refine le_trans (Real.arcsin_le_arcsin hx2) ?_
      have h3 : Real.arcsin (Real.sin (Real.pi / 3)) = Real.pi / 3 :=
        Real.arcsin_sin (by linarith) (by linarith)
      rw [Real.sin_pi_div_three] at h3
      rw [h3]
    constructor
    · have h4 : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      linarith [hasin, h4]
    · have h4b : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      have h5 : Real.arcsin (x / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
      linarith [h5, h4b, Real.pi_pos]
  have hxeq : p22_bjf_T a = Real.cos (Real.pi / 3 - Real.arcsin (a / 2)) :=
    p22_bjf_Tcos a ha0 (by linarith [h126, hble])
  have hbeq : p22_bjf_T b = Real.cos (Real.pi / 3 - Real.arcsin (b / 2)) :=
    p22_bjf_Tcos b hb0 (by linarith [h126, hble])
  rw [hxeq, hbeq]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
  · exact (hrange b (le_trans ha hab) hb).1
  · exact (hrange a ha (le_trans hab hb)).2
  · have h1 : Real.arcsin (a / 2) ≤ Real.arcsin (b / 2) := Real.arcsin_le_arcsin hab2
    linarith

/-- sqrt-subtraction identity used by the chord bounds. -/
private theorem p22_bjf_sqrtAB (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpos : 0 < Real.sqrt x + Real.sqrt y) :
    Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have h2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
  rw [eq_div_iff (ne_of_gt hpos)]
  nlinarith [h1, h2]

/-- global chord: `T b - T a ≤ (b-a)*2887/10000` on `[1, h0]` (slope `≤ 1/(2√3)`). -/
private theorem p22_bjf_chord {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h0) :
    p22_bjf_T b - p22_bjf_T a ≤ (b - a) * 2887 / 10000 := by
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha
  have hab0 : (0:ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hTdiff := p22_bjf_Tdiff ha0 (le_trans ha0 hab)
  have hA0 : (0:ℝ) ≤ 1 - (a / 2) ^ 2 := by nlinarith
  have hB0 : (0:ℝ) ≤ 1 - (b / 2) ^ 2 := by nlinarith
  have hA0s : (0:ℝ) < 1 - (a / 2) ^ 2 :=
    p22_bjf_sq_sub_pos (by linarith : (a:ℝ) / 2 < 1) (by linarith : (0:ℝ) ≤ a / 2)
  have hB0s : (0:ℝ) < 1 - (b / 2) ^ 2 :=
    p22_bjf_sq_sub_pos (by linarith : (b:ℝ) / 2 < 1) (by linarith : (0:ℝ) ≤ b / 2)
  have hpos : (0:ℝ) < Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hA0s) (Real.sqrt_pos.mpr hB0s)
  have hWsub : Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)
      = ((b:ℝ) ^ 2 - a ^ 2) / 4
        / (Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2)) := by
    rw [p22_bjf_sqrtAB (1 - (a / 2) ^ 2) (1 - (b / 2) ^ 2) hA0 hB0 hpos]
    have h4 : (1:ℝ) - (a / 2) ^ 2 - (1 - (b / 2) ^ 2) = ((b:ℝ) ^ 2 - a ^ 2) / 4 := by ring
    rw [h4]
  have hb1 : (1:ℝ) ≤ b := le_trans ha hab
  have hsqb : (1:ℝ) ≤ b * b := by
    have hbb : (1:ℝ) * 1 ≤ b * b :=
      mul_le_mul hb1 hb1 (by norm_num) (le_trans (by norm_num) hb1)
    simpa using hbb
  have hb2 : (1:ℝ) ≤ b ^ 2 := by rw [show b ^ 2 = b * b from by ring]; exact hsqb
  have hBle : Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by
    have h3 : (1:ℝ) - (b / 2) ^ 2 ≤ 3 / 4 := by linarith
    have h4 : Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt (3 / 4) := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)] at h4
    norm_num at h4
    exact h4
  have hsqa : (1:ℝ) ≤ a * a := by
    have haa : (1:ℝ) * 1 ≤ a * a :=
      mul_le_mul ha ha (by norm_num) (le_trans (by norm_num) ha)
    simpa using haa
  have ha2 : (1:ℝ) ≤ a ^ 2 := by rw [show a ^ 2 = a * a from by ring]; exact hsqa
  have hAle : Real.sqrt (1 - (a / 2) ^ 2) ≤ Real.sqrt 3 / 2 := by
    have h3 : (1:ℝ) - (a / 2) ^ 2 ≤ 3 / 4 := by linarith
    have h4 : Real.sqrt (1 - (a / 2) ^ 2) ≤ Real.sqrt (3 / 4) := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)] at h4
    norm_num at h4
    exact h4
  have hsum : Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt 3 := by
    have h4 : Real.sqrt 3 / 2 + Real.sqrt 3 / 2 = Real.sqrt 3 := by ring
    rw [← h4]; linarith
  have hs3p : (0:ℝ) < Real.sqrt 3 :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (by linarith [p22_bjf_sqrt3_le])
  -- W := (√(1-a²/4) - √(1-b²/4))/2 ≥ (b-a)/(4√3)
  have hS : Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) > 0 :=
    add_pos (Real.sqrt_pos.mpr hA0s) (Real.sqrt_pos.mpr hB0s)
  have hWge : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
      ≥ (b - a) / (4 * Real.sqrt 3) := by
    have hW2 : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
        = ((b:ℝ) ^ 2 - a ^ 2) / (8 * (Real.sqrt (1 - (a / 2) ^ 2)
          + Real.sqrt (1 - (b / 2) ^ 2))) := by
      rw [hWsub, eq_div_iff (by exact ne_of_gt hpos)]
      ring
    have e1 : (b:ℝ) ^ 2 - a ^ 2 = (b - a) * (a + b) := by ring
    have hstep1 : (b - a) * (8 * (Real.sqrt (1 - (a / 2) ^ 2)
        + Real.sqrt (1 - (b / 2) ^ 2))) ≤ (b - a) * (8 * Real.sqrt 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hab0
    have h4ab : (8:ℝ) ≤ (a + b) * 4 := by linarith
    rw [hW2, ge_iff_le, div_le_iff₀ (by linarith [hpos])]
    rw [div_mul_eq_mul_div, eq_div_iff (by exact ne_of_gt (by
      exact lt_of_le_of_lt (by norm_num : (0:ℝ) ≤ 4) (le_of_lt hs3p)))]
    have h2le : (2:ℝ) ≤ a + b := by linarith
    have hprod' : (2:ℝ) * (Real.sqrt (1 - (a / 2) ^ 2)
        + Real.sqrt (1 - (b / 2) ^ 2)) ≤ Real.sqrt 3 * (a + b) := by
      refine mul_le_mul_of_nonneg_right (by linarith [hsum]) (by nlinarith)
    calc ((b:ℝ) ^ 2 - a ^ 2) * (4 * Real.sqrt 3)
        = (b - a) * ((a + b) * (4 * Real.sqrt 3)) := by rw [e1]; ring
      _ ≤ (b - a) * (8 * (Real.sqrt (1 - (a / 2) ^ 2)
            + Real.sqrt (1 - (b / 2) ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ hab0
          linarith [hprod', h2le]
    have hc : (0:ℝ) < (8 * (Real.sqrt (1 - (a / 2) ^ 2)
        + Real.sqrt (1 - (b / 2) ^ 2))) * (4 * Real.sqrt 3) := by positivity
    have hx : ((b:ℝ) ^ 2 - a ^ 2) / (8 * (Real.sqrt (1 - (a / 2) ^ 2)
        + Real.sqrt (1 - (b / 2) ^ 2)))
        = ((b:ℝ) ^ 2 - a ^ 2) * (4 * Real.sqrt 3)
          / ((8 * (Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2)))
            * (4 * Real.sqrt 3)) := by ring
    have hy : (b - a) / (4 * Real.sqrt 3)
        = (b - a) * (8 * (Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2)))
          / ((8 * (Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2)))
            * (4 * Real.sqrt 3)) := by ring
  -- conclude: (b-a)*√3/4 - W ≤ (b-a)/(2√3) ≤ (b-a)*2887/10000
  have hident : (b - a) * (sqrt3 / 4) - (b - a) / (4 * Real.sqrt 3)
      = (b - a) / (2 * Real.sqrt 3) := by
    have hs : sqrt3 = Real.sqrt 3 := rfl
    rw [hs]
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have h2p : (0:ℝ) < 2 * Real.sqrt 3 := by positivity
    rw [eq_div_iff (by exact ne_of_gt h2p), sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
      show Real.sqrt 3 * (2 * Real.sqrt 3) = 2 * (Real.sqrt 3 * Real.sqrt 3) from by ring,
      hsq]
    norm_num
  have hrec : (1:ℝ) / (2 * Real.sqrt 3) ≤ 125 / 433 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt 3)]
    have h : (433:ℝ)/250 ≤ Real.sqrt 3 := p22_bjf_sqrt3_le
    nlinarith
  have h1 : (b - a) * (sqrt3 / 4) - (b - a) / (4 * Real.sqrt 3)
      ≤ (b - a) / (2 * Real.sqrt 3) := by rw [hident]
  have h3 : (b - a) / (2 * Real.sqrt 3) = (b - a) * (1 / (2 * Real.sqrt 3)) := by
    field_simp
  have hpos2 : (0:ℝ) ≤ b - a := hab0
  have hfin : ((b:ℝ) - a) * (1 / (2 * Real.sqrt 3)) ≤ (b - a) * 2887 / 10000 := by
    have h2' : (125:ℝ) / 433 ≤ 2887 / 10000 := by norm_num
    have h3' : ((b:ℝ) - a) * (1 / (2 * Real.sqrt 3)) ≤ ((b:ℝ) - a) * (125 / 433) :=
      mul_le_mul_of_nonneg_left hrec hab0
    have h5' : ((b:ℝ) - a) * (2887 / 10000) = ((b:ℝ) - a) * 2887 / 10000 := by ring
    have h4' : ((b:ℝ) - a) * (125 / 433) ≤ ((b:ℝ) - a) * (2887 / 10000) :=
      mul_le_mul_of_nonneg_left h2' hab0
    rw [h5']
    exact le_trans h3' h4'
  have hstep : ((b:ℝ) - a) * (sqrt3 / 4) - (Real.sqrt (1 - (a / 2) ^ 2)
      - Real.sqrt (1 - (b / 2) ^ 2)) / 2
      ≤ ((b:ℝ) - a) * (1 / (2 * Real.sqrt 3)) := by linarith [hWge, h1, h3]
  calc p22_bjf_T b - p22_bjf_T a
      = (b - a) * (sqrt3 / 4) - (Real.sqrt (1 - (a / 2) ^ 2)
          - Real.sqrt (1 - (b / 2) ^ 2)) / 2 := hTdiff
    _ ≤ ((b:ℝ) - a) * (1 / (2 * Real.sqrt 3)) := hstep
    _ ≤ ((b:ℝ) - a) * 2887 / 10000 := hfin

/-- chord between `a ≤ b` in `[1, h0]` with slope bound `kappa ≥ sqrt3/4 - a/(8r)`,
    `r ≥ √(1-(a/2)²)`. -/
private theorem p22_bjf_chord_b {a b r kappa : ℝ} (ha1 : 1 ≤ a) (hab : a ≤ b)
    (hb0 : b ≤ h0) (hr : Real.sqrt (1 - (a / 2) ^ 2) ≤ r) (hr0 : 0 < r)
    (hcle : sqrt3 / 4 - a / (8 * r) ≤ kappa) :
    p22_bjf_T b - p22_bjf_T a ≤ (b - a) * kappa := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha1
  have hab0 : (0:ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hTdiff := p22_bjf_Tdiff ha0 (le_trans ha0 hab)
  have hA0 : (0:ℝ) ≤ 1 - (a / 2) ^ 2 := by nlinarith
  have hB0 : (0:ℝ) ≤ 1 - (b / 2) ^ 2 := by nlinarith
  have h2lt : (h0:ℝ) < 2 := by norm_num [h0]
  have hA0s : (0:ℝ) < 1 - (a / 2) ^ 2 :=
    p22_bjf_sq_sub_pos (by linarith : (a:ℝ) / 2 < 1) (by linarith : (0:ℝ) ≤ a / 2)
  have hB0s : (0:ℝ) < 1 - (b / 2) ^ 2 :=
    p22_bjf_sq_sub_pos (by linarith : (b:ℝ) / 2 < 1) (by linarith : (0:ℝ) ≤ b / 2)
  have hpos : (0:ℝ) < Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) :=
    add_pos (Real.sqrt_pos.mpr hA0s) (Real.sqrt_pos.mpr hB0s)
  have hWsub : Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)
      = ((b:ℝ) ^ 2 - a ^ 2) / 4
        / (Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2)) := by
    rw [p22_bjf_sqrtAB (1 - (a / 2) ^ 2) (1 - (b / 2) ^ 2) hA0 hB0 hpos]
    have h4 : (1:ℝ) - (a / 2) ^ 2 - (1 - (b / 2) ^ 2) = ((b:ℝ) ^ 2 - a ^ 2) / 4 := by ring
    rw [h4]
  have hS : Real.sqrt (1 - (a / 2) ^ 2) + Real.sqrt (1 - (b / 2) ^ 2) ≤ 2 * r := by
    have h1 : Real.sqrt (1 - (b / 2) ^ 2) ≤ Real.sqrt (1 - (a / 2) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h2 : Real.sqrt (1 - (a / 2) ^ 2) ≤ r := hr
    linarith
  have hWge : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
      ≥ (b - a) * a / (8 * r) := by
    have hW2 : (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2
        = ((b:ℝ) ^ 2 - a ^ 2) / (8 * (Real.sqrt (1 - (a / 2) ^ 2)
          + Real.sqrt (1 - (b / 2) ^ 2))) := by
      rw [hWsub, eq_div_iff (by exact mul_ne_zero (by norm_num) (ne_of_gt hpos))]
      ring
    have hstep1 : (b - a) * a * (8 * (Real.sqrt (1 - (a / 2) ^ 2)
        + Real.sqrt (1 - (b / 2) ^ 2))) ≤ (b - a) * a * (8 * (2 * r)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith) (by norm_num))
        (mul_nonneg hab0 ha0)
    have e1 : (b:ℝ) ^ 2 - a ^ 2 = (b - a) * (a + b) := by ring
    have hstep2 : (b - a) * a * (8 * (2 * r)) ≤ ((b:ℝ) ^ 2 - a ^ 2) * (8 * r) := by
      rw [e1]
      have hr0' : (0:ℝ) ≤ r := le_of_lt hr0
      have hcore : (a:ℝ) * (8 * (2 * r)) ≤ (a + b) * (8 * r) := by
        have e2 : (a:ℝ) * (8 * (2 * r)) = (a * r) * 16 := by ring
        have e3 : (a + b) * (8 * r) = (a * r) * 8 + (b * r) * 8 := by ring
        rw [e2, e3]
        have hbr : (a:ℝ) * r ≤ b * r := mul_le_mul_of_nonneg_right hab hr0'
        linarith
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hcore hab0
    rw [hW2, ge_iff_le, div_le_iff₀ (by linarith [hpos])]
    rw [div_mul_eq_mul_div, eq_div_iff (by exact ne_of_gt (by
      exact lt_of_le_of_lt (by norm_num : (0:ℝ) ≤ 8) (le_of_lt hr0)))]
    have hab' : (a:ℝ) ≤ a + b := by linarith
    have hge2 : ((b:ℝ) ^ 2 - a ^ 2) * (8 * r)
        ≥ (b - a) * a * (8 * r) := by
      have hpp : ((b:ℝ) ^ 2 - a ^ 2) = (b - a) * (a + b) := by rw [e1]; ring
      rw [hpp]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_refl _)
        (by linarith)) (by nlinarith)
    exact le_of_lt (by
      have h1 : (b - a) * a * (8 * r) ≤ ((b:ℝ) ^ 2 - a ^ 2) * (8 * r) := hge2
      linarith)
  have h1 : p22_bjf_T b - p22_bjf_T a
      ≤ (b - a) * (sqrt3 / 4) - (b - a) * (a / (8 * r)) := by
    linarith [hTdiff, hWge]
  have h2 : (b - a) * (sqrt3 / 4) - (b - a) * (a / (8 * r)) ≤ (b - a) * kappa := by
    have e2 : (b - a) * (sqrt3 / 4) - (b - a) * (a / (8 * r))
        = (b - a) * (sqrt3 / 4 - a / (8 * r)) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hcle hab0
  exact le_trans h1 h2

/-- `asn` increment bound (derivative majorized at the right end). -/
private theorem p22_bjf_asn_inc {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy1 : y < 1) :
    asn y - asn x ≤ (y - x) / Real.sqrt (1 - y ^ 2) := by
  show Real.arcsin y - Real.arcsin x ≤ _
  have hyQ : (0:ℝ) < 1 - y ^ 2 := p22_bjf_sq_sub_pos (by linarith) (le_trans hx hxy)
  have hle : ∀ t ∈ Set.Icc x y,
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - y ^ 2) := by
    intro t ht
    obtain ⟨ht0, hty⟩ := ht
    have hQt : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    have hsle : Real.sqrt (1 - y ^ 2) ≤ Real.sqrt (1 - t ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hyQ) hsle
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc x y) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) (Set.uIcc x y) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    obtain ⟨ht0, hty⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in x..y, 1 / Real.sqrt (1 - t ^ 2) = asn y - asn x := by
    have hderiv : ∀ t ∈ Set.uIcc x y, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hxy] at ht
      obtain ⟨ht0, hty⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
  have hcon2 : ContinuousOn (fun _ : ℝ => 1 / Real.sqrt (1 - y ^ 2)) (Set.uIcc x y) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hcon2.intervalIntegrable hle
  have hconst : ∫ t in x..y, (1:ℝ) / Real.sqrt (1 - y ^ 2)
      = (y - x) / Real.sqrt (1 - y ^ 2) := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul]
  rw [hint, hconst] at hmono
  exact hmono

/-- Phi-window slide: `2k*(asn y - asn x) ≤ 2k*S*phi` from the Phi-certificate
    `phi²(1-(tau*sig)²) ≥ sig²`, `y = T h*sin(pi/k) ≤ tau*sig < 1`, `y - x ≤ S*sig`. -/
private theorem p22_bjf_incle {k : ℕ} {h x y sig tau phi S : ℝ}
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy : y = p22_bjf_T h * Real.sin (Real.pi / k))
    (hT0 : 0 ≤ p22_bjf_T h) (hy1 : y < 1) (hTtau : p22_bjf_T h ≤ tau)
    (htau0 : 0 ≤ tau) (hsub : y - x ≤ S * sig) (hS0 : 0 ≤ S)
    (hsin0 : 0 ≤ Real.sin (Real.pi / k)) (hsig : Real.sin (Real.pi / k) ≤ sig)
    (hphiP : 0 < phi) (hQ0p : 0 < 1 - (tau * sig) ^ 2)
    (hphi : (1 - (tau * sig) ^ 2) * phi ^ 2 ≥ sig ^ 2) :
    2 * (k:ℝ) * (asn y - asn x) ≤ 2 * (k:ℝ) * S * phi := by
  have hy0 : (0:ℝ) ≤ y := by rw [hy]; exact mul_nonneg hT0 hsin0
  have hinc := p22_bjf_asn_inc hx0 hxy hy1
  have hy2 : y ^ 2 ≤ (tau * sig) ^ 2 := by
    rw [hy]
    refine pow_le_pow_left₀ (mul_nonneg hT0 hsin0) ?_ 2
    exact mul_le_mul hTtau hsig hsin0 htau0
  have hQ : (0:ℝ) < 1 - y ^ 2 := p22_bjf_sq_sub_pos (by linarith) hy0
  have hsqrt1 : Real.sqrt (1 - y ^ 2) ≥ Real.sqrt (1 - (tau * sig) ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq1 : (sig / phi) ^ 2 ≤ 1 - (tau * sig) ^ 2 := by
    have hpow : (sig / phi) ^ 2 = sig ^ 2 / phi ^ 2 := by rw [div_pow]
    rw [hpow]
    exact (div_le_iff₀ (by nlinarith [hphiP])).mpr (by linarith)
  have hsig0 : (0:ℝ) ≤ sig := le_trans hsin0 hsig
  have hsq2 : sig / phi ≤ Real.sqrt (1 - (tau * sig) ^ 2) :=
    (Real.le_sqrt (div_nonneg hsig0 (le_of_lt hphiP)) (le_of_lt hQ0p)).mpr hsq1
  have hsigle : (sig:ℝ) ≤ phi * Real.sqrt (1 - y ^ 2) := by
    have h3 : (sig:ℝ)/phi ≤ Real.sqrt (1 - y ^ 2) := le_trans hsq2 hsqrt1
    have h4 : (sig:ℝ) = phi * (sig / phi) := by field_simp
    rw [h4]
    exact mul_le_mul_of_nonneg_left h3 (le_of_lt hphiP)
  have hstep : (y - x) / Real.sqrt (1 - y ^ 2) ≤ S * phi := by
    have hchain : y - x ≤ (S * phi) * Real.sqrt (1 - y ^ 2) := by
      have hs1 : y - x ≤ S * (phi * Real.sqrt (1 - y ^ 2)) := by
        calc y - x ≤ S * sig := hsub
          _ ≤ S * (phi * Real.sqrt (1 - y ^ 2)) := mul_le_mul_of_nonneg_left hsigle hS0
      have hrw : S * (phi * Real.sqrt (1 - y ^ 2)) = (S * phi) * Real.sqrt (1 - y ^ 2) := by
        ring
      rw [hrw] at hs1
      exact hs1
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr hchain
  calc 2 * (k:ℝ) * (asn y - asn x)
      ≤ 2 * (k:ℝ) * ((y - x) / Real.sqrt (1 - y ^ 2)) :=
        mul_le_mul_of_nonneg_left hinc (by positivity)
    _ ≤ 2 * (k:ℝ) * (S * phi) := mul_le_mul_of_nonneg_left hstep (by positivity)

/-- quadratic majorant: `asn w ≤ w+w³/6+w⁵/10` for `w² ≤ 17/64`. -/
private theorem p22_bjf_asn_quad {w : ℝ} (hw : 0 ≤ w) (hwu : w ^ 2 ≤ 17 / 64) :
    asn w ≤ w + w ^ 3 / 6 + w ^ 5 / 10 := by
  show Real.arcsin w ≤ _
  have hdom : ∀ t ∈ Set.Icc (0:ℝ) w,
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have hu : t ^ 2 ≤ (17:ℝ) / 64 := by nlinarith
    have hu0 : (0:ℝ) ≤ t ^ 2 := by nlinarith
    have hQ : 0 < 1 - t ^ 2 := by nlinarith
    have hu2p : (0:ℝ) ≤ t ^ 4 := by
      have e : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 2)
    have hu2 : t ^ 4 ≤ (17:ℝ)/64 * t ^ 2 := by
      have e : t ^ 4 = t ^ 2 * t ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hu0
    have hu3 : t ^ 6 ≤ (17:ℝ)/64 * t ^ 4 := by
      have e : t ^ 6 = t ^ 4 * t ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hu2p
    have hcert : 1 - 3 * t ^ 2 - t ^ 4 - t ^ 6 ≥ 0 := by linarith
    have hkey : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2) ≥ 1 := by
      have hex : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2)
          = 1 + t ^ 4 * (1 - 3 * t ^ 2 - t ^ 4 - t ^ 6) / 4 := by ring
      rw [hex]
      exact le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (by nlinarith) hcert) (by norm_num : (0:ℝ) ≤ 4))
    have hP : (0:ℝ) < 1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4 := by nlinarith
    have hge : (0:ℝ) ≤ 1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4 := le_of_lt hP
    have hsq : (1:ℝ) ≤ (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2) := by
      have hQnn : (0:ℝ) ≤ 1 - t ^ 2 := le_of_lt hQ
      have h2 : (1:ℝ) ≤ Real.sqrt ((1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2
          * (1 - t ^ 2)) := le_trans (by rw [Real.sqrt_one]) (Real.sqrt_le_sqrt hkey)
      have h3 : Real.sqrt ((1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2))
          = (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) * Real.sqrt (1 - t ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)),
          Real.sqrt_sq hge]
      rw [← h3]; exact h2
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by linarith [hsq])
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hw] at ht
    obtain ⟨ht0, htw⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hw] at ht
      obtain ⟨ht0, htw⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 2) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hbase4 : IntervalIntegrable (fun t : ℝ => t ^ 4) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 4) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => 1) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)) MeasureTheory.volume (0:ℝ) w :=
    hc1.add ((hbase.const_mul (1/2)).add (hbase4.const_mul (1/2)))
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
      = w + w ^ 3 / 6 + w ^ 5 / 10 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
        MeasureTheory.volume (0:ℝ) w from (hbase.const_mul (1/2)).add (hbase4.const_mul (1/2))),
      intervalIntegral.integral_add (hbase.const_mul (1/2)) (hbase4.const_mul (1/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

PLACEHOLDER_SEPT
PLACEHOLDER_SER4
PLACEHOLDER_REST
'''


SEPT = r'''/-- septic majorant: `asn w ≤ w+w³/6+w⁵/10+3w⁷/28` for `w² ≤ 7/10`.
    Certificate: `(1+u/2+u²/2+3u³/4)²(1-u) = 1 + u²(1/4+3u/4-u²-u³/4-3u⁴/16-9u⁵/16)`. -/
private theorem p22_bjf_asn_sept {w : ℝ} (hw : 0 ≤ w) (hwu : w ^ 2 ≤ 7 / 10) :
    asn w ≤ w + w ^ 3 / 6 + w ^ 5 / 10 + 3 * w ^ 7 / 28 := by
  show Real.arcsin w ≤ _
  have hdom : ∀ t ∈ Set.Icc (0:ℝ) w,
      1 / Real.sqrt (1 - t ^ 2)
      ≤ 1 + ((1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have hu0 : (0:ℝ) ≤ t ^ 2 := by nlinarith
    have hu : t ^ 2 ≤ (7:ℝ) / 10 := by nlinarith
    have hQ : 0 < 1 - t ^ 2 := by nlinarith
    have hp2 : (0:ℝ) ≤ t ^ 4 := by
      have e : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 2)
    have hp3 : (0:ℝ) ≤ t ^ 6 := by
      have e : t ^ 6 = (t ^ 3) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 3)
    have hp4 : (0:ℝ) ≤ t ^ 8 := by
      have e : t ^ 8 = (t ^ 4) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 4)
    have hp5 : (0:ℝ) ≤ t ^ 10 := by
      have e : t ^ 10 = (t ^ 5) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 5)
    have h2 : t ^ 4 ≤ (7:ℝ)/10 * t ^ 2 := by
      have e : t ^ 4 = t ^ 2 * t ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hu0
    have h3 : t ^ 6 ≤ (7:ℝ)/10 * t ^ 4 := by
      have e : t ^ 6 = t ^ 2 * t ^ 4 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp2
    have h4 : t ^ 8 ≤ (7:ℝ)/10 * t ^ 6 := by
      have e : t ^ 8 = t ^ 2 * t ^ 6 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp3
    have h5 : t ^ 10 ≤ (7:ℝ)/10 * t ^ 8 := by
      have e : t ^ 10 = t ^ 2 * t ^ 8 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp4
    have hcert : (1:ℝ)/4 + 3 * t ^ 2 / 4 - t ^ 4 - t ^ 6 / 4 - 3 * t ^ 8 / 16
        - 9 * t ^ 10 / 16 ≥ 0 := by linarith
    have hkey : (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2
        * (1 - t ^ 2) ≥ 1 := by
      have hex : (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2
          * (1 - t ^ 2)
          = 1 + t ^ 2 * ((1:ℝ)/4 + 3 * t ^ 2 / 4 - t ^ 4 - t ^ 6 / 4 - 3 * t ^ 8 / 16
            - 9 * t ^ 10 / 16) := by ring
      rw [hex]
      exact le_add_of_nonneg_right (mul_nonneg hu0 hcert)
    have hP : (0:ℝ) < 1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6) := by
      nlinarith
    have hge : (0:ℝ) ≤ 1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6) :=
      le_of_lt hP
    have hsq : (1:ℝ) ≤ (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
        * Real.sqrt (1 - t ^ 2) := by
      have hQnn : (0:ℝ) ≤ 1 - t ^ 2 := le_of_lt hQ
      have h2' : (1:ℝ) ≤ Real.sqrt ((1 + (1:ℝ)/2 * t ^ 2
          + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2 * (1 - t ^ 2)) :=
        le_trans (by rw [Real.sqrt_one]) (Real.sqrt_le_sqrt hkey)
      have h3' : Real.sqrt ((1 + (1:ℝ)/2 * t ^ 2
          + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)) ^ 2 * (1 - t ^ 2))
          = (1 + (1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
            * Real.sqrt (1 - t ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg (1 + (1:ℝ)/2 * t ^ 2
          + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))), Real.sqrt_sq hge]
      rw [← h3']; exact h2'
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by linarith [hsq])
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hw] at ht
    obtain ⟨ht0, htw⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hw] at ht
      obtain ⟨ht0, htw⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 2) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hbase4 : IntervalIntegrable (fun t : ℝ => t ^ 4) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 4) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hbase6 : IntervalIntegrable (fun t : ℝ => t ^ 6) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 6) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => 1) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6)))
      MeasureTheory.volume (0:ℝ) w :=
    hc1.add ((hbase.const_mul (1/2)).add ((hbase4.const_mul (1/2)).add
      (hbase6.const_mul (3/4))))
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
      = w + w ^ 3 / 6 + w ^ 5 / 10 + 3 * w ^ 7 / 28 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2
        + ((1:ℝ)/2 * t ^ 4 + (3:ℝ)/4 * t ^ 6))
        MeasureTheory.volume (0:ℝ) w
        from (hbase.const_mul (1/2)).add ((hbase4.const_mul (1/2)).add
          (hbase6.const_mul (3/4)))),
      intervalIntegral.integral_add (hbase.const_mul (1/2))
        ((hbase4.const_mul (1/2)).add (hbase6.const_mul (3/4))),
      intervalIntegral.integral_add (hbase4.const_mul (1/2)) (hbase6.const_mul (3/4)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow, integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

'''

SER4 = r'''/-- arcsin series bound with inflated 9th-order term (tail `≤ d₄u⁴/(1-u)`,
    `d₄ = 35/128`, window `u ≤ 3/8`):
    `asn w ≤ w+w³/6+3w⁵/40+5w⁷/112+7w⁹/144` for `w² ≤ 3/8`.
    Certificate: `(1+u/2+3u²/8+5u³/16+7u⁴/16)²(1-u)
      = 1 + 21u⁴/64 - 21u⁵/32 - 63u⁶/256 - 39u⁷/256 - 21u⁸/256 - 49u⁹/256 ≥ 1`
    on `u ≤ 3/8` (exact-rational/LP-checked). -/
private theorem p22_bjf_asn_ser4 {w : ℝ} (hw : 0 ≤ w) (hwu : w ^ 2 ≤ 3 / 8) :
    asn w ≤ w + w ^ 3 / 6 + 3 * w ^ 5 / 40 + 5 * w ^ 7 / 112 + 7 * w ^ 9 / 144 := by
  show Real.arcsin w ≤ _
  have hdom : ∀ t ∈ Set.Icc (0:ℝ) w,
      1 / Real.sqrt (1 - t ^ 2)
      ≤ 1 + ((1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4 + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have hu0 : (0:ℝ) ≤ t ^ 2 := by nlinarith
    have hu : t ^ 2 ≤ (3:ℝ) / 8 := by nlinarith
    have hQ : 0 < 1 - t ^ 2 := by nlinarith
    have hp2 : (0:ℝ) ≤ t ^ 4 := by
      have e : t ^ 4 = (t ^ 2) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 2)
    have hp3 : (0:ℝ) ≤ t ^ 6 := by
      have e : t ^ 6 = (t ^ 3) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 3)
    have hp4 : (0:ℝ) ≤ t ^ 8 := by
      have e : t ^ 8 = (t ^ 4) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 4)
    have hp5 : (0:ℝ) ≤ t ^ 10 := by
      have e : t ^ 10 = (t ^ 5) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 5)
    have hp6 : (0:ℝ) ≤ t ^ 12 := by
      have e : t ^ 12 = (t ^ 6) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 6)
    have hp7 : (0:ℝ) ≤ t ^ 14 := by
      have e : t ^ 14 = (t ^ 7) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 7)
    have hp8 : (0:ℝ) ≤ t ^ 16 := by
      have e : t ^ 16 = (t ^ 8) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 8)
    have hp9 : (0:ℝ) ≤ t ^ 18 := by
      have e : t ^ 18 = (t ^ 9) ^ 2 := by ring
      rw [e]; exact sq_nonneg (t ^ 9)
    have h2 : t ^ 4 ≤ (3:ℝ)/8 * t ^ 2 := by
      have e : t ^ 4 = t ^ 2 * t ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hu0
    have h3 : t ^ 6 ≤ (3:ℝ)/8 * t ^ 4 := by
      have e : t ^ 6 = t ^ 2 * t ^ 4 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp2
    have h4 : t ^ 8 ≤ (3:ℝ)/8 * t ^ 6 := by
      have e : t ^ 8 = t ^ 2 * t ^ 6 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp3
    have h5 : t ^ 10 ≤ (3:ℝ)/8 * t ^ 8 := by
      have e : t ^ 10 = t ^ 2 * t ^ 8 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp4
    have h6 : t ^ 12 ≤ (3:ℝ)/8 * t ^ 10 := by
      have e : t ^ 12 = t ^ 2 * t ^ 10 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp5
    have h7 : t ^ 14 ≤ (3:ℝ)/8 * t ^ 12 := by
      have e : t ^ 14 = t ^ 2 * t ^ 12 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp6
    have h8 : t ^ 16 ≤ (3:ℝ)/8 * t ^ 14 := by
      have e : t ^ 16 = t ^ 2 * t ^ 14 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp7
    have h9 : t ^ 18 ≤ (3:ℝ)/8 * t ^ 16 := by
      have e : t ^ 18 = t ^ 2 * t ^ 16 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hu hp8
    have hcert : (0:ℝ) ≤ (21:ℝ)/64 * t ^ 8 - (21:ℝ)/32 * t ^ 10 - (63:ℝ)/256 * t ^ 12
        - (39:ℝ)/256 * t ^ 14 - (21:ℝ)/256 * t ^ 16 - (49:ℝ)/256 * t ^ 18 := by
      linarith
    have hkey : (1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
        + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) ^ 2 * (1 - t ^ 2) ≥ 1 := by
      have hex : (1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
          + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) ^ 2 * (1 - t ^ 2)
          = 1 + (21:ℝ)/64 * t ^ 8 - (21:ℝ)/32 * t ^ 10 - (63:ℝ)/256 * t ^ 12
            - (39:ℝ)/256 * t ^ 14 - (21:ℝ)/256 * t ^ 16 - (49:ℝ)/256 * t ^ 18 := by
        ring
      rw [hex]
      linarith
    have hP : (0:ℝ) < 1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
        + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8)) := by
      nlinarith
    have hge : (0:ℝ) ≤ 1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
        + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8)) := le_of_lt hP
    have hsq : (1:ℝ) ≤ (1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
        + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) * Real.sqrt (1 - t ^ 2) := by
      have hQnn : (0:ℝ) ≤ 1 - t ^ 2 := le_of_lt hQ
      have h2' : (1:ℝ) ≤ Real.sqrt ((1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
          + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) ^ 2 * (1 - t ^ 2)) :=
        le_trans (by rw [Real.sqrt_one]) (Real.sqrt_le_sqrt hkey)
      have h3' : Real.sqrt ((1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
          + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) ^ 2 * (1 - t ^ 2))
          = (1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
            + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8))) * Real.sqrt (1 - t ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg (1 + (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
          + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8)))), Real.sqrt_sq hge]
      rw [← h3']; exact h2'
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr (by linarith [hsq])
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hw] at ht
    obtain ⟨ht0, htw⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hw] at ht
      obtain ⟨ht0, htw⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 2) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hbase4 : IntervalIntegrable (fun t : ℝ => t ^ 4) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 4) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hbase6 : IntervalIntegrable (fun t : ℝ => t ^ 6) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 6) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hbase8 : IntervalIntegrable (fun t : ℝ => t ^ 8) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => t ^ 8) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (u := fun t : ℝ => 1) (a := (0:ℝ)) (b := w) (by fun_prop)
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
        + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8)))) MeasureTheory.volume (0:ℝ) w :=
    hc1.add ((hbase.const_mul (1/2)).add ((hbase4.const_mul (3/8)).add
      ((hbase6.const_mul (5/16)).add (hbase8.const_mul (7/16)))))
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
      + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8)))
      = w + w ^ 3 / 6 + 3 * w ^ 5 / 40 + 5 * w ^ 7 / 112 + 7 * w ^ 9 / 144 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2 + ((3:ℝ)/8 * t ^ 4
        + ((5:ℝ)/16 * t ^ 6 + (7:ℝ)/16 * t ^ 8)))
        MeasureTheory.volume (0:ℝ) w
        from (hbase.const_mul (1/2)).add ((hbase4.const_mul (3/8)).add
          ((hbase6.const_mul (5/16)).add (hbase8.const_mul (7/16))))),
      intervalIntegral.integral_add (hbase.const_mul (1/2))
        ((hbase4.const_mul (3/8)).add
          ((hbase6.const_mul (5/16)).add (hbase8.const_mul (7/16)))),
      intervalIntegral.integral_add (hbase4.const_mul (3/8))
        ((hbase6.const_mul (5/16)).add (hbase8.const_mul (7/16))),
      intervalIntegral.integral_add (hbase6.const_mul (5/16)) (hbase8.const_mul (7/16)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow,
      integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

'''

REST = r'''/-- shared: `sin(pi/k) ≥ 0` for `k ≥ 1`. -/
private theorem p22_bjf_sinpos {k : ℕ} (hk : 1 ≤ k) : 0 ≤ Real.sin (Real.pi / k) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hk
  refine Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg Real.pi_pos.le hk0.le) ?_
  have h1 : Real.pi / k ≤ Real.pi / 1 :=
    p22_div_le_div_real_left (le_of_lt Real.pi_pos) (by norm_num) (by exact_mod_cast hk)
  linarith

/-- shared: `T h ≤ 235273/250000` on `[1, h0]` (= `√3/2 + 0.26*2887/10⁴`). -/
private theorem p22_bjf_hTbound {h : ℝ} (hh1 : 1 ≤ h) (hh0 : h ≤ h0) :
    p22_bjf_T h ≤ 235273 / 250000 := by
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hch := p22_bjf_chord (a := 1) (b := h) (le_refl 1) hh1 hh0
  have hT1 : p22_bjf_T 1 = sqrt3 / 2 := p22_bjf_T1
  have hs := p22_bjf_sqrt3_half
  rw [hT1] at hch
  have h26 : (h0:ℝ) - 1 = 26 / 100 := by rw [h126]; norm_num
  have hsub : ((h:ℝ) - 1) * 2887 / 10000 ≤ ((h0:ℝ) - 1) * 2887 / 10000 := by
    refine p22_div_le_div_right (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hsub2 : ((h0:ℝ) - 1) * 2887 / 10000 = 26 / 100 * 2887 / 10000 := by rw [h26]
  linarith

/-- Phi-window certificate for the tail (`k ≥ 12`): monotone reduction to the
`k = 12` worst case + exact rational check. -/
private theorem p22_bjf_tail_phi (k : ℕ) (hk : 12 ≤ k) :
    (1 - ((235273 / 250000) * (31416 / 10000 / k)) ^ 2)
      * (270126977 / 1000000000) ^ 2 ≥ (31416 / 10000 / k) ^ 2 := by
  have hk1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk
  have hsp : (0:ℝ) ≤ (31416:ℝ)/10000/k :=
    div_nonneg (by norm_num) (le_of_lt (by exact_mod_cast lt_of_lt_of_le (by norm_num) hk))
  have hs : (31416:ℝ)/10000/k ≤ (31416:ℝ)/10000/12 :=
    p22_div_le_div_real_left (by norm_num) (by norm_num) hk1
  have hs2 : ((31416:ℝ)/10000/k)^2 ≤ ((31416:ℝ)/10000/12)^2 :=
    pow_le_pow_left₀ hsp hs 2
  have hτp : (0:ℝ) ≤ (235273:ℝ)/250000*(31416/10000/k) := by positivity
  have hτ : ((235273:ℝ)/250000*(31416/10000/k))^2
      ≤ ((235273:ℝ)/250000*(31416/10000/12))^2 :=
    pow_le_pow_left₀ hτp (mul_le_mul_of_nonneg_left hs (by positivity)) 2
  have hkey : ((270126977:ℝ)/1000000000)^2
      - ((270126977:ℝ)/1000000000)^2 * (((235273:ℝ)/250000)*((31416:ℝ)/10000/12))^2
      ≥ ((31416:ℝ)/10000/12)^2 := by norm_num
  have hφp : (0:ℝ) ≤ ((270126977:ℝ)/1000000000) ^ 2 := by positivity
  have hQ0 : (0:ℝ) ≤ 1 - ((235273:ℝ)/250000*(31416/10000/k))^2 := by nlinarith [hτ]
  nlinarith [hs2, hτ, hkey, hφp, hQ0]

/-- tail slide-budget (k-cancellation): `0.26*2k*C*phi ≤ 0.26*2*C*(31416/10^4)
= 0.4716 ≤ 2*pi - 5.777`. -/
private theorem p22_bjf_tail_mono (k : ℕ) (hk : 12 ≤ k) :
    ((26:ℝ)/100) * (2 * (k:ℝ) * (2887 / 10000) * (270126977 / 1000000000))
      ≤ 2 * Real.pi - 5777 / 1000 := by
  have hπ : (2:ℝ) * Real.pi ≥ 6283 / 1000 := by
    have := Real.pi_gt_d4
    linarith
  have hk1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk
  have hτc : (235273:ℝ) / 250000 * (31416 / 10000) ≤ 149 / 50 := by norm_num
  have hτk : ((235273:ℝ)/250000*(31416/10000/k))^2
      ≤ ((235273:ℝ)/250000*(31416/10000/12))^2 := by
    have hsp : (0:ℝ) ≤ (235273:ℝ)/250000*(31416/10000/k) := by positivity
    refine pow_le_pow_left₀ hsp ?_ 2
    exact mul_le_mul_of_nonneg_left
      (p22_div_le_div_real_left (by norm_num) (by norm_num) hk1) (by positivity)
  have hQ0p : (0:ℝ) < 1 - ((235273:ℝ)/250000*(31416/10000/k))^2 := by nlinarith [hτk]
  have hφk : (270126977:ℝ) / 1000000000
      ≤ (31416:ℝ) / 10000 / k / Real.sqrt
          (1 - ((235273:ℝ) / 250000 * (31416 / 10000 / k)) ^ 2) := by
    refine (Real.le_sqrt (by norm_num) hQ0p).mpr ?_
    rw [div_pow, div_pow, div_div_eq_mul_div, div_div_eq_mul_div]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^2 * (k:ℝ)^2)]
    nlinarith [hk1, hτc, hτk]
  have hcancel : ((26:ℝ)/100) * (2 * (k:ℝ) * (2887 / 10000) * (270126977 / 1000000000))
      ≤ (26:ℝ)/100 * ((2:ℝ) * (2887 / 10000) * (31416 / 10000)) := by
    have h1 : ((2:ℝ) * k * (2887 / 10000)) * ((270126977:ℝ)/1000000000)
        ≤ ((2:ℝ) * k * (2887 / 10000)) * ((31416:ℝ)/10000/k) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [hφk]
    have h2 : ((2:ℝ) * (k:ℝ) * (2887 / 10000)) * ((31416:ℝ)/10000/(k:ℝ))
        = (2:ℝ) * (2887 / 10000) * (31416 / 10000) := by field_simp
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  linarith [hπ, hcancel]

/-- single-piece slide route (`k ≥ 7`): case split `2k*C*phi ≤ LF`; the
LF-dominated case telescopes to 0.506, the other uses the h0-budget `hmono`. -/
private theorem p22_bjf_route1 {k : ℕ} {h sig phi : ℝ} (hh1 : 1 ≤ h) (hh0 : h ≤ h0)
    (hwin : (2:ℝ)*k*asn ((sqrt3/2)*Real.sin (Real.pi/k)) ≤ 5.186 + 0.0331*k)
    (hsin0 : 0 ≤ Real.sin (Real.pi / k)) (hsig : Real.sin (Real.pi / k) ≤ sig)
    (hTb : p22_bjf_T h ≤ 235273 / 250000) (hT0 : 0 ≤ p22_bjf_T h)
    (hQ1 : (235273:ℝ)/250000 * sig < 1)
    (hphi : (1 - (235273 / 250000 * sig) ^ 2) * phi ^ 2 ≥ sig ^ 2) (hphi0 : 0 ≤ phi)
    (hmono : ((126:ℝ)/100 - 1) * (2 * k * (2887 / 10000) * phi) ≤ 2 * Real.pi - 5777 / 1000) :
    (0.591 - 0.0331 * k + 0.506 * lfun h)
      ≤ 2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)) := by
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hpos126 : (0:ℝ) ≤ 126 / 100 - h := by linarith [h126, hh0]
  have hlf : (0.506:ℝ) * lfun h = (253 / 130) * (126 / 100 - h) := by
    have h1 : lfun h = (h0 - h) / (h0 - 1) := rfl
    have h2 : (h0:ℝ) - 1 = 26 / 100 := by rw [h126]; norm_num
    rw [h1, h2, h126]
    field_simp
    norm_num
  have hv1 : 0 ≤ (sqrt3:ℝ)/2 * Real.sin (Real.pi/k) :=
    mul_nonneg (le_trans (by norm_num) p22_bjf_sqrt3_le) hsin0
  have hxy0 := p22_bjf_Tmono (a := 1) (b := h) (le_refl 1) hh1 hh0
  rw [p22_bjf_T1] at hxy0
  have hxy : (sqrt3:ℝ)/2 * Real.sin (Real.pi/k)
      ≤ p22_bjf_T h * Real.sin (Real.pi / k) :=
    mul_le_mul_of_nonneg_right hxy0 hsin0
  have hy1 : p22_bjf_T h * Real.sin (Real.pi/k) < 1 := by
    have h1 : p22_bjf_T h * Real.sin (Real.pi/k) ≤ (235273:ℝ)/250000 * sig :=
      mul_le_mul hTb hsig (by positivity) hT0
    linarith
  have hch1 := p22_bjf_chord hh1 (le_refl h) hh0
  have hS0 : (0:ℝ) ≤ (h - 1) * 2887 / 10000 := by
    have h2 : (0:ℝ) ≤ h - 1 := sub_nonneg.mpr hh1
    exact mul_nonneg h2 (by norm_num)
  have hsub1 : p22_bjf_T h * Real.sin (Real.pi / k)
      - (sqrt3:ℝ)/2 * Real.sin (Real.pi / k)
      ≤ ((h:ℝ) - 1) * 2887 / 10000 * sig := by
    have e0 : p22_bjf_T h * Real.sin (Real.pi / k)
        - (sqrt3:ℝ)/2 * Real.sin (Real.pi / k)
        = (p22_bjf_T h - p22_bjf_T 1) * Real.sin (Real.pi / k) := by ring
    have h1 : (0:ℝ) ≤ p22_bjf_T h - p22_bjf_T 1 := by linarith
    calc (p22_bjf_T h - p22_bjf_T 1) * Real.sin (Real.pi / k)
        ≤ ((h:ℝ) - 1) * 2887 / 10000 * Real.sin (Real.pi / k) :=
          mul_le_mul_of_nonneg_right (by linarith [hch1]) h1
      _ ≤ ((h:ℝ) - 1) * 2887 / 10000 * sig :=
          mul_le_mul_of_nonneg_left hsig (by linarith)
  have hinc := p22_bjf_incle (k := k) (h := h) (x := (sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
    (y := p22_bjf_T h * Real.sin (Real.pi / k)) (sig := sig) (tau := 235273 / 250000)
    (phi := phi) (S := (h - 1) * 2887 / 10000)
    hv1 hxy rfl hT0 hy1 hTb (by norm_num) hsub1 hS0 hsin0 hsig
    (by norm_num) (by norm_num) hphi
  have hπ : (2:ℝ) * Real.pi ≥ 6283 / 1000 := by
    have := Real.pi_gt_d4
    linarith
  have eM : (2:ℝ) * (k:ℝ) * ((h - 1) * 2887 / 10000) * phi
      = (h - 1) * (2 * k * (2887 / 10000) * phi) := by ring
  have hsplit : (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k))
      = 2 * k * asn ((sqrt3 / 2) * Real.sin (Real.pi / k))
        + (2 * (k:ℝ) * (asn (p22_bjf_T h * Real.sin (Real.pi / k))
          - asn ((sqrt3 / 2) * Real.sin (Real.pi / k)))) := by ring
  rw [hlf]
  rcases le_or_lt (2 * k * (2887 / 10000) * phi) (253 / 130) with hc | hc
  · have h5 : (h - 1) * (2 * k * (2887 / 10000) * phi) ≤ (h - 1) * (253 / 130) :=
      mul_le_mul_of_nonneg_left hc (by linarith)
    have e1 : ((h:ℝ) - 1) * (253 / 130) = (253 / 130) * h - 253 / 130 := by ring
    have e2 : (253:ℝ) / 130 * (126 / 100 - h)
        = 253 * 126 / 13000 - (253 / 130) * h := by ring
    have htot : (0.591:ℝ) - 0.0331 * k + (253 / 130) * (126 / 100 - h)
        + (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k)) ≤ 6283 / 1000 := by
      linarith [hsplit, hwin, hinc, eM, h5, e1, e2]
    exact le_trans htot (by linarith)
  · have hLFM : (253:ℝ) / 130 * (126 / 100 - h)
        ≤ (126 / 100 - h) * (2 * k * (2887 / 10000) * phi) := by
      nlinarith [hc, hpos126]
    have e1 : ((126:ℝ) / 100 - h) * (2 * k * (2887 / 10000) * phi)
        + ((h:ℝ) - 1) * (2 * k * (2887 / 10000) * phi)
        = ((126:ℝ) / 100 - 1) * (2 * k * (2887 / 10000) * phi) := by ring
    have htot : (0.591:ℝ) - 0.0331 * k + (253 / 130) * (126 / 100 - h)
        + (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k))
        ≤ (2:ℝ) * Real.pi := by
      linarith [hsplit, hwin, hinc, eM, hLFM, e1, hmono, hπ]
    exact htot

/-- two-piece slide route (`k ∈ {3,4,5,6}`): split `[1,h0]` at `b`; piece 1 on
the global chord with window `ta/phiA`, piece 2 on the `b`-chord with window
`tb/phiB`; endpoint budgets `hX1/hX2`, total budgets `hB/hB506`. -/
private theorem p22_bjf_route2 {k : ℕ} {h b sig ta tb kappa phiA phiB A B : ℝ}
    (hh1 : 1 ≤ h) (hh0 : h ≤ h0) (hb1 : 1 ≤ b) (hbb : b ≤ h0)
    (hwin : (2:ℝ) * k * asn ((sqrt3/2) * Real.sin (Real.pi/k)) ≤ A)
    (hsin0 : 0 ≤ Real.sin (Real.pi / k)) (hsig : Real.sin (Real.pi / k) ≤ sig)
    (hT0 : 0 ≤ p22_bjf_T h) (hT0b : 0 ≤ p22_bjf_T b)
    (hTa : ∀ x : ℝ, 1 ≤ x → x ≤ b → p22_bjf_T x ≤ ta) (hQa : ta * sig < 1)
    (hphiA : (1 - (ta * sig) ^ 2) * phiA ^ 2 ≥ sig ^ 2) (hphiA0 : 0 ≤ phiA)
    (hTb : ∀ x : ℝ, 1 ≤ x → x ≤ h0 → p22_bjf_T x ≤ tb) (hQb : tb * sig < 1)
    (hphiB : (1 - (tb * sig) ^ 2) * phiB ^ 2 ≥ sig ^ 2) (hphiB0 : 0 ≤ phiB)
    (hkappa0 : 0 ≤ kappa)
    (hchorda : ∀ x : ℝ, b ≤ x → x ≤ h0 → p22_bjf_T x - p22_bjf_T b ≤ (x - b) * kappa)
    (hX1 : (253:ℝ)/130*(126/100-b) + (b-1)*(2*k*(2887/10000)*phiA) ≤ B)
    (hX2 : (b-1)*(2*k*(2887/10000)*phiA) + ((126:ℝ)/100-b)*(2*k*kappa*phiB) ≤ B)
    (hB : (0.591 - 0.0331 * k) + A + B ≤ 6283 / 1000)
    (hB506 : (0.591 - 0.0331 * k) + A + 506 / 1000 ≤ 6283 / 1000) :
    (0.591 - 0.0331 * k + 0.506 * lfun h)
      ≤ 2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)) := by
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hpos126 : (0:ℝ) ≤ 126 / 100 - h := by linarith [h126, hh0]
  have hposb : (0:ℝ) ≤ 126 / 100 - b := by linarith [h126, hbb]
  have hlf : (0.506:ℝ) * lfun h = (253 / 130) * (126 / 100 - h) := by
    have h1 : lfun h = (h0 - h) / (h0 - 1) := rfl
    have h2 : (h0:ℝ) - 1 = 26 / 100 := by rw [h126]; norm_num
    rw [h1, h2, h126]
    field_simp
    norm_num
  have hv1 : 0 ≤ (sqrt3:ℝ)/2 * Real.sin (Real.pi/k) :=
    mul_nonneg (le_trans (by norm_num) p22_bjf_sqrt3_le) hsin0
  have hsplit : (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k))
      = 2 * k * asn ((sqrt3 / 2) * Real.sin (Real.pi / k))
        + (2 * (k:ℝ) * (asn (p22_bjf_T b * Real.sin (Real.pi / k))
          - asn ((sqrt3 / 2) * Real.sin (Real.pi / k))))
        + (2 * (k:ℝ) * (asn (p22_bjf_T h * Real.sin (Real.pi / k))
          - asn (p22_bjf_T b * Real.sin (Real.pi / k)))) := by ring
  rw [hlf]
  rcases le_or_lt h b with hcase | hcase
  · -- piece 1: h ∈ [1, b]
    have hTa' : p22_bjf_T h ≤ ta := hTa h hh1 (le_of_lt hcase)
    have hxy0 := p22_bjf_Tmono (a := 1) (b := h) (le_refl 1) hh1 hh0
    rw [p22_bjf_T1] at hxy0
    have hxy : (sqrt3:ℝ)/2 * Real.sin (Real.pi/k)
        ≤ p22_bjf_T h * Real.sin (Real.pi / k) :=
      mul_le_mul_of_nonneg_right hxy0 hsin0
    have hy1 : p22_bjf_T h * Real.sin (Real.pi/k) < 1 := by
      have h1 : p22_bjf_T h * Real.sin (Real.pi/k) ≤ ta * sig :=
        mul_le_mul hTa' hsig (by positivity) hT0
      linarith
    have hch1 := p22_bjf_chord hh1 (le_refl h) hh0
    have hS0 : (0:ℝ) ≤ (h - 1) * 2887 / 10000 := by
      have h2 : (0:ℝ) ≤ h - 1 := sub_nonneg.mpr hh1
      exact mul_nonneg h2 (by norm_num)
    have hsub1 : p22_bjf_T h * Real.sin (Real.pi / k)
        - (sqrt3:ℝ)/2 * Real.sin (Real.pi / k)
        ≤ ((h:ℝ) - 1) * 2887 / 10000 * sig := by
      have e0 : p22_bjf_T h * Real.sin (Real.pi / k)
          - (sqrt3:ℝ)/2 * Real.sin (Real.pi / k)
          = (p22_bjf_T h - p22_bjf_T 1) * Real.sin (Real.pi / k) := by ring
      have h1 : (0:ℝ) ≤ p22_bjf_T h - p22_bjf_T 1 := by linarith
      calc (p22_bjf_T h - p22_bjf_T 1) * Real.sin (Real.pi / k)
          ≤ ((h:ℝ) - 1) * 2887 / 10000 * Real.sin (Real.pi / k) :=
            mul_le_mul_of_nonneg_right (by linarith [hch1]) h1
        _ ≤ ((h:ℝ) - 1) * 2887 / 10000 * sig :=
            mul_le_mul_of_nonneg_left hsig (mul_nonneg (by linarith) (by norm_num))
    have hinc := p22_bjf_incle (k := k) (h := h)
      (x := (sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
      (y := p22_bjf_T h * Real.sin (Real.pi / k)) (sig := sig) (tau := ta)
      (phi := phiA) (S := (h - 1) * 2887 / 10000)
      hv1 hxy rfl hT0 hy1 hTa' (by norm_num) hsub1 hS0 hsin0 hsig
      (by norm_num) (by norm_num) hphiA
    have eM : (2:ℝ) * (k:ℝ) * ((h - 1) * 2887 / 10000) * phiA
        = (h - 1) * (2 * k * (2887 / 10000) * phiA) := by ring
    rcases le_or_lt (2 * k * (2887 / 10000) * phiA) (253 / 130) with hcm | hcm
    · have hL1 : (253:ℝ)/130*(126/100-h) ≤ ((126:ℝ)/100-h)*(253/130) := by
        nlinarith [hpos126]
      have hL2 : (h - 1) * (2 * k * (2887 / 10000) * phiA) ≤ (h - 1) * (253 / 130) :=
        mul_le_mul_of_nonneg_left hcm (by linarith)
      have e2 : ((126:ℝ)/100-h)*(253/130) + ((h:ℝ)-1)*(253/130)
          = ((126:ℝ)/100-1)*(253/130) := by ring
      have h506 : ((126:ℝ)/100-1)*(253/130) = 506/1000 := by rw [h126]; norm_num
      have htot : (0.591:ℝ) - 0.0331 * k + (253 / 130) * (126 / 100 - h)
          + (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k)) ≤ 6283 / 1000 := by
        linarith [hsplit, hwin, hinc, eM, hL1, hL2, e2, h506, hB506]
      exact htot
    · have hL2 : (h - 1) * (2 * k * (2887 / 10000) * phiA)
        ≤ (b - 1) * (2 * k * (2887 / 10000) * phiA) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have htot : (0.591:ℝ) - 0.0331 * k + (253 / 130) * (126 / 100 - h)
          + (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k)) ≤ 6283 / 1000 := by
        linarith [hsplit, hwin, hinc, eM, hL2, hX1, hB]
      exact htot
  · -- piece 2: h ∈ [b, h0]
    have hbh : (b:ℝ) ≤ h := le_of_lt hcase
    have hTmono' : p22_bjf_T b ≤ p22_bjf_T h := p22_bjf_Tmono hb1 hbh hh0
    have hxya0 := p22_bjf_Tmono (a := 1) (b := b) (le_refl 1) hb1 hbb
    rw [p22_bjf_T1] at hxya0
    have hxya : (sqrt3:ℝ)/2 * Real.sin (Real.pi/k)
        ≤ p22_bjf_T b * Real.sin (Real.pi / k) :=
      mul_le_mul_of_nonneg_right hxya0 hsin0
    have hxyb : p22_bjf_T b * Real.sin (Real.pi/k)
        ≤ p22_bjf_T h * Real.sin (Real.pi / k) :=
      mul_le_mul_of_nonneg_right hTmono' hsin0
    have hTb' : p22_bjf_T b ≤ ta := hTa b hb1 (le_refl _)
    have hTh' : p22_bjf_T h ≤ tb := hTb h hh1 hh0
    have hchorda'' := p22_bjf_chord hb1 (le_refl b) hbb
    have hya : p22_bjf_T b * Real.sin (Real.pi/k) < 1 := by
      have h1 : p22_bjf_T b * Real.sin (Real.pi/k) ≤ ta * sig :=
        mul_le_mul hTb' hsig (by positivity) hT0b
      linarith
    have hyb : p22_bjf_T h * Real.sin (Real.pi/k) < 1 := by
      have h1 : p22_bjf_T h * Real.sin (Real.pi/k) ≤ tb * sig :=
        mul_le_mul hTh' hsig (by positivity) hT0
      linarith
    have hS0b : (0:ℝ) ≤ (b - 1) * 2887 / 10000 := by
      have h2 : (0:ℝ) ≤ b - 1 := sub_nonneg.mpr hb1
      exact mul_nonneg h2 (by norm_num)
    have hsub1b : p22_bjf_T b * Real.sin (Real.pi / k)
        - (sqrt3:ℝ)/2 * Real.sin (Real.pi / k)
        ≤ ((b:ℝ) - 1) * 2887 / 10000 * sig := by
      have e0 : p22_bjf_T b * Real.sin (Real.pi / k)
          - (sqrt3:ℝ)/2 * Real.sin (Real.pi / k)
          = (p22_bjf_T b - p22_bjf_T 1) * Real.sin (Real.pi / k) := by ring
      have h1 : (0:ℝ) ≤ p22_bjf_T b - p22_bjf_T 1 := by linarith
      calc (p22_bjf_T b - p22_bjf_T 1) * Real.sin (Real.pi / k)
          ≤ ((b:ℝ) - 1) * 2887 / 10000 * Real.sin (Real.pi / k) :=
            mul_le_mul_of_nonneg_right (by linarith [hchorda'']) h1
        _ ≤ ((b:ℝ) - 1) * 2887 / 10000 * sig :=
            mul_le_mul_of_nonneg_left hsig (mul_nonneg (by linarith) (by norm_num))
    have hS2 : (0:ℝ) ≤ (h - b) * kappa :=
      mul_nonneg (by linarith) hkappa0
    have hsub2 : p22_bjf_T h * Real.sin (Real.pi / k)
        - p22_bjf_T b * Real.sin (Real.pi / k) ≤ ((h:ℝ) - b) * kappa * sig := by
      have e0 : p22_bjf_T h * Real.sin (Real.pi / k)
          - p22_bjf_T b * Real.sin (Real.pi / k)
          = (p22_bjf_T h - p22_bjf_T b) * Real.sin (Real.pi / k) := by ring
      rw [e0]
      have h1 : (0:ℝ) ≤ p22_bjf_T h - p22_bjf_T b := by linarith
      calc (p22_bjf_T h - p22_bjf_T b) * Real.sin (Real.pi / k)
          ≤ ((h:ℝ) - b) * kappa * Real.sin (Real.pi / k) :=
            mul_le_mul_of_nonneg_right (hchorda h hbh hh0) h1
        _ ≤ ((h:ℝ) - b) * kappa * sig :=
            mul_le_mul_of_nonneg_left hsig (mul_nonneg (by linarith) hkappa0)
    have hinc1 := p22_bjf_incle (k := k) (h := b)
      (x := (sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
      (y := p22_bjf_T b * Real.sin (Real.pi / k)) (sig := sig) (tau := ta)
      (phi := phiA) (S := (b - 1) * 2887 / 10000)
      hv1 hxya rfl hT0b hya hTb' (by norm_num) hsub1b hS0b hsin0 hsig
      (by norm_num) (by norm_num) hphiA
    have hinc2 := p22_bjf_incle (k := k) (h := h)
      (x := p22_bjf_T b * Real.sin (Real.pi / k))
      (y := p22_bjf_T h * Real.sin (Real.pi / k)) (sig := sig) (tau := tb)
      (phi := phiB) (S := (h - b) * kappa)
      (by linarith) hxyb rfl hT0 hyb hTh' (by norm_num) hsub2 hS2
      hsin0 hsig (by norm_num) (by norm_num) (by norm_num) hphiB
    have eMb : (2:ℝ) * (k:ℝ) * ((b - 1) * 2887 / 10000) * phiA
        = (b - 1) * (2 * k * (2887 / 10000) * phiA) := by ring
    rcases le_or_lt (2 * k * kappa * phiB) (253 / 130) with hc2 | hc2
    · have hL1 : (253:ℝ)/130*(126/100-h) ≤ ((126:ℝ)/100-h)*(2*k*kappa*phiB) := by
        nlinarith [hc2, hpos126]
      have e3 : ((126:ℝ)/100-h)*(2*k*kappa*phiB) + ((h:ℝ)-b)*(2*k*kappa*phiB)
          = ((126:ℝ)/100-b)*(2*k*kappa*phiB) := by ring
      have h1 : (2:ℝ) * k * asn (p22_bjf_T b * Real.sin (Real.pi / k))
          - 2 * k * asn ((sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
          ≤ (b - 1) * (2 * k * (2887 / 10000) * phiA) := by linarith [hinc1, eMb]
      have htot : (0.591:ℝ) - 0.0331 * k + (253 / 130) * (126 / 100 - h)
          + (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k)) ≤ 6283 / 1000 := by
        linarith [hsplit, hwin, hinc2, h1, hL1, e3, hX1, hB]
      exact htot
    · have hL1 : (253:ℝ)/130*(126/100-h) ≤ ((126:ℝ)/100-h)*(2*k*kappa*phiB) := by
        nlinarith [hc2, hpos126]
      have h1 : (2:ℝ) * k * asn (p22_bjf_T b * Real.sin (Real.pi / k))
          - 2 * k * asn ((sqrt3:ℝ)/2 * Real.sin (Real.pi/k))
          ≤ (b - 1) * (2 * k * (2887 / 10000) * phiA) := by linarith [hinc1, eMb]
      have htot : (0.591:ℝ) - 0.0331 * k + (253 / 130) * (126 / 100 - h)
          + (2:ℝ) * k * asn (p22_bjf_T h * Real.sin (Real.pi / k)) ≤ 6283 / 1000 := by
        linarith [hsplit, hwin, hinc2, h1, hL1, hX2, hB]
      exact htot
'''

print("REST written (route2 piece2 to be completed)")

WTAYLOR = r'''/-- Taylor-5 upper bound for `sin(pi/k)` with `pi ∈ (3.1415, 3.1416)`. -/
private theorem p22_bjf_wtaylor {k : ℕ} (hk4 : 4 ≤ k) :
    Real.sin (Real.pi / k)
      ≤ (31416:ℝ)/10000/k - (((31415:ℝ)/10000/k) ^ 3) / 6
        + (((31416:ℝ)/10000/k) ^ 5) / 120 := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by norm_num) hk4
  have hy0 : 0 ≤ Real.pi / k := div_nonneg Real.pi_pos.le hkpos.le
  have hyU : Real.pi / k ≤ (31416:ℝ)/10000/k :=
    p22_div_le_div_nat_right hkpos (by linarith [Real.pi_lt_d4])
  have hyL : (31415:ℝ)/10000/k ≤ Real.pi / k :=
    p22_div_le_div_nat_right hkpos (by linarith [Real.pi_gt_d4])
  have hy4 : Real.pi / k ≤ 4 := by
    have h1 : Real.pi / k ≤ (31416:ℝ)/10000/4 := by
      refine le_trans hyU ?_
      exact p22_div_le_div_nat_left (by norm_num) (by norm_num) hk4
    linarith
  have hsin := p22_sin_le_taylor5 hy0 hy4
  have h30 : (0:ℝ) ≤ (31415:ℝ)/10000/k := div_nonneg (by norm_num) hkpos.le
  have hpi3 : ((31415:ℝ)/10000/k) ^ 3 ≤ (Real.pi / k) ^ 3 := by
    refine pow_le_pow_left₀ h30 ?_ 3
    exact hyL
  have hpi5 : (Real.pi / k) ^ 5 ≤ ((31416:ℝ)/10000/k) ^ 5 := by
    refine pow_le_pow_left₀ hy0 ?_ 5
    exact p22_div_le_div_nat_right hkpos (by linarith [Real.pi_lt_d4])
  linarith

'''

W3 = r'''/-- k=3 window (w = 3/4 exactly; septic majorant at `w² = 9/16 ≤ 7/10`). -/
private theorem p22_bjf_w3 :
    (2:ℝ)*3*asn ((sqrt3/2)*Real.sin (Real.pi/3)) ≤ 5.1501 := by
  have hsin : Real.sin (Real.pi/3) = Real.sqrt 3/2 := Real.sin_pi_div_three
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/3) = (3:ℝ)/4 := by
    unfold sqrt3
    rw [hsin]
    have h := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
    field_simp
    linarith [h]
  have hle : asn ((3:ℝ)/4) ≤ (3:ℝ)/4 + ((3:ℝ)/4)^3/6 + ((3:ℝ)/4)^5/10
      + 3*((3:ℝ)/4)^7/28 :=
    p22_bjf_asn_sept (by norm_num) (by norm_num)
  rw [hv]
  refine le_trans (mul_le_mul_of_nonneg_left hle (by norm_num)) ?_
  norm_num

'''

W4 = r'''/-- 5-term polynomial monotonicity for the ser4 window step. -/
private theorem p22_bjf_ser4_mono {u v : ℝ} (h0 : 0 ≤ u) (huv : u ≤ v) :
    u + u ^ 3 / 6 + 3 * u ^ 5 / 40 + 5 * u ^ 7 / 112 + 7 * u ^ 9 / 144
      ≤ v + v ^ 3 / 6 + 3 * v ^ 5 / 40 + 5 * v ^ 7 / 112 + 7 * v ^ 9 / 144 := by
  have h3 : u ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ h0 huv 3
  have h5 : u ^ 5 ≤ v ^ 5 := pow_le_pow_left₀ h0 huv 5
  have h7 : u ^ 7 ≤ v ^ 7 := pow_le_pow_left₀ h0 huv 7
  have h9 : u ^ 9 ≤ v ^ 9 := pow_le_pow_left₀ h0 huv 9
  have p5 : (3:ℝ) * u ^ 5 ≤ 3 * v ^ 5 := mul_le_mul_of_nonneg_left h5 (by norm_num)
  have p7 : (5:ℝ) * u ^ 7 ≤ 5 * v ^ 7 := mul_le_mul_of_nonneg_left h7 (by norm_num)
  have p9 : (7:ℝ) * u ^ 9 ≤ 7 * v ^ 9 := mul_le_mul_of_nonneg_left h9 (by norm_num)
  refine add_le_add (add_le_add (add_le_add (add_le_add huv
    (p22_div_le_div_right (by norm_num) h3))
    (p22_div_le_div_right (by norm_num) p5))
    (p22_div_le_div_right (by norm_num) p7))
    (p22_div_le_div_right (by norm_num) p9)

/-- k=4 window (w = √6/4; arcsin series bound with 9th-order tail). -/
private theorem p22_bjf_w4 :
    (2:ℝ)*4*asn ((sqrt3/2)*Real.sin (Real.pi/4)) ≤ 5.2734 := by
  have hsin4 : Real.sin (Real.pi/4) = Real.sqrt 2/2 := Real.sin_pi_div_four
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/4) = Real.sqrt 6/4 := by
    unfold sqrt3
    rw [hsin4]
    have h6 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
      norm_num
    calc Real.sqrt 3 / 2 * (Real.sqrt 2 / 2) = Real.sqrt 3 * Real.sqrt 2 / 4 := by ring
      _ = Real.sqrt 6 / 4 := by rw [h6]
  have hvle : Real.sqrt 6/4 ≤ 6124/10000 := by
    have he : (Real.sqrt 6/4)^2 = 3/8 := by
      have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
      have e1 : (Real.sqrt 6/4)^2 = Real.sqrt 6 * Real.sqrt 6 / 4 ^ 2 := by ring
      rw [e1, h6]; norm_num
    have hsq : (Real.sqrt 6/4)^2 ≤ (6124/10000)^2 := by rw [he]; norm_num
    have h2' : Real.sqrt 6/4 ≤ Real.sqrt ((6124/10000)^2) := Real.le_sqrt_of_sq_le hsq
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 6124/10000)] at h2'
    exact h2'
  have hw0 : (0:ℝ) ≤ Real.sqrt 6/4 := by positivity
  have hwu : (Real.sqrt 6 / 4) ^ 2 ≤ 3/8 := by
    have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
    have he : (Real.sqrt 6 / 4) ^ 2 = Real.sqrt 6 * Real.sqrt 6 / 4 ^ 2 := by ring
    rw [he, h6]
    norm_num
  have hle : asn (Real.sqrt 6/4) ≤ Real.sqrt 6/4 + (Real.sqrt 6/4)^3/6
      + 3*(Real.sqrt 6/4)^5/40 + 5*(Real.sqrt 6/4)^7/112 + 7*(Real.sqrt 6/4)^9/144 :=
    p22_bjf_asn_ser4 hw0 hwu
  have hstep := p22_bjf_ser4_mono (u := Real.sqrt 6/4) (v := (6124:ℝ)/10000) hw0 hvle
  rw [hv]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hle hstep) (by norm_num)) ?_
  norm_num

'''

def wgen(n, A):
    return f'''/-- k={n} window (Taylor sigma, quadratic majorant). -/
private theorem p22_bjf_w{n} :
    (2:ℝ)*{n}*asn ((sqrt3/2)*Real.sin (Real.pi/{n})) ≤ {A} := by
  have hsig : Real.sin (Real.pi/{n})
      ≤ (31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
        + (((31416:ℝ)/10000/{n}) ^ 5) / 120 :=
    p22_bjf_wtaylor (by norm_num)
  have hsqrt : (sqrt3:ℝ)/2 ≤ 8661/10000 := p22_bjf_sqrt3_half2
  have hsqrt0 : (0:ℝ) ≤ sqrt3 / 2 := by unfold sqrt3; positivity
  have hsig0 : (0:ℝ) ≤ (31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
      + (((31416:ℝ)/10000/{n}) ^ 5) / 120 := by norm_num
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/{n})
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
        + (((31416:ℝ)/10000/{n}) ^ 5) / 120) := by
    have hstep1 : (sqrt3:ℝ)/2*Real.sin (Real.pi/{n})
        ≤ (sqrt3:ℝ)/2*((31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
          + (((31416:ℝ)/10000/{n}) ^ 5) / 120) :=
      mul_le_mul_of_nonneg_left hsig hsqrt0
    have hstep2 : (sqrt3:ℝ)/2*((31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
        + (((31416:ℝ)/10000/{n}) ^ 5) / 120)
        ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
          + (((31416:ℝ)/10000/{n}) ^ 5) / 120) :=
      mul_le_mul_of_nonneg_right hsqrt hsig0
    exact le_trans hstep1 hstep2
  have hw0 : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/{n}) :=
    mul_nonneg hsqrt0 (p22_bjf_sinpos (by norm_num))
  have hB : Real.sin (Real.pi/{n}) ≤ (31416:ℝ)/10000/{n} :=
    le_trans hsig (by
      have hpos5 : (0:ℝ) ≤ (((31416:ℝ)/10000/{n}) ^ 5) := by positivity
      have hpos3 : (0:ℝ) ≤ (((31415:ℝ)/10000/{n}) ^ 3) := by positivity
      linarith)
  have h2l : (sqrt3:ℝ)/2*Real.sin (Real.pi/{n})
      ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/{n}) := by
    have hB2 : (sqrt3:ℝ)/2*((31416:ℝ)/10000/{n})
        ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/{n}) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    calc (sqrt3:ℝ)/2*Real.sin (Real.pi/{n})
        ≤ (sqrt3:ℝ)/2*((31416:ℝ)/10000/{n}) := mul_le_mul_of_nonneg_left hB hsqrt0
      _ ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/{n}) := hB2
  have hgd : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/{n}) := by positivity
  have hk1 : (({n}:ℝ)) ≥ 5 := by norm_num
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/{n}))^2 ≤ 17/64 := by
    have h1 : ((sqrt3:ℝ)/2*Real.sin (Real.pi/{n}))^2
        ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/{n}))^2 := pow_le_pow_left₀ hw0 h2l 2
    have h2 : ((8661:ℝ)/10000*((31416:ℝ)/10000/{n}))^2
        ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/5))^2 :=
      pow_le_pow_left₀ hgd (p22_div_le_div_real_left (by positivity) (by norm_num) hk1) 2
    have h3' : ((8661:ℝ)/10000*((31416:ℝ)/10000/5))^2 ≤ 17/64 := by norm_num
    linarith
  have hle := p22_bjf_asn_quad hw0 hwu
  have h3 : ((sqrt3:ℝ)/2*Real.sin (Real.pi/{n}))^3
      ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
        + (((31416:ℝ)/10000/{n}) ^ 5) / 120))^3 := pow_le_pow_left₀ hw0 hv 3
  have h5 : ((sqrt3:ℝ)/2*Real.sin (Real.pi/{n}))^5
      ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/{n} - (((31415:ℝ)/10000/{n}) ^ 3) / 6
        + (((31416:ℝ)/10000/{n}) ^ 5) / 120))^5 := pow_le_pow_left₀ hw0 hv 5
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hle
    (add_le_add (add_le_add hv (p22_div_le_div_right (by norm_num) h3))
      (p22_div_le_div_right (by norm_num) h5))) (by norm_num)) ?_
  norm_num

'''

WTAIL = r'''/-- tail window (`k ≥ 12`): `2k*asn(w0) ≤ 5.5367` via the quadratic majorant
and `w0 ≤ 8661/10^4*31416/10^4/k`, the k-terms maximized at `k = 12`. -/
private theorem p22_bjf_wtail {k : ℕ} (hk : 12 ≤ k) :
    (2:ℝ)*k*asn ((sqrt3/2)*Real.sin (Real.pi/k)) ≤ 5.5367 := by
  have hsqrt0 : (0:ℝ) ≤ sqrt3 / 2 := by unfold sqrt3; positivity
  have hw0 : (0:ℝ) ≤ (sqrt3:ℝ)/2*Real.sin (Real.pi/k) :=
    mul_nonneg hsqrt0 (p22_bjf_sinpos
      (by exact_mod_cast lt_of_lt_of_le (by norm_num) hk))
  have hv : (sqrt3:ℝ)/2*Real.sin (Real.pi/k) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/k) := by
    have hstep1 : (sqrt3:ℝ)/2*Real.sin (Real.pi/k)
        ≤ (sqrt3:ℝ)/2*((31416:ℝ)/10000/k) :=
      mul_le_mul_of_nonneg_left
        (p22_div_le_div_nat_right (by exact_mod_cast lt_of_lt_of_le (by norm_num) hk)
          (le_trans Real.sin_le_one (by norm_num) : (0:ℝ) < (31416:ℝ)/10000)
          ) hsqrt0
    have hstep2 : (sqrt3:ℝ)/2*((31416:ℝ)/10000/k)
        ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/k) :=
      mul_le_mul_of_nonneg_right p22_bjf_sqrt3_half2 (by positivity)
    exact le_trans hstep1 hstep2
  have hk1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk
  have hk2 : ((k:ℝ))^2 ≥ 144 := by nlinarith [hk1]
  have hgd : (0:ℝ) ≤ (8661:ℝ)/10000*((31416:ℝ)/10000/k) := by positivity
  have hwu : ((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^2 ≤ 17/64 := by
    have h1 : ((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^2
        ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/k))^2 := pow_le_pow_left₀ hw0 hv 2
    have h2 : ((8661:ℝ)/10000*((31416:ℝ)/10000/k))^2
        ≤ ((8661:ℝ)/10000*(31416:ℝ)/10000/12)^2 :=
      pow_le_pow_left₀ hgd (p22_div_le_div_real_left (by positivity) (by norm_num) hk1) 2
    have h3' : ((8661:ℝ)/10000*(31416:ℝ)/10000/12)^2 ≤ 17/64 := by norm_num
    linarith
  have hle := p22_bjf_asn_quad hw0 hwu
  have h3 : ((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^3
      ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/k))^3 := pow_le_pow_left₀ hw0 hv 3
  have h5 : ((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^5
      ≤ ((8661:ℝ)/10000*((31416:ℝ)/10000/k))^5 := pow_le_pow_left₀ hw0 hv 5
  have hv1 : (2:ℝ)*k*((sqrt3:ℝ)/2*Real.sin (Real.pi/k))
      ≤ (8661:ℝ)/10000*(31416:ℝ)/10000*2 := by
    have h := mul_le_mul_of_nonneg_left hv (by positivity)
    calc (2:ℝ)*k*((sqrt3:ℝ)/2*Real.sin (Real.pi/k))
        ≤ (2:ℝ)*k*((8661:ℝ)/10000*((31416:ℝ)/10000/k)) := h
      _ = (8661:ℝ)/10000*(31416:ℝ)/10000*2 := by ring
  have hterm3 : (2:ℝ)*k*(((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^3/6)
      ≤ (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
        *(8661:ℝ)/10000*(31416:ℝ)/10000/3/144 := by
    have hstep : (2:ℝ)*k*(((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^3/6)
        ≤ (2:ℝ)*k*(((8661:ℝ)/10000*((31416:ℝ)/10000/k))^3/6) :=
      mul_le_mul_of_nonneg_left (p22_div_le_div_right (by norm_num) h3) (by positivity)
    have hp : (2:ℝ)*k*(((8661:ℝ)/10000*((31416:ℝ)/10000/k))^3/6)
        = (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
          *(8661:ℝ)/10000*(31416:ℝ)/10000/3/((k:ℝ)^2) := by ring
    calc (2:ℝ)*k*(((8661:ℝ)/10000*((31416:ℝ)/10000/k))^3/6)
        = (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
          *(8661:ℝ)/10000*(31416:ℝ)/10000/3/((k:ℝ)^2) := hp
      _ ≤ (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
            *(8661:ℝ)/10000*(31416:ℝ)/10000/3/144 := by
          refine p22_div_le_div_real_left (by positivity) (by positivity) hk2
  have hk4 : ((k:ℝ))^4 ≥ 20736 := by nlinarith [hk2]
  have hterm5 : (2:ℝ)*k*(((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^5/10)
      ≤ (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
        *((8661:ℝ)/10000*(31416:ℝ)/10000)*(8661:ℝ)/10000*(31416:ℝ)/10000*(1/5)/20736 := by
    have hstep : (2:ℝ)*k*(((sqrt3:ℝ)/2*Real.sin (Real.pi/k))^5/10)
        ≤ (2:ℝ)*k*(((8661:ℝ)/10000*((31416:ℝ)/10000/k))^5/10) :=
      mul_le_mul_of_nonneg_left (p22_div_le_div_right (by norm_num) h5) (by positivity)
    have hp : (2:ℝ)*k*(((8661:ℝ)/10000*((31416:ℝ)/10000/k))^5/10)
        = (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
          *((8661:ℝ)/10000*(31416:ℝ)/10000)*(8661:ℝ)/10000*(31416:ℝ)/10000
          *(1/5)/((k:ℝ)^4) := by ring
    calc (2:ℝ)*k*(((8661:ℝ)/10000*((31416:ℝ)/10000/k))^5/10)
        = (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
          *((8661:ℝ)/10000*(31416:ℝ)/10000)*(8661:ℝ)/10000*(31416:ℝ)/10000
          *(1/5)/((k:ℝ)^4) := hp
      _ ≤ (8661:ℝ)/10000*(31416:ℝ)/10000*(8661:ℝ)/10000*(31416:ℝ)/10000
            *((8661:ℝ)/10000*(31416:ℝ)/10000)*(8661:ℝ)/10000*(31416:ℝ)/10000
            *(1/5)/20736 := by
          refine p22_div_le_div_real_left (by positivity) (by positivity) hk4
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hle
    (add_le_add hv (add_le_add (p22_div_le_div_right (by norm_num) h3)
      (p22_div_le_div_right (by norm_num) h5)))) (by positivity)) ?_
  linarith [hv1, hterm3, hterm5]

'''

def pack2gen(K, b, sig, ta, phiA, kap, tb, phiB, B, r):
    A = A_VAL[K]
    if K == 3:
        hsig = r'''  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsig : Real.sin (Real.pi/3) ≤ (8661:ℝ)/10000 := by
    rw [Real.sin_pi_div_three]
    refine (Real.le_sqrt (by positivity) (by norm_num)).mpr ?_
    have he : (Real.sqrt 3 / 2)^2 = 3/4 := by
      have e1 : (Real.sqrt 3 / 2)^2 = Real.sqrt 3 * Real.sqrt 3 / 4 := by ring
      rw [e1, hsq3]; norm_num
    rw [he]; norm_num'''
    elif K == 4:
        hsig = r'''  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsig : Real.sin (Real.pi/4) ≤ (7072:ℝ)/10000 := by
    rw [Real.sin_pi_div_four]
    refine (Real.le_sqrt (by positivity) (by norm_num)).mpr ?_
    have he : (Real.sqrt 2 / 2)^2 = 1/2 := by
      have e1 : (Real.sqrt 2 / 2)^2 = Real.sqrt 2 * Real.sqrt 2 / 4 := by ring
      rw [e1, hsq2]; norm_num
    rw [he]; norm_num'''
    elif K == 5:
        hsig = r'''  have hsig : Real.sin (Real.pi/5)
      ≤ (31416:ℝ)/10000/5 - (((31415:ℝ)/10000/5) ^ 3) / 6
        + (((31416:ℝ)/10000/5) ^ 5) / 120 :=
    p22_bjf_wtaylor (by norm_num)'''
    else:
        hsig = r'''  have hsig : Real.sin (Real.pi/6) ≤ (1:ℝ)/2 := by
    rw [Real.sin_pi_div_six]; norm_num'''
    return f'''/-- k={K} pack: route2 with split `b = {b}`; sigma, Phi-windows and slide
budgets are the exact-rational-verified certificates. -/
private theorem p22_bjf_pack{K} (h : ℝ) (hh1 : 1 ≤ h) (hh0 : h ≤ h0) :
    (0.591 - 0.0331 * {K} + 0.506 * lfun h)
      ≤ 2 * Real.pi - 2 * ({K}:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / {K})) := by
  have hs4 : (sqrt3:ℝ)/4 ≤ 4331 / 10000 := p22_bjf_sqrt3_quarter
  have hrc : Real.sqrt (1 - (({b}:ℝ) / 2) ^ 2) ≤ {r} :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hcle : sqrt3 / 4 - ({b}:ℝ) / (8 * {r}) ≤ {kap} := by
    have hnum : (4331:ℝ)/10000 - ({b}:ℝ)/(8*{r}) ≤ {kap} := by norm_num
    linarith [hs4, hnum]
  have hwin : (2:ℝ) * {K} * asn ((sqrt3/2)*Real.sin (Real.pi/{K})) ≤ {A} := by
    refine le_trans (p22_bjf_w{K}) ?_
    norm_num
  have hT0nn : 0 ≤ p22_bjf_T h := by unfold p22_bjf_T sqrt3; positivity
  have hT0bnn : 0 ≤ p22_bjf_T ({b}:ℝ) := by unfold p22_bjf_T sqrt3; positivity
  have hTa : ∀ x : ℝ, 1 ≤ x → x ≤ ({b}:ℝ) → p22_bjf_T x ≤ {ta} := by
    intro x hx1 hxb
    have hch := p22_bjf_chord hx1 (le_trans hx1 hxb) hxb
    have hT1 : p22_bjf_T 1 = sqrt3 / 2 := p22_bjf_T1
    have hs := p22_bjf_sqrt3_half
    have hxC : ((x:ℝ) - 1) * 2887 / 10000 ≤ (({b}:ℝ) - 1) * 2887 / 10000 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    calc p22_bjf_T x ≤ sqrt3 / 2 + ((x:ℝ) - 1) * 2887 / 10000 := by linarith [hch, hT1]
      _ ≤ 86603 / 100000 + (({b}:ℝ) - 1) * 2887 / 10000 := by linarith [hs, hxC]
      _ ≤ {ta} := by norm_num
  have hTb : ∀ x : ℝ, 1 ≤ x → x ≤ h0 → p22_bjf_T x ≤ {tb} := by
    intro x hx1 hx2
    rcases le_or_lt x ({b}:ℝ) with hxb | hxb
    · have hxa := hTa x hx1 hxb
      linarith
    · have hchb := p22_bjf_chord_b (a := ({b}:ℝ)) (b := x) (r := {r}) (kappa := {kap})
        hx1 hxb hx2 hrc (by norm_num) hcle
      have hTbu := hTa ({b}:ℝ) (by norm_num) (le_refl _)
      have hxC : ((x:ℝ) - {b}) * {kap} ≤ ((h0:ℝ) - {b}) * {kap} :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      calc p22_bjf_T x ≤ p22_bjf_T ({b}:ℝ) + ((x:ℝ) - {b}) * {kap} := by linarith [hchb]
        _ ≤ {tb} := by linarith [hTbu, hxC]
  have hchorda : ∀ x : ℝ, ({b}:ℝ) ≤ x → x ≤ h0 →
      p22_bjf_T x - p22_bjf_T ({b}:ℝ) ≤ (x - ({b}:ℝ)) * {kap} := by
    intro x hxb hx2
    exact p22_bjf_chord_b (a := ({b}:ℝ)) (b := x) (r := {r}) (kappa := {kap})
      hxb hxb hx2 hrc (by norm_num) hcle
{hsig}
  exact p22_bjf_route2 (k := {K}) (h := h) (b := ({b}:ℝ)) (sig := {sig})
    (ta := ({ta}:ℝ)) (tb := ({tb}:ℝ)) (kappa := ({kap}:ℝ)) (phiA := ({phiA}:ℝ))
    (phiB := ({phiB}:ℝ)) (A := {A}) (B := {B})
    hh1 hh0 (by norm_num) hh0 hwin (p22_bjf_sinpos (by norm_num)) hsig
    hT0nn hT0bnn hTa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hTb (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hchorda (by norm_num) (by norm_num) (by norm_num) (by norm_num)

'''

def pack1gen(K, phi):
    return f'''/-- k={K} pack: route1 with the Taylor sigma window and exact Phi budget. -/
private theorem p22_bjf_pack{K} (h : ℝ) (hh1 : 1 ≤ h) (hh0 : h ≤ h0) :
    (0.591 - 0.0331 * {K} + 0.506 * lfun h)
      ≤ 2 * Real.pi - 2 * ({K}:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / {K})) := by
  have hT0nn : 0 ≤ p22_bjf_T h := by unfold p22_bjf_T sqrt3; positivity
  have hsig : Real.sin (Real.pi/{K})
      ≤ (31416:ℝ)/10000/{K} - (((31415:ℝ)/10000/{K}) ^ 3) / 6
        + (((31416:ℝ)/10000/{K}) ^ 5) / 120 :=
    p22_bjf_wtaylor (by norm_num)
  refine p22_bjf_route1 (k := {K}) (h := h) (sig := (31416:ℝ)/10000/{K}
    - (((31415:ℝ)/10000/{K}) ^ 3) / 6 + (((31416:ℝ)/10000/{K}) ^ 5) / 120)
    (phi := {phi}) hh1 hh0 ?_ (p22_bjf_sinpos (by norm_num)) hsig
    (p22_bjf_hTbound hh1 hh0) (by unfold p22_bjf_T sqrt3; positivity)
    (by norm_num) (by norm_num) (by norm_num) ?_
  · refine le_trans (p22_bjf_w{K}) ?_
    norm_num
  · have h1 : ((126:ℝ)/100 - 1) * (2 * ({K}:ℝ) * (2887 / 10000) * {phi}) ≤ 506 / 1000 := by
      norm_num
    have hpi : (2:ℝ) * Real.pi ≥ 6283 / 1000 := by linarith [Real.pi_gt_d4]
    linarith
'''

ASSEMBLY = r'''/-- HOL `BIEFJHU_explicit` (counting_spheres.hl:965).  Filled (PA22g wave) via
the corrected interior-worst-point route: piecewise chord/Phi-window slide on
`[1, h0]` (`p22_bjf_route2`, `k ∈ {3,4,5,6}`), single-piece slide
(`p22_bjf_route1`, `k ≥ 7`), polynomial `k`-windows (`w3..w11`, `wtail`), tail
by k-cancellation (`tail_phi`/`tail_mono`). -/
theorem BIEFJHU_explicit (h : ℝ) (k : ℕ) (hpa : packIneqDefAP22)
    (hh : 1 ≤ h ∧ h ≤ h0) (hk : 3 ≤ k) :
    (0.591 - 0.0331 * k + 0.506 * lfun h) ≤
      max 0 (regularSphericalPolygonAreaP22
        (h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2) k) := by
  show (0.591 - 0.0331 * k + 0.506 * lfun h) ≤
      max 0 (2 * Real.pi - 2 * (k:ℝ) * asn (p22_bjf_T h * Real.sin (Real.pi / k)))
  rcases Nat.lt_or_ge k 7 with hk7 | hk7
  · interval_cases k
    · exact le_trans (p22_bjf_pack3 h hh.1 hh.2) (le_max_left _ _)
    · exact le_trans (p22_bjf_pack4 h hh.1 hh.2) (le_max_left _ _)
    · exact le_trans (p22_bjf_pack5 h hh.1 hh.2) (le_max_left _ _)
    · exact le_trans (p22_bjf_pack6 h hh.1 hh.2) (le_max_left _ _)
  · rcases Nat.lt_or_ge k 12 with hk11 | hk12
    · interval_cases k
      · exact le_trans (p22_bjf_pack7 h hh.1 hh.2) (le_max_left _ _)
      · exact le_trans (p22_bjf_pack8 h hh.1 hh.2) (le_max_left _ _)
      · exact le_trans (p22_bjf_pack9 h hh.1 hh.2) (le_max_left _ _)
      · exact le_trans (p22_bjf_pack10 h hh.1 hh.2) (le_max_left _ _)
      · exact le_trans (p22_bjf_pack11 h hh.1 hh.2) (le_max_left _ _)
    · refine le_trans ?_ (le_max_left _ _)
      have hsig : Real.sin (Real.pi / k)
          ≤ (31416:ℝ)/10000/k := by
        have hw := p22_bjf_wtaylor (k := k) (by norm_num)
        have hb : (0:ℝ) ≤ (((31415:ℝ)/10000/k) ^ 3) := by positivity
        have hc : (0:ℝ) ≤ (((31416:ℝ)/10000/k) ^ 5) := by positivity
        linarith
      refine p22_bjf_route1 (k := k) (h := h) (sig := (31416:ℝ)/10000/k)
        (phi := (270126977:ℝ)/1000000000) hh.1 hh.2 ?_
        (p22_bjf_sinpos (by exact_mod_cast hk12)) hsig
        (p22_bjf_hTbound hh.1 hh.2) (by unfold p22_bjf_T sqrt3; positivity) ?_ ?_
        (by norm_num) (p22_bjf_tail_mono k hk12)
      · -- hwin (loose form, from the tail window)
        have hk1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk12
        have h536 : (5.5367:ℝ) ≤ 5.186 + 0.0331 * 12 := by norm_num
        exact le_trans (p22_bjf_wtail hk12) (by linarith)
      · -- hQ1
        have hk1 : ((k:ℝ)) ≥ 12 := by exact_mod_cast hk12
        have h1 : (235273:ℝ)/250000*(31416/10000/k)
            ≤ (235273:ℝ)/250000*(31416/10000/12) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact p22_div_le_div_real_left (by positivity) (by positivity) hk1
        linarith [h1]
      · exact p22_bjf_tail_phi k hk12

'''

def main():
    parts = []
    parts.append(HEAD)
    parts.append(KIT.replace("PLACEHOLDER_SEPT", "").replace("PLACEHOLDER_SER4", "").replace("PLACEHOLDER_REST", ""))
    parts.append(SEPT)
    parts.append(SER4)
    parts.append(REST)
    parts.append(WTAYLOR)
    parts.append(W3)
    parts.append(W4)
    for n in range(5, 12):
        parts.append(wgen(n, A_VAL[n]))
    parts.append(WTAIL)
    parts.append(pack2gen(3, "23/20", "((8661:ℝ)/10000)", "181867/200000",
        "351377/250000", "25741/100000", "9376501/10000000", "371067/250000",
        "0.6412", "10227/12500"))
    parts.append(pack2gen(4, "11/10", "((7072:ℝ)/10000)", "8949/10000",
        "456697/500000", "26847/100000", "1172319/1250000", "472477/500000",
        "0.5510", "83517/100000"))
    parts.append(pack2gen(5, "27/25",
        "((31416:ℝ)/10000/5 - (((31415:ℝ)/10000/5) ^ 3) / 6 + (((31416:ℝ)/10000/5) ^ 5) / 120)",
        "444563/500000", "13789/20000", "27271/100000", "4691069/5000000",
        "140927/200000", "0.5123", "84167/100000"))
    parts.append(pack2gen(6, "6/5", "((1:ℝ)/2)", "92377/100000",
        "563737/1000000", "307/1250", "469253/500000", "566211/1000000",
        "0.5131", "4/5"))
    for n, phi in [(7, "(237659:ℝ)/500000"), (8, "(102553:ℝ)/250000"),
                   (9, "(361247:ℝ)/1000000"), (10, "(161489:ℝ)/500000"),
                   (11, "(292191:ℝ)/1000000")]:
        parts.append(pack1gen(n, phi))
    parts.append(ASSEMBLY)
    out = "\n".join(parts)
    with open("/tmp/bjf_block.lean", "w") as f:
        f.write(out)
    print(f"wrote /tmp/bjf_block.lean: {len(out.splitlines())} lines")

if __name__ == "__main__":
    main()
