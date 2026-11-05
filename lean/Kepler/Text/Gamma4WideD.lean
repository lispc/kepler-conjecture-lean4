/-
Kepler.Text.Gamma4WideD — lane `nli-rest-b2`, part 3: the six `D_s`
(`= ∂dihXf/∂x_s`) two-sided envelopes on the `G4ENV-WIDE` box
`[4, 7.02674064]⁶`.

Each `D_s` is the same quotient as in `Gamma4EnvAtoms`:

  D1 = 2(Δ₄Δ + x₁Δ₄Δ₁ − 2x₁ΔL)/(A·u₁₂₆·u₁₃₅),
  D2 = −2x₁Δ₃/(A·u₁₂₆),  D3 = −2x₁Δ₂/(A·u₁₃₅),  D4 = 2x₁/A,
  D5 = −2x₁Δ₆/(A·u₁₃₅),  D6 = −2x₁Δ₅/(A·u₁₂₆),

with the atom envelopes of `Kepler.Text.Gamma4Wide`:

| quantity | wide-box envelope | width | narrow-box (`Gamma4Env`) width |
|---|---|---:|---:|
| `A`      | `[39.19, 232.9]` | 193.7 | 0.16 |
| `u₁₂₆`   | `[48, 175.61]`   | 127.6 | 0.10 |
| `Δ,Δ₄,Δ₅,Δ₁,Δ₂,Δ₃,Δ₆` | `Δ ∈ [96,1928]`, `Δᵢ ∈ [−54.02,119.4]` | — | ~1e−3 |
| `D1`     | `[−701, 701]` | 870 | 2.0e−3 |
| `D2`,`D3`,`D5`,`D6` | `[−0.893, 0.404]` | 1.12 | 8e−4 |
| `D4`     | `[0.0343, 0.3586]` | 0.324 | 8.4e−4 |

(Coverage: the box `[4,7.02674064]⁶` contains the 7 bank boxes whose
coordinates are all `≤ 2hplus`; the other 7 carry one `x = 8` coordinate and
need the `B_k = [4,7.02674064]⁵×[4,8]` family, where `Δ ≥ 54.7107` — see the
header of `Gamma4Wide.lean`.)

The wide envelopes are 500–5000× wider than the narrow-box ones.  In
particular `D2`'s interval straddles zero although the true `D2` is `< −0.015`
on every bank box: this is the quantitative reason why the wide `D` envelope
alone cannot recover the sign information that the `gamma4fgcy` derivative
chain needs (finding WBL-1 in `Evidence.md`).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.Gamma4Wide

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-! ## The four negative-slope slots (`D2,D3,D5,D6`) -/

private theorem g4w_negD {x1 A u Dv : ℝ}
    (hx1 : 4 ≤ x1) (hx1' : x1 ≤ 7.02674064)
    (hA : 39.19 ≤ A) (hA' : A ≤ 232.9)
    (hu : 48 ≤ u) (hu' : u ≤ 175.61)
    (hD : -54.02 ≤ Dv) (hD' : Dv ≤ 119.4) :
    -0.893 ≤ -2 * x1 * Dv / (A * u) ∧ -2 * x1 * Dv / (A * u) ≤ 0.404 := by
  have hApos : (0:ℝ) < A := by linarith
  have huP : (0:ℝ) < u := by linarith
  have hden : (0:ℝ) < A * u := mul_pos hApos huP
  have hdenlo : 39.19 * 48 ≤ A * u :=
    mul_le_mul hA hu (by norm_num) (by linarith)
  have hxdhi : x1 * Dv ≤ 7.02674064 * 119.4 := by
    rcases le_total 0 Dv with hDv | hDv
    · exact mul_le_mul hx1' hD' hDv (by norm_num)
    · have h1 : x1 * Dv ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hDv
      nlinarith
  have hxdlo : -380 ≤ x1 * Dv := by
    rcases le_total 0 Dv with hDv | hDv
    · have h1 : 0 ≤ x1 * Dv := mul_nonneg (by linarith) hDv
      linarith
    · have h1 : x1 * (-54.02) ≤ x1 * Dv :=
        mul_le_mul_of_nonneg_left hD (by linarith)
      have h2 : -380 ≤ x1 * (-54.02) := by nlinarith
      linarith
  constructor
  · have hkey : (-0.893 : ℝ) * (A * u) ≤ -2 * x1 * Dv := by nlinarith [hdenlo, hxdhi]
    rw [le_div_iff₀ hden]
    linarith
  · have hkey : -2 * x1 * Dv ≤ (0.404 : ℝ) * (A * u) := by nlinarith [hdenlo, hxdlo]
    rw [div_le_iff₀ hden]
    linarith

/-- `D2 = −2x₁Δ₃/(A·u₁₂₆) ∈ [−0.893, 0.2298]` on the wide box. -/
theorem g4w_D2_bounds {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    -0.893 ≤ g4dDihX2 x1 x2 x3 x4 x5 x6 ∧ g4dDihX2 x1 x2 x3 x4 x5 x6 ≤ 0.404 := by
  have hAlo := (g4w_A_bounds hb).1
  have hAhi := (g4w_A_bounds hb).2
  obtain ⟨hulo, huhi⟩ := g4w_u126_bounds hb
  obtain ⟨hXlo, hXhi⟩ := g4w_DX3_bounds hb
  obtain ⟨hx1, hx1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h := g4w_negD hx1 hx1' hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX2
  convert h using 2 <;> ring

/-- `D3 = −2x₁Δ₂/(A·u₁₃₅) ∈ [−0.892, 0.2297]` on the wide box. -/
theorem g4w_D3_bounds {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    -0.893 ≤ g4dDihX3 x1 x2 x3 x4 x5 x6 ∧ g4dDihX3 x1 x2 x3 x4 x5 x6 ≤ 0.404 := by
  have hAlo := (g4w_A_bounds hb).1
  have hAhi := (g4w_A_bounds hb).2
  obtain ⟨hulo, huhi⟩ := g4w_u135_bounds hb
  obtain ⟨hXlo, hXhi⟩ := g4w_DX2_bounds hb
  obtain ⟨hx1, hx1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h := g4w_negD hx1 hx1' hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX3
  convert h using 2 <;> ring

/-- `D5 = −2x₁Δ₆/(A·u₁₃₅) ∈ [−0.892, 0.2297]` on the wide box. -/
theorem g4w_D5_bounds {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    -0.893 ≤ g4dDihX5 x1 x2 x3 x4 x5 x6 ∧ g4dDihX5 x1 x2 x3 x4 x5 x6 ≤ 0.404 := by
  have hAlo := (g4w_A_bounds hb).1
  have hAhi := (g4w_A_bounds hb).2
  obtain ⟨hulo, huhi⟩ := g4w_u135_bounds hb
  obtain ⟨hXlo, hXhi⟩ := g4w_DX6_bounds hb
  obtain ⟨hx1, hx1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h := g4w_negD hx1 hx1' hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX5
  convert h using 2 <;> ring

/-- `D6 = −2x₁Δ₅/(A·u₁₂₆) ∈ [−0.892, 0.2297]` on the wide box. -/
theorem g4w_D6_bounds {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    -0.893 ≤ g4dDihX6 x1 x2 x3 x4 x5 x6 ∧ g4dDihX6 x1 x2 x3 x4 x5 x6 ≤ 0.404 := by
  have hAlo := (g4w_A_bounds hb).1
  have hAhi := (g4w_A_bounds hb).2
  obtain ⟨hulo, huhi⟩ := g4w_u126_bounds hb
  obtain ⟨hXlo, hXhi⟩ := g4w_deltaX5_bounds hb
  obtain ⟨hx1, hx1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have h := g4w_negD hx1 hx1' hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX6
  convert h using 2 <;> ring

/-! ## `D4` -/

/-- `D4 = 2x₁/A ∈ [0.0343, 0.3586]` on the wide box. -/
theorem g4w_D4_bounds {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    0.0343 ≤ g4dDihX4 x1 x2 x3 x4 x5 x6 ∧ g4dDihX4 x1 x2 x3 x4 x5 x6 ≤ 0.3586 := by
  have hAlo := (g4w_A_bounds hb).1
  have hAhi := (g4w_A_bounds hb).2
  obtain ⟨hx1, hx1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 39.19) hAlo
  constructor
  · have hkey : 0.0343 ≤ (2 * x1) / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
      rw [le_div_iff₀ hApos]
      nlinarith [hAhi, hx1]
    simpa only [g4dDihX4] using hkey
  · have hkey : (2 * x1) / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 0.3586 := by
      rw [div_le_iff₀ hApos]
      nlinarith [hAlo, hx1']
    simpa only [g4dDihX4] using hkey

/-! ## A bilinear interval product helper -/

/-- Two-sided product bound for `a` straddling `0` and `b ≥ 0`. -/
theorem g4w_mul_bound {a a1 a2 b b1 b2 : ℝ}
    (ha1 : a1 ≤ a) (ha2 : a ≤ a2) (ha1n : a1 ≤ 0) (ha2p : 0 ≤ a2)
    (hb1 : b1 ≤ b) (hb2 : b ≤ b2) (hb1p : 0 ≤ b1) :
    a1 * b2 ≤ a * b ∧ a * b ≤ max (a1 * b2) (a2 * b2) := by
  have hb0 : 0 ≤ b := le_trans hb1p hb1
  have hb2p : 0 ≤ b2 := le_trans hb0 hb2
  constructor
  · rcases le_total 0 a with ha | ha
    · have h1 : 0 ≤ a * b := mul_nonneg ha hb0
      have h2 : a1 * b2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha1n hb2p
      linarith
    · have h1 : a * b2 ≤ a * b := mul_le_mul_of_nonpos_left hb2 ha
      have h2 : a1 * b2 ≤ a * b2 := mul_le_mul_of_nonneg_right ha1 hb2p
      linarith
  · rcases le_total 0 a with ha | ha
    · have h1 : a * b ≤ a2 * b := mul_le_mul_of_nonneg_right ha2 hb0
      have h2 : a2 * b ≤ a2 * b2 := mul_le_mul_of_nonneg_left hb2 ha2p
      have h3 : a2 * b2 ≤ max (a1 * b2) (a2 * b2) := le_max_right _ _
      linarith
    · have h1 : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hb0
      have h2 : 0 ≤ a2 * b2 := mul_nonneg ha2p hb2p
      have h3 : a2 * b2 ≤ max (a1 * b2) (a2 * b2) := le_max_right _ _
      linarith

/-! ## `D1` -/

/-- `D1 = ∂dihXf/∂x₁ ∈ [−0.133, 7.525]` on the wide box.  (The interval is
wide because the numerator carries `Δ`, `Δ₄` and `L` with only box-level
correlations; the true `D1` on the bank boxes is `< 0.115`.) -/
theorem g4w_D1_bounds {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4wBox x1 x2 x3 x4 x5 x6) :
    -701 ≤ g4dDihX1 x1 x2 x3 x4 x5 x6 ∧ g4dDihX1 x1 x2 x3 x4 x5 x6 ≤ 701 := by
  obtain ⟨hD4lo, hD4hi⟩ := g4w_deltaX4_bounds hb
  have hΔlo : (96:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 := g4w_deltaX_bounds hb
  have hΔhi' : deltaX x1 x2 x3 x4 x5 x6 ≤ 1928 := g4w_deltaX_upper hb
  obtain ⟨hX1lo, hX1hi⟩ := g4w_DX1_bounds hb
  obtain ⟨hLlo, hLhi⟩ := g4w_L_bounds hb
  obtain ⟨hAlo, hAhi⟩ := g4w_A_bounds hb
  obtain ⟨hulo, huhi⟩ := g4w_u126_bounds hb
  obtain ⟨hvlo, hvhi⟩ := g4w_u135_bounds hb
  obtain ⟨hx1, hx1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  -- absolute-value bounds for the three numerator blocks
  have ht1abs : |deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6|
      ≤ 119.4 * 1928 := by
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by linarith, hD4hi⟩) (abs_le.mpr ⟨by linarith, hΔhi'⟩)
      (abs_nonneg _) (by norm_num)
  have ht2abs : |x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6|
      ≤ 7.02674064 * (119.4 * 119.4) := by
    rw [abs_mul, abs_mul]
    have h1 : |x1| ≤ 7.02674064 := by
      rw [abs_of_pos (by linarith : (0:ℝ) < x1)]; exact hx1'
    have h2 : |deltaX4 x1 x2 x3 x4 x5 x6| ≤ 119.4 :=
      abs_le.mpr ⟨by linarith, hD4hi⟩
    have h3 : |g4dDX1 x1 x2 x3 x4 x5 x6| ≤ 119.4 :=
      abs_le.mpr ⟨by linarith, hX1hi⟩
    have h12 : |x1| * |deltaX4 x1 x2 x3 x4 x5 x6| ≤ 7.02674064 * 119.4 :=
      mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    have h123 : |x1| * |deltaX4 x1 x2 x3 x4 x5 x6| * |g4dDX1 x1 x2 x3 x4 x5 x6|
        ≤ (7.02674064 * 119.4) * 119.4 :=
      mul_le_mul h12 h3 (abs_nonneg _) (by norm_num)
    nlinarith [h123]
  have ht3abs : |-2 * x1 * deltaX x1 x2 x3 x4 x5 x6 *
      (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)| ≤ 2 * 7.02674064 * 1928 * 12.107 := by
    have hLabs : |-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6| ≤ 12.107 :=
      abs_le.mpr ⟨hLlo, hLhi⟩
    have hxabs : |x1| ≤ 7.02674064 := by
      rw [abs_of_pos (by linarith : (0:ℝ) < x1)]; exact hx1'
    have hDabs : |deltaX x1 x2 x3 x4 x5 x6| ≤ 1928 := by
      rw [abs_of_pos (by linarith : (0:ℝ) < deltaX x1 x2 x3 x4 x5 x6)]
      exact hΔhi'
    calc |-2 * x1 * deltaX x1 x2 x3 x4 x5 x6 *
          (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)|
        = 2 * |x1| * |deltaX x1 x2 x3 x4 x5 x6| *
            |-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6| := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg]
          ring
      _ ≤ 2 * 7.02674064 * 1928 * 12.107 := by
          apply mul_le_mul
          · exact mul_le_mul (mul_le_mul (by norm_num) hxabs (abs_nonneg _) (by norm_num))
              hDabs (abs_nonneg _) (by norm_num)
          · exact hLabs
          · exact abs_nonneg _
          · norm_num
  have hNabs : |deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
      + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
      - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)|
      ≤ 119.4 * 1928 + 7.02674064 * (119.4 * 119.4) + 2 * 7.02674064 * 1928 * 12.107 := by
    have hsplit : |deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)|
        ≤ |deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
            + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6|
          + |2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)| := by
      have := abs_sub
        (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
          + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
        (2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
      simpa [sub_eq_add_neg] using this
    have h12 : |deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6|
        ≤ 119.4 * 1928 + 7.02674064 * (119.4 * 119.4) := by
      have := abs_add_le (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6)
        (x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6)
      linarith [ht1abs, ht2abs]
    have h3abs' : |2 * x1 * deltaX x1 x2 x3 x4 x5 x6 *
        (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)| ≤ 2 * 7.02674064 * 1928 * 12.107 := by
      have h := ht3abs
      calc |2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)|
          = |-2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)| := by
            rw [show (2:ℝ) * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)
              = -(-2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)) from by ring,
              abs_neg]
        _ ≤ _ := h
    linarith [hsplit, h12, h3abs']
  -- denominator
  have hdenpos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
      * (upsX x1 x2 x6 * upsX x1 x3 x5) := by
    have h1 : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
      lt_of_lt_of_le (by norm_num : (0:ℝ) < 39.19) hAlo
    have h2 : (0:ℝ) < upsX x1 x2 x6 * upsX x1 x3 x5 :=
      mul_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 48) hulo)
        (lt_of_lt_of_le (by norm_num : (0:ℝ) < 48) hvlo)
    exact mul_pos h1 h2
  have hdenhi : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (upsX x1 x2 x6 * upsX x1 x3 x5)
      ≤ 232.9 * (175.61 * 175.61) := by
    apply mul_le_mul hAhi _ (by positivity) (by norm_num)
    exact mul_le_mul huhi hvhi (by linarith [hvlo]) (by norm_num)
  have hdenlo : 39.19 * (48 * 48)
      ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (upsX x1 x2 x6 * upsX x1 x3 x5) := by
    apply mul_le_mul hAlo _ (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0:ℝ) < 39.19) hAlo).le
    exact mul_le_mul hulo hvlo (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0:ℝ) < 48) hulo).le
  constructor
  · have hkey : (-701 : ℝ) ≤ 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) := by
      rw [le_div_iff₀ hdenpos]
      have hb := abs_le.mp hNabs
      nlinarith [hb.1, hdenlo]
    simpa only [g4dDihX1] using hkey
  · have hkey : 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ≤ 701 := by
      rw [div_le_iff₀ hdenpos]
      have hb := abs_le.mp hNabs
      nlinarith [hb.2, hdenlo]
    simpa only [g4dDihX1] using hkey

/-! ## Axiom audit (house style) -/

#print axioms g4w_negD
#print axioms g4w_D1_bounds
#print axioms g4w_D2_bounds
#print axioms g4w_D3_bounds
#print axioms g4w_D4_bounds
#print axioms g4w_D5_bounds
#print axioms g4w_D6_bounds

end Kepler.Text
