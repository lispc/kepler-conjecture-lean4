/-
Kepler.Text.Gamma4Env — two-sided box enclosures for the six `dihXf` slot
partials `g4dDihX1..6` (`D1..D6`) on the sharp `x`-box `[4,4.004001]^6`.

Each `D_s` is enclosed as a quotient `N_s / (A · U_s)`; the atom bounds on
`Δ₄,Δ₅,Δ₁,Δ₂,Δ₃,Δ₆,u₁₂₆,u₁₃₅,L` and on the radical `A = √(4x₁Δ)` live in
`Kepler.Text.Gamma4EnvAtoms` (imported here).  All enclosures are two-sided
(the `D1`/`D4` coefficients of the downstream monotonicity chain are
negative, so sign-only information is insufficient).  Widths: `D1` 2.0e-3,
`D2/D3/D5/D6` 8e-4, `D4` 8.4e-4 — the box-internal deviations are only
2.1e-4, so the enclosures carry a 10x margin.
-/
import Kepler.Text.Gamma4EnvAtoms

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## The six `D` enclosures -/

/-- `D1 = ∂dihXf/∂x1 ∈ [0.0579, 0.0599]`. -/
theorem g4dDihX1_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    0.0579 ≤ g4dDihX1 x1 x2 x3 x4 x5 x6 ∧
      g4dDihX1 x1 x2 x3 x4 x5 x6 ≤ 0.0599 := by
  have hbk : g4dInBox x1 x2 x3 x4 x5 x6 := hb
  obtain ⟨hD4lo, hD4hi⟩ := g4d_deltaX4_bounds hbk
  obtain ⟨hD1lo, hD1hi⟩ := g4d_DX1_bounds hbk
  obtain ⟨hΔlo, hΔhi⟩ := g4d_deltaX_bounds hbk
  obtain ⟨hLlo, hLhi⟩ := g4d_Llin_bounds hbk
  obtain ⟨hulo, huhi⟩ := g4d_u126_bounds hbk
  obtain ⟨hvlo, hvhi⟩ := g4d_u135_bounds hbk
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbk
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hx1lo : (4:ℝ) ≤ x1 := h1
  have hx1hi : x1 ≤ 4.004001 := h1'
  -- numerator bounds
  have hp1 : 15.965 * 127.67 ≤ deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6 :=
    mul_le_mul hD4lo hΔlo (by norm_num) (by linarith [hD4lo])
  have hp2 : 4 * 15.965 * 15.965 ≤
      x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6 := by
    have hin : 15.965 * 15.965 ≤ deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6 :=
      mul_le_mul hD4lo hD1lo (by norm_num) (by linarith [hD4lo])
    have h4 : (4:ℝ) ≤ x1 := hx1lo
    have := mul_le_mul h4 hin (by norm_num) (by linarith [hx1lo])
    nlinarith [this]
  have hp3 : -2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) ≤
      2 * 4.004001 * 128.71 * 0.017 := by
    have hprod : x1 * deltaX x1 x2 x3 x4 x5 x6 ≤ 4.004001 * 128.71 :=
      mul_le_mul hx1hi hΔhi (by linarith [hΔlo]) (by norm_num)
    nlinarith [hprod, hLhi, hx1lo, hΔlo]
  have hp3' : -2 * 4.004001 * 128.71 * 0.017 ≤
      -2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) := by
    have hprod : 4 * 127.67 ≤ x1 * deltaX x1 x2 x3 x4 x5 x6 :=
      mul_le_mul hx1lo hΔlo (by norm_num) (by linarith [hx1lo])
    have hxdn : (0:ℝ) ≤ x1 * deltaX x1 x2 x3 x4 x5 x6 := by linarith
    have ht1 : -2 * (x1 * deltaX x1 x2 x3 x4 x5 x6) * 0.017
        ≤ -2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6) := by
      nlinarith [hLhi, hxdn]
    have ht2 : -2 * 4.004001 * 128.71 * 0.017
        ≤ -2 * (x1 * deltaX x1 x2 x3 x4 x5 x6) * 0.017 := by
      nlinarith [hprod]
    linarith [ht1, ht2]
  constructor
  · -- lower bound of numerator
    have hNlo : 2 * (15.965 * 127.67 + 4 * 15.965 * 15.965 - 2 * 4.004001 * 128.71 * 0.017)
        ≤ 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
          + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
          - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)) := by
      nlinarith [hp1, hp2, hp3']
    have huP : (0:ℝ) < upsX x1 x2 x6 * upsX x1 x3 x5 := by
      have : (0:ℝ) < 47.999 := by norm_num
      nlinarith [hulo, hvlo]
    have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
      have : (0:ℝ) < 45.22 := by norm_num
      linarith
    have hkey : 0.0579 ≤ (2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) := by
      rw [le_div_iff₀ (by positivity)]
      have hden : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (upsX x1 x2 x6 * upsX x1 x3 x5)
          ≤ 45.38 * (48.1 * 48.1) := by
        apply mul_le_mul hAhi _ (by positivity) (by norm_num)
        exact mul_le_mul huhi hvhi (by linarith [hulo]) (by norm_num)
      nlinarith [hNlo, hden]
    unfold g4dDihX1
    exact hkey
  · -- upper bound of numerator
    have hNhi : 2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6))
        ≤ 2 * (16.07 * 128.71 + 4.004001 * 16.07 * 16.07 + 2 * 4.004001 * 128.71 * 0.017) := by
      have hp1' : deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
          ≤ 16.07 * 128.71 :=
        mul_le_mul hD4hi hΔhi (by linarith [hΔlo]) (by norm_num)
      have hp2' : x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
          ≤ 4.004001 * 16.07 * 16.07 := by
        have hin : deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
            ≤ 16.07 * 16.07 :=
          mul_le_mul hD4hi hD1hi (by linarith [hD1lo]) (by norm_num)
        nlinarith [hin, hx1hi]
      nlinarith [hp1', hp2', hp3]
    -- denominator > 0 and lower-bounded
    have huP : (0:ℝ) < upsX x1 x2 x6 * upsX x1 x3 x5 := by
      have : (0:ℝ) < 47.999 := by norm_num
      nlinarith [hulo, hvlo]
    have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
      have : (0:ℝ) < 45.22 := by norm_num
      linarith
    have hkey : (2 * (deltaX4 x1 x2 x3 x4 x5 x6 * deltaX x1 x2 x3 x4 x5 x6
        + x1 * deltaX4 x1 x2 x3 x4 x5 x6 * g4dDX1 x1 x2 x3 x4 x5 x6
        - 2 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1 + x2 + x3 - 2 * x4 + x5 + x6)))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (upsX x1 x2 x6 * upsX x1 x3 x5)) ≤ 0.0599 := by
      rw [div_le_iff₀ (by positivity)]
      have hden : 45.22 * (47.999 * 47.999)
          ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * (upsX x1 x2 x6 * upsX x1 x3 x5) := by
        apply mul_le_mul hAlo _ (by norm_num) (by linarith [hAlo])
        exact mul_le_mul hulo hvlo (by norm_num) (by linarith [huhi])
      nlinarith [hNhi, hden]
    unfold g4dDihX1
    exact hkey
/-- `D2 = ∂dihXf/∂x2 ∈ [−0.0593, −0.0585]`. -/
theorem g4dDihX2_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    -0.0593 ≤ g4dDihX2 x1 x2 x3 x4 x5 x6 ∧
      g4dDihX2 x1 x2 x3 x4 x5 x6 ≤ -0.0585 := by
  have hbk : g4dInBox x1 x2 x3 x4 x5 x6 := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX3_bounds hbk
  obtain ⟨hulo, huhi⟩ := g4d_u126_bounds hbk
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbk
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hPlo : 8 * 15.965 ≤ 2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 := by
    have h2x : (8:ℝ) ≤ 2 * x1 := by linarith
    calc (8 * 15.965 : ℝ) = 8 * 15.965 := rfl
      _ ≤ (2 * x1) * g4dDX3 x1 x2 x3 x4 x5 x6 :=
        mul_le_mul h2x hDXlo (by norm_num) (by linarith)
  have hPhi : 2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6 ≤ 2 * 4.004001 * 16.07 := by
    have h2x : 2 * x1 ≤ 2 * 4.004001 := by linarith
    exact mul_le_mul h2x hDXhi (by linarith [hDXlo]) (by norm_num)
  have huP : (0:ℝ) < upsX x1 x2 x6 := by linarith [hulo]
  have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    have : (0:ℝ) < 45.22 := by norm_num
    linarith
  constructor
  · have hkey : (2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ≤ 0.0593 := by
      rw [div_le_iff₀ (by positivity)]
      have hden : 45.22 * 47.999
          ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6 :=
        mul_le_mul hAlo hulo (by norm_num) (by linarith [hAlo])
      nlinarith [hPhi, hden]
    unfold g4dDihX2
    have : -2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        = -((2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) := by
      ring
    rw [this]
    linarith
  · have hkey : 0.0585 ≤ (2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) := by
      rw [le_div_iff₀ (by positivity)]
      have hden : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6
          ≤ 45.38 * 48.1 :=
        mul_le_mul hAhi huhi (by linarith [hulo]) (by norm_num)
      nlinarith [hPlo, hden]
    unfold g4dDihX2
    have : -2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        = -((2 * x1 * g4dDX3 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) := by
      ring
    rw [this]
    linarith

/-- `D3 = ∂dihXf/∂x3 ∈ [−0.0593, −0.0585]`. -/
theorem g4dDihX3_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    -0.0593 ≤ g4dDihX3 x1 x2 x3 x4 x5 x6 ∧
      g4dDihX3 x1 x2 x3 x4 x5 x6 ≤ -0.0585 := by
  have hbk : g4dInBox x1 x2 x3 x4 x5 x6 := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX2_bounds hbk
  obtain ⟨hulo, huhi⟩ := g4d_u135_bounds hbk
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbk
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hPlo : 8 * 15.965 ≤ 2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 := by
    have h2x : (8:ℝ) ≤ 2 * x1 := by linarith
    calc (8 * 15.965 : ℝ) = 8 * 15.965 := rfl
      _ ≤ (2 * x1) * g4dDX2 x1 x2 x3 x4 x5 x6 :=
        mul_le_mul h2x hDXlo (by norm_num) (by linarith)
  have hPhi : 2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6 ≤ 2 * 4.004001 * 16.07 := by
    have h2x : 2 * x1 ≤ 2 * 4.004001 := by linarith
    exact mul_le_mul h2x hDXhi (by linarith [hDXlo]) (by norm_num)
  have huP : (0:ℝ) < upsX x1 x3 x5 := by linarith [hulo]
  have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    have : (0:ℝ) < 45.22 := by norm_num
    linarith
  constructor
  · have hkey : (2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ≤ 0.0593 := by
      rw [div_le_iff₀ (by positivity)]
      have hden : 45.22 * 47.999
          ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5 :=
        mul_le_mul hAlo hulo (by norm_num) (by linarith [hAlo])
      nlinarith [hPhi, hden]
    unfold g4dDihX3
    have : -2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        = -((2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) := by
      ring
    rw [this]
    linarith
  · have hkey : 0.0585 ≤ (2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) := by
      rw [le_div_iff₀ (by positivity)]
      have hden : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5
          ≤ 45.38 * 48.1 :=
        mul_le_mul hAhi huhi (by linarith [hulo]) (by norm_num)
      nlinarith [hPlo, hden]
    unfold g4dDihX3
    have : -2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        = -((2 * x1 * g4dDX2 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) := by
      ring
    rw [this]
    linarith

/-- `D4 = ∂dihXf/∂x4 ∈ [0.1763, 0.17709]`. -/
theorem g4dDihX4_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    0.17625 ≤ g4dDihX4 x1 x2 x3 x4 x5 x6 ∧
      g4dDihX4 x1 x2 x3 x4 x5 x6 ≤ 0.17709 := by
  have hbk : g4dInBox x1 x2 x3 x4 x5 x6 := hb
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbk
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    have : (0:ℝ) < 45.22 := by norm_num
    linarith
  constructor
  · have hkey : 0.17625 ≤ (2 * x1) / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
      rw [le_div_iff₀ hApos]
      nlinarith [hAhi, h1]
    unfold g4dDihX4
    exact hkey
  · have hkey : (2 * x1) / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 0.17709 := by
      rw [div_le_iff₀ hApos]
      nlinarith [hAlo, h1']
    unfold g4dDihX4
    exact hkey

/-- `D5 = ∂dihXf/∂x5 ∈ [−0.0593, −0.0585]`. -/
theorem g4dDihX5_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    -0.0593 ≤ g4dDihX5 x1 x2 x3 x4 x5 x6 ∧
      g4dDihX5 x1 x2 x3 x4 x5 x6 ≤ -0.0585 := by
  have hbk : g4dInBox x1 x2 x3 x4 x5 x6 := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_DX6_bounds hbk
  obtain ⟨hulo, huhi⟩ := g4d_u135_bounds hbk
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbk
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hPlo : 8 * 15.965 ≤ 2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 := by
    have h2x : (8:ℝ) ≤ 2 * x1 := by linarith
    calc (8 * 15.965 : ℝ) = 8 * 15.965 := rfl
      _ ≤ (2 * x1) * g4dDX6 x1 x2 x3 x4 x5 x6 :=
        mul_le_mul h2x hDXlo (by norm_num) (by linarith)
  have hPhi : 2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6 ≤ 2 * 4.004001 * 16.07 := by
    have h2x : 2 * x1 ≤ 2 * 4.004001 := by linarith
    exact mul_le_mul h2x hDXhi (by linarith [hDXlo]) (by norm_num)
  have huP : (0:ℝ) < upsX x1 x3 x5 := by linarith [hulo]
  have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    have : (0:ℝ) < 45.22 := by norm_num
    linarith
  constructor
  · have hkey : (2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) ≤ 0.0593 := by
      rw [div_le_iff₀ (by positivity)]
      have hden : 45.22 * 47.999
          ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5 :=
        mul_le_mul hAlo hulo (by norm_num) (by linarith [hAlo])
      nlinarith [hPhi, hden]
    unfold g4dDihX5
    have : -2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        = -((2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) := by
      ring
    rw [this]
    linarith
  · have hkey : 0.0585 ≤ (2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5) := by
      rw [le_div_iff₀ (by positivity)]
      have hden : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5
          ≤ 45.38 * 48.1 :=
        mul_le_mul hAhi huhi (by linarith [hulo]) (by norm_num)
      nlinarith [hPlo, hden]
    unfold g4dDihX5
    have : -2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)
        = -((2 * x1 * g4dDX6 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) := by
      ring
    rw [this]
    linarith

/-- `D6 = ∂dihXf/∂x6 ∈ [−0.0593, −0.0585]`. -/
theorem g4dDihX6_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    -0.0593 ≤ g4dDihX6 x1 x2 x3 x4 x5 x6 ∧
      g4dDihX6 x1 x2 x3 x4 x5 x6 ≤ -0.0585 := by
  have hbk : g4dInBox x1 x2 x3 x4 x5 x6 := hb
  obtain ⟨hDXlo, hDXhi⟩ := g4d_deltaX5_bounds hbk
  obtain ⟨hulo, huhi⟩ := g4d_u126_bounds hbk
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hbk
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hPlo : 8 * 15.965 ≤ 2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 := by
    have h2x : (8:ℝ) ≤ 2 * x1 := by linarith
    calc (8 * 15.965 : ℝ) = 8 * 15.965 := rfl
      _ ≤ (2 * x1) * deltaX5 x1 x2 x3 x4 x5 x6 :=
        mul_le_mul h2x hDXlo (by norm_num) (by linarith)
  have hPhi : 2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6 ≤ 2 * 4.004001 * 16.07 := by
    have h2x : 2 * x1 ≤ 2 * 4.004001 := by linarith
    exact mul_le_mul h2x hDXhi (by linarith [hDXlo]) (by norm_num)
  have huP : (0:ℝ) < upsX x1 x2 x6 := by linarith [hulo]
  have hApos : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    have : (0:ℝ) < 45.22 := by norm_num
    linarith
  constructor
  · have hkey : (2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) ≤ 0.0593 := by
      rw [div_le_iff₀ (by positivity)]
      have hden : 45.22 * 47.999
          ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6 :=
        mul_le_mul hAlo hulo (by norm_num) (by linarith [hAlo])
      nlinarith [hPhi, hden]
    unfold g4dDihX6
    have : -2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        = -((2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) := by
      ring
    rw [this]
    linarith
  · have hkey : 0.0585 ≤ (2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6)
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6) := by
      rw [le_div_iff₀ (by positivity)]
      have hden : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6
          ≤ 45.38 * 48.1 :=
        mul_le_mul hAhi huhi (by linarith [hulo]) (by norm_num)
      nlinarith [hPlo, hden]
    unfold g4dDihX6
    have : -2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)
        = -((2 * x1 * deltaX5 x1 x2 x3 x4 x5 x6)
          / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x2 x6)) := by
      ring
    rw [this]
    linarith


/-- **W4-d**: the `dihXf` x₁-slot partial is positive on the sharp x-box,
closing the wave-2 `x1` sign GAP through the two-sided `D1` enclosure. -/
theorem g4d_dihXf_x1_pos {x1 x2 x3 x4 x5 x6 : ℝ} (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    0 < g4dDihX1 x1 x2 x3 x4 x5 x6 := by
  have := (g4dDihX1_bounds hb).1
  linarith

/-! ## Axiom audit (house style) -/

#print axioms g4dDihX1_bounds
#print axioms g4dDihX2_bounds
#print axioms g4dDihX3_bounds
#print axioms g4dDihX4_bounds
#print axioms g4dDihX5_bounds
#print axioms g4dDihX6_bounds
#print axioms g4d_dihXf_x1_pos

end Kepler.Text
