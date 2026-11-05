/-
Kepler.Text.Gamma4EnvAtoms — two-sided box enclosures for the six `dihXf` slot
partials `g4dDihX1..6` (`D1..D6`) on the sharp `x`-box `[4,4.004001]^6`, and
the numeric `sol0`/`tau0`/`mm1`/`mm2`/`π` enclosures (lane `gamma4-w4`).

Strategy.  Every `D_s` is a quotient `N_s / (A · U_s)` with
`A = √(4·x₁·Δ)`, `U_s` a product of `upsX` factors and `N_s` polynomial:
  D1 = 2(Δ₄Δ + x₁Δ₄Δ₁ − 2x₁ΔL)/(A·u₁₂₆·u₁₃₅)
  D2 = −2x₁Δ₃/(A·u₁₂₆),  D3 = −2x₁Δ₂/(A·u₁₃₅),  D4 = 2x₁/A,
  D5 = −2x₁Δ₆/(A·u₁₃₅),  D6 = −2x₁Δ₅/(A·u₁₂₆)
(`Δᵢ` the `g4dDXᵢ`/`deltaX4`/`deltaX5` atoms).  Each factor is enclosed by a
rational interval; the quotient bounds then follow by monotone
cross-multiplication.  The polynomial atom enclosures are proved by a
monomial-relaxation argument: after expanding in `δᵢ = xᵢ − 4`, every
quadratic monomial is relaxed to a linear one by
`δᵢδⱼ ≤ 0.004001·δᵢ` (from `δᵢ,δⱼ ∈ [0,0.004001]`), and `nlinarith`
finishes.  The radical `A` is enclosed through the rationalisation identity
`Δ₄² + 4x₁Δ = u₁₂₆·u₁₃₅`, i.e. `A² = u₁₂₆·u₁₃₅ − Δ₄²`, which is polynomial.
-/
import Kepler.Text.Gamma4Deriv8

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## The box monomial-relaxation kit

On `δᵢ = xᵢ − 4 ∈ [0, 0.004001]` we have `δᵢ(0.004001 − δⱼ) ≥ 0`, hence
`δᵢδⱼ ≤ 0.004001·δᵢ`.  These are the only nonlinear hints the atom
enclosures need. -/

private theorem g4d_box_sq {x : ℝ} (h1 : 4 ≤ x) (_h2 : x ≤ 4.004001) :
    0 ≤ (x - 4) * (0.004001 - (x - 4)) :=
  mul_nonneg (by linarith) (by linarith)

private theorem g4d_box_cross {x y : ℝ} (h1 : 4 ≤ x) (h2 : x ≤ 4.004001)
    (_h3 : 4 ≤ y) (h4 : y ≤ 4.004001) :
    0 ≤ (x - 4) * (0.004001 - (y - 4)) :=
  mul_nonneg (by linarith) (by linarith)

/-- The 21 monomial relaxations used by every atom bound below. -/
private theorem g4d_box_pack {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    0 ≤ (x1 - 4) * (0.004001 - (x1 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x2 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x4 - 4) * (0.004001 - (x4 - 4)) ∧
    0 ≤ (x5 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x6 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x1 - 4) * (0.004001 - (x2 - 4)) ∧
    0 ≤ (x1 - 4) * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x1 - 4) * (0.004001 - (x4 - 4)) ∧
    0 ≤ (x1 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x1 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x4 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x4 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x4 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x4 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x5 - 4) * (0.004001 - (x6 - 4)) := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  exact ⟨g4d_box_sq h1 h1', g4d_box_sq h2 h2', g4d_box_sq h3 h3',
    g4d_box_sq h4 h4', g4d_box_sq h5 h5', g4d_box_sq h6 h6',
    g4d_box_cross h1 h1' h2 h2', g4d_box_cross h1 h1' h3 h3',
    g4d_box_cross h1 h1' h4 h4', g4d_box_cross h1 h1' h5 h5',
    g4d_box_cross h1 h1' h6 h6', g4d_box_cross h2 h2' h3 h3',
    g4d_box_cross h2 h2' h4 h4', g4d_box_cross h2 h2' h5 h5',
    g4d_box_cross h2 h2' h6 h6', g4d_box_cross h3 h3' h4 h4',
    g4d_box_cross h3 h3' h5 h5', g4d_box_cross h3 h3' h6 h6',
    g4d_box_cross h4 h4' h5 h5', g4d_box_cross h4 h4' h6 h6',
    g4d_box_cross h5 h5' h6 h6'⟩

/-! ## The nine polynomial atom enclosures (`Δ₄,Δ₅,Δ₁,Δ₂,Δ₃,Δ₆,u₁₂₆,u₁₃₅,L`) -/

theorem g4d_deltaX4_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    15.965 ≤ deltaX4 x1 x2 x3 x4 x5 x6 ∧
      deltaX4 x1 x2 x3 x4 x5 x6 ≤ 16.07 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : deltaX4 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6 - 4) + 4*(x5 - 4) + -8*(x4 - 4) + 4*(x3 - 4) + 4*(x2 - 4)
        + -1*(x5 - 4)*(x6 - 4) + 1*(x3 - 4)*(x6 - 4) + 1*(x2 - 4)*(x5 - 4)
        + -1*(x2 - 4)*(x3 - 4) + 1*(x1 - 4)*(x6 - 4) + 1*(x1 - 4)*(x5 - 4)
        + -2*(x1 - 4)*(x4 - 4) + 1*(x1 - 4)*(x3 - 4) + 1*(x1 - 4)*(x2 - 4)
        + -1*(x1 - 4)*(x1 - 4) := by
    unfold deltaX4; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_deltaX5_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    15.965 ≤ deltaX5 x1 x2 x3 x4 x5 x6 ∧
      deltaX5 x1 x2 x3 x4 x5 x6 ≤ 16.07 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : deltaX5 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6 - 4) + -8*(x5 - 4) + 4*(x4 - 4) + 4*(x3 - 4) + 4*(x1 - 4)
        + -1*(x4 - 4)*(x6 - 4) + 1*(x3 - 4)*(x6 - 4) + 1*(x2 - 4)*(x6 - 4)
        + -2*(x2 - 4)*(x5 - 4) + 1*(x2 - 4)*(x4 - 4) + 1*(x2 - 4)*(x3 - 4)
        + -1*(x2 - 4)*(x2 - 4) + 1*(x1 - 4)*(x4 - 4) + -1*(x1 - 4)*(x3 - 4)
        + 1*(x1 - 4)*(x2 - 4) := by
    unfold deltaX5; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_DX1_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    15.965 ≤ g4dDX1 x1 x2 x3 x4 x5 x6 ∧ g4dDX1 x1 x2 x3 x4 x5 x6 ≤ 16.07 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : g4dDX1 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6 - 4) + 4*(x5 - 4) + 4*(x3 - 4) + 4*(x2 - 4) + -8*(x1 - 4)
        + 1*(x4 - 4)*(x6 - 4) + 1*(x4 - 4)*(x5 - 4) + -1*(x4 - 4)*(x4 - 4)
        + 1*(x3 - 4)*(x6 - 4) + -1*(x3 - 4)*(x5 - 4) + 1*(x3 - 4)*(x4 - 4)
        + -1*(x2 - 4)*(x6 - 4) + 1*(x2 - 4)*(x5 - 4) + 1*(x2 - 4)*(x4 - 4)
        + -2*(x1 - 4)*(x4 - 4) := by
    unfold g4dDX1; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_DX2_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    15.965 ≤ g4dDX2 x1 x2 x3 x4 x5 x6 ∧ g4dDX2 x1 x2 x3 x4 x5 x6 ≤ 16.07 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : g4dDX2 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x6 - 4) + 4*(x4 - 4) + 4*(x3 - 4) + -8*(x2 - 4) + 4*(x1 - 4)
        + 1*(x5 - 4)*(x6 - 4) + -1*(x5 - 4)*(x5 - 4) + 1*(x4 - 4)*(x5 - 4)
        + 1*(x3 - 4)*(x6 - 4) + 1*(x3 - 4)*(x5 - 4) + -1*(x3 - 4)*(x4 - 4)
        + -2*(x2 - 4)*(x5 - 4) + -1*(x1 - 4)*(x6 - 4) + 1*(x1 - 4)*(x5 - 4)
        + 1*(x1 - 4)*(x4 - 4) := by
    unfold g4dDX2; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_DX3_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    15.965 ≤ g4dDX3 x1 x2 x3 x4 x5 x6 ∧ g4dDX3 x1 x2 x3 x4 x5 x6 ≤ 16.07 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : g4dDX3 x1 x2 x3 x4 x5 x6
      = 16 + 4*(x5 - 4) + 4*(x4 - 4) + -8*(x3 - 4) + 4*(x2 - 4) + 4*(x1 - 4)
        + -1*(x6 - 4)*(x6 - 4) + 1*(x5 - 4)*(x6 - 4) + 1*(x4 - 4)*(x6 - 4)
        + -2*(x3 - 4)*(x6 - 4) + 1*(x2 - 4)*(x6 - 4) + 1*(x2 - 4)*(x5 - 4)
        + -1*(x2 - 4)*(x4 - 4) + 1*(x1 - 4)*(x6 - 4) + -1*(x1 - 4)*(x5 - 4)
        + 1*(x1 - 4)*(x4 - 4) := by
    unfold g4dDX3; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_DX6_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    15.965 ≤ g4dDX6 x1 x2 x3 x4 x5 x6 ∧ g4dDX6 x1 x2 x3 x4 x5 x6 ≤ 16.07 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : g4dDX6 x1 x2 x3 x4 x5 x6
      = 16 + -8*(x6 - 4) + 4*(x5 - 4) + 4*(x4 - 4) + 4*(x2 - 4) + 4*(x1 - 4)
        + -1*(x4 - 4)*(x5 - 4) + -2*(x3 - 4)*(x6 - 4) + 1*(x3 - 4)*(x5 - 4)
        + 1*(x3 - 4)*(x4 - 4) + -1*(x3 - 4)*(x3 - 4) + 1*(x2 - 4)*(x5 - 4)
        + 1*(x2 - 4)*(x3 - 4) + 1*(x1 - 4)*(x4 - 4) + 1*(x1 - 4)*(x3 - 4)
        + -1*(x1 - 4)*(x2 - 4) := by
    unfold g4dDX6; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_u126_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    47.999 ≤ upsX x1 x2 x6 ∧ upsX x1 x2 x6 ≤ 48.1 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : upsX x1 x2 x6
      = 48 + 8*(x6 - 4) + 8*(x2 - 4) + 8*(x1 - 4)
        + -1*(x6 - 4)*(x6 - 4) + 2*(x2 - 4)*(x6 - 4) + -1*(x2 - 4)*(x2 - 4)
        + 2*(x1 - 4)*(x6 - 4) + 2*(x1 - 4)*(x2 - 4) + -1*(x1 - 4)*(x1 - 4) := by
    unfold upsX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

theorem g4d_u135_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    47.999 ≤ upsX x1 x3 x5 ∧ upsX x1 x3 x5 ≤ 48.1 := by
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
    hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56⟩ := g4d_box_pack hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hexp : upsX x1 x3 x5
      = 48 + 8*(x5 - 4) + 8*(x3 - 4) + 8*(x1 - 4)
        + -1*(x5 - 4)*(x5 - 4) + 2*(x3 - 4)*(x5 - 4) + -1*(x3 - 4)*(x3 - 4)
        + 2*(x1 - 4)*(x5 - 4) + 2*(x1 - 4)*(x3 - 4) + -1*(x1 - 4)*(x1 - 4) := by
    unfold upsX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6',
      hs1, hs2, hs3, hs4, hs5, hs6, hp12, hp13, hp14, hp15, hp16,
      hp23, hp24, hp25, hp26, hp34, hp35, hp36, hp45, hp46, hp56]

/-- The linear atom `L = −2x₁+x₂+x₃−2x₄+x₅+x₆` of the `x₁`-slot numerator. -/
theorem g4d_Llin_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    -0.017 ≤ -2 * x1 + x2 + x3 - 2 * x4 + x5 + x6 ∧
      -2 * x1 + x2 + x3 - 2 * x4 + x5 + x6 ≤ 0.017 := by
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  constructor <;> linarith

/-! ## The radical `A = √(4·x₁·Δ)` via the rationalisation identity

`g4d_ups_delta`: `Δ₄² + 4x₁Δ = u₁₂₆·u₁₃₅`, so `A² = u₁₂₆·u₁₃₅ − Δ₄²`. -/

theorem g4d_A_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    45.22 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ∧
      Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 45.38 := by
  obtain ⟨hu1lo, hu1hi⟩ := g4d_u126_bounds hb
  obtain ⟨hu3lo, hu3hi⟩ := g4d_u135_bounds hb
  obtain ⟨hd4lo, hd4hi⟩ := g4d_deltaX4_bounds hb
  have hid := g4d_ups_delta x1 x2 x3 x4 x5 x6
  have hd4sq_lo : 15.965 * 15.965 ≤ deltaX4 x1 x2 x3 x4 x5 x6 * deltaX4 x1 x2 x3 x4 x5 x6 :=
    mul_le_mul hd4lo hd4lo (by norm_num) (by linarith [hd4lo])
  have hd4sq_hi : deltaX4 x1 x2 x3 x4 x5 x6 * deltaX4 x1 x2 x3 x4 x5 x6 ≤ 16.07 * 16.07 :=
    mul_le_mul hd4hi hd4hi (by linarith [hd4lo]) (by norm_num)
  constructor
  · apply Real.le_sqrt_of_sq_le
    have hprod : 47.999 * 47.999 ≤ upsX x1 x2 x6 * upsX x1 x3 x5 :=
      mul_le_mul hu1lo hu3lo (by norm_num) (by linarith [hu1lo])
    nlinarith [hid, hprod, hd4sq_hi]
  · rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 45.38)]
    have hprod : upsX x1 x2 x6 * upsX x1 x3 x5 ≤ 48.1 * 48.1 :=
      mul_le_mul hu1hi hu3hi (by linarith [hu3lo]) (by norm_num)
    nlinarith [hid, hprod, hd4sq_lo]

/-- A crude two-sided enclosure of `Δ` itself (only the `x₁`-slot `L`-term
needs it).  Derived from `A² = 4x₁Δ`. -/
theorem g4d_deltaX_bounds {x1 x2 x3 x4 x5 x6 : ℝ}
    (hb : g4dInBox x1 x2 x3 x4 x5 x6) :
    127.67 ≤ deltaX x1 x2 x3 x4 x5 x6 ∧ deltaX x1 x2 x3 x4 x5 x6 ≤ 128.71 := by
  obtain ⟨hAlo, hAhi⟩ := g4d_A_bounds hb
  obtain ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ := hb
  have hpr : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 = Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ^ 2 :=
    (Real.sq_sqrt (Real.sqrt_pos.mp (by linarith [hAlo])).le).symm
  have hAsq_lo : 45.22 * 45.22 ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by
    nlinarith [hAlo, hpr]
  have hAsq_hi : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 ≤ 45.38 * 45.38 := by
    nlinarith [hAhi, hpr]
  have hx4pos : (0:ℝ) < 4 * x1 := by linarith
  constructor
  · have hrepr : deltaX x1 x2 x3 x4 x5 x6
        = (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) / (4 * x1) := by
      field_simp
    rw [hrepr, le_div_iff₀ hx4pos]
    nlinarith [hAsq_lo, h1']
  · have hrepr : deltaX x1 x2 x3 x4 x5 x6
        = (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) / (4 * x1) := by
      field_simp
    rw [hrepr, div_le_iff₀ hx4pos]
    nlinarith [hAsq_hi, h1]


/-! ## Axiom audit (house style) -/

#print axioms g4d_deltaX4_bounds
#print axioms g4d_deltaX5_bounds
#print axioms g4d_DX1_bounds
#print axioms g4d_DX2_bounds
#print axioms g4d_DX3_bounds
#print axioms g4d_DX6_bounds
#print axioms g4d_u126_bounds
#print axioms g4d_u135_bounds
#print axioms g4d_Llin_bounds
#print axioms g4d_A_bounds
#print axioms g4d_deltaX_bounds

end Kepler.Text
