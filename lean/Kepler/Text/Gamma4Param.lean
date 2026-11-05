/-
Kepler.Text.Gamma4Param — lane `gamma4-w5`, W5-a base layer.

The YOUOBF-v2 4-variable monotone slot needs `D_s = ∂dihXf/∂x_s` on the wide
`(y1,y4)` box; its numerical minimum sits at the corner `(y1,y4) = (√8,2)`,
i.e. the `x`-corner `x1 = 8`, `x4 = 4`, with the other four `x`-coordinates in
`[4,4.004001]`.  This module supplies the *base narrow envelope* at that
corner (the "one base enclosure" of the work order's Lipschitz route):

* `g4w5Corner`: the corner-slice predicate `x1 = 8`, `x4 = 4`,
  `x2,x3,x5,x6 ∈ [4,4.004001]`;
* two-sided enclosures of the nine atoms `Δ, Δ4, Δ5, Δ1, Δ2, Δ3, Δ6, u126,
  u135` and of the radical `A = √(4x1Δ)`, by monomial relaxation
  `δᵢ = xᵢ − 4 ∈ [0,0.004001]`;
* the six `D_s` values at the corner point `(8,4,4,4,4,4)` as exact rationals
  `D1 = 1/8`, `D2 = D3 = D5 = D6 = −1/8`, `D4 = 1/4`.

The wide-box (`y1² ∈ [7.03,8]`, `y4² ∈ [4,6.76]`) parameterisation is NOT in
this module: see `DELIVERY.md`, W5-a is a quantified GAP (per-`D` interval
arithmetic needs ≤1.6e−3 per piece, a ~160×160 grid). -/
import Kepler.Text.Gamma4Env

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- The `(y1,y4) = (√8,2)` corner slice in squared coordinates:
`x1 = 8`, `x4 = 4`, `x2,x3,x5,x6 ∈ [4,4.004001]`. -/
def g4w5Corner (x1 x2 x3 x4 x5 x6 : ℝ) : Prop :=
  x1 = 8 ∧ 4 ≤ x2 ∧ x2 ≤ 4.004001 ∧ 4 ≤ x3 ∧ x3 ≤ 4.004001 ∧
    x4 = 4 ∧ 4 ≤ x5 ∧ x5 ≤ 4.004001 ∧ 4 ≤ x6 ∧ x6 ≤ 4.004001

/-! ## The monomial-relaxation kit on the four narrow coordinates -/

private theorem g4w5_box_sq {x : ℝ} (h1 : 4 ≤ x) (_h2 : x ≤ 4.004001) :
    0 ≤ (x - 4) * (0.004001 - (x - 4)) :=
  mul_nonneg (by linarith) (by linarith)

private theorem g4w5_box_cross {x y : ℝ} (h1 : 4 ≤ x) (_h2 : x ≤ 4.004001)
    (_h3 : 4 ≤ y) (h4 : y ≤ 4.004001) :
    0 ≤ (x - 4) * (0.004001 - (y - 4)) :=
  mul_nonneg (by linarith) (by linarith)

private theorem g4w5_box_cube {x y : ℝ} (h1 : 4 ≤ x) (_h2 : x ≤ 4.004001)
    (_h3 : 4 ≤ y) (h4 : y ≤ 4.004001) :
    0 ≤ (x - 4) ^ 2 * (0.004001 - (y - 4)) :=
  mul_nonneg (sq_nonneg _) (by linarith)

/-- The ten quadratic monomial relaxations plus the six cubic ones used by the
`Δ` enclosure. -/
private theorem g4w5_pack {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    0 ≤ (x2 - 4) * (0.004001 - (x2 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x5 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x6 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x2 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x3 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x5 - 4) * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x2 - 4) ^ 2 * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x2 - 4) ^ 2 * (0.004001 - (x5 - 4)) ∧
    0 ≤ (x5 - 4) ^ 2 * (0.004001 - (x2 - 4)) ∧
    0 ≤ (x3 - 4) ^ 2 * (0.004001 - (x6 - 4)) ∧
    0 ≤ (x6 - 4) ^ 2 * (0.004001 - (x3 - 4)) ∧
    0 ≤ (x6 - 4) ^ 2 * (0.004001 - (x5 - 4)) := by
  exact ⟨g4w5_box_sq h2 h2', g4w5_box_sq h3 h3', g4w5_box_sq h5 h5',
    g4w5_box_sq h6 h6', g4w5_box_cross h2 h2' h3 h3',
    g4w5_box_cross h2 h2' h5 h5', g4w5_box_cross h2 h2' h6 h6',
    g4w5_box_cross h3 h3' h5 h5', g4w5_box_cross h3 h3' h6 h6',
    g4w5_box_cross h5 h5' h6 h6', g4w5_box_cube h2 h2' h3 h3',
    g4w5_box_cube h2 h2' h5 h5', g4w5_box_cube h5 h5' h2 h2',
    g4w5_box_cube h3 h3' h6 h6', g4w5_box_cube h6 h6' h3 h3',
    g4w5_box_cube h6 h6' h5 h5'⟩

/-! ## Atom enclosures -/


theorem g4w5_deltaX_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    127.99 ≤ deltaX 8 x2 x3 4 x5 x6 ∧ deltaX 8 x2 x3 4 x5 x6 ≤ 128.53 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : deltaX 8 x2 x3 4 x5 x6
      = (-1)*(x2-4)^2*(x5-4) + (-4)*(x2-4)^2 + (1)*(x2-4)*(x3-4)*(x5-4) + (1)*(x2-4)*(x3-4)*(x6-4) + (4)*(x2-4)*(x3-4) + (-1)*(x2-4)*(x5-4)^2 + (1)*(x2-4)*(x5-4)*(x6-4) + (4)*(x2-4)*(x5-4) + (32)*(x2-4) + (-1)*(x3-4)^2*(x6-4) + (-4)*(x3-4)^2 + (1)*(x3-4)*(x5-4)*(x6-4) + (-1)*(x3-4)*(x6-4)^2 + (4)*(x3-4)*(x6-4) + (32)*(x3-4) + (-4)*(x5-4)^2 + (4)*(x5-4)*(x6-4) + (32)*(x5-4) + (-4)*(x6-4)^2 + (32)*(x6-4) + (128) := by
    unfold deltaX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_deltaX4_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -0.0001 ≤ deltaX4 8 x2 x3 4 x5 x6 ∧ deltaX4 8 x2 x3 4 x5 x6 ≤ 0.129 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : deltaX4 8 x2 x3 4 x5 x6
      = (-1)*(x2-4)*(x3-4) + (1)*(x2-4)*(x5-4) + (8)*(x2-4) + (1)*(x3-4)*(x6-4) + (8)*(x3-4) + (-1)*(x5-4)*(x6-4) + (8)*(x5-4) + (8)*(x6-4) := by
    unfold deltaX4; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_deltaX5_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    31.96 ≤ deltaX5 8 x2 x3 4 x5 x6 ∧ deltaX5 8 x2 x3 4 x5 x6 ≤ 32.04 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : deltaX5 8 x2 x3 4 x5 x6
      = (-1)*(x2-4)^2 + (1)*(x2-4)*(x3-4) + (-2)*(x2-4)*(x5-4) + (1)*(x2-4)*(x6-4) + (4)*(x2-4) + (1)*(x3-4)*(x6-4) + (-8)*(x5-4) + (4)*(x6-4) + (32) := by
    unfold deltaX5; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_DX1_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -16.001 ≤ g4dDX1 8 x2 x3 4 x5 x6 ∧ g4dDX1 8 x2 x3 4 x5 x6 ≤ -15.935 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : g4dDX1 8 x2 x3 4 x5 x6
      = (1)*(x2-4)*(x5-4) + (-1)*(x2-4)*(x6-4) + (4)*(x2-4) + (-1)*(x3-4)*(x5-4) + (1)*(x3-4)*(x6-4) + (4)*(x3-4) + (4)*(x5-4) + (4)*(x6-4) + (-16) := by
    unfold g4dDX1; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_DX2_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    31.96 ≤ g4dDX2 8 x2 x3 4 x5 x6 ∧ g4dDX2 8 x2 x3 4 x5 x6 ≤ 32.04 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : g4dDX2 8 x2 x3 4 x5 x6
      = (-2)*(x2-4)*(x5-4) + (-8)*(x2-4) + (1)*(x3-4)*(x5-4) + (1)*(x3-4)*(x6-4) + (4)*(x3-4) + (-1)*(x5-4)^2 + (1)*(x5-4)*(x6-4) + (4)*(x5-4) + (32) := by
    unfold g4dDX2; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_DX3_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    31.96 ≤ g4dDX3 8 x2 x3 4 x5 x6 ∧ g4dDX3 8 x2 x3 4 x5 x6 ≤ 32.04 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : g4dDX3 8 x2 x3 4 x5 x6
      = (1)*(x2-4)*(x5-4) + (1)*(x2-4)*(x6-4) + (4)*(x2-4) + (-2)*(x3-4)*(x6-4) + (-8)*(x3-4) + (1)*(x5-4)*(x6-4) + (-1)*(x6-4)^2 + (4)*(x6-4) + (32) := by
    unfold g4dDX3; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_DX6_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    31.96 ≤ g4dDX6 8 x2 x3 4 x5 x6 ∧ g4dDX6 8 x2 x3 4 x5 x6 ≤ 32.04 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : g4dDX6 8 x2 x3 4 x5 x6
      = (1)*(x2-4)*(x3-4) + (1)*(x2-4)*(x5-4) + (-1)*(x3-4)^2 + (1)*(x3-4)*(x5-4) + (-2)*(x3-4)*(x6-4) + (4)*(x3-4) + (4)*(x5-4) + (-8)*(x6-4) + (32) := by
    unfold g4dDX6; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_u126_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    63.999 ≤ upsX 8 x2 x6 ∧ upsX 8 x2 x6 ≤ 64.129 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : upsX 8 x2 x6
      = (-1)*(x2-4)^2 + (2)*(x2-4)*(x6-4) + (16)*(x2-4) + (-1)*(x6-4)^2 + (16)*(x6-4) + (64) := by
    unfold upsX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]

theorem g4w5_u135_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    63.999 ≤ upsX 8 x3 x5 ∧ upsX 8 x3 x5 ≤ 64.129 := by
  obtain ⟨hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56,
    hc1, hc2, hc3, hc4, hc5, hc6⟩ := g4w5_pack h2 h2' h3 h3' h5 h5' h6 h6'
  have hexp : upsX 8 x3 x5
      = (-1)*(x3-4)^2 + (2)*(x3-4)*(x5-4) + (16)*(x3-4) + (-1)*(x5-4)^2 + (16)*(x5-4) + (64) := by
    unfold upsX; ring
  constructor <;> rw [hexp] <;>
    nlinarith only [h2, h2', h3, h3', h5, h5', h6, h6', hs2, hs3, hs5, hs6, hp23, hp25, hp26, hp35, hp36, hp56, hc1, hc2, hc3, hc4, hc5, hc6]


/-- The linear atom `L = −2x₁+x₂+x₃−2x₄+x₅+x₆` on the corner slice. -/
theorem g4w5_L_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -8 ≤ -2 * 8 + x2 + x3 - 2 * 4 + x5 + x6 ∧
      -2 * 8 + x2 + x3 - 2 * 4 + x5 + x6 ≤ -7.983 := by
  constructor <;> linarith

/-! ## The radical `A = √(4·x1·Δ)` on the corner slice -/

theorem g4w5_A_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    63.99 ≤ Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) ∧
      Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) ≤ 64.133 := by
  obtain ⟨hdlo, hdhi⟩ := g4w5_deltaX_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [hdlo]
  · rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 64.133)]
    nlinarith [hdhi]

/-! ## Axiom audit (house style) -/

#print axioms g4w5_deltaX_bounds
#print axioms g4w5_deltaX4_bounds
#print axioms g4w5_deltaX5_bounds
#print axioms g4w5_DX1_bounds
#print axioms g4w5_DX2_bounds
#print axioms g4w5_DX3_bounds
#print axioms g4w5_DX6_bounds
#print axioms g4w5_u126_bounds
#print axioms g4w5_u135_bounds
#print axioms g4w5_L_bounds
#print axioms g4w5_A_bounds

end Kepler.Text
