/-
Kepler.Text.Gamma4ParamD — lane `gamma4-w5`, W5-a base envelope (part 2).

The six `D_s = ∂dihXf/∂x_s` on the corner slice `x1 = 8`, `x4 = 4`,
`x2,x3,x5,x6 ∈ [4,4.004001]` (the `(y1,y4) = (√8,2)` corner of the YOUOBF-v2
box).  Envelopes (from `Gamma4Param`'s atom bounds):

| slot | enclosure | width |
|---|---|---:|
| `D1` | `[0.1237, 0.1258]` | 2.1e−3 |
| `D2`,`D3`,`D5`,`D6` | `[−0.1252, −0.1243]` | 9.0e−4 |
| `D4` | `[0.2494, 0.2501]` | 7.0e−4 |

and the exact corner values `D1 = 1/8`, `D2 = D3 = D5 = D6 = −1/8`,
`D4 = 1/4` at `(8,4,4,4,4,4)`.  This is the "one base narrow enclosure" of the
recommended Lipschitz route; the wide-box Lipschitz half is a GAP (see
`DELIVERY.md`).
-/
import Kepler.Text.Gamma4Param

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-! ## The four negative `D` slots (common helper) -/

private theorem g4w5_negD {A u Dv : ℝ}
    (hA : 63.99 ≤ A) (hA' : A ≤ 64.133)
    (hu : 63.999 ≤ u) (hu' : u ≤ 64.129)
    (hD : 31.96 ≤ Dv) (hD' : Dv ≤ 32.04) :
    -0.1252 ≤ -2 * 8 * Dv / (A * u) ∧ -2 * 8 * Dv / (A * u) ≤ -0.1243 := by
  have hApos : (0:ℝ) < A := by linarith
  have huP : (0:ℝ) < u := by linarith
  have hden : (0:ℝ) < A * u := mul_pos hApos huP
  have hdenlo : 63.99 * 63.999 ≤ A * u :=
    mul_le_mul hA hu (by norm_num) (by linarith)
  have hdenhi : A * u ≤ 64.133 * 64.129 :=
    mul_le_mul hA' hu' (by linarith) (by norm_num)
  have hpos_lo : 0.1243 ≤ (2 * 8) * Dv / (A * u) := by
    rw [le_div_iff₀ hden]
    nlinarith [hdenhi, hD]
  have hpos_hi : (2 * 8) * Dv / (A * u) ≤ 0.1252 := by
    rw [div_le_iff₀ hden]
    nlinarith [hdenlo, hD']
  have heq : -2 * 8 * Dv / (A * u) = -((2 * 8) * Dv / (A * u)) := by ring
  constructor
  · rw [heq]; linarith
  · rw [heq]; linarith

/-! ## `D2`, `D3`, `D5`, `D6` -/

theorem g4w5_D2_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -0.1252 ≤ g4dDihX2 8 x2 x3 4 x5 x6 ∧ g4dDihX2 8 x2 x3 4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hAlo, hAhi⟩ := g4w5_A_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hulo, huhi⟩ := g4w5_u126_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hXlo, hXhi⟩ := g4w5_DX3_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  have h := g4w5_negD hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX2
  convert h using 2 <;> ring

theorem g4w5_D3_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -0.1252 ≤ g4dDihX3 8 x2 x3 4 x5 x6 ∧ g4dDihX3 8 x2 x3 4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hAlo, hAhi⟩ := g4w5_A_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hulo, huhi⟩ := g4w5_u135_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hXlo, hXhi⟩ := g4w5_DX2_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  have h := g4w5_negD hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX3
  convert h using 2 <;> ring

theorem g4w5_D5_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -0.1252 ≤ g4dDihX5 8 x2 x3 4 x5 x6 ∧ g4dDihX5 8 x2 x3 4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hAlo, hAhi⟩ := g4w5_A_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hulo, huhi⟩ := g4w5_u135_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hXlo, hXhi⟩ := g4w5_DX6_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  have h := g4w5_negD hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX5
  convert h using 2 <;> ring

theorem g4w5_D6_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    -0.1252 ≤ g4dDihX6 8 x2 x3 4 x5 x6 ∧ g4dDihX6 8 x2 x3 4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hAlo, hAhi⟩ := g4w5_A_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hulo, huhi⟩ := g4w5_u126_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hXlo, hXhi⟩ := g4w5_deltaX5_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  have h := g4w5_negD hAlo hAhi hulo huhi hXlo hXhi
  unfold g4dDihX6
  convert h using 2 <;> ring

/-! ## `D4` -/

theorem g4w5_D4_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    0.2494 ≤ g4dDihX4 8 x2 x3 4 x5 x6 ∧ g4dDihX4 8 x2 x3 4 x5 x6 ≤ 0.2501 := by
  obtain ⟨hAlo, hAhi⟩ := g4w5_A_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  have hApos : (0:ℝ) < Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 63.99) hAlo
  constructor
  · have hkey : 0.2494 ≤ (2 * 8) / Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) := by
      rw [le_div_iff₀ hApos]
      nlinarith [hAhi]
    simpa only [g4dDihX4] using hkey
  · have hkey : (2 * 8) / Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) ≤ 0.2501 := by
      rw [div_le_iff₀ hApos]
      nlinarith [hAlo]
    simpa only [g4dDihX4] using hkey

/-! ## `D1` -/

theorem g4w5_D1_bounds {x2 x3 x5 x6 : ℝ}
    (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.004001)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.004001)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.004001)
    (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.004001) :
    0.1237 ≤ g4dDihX1 8 x2 x3 4 x5 x6 ∧ g4dDihX1 8 x2 x3 4 x5 x6 ≤ 0.1258 := by
  obtain ⟨hD4lo, hD4hi⟩ := g4w5_deltaX4_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hΔlo, hΔhi⟩ := g4w5_deltaX_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hX1lo, hX1hi⟩ := g4w5_DX1_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hLlo, hLhi⟩ := g4w5_L_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hAlo, hAhi⟩ := g4w5_A_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hulo, huhi⟩ := g4w5_u126_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  obtain ⟨hvlo, hvhi⟩ := g4w5_u135_bounds h2 h2' h3 h3' h5 h5' h6 h6'
  have ht1lo : -0.013 ≤ deltaX4 8 x2 x3 4 x5 x6 * deltaX 8 x2 x3 4 x5 x6 := by
    nlinarith [hD4lo, hD4hi, hΔlo, hΔhi]
  have ht1hi : deltaX4 8 x2 x3 4 x5 x6 * deltaX 8 x2 x3 4 x5 x6 ≤ 16.59 := by
    nlinarith [hD4lo, hD4hi, hΔlo, hΔhi]
  have ht2lo : -16.52 ≤ 8 * (deltaX4 8 x2 x3 4 x5 x6 * g4dDX1 8 x2 x3 4 x5 x6) := by
    nlinarith [hD4lo, hD4hi, hX1lo, hX1hi]
  have ht2hi : 8 * (deltaX4 8 x2 x3 4 x5 x6 * g4dDX1 8 x2 x3 4 x5 x6) ≤ 0.013 := by
    nlinarith [hD4lo, hD4hi, hX1lo, hX1hi]
  have ht3lo : 16347 ≤ -16 * (deltaX 8 x2 x3 4 x5 x6 * (-2 * 8 + x2 + x3 - 2 * 4 + x5 + x6)) := by
    nlinarith [hΔlo, hΔhi, hLlo, hLhi]
  have ht3hi : -16 * (deltaX 8 x2 x3 4 x5 x6 * (-2 * 8 + x2 + x3 - 2 * 4 + x5 + x6)) ≤ 16452 := by
    nlinarith [hΔlo, hΔhi, hLlo, hLhi]
  have hNlo : 16330 ≤ deltaX4 8 x2 x3 4 x5 x6 * deltaX 8 x2 x3 4 x5 x6
      + 8 * (deltaX4 8 x2 x3 4 x5 x6 * g4dDX1 8 x2 x3 4 x5 x6)
      - 16 * (deltaX 8 x2 x3 4 x5 x6 * (-2 * 8 + x2 + x3 - 2 * 4 + x5 + x6)) := by
    linarith
  have hNhi : deltaX4 8 x2 x3 4 x5 x6 * deltaX 8 x2 x3 4 x5 x6
      + 8 * (deltaX4 8 x2 x3 4 x5 x6 * g4dDX1 8 x2 x3 4 x5 x6)
      - 16 * (deltaX 8 x2 x3 4 x5 x6 * (-2 * 8 + x2 + x3 - 2 * 4 + x5 + x6)) ≤ 16469 := by
    linarith
  have hdenpos : (0:ℝ) < Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6)
      * (upsX 8 x2 x6 * upsX 8 x3 x5) := by
    have h1 : (0:ℝ) < Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) :=
      lt_of_lt_of_le (by norm_num : (0:ℝ) < 63.99) hAlo
    have h2 : (0:ℝ) < upsX 8 x2 x6 * upsX 8 x3 x5 :=
      mul_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 63.999) hulo)
        (lt_of_lt_of_le (by norm_num : (0:ℝ) < 63.999) hvlo)
    exact mul_pos h1 h2
  have hdenhi : Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) * (upsX 8 x2 x6 * upsX 8 x3 x5)
      ≤ 64.133 * (64.129 * 64.129) := by
    apply mul_le_mul hAhi _ (by positivity) (by norm_num)
    exact mul_le_mul huhi hvhi (by linarith [hvlo]) (by norm_num)
  have hdenlo : 63.99 * (63.999 * 63.999)
      ≤ Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6) * (upsX 8 x2 x6 * upsX 8 x3 x5) := by
    apply mul_le_mul hAlo _ (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0:ℝ) < 63.99) hAlo).le
    exact mul_le_mul hulo hvlo (by norm_num)
      (lt_of_lt_of_le (by norm_num : (0:ℝ) < 63.999) hulo).le
  constructor
  · have hkey : 0.1237 ≤ 2 * (deltaX4 8 x2 x3 4 x5 x6 * deltaX 8 x2 x3 4 x5 x6
        + 8 * deltaX4 8 x2 x3 4 x5 x6 * g4dDX1 8 x2 x3 4 x5 x6
        - 2 * 8 * deltaX 8 x2 x3 4 x5 x6 * (-2 * 8 + x2 + x3 - 2 * 4 + x5 + x6))
        / (Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6)
            * (upsX 8 x2 x6 * upsX 8 x3 x5)) := by
      rw [le_div_iff₀ hdenpos]
      nlinarith [hNlo, hdenhi]
    simpa only [g4dDihX1] using hkey
  · have hkey : 2 * (deltaX4 8 x2 x3 4 x5 x6 * deltaX 8 x2 x3 4 x5 x6
        + 8 * deltaX4 8 x2 x3 4 x5 x6 * g4dDX1 8 x2 x3 4 x5 x6
        - 2 * 8 * deltaX 8 x2 x3 4 x5 x6 * (-2 * 8 + x2 + x3 - 2 * 4 + x5 + x6))
        / (Real.sqrt (4 * 8 * deltaX 8 x2 x3 4 x5 x6)
            * (upsX 8 x2 x6 * upsX 8 x3 x5)) ≤ 0.1258 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [hNhi, hdenlo]
    simpa only [g4dDihX1] using hkey

/-! ## Exact corner values at `(x1,…,x6) = (8,4,4,4,4,4)` -/

theorem g4w5_D1_corner : g4dDihX1 8 4 4 4 4 4 = 1/8 := by
  unfold g4dDihX1 deltaX deltaX4 g4dDX1 upsX
  norm_num

theorem g4w5_D2_corner : g4dDihX2 8 4 4 4 4 4 = -1/8 := by
  unfold g4dDihX2 deltaX g4dDX3 upsX
  norm_num

theorem g4w5_D3_corner : g4dDihX3 8 4 4 4 4 4 = -1/8 := by
  unfold g4dDihX3 deltaX g4dDX2 upsX
  norm_num

theorem g4w5_D4_corner : g4dDihX4 8 4 4 4 4 4 = 1/4 := by
  unfold g4dDihX4 deltaX
  norm_num

theorem g4w5_D5_corner : g4dDihX5 8 4 4 4 4 4 = -1/8 := by
  unfold g4dDihX5 deltaX g4dDX6 upsX
  norm_num

theorem g4w5_D6_corner : g4dDihX6 8 4 4 4 4 4 = -1/8 := by
  unfold g4dDihX6 deltaX deltaX5 upsX
  norm_num

/-! ## Box-level restatements on `g4w5Corner` -/

theorem g4w5_D1_bounds_box {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : g4w5Corner x1 x2 x3 x4 x5 x6) :
    0.1237 ≤ g4dDihX1 x1 x2 x3 x4 x5 x6 ∧ g4dDihX1 x1 x2 x3 x4 x5 x6 ≤ 0.1258 := by
  obtain ⟨hx1, h2, h2', h3, h3', hx4, h5, h5', h6, h6'⟩ := h
  subst hx1; subst hx4
  exact g4w5_D1_bounds h2 h2' h3 h3' h5 h5' h6 h6'

theorem g4w5_D2_bounds_box {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : g4w5Corner x1 x2 x3 x4 x5 x6) :
    -0.1252 ≤ g4dDihX2 x1 x2 x3 x4 x5 x6 ∧ g4dDihX2 x1 x2 x3 x4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hx1, h2, h2', h3, h3', hx4, h5, h5', h6, h6'⟩ := h
  subst hx1; subst hx4
  exact g4w5_D2_bounds h2 h2' h3 h3' h5 h5' h6 h6'

theorem g4w5_D3_bounds_box {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : g4w5Corner x1 x2 x3 x4 x5 x6) :
    -0.1252 ≤ g4dDihX3 x1 x2 x3 x4 x5 x6 ∧ g4dDihX3 x1 x2 x3 x4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hx1, h2, h2', h3, h3', hx4, h5, h5', h6, h6'⟩ := h
  subst hx1; subst hx4
  exact g4w5_D3_bounds h2 h2' h3 h3' h5 h5' h6 h6'

theorem g4w5_D4_bounds_box {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : g4w5Corner x1 x2 x3 x4 x5 x6) :
    0.2494 ≤ g4dDihX4 x1 x2 x3 x4 x5 x6 ∧ g4dDihX4 x1 x2 x3 x4 x5 x6 ≤ 0.2501 := by
  obtain ⟨hx1, h2, h2', h3, h3', hx4, h5, h5', h6, h6'⟩ := h
  subst hx1; subst hx4
  exact g4w5_D4_bounds h2 h2' h3 h3' h5 h5' h6 h6'

theorem g4w5_D5_bounds_box {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : g4w5Corner x1 x2 x3 x4 x5 x6) :
    -0.1252 ≤ g4dDihX5 x1 x2 x3 x4 x5 x6 ∧ g4dDihX5 x1 x2 x3 x4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hx1, h2, h2', h3, h3', hx4, h5, h5', h6, h6'⟩ := h
  subst hx1; subst hx4
  exact g4w5_D5_bounds h2 h2' h3 h3' h5 h5' h6 h6'

theorem g4w5_D6_bounds_box {x1 x2 x3 x4 x5 x6 : ℝ}
    (h : g4w5Corner x1 x2 x3 x4 x5 x6) :
    -0.1252 ≤ g4dDihX6 x1 x2 x3 x4 x5 x6 ∧ g4dDihX6 x1 x2 x3 x4 x5 x6 ≤ -0.1243 := by
  obtain ⟨hx1, h2, h2', h3, h3', hx4, h5, h5', h6, h6'⟩ := h
  subst hx1; subst hx4
  exact g4w5_D6_bounds h2 h2' h3 h3' h5 h5' h6 h6'

/-! ## Axiom audit (house style) -/

#print axioms g4w5_D1_bounds
#print axioms g4w5_D2_bounds
#print axioms g4w5_D3_bounds
#print axioms g4w5_D4_bounds
#print axioms g4w5_D5_bounds
#print axioms g4w5_D6_bounds
#print axioms g4w5_D1_corner
#print axioms g4w5_D2_corner
#print axioms g4w5_D3_corner
#print axioms g4w5_D4_corner
#print axioms g4w5_D5_corner
#print axioms g4w5_D6_corner
#print axioms g4w5_D1_bounds_box
#print axioms g4w5_D2_bounds_box
#print axioms g4w5_D3_bounds_box
#print axioms g4w5_D4_bounds_box
#print axioms g4w5_D5_bounds_box
#print axioms g4w5_D6_bounds_box

end Kepler.Text
