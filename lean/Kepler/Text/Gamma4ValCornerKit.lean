/-
Kepler.Text.Gamma4ValCornerKit — lane `gamma4-val1e6`, V5 assembly.

`g4v_corner_value_bounds` is the reusable "certified corner value" kit: it
combines interval data for `volY`, `Σ solY`, `Σ lmfun·dihY` and the two
π-scaled coefficients into two-sided bounds for `gamma4fgcy`.

The concrete instances use the V1–V4 value chain (`π` 1e-20, `arccos(1/3)`
1.1e-9, `mm1` 1e-7, `mm2` 1e-8, corner `atan` 1e-8) and certify

* `(2hplus, 2⁵)`: `gamma4fgcy ∈ [2.23e-6, 2.62e-6]` (true `2.412783872…e-6`);
* `(√8, 2⁵)`: `gamma4fgcy ∈ [-1.6e-7, 1.4e-7]`; with the exact theorem
  `gamma4_at_sqrt8 : gamma4fgcy (√8) 2⁵ lmfun = 0`, this is the strong
  self-check (0 strictly inside the kit's interval).
-/
import Kepler.Text.Gamma4ValCorner

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-- **The kit core.**  From two-sided bounds on `volY`, the four-term `solY`
sum `S`, the six-term weighted `dihY` sum `D`, and on the coefficients
`A = 2·mm1/π`, `B = 8·mm2/π`, conclude two-sided bounds on
`gamma4fgcy y₁…y₆ lmfun`.  The four `0 ≤ ·lo` hypotheses supply the
non-negativity needed to multiply interval bounds. -/
theorem g4v_corner_value_bounds
    {y1 y2 y3 y4 y5 y6 Vlo Vhi Slo Shi Dlo Dhi Alo Ahi Blo Bhi : ℝ}
    (hV : Vlo ≤ volY y1 y2 y3 y4 y5 y6 ∧ volY y1 y2 y3 y4 y5 y6 ≤ Vhi)
    (hS : Slo ≤ solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
        solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3 ∧
      solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
        solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3 ≤ Shi)
    (hD : Dlo ≤ lmfun (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
        lmfun (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
        lmfun (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
        lmfun (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
        lmfun (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
        lmfun (y6 / 2) * dihY y6 y1 y5 y3 y4 y2 ∧
      lmfun (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
        lmfun (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
        lmfun (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
        lmfun (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
        lmfun (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
        lmfun (y6 / 2) * dihY y6 y1 y5 y3 y4 y2 ≤ Dhi)
    (hA : Alo ≤ 2 * mm1 / Real.pi ∧ 2 * mm1 / Real.pi ≤ Ahi)
    (hB : Blo ≤ 8 * mm2 / Real.pi ∧ 8 * mm2 / Real.pi ≤ Bhi)
    (hSlo : 0 ≤ Slo) (hDlo : 0 ≤ Dlo) (hAlo : 0 ≤ Alo) (hBlo : 0 ≤ Blo) :
    Vlo - Ahi * Shi + Blo * Dlo ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ∧
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ≤ Vhi - Alo * Slo + Bhi * Dhi := by
  have hS0 : 0 ≤ solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3 := le_trans hSlo hS.1
  have hD0 : 0 ≤ lmfun (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
      lmfun (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
      lmfun (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
      lmfun (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
      lmfun (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
      lmfun (y6 / 2) * dihY y6 y1 y5 y3 y4 y2 := le_trans hDlo hD.1
  have hA0 : 0 ≤ 2 * mm1 / Real.pi := le_trans hAlo hA.1
  have hB0 : 0 ≤ 8 * mm2 / Real.pi := le_trans hBlo hB.1
  have hAS : (2 * mm1 / Real.pi) *
      (solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
        solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3) ≤ Ahi * Shi :=
    mul_le_mul hA.2 hS.2 hS0 (le_trans hAlo (le_trans hA.1 hA.2))
  have hAS2 : Alo * Slo ≤ (2 * mm1 / Real.pi) *
      (solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
        solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3) :=
    mul_le_mul hA.1 hS.1 hSlo hA0
  have hBD : Blo * Dlo ≤ (8 * mm2 / Real.pi) *
      (lmfun (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
        lmfun (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
        lmfun (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
        lmfun (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
        lmfun (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
        lmfun (y6 / 2) * dihY y6 y1 y5 y3 y4 y2) :=
    mul_le_mul hB.1 hD.1 hDlo hB0
  have hBD2 : (8 * mm2 / Real.pi) *
      (lmfun (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
        lmfun (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
        lmfun (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
        lmfun (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
        lmfun (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
        lmfun (y6 / 2) * dihY y6 y1 y5 y3 y4 y2) ≤ Bhi * Dhi :=
    mul_le_mul hB.2 hD.2 hD0 (le_trans hBlo (le_trans hB.1 hB.2))
  unfold gamma4fgcy vol4f
  constructor <;> nlinarith [hV.1, hV.2, hAS, hAS2, hBD, hBD2]

/-- The `A = 2·mm1/π`, `B = 8·mm2/π` interval pair derived from V2. -/
theorem g4v_AB_bounds :
    (0.6443106485 : ℝ) ≤ 2 * mm1 / Real.pi ∧
      2 * mm1 / Real.pi ≤ 0.6443107122 ∧
      (0.0647174928 : ℝ) ≤ 8 * mm2 / Real.pi ∧
      8 * mm2 / Real.pi ≤ 0.0647175183 := by
  obtain ⟨hm11, hm12⟩ := g4v_mm1_bounds
  obtain ⟨hm21, hm22⟩ := g4v_mm2_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · rw [le_div_iff₀ hpi]; nlinarith [hm11, hp1]
  constructor
  · rw [div_le_iff₀ hpi]; nlinarith [hm12, hp2]
  constructor
  · rw [le_div_iff₀ hpi]; nlinarith [hm21, hp1]
  · rw [div_le_iff₀ hpi]; nlinarith [hm22, hp2]

/-- **V5 concrete corner `(2hplus, 2⁵)`**: the razor-thin
`nliRestGLFVCVK4` corner value is certified in `[2.23e-6, 2.62e-6]`. -/
theorem g4v_corner_2hplus_bounds :
    (0.00000223 : ℝ) ≤ gamma4fgcy (2 * hplus) 2 2 2 2 2 lmfun ∧
      gamma4fgcy (2 * hplus) 2 2 2 2 2 lmfun ≤ 0.00000262 := by
  have h := g4v_corner_value_bounds
    (y1 := 2 * hplus) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := 0.985249591) (Vhi := 0.9852496)
    (Slo := 2.119863293) (Shi := 2.119863428)
    (Dlo := 5.88099662) (Dhi := 5.880996673)
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    g4v_2hp_volY_bounds g4v_2hp_S_bounds g4v_2hp_D_bounds
    ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]

/-- **V5 concrete corner `(√8, 2⁵)`** (self-check): the kit certifies
`gamma4fgcy ∈ [-1.6e-7, 1.4e-7]`. -/
theorem g4v_corner_sqrt8_bounds :
    (-0.00000016 : ℝ) ≤ gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun ∧
      gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun ≤ 0.00000014 := by
  have h := g4v_corner_value_bounds
    (y1 := Real.sqrt 8) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := 0.94280904) (Vhi := 0.942809047)
    (Slo := 2.039021453) (Shi := 2.039021461)
    (Dlo := 5.731899707) (Dhi := 5.731899711)
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    g4v_s8_volY_bounds g4v_s8_S_bounds g4v_s8_D_bounds
    ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]

/-- **V5 strong self-check**: at `(√8, 2⁵)` the exact value is `0`
(`gamma4_at_sqrt8`) and the kit's interval is `[-1.6e-7, 1.4e-7]`, which
contains `0` strictly. -/
theorem g4v_sqrt8_selfcheck :
    gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun = 0 ∧
      (-0.00000016 : ℝ) ≤ gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun ∧
      gamma4fgcy (Real.sqrt 8) 2 2 2 2 2 lmfun ≤ 0.00000014 :=
  ⟨gamma4_at_sqrt8, g4v_corner_sqrt8_bounds⟩

/-! ## Axiom audit -/

#print axioms g4v_corner_value_bounds
#print axioms g4v_AB_bounds
#print axioms g4v_corner_2hplus_bounds
#print axioms g4v_corner_sqrt8_bounds
#print axioms g4v_sqrt8_selfcheck

end Kepler.Text
