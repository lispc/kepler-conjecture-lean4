/-
Kepler.Text.Gamma4EnvNum — the `π`, `sol0`, `tau0`, `mm1`, `mm2` rational
enclosures (`~1e-3` absolute) consumed by the `gamma4fgcy` sign analysis.

The `arccos(1/3)` and `arcsin(1/3)` brackets are the PA21 numeric seeds
re-derived here (the originals are `private` in `PackingAuto21`).
-/
import Kepler.Text.Gamma4Env

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## The enclosures

The two `arccos`/`arcsin` rational brackets are the PA21 numeric seeds
re-derived here (the originals are `private` in `PackingAuto21`):
`arccos(1/3) ≤ 1.231` via the triple-angle identity at `1231/3000`, and
`arcsin(1/3) ≤ 17/50` via `Real.sin_ge_sub_cube` at `17/50`. -/

theorem g4d_arccos_third_le : Real.arccos (1 / 3 : ℝ) ≤ 1231 / 1000 := by
  have hw0 : (0 : ℝ) ≤ 1231 / 3000 / 2 := by norm_num
  have hsb := Real.sin_ge_sub_cube hw0
  have hpos : (0 : ℝ) < 1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6 := by norm_num
  have hsq : (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2
      ≤ (Real.sin (1231 / 3000 / 2)) ^ 2 := pow_le_pow_left₀ (by norm_num) hsb 2
  have hhalf := Real.sin_sq_eq_half_sub (x := 1231 / 3000 / 2)
  have hcw : Real.cos (1231 / 3000)
      = 1 - 2 * (Real.sin (1231 / 3000 / 2)) ^ 2 := by
    conv_lhs => rw [← show (2 : ℝ) * (1231 / 3000 / 2) = 1231 / 3000 from by norm_num]
    rw [hhalf]
    ring
  have hcwUB : Real.cos (1231 / 3000)
      ≤ 1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2 := by
    rw [hcw]
    linarith
  have hsinle : Real.sin (1231 / 3000 / 2) ≤ 1231 / 3000 / 2 := by
    have := Real.sin_lt (by norm_num : (0 : ℝ) < 1231 / 3000 / 2)
    linarith
  have hsinpos : (0 : ℝ) ≤ Real.sin (1231 / 3000 / 2) := by linarith
  have hsin2 : (Real.sin (1231 / 3000 / 2)) ^ 2 ≤ (1231 / 3000 / 2) ^ 2 :=
    pow_le_pow_left₀ hsinpos hsinle 2
  have hcwLB : (1 : ℝ) / 2 ≤ Real.cos (1231 / 3000) := by
    rw [hcw]
    have h2 : (1231 / 3000 / 2) ^ 2 ≤ (41 : ℝ) / 100 := by norm_num
    linarith
  have hf : ∀ x y : ℝ, (1 : ℝ) / 2 ≤ x → x ≤ y → 4 * x ^ 3 - 3 * x ≤ 4 * y ^ 3 - 3 * y := by
    intro x y hx hxy
    have hd : 4 * y ^ 3 - 3 * y - (4 * x ^ 3 - 3 * x)
        = (y - x) * (4 * (x * x + y * x + y * y) - 3) := by ring
    have hp1 : (0 : ℝ) ≤ y - x := by linarith
    have hp2 : (0 : ℝ) ≤ 4 * (x * x + y * x + y * y) - 3 := by
      nlinarith [hx, hx, hxy]
    have hprod : (0 : ℝ) ≤ (y - x) * (4 * (x * x + y * x + y * y) - 3) :=
      mul_nonneg hp1 hp2
    linarith [hd, hprod]
  have hmono : 4 * (Real.cos (1231 / 3000)) ^ 3 - 3 * Real.cos (1231 / 3000)
      ≤ 4 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) ^ 3
        - 3 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) :=
    hf _ _ hcwLB hcwUB
  have hfin : 4 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) ^ 3
      - 3 * (1 - 2 * (1231 / 3000 / 2 - (1231 / 3000 / 2) ^ 3 / 6) ^ 2) ≤ (1 : ℝ) / 3 := by
    norm_num
  have hcos3 : Real.cos (3 * (1231 / 3000))
      = 4 * (Real.cos (1231 / 3000)) ^ 3 - 3 * Real.cos (1231 / 3000) :=
    Real.cos_three_mul _
  have hcosT : Real.cos (1231 / 1000) ≤ (1 : ℝ) / 3 := by
    rw [show (1231 : ℝ) / 1000 = 3 * (1231 / 3000) from by norm_num, hcos3]
    exact le_trans hmono hfin
  have hstep : Real.arccos (1 / 3) ≤ Real.arccos (Real.cos (1231 / 1000)) :=
    Real.arccos_le_arccos hcosT
  rw [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_d2])] at hstep
  exact hstep

theorem g4d_arcsin_third_le : Real.arcsin (1 / 3 : ℝ) ≤ 17 / 50 := by
  have hmem : (1 : ℝ) / 3 ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem2 : (17 / 50 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_d2]⟩
  have hsb := Real.sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 17 / 50)
  have hval : (1 : ℝ) / 3 ≤ 17 / 50 - (17 / 50) ^ 3 / 6 := by norm_num
  have hsin : (1 : ℝ) / 3 ≤ Real.sin (17 / 50) := by linarith
  exact (Real.arcsin_le_iff_le_sin hmem hmem2).mpr hsin

/-- Mathlib's rational `π` bracket. -/
theorem g4d_pi_bounds : (3.141592 : ℝ) < Real.pi ∧ Real.pi < 3.1416 :=
  ⟨Real.pi_gt_d6, Real.pi_lt_d4⟩

/-- `sol0 = 3·arccos(1/3) − π ∈ [0.550796, 0.551408]`. -/
theorem g4d_sol0_bounds : (550796 : ℝ) / 1000000 ≤ sol0 ∧ sol0 ≤ 551408 / 1000000 := by
  have hp1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hp2 : Real.pi < 3.1416 := Real.pi_lt_d4
  have ha := g4d_arccos_third_le
  have hb := g4d_arcsin_third_le
  have hsol : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
  constructor
  · rw [hsol, Real.arccos_eq_pi_div_two_sub_arcsin]
    linarith
  · rw [hsol]
    linarith

/-- `tau0 = 4π − 20·sol0 ∈ [1.538208, 1.55048]`. -/
theorem g4d_tau0_bounds : (1538208 : ℝ) / 1000000 ≤ tau0 ∧
    tau0 ≤ 155048 / 100000 := by
  obtain ⟨hslo, hshi⟩ := g4d_sol0_bounds
  have hp1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hp2 : Real.pi < 3.1416 := Real.pi_lt_d4
  have ht : tau0 = 4 * Real.pi - 20 * sol0 := rfl
  constructor <;> rw [ht] <;> linarith

/-- `mm1 = sol0·√8/tau0 ∈ [5023/5000, 507/500]` (true value ≈ 1.0121). -/
theorem g4d_mm1_bounds : (5023 : ℝ) / 5000 ≤ mm1 ∧ mm1 ≤ 507 / 500 := by
  obtain ⟨hslo, hshi⟩ := g4d_sol0_bounds
  obtain ⟨htlo, hthi⟩ := g4d_tau0_bounds
  have h8lo : (7071 : ℝ) / 2500 < Real.sqrt 8 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have h8hi : Real.sqrt 8 ≤ 282843 / 100000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hmm : mm1 = sol0 * Real.sqrt 8 / tau0 := rfl
  have htpos : (0 : ℝ) < tau0 := by linarith
  constructor
  · rw [hmm, le_div_iff₀ htpos]
    have h1 : (5023 : ℝ) / 5000 * tau0 ≤ 5023 / 5000 * (155048 / 100000) :=
      mul_le_mul_of_nonneg_left hthi (by norm_num)
    have h2 : (550796 : ℝ) / 1000000 * (7071 / 2500) ≤ sol0 * Real.sqrt 8 :=
      mul_le_mul hslo h8lo.le (by norm_num) (by linarith)
    nlinarith [h1, h2]
  · rw [hmm, div_le_iff₀ htpos]
    have h1 : sol0 * Real.sqrt 8 ≤ (551408 : ℝ) / 1000000 * (282843 / 100000) :=
      mul_le_mul hshi h8hi (by positivity) (by linarith)
    have h2 : (507 : ℝ) / 500 * (1538208 / 1000000) ≤ 507 / 500 * tau0 :=
      mul_le_mul_of_nonneg_left htlo (by norm_num)
    nlinarith [h1, h2]

/-- `mm2 = (6·sol0 − π)·√2/(6·tau0) ∈ [0.0248, 0.02557]` (true ≈ 0.02541). -/
theorem g4d_mm2_bounds : (0.0248 : ℝ) ≤ mm2 ∧ mm2 ≤ 0.02557 := by
  obtain ⟨hslo, hshi⟩ := g4d_sol0_bounds
  obtain ⟨htlo, hthi⟩ := g4d_tau0_bounds
  have hp1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hp2 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hr2lo : (1414213 : ℝ) / 1000000 < Real.sqrt 2 :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hr2hi : Real.sqrt 2 ≤ 1414214 / 1000000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hmm : mm2 = (6 * sol0 - Real.pi) * Real.sqrt 2 / (6 * tau0) := rfl
  have htpos : (0 : ℝ) < 6 * tau0 := by linarith
  have hNlo : (6 * (550796 : ℝ) / 1000000 - 3.1416) ≤ 6 * sol0 - Real.pi := by
    linarith
  have hNhi : 6 * sol0 - Real.pi ≤ 6 * (551408 : ℝ) / 1000000 - 3.141592 := by
    linarith
  constructor
  · rw [hmm, le_div_iff₀ htpos]
    have hDen : (0.0248 : ℝ) * (6 * tau0) ≤ 0.0248 * (6 * (155048 / 100000)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have hNum : (0.0248 : ℝ) * (6 * (155048 / 100000)) ≤
        (6 * (550796 : ℝ) / 1000000 - 3.1416) * (1414213 / 1000000) := by
      norm_num
    have hPr : (6 * (550796 : ℝ) / 1000000 - 3.1416) * (1414213 / 1000000)
        ≤ (6 * sol0 - Real.pi) * Real.sqrt 2 :=
      mul_le_mul hNlo hr2lo.le (by norm_num) (by linarith)
    nlinarith [hDen, hNum, hPr]
  · rw [hmm, div_le_iff₀ htpos]
    have hNum : (6 * sol0 - Real.pi) * Real.sqrt 2
        ≤ (6 * (551408 : ℝ) / 1000000 - 3.141592) * (1414214 / 1000000) :=
      mul_le_mul hNhi hr2hi (by positivity) (by linarith)
    have hDen : 0.02557 * (6 * (1538208 / 1000000)) ≤ 0.02557 * (6 * tau0) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    have hNum2 : (6 * (551408 : ℝ) / 1000000 - 3.141592) * (1414214 / 1000000)
        ≤ 0.02557 * (6 * (1538208 / 1000000)) := by
      norm_num
    nlinarith [hNum, hDen, hNum2]

/-! ## Axiom audit (house style) -/

#print axioms g4d_pi_bounds
#print axioms g4d_arccos_third_le
#print axioms g4d_arcsin_third_le
#print axioms g4d_sol0_bounds
#print axioms g4d_tau0_bounds
#print axioms g4d_mm1_bounds
#print axioms g4d_mm2_bounds

end Kepler.Text
