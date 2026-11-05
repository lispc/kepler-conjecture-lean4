/-
Kepler.Text.Gamma4ValCorner0 — lane `gamma4-val1e6`, V5 at the fold corner.

The critical `(2h0, 2,2,2,2,2)` corner (`2h0 = 2.52`, the `lmfun` fold plane),
where the thin B2 banks `QITNPEA3848804089` (7.97e-5) and
`BIXPCGW9455898160` (1.31e-4) attain their refined minimum.

The kit certifies `gamma4fgcy ∈ [-5.559154e-3, -5.558778e-3]` (width 3.76e-7;
true value `-5.558935401…e-3`).  For `BIXPCGW9455898160`
(`main = gamma4 + 0.00569`) this yields the machine-checked margin
`[1.30846e-4, 1.31222e-4]` — 350× tighter than the `1.31e-4` the bank needs,
which is exactly the WBL-2 gap this lane was opened to close.
-/
import Kepler.Text.Gamma4ValArctan2
import Kepler.Text.Gamma4ValCornerKit

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-! ## `sqrt` normalisations -/

theorem g4v_sqrt_den0a :
    Real.sqrt (889979284656 / 244140625) =
      Real.sqrt 889979284656 / 15625 := by
  have h : (889979284656 / 244140625 : ℝ) =
      889979284656 * (1 / 15625) ^ 2 := by norm_num
  rw [h, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 889979284656),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 15625)]
  ring

theorem g4v_sqrt_den0b :
    Real.sqrt (896930496 / 390625) = Real.sqrt 896930496 / 625 := by
  have h : (896930496 / 390625 : ℝ) = 896930496 * (1 / 625) ^ 2 := by norm_num
  rw [h, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 896930496),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 625)]
  ring

theorem g4v_lmfun_h0 : lmfun h0 = 0 := by
  norm_num [lmfun, h0]

/-! ## `dihY` values at `(2h0, 2⁵)` -/

theorem g4v_2h0_dih_eq1 :
    dihY (2 * h0) 2 2 2 2 2 =
      Real.pi / 2 + Real.arctan ((-(4092039 / 390625)) /
        Real.sqrt (889979284656 / 244140625)) := by
  have hsq := g4v_sqrt_den0a
  have hbr : |(-(4092039 / 390625) : ℝ)| <
      Real.sqrt (889979284656 / 244140625) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [h0, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

theorem g4v_2h0_dih_eq2 :
    dihY 2 (2 * h0) 2 2 2 2 =
      Real.pi / 2 + Real.arctan ((-(15876 / 625)) /
        Real.sqrt (896930496 / 390625)) := by
  have hsq := g4v_sqrt_den0b
  have hbr : |(-(15876 / 625) : ℝ)| < Real.sqrt (896930496 / 390625) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [h0, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

theorem g4v_2h0_dih_eq3 :
    dihY 2 2 (2 * h0) 2 2 2 =
      Real.pi / 2 + Real.arctan ((-(15876 / 625)) /
        Real.sqrt (896930496 / 390625)) := by
  have hsq := g4v_sqrt_den0b
  have hbr : |(-(15876 / 625) : ℝ)| < Real.sqrt (896930496 / 390625) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [h0, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

theorem g4v_2h0_dih_eq4 :
    dihY 2 2 2 (2 * h0) 2 2 =
      Real.pi / 2 + Real.arctan ((1752 / 625) /
        Real.sqrt (896930496 / 390625)) := by
  have hsq := g4v_sqrt_den0b
  have hbr : |(1752 / 625 : ℝ)| < Real.sqrt (896930496 / 390625) := by
    rw [abs_of_pos (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [h0, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

theorem g4v_2h0_dih_eq5 :
    dihY 2 2 2 2 (2 * h0) 2 =
      Real.pi / 2 + Real.arctan ((-(15876 / 625)) /
        Real.sqrt (896930496 / 390625)) := by
  have hsq := g4v_sqrt_den0b
  have hbr : |(-(15876 / 625) : ℝ)| < Real.sqrt (896930496 / 390625) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [h0, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

theorem g4v_2h0_dih_eq6 :
    dihY 2 2 2 2 2 (2 * h0) =
      Real.pi / 2 + Real.arctan ((-(15876 / 625)) /
        Real.sqrt (896930496 / 390625)) := by
  have hsq := g4v_sqrt_den0b
  have hbr : |(-(15876 / 625) : ℝ)| < Real.sqrt (896930496 / 390625) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [h0, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-! ## `S` / `D` formulas and bounds -/

theorem g4v_2h0_S_eq :
    solY (2 * h0) 2 2 2 2 2 + solY (2 * h0) 2 2 2 2 2 +
      solY 2 2 2 (2 * h0) 2 2 + solY 2 2 2 (2 * h0) 2 2 =
      (Real.pi / 2 + Real.arctan ((-(4092039 / 390625)) /
        Real.sqrt (889979284656 / 244140625))) * 2 +
      (Real.pi / 2 + Real.arctan ((-(15876 / 625)) /
        Real.sqrt (896930496 / 390625))) * 8 +
      (Real.pi / 2 + Real.arctan ((1752 / 625) /
        Real.sqrt (896930496 / 390625))) * 2 - 4 * Real.pi := by
  simp only [solY, g4v_2h0_dih_eq1, g4v_2h0_dih_eq2, g4v_2h0_dih_eq3,
    g4v_2h0_dih_eq4, g4v_2h0_dih_eq5, g4v_2h0_dih_eq6]
  ring

theorem g4v_2h0_D_eq :
    lmfun (2 * h0 / 2) * dihY (2 * h0) 2 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 2 (2 * h0) 2 2 2 +
      lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 2 2 (2 * h0) 2 2 +
      lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 =
      (Real.pi / 2 + Real.arctan ((-(15876 / 625)) /
        Real.sqrt (896930496 / 390625))) * 4 +
      (Real.pi / 2 + Real.arctan ((1752 / 625) /
        Real.sqrt (896930496 / 390625))) := by
  rw [show (2 * h0 / 2) = h0 by ring]
  simp only [g4v_lmfun_h0, show (2:ℝ) / 2 = 1 by norm_num, g4v_lmfun_one,
    zero_mul, one_mul]
  rw [g4v_2h0_dih_eq2, g4v_2h0_dih_eq3, g4v_2h0_dih_eq4]
  ring

theorem g4v_2h0_S_bounds :
    (2.156941194 : ℝ) ≤
      solY (2 * h0) 2 2 2 2 2 + solY (2 * h0) 2 2 2 2 2 +
        solY 2 2 2 (2 * h0) 2 2 + solY 2 2 2 (2 * h0) 2 2 ∧
      solY (2 * h0) 2 2 2 2 2 + solY (2 * h0) 2 2 2 2 2 +
        solY 2 2 2 (2 * h0) 2 2 + solY 2 2 2 (2 * h0) 2 2 ≤ 2.156941313 := by
  rw [g4v_2h0_S_eq]
  obtain ⟨ha11, ha12⟩ := g4v_atan_B1_bounds
  obtain ⟨ha21, ha22⟩ := g4v_atan_B2_bounds
  obtain ⟨ha31, ha32⟩ := g4v_atan_B3_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  constructor <;> linarith

theorem g4v_2h0_D_bounds :
    (5.962653456 : ℝ) ≤
      lmfun (2 * h0 / 2) * dihY (2 * h0) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (2 * h0) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (2 * h0) 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 ∧
      lmfun (2 * h0 / 2) * dihY (2 * h0) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (2 * h0) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (2 * h0) 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * h0) 2 2 2 2 ≤ 5.962653504 := by
  rw [g4v_2h0_D_eq]
  obtain ⟨ha21, ha22⟩ := g4v_atan_B2_bounds
  obtain ⟨ha31, ha32⟩ := g4v_atan_B3_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  constructor <;> linarith

theorem g4v_2h0_volY_eq :
    volY (2 * h0) 2 2 2 2 2 = Real.sqrt (56058156 / 390625) / 12 := by
  unfold volY volXf
  norm_num [h0, deltaX]

theorem g4v_2h0_volY_bounds :
    (0.998293258 : ℝ) ≤ volY (2 * h0) 2 2 2 2 2 ∧
      volY (2 * h0) 2 2 2 2 2 ≤ 0.998293267 := by
  rw [g4v_2h0_volY_eq]
  have hsq1 : (11.9795191 : ℝ) ^ 2 ≤ 56058156 / 390625 := by norm_num
  have hsq2 : (56058156 / 390625 : ℝ) ≤ (11.9795192) ^ 2 := by norm_num
  have h1 : (11.9795191 : ℝ) ≤ Real.sqrt (56058156 / 390625) :=
    Real.le_sqrt_of_sq_le hsq1
  have h2 : Real.sqrt (56058156 / 390625) ≤ 11.9795192 :=
    (Real.sqrt_le_left (by norm_num)).mpr hsq2
  constructor <;> linarith

/-- **V5 at the fold corner** `(2h0, 2⁵)`: `gamma4fgcy` is certified in
`[-5.559154e-3, -5.558778e-3]` (width 3.76e-7). -/
theorem g4v_corner_2h0_bounds :
    (-0.005559154 : ℝ) ≤ gamma4fgcy (2 * h0) 2 2 2 2 2 lmfun ∧
      gamma4fgcy (2 * h0) 2 2 2 2 2 lmfun ≤ -0.005558775 := by
  have h := g4v_corner_value_bounds
    (y1 := 2 * h0) (y2 := 2) (y3 := 2) (y4 := 2) (y5 := 2) (y6 := 2)
    (Vlo := 0.998293258) (Vhi := 0.998293267)
    (Slo := 2.156941194) (Shi := 2.156941313)
    (Dlo := 5.962653456) (Dhi := 5.962653504)
    (Alo := 0.6443106485) (Ahi := 0.6443107122)
    (Blo := 0.0647174928) (Bhi := 0.0647175183)
    g4v_2h0_volY_bounds g4v_2h0_S_bounds g4v_2h0_D_bounds
    ⟨g4v_AB_bounds.1, g4v_AB_bounds.2.1⟩
    ⟨g4v_AB_bounds.2.2.1, g4v_AB_bounds.2.2.2⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor <;> linarith [h.1, h.2]

/-- **WBL-2 witness**: at the refined argmin `(2h0, 2⁵)` of
`BIXPCGW9455898160`, the certified `main = gamma4fgcy + 0.00569` lies in
`[1.30846e-4, 1.31222e-4]` — far above `0` with the value chain's `~4e-7`
precision (the bank needs only `< 1.31e-4`). -/
theorem g4v_bixpcgw_9455898160_margin :
    (0.000130846 : ℝ) ≤ gamma4fgcy (2 * h0) 2 2 2 2 2 lmfun + 0.00569 ∧
      gamma4fgcy (2 * h0) 2 2 2 2 2 lmfun + 0.00569 ≤ 0.000131225 := by
  obtain ⟨h1, h2⟩ := g4v_corner_2h0_bounds
  constructor <;> linarith

#print axioms g4v_sqrt_den0a
#print axioms g4v_sqrt_den0b
#print axioms g4v_lmfun_h0
#print axioms g4v_2h0_dih_eq1
#print axioms g4v_2h0_dih_eq2
#print axioms g4v_2h0_dih_eq3
#print axioms g4v_2h0_dih_eq4
#print axioms g4v_2h0_dih_eq5
#print axioms g4v_2h0_dih_eq6
#print axioms g4v_2h0_S_eq
#print axioms g4v_2h0_D_eq
#print axioms g4v_2h0_S_bounds
#print axioms g4v_2h0_D_bounds
#print axioms g4v_2h0_volY_eq
#print axioms g4v_2h0_volY_bounds
#print axioms g4v_corner_2h0_bounds
#print axioms g4v_bixpcgw_9455898160_margin

end Kepler.Text
