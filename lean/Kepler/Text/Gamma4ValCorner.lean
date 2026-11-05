/-
Kepler.Text.Gamma4ValCorner — lane `gamma4-val1e6`, V5.

The reusable "certified corner value" kit: `g4v_corner_value_bounds` takes
two-sided bounds for `volY`, the four-term `solY` sum, the six-term weighted
`dihY` sum, and the two `π`-scaled coefficient intervals `2·mm1/π`,
`8·mm2/π`, and returns two-sided bounds for `gamma4fgcy`.

Two concrete instantiations at the B2 corner alphabet:
* `(2hplus, 2, 2, 2, 2, 2)` — the razor-thin `nliRestGLFVCVK4` corner; the kit
  proves `gamma4fgcy ∈ [2.23e-6, 2.62e-6]` (width 3.8e-7), resolving the true
  value `2.412783872…e-6`;
* `(√8, 2, 2, 2, 2, 2)` — the exact-zero corner; the kit proves
  `gamma4fgcy ∈ [-1.6e-7, 1.4e-7]`, and `gamma4_at_sqrt8` (Gamma4Sharp)
  places `0` strictly inside (strong self-check).
-/
import Kepler.Text.Gamma4ValArctan

set_option maxHeartbeats 8000000

namespace Kepler.Text

/-! ## `dihY` values at `(2hplus, 2⁵)` -/

/-- The two `sqrt`-denominator normalisations used by the slot reductions. -/
theorem g4v_sqrt_den1 :
    Real.sqrt (59949975283774561462311 / 15258789062500000000) =
      Real.sqrt 59949975283774561462311 / 3906250000 := by
  have h : (59949975283774561462311 / 15258789062500000000 : ℝ) =
      59949975283774561462311 * (1 / 3906250000) ^ 2 := by norm_num
  rw [h, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 59949975283774561462311),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 3906250000)]
  ring

theorem g4v_sqrt_den23 :
    Real.sqrt (1365070455397359 / 610351562500) =
      Real.sqrt 1365070455397359 / 781250 := by
  have h : (1365070455397359 / 610351562500 : ℝ) =
      1365070455397359 * (1 / 781250) ^ 2 := by norm_num
  rw [h, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1365070455397359),
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 781250)]
  ring

/-- Slot 1: `dihY (2hplus) 2 2 2 2 2`. -/
theorem g4v_2hp_dih_eq1 :
    dihY (2 * hplus) 2 2 2 2 2 =
      Real.pi / 2 + Real.arctan ((-(267142230397359 / 39062500000000)) /
        Real.sqrt (59949975283774561462311 / 15258789062500000000)) := by
  have hsq := g4v_sqrt_den1
  have hbr : |(-(267142230397359 / 39062500000000) : ℝ)| <
      Real.sqrt (59949975283774561462311 / 15258789062500000000) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [hplus, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-- Slot 2: `dihY 2 (2hplus) 2 2 2 2`. -/
theorem g4v_2hp_dih_eq2 :
    dihY 2 (2 * hplus) 2 2 2 2 =
      Real.pi / 2 + Real.arctan ((-(43917129 / 1562500)) /
        Real.sqrt (1365070455397359 / 610351562500)) := by
  have hsq := g4v_sqrt_den23
  have hbr : |(-(43917129 / 1562500) : ℝ)| <
      Real.sqrt (1365070455397359 / 610351562500) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [hplus, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-- Slot 3. -/
theorem g4v_2hp_dih_eq3 :
    dihY 2 2 (2 * hplus) 2 2 2 =
      Real.pi / 2 + Real.arctan ((-(43917129 / 1562500)) /
        Real.sqrt (1365070455397359 / 610351562500)) := by
  have hsq := g4v_sqrt_den23
  have hbr : |(-(43917129 / 1562500) : ℝ)| <
      Real.sqrt (1365070455397359 / 610351562500) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [hplus, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-- Slot 4. -/
theorem g4v_2hp_dih_eq4 :
    dihY 2 2 2 (2 * hplus) 2 2 =
      Real.pi / 2 + Real.arctan ((6417129 / 781250) /
        Real.sqrt (1365070455397359 / 610351562500)) := by
  have hsq := g4v_sqrt_den23
  have hbr : |(6417129 / 781250 : ℝ)| <
      Real.sqrt (1365070455397359 / 610351562500) := by
    rw [abs_of_pos (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [hplus, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-- Slot 5. -/
theorem g4v_2hp_dih_eq5 :
    dihY 2 2 2 2 (2 * hplus) 2 =
      Real.pi / 2 + Real.arctan ((-(43917129 / 1562500)) /
        Real.sqrt (1365070455397359 / 610351562500)) := by
  have hsq := g4v_sqrt_den23
  have hbr : |(-(43917129 / 1562500) : ℝ)| <
      Real.sqrt (1365070455397359 / 610351562500) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [hplus, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-- Slot 6. -/
theorem g4v_2hp_dih_eq6 :
    dihY 2 2 2 2 2 (2 * hplus) =
      Real.pi / 2 + Real.arctan ((-(43917129 / 1562500)) /
        Real.sqrt (1365070455397359 / 610351562500)) := by
  have hsq := g4v_sqrt_den23
  have hbr : |(-(43917129 / 1562500) : ℝ)| <
      Real.sqrt (1365070455397359 / 610351562500) := by
    rw [abs_of_neg (by norm_num)]
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold dihY dihXf
  norm_num [hplus, deltaX, deltaX4]
  rw [← hsq]
  rw [atn2, if_pos hbr]

/-! ## `lmfun` at the corner arguments -/

theorem g4v_lmfun_hplus : lmfun hplus = 0 := by
  show (if hplus ≤ h0 then (h0 - hplus) / (h0 - 1) else 0) = 0
  rw [if_neg (by norm_num [hplus, h0])]

theorem g4v_lmfun_one : lmfun 1 = 1 := by
  norm_num [lmfun, h0]

/-! ## Exact `S` / `D` formulas at `(2hplus, 2⁵)` -/

/-- The four `solY` sum equals `2·d₁ + 8·d₂ + 2·d₄ − 4π` (the slot-2/3/5/6
value occurs eight times, slot 1 and slot 4 twice each). -/
theorem g4v_2hp_S_eq :
    solY (2 * hplus) 2 2 2 2 2 + solY (2 * hplus) 2 2 2 2 2 +
      solY 2 2 2 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 2 =
      (Real.pi / 2 + Real.arctan ((-(267142230397359 / 39062500000000)) /
        Real.sqrt (59949975283774561462311 / 15258789062500000000))) * 2 +
      (Real.pi / 2 + Real.arctan ((-(43917129 / 1562500)) /
        Real.sqrt (1365070455397359 / 610351562500))) * 8 +
      (Real.pi / 2 + Real.arctan ((6417129 / 781250) /
        Real.sqrt (1365070455397359 / 610351562500))) * 2 - 4 * Real.pi := by
  simp only [solY, g4v_2hp_dih_eq1, g4v_2hp_dih_eq2, g4v_2hp_dih_eq3,
    g4v_2hp_dih_eq4, g4v_2hp_dih_eq5, g4v_2hp_dih_eq6]
  ring

/-- The weighted `dihY` sum at `(2hplus, 2⁵)` is `4·d₂ + d₄` (the slot-1
weight is `lmfun hplus = 0`). -/
theorem g4v_2hp_D_eq :
    lmfun (2 * hplus / 2) * dihY (2 * hplus) 2 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 2 (2 * hplus) 2 2 2 +
      lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 2 2 (2 * hplus) 2 2 +
      lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 =
      (Real.pi / 2 + Real.arctan ((-(43917129 / 1562500)) /
        Real.sqrt (1365070455397359 / 610351562500))) * 4 +
      (Real.pi / 2 + Real.arctan ((6417129 / 781250) /
        Real.sqrt (1365070455397359 / 610351562500))) := by
  rw [show (2 * hplus / 2) = hplus by ring]
  simp only [g4v_lmfun_hplus, show (2:ℝ) / 2 = 1 by norm_num, g4v_lmfun_one,
    zero_mul, one_mul]
  rw [g4v_2hp_dih_eq2, g4v_2hp_dih_eq3, g4v_2hp_dih_eq4]
  ring

/-! ## `dihY` values at `(√8, 2⁵)` -/

theorem g4v_sqrt2048 : Real.sqrt 2048 = 32 * Real.sqrt 2 := by
  rw [show (2048:ℝ) = 32^2 * 2 by norm_num, Real.sqrt_mul (by positivity)]
  rw [show Real.sqrt ((32:ℝ)^2) = 32 from Real.sqrt_sq (by norm_num)]

theorem g4v_s8_dih_eq1 :
    dihY (Real.sqrt 8) 2 2 2 2 2 = Real.pi / 2 := by
  unfold dihY dihXf
  norm_num [deltaX, deltaX4]
  rw [atn2, if_pos (by norm_num)]
  norm_num

theorem g4v_s8_dih_eq2 :
    dihY 2 (Real.sqrt 8) 2 2 2 2 = Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  unfold dihY dihXf
  norm_num [deltaX, deltaX4]
  have hbr : |(-32:ℝ)| < Real.sqrt 2048 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [atn2, if_pos hbr]
  have hconv : (-32 : ℝ) / Real.sqrt 2048 = -(1 / Real.sqrt 2) := by
    rw [g4v_sqrt2048]
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  rw [hconv, Real.arctan_neg, g4v_atan_inv_sqrt2]
  ring

theorem g4v_s8_dih_eq3 :
    dihY 2 2 (Real.sqrt 8) 2 2 2 = Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  unfold dihY dihXf
  norm_num [deltaX, deltaX4]
  have hbr : |(-32:ℝ)| < Real.sqrt 2048 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [atn2, if_pos hbr]
  have hconv : (-32 : ℝ) / Real.sqrt 2048 = -(1 / Real.sqrt 2) := by
    rw [g4v_sqrt2048]
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  rw [hconv, Real.arctan_neg, g4v_atan_inv_sqrt2]
  ring

theorem g4v_s8_dih_eq4 :
    dihY 2 2 2 (Real.sqrt 8) 2 2 = Real.pi - Real.arccos (1 / 3) := by
  unfold dihY dihXf
  norm_num [deltaX, deltaX4]
  have hbr : |(16:ℝ)| < Real.sqrt 2048 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [atn2, if_pos hbr]
  have hconv : (16 : ℝ) / Real.sqrt 2048 = 1 / (2 * Real.sqrt 2) := by
    rw [g4v_sqrt2048]
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    norm_num
  rw [hconv, g4v_atan_inv_two_sqrt2]
  have harc : Real.arcsin (1/3) = Real.pi/2 - Real.arccos (1/3) := by
    have h := Real.arccos_eq_pi_div_two_sub_arcsin (1/3)
    linarith
  rw [harc]
  ring

theorem g4v_s8_dih_eq5 :
    dihY 2 2 2 2 (Real.sqrt 8) 2 = Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  unfold dihY dihXf
  norm_num [deltaX, deltaX4]
  have hbr : |(-32:ℝ)| < Real.sqrt 2048 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [atn2, if_pos hbr]
  have hconv : (-32 : ℝ) / Real.sqrt 2048 = -(1 / Real.sqrt 2) := by
    rw [g4v_sqrt2048]
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  rw [hconv, Real.arctan_neg, g4v_atan_inv_sqrt2]
  ring

theorem g4v_s8_dih_eq6 :
    dihY 2 2 2 2 2 (Real.sqrt 8) = Real.pi / 2 - Real.arccos (1 / 3) / 2 := by
  unfold dihY dihXf
  norm_num [deltaX, deltaX4]
  have hbr : |(-32:ℝ)| < Real.sqrt 2048 := by
    exact Real.lt_sqrt_of_sq_lt (by norm_num)
  rw [atn2, if_pos hbr]
  have hconv : (-32 : ℝ) / Real.sqrt 2048 = -(1 / Real.sqrt 2) := by
    rw [g4v_sqrt2048]
    have h2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  rw [hconv, Real.arctan_neg, g4v_atan_inv_sqrt2]
  ring

/-! ## Exact `S` / `D` formulas at `(√8, 2⁵)` -/

theorem g4v_s8_S_eq :
    solY (Real.sqrt 8) 2 2 2 2 2 + solY (Real.sqrt 8) 2 2 2 2 2 +
      solY 2 2 2 (Real.sqrt 8) 2 2 + solY 2 2 2 (Real.sqrt 8) 2 2 =
      3 * Real.pi - 6 * Real.arccos (1 / 3) := by
  simp only [solY, g4v_s8_dih_eq1, g4v_s8_dih_eq2, g4v_s8_dih_eq3,
    g4v_s8_dih_eq4, g4v_s8_dih_eq5, g4v_s8_dih_eq6]
  ring

theorem g4v_s8_D_eq :
    lmfun (Real.sqrt 8 / 2) * dihY (Real.sqrt 8) 2 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 2 (Real.sqrt 8) 2 2 2 +
      lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 2 2 (Real.sqrt 8) 2 2 +
      lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 +
      lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 =
      3 * Real.pi - 3 * Real.arccos (1 / 3) := by
  rw [lmfun_sqrt8_div_two]
  simp only [show (2:ℝ) / 2 = 1 by norm_num, g4v_lmfun_one, zero_mul, one_mul]
  rw [g4v_s8_dih_eq2, g4v_s8_dih_eq3, g4v_s8_dih_eq4]
  ring

/-! ## `S` / `D` / `volY` bounds at the two corners -/

theorem g4v_2hp_S_bounds :
    (2.119863293 : ℝ) ≤
      solY (2 * hplus) 2 2 2 2 2 + solY (2 * hplus) 2 2 2 2 2 +
        solY 2 2 2 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 2 ∧
      solY (2 * hplus) 2 2 2 2 2 + solY (2 * hplus) 2 2 2 2 2 +
        solY 2 2 2 (2 * hplus) 2 2 + solY 2 2 2 (2 * hplus) 2 2 ≤ 2.119863428 := by
  rw [g4v_2hp_S_eq]
  obtain ⟨ha11, ha12⟩ := g4v_atan_A1_bounds
  obtain ⟨ha21, ha22⟩ := g4v_atan_A2_bounds
  obtain ⟨ha31, ha32⟩ := g4v_atan_A3_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  constructor <;> linarith

theorem g4v_2hp_D_bounds :
    (5.88099662 : ℝ) ≤
      lmfun (2 * hplus / 2) * dihY (2 * hplus) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (2 * hplus) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (2 * hplus) 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 ∧
      lmfun (2 * hplus / 2) * dihY (2 * hplus) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (2 * hplus) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (2 * hplus) 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (2 * hplus) 2 2 2 2 ≤ 5.880996673 := by
  rw [g4v_2hp_D_eq]
  obtain ⟨ha21, ha22⟩ := g4v_atan_A2_bounds
  obtain ⟨ha31, ha32⟩ := g4v_atan_A3_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  constructor <;> linarith

theorem g4v_2hp_volY_eq :
    volY (2 * hplus) 2 2 2 2 2 =
      Real.sqrt (1365070455397359 / 9765625000000) / 12 := by
  unfold volY volXf
  norm_num [hplus, deltaX]

theorem g4v_2hp_volY_bounds :
    (0.985249591 : ℝ) ≤ volY (2 * hplus) 2 2 2 2 2 ∧
      volY (2 * hplus) 2 2 2 2 2 ≤ 0.9852496 := by
  rw [g4v_2hp_volY_eq]
  have hsq1 : (11.8229951 : ℝ) ^ 2 ≤ 1365070455397359 / 9765625000000 := by
    norm_num
  have hsq2 : (1365070455397359 / 9765625000000 : ℝ) ≤ (11.8229952) ^ 2 := by
    norm_num
  have h1 : (11.8229951 : ℝ) ≤ Real.sqrt (1365070455397359 / 9765625000000) :=
    Real.le_sqrt_of_sq_le hsq1
  have h2 : Real.sqrt (1365070455397359 / 9765625000000) ≤ 11.8229952 :=
    (Real.sqrt_le_left (by norm_num)).mpr hsq2
  constructor <;> linarith

theorem g4v_s8_S_bounds :
    (2.039021453 : ℝ) ≤
      solY (Real.sqrt 8) 2 2 2 2 2 + solY (Real.sqrt 8) 2 2 2 2 2 +
        solY 2 2 2 (Real.sqrt 8) 2 2 + solY 2 2 2 (Real.sqrt 8) 2 2 ∧
      solY (Real.sqrt 8) 2 2 2 2 2 + solY (Real.sqrt 8) 2 2 2 2 2 +
        solY 2 2 2 (Real.sqrt 8) 2 2 + solY 2 2 2 (Real.sqrt 8) 2 2 ≤ 2.039021461 := by
  rw [g4v_s8_S_eq]
  obtain ⟨ha1, ha2⟩ := g4v_arccos_third_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  constructor <;> linarith

theorem g4v_s8_D_bounds :
    (5.731899707 : ℝ) ≤
      lmfun (Real.sqrt 8 / 2) * dihY (Real.sqrt 8) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (Real.sqrt 8) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (Real.sqrt 8) 2 2 +
        lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 ∧
      lmfun (Real.sqrt 8 / 2) * dihY (Real.sqrt 8) 2 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 (Real.sqrt 8) 2 2 2 +
        lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 2 2 (Real.sqrt 8) 2 2 +
        lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 +
        lmfun (2 / 2) * dihY 2 (Real.sqrt 8) 2 2 2 2 ≤ 5.731899711 := by
  rw [g4v_s8_D_eq]
  obtain ⟨ha1, ha2⟩ := g4v_arccos_third_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  constructor <;> linarith

theorem g4v_s8_volY_eq :
    volY (Real.sqrt 8) 2 2 2 2 2 = Real.sqrt 128 / 12 := by
  unfold volY volXf
  norm_num [deltaX]

theorem g4v_sqrt128_eq : Real.sqrt 128 = 8 * Real.sqrt 2 := by
  rw [show (128:ℝ) = 8^2 * 2 by norm_num, Real.sqrt_mul (by positivity)]
  rw [show Real.sqrt ((8:ℝ)^2) = 8 from Real.sqrt_sq (by norm_num)]

theorem g4v_s8_volY_bounds :
    (0.94280904 : ℝ) ≤ volY (Real.sqrt 8) 2 2 2 2 2 ∧
      volY (Real.sqrt 8) 2 2 2 2 2 ≤ 0.942809047 := by
  rw [g4v_s8_volY_eq, g4v_sqrt128_eq]
  obtain ⟨h1, h2⟩ := g4v_sqrt2_bounds
  constructor <;> linarith

/-! ## Axiom audit -/

#print axioms g4v_sqrt_den1
#print axioms g4v_sqrt_den23
#print axioms g4v_2hp_dih_eq1
#print axioms g4v_2hp_dih_eq2
#print axioms g4v_2hp_dih_eq3
#print axioms g4v_2hp_dih_eq4
#print axioms g4v_2hp_dih_eq5
#print axioms g4v_2hp_dih_eq6
#print axioms g4v_lmfun_hplus
#print axioms g4v_lmfun_one
#print axioms g4v_2hp_S_eq
#print axioms g4v_2hp_D_eq
#print axioms g4v_sqrt2048
#print axioms g4v_s8_dih_eq1
#print axioms g4v_s8_dih_eq2
#print axioms g4v_s8_dih_eq3
#print axioms g4v_s8_dih_eq4
#print axioms g4v_s8_dih_eq5
#print axioms g4v_s8_dih_eq6
#print axioms g4v_s8_S_eq
#print axioms g4v_s8_D_eq
#print axioms g4v_2hp_S_bounds
#print axioms g4v_2hp_D_bounds
#print axioms g4v_2hp_volY_eq
#print axioms g4v_2hp_volY_bounds
#print axioms g4v_s8_S_bounds
#print axioms g4v_s8_D_bounds
#print axioms g4v_s8_volY_eq
#print axioms g4v_sqrt128_eq
#print axioms g4v_s8_volY_bounds

end Kepler.Text
