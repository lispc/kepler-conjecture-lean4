import Kepler.Text.TaylorSecond.Wt1C2
import Kepler.Text.TaylorSecond.Base200

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-- Exact lower corners of the selected `LRLRLRLRL` box. -/
noncomputable def selectedLo : Fin 3 → ℝ :=
  ![4927 / 2000, 2, 709528000001 / 320000000000]

/-- Exact upper corners of the selected `LRLRLRLRL` box. -/
noncomputable def selectedHi : Fin 3 → ℝ :=
  ![1585680000001 / 640000000000, 1289270400001 / 640000000000,
    714163200001 / 320000000000]

/-- The selected whole three-dimensional box; no one-variable slice is used. -/
def selectedBox : Set (Fin 3 → ℝ) := Box selectedLo selectedHi

/-- pp=3 value enclosure of the selected joint object. -/
def selectedValue : QInterval := ⟨43890 / 8000000, 49101 / 8000000⟩

/-- pp=3 first-partial enclosures of the selected joint object. -/
def selectedFirst : Fin 3 → QInterval :=
  ![⟨-50404 / 8000000, -42966 / 8000000⟩,
    ⟨196481 / 8000000, 201901 / 8000000⟩,
    ⟨125542 / 8000000, 131257 / 8000000⟩]

/-- Exact pp=3 `D00` enclosure. -/
def selectedD00 : QInterval := ⟨-1113417 / 8000000, -347581 / 8000000⟩

/-- Exact pp=3 `D10` enclosure. -/
def selectedD10 : QInterval := ⟨-120051 / 8000000, 443741 / 8000000⟩

/-- Exact pp=3 `D11 = w1F2` enclosure, decoded from base 200. -/
def selectedD11 : QInterval := IFloat200.interval IFloat200.selectedD11Lo IFloat200.selectedD11Hi

/-- Exact pp=3 `D20` enclosure. -/
def selectedD20 : QInterval := ⟨-74603 / 8000000, 783 / 12500⟩

/-- Exact pp=3 `D21` enclosure. -/
def selectedD21 : QInterval := ⟨-30817 / 800000, 68089 / 2000000⟩

/-- Exact pp=3 `D22` enclosure. -/
def selectedD22 : QInterval := ⟨-133971 / 1600000, -72401 / 8000000⟩

/-- All six pp=3 lower-triangular Hessian intervals; no target-only reduced object. -/
def selectedSecond : Fin 3 → Fin 3 → QInterval :=
  ![![selectedD00, selectedD10, selectedD20],
    ![selectedD10, selectedD11, selectedD21],
    ![selectedD20, selectedD21, selectedD22]]

/-- Remaining machine input for the selected leaf.  Constructing this record is
precisely the outstanding numerical certificate obligation, not a proved leaf result. -/
structure SelectedLeafEvidence (U : Set (Fin 3 → ℝ)) where
  c2data : Wt1C2Data U
  subset : ∀ x ∈ selectedBox, x ∈ U
  jet : WholeBoxJet w1F3 selectedBox
  value_eq : jet.value = selectedValue
  first_eq : jet.first = selectedFirst
  second_eq : jet.second = selectedSecond

/-- Gated consumer of the full selected-leaf certificate.  Until a
`SelectedLeafEvidence` record is constructed, the leaf remains `LEAF_NOT_READY`. -/
theorem w1F2_le_of_selectedLeafEvidence {U : Set (Fin 3 → ℝ)}
    (E : SelectedLeafEvidence U) (x : Fin 3 → ℝ) (hx : x ∈ selectedBox) :
    w1F2 (x 0) (x 1) (x 2) ≤ -101749 / 8000000 ∧ -101749 / 8000000 < (0 : ℝ) := by
  have h := E.jet.second_mem x hx 1 1 (le_refl 1)
  rw [E.second_eq] at h
  have h11 : selectedD11.mem (partial2 1 1 w1F3 x) := by
    simpa [selectedSecond] using h
  rw [partial2_w1F3_eq_w1F2_of_data E.c2data x (E.subset x hx)] at h11
  exact IFloat200.selectedD11_negative_of_mem h11

/-- The same gate exposes the exact two-sided `D11` enclosure, not merely a sign. -/
theorem w1F2_mem_of_selectedLeafEvidence {U : Set (Fin 3 → ℝ)}
    (E : SelectedLeafEvidence U) (x : Fin 3 → ℝ) (hx : x ∈ selectedBox) :
    selectedD11.mem (w1F2 (x 0) (x 1) (x 2)) := by
  have h := E.jet.second_mem x hx 1 1 (le_refl 1)
  rw [E.second_eq] at h
  have h11 : selectedD11.mem (partial2 1 1 w1F3 x) := by
    simpa [selectedSecond] using h
  rwa [partial2_w1F3_eq_w1F2_of_data E.c2data x (E.subset x hx)] at h11

#print axioms w1F2_le_of_selectedLeafEvidence
#print axioms w1F2_mem_of_selectedLeafEvidence

/-! ## DEF-FIX `wt1c2-opendomain` (2026-11-24): an inhabited `Wt1C2Data` witness

The frozen `selectedLo`/`selectedHi` sit exactly on the old six-bound
`Wt1C2Data.box` boundary (`selectedLo 0 = 4927/2000` = the x0 lower edge,
`selectedLo 1 = 2` = the x1 lower edge), so `IsOpen U` + the closed-box
condition on `U` + `selectedBox ⊆ U` were jointly contradictory and
`SelectedLeafEvidence` was uninhabitable for every `U`.

After the DEF-FIXed positivity-only `box` field, the explicit rational open
box `leafU` below — strictly containing `selectedBox` with narrow margins —
carries a fully constructed `Wt1C2Data leafU`.  All constants and gated
theorem statements above are untouched; this block is purely additive.

Margins (charter §3.4): the two touched faces open outward by `1/10⁶`
(x0 lower edge: `4927/2000 − 1/10⁶`) and `1/10⁹` (x1 lower edge: `2 − 1/10⁹`);
x2 and all upper edges stay inside the old numeric bounds; x0 upper
`62/25 = 2.48 < 2 * h0 = 2.52` keeps `cut`; and the positivity brackets
(e.g. `x1² + x0² − x2² ≥ 5.04`) stay strictly positive on the strip, which
is what the 12 condition proofs below discharge by explicit `nlinarith`
bounds (the frozen six-bound lemmas `w1a*_pos`/`w1t*_domain`/`w1g*_domain`
do NOT cover the strip, since `x 0` may dip `1/10⁶` below `2.4635`). -/

/-- Explicit rational open box `U ⊇ selectedBox` with narrow margins:
`x0 ∈ (4927/2000 − 1/10⁶, 62/25)`, `x1 ∈ (1999999999/10⁹, 21/10)`,
`x2 ∈ (221/100, 56/25)`. -/
def leafU : Set (Fin 3 → ℝ) :=
  Set.inter
    ((fun x : Fin 3 → ℝ => x 0) ⁻¹' Set.Ioo (4927 / 2000 - 1 / 1000000) (62 / 25))
    (Set.inter
      ((fun x : Fin 3 → ℝ => x 1) ⁻¹' Set.Ioo (1999999999 / 1000000000) (21 / 10))
      ((fun x : Fin 3 → ℝ => x 2) ⁻¹' Set.Ioo (221 / 100) (56 / 25)))

theorem leafU_mem_iff {x : Fin 3 → ℝ} :
    x ∈ leafU ↔
      4927 / 2000 - 1 / 1000000 < x 0 ∧ x 0 < 62 / 25 ∧
      1999999999 / 1000000000 < x 1 ∧ x 1 < 21 / 10 ∧
      221 / 100 < x 2 ∧ x 2 < 56 / 25 := by
  constructor
  · intro h
    obtain ⟨h01, h23⟩ := h
    obtain ⟨h0, h1⟩ := h01
    obtain ⟨h2, h3⟩ := h23
    obtain ⟨h2', h3'⟩ := h2
    obtain ⟨h4, h5⟩ := h3
    exact ⟨h0, h1, h2', h3', h4, h5⟩
  · intro h
    exact (Set.mem_inter_iff x _ _).mpr ⟨(Set.mem_preimage).mpr ⟨h.1, h.2.1⟩,
      (Set.mem_inter_iff x _ _).mpr ⟨(Set.mem_preimage).mpr ⟨h.2.2.1, h.2.2.2.1⟩,
        (Set.mem_preimage).mpr ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩⟩

/-- `leafU` is open (finite intersection of rational coordinate half-space
pairs). -/
theorem leafU_open : IsOpen leafU := by
  unfold leafU
  exact (isOpen_Ioo.preimage (continuous_apply (0 : Fin 3))).inter
    ((isOpen_Ioo.preimage (continuous_apply (1 : Fin 3))).inter
      (isOpen_Ioo.preimage (continuous_apply (2 : Fin 3))))

/-- All three coordinates are strictly positive on `leafU`. -/
theorem leafU_coord_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < x 0 ∧ (0 : ℝ) < x 1 ∧ (0 : ℝ) < x 2 := by
  rw [leafU_mem_iff] at hx
  obtain ⟨h0l, _, h1l, _, h2l, _⟩ := hx
  have e1 : (0 : ℝ) < 4927 / 2000 - 1 / 1000000 := by norm_num
  have e2 : (0 : ℝ) < 1999999999 / 1000000000 := by norm_num
  have e3 : (0 : ℝ) < 221 / 100 := by norm_num
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Coordinate square bounds on `leafU` (slack decimals; feed every condition
below). -/
theorem leafU_sq_bounds {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (6.068 : ℝ) ≤ x 0 * x 0 ∧ x 0 * x 0 ≤ 6.156 ∧
    (3.996 : ℝ) ≤ x 1 * x 1 ∧ x 1 * x 1 ≤ 4.415 ∧
    (4.879 : ℝ) ≤ x 2 * x 2 ∧ x 2 * x 2 ≤ 5.023 := by
  rw [leafU_mem_iff] at hx
  obtain ⟨h0l, h0u, h1l, h1u, h2l, h2u⟩ := hx
  have b0l : (2.4634 : ℝ) ≤ x 0 := by
    have e : (2.4634 : ℝ) ≤ 4927 / 2000 - 1 / 1000000 := by norm_num
    linarith
  have b0u : x 0 ≤ 2.481 := by
    have e : (62 : ℝ) / 25 ≤ 2.481 := by norm_num
    linarith
  have b1l : (1.999 : ℝ) ≤ x 1 := by
    have e : (1.999 : ℝ) ≤ 1999999999 / 1000000000 := by norm_num
    linarith
  have b1u : x 1 ≤ 2.101 := by
    have e : (21 : ℝ) / 10 ≤ 2.101 := by norm_num
    linarith
  have b2l : (2.209 : ℝ) ≤ x 2 := by
    have e : (2.209 : ℝ) ≤ 221 / 100 := by norm_num
    linarith
  have b2u : x 2 ≤ 2.241 := by
    have e : (56 : ℝ) / 25 ≤ 2.241 := by norm_num
    linarith
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith⟩

/-- The symmetric `Delta` is strictly positive on `leafU` (numerically
`Δ ≥ 2.83` on the strip), via the exact decomposition
`Δ = X·(4Y + 4Z − 2X − YZ) − 2·(Z − Y)²` with `X = x0²`, `Y = x1²`, `Z = x2²`.
This single lemma is the engine of all six `t_pos`/`g_pos` conditions. -/
theorem leafU_delta_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  have hXYl : (24.2 : ℝ) ≤ x 0 * x 0 * (x 1 * x 1) := by nlinarith
  have hXYu : x 0 * x 0 * (x 1 * x 1) ≤ 27.18 := by nlinarith
  have hXZl : (29.6 : ℝ) ≤ x 0 * x 0 * (x 2 * x 2) := by nlinarith
  have hXsql : (36.82 : ℝ) ≤ x 0 * x 0 * (x 0 * x 0) := by nlinarith
  have hXsqu : x 0 * x 0 * (x 0 * x 0) ≤ 37.9 := by nlinarith
  have hXYZu : x 0 * x 0 * (x 1 * x 1) * (x 2 * x 2) ≤ 136.6 := by
    have h0 : (0 : ℝ) ≤ x 0 * x 0 * (x 1 * x 1) := by nlinarith
    have h1 : (0 : ℝ) ≤ x 2 * x 2 := by nlinarith
    have h2 := mul_le_mul hXYu x6u h1 (by norm_num : (0 : ℝ) ≤ 27.18)
    have e : (27.18 : ℝ) * 5.023 ≤ 136.6 := by norm_num
    linarith
  have hZYl : (0 : ℝ) ≤ (x 2 * x 2) - (x 1 * x 1) := by linarith
  have hZYu : (x 2 * x 2) - (x 1 * x 1) ≤ 1.027 := by linarith
  have hsq : ((x 2 * x 2) - (x 1 * x 1)) ^ 2 ≤ 1.061 := by nlinarith
  have hring : w1Dlt (x 0) (x 1) (x 2)
      = 4 * (x 0 * x 0 * (x 1 * x 1)) + 4 * (x 0 * x 0 * (x 2 * x 2))
        - 2 * (x 0 * x 0 * (x 0 * x 0))
        - x 0 * x 0 * (x 1 * x 1) * (x 2 * x 2)
        - 2 * ((x 2 * x 2) - (x 1 * x 1)) ^ 2 := by
    unfold w1Dlt
    ring
  linarith [hring, hsq, hXYl, hXZl, hXsqu, hXYZu]

/-! ### The 12 `Wt1C2Data` conditions on `leafU`

`area_ne`/`d4_ne` (3 + 3): strict positivity by explicit rational bounds.
`t_pos`/`g_pos` (3 + 3): `t = Δ/(4a²) > 0` and `g = 4y²Δ/d4² > 0` follow
from `leafU_delta_pos` plus the positivity just established. -/

/-- `w1aA > 0` on `leafU` (condition `area_ne.1`). -/
theorem leafU_aA_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1aA (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  obtain ⟨hy4, hy5, hy6⟩ := leafU_coord_pos hx
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hthird : (0 : ℝ) ≤ Real.sqrt 2 * ((x 1 * x 1) + (x 0 * x 0) - (x 2 * x 2)) / 2 := by
    have hd : (0 : ℝ) ≤ (x 1 * x 1) + (x 0 * x 0) - (x 2 * x 2) := by linarith
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hd) (by norm_num)
  have hT1 : (0 : ℝ) < Real.sqrt 2 * x 1 * x 0 :=
    mul_pos (mul_pos hs2pos hy5) hy4
  have h2t : (0 : ℝ) ≤ x 1 * (x 0 * x 0) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hy5) (mul_self_nonneg (x 0))) (by norm_num)
  have h4t : (0 : ℝ) ≤ x 0 * (x 1 * x 1) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hy4) (mul_self_nonneg (x 1))) (by norm_num)
  unfold w1aA
  linarith

/-- `w1aB > 0` on `leafU` (condition `area_ne.2`). -/
theorem leafU_aB_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1aB (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  obtain ⟨hy4, hy5, hy6⟩ := leafU_coord_pos hx
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hthird : (0 : ℝ) ≤ Real.sqrt 2 * ((x 2 * x 2) + (x 1 * x 1) - (x 0 * x 0)) / 2 := by
    have hd : (0 : ℝ) ≤ (x 2 * x 2) + (x 1 * x 1) - (x 0 * x 0) := by linarith
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hd) (by norm_num)
  have hT1 : (0 : ℝ) < Real.sqrt 2 * x 2 * x 1 :=
    mul_pos (mul_pos hs2pos hy6) hy5
  have h2t : (0 : ℝ) ≤ x 2 * (x 1 * x 1) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hy6) (mul_self_nonneg (x 1))) (by norm_num)
  have h4t : (0 : ℝ) ≤ x 1 * (x 2 * x 2) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hy5) (mul_self_nonneg (x 2))) (by norm_num)
  unfold w1aB
  linarith

/-- `w1aC > 0` on `leafU` (condition `area_ne.3`). -/
theorem leafU_aC_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1aC (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  obtain ⟨hy4, hy5, hy6⟩ := leafU_coord_pos hx
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hthird : (0 : ℝ) ≤ Real.sqrt 2 * ((x 0 * x 0) + (x 2 * x 2) - (x 1 * x 1)) / 2 := by
    have hd : (0 : ℝ) ≤ (x 0 * x 0) + (x 2 * x 2) - (x 1 * x 1) := by linarith
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hd) (by norm_num)
  have hT1 : (0 : ℝ) < Real.sqrt 2 * x 0 * x 2 :=
    mul_pos (mul_pos hs2pos hy4) hy6
  have h2t : (0 : ℝ) ≤ x 0 * (x 2 * x 2) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hy4) (mul_self_nonneg (x 2))) (by norm_num)
  have h4t : (0 : ℝ) ≤ x 2 * (x 0 * x 0) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hy6) (mul_self_nonneg (x 0))) (by norm_num)
  unfold w1aC
  linarith

/-- `w1d4A > 0` on `leafU` (condition `d4_ne.1`: `= x1²·(x0²+x2²−x1²)`). -/
theorem leafU_d4A_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1d4A (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  have hs : (0 : ℝ) < x 1 * x 1 := by linarith
  have hb : (0 : ℝ) < (x 0 * x 0) + (x 2 * x 2) - (x 1 * x 1) := by linarith
  unfold w1d4A
  exact mul_pos hs hb

/-- `w1d4B > 0` on `leafU` (condition `d4_ne.2`: `= x2²·(x1²+x0²−x2²)`). -/
theorem leafU_d4B_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1d4B (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  have hs : (0 : ℝ) < x 2 * x 2 := by linarith
  have hb : (0 : ℝ) < (x 1 * x 1) + (x 0 * x 0) - (x 2 * x 2) := by linarith
  unfold w1d4B
  exact mul_pos hs hb

/-- `w1d4C > 0` on `leafU` (condition `d4_ne.3`: `= x0²·(x2²+x1²−x0²)`). -/
theorem leafU_d4C_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1d4C (x 0) (x 1) (x 2) := by
  obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
  have hs : (0 : ℝ) < x 0 * x 0 := by linarith
  have hb : (0 : ℝ) < (x 2 * x 2) + (x 1 * x 1) - (x 0 * x 0) := by linarith
  unfold w1d4C
  exact mul_pos hs hb

/-- `w1tA > 0` on `leafU` (condition `t_pos.1`: `t = Δ/(4a_A²)`). -/
theorem leafU_tA_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1tA (x 0) (x 1) (x 2) := by
  have hd : (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := leafU_delta_pos hx
  have ha : (0 : ℝ) < w1aA (x 0) (x 1) (x 2) := leafU_aA_pos hx
  have hden : (0 : ℝ) < 4 * w1aA (x 0) (x 1) (x 2) ^ 2 :=
    mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_ne_zero (ne_of_gt ha))
  unfold w1tA w1tOf
  exact div_pos hd hden

/-- `w1tB > 0` on `leafU` (condition `t_pos.2`). -/
theorem leafU_tB_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1tB (x 0) (x 1) (x 2) := by
  have hd : (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := leafU_delta_pos hx
  have ha : (0 : ℝ) < w1aB (x 0) (x 1) (x 2) := leafU_aB_pos hx
  have hden : (0 : ℝ) < 4 * w1aB (x 0) (x 1) (x 2) ^ 2 :=
    mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_ne_zero (ne_of_gt ha))
  unfold w1tB w1tOf
  exact div_pos hd hden

/-- `w1tC > 0` on `leafU` (condition `t_pos.3`). -/
theorem leafU_tC_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1tC (x 0) (x 1) (x 2) := by
  have hd : (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := leafU_delta_pos hx
  have ha : (0 : ℝ) < w1aC (x 0) (x 1) (x 2) := leafU_aC_pos hx
  have hden : (0 : ℝ) < 4 * w1aC (x 0) (x 1) (x 2) ^ 2 :=
    mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_of_ne_zero (ne_of_gt ha))
  unfold w1tC w1tOf
  exact div_pos hd hden

/-- `w1gA > 0` on `leafU` (condition `g_pos.1`: `g = 4x1²·Δ/d4_A²`). -/
theorem leafU_gA_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1gA (x 0) (x 1) (x 2) := by
  have hd : (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := leafU_delta_pos hx
  have hY : (0 : ℝ) < x 1 * x 1 := by
    obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
    linarith
  have hd4 : (0 : ℝ) < w1d4A (x 0) (x 1) (x 2) := leafU_d4A_pos hx
  unfold w1gA w1gOf
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hY) hd)
    (sq_pos_of_ne_zero (ne_of_gt hd4))

/-- `w1gB > 0` on `leafU` (condition `g_pos.2`). -/
theorem leafU_gB_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1gB (x 0) (x 1) (x 2) := by
  have hd : (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := leafU_delta_pos hx
  have hZ : (0 : ℝ) < x 2 * x 2 := by
    obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
    linarith
  have hd4 : (0 : ℝ) < w1d4B (x 0) (x 1) (x 2) := leafU_d4B_pos hx
  unfold w1gB w1gOf
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hZ) hd)
    (sq_pos_of_ne_zero (ne_of_gt hd4))

/-- `w1gC > 0` on `leafU` (condition `g_pos.3`). -/
theorem leafU_gC_pos {x : Fin 3 → ℝ} (hx : x ∈ leafU) :
    (0 : ℝ) < w1gC (x 0) (x 1) (x 2) := by
  have hd : (0 : ℝ) < w1Dlt (x 0) (x 1) (x 2) := leafU_delta_pos hx
  have hX : (0 : ℝ) < x 0 * x 0 := by
    obtain ⟨x4l, x4u, x5l, x5u, x6l, x6u⟩ := leafU_sq_bounds hx
    linarith
  have hd4 : (0 : ℝ) < w1d4C (x 0) (x 1) (x 2) := leafU_d4C_pos hx
  unfold w1gC w1gOf
  exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hX) hd)
    (sq_pos_of_ne_zero (ne_of_gt hd4))

/-- **The inhabited `Wt1C2Data leafU` record** — the constructive refutation
of the frozen uninhabitability (charter §3.2/§4: this is the fix lane's
delivery endpoint; `jet`/payload remain the other lane's task). -/
theorem leafU_c2data : Wt1C2Data leafU where
  isOpen := leafU_open
  box := by
    intro x hx
    rw [leafU_mem_iff] at hx
    obtain ⟨h0l, _, h1l, _, h2l, _⟩ := hx
    have e1 : (0 : ℝ) < 4927 / 2000 - 1 / 1000000 := by norm_num
    have e2 : (0 : ℝ) < 1999999999 / 1000000000 := by norm_num
    have e3 : (0 : ℝ) ≤ 221 / 100 := by norm_num
    exact ⟨by linarith, by linarith, by linarith⟩
  cut := by
    intro x hx
    rw [leafU_mem_iff] at hx
    obtain ⟨_, h0u, _, _, _, _⟩ := hx
    have e : (62 : ℝ) / 25 ≤ 2 * h0 := by norm_num [h0]
    linarith
  area_ne := by
    intro x hx
    exact ⟨ne_of_gt (leafU_aA_pos hx), ne_of_gt (leafU_aB_pos hx),
      ne_of_gt (leafU_aC_pos hx)⟩
  d4_ne := by
    intro x hx
    exact ⟨ne_of_gt (leafU_d4A_pos hx), ne_of_gt (leafU_d4B_pos hx),
      ne_of_gt (leafU_d4C_pos hx)⟩
  t_pos := by
    intro x hx
    exact ⟨leafU_tA_pos hx, leafU_tB_pos hx, leafU_tC_pos hx⟩
  g_pos := by
    intro x hx
    exact ⟨leafU_gA_pos hx, leafU_gB_pos hx, leafU_gC_pos hx⟩

/-- The frozen closed box is contained in `leafU` (the second half of the
constructive refutation). -/
theorem selectedBox_subset_leafU : ∀ x ∈ selectedBox, x ∈ leafU := by
  intro x hx
  have hb : ∀ i : Fin 3, x i ∈ Set.Icc (selectedLo i) (selectedHi i) := hx
  have c0 : x 0 ∈ Set.Icc (4927 / 2000 : ℝ) (1585680000001 / 640000000000) := hb 0
  have c1 : x 1 ∈ Set.Icc (2 : ℝ) (1289270400001 / 640000000000) := hb 1
  have c2 : x 2 ∈ Set.Icc (709528000001 / 320000000000 : ℝ)
      (714163200001 / 320000000000) := hb 2
  rw [leafU_mem_iff]
  rw [Set.mem_Icc] at c0 c1 c2
  obtain ⟨c0l, c0u⟩ := c0
  obtain ⟨c1l, c1u⟩ := c1
  obtain ⟨c2l, c2u⟩ := c2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : 4927 / 2000 - 1 / 1000000 < (4927 : ℝ) / 2000 := by norm_num
    linarith
  · have e : (1585680000001 : ℝ) / 640000000000 < 62 / 25 := by norm_num
    linarith
  · have e : (1999999999 : ℝ) / 1000000000 < 2 := by norm_num
    linarith
  · have e : (1289270400001 : ℝ) / 640000000000 < 21 / 10 := by norm_num
    linarith
  · have e : (221 : ℝ) / 100 < 709528000001 / 320000000000 := by norm_num
    linarith
  · have e : (714163200001 : ℝ) / 320000000000 < 56 / 25 := by norm_num
    linarith

/-- Non-vacuity: `leafU` contains the selected lower corner itself, so the
constructed `Wt1C2Data` lives on a genuinely nonempty open set. -/
theorem leafU_nonempty : ∃ y : Fin 3 → ℝ, y ∈ leafU := by
  have b0 : selectedLo 0 ≤ selectedHi 0 := by
    have e0 : selectedLo 0 = (4927 : ℝ) / 2000 := rfl
    have e1 : selectedHi 0 = (1585680000001 : ℝ) / 640000000000 := rfl
    rw [e0, e1]
    norm_num
  have b1 : selectedLo 1 ≤ selectedHi 1 := by
    have e0 : selectedLo 1 = (2 : ℝ) := rfl
    have e1 : selectedHi 1 = (1289270400001 : ℝ) / 640000000000 := rfl
    rw [e0, e1]
    norm_num
  have b2 : selectedLo 2 ≤ selectedHi 2 := by
    have e0 : selectedLo 2 = (709528000001 : ℝ) / 320000000000 := rfl
    have e1 : selectedHi 2 = (714163200001 : ℝ) / 320000000000 := rfl
    rw [e0, e1]
    norm_num
  have hb : ∀ i : Fin 3, selectedLo i ∈ Set.Icc (selectedLo i) (selectedHi i) := by
    intro i
    fin_cases i
    · exact ⟨le_refl _, b0⟩
    · exact ⟨le_refl _, b1⟩
    · exact ⟨le_refl _, b2⟩
  exact ⟨selectedLo, selectedBox_subset_leafU selectedLo hb⟩

#print axioms leafU_open
#print axioms leafU_delta_pos
#print axioms leafU_c2data
#print axioms selectedBox_subset_leafU
#print axioms leafU_nonempty

end Kepler.Text.TaylorSecond
