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

end Kepler.Text.TaylorSecond
