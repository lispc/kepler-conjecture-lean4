/-
Kepler.NliKit.BoxTreeWt2AS1 — leaf witnesses, shard 1 of the
wt2A tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeWt2ARows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeWt2A

open Kepler.NliKit.BoxTree

theorem vD32_0 : ((rowsWt2A (32 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF32_0 : ((rowsWt2A (32 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD32_0, vB40_2708646895026]; norm_num
theorem vD32_1 : ((rowsWt2A (32 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF32_1 : ((rowsWt2A (32 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD32_1, vB40_2739708098510]; norm_num
theorem vD32_2 : ((rowsWt2A (32 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF32_2 : ((rowsWt2A (32 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD32_2, vB40_2708646895026]; norm_num
theorem vD32_3 : ((rowsWt2A (32 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF32_3 : ((rowsWt2A (32 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD32_3, vB40_2770769301995]; norm_num
theorem vD32_4 : ((rowsWt2A (32 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF32_4 : ((rowsWt2A (32 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD32_4, vB40_2262794929963]; norm_num
theorem vD32_5 : ((rowsWt2A (32 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF32_5 : ((rowsWt2A (32 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD32_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp32a2h_1 : ((rowsWt2A (32 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF32_5]; norm_num
theorem cmp32a1h_2 : ((rowsWt2A (32 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF32_3]; norm_num
theorem cmp32a0h_3 : ((rowsWt2A (32 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF32_1]; norm_num
theorem leaf_32_cell33_core : ∀ x ∈ rowBox (rowsWt2A (32 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (19821/8000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell10_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp32a2h_1]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp32a1h_2]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp32a1h_2]) (by linarith) (by linarith [cmp32a2h_1]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell09_core (by linarith) (by linarith [cmp32a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp32a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp32a2h_1]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell14_core (by linarith) (by linarith [cmp32a0h_3]) (by linarith) (by linarith [cmp32a1h_2]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp32a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp32a1h_2]) (by linarith) (by linarith [cmp32a2h_1]) hd

theorem vD33_0 : ((rowsWt2A (33 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF33_0 : ((rowsWt2A (33 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD33_0, vB40_2708646895026]; norm_num
theorem vD33_1 : ((rowsWt2A (33 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF33_1 : ((rowsWt2A (33 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD33_1, vB40_2724177496768]; norm_num
theorem vD33_2 : ((rowsWt2A (33 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF33_2 : ((rowsWt2A (33 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD33_2, vB40_2770769301995]; norm_num
theorem vD33_3 : ((rowsWt2A (33 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF33_3 : ((rowsWt2A (33 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD33_3, vB40_2940328904376]; norm_num
theorem vD33_4 : ((rowsWt2A (33 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF33_4 : ((rowsWt2A (33 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD33_4, vB40_2262794929963]; norm_num
theorem vD33_5 : ((rowsWt2A (33 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF33_5 : ((rowsWt2A (33 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD33_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp33a0h_1 : ((rowsWt2A (33 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF33_1]; norm_num
theorem cmp33a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (33 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF33_2]; norm_num
theorem cmp33a0h_3 : ((rowsWt2A (33 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF33_1]; norm_num
theorem cmp33a2h_4 : ((rowsWt2A (33 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF33_5]; norm_num
theorem cmp33a1h_5 : ((rowsWt2A (33 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF33_3]; norm_num
theorem leaf_33_cell38_core : ∀ x ∈ rowBox (rowsWt2A (33 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 1 ≤ (63/25:ℝ)
  ·
    by_cases n1 : x 2 ≤ (1029/500:ℝ)
    ·
      exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp33a0h_1]) (by linarith [cmp33a1l_2]) (by linarith) (by linarith) (by linarith) hd
    ·
      exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp33a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp33a2h_4]) hd
  ·
    by_cases n1 : x 2 ≤ (1029/500:ℝ)
    ·
      exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp33a0h_1]) (by linarith) (by linarith [cmp33a1h_5]) (by linarith) (by linarith) hd
    ·
      exact Kepler.NliBanks25.cell38_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp33a0h_1]) (by linarith) (by linarith [cmp33a1h_5]) (by linarith) (by linarith [cmp33a2h_4]) hd

theorem vD34_0 : ((rowsWt2A (34 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF34_0 : ((rowsWt2A (34 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD34_0, vB40_2724177496768]; norm_num
theorem vD34_1 : ((rowsWt2A (34 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF34_1 : ((rowsWt2A (34 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD34_1, vB40_2739708098510]; norm_num
theorem vD34_2 : ((rowsWt2A (34 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF34_2 : ((rowsWt2A (34 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD34_2, vB40_2770769301995]; norm_num
theorem vD34_3 : ((rowsWt2A (34 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF34_3 : ((rowsWt2A (34 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD34_3, vB40_2940328904376]; norm_num
theorem vD34_4 : ((rowsWt2A (34 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF34_4 : ((rowsWt2A (34 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD34_4, vB40_2262794929963]; norm_num
theorem vD34_5 : ((rowsWt2A (34 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF34_5 : ((rowsWt2A (34 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD34_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp34a1l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (34 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF34_2]; norm_num
theorem cmp34a2h_2 : ((rowsWt2A (34 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF34_5]; norm_num
theorem cmp34a1h_3 : ((rowsWt2A (34 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF34_3]; norm_num
theorem cmp34a0h_4 : ((rowsWt2A (34 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF34_1]; norm_num
theorem leaf_34_cell39_core : ∀ x ∈ rowBox (rowsWt2A (34 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (19821/8000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp34a1l_1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp34a2h_2]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp34a1h_3]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell38_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp34a1h_3]) (by linarith) (by linarith [cmp34a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell14_core (by linarith) (by linarith [cmp34a0h_4]) (by linarith [cmp34a1l_1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp34a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp34a2h_2]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell07_core (by linarith) (by linarith [cmp34a0h_4]) (by linarith) (by linarith [cmp34a1h_3]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell39_core (by linarith) (by linarith [cmp34a0h_4]) (by linarith) (by linarith [cmp34a1h_3]) (by linarith) (by linarith [cmp34a2h_2]) hd

theorem vD35_0 : ((rowsWt2A (35 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF35_0 : ((rowsWt2A (35 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD35_0, vB40_2708646895026]; norm_num
theorem vD35_1 : ((rowsWt2A (35 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF35_1 : ((rowsWt2A (35 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD35_1, vB40_2724177496768]; norm_num
theorem vD35_2 : ((rowsWt2A (35 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF35_2 : ((rowsWt2A (35 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD35_2, vB40_2940328904376]; norm_num
theorem vD35_3 : ((rowsWt2A (35 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF35_3 : ((rowsWt2A (35 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD35_3, vB40_3109888511976]; norm_num
theorem vD35_4 : ((rowsWt2A (35 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF35_4 : ((rowsWt2A (35 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD35_4, vB40_2262794929963]; norm_num
theorem vD35_5 : ((rowsWt2A (35 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF35_5 : ((rowsWt2A (35 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD35_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp35a0h_1 : ((rowsWt2A (35 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF35_1]; norm_num
theorem cmp35a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (35 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF35_2]; norm_num
theorem cmp35a2h_3 : ((rowsWt2A (35 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF35_5]; norm_num
theorem leaf_35_cell45_core : ∀ x ∈ rowBox (rowsWt2A (35 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 1 ≤ (66855339/25000000:ℝ)
  ·
    by_cases n1 : x 2 ≤ (1029/500:ℝ)
    ·
      exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp35a0h_1]) (by linarith [cmp35a1l_2]) (by linarith) (by linarith) (by linarith) hd
    ·
      exact Kepler.NliBanks25.cell38_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp35a0h_1]) (by linarith [cmp35a1l_2]) (by linarith) (by linarith) (by linarith [cmp35a2h_3]) hd
  ·
    by_cases n1 : x 2 ≤ (1029/500:ℝ)
    ·
      exact Kepler.NliBanks24.cell25_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp35a0h_1]) (by linarith) (by linarith) (by linarith) (by linarith) hd
    ·
      exact Kepler.NliBanks25.cell45_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp35a0h_1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp35a2h_3]) hd

theorem vD36_0 : ((rowsWt2A (36 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF36_0 : ((rowsWt2A (36 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD36_0, vB40_2724177496768]; norm_num
theorem vD36_1 : ((rowsWt2A (36 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF36_1 : ((rowsWt2A (36 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD36_1, vB40_2739708098510]; norm_num
theorem vD36_2 : ((rowsWt2A (36 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF36_2 : ((rowsWt2A (36 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD36_2, vB40_2940328904376]; norm_num
theorem vD36_3 : ((rowsWt2A (36 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF36_3 : ((rowsWt2A (36 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD36_3, vB40_3109888511976]; norm_num
theorem vD36_4 : ((rowsWt2A (36 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF36_4 : ((rowsWt2A (36 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD36_4, vB40_2262794929963]; norm_num
theorem vD36_5 : ((rowsWt2A (36 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF36_5 : ((rowsWt2A (36 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD36_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp36a1l_1 : (63/25:ℝ) ≤ ((rowsWt2A (36 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF36_2]; norm_num
theorem cmp36a2h_2 : ((rowsWt2A (36 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF36_5]; norm_num
theorem cmp36a0h_3 : ((rowsWt2A (36 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF36_1]; norm_num
theorem leaf_36_cell46_core : ∀ x ∈ rowBox (rowsWt2A (36 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (19821/8000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp36a1l_1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell38_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp36a1l_1]) (by linarith) (by linarith) (by linarith [cmp36a2h_2]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell25_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell45_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp36a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell07_core (by linarith) (by linarith [cmp36a0h_3]) (by linarith [cmp36a1l_1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell39_core (by linarith) (by linarith [cmp36a0h_3]) (by linarith [cmp36a1l_1]) (by linarith) (by linarith) (by linarith [cmp36a2h_2]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell26_core (by linarith) (by linarith [cmp36a0h_3]) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell46_core (by linarith) (by linarith [cmp36a0h_3]) (by linarith) (by linarith) (by linarith) (by linarith [cmp36a2h_2]) hd

theorem vD37_0 : ((rowsWt2A (37 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF37_0 : ((rowsWt2A (37 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD37_0, vB40_2739708098510]; norm_num
theorem vD37_1 : ((rowsWt2A (37 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF37_1 : ((rowsWt2A (37 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD37_1, vB40_2770769301995]; norm_num
theorem vD37_2 : ((rowsWt2A (37 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF37_2 : ((rowsWt2A (37 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD37_2, vB40_2708646895026]; norm_num
theorem vD37_3 : ((rowsWt2A (37 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF37_3 : ((rowsWt2A (37 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD37_3, vB40_2770769301995]; norm_num
theorem vD37_4 : ((rowsWt2A (37 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF37_4 : ((rowsWt2A (37 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD37_4, vB40_2262794929963]; norm_num
theorem vD37_5 : ((rowsWt2A (37 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF37_5 : ((rowsWt2A (37 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD37_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp37a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (37 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF37_0]; norm_num
theorem cmp37a2h_2 : ((rowsWt2A (37 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF37_5]; norm_num
theorem cmp37a1h_3 : ((rowsWt2A (37 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF37_3]; norm_num
theorem cmp37a0h_4 : ((rowsWt2A (37 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF37_1]; norm_num
theorem leaf_37_cell32_core : ∀ x ∈ rowBox (rowsWt2A (37 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (9967/4000:ℝ)
  ·
    by_cases n1 : x 0 ≤ (20047/8000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell09_core (by linarith [cmp37a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp37a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell14_core (by linarith [cmp37a0l_1]) (by linarith) (by linarith) (by linarith [cmp37a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp37a1h_3]) (by linarith) (by linarith [cmp37a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp37a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell12_core (by linarith) (by linarith) (by linarith) (by linarith [cmp37a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp37a1h_3]) (by linarith) (by linarith [cmp37a2h_2]) hd
  ·
    by_cases n1 : x 0 ≤ (20047/8000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell08_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp37a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell13_core (by linarith) (by linarith) (by linarith) (by linarith [cmp37a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp37a1h_3]) (by linarith) (by linarith [cmp37a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith [cmp37a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp37a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp37a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell12_core (by linarith) (by linarith [cmp37a0h_4]) (by linarith) (by linarith [cmp37a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp37a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp37a1h_3]) (by linarith) (by linarith [cmp37a2h_2]) hd

theorem vD38_0 : ((rowsWt2A (38 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF38_0 : ((rowsWt2A (38 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD38_0, vB40_2739708098510]; norm_num
theorem vD38_1 : ((rowsWt2A (38 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF38_1 : ((rowsWt2A (38 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD38_1, vB40_2755238700253]; norm_num
theorem vD38_2 : ((rowsWt2A (38 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF38_2 : ((rowsWt2A (38 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD38_2, vB40_2770769301995]; norm_num
theorem vD38_3 : ((rowsWt2A (38 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF38_3 : ((rowsWt2A (38 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD38_3, vB40_2940328904376]; norm_num
theorem vD38_4 : ((rowsWt2A (38 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF38_4 : ((rowsWt2A (38 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD38_4, vB40_2262794929963]; norm_num
theorem vD38_5 : ((rowsWt2A (38 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF38_5 : ((rowsWt2A (38 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD38_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp38a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (38 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF38_0]; norm_num
theorem cmp38a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (38 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF38_2]; norm_num
theorem cmp38a2h_3 : ((rowsWt2A (38 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF38_5]; norm_num
theorem cmp38a1h_4 : ((rowsWt2A (38 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF38_3]; norm_num
theorem cmp38a0h_5 : ((rowsWt2A (38 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (20047/8000:ℝ) := by rw [vF38_1]; norm_num
theorem cmp38a0h_6 : ((rowsWt2A (38 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF38_1]; norm_num
theorem leaf_38_cell40_core : ∀ x ∈ rowBox (rowsWt2A (38 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (9967/4000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell14_core (by linarith [cmp38a0l_1]) (by linarith) (by linarith [cmp38a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp38a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell07_core (by linarith [cmp38a0l_1]) (by linarith) (by linarith) (by linarith [cmp38a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell39_core (by linarith [cmp38a0l_1]) (by linarith) (by linarith) (by linarith [cmp38a1h_4]) (by linarith) (by linarith [cmp38a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell13_core (by linarith) (by linarith [cmp38a0h_5]) (by linarith [cmp38a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp38a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp38a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell06_core (by linarith) (by linarith [cmp38a0h_5]) (by linarith) (by linarith [cmp38a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell40_core (by linarith) (by linarith [cmp38a0h_5]) (by linarith) (by linarith [cmp38a1h_4]) (by linarith) (by linarith [cmp38a2h_3]) hd

theorem vD39_0 : ((rowsWt2A (39 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF39_0 : ((rowsWt2A (39 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD39_0, vB40_2755238700253]; norm_num
theorem vD39_1 : ((rowsWt2A (39 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF39_1 : ((rowsWt2A (39 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD39_1, vB40_2770769301995]; norm_num
theorem vD39_2 : ((rowsWt2A (39 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF39_2 : ((rowsWt2A (39 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD39_2, vB40_2770769301995]; norm_num
theorem vD39_3 : ((rowsWt2A (39 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF39_3 : ((rowsWt2A (39 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD39_3, vB40_2940328904376]; norm_num
theorem vD39_4 : ((rowsWt2A (39 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF39_4 : ((rowsWt2A (39 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD39_4, vB40_2262794929963]; norm_num
theorem vD39_5 : ((rowsWt2A (39 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF39_5 : ((rowsWt2A (39 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD39_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp39a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (39 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF39_0]; norm_num
theorem cmp39a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (39 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF39_2]; norm_num
theorem cmp39a2h_3 : ((rowsWt2A (39 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF39_5]; norm_num
theorem cmp39a1h_4 : ((rowsWt2A (39 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF39_3]; norm_num
theorem cmp39a0h_5 : ((rowsWt2A (39 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF39_1]; norm_num
theorem leaf_39_cell41_core : ∀ x ∈ rowBox (rowsWt2A (39 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (20047/8000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell13_core (by linarith [cmp39a0l_1]) (by linarith) (by linarith [cmp39a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell32_core (by linarith [cmp39a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp39a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell06_core (by linarith [cmp39a0l_1]) (by linarith) (by linarith) (by linarith [cmp39a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell40_core (by linarith [cmp39a0l_1]) (by linarith) (by linarith) (by linarith [cmp39a1h_4]) (by linarith) (by linarith [cmp39a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell12_core (by linarith) (by linarith [cmp39a0h_5]) (by linarith [cmp39a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp39a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp39a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell04_core (by linarith) (by linarith [cmp39a0h_5]) (by linarith) (by linarith [cmp39a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell41_core (by linarith) (by linarith [cmp39a0h_5]) (by linarith) (by linarith [cmp39a1h_4]) (by linarith) (by linarith [cmp39a2h_3]) hd

theorem vD40_0 : ((rowsWt2A (40 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF40_0 : ((rowsWt2A (40 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD40_0, vB40_2739708098510]; norm_num
theorem vD40_1 : ((rowsWt2A (40 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF40_1 : ((rowsWt2A (40 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD40_1, vB40_2755238700253]; norm_num
theorem vD40_2 : ((rowsWt2A (40 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF40_2 : ((rowsWt2A (40 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD40_2, vB40_2940328904376]; norm_num
theorem vD40_3 : ((rowsWt2A (40 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF40_3 : ((rowsWt2A (40 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD40_3, vB40_3109888511976]; norm_num
theorem vD40_4 : ((rowsWt2A (40 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF40_4 : ((rowsWt2A (40 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD40_4, vB40_2262794929963]; norm_num
theorem vD40_5 : ((rowsWt2A (40 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF40_5 : ((rowsWt2A (40 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD40_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp40a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (40 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF40_0]; norm_num
theorem cmp40a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (40 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF40_2]; norm_num
theorem cmp40a2h_3 : ((rowsWt2A (40 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF40_5]; norm_num
theorem cmp40a0h_4 : ((rowsWt2A (40 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (20047/8000:ℝ) := by rw [vF40_1]; norm_num
theorem leaf_40_cell47_core : ∀ x ∈ rowBox (rowsWt2A (40 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (9967/4000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell07_core (by linarith [cmp40a0l_1]) (by linarith) (by linarith [cmp40a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell39_core (by linarith [cmp40a0l_1]) (by linarith) (by linarith [cmp40a1l_2]) (by linarith) (by linarith) (by linarith [cmp40a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell26_core (by linarith [cmp40a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell46_core (by linarith [cmp40a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp40a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell06_core (by linarith) (by linarith [cmp40a0h_4]) (by linarith [cmp40a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell40_core (by linarith) (by linarith [cmp40a0h_4]) (by linarith [cmp40a1l_2]) (by linarith) (by linarith) (by linarith [cmp40a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell27_core (by linarith) (by linarith [cmp40a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell47_core (by linarith) (by linarith [cmp40a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp40a2h_3]) hd

theorem vD41_0 : ((rowsWt2A (41 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF41_0 : ((rowsWt2A (41 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD41_0, vB40_2755238700253]; norm_num
theorem vD41_1 : ((rowsWt2A (41 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF41_1 : ((rowsWt2A (41 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD41_1, vB40_2770769301995]; norm_num
theorem vD41_2 : ((rowsWt2A (41 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF41_2 : ((rowsWt2A (41 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD41_2, vB40_2940328904376]; norm_num
theorem vD41_3 : ((rowsWt2A (41 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF41_3 : ((rowsWt2A (41 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD41_3, vB40_3109888511976]; norm_num
theorem vD41_4 : ((rowsWt2A (41 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF41_4 : ((rowsWt2A (41 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD41_4, vB40_2262794929963]; norm_num
theorem vD41_5 : ((rowsWt2A (41 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF41_5 : ((rowsWt2A (41 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD41_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp41a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (41 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF41_0]; norm_num
theorem cmp41a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (41 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF41_2]; norm_num
theorem cmp41a2h_3 : ((rowsWt2A (41 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF41_5]; norm_num
theorem cmp41a0h_4 : ((rowsWt2A (41 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF41_1]; norm_num
theorem leaf_41_cell51_vac : ∀ x ∈ rowBox (rowsWt2A (41 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (20047/8000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell06_core (by linarith [cmp41a0l_1]) (by linarith) (by linarith [cmp41a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell40_core (by linarith [cmp41a0l_1]) (by linarith) (by linarith [cmp41a1l_2]) (by linarith) (by linarith) (by linarith [cmp41a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell27_core (by linarith [cmp41a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell47_core (by linarith [cmp41a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp41a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell04_core (by linarith) (by linarith [cmp41a0h_4]) (by linarith [cmp41a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell41_core (by linarith) (by linarith [cmp41a0h_4]) (by linarith [cmp41a1l_2]) (by linarith) (by linarith) (by linarith [cmp41a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell28_core (by linarith) (by linarith [cmp41a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact ((Kepler.NliBanks25.cell51_vac (by linarith) (by linarith [cmp41a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp41a2h_3])) hd).elim

theorem vD42_0 : ((rowsWt2A (42 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF42_0 : ((rowsWt2A (42 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD42_0, vB40_2770769301995]; norm_num
theorem vD42_1 : ((rowsWt2A (42 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF42_1 : ((rowsWt2A (42 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD42_1, vB40_2855549103185]; norm_num
theorem vD42_2 : ((rowsWt2A (42 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF42_2 : ((rowsWt2A (42 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD42_2, vB40_2708646895026]; norm_num
theorem vD42_3 : ((rowsWt2A (42 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF42_3 : ((rowsWt2A (42 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD42_3, vB40_2739708098510]; norm_num
theorem vD42_4 : ((rowsWt2A (42 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF42_4 : ((rowsWt2A (42 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD42_4, vB40_2262794929963]; norm_num
theorem vD42_5 : ((rowsWt2A (42 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF42_5 : ((rowsWt2A (42 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD42_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp42a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (42 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF42_0]; norm_num
theorem cmp42a0l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (42 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF42_0]; norm_num
theorem cmp42a2h_3 : ((rowsWt2A (42 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF42_5]; norm_num
theorem cmp42a1h_4 : ((rowsWt2A (42 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF42_3]; norm_num
theorem cmp42a1h_5 : ((rowsWt2A (42 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF42_3]; norm_num
theorem cmp42a0h_6 : ((rowsWt2A (42 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF42_1]; norm_num
theorem leaf_42_cell34_core : ∀ x ∈ rowBox (rowsWt2A (42 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (63/25:ℝ)
  ·
    by_cases n1 : x 0 ≤ (255855339/100000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (19821/8000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith [cmp42a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith [cmp42a0l_2]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp42a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith [cmp42a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp42a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith [cmp42a0l_2]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp42a1h_5]) (by linarith) (by linarith [cmp42a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (19821/8000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp42a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp42a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp42a1h_5]) (by linarith) (by linarith [cmp42a2h_3]) hd
  ·
    by_cases n1 : x 0 ≤ (255855339/100000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (19821/8000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell11_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp42a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell16_core (by linarith) (by linarith) (by linarith) (by linarith [cmp42a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp42a1h_4]) (by linarith) (by linarith [cmp42a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (19821/8000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell19_core (by linarith) (by linarith [cmp42a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith [cmp42a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp42a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell21_core (by linarith) (by linarith [cmp42a0h_6]) (by linarith) (by linarith [cmp42a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith [cmp42a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp42a1h_4]) (by linarith) (by linarith [cmp42a2h_3]) hd

theorem vD43_0 : ((rowsWt2A (43 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF43_0 : ((rowsWt2A (43 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD43_0, vB40_2770769301995]; norm_num
theorem vD43_1 : ((rowsWt2A (43 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF43_1 : ((rowsWt2A (43 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD43_1, vB40_2855549103185]; norm_num
theorem vD43_2 : ((rowsWt2A (43 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF43_2 : ((rowsWt2A (43 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD43_2, vB40_2739708098510]; norm_num
theorem vD43_3 : ((rowsWt2A (43 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF43_3 : ((rowsWt2A (43 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD43_3, vB40_2770769301995]; norm_num
theorem vD43_4 : ((rowsWt2A (43 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF43_4 : ((rowsWt2A (43 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD43_4, vB40_2262794929963]; norm_num
theorem vD43_5 : ((rowsWt2A (43 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF43_5 : ((rowsWt2A (43 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD43_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp43a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (43 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF43_0]; norm_num
theorem cmp43a0l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (43 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF43_0]; norm_num
theorem cmp43a2h_3 : ((rowsWt2A (43 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF43_5]; norm_num
theorem cmp43a1h_4 : ((rowsWt2A (43 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF43_3]; norm_num
theorem cmp43a1l_5 : (19821/8000:ℝ) ≤ ((rowsWt2A (43 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF43_2]; norm_num
theorem cmp43a0h_6 : ((rowsWt2A (43 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF43_1]; norm_num
theorem leaf_43_cell37_core : ∀ x ∈ rowBox (rowsWt2A (43 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (63/25:ℝ)
  ·
    by_cases n1 : x 0 ≤ (255855339/100000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith [cmp43a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith [cmp43a0l_2]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp43a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell12_core (by linarith [cmp43a0l_1]) (by linarith) (by linarith) (by linarith [cmp43a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith [cmp43a0l_2]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp43a1h_4]) (by linarith) (by linarith [cmp43a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp43a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith) (by linarith) (by linarith [cmp43a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp43a1h_4]) (by linarith) (by linarith [cmp43a2h_3]) hd
  ·
    by_cases n1 : x 0 ≤ (255855339/100000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell16_core (by linarith) (by linarith) (by linarith [cmp43a1l_5]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp43a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith) (by linarith) (by linarith [cmp43a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell37_core (by linarith) (by linarith) (by linarith) (by linarith [cmp43a1h_4]) (by linarith) (by linarith [cmp43a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell21_core (by linarith) (by linarith [cmp43a0h_6]) (by linarith [cmp43a1l_5]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith [cmp43a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp43a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith [cmp43a0h_6]) (by linarith) (by linarith [cmp43a1h_4]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell37_core (by linarith) (by linarith [cmp43a0h_6]) (by linarith) (by linarith [cmp43a1h_4]) (by linarith) (by linarith [cmp43a2h_3]) hd

theorem vD44_0 : ((rowsWt2A (44 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF44_0 : ((rowsWt2A (44 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD44_0, vB40_2855549103185]; norm_num
theorem vD44_1 : ((rowsWt2A (44 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF44_1 : ((rowsWt2A (44 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD44_1, vB40_2940328904376]; norm_num
theorem vD44_2 : ((rowsWt2A (44 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF44_2 : ((rowsWt2A (44 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD44_2, vB40_2708646895026]; norm_num
theorem vD44_3 : ((rowsWt2A (44 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF44_3 : ((rowsWt2A (44 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD44_3, vB40_2739708098510]; norm_num
theorem vD44_4 : ((rowsWt2A (44 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF44_4 : ((rowsWt2A (44 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD44_4, vB40_2262794929963]; norm_num
theorem vD44_5 : ((rowsWt2A (44 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF44_5 : ((rowsWt2A (44 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD44_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp44a0l_1 : (255855339/100000000:ℝ) ≤ ((rowsWt2A (44 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF44_0]; norm_num
theorem cmp44a0l_2 : (63/25:ℝ) ≤ ((rowsWt2A (44 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF44_0]; norm_num
theorem cmp44a2h_3 : ((rowsWt2A (44 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF44_5]; norm_num
theorem cmp44a1h_4 : ((rowsWt2A (44 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF44_3]; norm_num
theorem cmp44a0h_5 : ((rowsWt2A (44 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF44_1]; norm_num
theorem leaf_44_cell42_core : ∀ x ∈ rowBox (rowsWt2A (44 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (129855339/50000000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell19_core (by linarith [cmp44a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell34_core (by linarith [cmp44a0l_2]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp44a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell21_core (by linarith [cmp44a0l_1]) (by linarith) (by linarith) (by linarith [cmp44a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell34_core (by linarith [cmp44a0l_2]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp44a1h_4]) (by linarith) (by linarith [cmp44a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith [cmp44a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell42_core (by linarith) (by linarith [cmp44a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp44a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith [cmp44a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp44a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell42_core (by linarith) (by linarith [cmp44a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp44a1h_4]) (by linarith) (by linarith [cmp44a2h_3]) hd

theorem vD45_0 : ((rowsWt2A (45 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF45_0 : ((rowsWt2A (45 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD45_0, vB40_2855549103185]; norm_num
theorem vD45_1 : ((rowsWt2A (45 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF45_1 : ((rowsWt2A (45 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD45_1, vB40_2940328904376]; norm_num
theorem vD45_2 : ((rowsWt2A (45 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF45_2 : ((rowsWt2A (45 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD45_2, vB40_2739708098510]; norm_num
theorem vD45_3 : ((rowsWt2A (45 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF45_3 : ((rowsWt2A (45 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD45_3, vB40_2770769301995]; norm_num
theorem vD45_4 : ((rowsWt2A (45 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF45_4 : ((rowsWt2A (45 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD45_4, vB40_2262794929963]; norm_num
theorem vD45_5 : ((rowsWt2A (45 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF45_5 : ((rowsWt2A (45 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD45_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp45a0l_1 : (255855339/100000000:ℝ) ≤ ((rowsWt2A (45 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF45_0]; norm_num
theorem cmp45a1l_2 : (19821/8000:ℝ) ≤ ((rowsWt2A (45 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF45_2]; norm_num
theorem cmp45a0l_3 : (63/25:ℝ) ≤ ((rowsWt2A (45 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF45_0]; norm_num
theorem cmp45a2h_4 : ((rowsWt2A (45 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF45_5]; norm_num
theorem cmp45a1h_5 : ((rowsWt2A (45 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF45_3]; norm_num
theorem cmp45a0h_6 : ((rowsWt2A (45 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF45_1]; norm_num
theorem leaf_45_cell43_core : ∀ x ∈ rowBox (rowsWt2A (45 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (129855339/50000000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell21_core (by linarith [cmp45a0l_1]) (by linarith) (by linarith [cmp45a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell34_core (by linarith [cmp45a0l_3]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp45a2h_4]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell02_core (by linarith [cmp45a0l_3]) (by linarith) (by linarith) (by linarith [cmp45a1h_5]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell37_core (by linarith [cmp45a0l_3]) (by linarith) (by linarith) (by linarith [cmp45a1h_5]) (by linarith) (by linarith [cmp45a2h_4]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith [cmp45a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell42_core (by linarith) (by linarith [cmp45a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp45a2h_4]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith [cmp45a0h_6]) (by linarith) (by linarith [cmp45a1h_5]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell43_core (by linarith) (by linarith [cmp45a0h_6]) (by linarith) (by linarith [cmp45a1h_5]) (by linarith) (by linarith [cmp45a2h_4]) hd

theorem vD46_0 : ((rowsWt2A (46 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF46_0 : ((rowsWt2A (46 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD46_0, vB40_2940328904376]; norm_num
theorem vD46_1 : ((rowsWt2A (46 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF46_1 : ((rowsWt2A (46 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD46_1, vB40_3109888511976]; norm_num
theorem vD46_2 : ((rowsWt2A (46 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF46_2 : ((rowsWt2A (46 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD46_2, vB40_2708646895026]; norm_num
theorem vD46_3 : ((rowsWt2A (46 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF46_3 : ((rowsWt2A (46 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD46_3, vB40_2770769301995]; norm_num
theorem vD46_4 : ((rowsWt2A (46 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF46_4 : ((rowsWt2A (46 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD46_4, vB40_2262794929963]; norm_num
theorem vD46_5 : ((rowsWt2A (46 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF46_5 : ((rowsWt2A (46 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD46_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp46a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (46 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF46_0]; norm_num
theorem cmp46a2h_2 : ((rowsWt2A (46 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF46_5]; norm_num
theorem cmp46a1h_3 : ((rowsWt2A (46 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF46_3]; norm_num
theorem leaf_46_cell35_core : ∀ x ∈ rowBox (rowsWt2A (46 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (66855339/25000000:ℝ)
  ·
    by_cases n1 : x 0 ≤ (137566017/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell17_core (by linarith [cmp46a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell42_core (by linarith [cmp46a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp46a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell20_core (by linarith [cmp46a0l_1]) (by linarith) (by linarith) (by linarith [cmp46a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell43_core (by linarith [cmp46a0l_1]) (by linarith) (by linarith) (by linarith [cmp46a1h_3]) (by linarith) (by linarith [cmp46a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp46a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith) (by linarith) (by linarith [cmp46a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp46a1h_3]) (by linarith) (by linarith [cmp46a2h_2]) hd
  ·
    by_cases n1 : x 0 ≤ (137566017/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks24.cell22_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp46a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact Kepler.NliBanks24.cell23_core (by linarith) (by linarith) (by linarith) (by linarith [cmp46a1h_3]) (by linarith) (by linarith) hd
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp46a1h_3]) (by linarith) (by linarith [cmp46a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith)) hd).elim
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp46a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1029/500:ℝ)
        ·
          exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith)) hd).elim
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp46a1h_3]) (by linarith) (by linarith [cmp46a2h_2]) hd

theorem vD47_0 : ((rowsWt2A (47 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF47_0 : ((rowsWt2A (47 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD47_0, vB40_2770769301995]; norm_num
theorem vD47_1 : ((rowsWt2A (47 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF47_1 : ((rowsWt2A (47 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD47_1, vB40_2855549103185]; norm_num
theorem vD47_2 : ((rowsWt2A (47 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF47_2 : ((rowsWt2A (47 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD47_2, vB40_2770769301995]; norm_num
theorem vD47_3 : ((rowsWt2A (47 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF47_3 : ((rowsWt2A (47 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD47_3, vB40_2940328904376]; norm_num
theorem vD47_4 : ((rowsWt2A (47 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF47_4 : ((rowsWt2A (47 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD47_4, vB40_2262794929963]; norm_num
theorem vD47_5 : ((rowsWt2A (47 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF47_5 : ((rowsWt2A (47 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD47_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp47a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (47 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF47_0]; norm_num
theorem cmp47a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (47 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF47_2]; norm_num
theorem cmp47a0l_3 : (9967/4000:ℝ) ≤ ((rowsWt2A (47 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF47_0]; norm_num
theorem cmp47a2h_4 : ((rowsWt2A (47 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF47_5]; norm_num
theorem cmp47a1h_5 : ((rowsWt2A (47 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF47_3]; norm_num
theorem cmp47a0h_6 : ((rowsWt2A (47 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF47_1]; norm_num
theorem leaf_47_cell36_core : ∀ x ∈ rowBox (rowsWt2A (47 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (63/25:ℝ)
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell12_core (by linarith [cmp47a0l_1]) (by linarith) (by linarith [cmp47a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell32_core (by linarith [cmp47a0l_3]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp47a2h_4]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell04_core (by linarith [cmp47a0l_1]) (by linarith) (by linarith) (by linarith [cmp47a1h_5]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell41_core (by linarith [cmp47a0l_1]) (by linarith) (by linarith) (by linarith [cmp47a1h_5]) (by linarith) (by linarith [cmp47a2h_4]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith [cmp47a0h_6]) (by linarith [cmp47a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell37_core (by linarith) (by linarith [cmp47a0h_6]) (by linarith [cmp47a1l_2]) (by linarith) (by linarith) (by linarith [cmp47a2h_4]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell01_core (by linarith) (by linarith [cmp47a0h_6]) (by linarith) (by linarith [cmp47a1h_5]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell36_core (by linarith) (by linarith [cmp47a0h_6]) (by linarith) (by linarith [cmp47a1h_5]) (by linarith) (by linarith [cmp47a2h_4]) hd

theorem vD48_0 : ((rowsWt2A (48 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF48_0 : ((rowsWt2A (48 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD48_0, vB40_2770769301995]; norm_num
theorem vD48_1 : ((rowsWt2A (48 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF48_1 : ((rowsWt2A (48 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD48_1, vB40_2855549103185]; norm_num
theorem vD48_2 : ((rowsWt2A (48 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF48_2 : ((rowsWt2A (48 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD48_2, vB40_2940328904376]; norm_num
theorem vD48_3 : ((rowsWt2A (48 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF48_3 : ((rowsWt2A (48 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD48_3, vB40_3109888511976]; norm_num
theorem vD48_4 : ((rowsWt2A (48 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF48_4 : ((rowsWt2A (48 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD48_4, vB40_2262794929963]; norm_num
theorem vD48_5 : ((rowsWt2A (48 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF48_5 : ((rowsWt2A (48 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD48_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp48a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (48 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF48_0]; norm_num
theorem cmp48a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (48 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF48_2]; norm_num
theorem cmp48a2h_3 : ((rowsWt2A (48 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF48_5]; norm_num
theorem cmp48a0h_4 : ((rowsWt2A (48 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF48_1]; norm_num
theorem leaf_48_cell49_vac : ∀ x ∈ rowBox (rowsWt2A (48 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (63/25:ℝ)
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell04_core (by linarith [cmp48a0l_1]) (by linarith) (by linarith [cmp48a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell41_core (by linarith [cmp48a0l_1]) (by linarith) (by linarith [cmp48a1l_2]) (by linarith) (by linarith) (by linarith [cmp48a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell28_core (by linarith [cmp48a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact ((Kepler.NliBanks25.cell51_vac (by linarith [cmp48a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp48a2h_3])) hd).elim
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell01_core (by linarith) (by linarith [cmp48a0h_4]) (by linarith [cmp48a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell36_core (by linarith) (by linarith [cmp48a0h_4]) (by linarith [cmp48a1l_2]) (by linarith) (by linarith) (by linarith [cmp48a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell24_core (by linarith) (by linarith [cmp48a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact ((Kepler.NliBanks25.cell49_vac (by linarith) (by linarith [cmp48a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp48a2h_3])) hd).elim

theorem vD49_0 : ((rowsWt2A (49 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF49_0 : ((rowsWt2A (49 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD49_0, vB40_2855549103185]; norm_num
theorem vD49_1 : ((rowsWt2A (49 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF49_1 : ((rowsWt2A (49 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD49_1, vB40_2940328904376]; norm_num
theorem vD49_2 : ((rowsWt2A (49 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF49_2 : ((rowsWt2A (49 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD49_2, vB40_2770769301995]; norm_num
theorem vD49_3 : ((rowsWt2A (49 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF49_3 : ((rowsWt2A (49 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD49_3, vB40_2940328904376]; norm_num
theorem vD49_4 : ((rowsWt2A (49 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF49_4 : ((rowsWt2A (49 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD49_4, vB40_2262794929963]; norm_num
theorem vD49_5 : ((rowsWt2A (49 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF49_5 : ((rowsWt2A (49 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD49_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp49a0l_1 : (63/25:ℝ) ≤ ((rowsWt2A (49 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF49_0]; norm_num
theorem cmp49a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (49 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF49_2]; norm_num
theorem cmp49a2h_3 : ((rowsWt2A (49 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF49_5]; norm_num
theorem cmp49a1h_4 : ((rowsWt2A (49 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF49_3]; norm_num
theorem cmp49a0h_5 : ((rowsWt2A (49 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF49_1]; norm_num
theorem leaf_49_cell44_core : ∀ x ∈ rowBox (rowsWt2A (49 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (129855339/50000000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell02_core (by linarith [cmp49a0l_1]) (by linarith) (by linarith [cmp49a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell37_core (by linarith [cmp49a0l_1]) (by linarith) (by linarith [cmp49a1l_2]) (by linarith) (by linarith) (by linarith [cmp49a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell01_core (by linarith [cmp49a0l_1]) (by linarith) (by linarith) (by linarith [cmp49a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell36_core (by linarith [cmp49a0l_1]) (by linarith) (by linarith) (by linarith [cmp49a1h_4]) (by linarith) (by linarith [cmp49a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith [cmp49a0h_5]) (by linarith [cmp49a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell43_core (by linarith) (by linarith [cmp49a0h_5]) (by linarith [cmp49a1l_2]) (by linarith) (by linarith) (by linarith [cmp49a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell18_core (by linarith) (by linarith [cmp49a0h_5]) (by linarith) (by linarith [cmp49a1h_4]) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell44_core (by linarith) (by linarith [cmp49a0h_5]) (by linarith) (by linarith [cmp49a1h_4]) (by linarith) (by linarith [cmp49a2h_3]) hd

theorem vD50_0 : ((rowsWt2A (50 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF50_0 : ((rowsWt2A (50 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD50_0, vB40_2855549103185]; norm_num
theorem vD50_1 : ((rowsWt2A (50 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF50_1 : ((rowsWt2A (50 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD50_1, vB40_2940328904376]; norm_num
theorem vD50_2 : ((rowsWt2A (50 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF50_2 : ((rowsWt2A (50 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD50_2, vB40_2940328904376]; norm_num
theorem vD50_3 : ((rowsWt2A (50 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF50_3 : ((rowsWt2A (50 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD50_3, vB40_3109888511976]; norm_num
theorem vD50_4 : ((rowsWt2A (50 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF50_4 : ((rowsWt2A (50 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD50_4, vB40_2262794929963]; norm_num
theorem vD50_5 : ((rowsWt2A (50 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF50_5 : ((rowsWt2A (50 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD50_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp50a0l_1 : (63/25:ℝ) ≤ ((rowsWt2A (50 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF50_0]; norm_num
theorem cmp50a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (50 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF50_2]; norm_num
theorem cmp50a2h_3 : ((rowsWt2A (50 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF50_5]; norm_num
theorem cmp50a0h_4 : ((rowsWt2A (50 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF50_1]; norm_num
theorem leaf_50_cell50_vac : ∀ x ∈ rowBox (rowsWt2A (50 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (129855339/50000000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks22.cell01_core (by linarith [cmp50a0l_1]) (by linarith) (by linarith [cmp50a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell36_core (by linarith [cmp50a0l_1]) (by linarith) (by linarith [cmp50a1l_2]) (by linarith) (by linarith) (by linarith [cmp50a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks24.cell24_core (by linarith [cmp50a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
      ·
        exact ((Kepler.NliBanks25.cell49_vac (by linarith [cmp50a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp50a2h_3])) hd).elim
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact Kepler.NliBanks23.cell18_core (by linarith) (by linarith [cmp50a0h_4]) (by linarith [cmp50a1l_2]) (by linarith) (by linarith) (by linarith) hd
      ·
        exact Kepler.NliBanks25.cell44_core (by linarith) (by linarith [cmp50a0h_4]) (by linarith [cmp50a1l_2]) (by linarith) (by linarith) (by linarith [cmp50a2h_3]) hd
    ·
      by_cases n2 : x 2 ≤ (1029/500:ℝ)
      ·
        exact ((Kepler.NliBanks24.cell29_vac (by linarith) (by linarith [cmp50a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
      ·
        exact ((Kepler.NliBanks25.cell50_vac (by linarith) (by linarith [cmp50a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp50a2h_3])) hd).elim

theorem vD51_0 : ((rowsWt2A (51 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF51_0 : ((rowsWt2A (51 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD51_0, vB40_2940328904376]; norm_num
theorem vD51_1 : ((rowsWt2A (51 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF51_1 : ((rowsWt2A (51 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD51_1, vB40_3109888511976]; norm_num
theorem vD51_2 : ((rowsWt2A (51 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF51_2 : ((rowsWt2A (51 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD51_2, vB40_2770769301995]; norm_num
theorem vD51_3 : ((rowsWt2A (51 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF51_3 : ((rowsWt2A (51 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD51_3, vB40_3109888511976]; norm_num
theorem vD51_4 : ((rowsWt2A (51 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF51_4 : ((rowsWt2A (51 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD51_4, vB40_2262794929963]; norm_num
theorem vD51_5 : ((rowsWt2A (51 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF51_5 : ((rowsWt2A (51 : Fin 62)).boxHi (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD51_5, vB40_2390338278785]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp51a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (51 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF51_0]; norm_num
theorem cmp51a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (51 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF51_2]; norm_num
theorem cmp51a2h_3 : ((rowsWt2A (51 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1087/500:ℝ) := by rw [vF51_5]; norm_num
theorem leaf_51_cell48_vac : ∀ x ∈ rowBox (rowsWt2A (51 : Fin 62)),
    (2:ℝ) * Kepler.Text.hminus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
    (2:ℝ) * Kepler.Text.hminus ≤ x 1 → x 1 ≤ Real.sqrt 8 →
    (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
    (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
    (0:ℝ) < Kepler.NliBanks19.w2aF (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hd
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (66855339/25000000:ℝ)
  ·
    by_cases n1 : x 0 ≤ (137566017/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks23.cell20_core (by linarith [cmp51a0l_1]) (by linarith) (by linarith [cmp51a1l_2]) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell43_core (by linarith [cmp51a0l_1]) (by linarith) (by linarith [cmp51a1l_2]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks23.cell18_core (by linarith [cmp51a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell43_core (by linarith [cmp51a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks23.cell18_core (by linarith [cmp51a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell44_core (by linarith [cmp51a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact ((Kepler.NliBanks24.cell29_vac (by linarith [cmp51a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)) hd).elim
          ·
            exact ((Kepler.NliBanks25.cell50_vac (by linarith [cmp51a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3])) hd).elim
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith) (by linarith [cmp51a1l_2]) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell44_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3])) hd).elim
  ·
    by_cases n1 : x 0 ≤ (137566017/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks24.cell23_core (by linarith) (by linarith) (by linarith [cmp51a1l_2]) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3])) hd).elim
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3])) hd).elim
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp51a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3])) hd).elim
        ·
          by_cases n4 : x 2 ≤ (1029/500:ℝ)
          ·
            exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd
          ·
            exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp51a2h_3])) hd).elim

end Kepler.NliKit.BoxTreeWt2A

