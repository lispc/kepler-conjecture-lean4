/-
Kepler.NliKit.BoxTreeWt2AS0 — leaf witnesses, shard 0 of the
wt2A tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeWt2ARows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeWt2A

open Kepler.NliKit.BoxTree

theorem vD00_0 : ((rowsWt2A (0 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF00_0 : ((rowsWt2A (0 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD00_0, vB40_2708646895026]; norm_num
theorem vD00_1 : ((rowsWt2A (0 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF00_1 : ((rowsWt2A (0 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD00_1, vB40_2724177496768]; norm_num
theorem vD00_2 : ((rowsWt2A (0 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF00_2 : ((rowsWt2A (0 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD00_2, vB40_2708646895026]; norm_num
theorem vD00_3 : ((rowsWt2A (0 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF00_3 : ((rowsWt2A (0 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD00_3, vB40_2739708098510]; norm_num
theorem vD00_4 : ((rowsWt2A (0 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF00_4 : ((rowsWt2A (0 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD00_4, vB40_2199023255552]; norm_num
theorem vD00_5 : ((rowsWt2A (0 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF00_5 : ((rowsWt2A (0 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD00_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp00a0h_1 : ((rowsWt2A (0 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF00_1]; norm_num
theorem cmp00a1h_2 : ((rowsWt2A (0 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF00_3]; norm_num
theorem cmp00a2h_3 : ((rowsWt2A (0 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF00_5]; norm_num
theorem leaf_00_cell10_core : ∀ x ∈ rowBox (rowsWt2A (0 : Fin 62)),
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
  exact Kepler.NliBanks22.cell10_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp00a0h_1]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp00a1h_2]) (by linarith) (by linarith [cmp00a2h_3]) hd

theorem vD01_0 : ((rowsWt2A (1 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF01_0 : ((rowsWt2A (1 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD01_0, vB40_2708646895026]; norm_num
theorem vD01_1 : ((rowsWt2A (1 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF01_1 : ((rowsWt2A (1 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD01_1, vB40_2724177496768]; norm_num
theorem vD01_2 : ((rowsWt2A (1 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF01_2 : ((rowsWt2A (1 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD01_2, vB40_2739708098510]; norm_num
theorem vD01_3 : ((rowsWt2A (1 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF01_3 : ((rowsWt2A (1 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD01_3, vB40_2770769301995]; norm_num
theorem vD01_4 : ((rowsWt2A (1 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF01_4 : ((rowsWt2A (1 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD01_4, vB40_2199023255552]; norm_num
theorem vD01_5 : ((rowsWt2A (1 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF01_5 : ((rowsWt2A (1 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD01_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp01a0h_1 : ((rowsWt2A (1 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF01_1]; norm_num
theorem cmp01a2h_2 : ((rowsWt2A (1 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF01_5]; norm_num
theorem cmp01a1h_3 : ((rowsWt2A (1 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF01_3]; norm_num
theorem leaf_01_cell15_core : ∀ x ∈ rowBox (rowsWt2A (1 : Fin 62)),
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
  by_cases n0 : x 1 ≤ (9967/4000:ℝ)
  ·
    exact Kepler.NliBanks22.cell10_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp01a0h_1]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp01a2h_2]) hd
  ·
    exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp01a0h_1]) (by linarith) (by linarith [cmp01a1h_3]) (by linarith) (by linarith [cmp01a2h_2]) hd

theorem vD02_0 : ((rowsWt2A (2 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF02_0 : ((rowsWt2A (2 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD02_0, vB40_2708646895026]; norm_num
theorem vD02_1 : ((rowsWt2A (2 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF02_1 : ((rowsWt2A (2 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD02_1, vB40_2724177496768]; norm_num
theorem vD02_2 : ((rowsWt2A (2 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF02_2 : ((rowsWt2A (2 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD02_2, vB40_2770769301995]; norm_num
theorem vD02_3 : ((rowsWt2A (2 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF02_3 : ((rowsWt2A (2 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD02_3, vB40_2940328904376]; norm_num
theorem vD02_4 : ((rowsWt2A (2 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF02_4 : ((rowsWt2A (2 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD02_4, vB40_2199023255552]; norm_num
theorem vD02_5 : ((rowsWt2A (2 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF02_5 : ((rowsWt2A (2 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD02_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp02a0h_1 : ((rowsWt2A (2 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF02_1]; norm_num
theorem cmp02a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (2 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF02_2]; norm_num
theorem cmp02a2h_3 : ((rowsWt2A (2 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF02_5]; norm_num
theorem cmp02a1h_4 : ((rowsWt2A (2 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF02_3]; norm_num
theorem leaf_02_cell05_core : ∀ x ∈ rowBox (rowsWt2A (2 : Fin 62)),
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
    exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp02a0h_1]) (by linarith [cmp02a1l_2]) (by linarith) (by linarith) (by linarith [cmp02a2h_3]) hd
  ·
    exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp02a0h_1]) (by linarith) (by linarith [cmp02a1h_4]) (by linarith) (by linarith [cmp02a2h_3]) hd

theorem vD03_0 : ((rowsWt2A (3 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF03_0 : ((rowsWt2A (3 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD03_0, vB40_2708646895026]; norm_num
theorem vD03_1 : ((rowsWt2A (3 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF03_1 : ((rowsWt2A (3 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD03_1, vB40_2724177496768]; norm_num
theorem vD03_2 : ((rowsWt2A (3 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF03_2 : ((rowsWt2A (3 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD03_2, vB40_2940328904376]; norm_num
theorem vD03_3 : ((rowsWt2A (3 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF03_3 : ((rowsWt2A (3 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD03_3, vB40_3109888511976]; norm_num
theorem vD03_4 : ((rowsWt2A (3 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF03_4 : ((rowsWt2A (3 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD03_4, vB40_2199023255552]; norm_num
theorem vD03_5 : ((rowsWt2A (3 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF03_5 : ((rowsWt2A (3 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD03_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp03a0h_1 : ((rowsWt2A (3 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF03_1]; norm_num
theorem cmp03a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (3 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF03_2]; norm_num
theorem cmp03a2h_3 : ((rowsWt2A (3 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF03_5]; norm_num
theorem leaf_03_cell25_core : ∀ x ∈ rowBox (rowsWt2A (3 : Fin 62)),
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
    exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp03a0h_1]) (by linarith [cmp03a1l_2]) (by linarith) (by linarith) (by linarith [cmp03a2h_3]) hd
  ·
    exact Kepler.NliBanks24.cell25_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp03a0h_1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp03a2h_3]) hd

theorem vD04_0 : ((rowsWt2A (4 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF04_0 : ((rowsWt2A (4 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD04_0, vB40_2724177496768]; norm_num
theorem vD04_1 : ((rowsWt2A (4 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF04_1 : ((rowsWt2A (4 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD04_1, vB40_2739708098510]; norm_num
theorem vD04_2 : ((rowsWt2A (4 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF04_2 : ((rowsWt2A (4 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD04_2, vB40_2708646895026]; norm_num
theorem vD04_3 : ((rowsWt2A (4 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF04_3 : ((rowsWt2A (4 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD04_3, vB40_2739708098510]; norm_num
theorem vD04_4 : ((rowsWt2A (4 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF04_4 : ((rowsWt2A (4 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD04_4, vB40_2199023255552]; norm_num
theorem vD04_5 : ((rowsWt2A (4 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF04_5 : ((rowsWt2A (4 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD04_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp04a1h_1 : ((rowsWt2A (4 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF04_3]; norm_num
theorem cmp04a2h_2 : ((rowsWt2A (4 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF04_5]; norm_num
theorem cmp04a0h_3 : ((rowsWt2A (4 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF04_1]; norm_num
theorem leaf_04_cell09_core : ∀ x ∈ rowBox (rowsWt2A (4 : Fin 62)),
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
    exact Kepler.NliBanks22.cell10_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp04a1h_1]) (by linarith) (by linarith [cmp04a2h_2]) hd
  ·
    exact Kepler.NliBanks22.cell09_core (by linarith) (by linarith [cmp04a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp04a1h_1]) (by linarith) (by linarith [cmp04a2h_2]) hd

theorem vD05_0 : ((rowsWt2A (5 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF05_0 : ((rowsWt2A (5 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD05_0, vB40_2724177496768]; norm_num
theorem vD05_1 : ((rowsWt2A (5 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF05_1 : ((rowsWt2A (5 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD05_1, vB40_2739708098510]; norm_num
theorem vD05_2 : ((rowsWt2A (5 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF05_2 : ((rowsWt2A (5 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD05_2, vB40_2739708098510]; norm_num
theorem vD05_3 : ((rowsWt2A (5 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF05_3 : ((rowsWt2A (5 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD05_3, vB40_2770769301995]; norm_num
theorem vD05_4 : ((rowsWt2A (5 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF05_4 : ((rowsWt2A (5 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD05_4, vB40_2199023255552]; norm_num
theorem vD05_5 : ((rowsWt2A (5 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF05_5 : ((rowsWt2A (5 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD05_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp05a2h_1 : ((rowsWt2A (5 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF05_5]; norm_num
theorem cmp05a1h_2 : ((rowsWt2A (5 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF05_3]; norm_num
theorem cmp05a0h_3 : ((rowsWt2A (5 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF05_1]; norm_num
theorem leaf_05_cell14_core : ∀ x ∈ rowBox (rowsWt2A (5 : Fin 62)),
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
      exact Kepler.NliBanks22.cell10_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp05a2h_1]) hd
    ·
      exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp05a1h_2]) (by linarith) (by linarith [cmp05a2h_1]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks22.cell09_core (by linarith) (by linarith [cmp05a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp05a2h_1]) hd
    ·
      exact Kepler.NliBanks23.cell14_core (by linarith) (by linarith [cmp05a0h_3]) (by linarith) (by linarith [cmp05a1h_2]) (by linarith) (by linarith [cmp05a2h_1]) hd

theorem vD06_0 : ((rowsWt2A (6 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF06_0 : ((rowsWt2A (6 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD06_0, vB40_2724177496768]; norm_num
theorem vD06_1 : ((rowsWt2A (6 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF06_1 : ((rowsWt2A (6 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD06_1, vB40_2739708098510]; norm_num
theorem vD06_2 : ((rowsWt2A (6 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF06_2 : ((rowsWt2A (6 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD06_2, vB40_2770769301995]; norm_num
theorem vD06_3 : ((rowsWt2A (6 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF06_3 : ((rowsWt2A (6 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD06_3, vB40_2940328904376]; norm_num
theorem vD06_4 : ((rowsWt2A (6 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF06_4 : ((rowsWt2A (6 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD06_4, vB40_2199023255552]; norm_num
theorem vD06_5 : ((rowsWt2A (6 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF06_5 : ((rowsWt2A (6 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD06_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp06a1l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (6 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF06_2]; norm_num
theorem cmp06a2h_2 : ((rowsWt2A (6 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF06_5]; norm_num
theorem cmp06a1h_3 : ((rowsWt2A (6 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF06_3]; norm_num
theorem cmp06a0h_4 : ((rowsWt2A (6 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF06_1]; norm_num
theorem leaf_06_cell07_core : ∀ x ∈ rowBox (rowsWt2A (6 : Fin 62)),
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
      exact Kepler.NliBanks23.cell15_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp06a1l_1]) (by linarith) (by linarith) (by linarith [cmp06a2h_2]) hd
    ·
      exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp06a1h_3]) (by linarith) (by linarith [cmp06a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      exact Kepler.NliBanks23.cell14_core (by linarith) (by linarith [cmp06a0h_4]) (by linarith [cmp06a1l_1]) (by linarith) (by linarith) (by linarith [cmp06a2h_2]) hd
    ·
      exact Kepler.NliBanks22.cell07_core (by linarith) (by linarith [cmp06a0h_4]) (by linarith) (by linarith [cmp06a1h_3]) (by linarith) (by linarith [cmp06a2h_2]) hd

theorem vD07_0 : ((rowsWt2A (7 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF07_0 : ((rowsWt2A (7 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD07_0, vB40_2724177496768]; norm_num
theorem vD07_1 : ((rowsWt2A (7 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF07_1 : ((rowsWt2A (7 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD07_1, vB40_2739708098510]; norm_num
theorem vD07_2 : ((rowsWt2A (7 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF07_2 : ((rowsWt2A (7 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD07_2, vB40_2940328904376]; norm_num
theorem vD07_3 : ((rowsWt2A (7 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF07_3 : ((rowsWt2A (7 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD07_3, vB40_3109888511976]; norm_num
theorem vD07_4 : ((rowsWt2A (7 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF07_4 : ((rowsWt2A (7 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD07_4, vB40_2199023255552]; norm_num
theorem vD07_5 : ((rowsWt2A (7 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF07_5 : ((rowsWt2A (7 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD07_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp07a1l_1 : (63/25:ℝ) ≤ ((rowsWt2A (7 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF07_2]; norm_num
theorem cmp07a2h_2 : ((rowsWt2A (7 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF07_5]; norm_num
theorem cmp07a0h_3 : ((rowsWt2A (7 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF07_1]; norm_num
theorem leaf_07_cell26_core : ∀ x ∈ rowBox (rowsWt2A (7 : Fin 62)),
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
      exact Kepler.NliBanks22.cell05_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp07a1l_1]) (by linarith) (by linarith) (by linarith [cmp07a2h_2]) hd
    ·
      exact Kepler.NliBanks24.cell25_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp07a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      exact Kepler.NliBanks22.cell07_core (by linarith) (by linarith [cmp07a0h_3]) (by linarith [cmp07a1l_1]) (by linarith) (by linarith) (by linarith [cmp07a2h_2]) hd
    ·
      exact Kepler.NliBanks24.cell26_core (by linarith) (by linarith [cmp07a0h_3]) (by linarith) (by linarith) (by linarith) (by linarith [cmp07a2h_2]) hd

theorem vD08_0 : ((rowsWt2A (8 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF08_0 : ((rowsWt2A (8 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD08_0, vB40_2739708098510]; norm_num
theorem vD08_1 : ((rowsWt2A (8 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF08_1 : ((rowsWt2A (8 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD08_1, vB40_2755238700253]; norm_num
theorem vD08_2 : ((rowsWt2A (8 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF08_2 : ((rowsWt2A (8 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD08_2, vB40_2708646895026]; norm_num
theorem vD08_3 : ((rowsWt2A (8 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF08_3 : ((rowsWt2A (8 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD08_3, vB40_2739708098510]; norm_num
theorem vD08_4 : ((rowsWt2A (8 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF08_4 : ((rowsWt2A (8 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD08_4, vB40_2199023255552]; norm_num
theorem vD08_5 : ((rowsWt2A (8 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF08_5 : ((rowsWt2A (8 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD08_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp08a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (8 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF08_0]; norm_num
theorem cmp08a1h_2 : ((rowsWt2A (8 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF08_3]; norm_num
theorem cmp08a2h_3 : ((rowsWt2A (8 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF08_5]; norm_num
theorem cmp08a0h_4 : ((rowsWt2A (8 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (20047/8000:ℝ) := by rw [vF08_1]; norm_num
theorem leaf_08_cell08_core : ∀ x ∈ rowBox (rowsWt2A (8 : Fin 62)),
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
    exact Kepler.NliBanks22.cell09_core (by linarith [cmp08a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp08a1h_2]) (by linarith) (by linarith [cmp08a2h_3]) hd
  ·
    exact Kepler.NliBanks22.cell08_core (by linarith) (by linarith [cmp08a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp08a1h_2]) (by linarith) (by linarith [cmp08a2h_3]) hd

theorem vD09_0 : ((rowsWt2A (9 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF09_0 : ((rowsWt2A (9 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD09_0, vB40_2739708098510]; norm_num
theorem vD09_1 : ((rowsWt2A (9 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF09_1 : ((rowsWt2A (9 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD09_1, vB40_2755238700253]; norm_num
theorem vD09_2 : ((rowsWt2A (9 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF09_2 : ((rowsWt2A (9 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD09_2, vB40_2739708098510]; norm_num
theorem vD09_3 : ((rowsWt2A (9 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF09_3 : ((rowsWt2A (9 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD09_3, vB40_2770769301995]; norm_num
theorem vD09_4 : ((rowsWt2A (9 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF09_4 : ((rowsWt2A (9 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD09_4, vB40_2199023255552]; norm_num
theorem vD09_5 : ((rowsWt2A (9 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF09_5 : ((rowsWt2A (9 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD09_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp09a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (9 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF09_0]; norm_num
theorem cmp09a2h_2 : ((rowsWt2A (9 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF09_5]; norm_num
theorem cmp09a1h_3 : ((rowsWt2A (9 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF09_3]; norm_num
theorem cmp09a0h_4 : ((rowsWt2A (9 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (20047/8000:ℝ) := by rw [vF09_1]; norm_num
theorem leaf_09_cell13_core : ∀ x ∈ rowBox (rowsWt2A (9 : Fin 62)),
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
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks22.cell09_core (by linarith [cmp09a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp09a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell14_core (by linarith [cmp09a0l_1]) (by linarith) (by linarith) (by linarith [cmp09a1h_3]) (by linarith) (by linarith [cmp09a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks22.cell08_core (by linarith) (by linarith [cmp09a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp09a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell13_core (by linarith) (by linarith [cmp09a0h_4]) (by linarith) (by linarith [cmp09a1h_3]) (by linarith) (by linarith [cmp09a2h_2]) hd

theorem vD10_0 : ((rowsWt2A (10 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF10_0 : ((rowsWt2A (10 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD10_0, vB40_2739708098510]; norm_num
theorem vD10_1 : ((rowsWt2A (10 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF10_1 : ((rowsWt2A (10 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD10_1, vB40_2755238700253]; norm_num
theorem vD10_2 : ((rowsWt2A (10 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF10_2 : ((rowsWt2A (10 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD10_2, vB40_2770769301995]; norm_num
theorem vD10_3 : ((rowsWt2A (10 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF10_3 : ((rowsWt2A (10 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD10_3, vB40_2940328904376]; norm_num
theorem vD10_4 : ((rowsWt2A (10 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF10_4 : ((rowsWt2A (10 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD10_4, vB40_2199023255552]; norm_num
theorem vD10_5 : ((rowsWt2A (10 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF10_5 : ((rowsWt2A (10 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD10_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp10a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (10 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF10_0]; norm_num
theorem cmp10a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (10 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF10_2]; norm_num
theorem cmp10a2h_3 : ((rowsWt2A (10 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF10_5]; norm_num
theorem cmp10a1h_4 : ((rowsWt2A (10 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF10_3]; norm_num
theorem cmp10a0h_5 : ((rowsWt2A (10 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (20047/8000:ℝ) := by rw [vF10_1]; norm_num
theorem leaf_10_cell06_core : ∀ x ∈ rowBox (rowsWt2A (10 : Fin 62)),
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
      exact Kepler.NliBanks23.cell14_core (by linarith [cmp10a0l_1]) (by linarith) (by linarith [cmp10a1l_2]) (by linarith) (by linarith) (by linarith [cmp10a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell07_core (by linarith [cmp10a0l_1]) (by linarith) (by linarith) (by linarith [cmp10a1h_4]) (by linarith) (by linarith [cmp10a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      exact Kepler.NliBanks23.cell13_core (by linarith) (by linarith [cmp10a0h_5]) (by linarith [cmp10a1l_2]) (by linarith) (by linarith) (by linarith [cmp10a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell06_core (by linarith) (by linarith [cmp10a0h_5]) (by linarith) (by linarith [cmp10a1h_4]) (by linarith) (by linarith [cmp10a2h_3]) hd

theorem vD11_0 : ((rowsWt2A (11 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF11_0 : ((rowsWt2A (11 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD11_0, vB40_2739708098510]; norm_num
theorem vD11_1 : ((rowsWt2A (11 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF11_1 : ((rowsWt2A (11 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD11_1, vB40_2755238700253]; norm_num
theorem vD11_2 : ((rowsWt2A (11 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF11_2 : ((rowsWt2A (11 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD11_2, vB40_2940328904376]; norm_num
theorem vD11_3 : ((rowsWt2A (11 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF11_3 : ((rowsWt2A (11 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD11_3, vB40_3109888511976]; norm_num
theorem vD11_4 : ((rowsWt2A (11 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF11_4 : ((rowsWt2A (11 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD11_4, vB40_2199023255552]; norm_num
theorem vD11_5 : ((rowsWt2A (11 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF11_5 : ((rowsWt2A (11 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD11_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp11a0l_1 : (19821/8000:ℝ) ≤ ((rowsWt2A (11 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF11_0]; norm_num
theorem cmp11a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (11 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF11_2]; norm_num
theorem cmp11a2h_3 : ((rowsWt2A (11 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF11_5]; norm_num
theorem cmp11a0h_4 : ((rowsWt2A (11 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (20047/8000:ℝ) := by rw [vF11_1]; norm_num
theorem leaf_11_cell27_core : ∀ x ∈ rowBox (rowsWt2A (11 : Fin 62)),
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
      exact Kepler.NliBanks22.cell07_core (by linarith [cmp11a0l_1]) (by linarith) (by linarith [cmp11a1l_2]) (by linarith) (by linarith) (by linarith [cmp11a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell26_core (by linarith [cmp11a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp11a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      exact Kepler.NliBanks22.cell06_core (by linarith) (by linarith [cmp11a0h_4]) (by linarith [cmp11a1l_2]) (by linarith) (by linarith) (by linarith [cmp11a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell27_core (by linarith) (by linarith [cmp11a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp11a2h_3]) hd

theorem vD12_0 : ((rowsWt2A (12 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF12_0 : ((rowsWt2A (12 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD12_0, vB40_2755238700253]; norm_num
theorem vD12_1 : ((rowsWt2A (12 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF12_1 : ((rowsWt2A (12 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD12_1, vB40_2770769301995]; norm_num
theorem vD12_2 : ((rowsWt2A (12 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF12_2 : ((rowsWt2A (12 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD12_2, vB40_2708646895026]; norm_num
theorem vD12_3 : ((rowsWt2A (12 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF12_3 : ((rowsWt2A (12 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD12_3, vB40_2739708098510]; norm_num
theorem vD12_4 : ((rowsWt2A (12 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF12_4 : ((rowsWt2A (12 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD12_4, vB40_2199023255552]; norm_num
theorem vD12_5 : ((rowsWt2A (12 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF12_5 : ((rowsWt2A (12 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD12_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp12a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (12 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF12_0]; norm_num
theorem cmp12a1h_2 : ((rowsWt2A (12 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF12_3]; norm_num
theorem cmp12a2h_3 : ((rowsWt2A (12 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF12_5]; norm_num
theorem cmp12a0h_4 : ((rowsWt2A (12 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF12_1]; norm_num
theorem leaf_12_cell03_core : ∀ x ∈ rowBox (rowsWt2A (12 : Fin 62)),
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
    exact Kepler.NliBanks22.cell08_core (by linarith [cmp12a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp12a1h_2]) (by linarith) (by linarith [cmp12a2h_3]) hd
  ·
    exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith [cmp12a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp12a1h_2]) (by linarith) (by linarith [cmp12a2h_3]) hd

theorem vD13_0 : ((rowsWt2A (13 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF13_0 : ((rowsWt2A (13 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD13_0, vB40_2755238700253]; norm_num
theorem vD13_1 : ((rowsWt2A (13 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF13_1 : ((rowsWt2A (13 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD13_1, vB40_2770769301995]; norm_num
theorem vD13_2 : ((rowsWt2A (13 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF13_2 : ((rowsWt2A (13 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD13_2, vB40_2739708098510]; norm_num
theorem vD13_3 : ((rowsWt2A (13 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF13_3 : ((rowsWt2A (13 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD13_3, vB40_2770769301995]; norm_num
theorem vD13_4 : ((rowsWt2A (13 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF13_4 : ((rowsWt2A (13 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD13_4, vB40_2199023255552]; norm_num
theorem vD13_5 : ((rowsWt2A (13 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF13_5 : ((rowsWt2A (13 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD13_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp13a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (13 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF13_0]; norm_num
theorem cmp13a2h_2 : ((rowsWt2A (13 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF13_5]; norm_num
theorem cmp13a1h_3 : ((rowsWt2A (13 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF13_3]; norm_num
theorem cmp13a0h_4 : ((rowsWt2A (13 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF13_1]; norm_num
theorem leaf_13_cell12_core : ∀ x ∈ rowBox (rowsWt2A (13 : Fin 62)),
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
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks22.cell08_core (by linarith [cmp13a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp13a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell13_core (by linarith [cmp13a0l_1]) (by linarith) (by linarith) (by linarith [cmp13a1h_3]) (by linarith) (by linarith [cmp13a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith [cmp13a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp13a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell12_core (by linarith) (by linarith [cmp13a0h_4]) (by linarith) (by linarith [cmp13a1h_3]) (by linarith) (by linarith [cmp13a2h_2]) hd

theorem vD14_0 : ((rowsWt2A (14 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF14_0 : ((rowsWt2A (14 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD14_0, vB40_2755238700253]; norm_num
theorem vD14_1 : ((rowsWt2A (14 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF14_1 : ((rowsWt2A (14 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD14_1, vB40_2770769301995]; norm_num
theorem vD14_2 : ((rowsWt2A (14 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF14_2 : ((rowsWt2A (14 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD14_2, vB40_2770769301995]; norm_num
theorem vD14_3 : ((rowsWt2A (14 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF14_3 : ((rowsWt2A (14 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD14_3, vB40_2940328904376]; norm_num
theorem vD14_4 : ((rowsWt2A (14 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF14_4 : ((rowsWt2A (14 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD14_4, vB40_2199023255552]; norm_num
theorem vD14_5 : ((rowsWt2A (14 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF14_5 : ((rowsWt2A (14 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD14_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp14a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (14 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF14_0]; norm_num
theorem cmp14a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (14 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF14_2]; norm_num
theorem cmp14a2h_3 : ((rowsWt2A (14 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF14_5]; norm_num
theorem cmp14a1h_4 : ((rowsWt2A (14 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF14_3]; norm_num
theorem cmp14a0h_5 : ((rowsWt2A (14 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF14_1]; norm_num
theorem leaf_14_cell04_core : ∀ x ∈ rowBox (rowsWt2A (14 : Fin 62)),
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
      exact Kepler.NliBanks23.cell13_core (by linarith [cmp14a0l_1]) (by linarith) (by linarith [cmp14a1l_2]) (by linarith) (by linarith) (by linarith [cmp14a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell06_core (by linarith [cmp14a0l_1]) (by linarith) (by linarith) (by linarith [cmp14a1h_4]) (by linarith) (by linarith [cmp14a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      exact Kepler.NliBanks23.cell12_core (by linarith) (by linarith [cmp14a0h_5]) (by linarith [cmp14a1l_2]) (by linarith) (by linarith) (by linarith [cmp14a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell04_core (by linarith) (by linarith [cmp14a0h_5]) (by linarith) (by linarith [cmp14a1h_4]) (by linarith) (by linarith [cmp14a2h_3]) hd

theorem vD15_0 : ((rowsWt2A (15 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2755238700253, 2755238700253⟩ : DC) := by decide
theorem vF15_0 : ((rowsWt2A (15 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5058749999998326529748737812042236328125 := by rw [vD15_0, vB40_2755238700253]; norm_num
theorem vD15_1 : ((rowsWt2A (15 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF15_1 : ((rowsWt2A (15 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD15_1, vB40_2770769301995]; norm_num
theorem vD15_2 : ((rowsWt2A (15 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF15_2 : ((rowsWt2A (15 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD15_2, vB40_2940328904376]; norm_num
theorem vD15_3 : ((rowsWt2A (15 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF15_3 : ((rowsWt2A (15 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD15_3, vB40_3109888511976]; norm_num
theorem vD15_4 : ((rowsWt2A (15 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF15_4 : ((rowsWt2A (15 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD15_4, vB40_2199023255552]; norm_num
theorem vD15_5 : ((rowsWt2A (15 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF15_5 : ((rowsWt2A (15 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD15_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp15a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (15 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF15_0]; norm_num
theorem cmp15a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (15 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF15_2]; norm_num
theorem cmp15a2h_3 : ((rowsWt2A (15 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF15_5]; norm_num
theorem cmp15a0h_4 : ((rowsWt2A (15 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF15_1]; norm_num
theorem leaf_15_cell28_core : ∀ x ∈ rowBox (rowsWt2A (15 : Fin 62)),
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
      exact Kepler.NliBanks22.cell06_core (by linarith [cmp15a0l_1]) (by linarith) (by linarith [cmp15a1l_2]) (by linarith) (by linarith) (by linarith [cmp15a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell27_core (by linarith [cmp15a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp15a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      exact Kepler.NliBanks22.cell04_core (by linarith) (by linarith [cmp15a0h_4]) (by linarith [cmp15a1l_2]) (by linarith) (by linarith) (by linarith [cmp15a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell28_core (by linarith) (by linarith [cmp15a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp15a2h_3]) hd

theorem vD16_0 : ((rowsWt2A (16 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF16_0 : ((rowsWt2A (16 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD16_0, vB40_2770769301995]; norm_num
theorem vD16_1 : ((rowsWt2A (16 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2813159202590, 2813159202590⟩ : DC) := by decide
theorem vF16_1 : ((rowsWt2A (16 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5585533899993606610223650932312011718750 := by rw [vD16_1, vB40_2813159202590]; norm_num
theorem vD16_2 : ((rowsWt2A (16 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF16_2 : ((rowsWt2A (16 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD16_2, vB40_2708646895026]; norm_num
theorem vD16_3 : ((rowsWt2A (16 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF16_3 : ((rowsWt2A (16 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD16_3, vB40_2724177496768]; norm_num
theorem vD16_4 : ((rowsWt2A (16 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF16_4 : ((rowsWt2A (16 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD16_4, vB40_2199023255552]; norm_num
theorem vD16_5 : ((rowsWt2A (16 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF16_5 : ((rowsWt2A (16 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD16_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp16a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (16 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF16_0]; norm_num
theorem cmp16a1h_2 : ((rowsWt2A (16 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF16_3]; norm_num
theorem cmp16a2h_3 : ((rowsWt2A (16 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF16_5]; norm_num
theorem cmp16a0h_4 : ((rowsWt2A (16 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (255855339/100000000:ℝ) := by rw [vF16_1]; norm_num
theorem cmp16a1h_5 : ((rowsWt2A (16 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF16_3]; norm_num
theorem leaf_16_cell11_core : ∀ x ∈ rowBox (rowsWt2A (16 : Fin 62)),
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
    exact Kepler.NliBanks22.cell03_core (by linarith [cmp16a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp16a1h_2]) (by linarith) (by linarith [cmp16a2h_3]) hd
  ·
    exact Kepler.NliBanks23.cell11_core (by linarith) (by linarith [cmp16a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp16a1h_5]) (by linarith) (by linarith [cmp16a2h_3]) hd

theorem vD17_0 : ((rowsWt2A (17 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF17_0 : ((rowsWt2A (17 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD17_0, vB40_2770769301995]; norm_num
theorem vD17_1 : ((rowsWt2A (17 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2813159202590, 2813159202590⟩ : DC) := by decide
theorem vF17_1 : ((rowsWt2A (17 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5585533899993606610223650932312011718750 := by rw [vD17_1, vB40_2813159202590]; norm_num
theorem vD17_2 : ((rowsWt2A (17 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF17_2 : ((rowsWt2A (17 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD17_2, vB40_2724177496768]; norm_num
theorem vD17_3 : ((rowsWt2A (17 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF17_3 : ((rowsWt2A (17 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD17_3, vB40_2739708098510]; norm_num
theorem vD17_4 : ((rowsWt2A (17 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF17_4 : ((rowsWt2A (17 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD17_4, vB40_2199023255552]; norm_num
theorem vD17_5 : ((rowsWt2A (17 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF17_5 : ((rowsWt2A (17 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD17_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp17a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (17 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF17_0]; norm_num
theorem cmp17a2h_2 : ((rowsWt2A (17 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF17_5]; norm_num
theorem cmp17a1h_3 : ((rowsWt2A (17 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF17_3]; norm_num
theorem cmp17a0h_4 : ((rowsWt2A (17 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (255855339/100000000:ℝ) := by rw [vF17_1]; norm_num
theorem leaf_17_cell16_core : ∀ x ∈ rowBox (rowsWt2A (17 : Fin 62)),
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
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      exact Kepler.NliBanks22.cell03_core (by linarith [cmp17a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp17a2h_2]) hd
    ·
      exact Kepler.NliBanks22.cell03_core (by linarith [cmp17a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp17a1h_3]) (by linarith) (by linarith [cmp17a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      exact Kepler.NliBanks23.cell11_core (by linarith) (by linarith [cmp17a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp17a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell16_core (by linarith) (by linarith [cmp17a0h_4]) (by linarith) (by linarith [cmp17a1h_3]) (by linarith) (by linarith [cmp17a2h_2]) hd

theorem vD18_0 : ((rowsWt2A (18 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2813159202590, 2813159202590⟩ : DC) := by decide
theorem vF18_0 : ((rowsWt2A (18 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5585533899993606610223650932312011718750 := by rw [vD18_0, vB40_2813159202590]; norm_num
theorem vD18_1 : ((rowsWt2A (18 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF18_1 : ((rowsWt2A (18 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD18_1, vB40_2855549103185]; norm_num
theorem vD18_2 : ((rowsWt2A (18 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF18_2 : ((rowsWt2A (18 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD18_2, vB40_2708646895026]; norm_num
theorem vD18_3 : ((rowsWt2A (18 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF18_3 : ((rowsWt2A (18 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD18_3, vB40_2724177496768]; norm_num
theorem vD18_4 : ((rowsWt2A (18 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF18_4 : ((rowsWt2A (18 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD18_4, vB40_2199023255552]; norm_num
theorem vD18_5 : ((rowsWt2A (18 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF18_5 : ((rowsWt2A (18 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD18_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp18a0l_1 : (63/25:ℝ) ≤ ((rowsWt2A (18 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF18_0]; norm_num
theorem cmp18a1h_2 : ((rowsWt2A (18 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (19821/8000:ℝ) := by rw [vF18_3]; norm_num
theorem cmp18a2h_3 : ((rowsWt2A (18 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF18_5]; norm_num
theorem cmp18a0h_4 : ((rowsWt2A (18 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF18_1]; norm_num
theorem leaf_18_cell19_core : ∀ x ∈ rowBox (rowsWt2A (18 : Fin 62)),
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
  by_cases n0 : x 0 ≤ (255855339/100000000:ℝ)
  ·
    exact Kepler.NliBanks23.cell11_core (by linarith [cmp18a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp18a1h_2]) (by linarith) (by linarith [cmp18a2h_3]) hd
  ·
    exact Kepler.NliBanks23.cell19_core (by linarith) (by linarith [cmp18a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp18a1h_2]) (by linarith) (by linarith [cmp18a2h_3]) hd

theorem vD19_0 : ((rowsWt2A (19 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2813159202590, 2813159202590⟩ : DC) := by decide
theorem vF19_0 : ((rowsWt2A (19 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5585533899993606610223650932312011718750 := by rw [vD19_0, vB40_2813159202590]; norm_num
theorem vD19_1 : ((rowsWt2A (19 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF19_1 : ((rowsWt2A (19 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD19_1, vB40_2855549103185]; norm_num
theorem vD19_2 : ((rowsWt2A (19 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2724177496768, 2724177496768⟩ : DC) := by decide
theorem vF19_2 : ((rowsWt2A (19 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4776249999995343387126922607421875000000 := by rw [vD19_2, vB40_2724177496768]; norm_num
theorem vD19_3 : ((rowsWt2A (19 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF19_3 : ((rowsWt2A (19 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD19_3, vB40_2739708098510]; norm_num
theorem vD19_4 : ((rowsWt2A (19 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF19_4 : ((rowsWt2A (19 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD19_4, vB40_2199023255552]; norm_num
theorem vD19_5 : ((rowsWt2A (19 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF19_5 : ((rowsWt2A (19 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD19_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp19a0l_1 : (63/25:ℝ) ≤ ((rowsWt2A (19 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF19_0]; norm_num
theorem cmp19a2h_2 : ((rowsWt2A (19 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF19_5]; norm_num
theorem cmp19a1h_3 : ((rowsWt2A (19 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF19_3]; norm_num
theorem cmp19a0h_4 : ((rowsWt2A (19 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF19_1]; norm_num
theorem leaf_19_cell21_core : ∀ x ∈ rowBox (rowsWt2A (19 : Fin 62)),
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
  by_cases n0 : x 0 ≤ (255855339/100000000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      exact Kepler.NliBanks23.cell11_core (by linarith [cmp19a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp19a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell16_core (by linarith [cmp19a0l_1]) (by linarith) (by linarith) (by linarith [cmp19a1h_3]) (by linarith) (by linarith [cmp19a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      exact Kepler.NliBanks23.cell19_core (by linarith) (by linarith [cmp19a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp19a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell21_core (by linarith) (by linarith [cmp19a0h_4]) (by linarith) (by linarith [cmp19a1h_3]) (by linarith) (by linarith [cmp19a2h_2]) hd

theorem vD20_0 : ((rowsWt2A (20 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF20_0 : ((rowsWt2A (20 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD20_0, vB40_2770769301995]; norm_num
theorem vD20_1 : ((rowsWt2A (20 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF20_1 : ((rowsWt2A (20 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD20_1, vB40_2855549103185]; norm_num
theorem vD20_2 : ((rowsWt2A (20 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF20_2 : ((rowsWt2A (20 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD20_2, vB40_2739708098510]; norm_num
theorem vD20_3 : ((rowsWt2A (20 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF20_3 : ((rowsWt2A (20 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD20_3, vB40_2770769301995]; norm_num
theorem vD20_4 : ((rowsWt2A (20 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF20_4 : ((rowsWt2A (20 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD20_4, vB40_2199023255552]; norm_num
theorem vD20_5 : ((rowsWt2A (20 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF20_5 : ((rowsWt2A (20 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD20_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp20a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (20 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF20_0]; norm_num
theorem cmp20a2h_2 : ((rowsWt2A (20 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF20_5]; norm_num
theorem cmp20a1h_3 : ((rowsWt2A (20 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF20_3]; norm_num
theorem cmp20a1l_4 : (19821/8000:ℝ) ≤ ((rowsWt2A (20 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF20_2]; norm_num
theorem cmp20a0h_5 : ((rowsWt2A (20 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF20_1]; norm_num
theorem leaf_20_cell02_core : ∀ x ∈ rowBox (rowsWt2A (20 : Fin 62)),
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
        exact Kepler.NliBanks22.cell03_core (by linarith [cmp20a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp20a2h_2]) hd
      ·
        exact Kepler.NliBanks23.cell12_core (by linarith [cmp20a0l_1]) (by linarith) (by linarith) (by linarith [cmp20a1h_3]) (by linarith) (by linarith [cmp20a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        exact Kepler.NliBanks22.cell03_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp20a2h_2]) hd
      ·
        exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith) (by linarith) (by linarith [cmp20a1h_3]) (by linarith) (by linarith [cmp20a2h_2]) hd
  ·
    by_cases n1 : x 0 ≤ (255855339/100000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        exact Kepler.NliBanks23.cell16_core (by linarith) (by linarith) (by linarith [cmp20a1l_4]) (by linarith) (by linarith) (by linarith [cmp20a2h_2]) hd
      ·
        exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith) (by linarith) (by linarith [cmp20a1h_3]) (by linarith) (by linarith [cmp20a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        exact Kepler.NliBanks23.cell21_core (by linarith) (by linarith [cmp20a0h_5]) (by linarith [cmp20a1l_4]) (by linarith) (by linarith) (by linarith [cmp20a2h_2]) hd
      ·
        exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith [cmp20a0h_5]) (by linarith) (by linarith [cmp20a1h_3]) (by linarith) (by linarith [cmp20a2h_2]) hd

theorem vD21_0 : ((rowsWt2A (21 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF21_0 : ((rowsWt2A (21 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD21_0, vB40_2770769301995]; norm_num
theorem vD21_1 : ((rowsWt2A (21 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF21_1 : ((rowsWt2A (21 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD21_1, vB40_2855549103185]; norm_num
theorem vD21_2 : ((rowsWt2A (21 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF21_2 : ((rowsWt2A (21 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD21_2, vB40_2770769301995]; norm_num
theorem vD21_3 : ((rowsWt2A (21 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF21_3 : ((rowsWt2A (21 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD21_3, vB40_2940328904376]; norm_num
theorem vD21_4 : ((rowsWt2A (21 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF21_4 : ((rowsWt2A (21 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD21_4, vB40_2199023255552]; norm_num
theorem vD21_5 : ((rowsWt2A (21 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF21_5 : ((rowsWt2A (21 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD21_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp21a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (21 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF21_0]; norm_num
theorem cmp21a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (21 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF21_2]; norm_num
theorem cmp21a2h_3 : ((rowsWt2A (21 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF21_5]; norm_num
theorem cmp21a1h_4 : ((rowsWt2A (21 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF21_3]; norm_num
theorem cmp21a0h_5 : ((rowsWt2A (21 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF21_1]; norm_num
theorem leaf_21_cell01_core : ∀ x ∈ rowBox (rowsWt2A (21 : Fin 62)),
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
      exact Kepler.NliBanks23.cell12_core (by linarith [cmp21a0l_1]) (by linarith) (by linarith [cmp21a1l_2]) (by linarith) (by linarith) (by linarith [cmp21a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell04_core (by linarith [cmp21a0l_1]) (by linarith) (by linarith) (by linarith [cmp21a1h_4]) (by linarith) (by linarith [cmp21a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      exact Kepler.NliBanks22.cell02_core (by linarith) (by linarith [cmp21a0h_5]) (by linarith [cmp21a1l_2]) (by linarith) (by linarith) (by linarith [cmp21a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell01_core (by linarith) (by linarith [cmp21a0h_5]) (by linarith) (by linarith [cmp21a1h_4]) (by linarith) (by linarith [cmp21a2h_3]) hd

theorem vD22_0 : ((rowsWt2A (22 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF22_0 : ((rowsWt2A (22 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD22_0, vB40_2770769301995]; norm_num
theorem vD22_1 : ((rowsWt2A (22 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF22_1 : ((rowsWt2A (22 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD22_1, vB40_2855549103185]; norm_num
theorem vD22_2 : ((rowsWt2A (22 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF22_2 : ((rowsWt2A (22 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD22_2, vB40_2940328904376]; norm_num
theorem vD22_3 : ((rowsWt2A (22 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF22_3 : ((rowsWt2A (22 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD22_3, vB40_3109888511976]; norm_num
theorem vD22_4 : ((rowsWt2A (22 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF22_4 : ((rowsWt2A (22 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD22_4, vB40_2199023255552]; norm_num
theorem vD22_5 : ((rowsWt2A (22 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF22_5 : ((rowsWt2A (22 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD22_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp22a0l_1 : (20047/8000:ℝ) ≤ ((rowsWt2A (22 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF22_0]; norm_num
theorem cmp22a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (22 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF22_2]; norm_num
theorem cmp22a2h_3 : ((rowsWt2A (22 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF22_5]; norm_num
theorem cmp22a0h_4 : ((rowsWt2A (22 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (129855339/50000000:ℝ) := by rw [vF22_1]; norm_num
theorem leaf_22_cell24_core : ∀ x ∈ rowBox (rowsWt2A (22 : Fin 62)),
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
      exact Kepler.NliBanks22.cell04_core (by linarith [cmp22a0l_1]) (by linarith) (by linarith [cmp22a1l_2]) (by linarith) (by linarith) (by linarith [cmp22a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell28_core (by linarith [cmp22a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp22a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      exact Kepler.NliBanks22.cell01_core (by linarith) (by linarith [cmp22a0h_4]) (by linarith [cmp22a1l_2]) (by linarith) (by linarith) (by linarith [cmp22a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell24_core (by linarith) (by linarith [cmp22a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp22a2h_3]) hd

theorem vD23_0 : ((rowsWt2A (23 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF23_0 : ((rowsWt2A (23 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD23_0, vB40_2855549103185]; norm_num
theorem vD23_1 : ((rowsWt2A (23 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF23_1 : ((rowsWt2A (23 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD23_1, vB40_2940328904376]; norm_num
theorem vD23_2 : ((rowsWt2A (23 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF23_2 : ((rowsWt2A (23 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD23_2, vB40_2708646895026]; norm_num
theorem vD23_3 : ((rowsWt2A (23 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF23_3 : ((rowsWt2A (23 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD23_3, vB40_2739708098510]; norm_num
theorem vD23_4 : ((rowsWt2A (23 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF23_4 : ((rowsWt2A (23 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD23_4, vB40_2199023255552]; norm_num
theorem vD23_5 : ((rowsWt2A (23 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF23_5 : ((rowsWt2A (23 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD23_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp23a0l_1 : (255855339/100000000:ℝ) ≤ ((rowsWt2A (23 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF23_0]; norm_num
theorem cmp23a2h_2 : ((rowsWt2A (23 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF23_5]; norm_num
theorem cmp23a1h_3 : ((rowsWt2A (23 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF23_3]; norm_num
theorem cmp23a0h_4 : ((rowsWt2A (23 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF23_1]; norm_num
theorem leaf_23_cell17_core : ∀ x ∈ rowBox (rowsWt2A (23 : Fin 62)),
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
      exact Kepler.NliBanks23.cell19_core (by linarith [cmp23a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp23a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell21_core (by linarith [cmp23a0l_1]) (by linarith) (by linarith) (by linarith [cmp23a1h_3]) (by linarith) (by linarith [cmp23a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (19821/8000:ℝ)
    ·
      exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith [cmp23a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp23a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith [cmp23a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp23a1h_3]) (by linarith) (by linarith [cmp23a2h_2]) hd

theorem vD24_0 : ((rowsWt2A (24 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF24_0 : ((rowsWt2A (24 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD24_0, vB40_2855549103185]; norm_num
theorem vD24_1 : ((rowsWt2A (24 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF24_1 : ((rowsWt2A (24 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD24_1, vB40_2940328904376]; norm_num
theorem vD24_2 : ((rowsWt2A (24 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF24_2 : ((rowsWt2A (24 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD24_2, vB40_2739708098510]; norm_num
theorem vD24_3 : ((rowsWt2A (24 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF24_3 : ((rowsWt2A (24 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD24_3, vB40_2770769301995]; norm_num
theorem vD24_4 : ((rowsWt2A (24 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF24_4 : ((rowsWt2A (24 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD24_4, vB40_2199023255552]; norm_num
theorem vD24_5 : ((rowsWt2A (24 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF24_5 : ((rowsWt2A (24 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD24_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp24a0l_1 : (255855339/100000000:ℝ) ≤ ((rowsWt2A (24 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF24_0]; norm_num
theorem cmp24a1l_2 : (19821/8000:ℝ) ≤ ((rowsWt2A (24 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF24_2]; norm_num
theorem cmp24a2h_3 : ((rowsWt2A (24 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF24_5]; norm_num
theorem cmp24a0l_4 : (63/25:ℝ) ≤ ((rowsWt2A (24 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF24_0]; norm_num
theorem cmp24a1h_5 : ((rowsWt2A (24 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF24_3]; norm_num
theorem cmp24a0h_6 : ((rowsWt2A (24 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF24_1]; norm_num
theorem leaf_24_cell20_core : ∀ x ∈ rowBox (rowsWt2A (24 : Fin 62)),
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
      exact Kepler.NliBanks23.cell21_core (by linarith [cmp24a0l_1]) (by linarith) (by linarith [cmp24a1l_2]) (by linarith) (by linarith) (by linarith [cmp24a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell02_core (by linarith [cmp24a0l_4]) (by linarith) (by linarith) (by linarith [cmp24a1h_5]) (by linarith) (by linarith [cmp24a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks23.cell17_core (by linarith) (by linarith [cmp24a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp24a2h_3]) hd
    ·
      exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith [cmp24a0h_6]) (by linarith) (by linarith [cmp24a1h_5]) (by linarith) (by linarith [cmp24a2h_3]) hd

theorem vD25_0 : ((rowsWt2A (25 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF25_0 : ((rowsWt2A (25 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD25_0, vB40_2855549103185]; norm_num
theorem vD25_1 : ((rowsWt2A (25 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF25_1 : ((rowsWt2A (25 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD25_1, vB40_2940328904376]; norm_num
theorem vD25_2 : ((rowsWt2A (25 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF25_2 : ((rowsWt2A (25 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD25_2, vB40_2770769301995]; norm_num
theorem vD25_3 : ((rowsWt2A (25 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF25_3 : ((rowsWt2A (25 : Fin 62)).boxHi (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD25_3, vB40_2940328904376]; norm_num
theorem vD25_4 : ((rowsWt2A (25 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF25_4 : ((rowsWt2A (25 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD25_4, vB40_2199023255552]; norm_num
theorem vD25_5 : ((rowsWt2A (25 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF25_5 : ((rowsWt2A (25 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD25_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp25a0l_1 : (63/25:ℝ) ≤ ((rowsWt2A (25 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF25_0]; norm_num
theorem cmp25a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (25 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF25_2]; norm_num
theorem cmp25a2h_3 : ((rowsWt2A (25 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF25_5]; norm_num
theorem cmp25a1h_4 : ((rowsWt2A (25 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF25_3]; norm_num
theorem cmp25a0h_5 : ((rowsWt2A (25 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF25_1]; norm_num
theorem leaf_25_cell18_core : ∀ x ∈ rowBox (rowsWt2A (25 : Fin 62)),
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
      exact Kepler.NliBanks22.cell02_core (by linarith [cmp25a0l_1]) (by linarith) (by linarith [cmp25a1l_2]) (by linarith) (by linarith) (by linarith [cmp25a2h_3]) hd
    ·
      exact Kepler.NliBanks22.cell01_core (by linarith [cmp25a0l_1]) (by linarith) (by linarith) (by linarith [cmp25a1h_4]) (by linarith) (by linarith [cmp25a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith [cmp25a0h_5]) (by linarith [cmp25a1l_2]) (by linarith) (by linarith) (by linarith [cmp25a2h_3]) hd
    ·
      exact Kepler.NliBanks23.cell18_core (by linarith) (by linarith [cmp25a0h_5]) (by linarith) (by linarith [cmp25a1h_4]) (by linarith) (by linarith [cmp25a2h_3]) hd

theorem vD26_0 : ((rowsWt2A (26 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2855549103185, 2855549103185⟩ : DC) := by decide
theorem vF26_0 : ((rowsWt2A (26 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5971067799991942592896521091461181640625 := by rw [vD26_0, vB40_2855549103185]; norm_num
theorem vD26_1 : ((rowsWt2A (26 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF26_1 : ((rowsWt2A (26 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD26_1, vB40_2940328904376]; norm_num
theorem vD26_2 : ((rowsWt2A (26 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF26_2 : ((rowsWt2A (26 : Fin 62)).boxLo (1 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD26_2, vB40_2940328904376]; norm_num
theorem vD26_3 : ((rowsWt2A (26 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF26_3 : ((rowsWt2A (26 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD26_3, vB40_3109888511976]; norm_num
theorem vD26_4 : ((rowsWt2A (26 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF26_4 : ((rowsWt2A (26 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD26_4, vB40_2199023255552]; norm_num
theorem vD26_5 : ((rowsWt2A (26 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF26_5 : ((rowsWt2A (26 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD26_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp26a0l_1 : (63/25:ℝ) ≤ ((rowsWt2A (26 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF26_0]; norm_num
theorem cmp26a1l_2 : (63/25:ℝ) ≤ ((rowsWt2A (26 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF26_2]; norm_num
theorem cmp26a2h_3 : ((rowsWt2A (26 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF26_5]; norm_num
theorem cmp26a0h_4 : ((rowsWt2A (26 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF26_1]; norm_num
theorem leaf_26_cell29_vac : ∀ x ∈ rowBox (rowsWt2A (26 : Fin 62)),
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
      exact Kepler.NliBanks22.cell01_core (by linarith [cmp26a0l_1]) (by linarith) (by linarith [cmp26a1l_2]) (by linarith) (by linarith) (by linarith [cmp26a2h_3]) hd
    ·
      exact Kepler.NliBanks24.cell24_core (by linarith [cmp26a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp26a2h_3]) hd
  ·
    by_cases n1 : x 1 ≤ (66855339/25000000:ℝ)
    ·
      exact Kepler.NliBanks23.cell18_core (by linarith) (by linarith [cmp26a0h_4]) (by linarith [cmp26a1l_2]) (by linarith) (by linarith) (by linarith [cmp26a2h_3]) hd
    ·
      exact ((Kepler.NliBanks24.cell29_vac (by linarith) (by linarith [cmp26a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp26a2h_3])) hd).elim

theorem vD27_0 : ((rowsWt2A (27 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF27_0 : ((rowsWt2A (27 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD27_0, vB40_2940328904376]; norm_num
theorem vD27_1 : ((rowsWt2A (27 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3025108705566, 3025108705566⟩ : DC) := by decide
theorem vF27_1 : ((rowsWt2A (27 : Fin 62)).boxHi (0 : Fin 3)).value = 2.7513203399994381470605731010437011718750 := by rw [vD27_1, vB40_3025108705566]; norm_num
theorem vD27_2 : ((rowsWt2A (27 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF27_2 : ((rowsWt2A (27 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD27_2, vB40_2708646895026]; norm_num
theorem vD27_3 : ((rowsWt2A (27 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF27_3 : ((rowsWt2A (27 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD27_3, vB40_2739708098510]; norm_num
theorem vD27_4 : ((rowsWt2A (27 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF27_4 : ((rowsWt2A (27 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD27_4, vB40_2199023255552]; norm_num
theorem vD27_5 : ((rowsWt2A (27 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF27_5 : ((rowsWt2A (27 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD27_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp27a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (27 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF27_0]; norm_num
theorem cmp27a1h_2 : ((rowsWt2A (27 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF27_3]; norm_num
theorem cmp27a2h_3 : ((rowsWt2A (27 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF27_5]; norm_num
theorem cmp27a0h_4 : ((rowsWt2A (27 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (137566017/50000000:ℝ) := by rw [vF27_1]; norm_num
theorem leaf_27_cell22_core : ∀ x ∈ rowBox (rowsWt2A (27 : Fin 62)),
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
    exact Kepler.NliBanks23.cell17_core (by linarith [cmp27a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp27a1h_2]) (by linarith) (by linarith [cmp27a2h_3]) hd
  ·
    exact Kepler.NliBanks24.cell22_core (by linarith) (by linarith [cmp27a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp27a1h_2]) (by linarith) (by linarith [cmp27a2h_3]) hd

theorem vD28_0 : ((rowsWt2A (28 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 3025108705566, 3025108705566⟩ : DC) := by decide
theorem vF28_0 : ((rowsWt2A (28 : Fin 62)).boxLo (0 : Fin 3)).value = 2.7513203399994381470605731010437011718750 := by rw [vD28_0, vB40_3025108705566]; norm_num
theorem vD28_1 : ((rowsWt2A (28 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF28_1 : ((rowsWt2A (28 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD28_1, vB40_3109888511976]; norm_num
theorem vD28_2 : ((rowsWt2A (28 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF28_2 : ((rowsWt2A (28 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD28_2, vB40_2708646895026]; norm_num
theorem vD28_3 : ((rowsWt2A (28 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF28_3 : ((rowsWt2A (28 : Fin 62)).boxHi (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD28_3, vB40_2739708098510]; norm_num
theorem vD28_4 : ((rowsWt2A (28 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF28_4 : ((rowsWt2A (28 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD28_4, vB40_2199023255552]; norm_num
theorem vD28_5 : ((rowsWt2A (28 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF28_5 : ((rowsWt2A (28 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD28_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp28a0l_1 : (66855339/25000000:ℝ) ≤ ((rowsWt2A (28 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF28_0]; norm_num
theorem cmp28a1h_2 : ((rowsWt2A (28 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF28_3]; norm_num
theorem cmp28a2h_3 : ((rowsWt2A (28 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF28_5]; norm_num
theorem leaf_28_cell_vac_demo : ∀ x ∈ rowBox (rowsWt2A (28 : Fin 62)),
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
  by_cases n0 : x 0 ≤ (137566017/50000000:ℝ)
  ·
    exact Kepler.NliBanks24.cell22_core (by linarith [cmp28a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp28a1h_2]) (by linarith) (by linarith [cmp28a2h_3]) hd
  ·
    exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp28a2h_3])) hd).elim

theorem vD29_0 : ((rowsWt2A (29 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF29_0 : ((rowsWt2A (29 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD29_0, vB40_2940328904376]; norm_num
theorem vD29_1 : ((rowsWt2A (29 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3025108705566, 3025108705566⟩ : DC) := by decide
theorem vF29_1 : ((rowsWt2A (29 : Fin 62)).boxHi (0 : Fin 3)).value = 2.7513203399994381470605731010437011718750 := by rw [vD29_1, vB40_3025108705566]; norm_num
theorem vD29_2 : ((rowsWt2A (29 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF29_2 : ((rowsWt2A (29 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD29_2, vB40_2739708098510]; norm_num
theorem vD29_3 : ((rowsWt2A (29 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF29_3 : ((rowsWt2A (29 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD29_3, vB40_2770769301995]; norm_num
theorem vD29_4 : ((rowsWt2A (29 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF29_4 : ((rowsWt2A (29 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD29_4, vB40_2199023255552]; norm_num
theorem vD29_5 : ((rowsWt2A (29 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF29_5 : ((rowsWt2A (29 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD29_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp29a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (29 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF29_0]; norm_num
theorem cmp29a2h_2 : ((rowsWt2A (29 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF29_5]; norm_num
theorem cmp29a1h_3 : ((rowsWt2A (29 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF29_3]; norm_num
theorem cmp29a0h_4 : ((rowsWt2A (29 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (137566017/50000000:ℝ) := by rw [vF29_1]; norm_num
theorem leaf_29_cell23_core : ∀ x ∈ rowBox (rowsWt2A (29 : Fin 62)),
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
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks23.cell17_core (by linarith [cmp29a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp29a2h_2]) hd
    ·
      exact Kepler.NliBanks23.cell20_core (by linarith [cmp29a0l_1]) (by linarith) (by linarith) (by linarith [cmp29a1h_3]) (by linarith) (by linarith [cmp29a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks24.cell22_core (by linarith) (by linarith [cmp29a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp29a2h_2]) hd
    ·
      exact Kepler.NliBanks24.cell23_core (by linarith) (by linarith [cmp29a0h_4]) (by linarith) (by linarith [cmp29a1h_3]) (by linarith) (by linarith [cmp29a2h_2]) hd

theorem vD30_0 : ((rowsWt2A (30 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 3025108705566, 3025108705566⟩ : DC) := by decide
theorem vF30_0 : ((rowsWt2A (30 : Fin 62)).boxLo (0 : Fin 3)).value = 2.7513203399994381470605731010437011718750 := by rw [vD30_0, vB40_3025108705566]; norm_num
theorem vD30_1 : ((rowsWt2A (30 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF30_1 : ((rowsWt2A (30 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD30_1, vB40_3109888511976]; norm_num
theorem vD30_2 : ((rowsWt2A (30 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF30_2 : ((rowsWt2A (30 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD30_2, vB40_2739708098510]; norm_num
theorem vD30_3 : ((rowsWt2A (30 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF30_3 : ((rowsWt2A (30 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD30_3, vB40_2770769301995]; norm_num
theorem vD30_4 : ((rowsWt2A (30 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF30_4 : ((rowsWt2A (30 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD30_4, vB40_2199023255552]; norm_num
theorem vD30_5 : ((rowsWt2A (30 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF30_5 : ((rowsWt2A (30 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD30_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp30a0l_1 : (66855339/25000000:ℝ) ≤ ((rowsWt2A (30 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF30_0]; norm_num
theorem cmp30a2h_2 : ((rowsWt2A (30 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF30_5]; norm_num
theorem cmp30a1h_3 : ((rowsWt2A (30 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF30_3]; norm_num
theorem leaf_30_cell31_vac : ∀ x ∈ rowBox (rowsWt2A (30 : Fin 62)),
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
  by_cases n0 : x 0 ≤ (137566017/50000000:ℝ)
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact Kepler.NliBanks24.cell22_core (by linarith [cmp30a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp30a2h_2]) hd
    ·
      exact Kepler.NliBanks24.cell23_core (by linarith [cmp30a0l_1]) (by linarith) (by linarith) (by linarith [cmp30a1h_3]) (by linarith) (by linarith [cmp30a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp30a2h_2])) hd).elim
    ·
      exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp30a2h_2])) hd).elim

theorem vD31_0 : ((rowsWt2A (31 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF31_0 : ((rowsWt2A (31 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD31_0, vB40_2940328904376]; norm_num
theorem vD31_1 : ((rowsWt2A (31 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF31_1 : ((rowsWt2A (31 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD31_1, vB40_3109888511976]; norm_num
theorem vD31_2 : ((rowsWt2A (31 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF31_2 : ((rowsWt2A (31 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD31_2, vB40_2770769301995]; norm_num
theorem vD31_3 : ((rowsWt2A (31 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF31_3 : ((rowsWt2A (31 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD31_3, vB40_3109888511976]; norm_num
theorem vD31_4 : ((rowsWt2A (31 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF31_4 : ((rowsWt2A (31 : Fin 62)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD31_4, vB40_2199023255552]; norm_num
theorem vD31_5 : ((rowsWt2A (31 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2262794929963, 2262794929963⟩ : DC) := by decide
theorem vF31_5 : ((rowsWt2A (31 : Fin 62)).boxHi (2 : Fin 3)).value = 2.0579999999999927240423858165740966796875 := by rw [vD31_5, vB40_2262794929963]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp31a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (31 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF31_0]; norm_num
theorem cmp31a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (31 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF31_2]; norm_num
theorem cmp31a2h_3 : ((rowsWt2A (31 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (1029/500:ℝ) := by rw [vF31_5]; norm_num
theorem leaf_31_cell00_core : ∀ x ∈ rowBox (rowsWt2A (31 : Fin 62)),
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
          exact Kepler.NliBanks23.cell20_core (by linarith [cmp31a0l_1]) (by linarith) (by linarith [cmp31a1l_2]) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact Kepler.NliBanks23.cell18_core (by linarith [cmp31a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact Kepler.NliBanks23.cell18_core (by linarith [cmp31a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact ((Kepler.NliBanks24.cell29_vac (by linarith [cmp31a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3])) hd).elim
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact Kepler.NliBanks23.cell20_core (by linarith) (by linarith) (by linarith [cmp31a1l_2]) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
  ·
    by_cases n1 : x 0 ≤ (137566017/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact Kepler.NliBanks24.cell23_core (by linarith) (by linarith) (by linarith [cmp31a1l_2]) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact ((Kepler.NliBanks20.cell_vac_demo (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp31a2h_3])) hd).elim
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd
        ·
          exact Kepler.NliBanks20.cell00_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp31a2h_3]) hd

end Kepler.NliKit.BoxTreeWt2A

