/-
Kepler.NliKit.BoxTreeWt2AS3 — leaf witnesses, shard 3 of the
wt2A tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeWt2ARows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeWt2A

open Kepler.NliKit.BoxTree

theorem vD60_0 : ((rowsWt2A (60 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF60_0 : ((rowsWt2A (60 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD60_0, vB40_2708646895026]; norm_num
theorem vD60_1 : ((rowsWt2A (60 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF60_1 : ((rowsWt2A (60 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD60_1, vB40_2770769301995]; norm_num
theorem vD60_2 : ((rowsWt2A (60 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF60_2 : ((rowsWt2A (60 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD60_2, vB40_2708646895026]; norm_num
theorem vD60_3 : ((rowsWt2A (60 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF60_3 : ((rowsWt2A (60 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD60_3, vB40_3109888511976]; norm_num
theorem vD60_4 : ((rowsWt2A (60 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF60_4 : ((rowsWt2A (60 : Fin 62)).boxLo (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD60_4, vB40_2580553790390]; norm_num
theorem vD60_5 : ((rowsWt2A (60 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem vF60_5 : ((rowsWt2A (60 : Fin 62)).boxHi (2 : Fin 3)).value = 2.4635200000002441811375319957733154296875 := by rw [vD60_5, vB40_2708668885259]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp60a2l_1 : (1087/500:ℝ) ≤ ((rowsWt2A (60 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF60_4]; norm_num
theorem cmp60a0h_2 : ((rowsWt2A (60 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF60_1]; norm_num
theorem leaf_60_cell61_core : ∀ x ∈ rowBox (rowsWt2A (60 : Fin 62)),
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
      by_cases n2 : x 2 ≤ (2347/1000:ℝ)
      ·
        exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp60a2l_1]) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell61_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) hd
    ·
      by_cases n2 : x 2 ≤ (2347/1000:ℝ)
      ·
        exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp60a2l_1]) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell61_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 2 ≤ (2347/1000:ℝ)
      ·
        exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith [cmp60a0h_2]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp60a2l_1]) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell61_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp60a0h_2]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) hd
    ·
      by_cases n2 : x 2 ≤ (2347/1000:ℝ)
      ·
        exact Kepler.NliBanks26.cell57_core (by linarith) (by linarith [cmp60a0h_2]) (by linarith) (by linarith) (by linarith [cmp60a2l_1]) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell61_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp60a0h_2]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) hd

end Kepler.NliKit.BoxTreeWt2A

