/-
Kepler.NliKit.BoxTreeWt2AS2 — leaf witnesses, shard 2 of the
wt2A tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeWt2ARows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeWt2A

open Kepler.NliKit.BoxTree

theorem vD52_0 : ((rowsWt2A (52 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF52_0 : ((rowsWt2A (52 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD52_0, vB40_2708646895026]; norm_num
theorem vD52_1 : ((rowsWt2A (52 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF52_1 : ((rowsWt2A (52 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD52_1, vB40_2739708098510]; norm_num
theorem vD52_2 : ((rowsWt2A (52 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF52_2 : ((rowsWt2A (52 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD52_2, vB40_2708646895026]; norm_num
theorem vD52_3 : ((rowsWt2A (52 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF52_3 : ((rowsWt2A (52 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD52_3, vB40_2770769301995]; norm_num
theorem vD52_4 : ((rowsWt2A (52 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF52_4 : ((rowsWt2A (52 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD52_4, vB40_2390338278785]; norm_num
theorem vD52_5 : ((rowsWt2A (52 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF52_5 : ((rowsWt2A (52 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD52_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp52a0h_1 : ((rowsWt2A (52 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF52_1]; norm_num
theorem cmp52a1h_2 : ((rowsWt2A (52 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF52_3]; norm_num
theorem cmp52a2l_3 : (1029/500:ℝ) ≤ ((rowsWt2A (52 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF52_4]; norm_num
theorem cmp52a2h_4 : ((rowsWt2A (52 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF52_5]; norm_num
theorem leaf_52_cell54_core : ∀ x ∈ rowBox (rowsWt2A (52 : Fin 62)),
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
  by_cases n0 : x 2 ≤ (1087/500:ℝ)
  ·
    exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp52a0h_1]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp52a1h_2]) (by linarith [cmp52a2l_3]) (by linarith) hd
  ·
    exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp52a0h_1]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp52a1h_2]) (by linarith) (by linarith [cmp52a2h_4]) hd

theorem vD53_0 : ((rowsWt2A (53 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF53_0 : ((rowsWt2A (53 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD53_0, vB40_2708646895026]; norm_num
theorem vD53_1 : ((rowsWt2A (53 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF53_1 : ((rowsWt2A (53 : Fin 62)).boxHi (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD53_1, vB40_2739708098510]; norm_num
theorem vD53_2 : ((rowsWt2A (53 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF53_2 : ((rowsWt2A (53 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD53_2, vB40_2770769301995]; norm_num
theorem vD53_3 : ((rowsWt2A (53 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF53_3 : ((rowsWt2A (53 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD53_3, vB40_3109888511976]; norm_num
theorem vD53_4 : ((rowsWt2A (53 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF53_4 : ((rowsWt2A (53 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD53_4, vB40_2390338278785]; norm_num
theorem vD53_5 : ((rowsWt2A (53 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF53_5 : ((rowsWt2A (53 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD53_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp53a2l_1 : (1029/500:ℝ) ≤ ((rowsWt2A (53 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF53_4]; norm_num
theorem cmp53a2h_2 : ((rowsWt2A (53 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF53_5]; norm_num
theorem cmp53a0h_3 : ((rowsWt2A (53 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (9967/4000:ℝ) := by rw [vF53_1]; norm_num
theorem leaf_53_cell55_core : ∀ x ∈ rowBox (rowsWt2A (53 : Fin 62)),
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
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell38_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell45_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp53a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp53a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp53a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp53a0h_3]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell39_core (by linarith) (by linarith [cmp53a0h_3]) (by linarith) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp53a0h_3]) (by linarith) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell46_core (by linarith) (by linarith [cmp53a0h_3]) (by linarith) (by linarith) (by linarith [cmp53a2l_1]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp53a0h_3]) (by linarith) (by linarith) (by linarith) (by linarith [cmp53a2h_2]) hd

theorem vD54_0 : ((rowsWt2A (54 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF54_0 : ((rowsWt2A (54 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD54_0, vB40_2739708098510]; norm_num
theorem vD54_1 : ((rowsWt2A (54 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF54_1 : ((rowsWt2A (54 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD54_1, vB40_2770769301995]; norm_num
theorem vD54_2 : ((rowsWt2A (54 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF54_2 : ((rowsWt2A (54 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD54_2, vB40_2708646895026]; norm_num
theorem vD54_3 : ((rowsWt2A (54 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF54_3 : ((rowsWt2A (54 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD54_3, vB40_2770769301995]; norm_num
theorem vD54_4 : ((rowsWt2A (54 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF54_4 : ((rowsWt2A (54 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD54_4, vB40_2390338278785]; norm_num
theorem vD54_5 : ((rowsWt2A (54 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF54_5 : ((rowsWt2A (54 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD54_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp54a1h_1 : ((rowsWt2A (54 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF54_3]; norm_num
theorem cmp54a2l_2 : (1029/500:ℝ) ≤ ((rowsWt2A (54 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF54_4]; norm_num
theorem cmp54a2h_3 : ((rowsWt2A (54 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF54_5]; norm_num
theorem cmp54a0h_4 : ((rowsWt2A (54 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF54_1]; norm_num
theorem leaf_54_cell56_core : ∀ x ∈ rowBox (rowsWt2A (54 : Fin 62)),
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
    by_cases n1 : x 2 ≤ (1087/500:ℝ)
    ·
      exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp54a1h_1]) (by linarith [cmp54a2l_2]) (by linarith) hd
    ·
      exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp54a1h_1]) (by linarith) (by linarith [cmp54a2h_3]) hd
  ·
    by_cases n1 : x 2 ≤ (1087/500:ℝ)
    ·
      exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp54a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp54a1h_1]) (by linarith [cmp54a2l_2]) (by linarith) hd
    ·
      exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith [cmp54a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp54a1h_1]) (by linarith) (by linarith [cmp54a2h_3]) hd

theorem vD55_0 : ((rowsWt2A (55 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2739708098510, 2739708098510⟩ : DC) := by decide
theorem vF55_0 : ((rowsWt2A (55 : Fin 62)).boxLo (0 : Fin 3)).value = 2.4917499999992287484928965568542480468750 := by rw [vD55_0, vB40_2739708098510]; norm_num
theorem vD55_1 : ((rowsWt2A (55 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF55_1 : ((rowsWt2A (55 : Fin 62)).boxHi (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD55_1, vB40_2770769301995]; norm_num
theorem vD55_2 : ((rowsWt2A (55 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF55_2 : ((rowsWt2A (55 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD55_2, vB40_2770769301995]; norm_num
theorem vD55_3 : ((rowsWt2A (55 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF55_3 : ((rowsWt2A (55 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD55_3, vB40_3109888511976]; norm_num
theorem vD55_4 : ((rowsWt2A (55 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF55_4 : ((rowsWt2A (55 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD55_4, vB40_2390338278785]; norm_num
theorem vD55_5 : ((rowsWt2A (55 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF55_5 : ((rowsWt2A (55 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD55_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp55a2l_1 : (1029/500:ℝ) ≤ ((rowsWt2A (55 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF55_4]; norm_num
theorem cmp55a2h_2 : ((rowsWt2A (55 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF55_5]; norm_num
theorem cmp55a0l_3 : (19821/8000:ℝ) ≤ ((rowsWt2A (55 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF55_0]; norm_num
theorem cmp55a0h_4 : ((rowsWt2A (55 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF55_1]; norm_num
theorem leaf_55_cell57_core : ∀ x ∈ rowBox (rowsWt2A (55 : Fin 62)),
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
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell33_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell39_core (by linarith [cmp55a0l_3]) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell46_core (by linarith [cmp55a0l_3]) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell54_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell39_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell46_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell55_core (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
  ·
    by_cases n1 : x 0 ≤ (20047/8000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell40_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell57_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell47_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell57_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell56_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell41_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell57_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact ((Kepler.NliBanks25.cell51_vac (by linarith) (by linarith [cmp55a0h_4]) (by linarith) (by linarith) (by linarith [cmp55a2l_1]) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks26.cell57_core (by linarith) (by linarith [cmp55a0h_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp55a2h_2]) hd

theorem vD56_0 : ((rowsWt2A (56 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF56_0 : ((rowsWt2A (56 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD56_0, vB40_2770769301995]; norm_num
theorem vD56_1 : ((rowsWt2A (56 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF56_1 : ((rowsWt2A (56 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD56_1, vB40_2940328904376]; norm_num
theorem vD56_2 : ((rowsWt2A (56 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF56_2 : ((rowsWt2A (56 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD56_2, vB40_2708646895026]; norm_num
theorem vD56_3 : ((rowsWt2A (56 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF56_3 : ((rowsWt2A (56 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD56_3, vB40_2770769301995]; norm_num
theorem vD56_4 : ((rowsWt2A (56 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF56_4 : ((rowsWt2A (56 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD56_4, vB40_2390338278785]; norm_num
theorem vD56_5 : ((rowsWt2A (56 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF56_5 : ((rowsWt2A (56 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD56_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp56a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (56 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF56_0]; norm_num
theorem cmp56a2l_2 : (1029/500:ℝ) ≤ ((rowsWt2A (56 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF56_4]; norm_num
theorem cmp56a2h_3 : ((rowsWt2A (56 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF56_5]; norm_num
theorem cmp56a1h_4 : ((rowsWt2A (56 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF56_3]; norm_num
theorem cmp56a0h_5 : ((rowsWt2A (56 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF56_1]; norm_num
theorem leaf_56_cell52_core : ∀ x ∈ rowBox (rowsWt2A (56 : Fin 62)),
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
    by_cases n1 : x 0 ≤ (129855339/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith [cmp56a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell56_core (by linarith [cmp56a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp56a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith [cmp56a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp56a1h_4]) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell56_core (by linarith [cmp56a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp56a1h_4]) (by linarith) (by linarith [cmp56a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp56a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp56a1h_4]) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp56a1h_4]) (by linarith) (by linarith [cmp56a2h_3]) hd
  ·
    by_cases n1 : x 0 ≤ (129855339/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell34_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp56a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell37_core (by linarith) (by linarith) (by linarith) (by linarith [cmp56a1h_4]) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp56a1h_4]) (by linarith) (by linarith [cmp56a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (9967/4000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell42_core (by linarith) (by linarith [cmp56a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith [cmp56a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp56a2h_3]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell43_core (by linarith) (by linarith [cmp56a0h_5]) (by linarith) (by linarith [cmp56a1h_4]) (by linarith [cmp56a2l_2]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith [cmp56a0h_5]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp56a1h_4]) (by linarith) (by linarith [cmp56a2h_3]) hd

theorem vD57_0 : ((rowsWt2A (57 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF57_0 : ((rowsWt2A (57 : Fin 62)).boxLo (0 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD57_0, vB40_2770769301995]; norm_num
theorem vD57_1 : ((rowsWt2A (57 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF57_1 : ((rowsWt2A (57 : Fin 62)).boxHi (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD57_1, vB40_2940328904376]; norm_num
theorem vD57_2 : ((rowsWt2A (57 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF57_2 : ((rowsWt2A (57 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD57_2, vB40_2770769301995]; norm_num
theorem vD57_3 : ((rowsWt2A (57 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF57_3 : ((rowsWt2A (57 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD57_3, vB40_3109888511976]; norm_num
theorem vD57_4 : ((rowsWt2A (57 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF57_4 : ((rowsWt2A (57 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD57_4, vB40_2390338278785]; norm_num
theorem vD57_5 : ((rowsWt2A (57 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF57_5 : ((rowsWt2A (57 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD57_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp57a0l_1 : (9967/4000:ℝ) ≤ ((rowsWt2A (57 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF57_0]; norm_num
theorem cmp57a2l_2 : (1029/500:ℝ) ≤ ((rowsWt2A (57 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF57_4]; norm_num
theorem cmp57a2h_3 : ((rowsWt2A (57 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF57_5]; norm_num
theorem cmp57a0l_4 : (20047/8000:ℝ) ≤ ((rowsWt2A (57 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF57_0]; norm_num
theorem cmp57a1l_5 : (9967/4000:ℝ) ≤ ((rowsWt2A (57 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF57_2]; norm_num
theorem cmp57a0h_6 : ((rowsWt2A (57 : Fin 62)).boxHi (0 : Fin 3)).value ≤ (66855339/25000000:ℝ) := by rw [vF57_1]; norm_num
theorem leaf_57_cell53_core : ∀ x ∈ rowBox (rowsWt2A (57 : Fin 62)),
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
    by_cases n1 : x 0 ≤ (129855339/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith [cmp57a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell56_core (by linarith [cmp57a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith [cmp57a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell56_core (by linarith [cmp57a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell41_core (by linarith [cmp57a0l_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell57_core (by linarith [cmp57a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact ((Kepler.NliBanks25.cell51_vac (by linarith [cmp57a0l_4]) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks26.cell57_core (by linarith [cmp57a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell32_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell36_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact ((Kepler.NliBanks25.cell49_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
  ·
    by_cases n1 : x 0 ≤ (129855339/50000000:ℝ)
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell37_core (by linarith) (by linarith) (by linarith [cmp57a1l_5]) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell36_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell36_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact ((Kepler.NliBanks25.cell49_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
    ·
      by_cases n2 : x 1 ≤ (63/25:ℝ)
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell43_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith [cmp57a1l_5]) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell43_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell52_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
      ·
        by_cases n3 : x 1 ≤ (66855339/25000000:ℝ)
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact Kepler.NliBanks25.cell44_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith) hd
          ·
            exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd
        ·
          by_cases n4 : x 2 ≤ (1087/500:ℝ)
          ·
            exact ((Kepler.NliBanks25.cell50_vac (by linarith) (by linarith [cmp57a0h_6]) (by linarith) (by linarith) (by linarith [cmp57a2l_2]) (by linarith)) hd).elim
          ·
            exact Kepler.NliBanks26.cell53_core (by linarith) (by linarith [cmp57a0h_6]) (by linarith) (by linarith) (by linarith) (by linarith [cmp57a2h_3]) hd

theorem vD58_0 : ((rowsWt2A (58 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF58_0 : ((rowsWt2A (58 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD58_0, vB40_2940328904376]; norm_num
theorem vD58_1 : ((rowsWt2A (58 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF58_1 : ((rowsWt2A (58 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD58_1, vB40_3109888511976]; norm_num
theorem vD58_2 : ((rowsWt2A (58 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2708646895026, 2708646895026⟩ : DC) := by decide
theorem vF58_2 : ((rowsWt2A (58 : Fin 62)).boxLo (1 : Fin 3)).value = 2.4634999999998399289324879646301269531250 := by rw [vD58_2, vB40_2708646895026]; norm_num
theorem vD58_3 : ((rowsWt2A (58 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF58_3 : ((rowsWt2A (58 : Fin 62)).boxHi (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD58_3, vB40_2770769301995]; norm_num
theorem vD58_4 : ((rowsWt2A (58 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF58_4 : ((rowsWt2A (58 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD58_4, vB40_2390338278785]; norm_num
theorem vD58_5 : ((rowsWt2A (58 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF58_5 : ((rowsWt2A (58 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD58_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp58a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (58 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF58_0]; norm_num
theorem cmp58a2l_2 : (1029/500:ℝ) ≤ ((rowsWt2A (58 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF58_4]; norm_num
theorem cmp58a0l_3 : (63/25:ℝ) ≤ ((rowsWt2A (58 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF58_0]; norm_num
theorem cmp58a2h_4 : ((rowsWt2A (58 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF58_5]; norm_num
theorem cmp58a1h_5 : ((rowsWt2A (58 : Fin 62)).boxHi (1 : Fin 3)).value ≤ (63/25:ℝ) := by rw [vF58_3]; norm_num
theorem leaf_58_cell58_vac : ∀ x ∈ rowBox (rowsWt2A (58 : Fin 62)),
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
      by_cases n2 : x 2 ≤ (1087/500:ℝ)
      ·
        exact Kepler.NliBanks25.cell42_core (by linarith [cmp58a0l_1]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp58a2l_2]) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell52_core (by linarith [cmp58a0l_3]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp58a2h_4]) hd
    ·
      by_cases n2 : x 2 ≤ (1087/500:ℝ)
      ·
        exact Kepler.NliBanks25.cell43_core (by linarith [cmp58a0l_1]) (by linarith) (by linarith) (by linarith [cmp58a1h_5]) (by linarith [cmp58a2l_2]) (by linarith) hd
      ·
        exact Kepler.NliBanks26.cell52_core (by linarith [cmp58a0l_3]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp58a1h_5]) (by linarith) (by linarith [cmp58a2h_4]) hd
  ·
    by_cases n1 : x 1 ≤ (9967/4000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (1087/500:ℝ)
      ·
        exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp58a2l_2]) (by linarith) hd
      ·
        exact ((Kepler.NliBanks26.cell58_vac (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp58a2h_4])) hd).elim
    ·
      by_cases n2 : x 2 ≤ (1087/500:ℝ)
      ·
        exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp58a1h_5]) (by linarith [cmp58a2l_2]) (by linarith) hd
      ·
        exact ((Kepler.NliBanks26.cell58_vac (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith [cmp58a1h_5]) (by linarith) (by linarith [cmp58a2h_4])) hd).elim

theorem vD59_0 : ((rowsWt2A (59 : Fin 62)).boxLo (0 : Fin 3)) = (⟨40, 2940328904376, 2940328904376⟩ : DC) := by decide
theorem vF59_0 : ((rowsWt2A (59 : Fin 62)).boxLo (0 : Fin 3)).value = 2.6742135599997709505259990692138671875000 := by rw [vD59_0, vB40_2940328904376]; norm_num
theorem vD59_1 : ((rowsWt2A (59 : Fin 62)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF59_1 : ((rowsWt2A (59 : Fin 62)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD59_1, vB40_3109888511976]; norm_num
theorem vD59_2 : ((rowsWt2A (59 : Fin 62)).boxLo (1 : Fin 3)) = (⟨40, 2770769301995, 2770769301995⟩ : DC) := by decide
theorem vF59_2 : ((rowsWt2A (59 : Fin 62)).boxLo (1 : Fin 3)).value = 2.5199999999995270627550780773162841796875 := by rw [vD59_2, vB40_2770769301995]; norm_num
theorem vD59_3 : ((rowsWt2A (59 : Fin 62)).boxHi (1 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF59_3 : ((rowsWt2A (59 : Fin 62)).boxHi (1 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD59_3, vB40_3109888511976]; norm_num
theorem vD59_4 : ((rowsWt2A (59 : Fin 62)).boxLo (2 : Fin 3)) = (⟨40, 2390338278785, 2390338278785⟩ : DC) := by decide
theorem vF59_4 : ((rowsWt2A (59 : Fin 62)).boxLo (2 : Fin 3)).value = 2.1739999999999781721271574497222900390625 := by rw [vD59_4, vB40_2390338278785]; norm_num
theorem vD59_5 : ((rowsWt2A (59 : Fin 62)).boxHi (2 : Fin 3)) = (⟨40, 2580553790390, 2580553790390⟩ : DC) := by decide
theorem vF59_5 : ((rowsWt2A (59 : Fin 62)).boxHi (2 : Fin 3)).value = 2.3469999999997526174411177635192871093750 := by rw [vD59_5, vB40_2580553790390]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp59a0l_1 : (129855339/50000000:ℝ) ≤ ((rowsWt2A (59 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF59_0]; norm_num
theorem cmp59a1l_2 : (9967/4000:ℝ) ≤ ((rowsWt2A (59 : Fin 62)).boxLo (1 : Fin 3)).value := by rw [vF59_2]; norm_num
theorem cmp59a2l_3 : (1029/500:ℝ) ≤ ((rowsWt2A (59 : Fin 62)).boxLo (2 : Fin 3)).value := by rw [vF59_4]; norm_num
theorem cmp59a0l_4 : (63/25:ℝ) ≤ ((rowsWt2A (59 : Fin 62)).boxLo (0 : Fin 3)).value := by rw [vF59_0]; norm_num
theorem cmp59a2h_5 : ((rowsWt2A (59 : Fin 62)).boxHi (2 : Fin 3)).value ≤ (2347/1000:ℝ) := by rw [vF59_5]; norm_num
theorem leaf_59_cell59_vac : ∀ x ∈ rowBox (rowsWt2A (59 : Fin 62)),
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
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell43_core (by linarith [cmp59a0l_1]) (by linarith) (by linarith [cmp59a1l_2]) (by linarith) (by linarith [cmp59a2l_3]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith [cmp59a0l_4]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp59a2h_5]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell43_core (by linarith [cmp59a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2l_3]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell52_core (by linarith [cmp59a0l_4]) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp59a2h_5]) hd
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell44_core (by linarith [cmp59a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2l_3]) (by linarith) hd
        ·
          exact Kepler.NliBanks26.cell53_core (by linarith [cmp59a0l_4]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2h_5]) hd
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact ((Kepler.NliBanks25.cell50_vac (by linarith [cmp59a0l_1]) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2l_3]) (by linarith)) hd).elim
        ·
          exact Kepler.NliBanks26.cell53_core (by linarith [cmp59a0l_4]) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2h_5]) hd
  ·
    by_cases n1 : x 1 ≤ (63/25:ℝ)
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp59a2l_3]) (by linarith) hd
        ·
          exact ((Kepler.NliBanks26.cell58_vac (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp59a2h_5])) hd).elim
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact Kepler.NliBanks25.cell35_core (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith [cmp59a2l_3]) (by linarith) hd
        ·
          exact ((Kepler.NliBanks26.cell58_vac (by linarith) (by linarith) (by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]) (by linarith) (by linarith) (by linarith [cmp59a2h_5])) hd).elim
    ·
      by_cases n2 : x 1 ≤ (66855339/25000000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2l_3]) (by linarith)) hd).elim
        ·
          exact ((Kepler.NliBanks26.cell59_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2h_5])) hd).elim
      ·
        by_cases n3 : x 2 ≤ (1087/500:ℝ)
        ·
          exact ((Kepler.NliBanks25.cell48_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2l_3]) (by linarith)) hd).elim
        ·
          exact ((Kepler.NliBanks26.cell59_vac (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith [cmp59a2h_5])) hd).elim

end Kepler.NliKit.BoxTreeWt2A

