/-
Kepler.NliKit.BoxTreeSqrt8S4 — leaf witnesses, shard 4 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD08_0 : ((rowsS8 (8 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF08_0 : ((rowsS8 (8 : Fin 30)).boxLo (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD08_0, vB40_2990671627550]; norm_num
theorem vD08_1 : ((rowsS8 (8 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3056642325217, 3056642325217⟩ : DC) := by decide
theorem vF08_1 : ((rowsS8 (8 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7799999999997453414835035800933837890625 := by rw [vD08_1, vB40_3056642325217]; norm_num
theorem vD08_2 : ((rowsS8 (8 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF08_2 : ((rowsS8 (8 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD08_2, vB40_2199023255552]; norm_num
theorem vD08_3 : ((rowsS8 (8 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF08_3 : ((rowsS8 (8 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD08_3, vB40_2230876107408]; norm_num
theorem vD08_4 : ((rowsS8 (8 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF08_4 : ((rowsS8 (8 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD08_4, vB40_2199023255552]; norm_num
theorem vD08_5 : ((rowsS8 (8 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF08_5 : ((rowsS8 (8 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD08_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp08a0l_1 : (2:ℝ) ≤ ((rowsS8 (8 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF08_0]; norm_num
theorem cmp08a0l_2 : (2683/1000:ℝ) ≤ ((rowsS8 (8 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF08_0]; norm_num
theorem cmp08a1h_3 : ((rowsS8 (8 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (202897/100000:ℝ) := by rw [vF08_3]; norm_num
theorem cmp08a2h_4 : ((rowsS8 (8 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF08_5]; norm_num
theorem cmp08a0h_5 : ((rowsS8 (8 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (139/50:ℝ) := by rw [vF08_1]; norm_num
theorem leaf_08_s8_cell08 : ∀ x ∈ rowBox (rowsS8 (8 : Fin 30)),
    (2:ℝ) * Kepler.Text.hplus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
      (2:ℝ) ≤ x 1 → x 1 ≤ (2:ℝ) * Kepler.Text.hminus →
      (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
      x 1 ≤ x 2 →
      (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
      (0:ℝ) < Kepler.NliBanks11.c3Main (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hy56 hdlt
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (68/25:ℝ)
  ·
    exact Kepler.Text.NliSqrt8.s8_cell03 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp08a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp08a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp08a2h_4]) (hd0 := hdlt)
  ·
    exact Kepler.Text.NliSqrt8.s8_cell08 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp08a0h_5]) (hc5l := by linarith) (hc5h := by linarith [cmp08a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp08a2h_4]) (hd0 := hdlt)

theorem vD09_0 : ((rowsS8 (9 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF09_0 : ((rowsS8 (9 : Fin 30)).boxLo (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD09_0, vB40_2990671627550]; norm_num
theorem vD09_1 : ((rowsS8 (9 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3056642325217, 3056642325217⟩ : DC) := by decide
theorem vF09_1 : ((rowsS8 (9 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7799999999997453414835035800933837890625 := by rw [vD09_1, vB40_3056642325217]; norm_num
theorem vD09_2 : ((rowsS8 (9 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF09_2 : ((rowsS8 (9 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD09_2, vB40_2230876107408]; norm_num
theorem vD09_3 : ((rowsS8 (9 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF09_3 : ((rowsS8 (9 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD09_3, vB40_2262728959265]; norm_num
theorem vD09_4 : ((rowsS8 (9 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF09_4 : ((rowsS8 (9 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD09_4, vB40_2199023255552]; norm_num
theorem vD09_5 : ((rowsS8 (9 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF09_5 : ((rowsS8 (9 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD09_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp09a0l_1 : (2:ℝ) ≤ ((rowsS8 (9 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF09_0]; norm_num
theorem cmp09a0l_2 : (2683/1000:ℝ) ≤ ((rowsS8 (9 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF09_0]; norm_num
theorem cmp09a2h_3 : ((rowsS8 (9 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF09_5]; norm_num
theorem cmp09a1h_4 : ((rowsS8 (9 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF09_3]; norm_num
theorem cmp09a0h_5 : ((rowsS8 (9 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (139/50:ℝ) := by rw [vF09_1]; norm_num
theorem leaf_09_s8_cell09 : ∀ x ∈ rowBox (rowsS8 (9 : Fin 30)),
    (2:ℝ) * Kepler.Text.hplus ≤ x 0 → x 0 ≤ Real.sqrt 8 →
      (2:ℝ) ≤ x 1 → x 1 ≤ (2:ℝ) * Kepler.Text.hminus →
      (2:ℝ) ≤ x 2 → x 2 ≤ (2:ℝ) * Kepler.Text.hminus →
      x 1 ≤ x 2 →
      (0:ℝ) ≤ Kepler.Text.deltaX (x 0 * x 0) 2 (x 1 * x 1) 2 (x 2 * x 2) 2 →
      (0:ℝ) < Kepler.NliBanks11.c3Main (x 0) (x 1) (x 2)
  := by
  intro x hx h4 h4' h5 h5' h6 h6' hy56 hdlt
  have f0 := hx (0 : Fin 3)
  have f1 := hx (1 : Fin 3)
  have f2 := hx (2 : Fin 3)
  by_cases n0 : x 0 ≤ (68/25:ℝ)
  ·
    by_cases n1 : x 1 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell03 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp09a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp09a2h_3]) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell04 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp09a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp09a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp09a2h_3]) (hd0 := hdlt)
  ·
    by_cases n1 : x 1 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell08 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp09a0h_5]) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp09a2h_3]) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell09 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp09a0h_5]) (hc5l := by linarith) (hc5h := by linarith [cmp09a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp09a2h_3]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

